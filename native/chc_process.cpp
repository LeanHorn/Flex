// A fresh solver process for each request, without fork() or a resident launcher.
// Only the public Lean FFI is used; no Lean runtime handle layouts are assumed.
#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include <lean/lean.h>

#include <algorithm>
#include <chrono>
#include <cstring>
#include <exception>
#include <string>
#include <system_error>
#include <vector>

#ifndef _WIN32
#include <cerrno>
#include <fcntl.h>
#include <poll.h>
#include <pthread.h>
#include <signal.h>
#include <spawn.h>
#include <sys/wait.h>
#include <unistd.h>
extern char **environ;
#endif

namespace {
using Bytes = std::vector<uint8_t>;

lean_object *leanBytes(const Bytes &bytes) {
    auto *result = lean_alloc_sarray(1, bytes.size(), bytes.size());
    if (!bytes.empty()) std::memcpy(lean_sarray_cptr(result), bytes.data(), bytes.size());
    return result;
}

// Keep in sync with Flex.CHC.Process.Native.RawResult: all five fields are objects.
lean_object *result(unsigned kind, unsigned code, const Bytes &out, const Bytes &err,
                    const std::string &message = {}) {
    auto *value = lean_alloc_ctor(0, 5, 0);
    lean_ctor_set(value, 0, lean_unsigned_to_nat(kind));
    lean_ctor_set(value, 1, lean_unsigned_to_nat(code));
    lean_ctor_set(value, 2, leanBytes(out));
    lean_ctor_set(value, 3, leanBytes(err));
    lean_ctor_set(value, 4, lean_mk_string(message.c_str()));
    return lean_io_result_mk_ok(value);
}

#ifndef _WIN32
using Clock = std::chrono::steady_clock;
constexpr size_t transferBudget = 64 * 1024;
constexpr int cancelPollMs = 10;

std::string errorMessage(const char *operation, int error) {
    return std::string(operation) + ": " + std::error_code(error, std::generic_category()).message();
}

// Closing an interrupted close again can close an unrelated descriptor on Linux.
class Fd {
    int value_ = -1;
public:
    Fd() = default;
    Fd(const Fd &) = delete;
    Fd &operator=(const Fd &) = delete;
    ~Fd() { reset(); }
    int get() const { return value_; }
    bool open() const { return value_ >= 0; }
    void reset(int value = -1) {
        if (value_ >= 0) close(value_);
        value_ = value;
    }
};

struct Pipe { Fd read, write; };

int makePipe(Pipe &pipe) {
    int fds[2];
#ifdef __linux__
    if (pipe2(fds, O_CLOEXEC) < 0) return errno;
#else
    if (::pipe(fds) < 0) return errno;
#endif
    pipe.read.reset(fds[0]);
    pipe.write.reset(fds[1]);
    for (Fd *fd : {&pipe.read, &pipe.write}) {
        // File actions must also work when the caller began with 0, 1, or 2 closed.
        if (fd->get() < 3) {
            int copy = fcntl(fd->get(), F_DUPFD_CLOEXEC, 3);
            if (copy < 0) return errno;
            fd->reset(copy);
        }
        if (fcntl(fd->get(), F_SETFD, FD_CLOEXEC) < 0) return errno;
    }
    return 0;
}

int nonblocking(Fd &fd) {
    int flags = fcntl(fd.get(), F_GETFL);
    if (flags < 0 || fcntl(fd.get(), F_SETFL, flags | O_NONBLOCK) < 0) return errno;
    return 0;
}

// A closed solver stdin must not deliver SIGPIPE to Lean. Signal state is local
// to this calling thread and restored; no process-wide signal handler is changed.
class BlockSigpipe {
    sigset_t blocked_{}, previous_{};
    bool active_ = false, previouslyPending_ = false, generated_ = false;
public:
    int start() {
        sigemptyset(&blocked_);
        sigaddset(&blocked_, SIGPIPE);
        int rc = pthread_sigmask(SIG_BLOCK, &blocked_, &previous_);
        if (rc) return rc;
        active_ = true;
        sigset_t pending;
        if (sigpending(&pending) < 0) return errno;
        previouslyPending_ = sigismember(&pending, SIGPIPE) == 1;
        return 0;
    }
    void generated() { generated_ = true; }
    ~BlockSigpipe() {
        if (!active_) return;
        if (generated_ && !previouslyPending_) {
            sigset_t pending;
            if (sigpending(&pending) == 0 && sigismember(&pending, SIGPIPE) == 1) {
                int signal;
                // SIGPIPE is blocked and known to be pending on this thread.
                sigwait(&blocked_, &signal);
            }
        }
        pthread_sigmask(SIG_SETMASK, &previous_, nullptr);
    }
};

class SpawnActions {
    posix_spawn_file_actions_t actions_{};
    bool active_ = false;
public:
    int start() {
        int rc = posix_spawn_file_actions_init(&actions_);
        active_ = rc == 0;
        return rc;
    }
    ~SpawnActions() { if (active_) posix_spawn_file_actions_destroy(&actions_); }
    posix_spawn_file_actions_t *get() { return &actions_; }
};

class SpawnAttributes {
    posix_spawnattr_t attributes_{};
    bool active_ = false;
public:
    int start() {
        int rc = posix_spawnattr_init(&attributes_);
        active_ = rc == 0;
        return rc;
    }
    ~SpawnAttributes() { if (active_) posix_spawnattr_destroy(&attributes_); }
    posix_spawnattr_t *get() { return &attributes_; }
};

// Leave an exited parent as a zombie while its pipes are open. Its PID therefore
// cannot be recycled before group cleanup, including when a descendant holds a pipe.
class Child {
    pid_t pid_ = -1;
public:
    void own(pid_t pid) { pid_ = pid; }
    int exited(bool &done) {
        siginfo_t info{};
        if (waitid(P_PID, static_cast<id_t>(pid_), &info, WEXITED | WNOHANG | WNOWAIT) < 0) {
            int error = errno;
            if (error == ECHILD) pid_ = -1; // Never signal a potentially recycled PID.
            return error == EINTR ? 0 : error;
        }
        done = info.si_pid != 0;
        return 0;
    }
    int finish(int &status) {
        if (pid_ < 0) return ECHILD;
        // Kill remaining descendants even after a successful parent exit.
        kill(-pid_, SIGKILL);
        kill(pid_, SIGKILL);
        pid_t waited;
        do { waited = waitpid(pid_, &status, 0); } while (waited < 0 && errno == EINTR);
        int error = waited < 0 ? errno : 0;
        pid_ = -1;
        return error;
    }
    ~Child() { if (pid_ >= 0) { int status; finish(status); } }
};

bool containsNul(b_lean_obj_arg string) {
    return std::memchr(lean_string_cstr(string), '\0', lean_string_size(string) - 1) != nullptr;
}

int setWorkingDirectory(SpawnActions &actions, const char *cwd) {
    if (!*cwd) return 0;
#if defined(__APPLE__) || defined(__linux__)
    // The child changes directory as a spawn action, never the multithreaded parent.
    return posix_spawn_file_actions_addchdir_np(actions.get(), cwd);
#else
    return ENOTSUP;
#endif
}

int spawn(const char *executable, char *const *argv, const char *cwd,
          Pipe &input, Pipe &output, Pipe &error, Child &child) {
    SpawnActions actions;
    SpawnAttributes attributes;
    int rc = actions.start();
    if (rc) return rc;
    if ((rc = attributes.start())) return rc;
    if ((rc = setWorkingDirectory(actions, cwd))) return rc;
    const int sources[] = {input.read.get(), output.write.get(), error.write.get()};
    for (int destination = 0; destination < 3; ++destination) {
        rc = posix_spawn_file_actions_adddup2(actions.get(), sources[destination], destination);
        if (rc) return rc;
    }
    for (int fd : {input.read.get(), input.write.get(), output.read.get(),
                   output.write.get(), error.read.get(), error.write.get()}) {
        if ((rc = posix_spawn_file_actions_addclose(actions.get(), fd))) return rc;
    }
    sigset_t mask, defaults;
    sigemptyset(&mask);
    sigemptyset(&defaults);
    sigaddset(&defaults, SIGPIPE);
    if ((rc = posix_spawnattr_setsigmask(attributes.get(), &mask))) return rc;
    if ((rc = posix_spawnattr_setsigdefault(attributes.get(), &defaults))) return rc;
    if ((rc = posix_spawnattr_setpgroup(attributes.get(), 0))) return rc;
    short flags = POSIX_SPAWN_SETPGROUP | POSIX_SPAWN_SETSIGMASK | POSIX_SPAWN_SETSIGDEF;
#ifdef POSIX_SPAWN_CLOEXEC_DEFAULT
    flags |= POSIX_SPAWN_CLOEXEC_DEFAULT;
#endif
    if ((rc = posix_spawnattr_setflags(attributes.get(), flags))) return rc;
    pid_t pid;
    rc = posix_spawnp(&pid, executable, actions.get(), attributes.get(), argv, environ);
    if (rc == 0) child.own(pid);
    return rc;
}

// Bound each stream's work so an always-ready pipe cannot starve timeout checks,
// cancellation, or the other two pipes. Bytes are decoded only on the Lean side.
int readAvailable(Fd &fd, Bytes &bytes) {
    if (!fd.open()) return 0;
    uint8_t buffer[8192];
    size_t transferred = 0;
    while (transferred < transferBudget) {
        ssize_t count = read(fd.get(), buffer, sizeof(buffer));
        if (count > 0) {
            bytes.insert(bytes.end(), buffer, buffer + count);
            transferred += static_cast<size_t>(count);
        } else if (count == 0) {
            fd.reset();
            return 0;
        } else {
            int error = errno;
            return error == EAGAIN || error == EWOULDBLOCK || error == EINTR ? 0 : error;
        }
    }
    return 0;
}

int writeAvailable(Fd &fd, const uint8_t *input, size_t size, size_t &offset,
                   BlockSigpipe &sigpipe) {
    size_t count = std::min(transferBudget, size - offset);
    ssize_t written = write(fd.get(), input + offset, count);
    if (written > 0) {
        offset += static_cast<size_t>(written);
        if (offset == size) fd.reset();
        return 0;
    }
    if (written == 0) return 0;
    int error = errno;
    if (error == EPIPE) sigpipe.generated();
    return error == EAGAIN || error == EWOULDBLOCK || error == EINTR ? 0 : error;
}

lean_object *run(b_lean_obj_arg executable, b_lean_obj_arg args, b_lean_obj_arg cwd,
                 b_lean_obj_arg input, uint64_t timeoutMs) {
    const auto started = Clock::now();
    if (!timeoutMs) return result(3, 0, {}, {}, "solver timeout must be positive");
    if (containsNul(executable) || containsNul(cwd))
        return result(2, 0, {}, {}, "executable and cwd must not contain NUL");
    std::vector<char *> argv;
    argv.push_back(const_cast<char *>(lean_string_cstr(executable)));
    for (size_t i = 0; i < lean_array_size(args); ++i) {
        auto *arg = lean_array_uget_borrowed(args, i);
        if (containsNul(arg)) return result(2, 0, {}, {}, "arguments must not contain NUL");
        argv.push_back(const_cast<char *>(lean_string_cstr(arg)));
    }
    argv.push_back(nullptr);

    BlockSigpipe sigpipe;
    int rc = sigpipe.start();
    if (rc) return result(3, 0, {}, {}, errorMessage("block SIGPIPE", rc));
    Pipe stdinPipe, stdoutPipe, stderrPipe;
    for (Pipe *pipe : {&stdinPipe, &stdoutPipe, &stderrPipe})
        if ((rc = makePipe(*pipe))) return result(2, 0, {}, {}, errorMessage("pipe", rc));
    for (Fd *fd : {&stdinPipe.write, &stdoutPipe.read, &stderrPipe.read})
        if ((rc = nonblocking(*fd))) return result(2, 0, {}, {}, errorMessage("nonblocking pipe", rc));
    Child child;
    rc = spawn(lean_string_cstr(executable), argv.data(), lean_string_cstr(cwd),
               stdinPipe, stdoutPipe, stderrPipe, child);
    if (rc) return result(2, 0, {}, {}, errorMessage("posix_spawnp", rc));
    stdinPipe.read.reset();
    stdoutPipe.write.reset();
    stderrPipe.write.reset();
    size_t inputSize = lean_sarray_size(input), inputOffset = 0;
    if (!inputSize) stdinPipe.write.reset();
    Bytes out, err;
    unsigned kind = 0;
    std::string message;
    bool exited = false;
    while (true) {
        if (lean_io_check_canceled_core()) {
            kind = 3;
            message = "solver request canceled";
            break;
        }
        if ((rc = child.exited(exited))) {
            kind = 3;
            message = errorMessage("waitid", rc);
            break;
        }
        if (exited && !stdinPipe.write.open() && !stdoutPipe.read.open() && !stderrPipe.read.open())
            break;
        auto elapsed = static_cast<uint64_t>(
            std::chrono::duration_cast<std::chrono::milliseconds>(Clock::now() - started).count());
        if (elapsed >= timeoutMs) {
            kind = 1;
            break;
        }
        pollfd fds[] = {{stdinPipe.write.get(), POLLOUT, 0},
                        {stdoutPipe.read.get(), POLLIN, 0},
                        {stderrPipe.read.get(), POLLIN, 0}};
        // EOF can precede waitid observing exit by a few microseconds. Avoid
        // adding the full cancellation polling interval to these short requests.
        bool hasIo = stdinPipe.write.open() || stdoutPipe.read.open() || stderrPipe.read.open();
        int intervalMs = hasIo ? cancelPollMs : 1;
        int waitMs = static_cast<int>(std::min<uint64_t>(intervalMs, timeoutMs - elapsed));
        if (poll(fds, 3, waitMs) < 0) {
            if (errno == EINTR) continue;
            kind = 3;
            message = errorMessage("poll", errno);
            break;
        }
        // Read diagnostics before attempting a write that may discover a closed stdin.
        if (fds[1].revents && (rc = readAvailable(stdoutPipe.read, out))) {
            kind = 3;
            message = errorMessage("read stdout", rc);
            break;
        }
        if (fds[2].revents && (rc = readAvailable(stderrPipe.read, err))) {
            kind = 3;
            message = errorMessage("read stderr", rc);
            break;
        }
        if (fds[0].revents && (rc = writeAvailable(stdinPipe.write, lean_sarray_cptr(input),
                                                  inputSize, inputOffset, sigpipe))) {
            kind = 3;
            message = errorMessage("write stdin", rc);
            break;
        }
    }
    stdinPipe.write.reset();
    int status = 0;
    rc = child.finish(status);
    if (rc && kind == 0) {
        kind = 3;
        message = errorMessage("waitpid", rc);
    }
    // Retain diagnostics already in the pipes on timeout or failure. Never wait on
    // a descendant which escaped the process group and kept a descriptor open.
    readAvailable(stdoutPipe.read, out);
    readAvailable(stderrPipe.read, err);
    unsigned code = 0;
    if (kind == 0) {
        if (WIFEXITED(status)) code = static_cast<unsigned>(WEXITSTATUS(status));
        else if (WIFSIGNALED(status)) code = 128 + static_cast<unsigned>(WTERMSIG(status));
        else { kind = 3; message = "child did not report an exit status"; }
    }
    return result(kind, code, out, err, message);
}
#endif
} // namespace

extern "C" LEAN_EXPORT lean_obj_res flex_chc_run(
    b_lean_obj_arg executable, b_lean_obj_arg args, b_lean_obj_arg cwd,
    b_lean_obj_arg input, uint64_t timeoutMs) {
#ifdef _WIN32
    return result(3, 0, {}, {}, "native CHC spawning is only available on POSIX");
#else
    try {
        return run(executable, args, cwd, input, timeoutMs);
    } catch (const std::exception &error) {
        // RAII has already killed and reaped the child before crossing the FFI.
        return result(3, 0, {}, {}, std::string("native process exception: ") + error.what());
    } catch (...) {
        return result(3, 0, {}, {}, "unknown native process exception");
    }
#endif
}
