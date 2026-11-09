import Lean

-- Each request starts from the same harness state; the parent enforces its watchdog.
open Lean Elab Command in
elab "rq3_batch_worker" : command => do
  let baseline ← get
  liftIO do
    let stdin ← IO.FS.Handle.mk "/dev/stdin" .read
    let stdout ← IO.FS.Handle.mk "/dev/stdout" .write
    let send (value : Json) : IO Unit := do
      stdout.putStrLn ("RQ3_WORKER " ++ value.compress)
      stdout.flush
    send (Json.mkObj [("kind", toJson "ready")])
    repeat
      let line ← stdin.getLine
      if line.isEmpty then break
      try
        let request ← match Json.parse line with
          | .ok request => pure request
          | .error error => throw <| IO.userError error
        let field (name : String) : IO String :=
          match request.getObjValAs? String name with
          | .ok value => pure value
          | .error error => throw <| IO.userError error
        let id ← field "id"
        let source ← field "source"
        let log ← field "log"
        let input ← IO.FS.readFile source
        let started ← IO.monoNanosNow
        -- Reuse only the baseline imported environment, never a previous request's state.
        let state ← Lean.Elab.IO.processCommands (Parser.mkInputContext input source) {}
          { baseline with
            messages := {}
            infoState := {}
            traceState := {}
            snapshotTasks := #[]
            prevLinterStates := none }
        let mut diagnostics := ""
        for message in state.commandState.messages.toList do
          diagnostics := diagnostics ++ (← message.toString) ++ "\n"
        IO.FS.writeFile log diagnostics
        send (Json.mkObj [("kind", toJson "done"), ("id", toJson id),
          ("has_errors", toJson state.commandState.messages.hasErrors),
          ("request_ns", toJson ((← IO.monoNanosNow) - started))])
      catch error =>
        send (Json.mkObj [("kind", toJson "error"), ("error", toJson (toString error))])
