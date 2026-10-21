/-! Precompiled FFI boundary for the CHC process runner. -/
namespace Flex.CHC.Process.Native

/-- All fields are objects, in this order, to match `native/chc_process.cpp`.
Kinds: 0 = exited, 1 = timeout, 2 = spawn error, 3 = I/O error (or cancellation).
Bytes are decoded only after collection, preserving split UTF-8 sequences. -/
structure RawResult where
  kind : Nat
  code : Nat
  stdout : ByteArray
  stderr : ByteArray
  message : String

@[extern "flex_chc_run"]
opaque run (executable : @& String) (args : @& Array String) (cwd : @& String)
    (input : @& ByteArray) (timeoutMs : UInt64) : IO RawResult

end Flex.CHC.Process.Native
