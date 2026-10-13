import Flex.VCG.SystemFRK.Typing.Recursion

/-! One operational regression for lexical recursion capture. The recursive
call is delayed beneath both a type abstraction and an ordinary lambda. The
caller invokes the returned closures with no current recursion frame. -/
namespace SystemFRK.RecursionChecks

private def nilCode : Expr := .lam "ignored" .int (.int 0)
private def consCode : Expr := .lam "ignored" .int
  (.letE "later" (.recur (.var "tail"))
    (.letE "call" (.tyApp (.var "later") .int) (.app (.var "call") (.int 0))))
private def body : Expr := .matchE (.var "xs")
  [("nil", [], .tyLam nilCode), ("cons", ["head", "tail"], .tyLam consCode)]
private def loop : Value := .recursiveClosure "xs" body []
private def singleton : Value := .ctor "cons" [.int 7, .ctor "nil" []]
private def rootEnv : Environment :=
  [("head", .int 7), ("tail", .ctor "nil" []), ("xs", singleton)]
private def emptyEnv : Environment := [("xs", .ctor "nil" [])]
private def deferred : Value := .typeClosure consCode rootEnv (some loop)

private theorem root_returns : Apply {} loop singleton deferred := by
  apply Apply.recursiveClosure
  exact .matchE (.var rfl) rfl rfl .tyLam

private theorem empty_returns : Apply {} loop (.ctor "nil" [])
    (.typeClosure nilCode emptyEnv (some loop)) := by
  apply Apply.recursiveClosure
  exact .matchE (.var rfl) rfl rfl .tyLam

/-- Both captured frames survive returning from the root call. In particular,
the `none` caller frame cannot accidentally replace the captured function. -/
theorem delayed_recursion_evaluates :
    Eval {} [("loop", loop), ("input", singleton)] none
      (.letE "deferred" (.app (.var "loop") (.var "input"))
        (.letE "instantiated" (.tyApp (.var "deferred") .int)
          (.app (.var "instantiated") (.int 99)))) (.int 0) := by
  apply Eval.letE (.app (.var rfl) (.var rfl) root_returns)
  apply Eval.letE (.tyApp (.var rfl) (.closure .lam))
  apply Eval.app (.var rfl) .int
  apply Apply.closure
  apply Eval.letE (.recur rfl (.var rfl) empty_returns)
  apply Eval.letE (.tyApp (.var rfl) (.closure .lam))
  exact .app (.var rfl) .int (.closure .int)

end SystemFRK.RecursionChecks
