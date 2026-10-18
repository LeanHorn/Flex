import Lean
import Flex.Core
import Flex.Zap.Scope



open Lean Meta Elab Tactic

partial def exprSol1Pres (κ : KVar) (e : Expr) : KM Expr := do
  let e ← exprScopePres κ e
  if let some (l, r) := e.and? then
    return mkApp2 (mkConst ``Or) (← exprSol1Pres κ l) (← exprSol1Pres κ r)
  else if e.isForall then
    let name := e.bindingName!
    let dom := e.bindingDomain!
    let domSort ← (inferType dom >>= whnf : MetaM Expr)
    if domSort.isProp then
      return ← withLocalDeclD name dom fun pfvar => do
        let body ← whnf (e.bindingBody!.instantiate1 pfvar)
        let inner ← exprSol1Pres κ body
        return mkApp2 (mkConst ``And) dom inner
    else
      return ← withLocalDeclD name dom fun fvar => do
        let body ← whnf (e.bindingBody!.instantiate1 fvar)
        let conjunct ← do
          if body.isForall then
            let p := body.bindingDomain!
            let pSort ← (inferType p >>= whnf : MetaM Expr)
            if pSort.isProp then
              withLocalDeclD body.bindingName! p fun pfvar => do
                let c'  := body.bindingBody!.instantiate1 pfvar
                let inner ← exprSol1Pres κ c'
                return mkApp2 (mkConst ``And) p inner
            else
              exprSol1Pres κ body
          else
            exprSol1Pres κ body
        let abstr := conjunct.abstract #[fvar]
        let lam   := Expr.lam name dom abstr .default
        return mkApp2 (mkConst ``Exists [Level.one]) dom lam
  else if e.getAppFn.isMVar && e.getAppFn.mvarId! == κ.mvarId then
    let args := e.getAppArgs.toList
    let eqs := (κ.params.zip (args.zip κ.paramTypes)).map fun (pi, (ai, ty)) =>
      mkApp3 (mkConst ``Eq [Level.one]) ty (.fvar (FVarId.mk pi)) ai
    match eqs with
    | []      => return mkConst ``True
    | [eq]    => return eq
    | eq :: rest => return rest.foldl (mkApp2 (mkConst ``And)) eq
  else
    return mkConst ``False
