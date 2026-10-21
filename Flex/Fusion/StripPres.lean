import Flex.Fusion.Strip
import Flex.Zap.Sol1

open Lean Meta

/-- Structure-preserving scoped solution + prefix metadata for the
    path-informed walk. `sol` is LCA-scoped param-form (no extra `∃`/guards
    above the LCA); the counts tell `cert` how many accumulated
    binders/guards/orPath bits to `drop` at each κ-leaf. -/
structure ScopedSolPres where
  sol      : Expr
  nBinders : Nat    -- prefix value-binders above the LCA  (→ κ-params)
  nGuards  : Nat    -- prefix Prop-guards above the LCA     (dropped)
  nOr      : Nat    -- one-sided `∧` routings above the LCA (→ orPath bits)
  deriving Inhabited

/-- `exprSolScopedPres κ e` — the structure-preserving analog of
    `exprSolScoped`. Descends the κ-free prefix through `∀`-binders **and**
    one-sided `∧` routings, param-matching value binders and counting the
    prefix, stops at the LCA (first `∧` with κ in both branches, or a κ-leaf,
    or a non-mapping value binder), and runs `exprSol1Pres` there so the
    below-LCA `∧`↔`∨` mirror survives for `cert`/`nav`.

    Mirrors `exprSolScoped` (Strip.lean) verbatim apart from: the `∧`-routing
    branch, the `(nB,nG,nOr)` prefix counters, and `exprSol1Pres` (preserving)
    in `finalize` instead of `exprSol1` (branch-stripping). -/
partial def exprSolScopedPres (κ : KVar) (e : Expr) : KM ScopedSolPres :=
  goStrip κ e [] 0 0 0
where
  goStrip (κ : KVar) (e : Expr) (acc : List (Expr × Name))
      (nB nG nOr : Nat) : KM ScopedSolPres := do
    -- ∧ routing: descend the unique κ-branch; κ in both ⇒ LCA, stop here.
    if let some (l, r) := e.and? then
      let lHas := (← KM.exprKVars l).contains κ
      let rHas := (← KM.exprKVars r).contains κ
      if lHas && !rHas then
        goStrip κ l acc nB nG (nOr + 1)
      else if rHas && !lHas then
        goStrip κ r acc nB nG (nOr + 1)
      else
        finalize κ e acc nB nG nOr
    else if e.isForall then
      let dom := e.bindingDomain!
      if (← KM.exprKVars dom).contains κ then
        finalize κ e acc nB nG nOr
      else
        let domSort ← (inferType dom >>= whnf : MetaM Expr)
        withLocalDeclD e.bindingName! dom fun fvar => do
          let body := e.bindingBody!.instantiate1 fvar
          if domSort.isProp then
            goStrip κ body acc nB (nG + 1) nOr
          else
            -- 2a: a Prop κ-arg (`dom = Sort 0`) at a *universal* slot folds — its
            -- slot equality carries the constraint (e.g. `z2 = True`), giving the
            -- tight solution. `findOuterBinderToParam` returns `some` only when the
            -- binder fills that slot in *every* κ-app, so the old worry ("a sibling
            -- clause pins the slot to a literal") already yields `none` (not
            -- universal) and stays an ∃-binder. Type-and-higher sort binders
            -- (`Sort ≥ 1`) remain blocked.
            let foldAt := if dom.isSort && dom != (.sort .zero) then none
                          else findOuterBinderToParam κ fvar.fvarId! body
            match foldAt with
            | some i =>
              goStrip κ body (acc ++ [(fvar, κ.params[i]!)]) (nB + 1) nG nOr
            | none =>
              -- 2b: a struct-typed scope binder reaches κ only via projections
              -- (`Foo.field x`), so the bare-fvar check above misses it. Fold the
              -- projections to κ-params and DROP the binder — but only when every
              -- occurrence of `fvar` sits inside a recorded projection (else
              -- dropping it would dangle a bare reference).
              let projFolds := findOuterBinderProjFolds κ fvar.fvarId! body
              let bodyNoProj := projFolds.foldl
                (fun b (pe, _) => b.replace (fun s => if s == pe then some (mkConst ``True) else none))
                body
              if !projFolds.isEmpty && !bodyNoProj.containsFVar fvar.fvarId! then
                let acc' := acc ++ projFolds.map (fun (pe, i) => (pe, κ.params[i]!))
                goStrip κ body acc' (nB + 1) nG nOr
              else
                -- stop-strip: re-close fvar; this binder stays below the LCA.
                let bodyClosed := body.abstract #[fvar]
                let cPrime := Expr.forallE e.bindingName! dom bodyClosed e.bindingInfo!
                finalize κ cPrime acc nB nG nOr
    else
      finalize κ e acc nB nG nOr

  finalize (κ : KVar) (cPrime : Expr) (acc : List (Expr × Name))
      (nB nG nOr : Nat) : KM ScopedSolPres := do
    let sol0 ← exprSol1Pres κ cPrime
    -- Substitute each recorded scope-expr → synthetic κ-param fvar. Entries are
    -- bare fvars (`fvar`) or struct projections (`Foo.field x`); one simultaneous
    -- `Expr.replace` pass matches whichever occurs (cf. Strip.lean).
    let sol := sol0.replace fun sub =>
      acc.findSome? fun (pe, paramName) =>
        if sub == pe then some (.fvar (FVarId.mk paramName)) else none
    return { sol := sol, nBinders := nB, nGuards := nG, nOr := nOr }
