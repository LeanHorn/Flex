import Flex.SMT.Encode

/-!
# Decoding solver models

The inverse of `Flex.SMT.Encode` for the terms solvers print in models: SMT symbols the encoder
declared (datatype sorts, constructors, selectors) map back to the Lean types and constructors
they came from, so a model over `F.Vec!3` becomes a Lean term over `F.Vec`.

SMT `Int` is Lean `Int` (`Nat` values are cast), and SMT `Bool` is Lean `Prop` (`Bool` values
`b` become `b = true`). Decoding needs no proof: candidates are checked by certification.
-/

namespace Flex.SMT

open Lean Meta

/-! ## S-expressions -/

inductive Sexp where
  | atom (value : String)
  | list (items : Array Sexp)
  deriving Inhabited, BEq, Repr

/-- `|s|` and `s` are the same SMT-LIB symbol. -/
def unquote (s : String) : String :=
  if s.length ≥ 2 && s.startsWith "|" && s.endsWith "|" then (s.drop 1 |>.dropEnd 1).toString
  else s

private partial def tokenize (input : String) : Except String (Array String) :=
  go input.toList #[]
where
  go : List Char → Array String → Except String (Array String)
    | [], out => .ok out
    | c :: rest, out =>
      if c.isWhitespace then go rest out
      else if c == ';' then go (rest.dropWhile (· != '\n')) out
      else if c == '(' || c == ')' then go rest (out.push (String.singleton c))
      else if c == '|' then
        let (body, after) := rest.span (· != '|')
        match after with
        | _ :: after => go after (out.push ("|" ++ String.ofList body ++ "|"))
        | [] => .error "unterminated quoted symbol"
      else if c == '"' then
        let rec string : List Char → List Char → Except String (List Char × List Char)
          | '"' :: '"' :: more, acc => string more ('"' :: '"' :: acc)
          | '"' :: more, acc => .ok (acc.reverse, more)
          | x :: more, acc => string more (x :: acc)
          | [], _ => .error "unterminated string"
        match string rest [] with
        | .ok (body, after) => go after (out.push ("\"" ++ String.ofList body ++ "\""))
        | .error e => .error e
      else
        let (atom, after) := (c :: rest).span fun x =>
          !(x.isWhitespace || x == '(' || x == ')' || x == ';' || x == '|' || x == '"')
        go after (out.push (String.ofList atom))

private partial def parseOne (tokens : Array String) (i : Nat) : Except String (Sexp × Nat) := do
  let some token := tokens[i]? | throw "unexpected end of input"
  if token == ")" then throw "unexpected ')'"
  if token != "(" then return (.atom (unquote token), i + 1)
  let mut items := #[]
  let mut j := i + 1
  repeat
    match tokens[j]? with
    | none => throw "missing ')'"
    | some ")" => return (.list items, j + 1)
    | some _ =>
      let (item, next) ← parseOne tokens j
      items := items.push item
      j := next
  throw "unreachable"

/-- All top-level S-expressions of `input`. Quoted symbols are unquoted. -/
def Sexp.parseAll (input : String) : Except String (Array Sexp) := do
  let tokens ← tokenize input
  let mut out := #[]
  let mut i := 0
  while i < tokens.size do
    let (e, next) ← parseOne tokens i
    out := out.push e
    i := next
  return out

partial def Sexp.toString : Sexp → String
  | .atom s => s
  | .list xs => "(" ++ " ".intercalate (xs.toList.map Sexp.toString) ++ ")"

instance : ToString Sexp := ⟨Sexp.toString⟩

/-! ## Symbol table -/

structure Constructor where
  /-- The monomorphic datatype instance. -/
  type : Expr
  ctor : Name
  deriving Inhabited

structure Selector where
  type : Expr
  ctor : Name
  field : Nat
  deriving Inhabited

/-- What the encoder declared, keyed by unquoted SMT symbol. -/
structure Symbols where
  sorts : Std.HashMap String Expr := {}
  constructors : Std.HashMap String Constructor := {}
  selectors : Std.HashMap String Selector := {}
  deriving Inhabited

def State.symbols (state : State) : Symbols := Id.run do
  let mut table : Symbols := {}
  for (type, datatype) in state.datatypes.toList do
    table := { table with sorts := table.sorts.insert (unquote datatype.symbol) type }
    for (ctor, symbol, selectors) in datatype.constructors do
      table := { table with constructors := table.constructors.insert (unquote symbol) { type, ctor } }
      for selector in selectors, i in [:selectors.size] do
        table := { table with
          selectors := table.selectors.insert (unquote selector) { type, ctor, field := i } }
  return table

/-! ## Terms -/

/-- A decoded term and its Lean type; type `Prop` means a formula. -/
structure Value where
  expr : Expr
  type : Expr
  deriving Inhabited

private def int : Expr := mkConst ``Int
private def prop : Expr := mkSort .zero
private def formula (e : Expr) : Value := { expr := e, type := prop }
private def integer (e : Expr) : Value := { expr := e, type := int }

/-- A model-defined function, expanded at each use. -/
structure Macro where
  params : Array (String × Sexp)
  body : Sexp
  deriving Inhabited

structure DecodeContext where
  symbols : Symbols
  macros : Std.HashMap String Macro := {}
  locals : Std.HashMap String Value := {}

abbrev DecodeM := ReaderT DecodeContext MetaM

private def fail (what : MessageData) : DecodeM α :=
  throwError m!"model decoding: {what}"

/-- Bring a Lean value into the decoder's canonical form: `Nat` as `Int`, `Bool` as `Prop`. -/
def normalize (e type : Expr) : MetaM Value := do
  let reduced ← whnf type
  if reduced.isConstOf ``Nat then return integer (mkIntNatCast e)
  if reduced.isConstOf ``Bool then return formula (← mkEq e (mkConst ``Bool.true))
  if reduced.isProp then return formula e
  if reduced.isConstOf ``Int then return integer e
  return { expr := e, type }

/-- A decoded value at an expected Lean type (the inverse of `normalize`). -/
def Value.at (value : Value) (expected : Expr) : MetaM Expr := do
  let target ← whnf expected
  if target.isConstOf ``Nat && value.type == int then return mkApp (mkConst ``Int.toNat) value.expr
  if target.isConstOf ``Bool && value.type.isProp then
    return mkApp2 (mkConst ``decide) value.expr
      (mkApp (mkConst ``Classical.propDecidable) value.expr)
  unless ← isDefEq value.type expected do
    throwError "model decoding: expected {expected}, got {value.expr} : {value.type}"
  return value.expr

/-- The fields of a constructor of a monomorphic datatype instance, with their types. -/
private def ctorFields (type : Expr) (ctor : Name) : MetaM (Expr × Array (Name × Expr)) := do
  let .const _ levels := type.getAppFn | throwError "model decoding: bad datatype {type}"
  let params := type.getAppArgs
  let info ← getConstInfoCtor ctor
  let mut fields ← instantiateForall (← instantiateTypeLevelParams info.toConstantVal levels) params
  let mut out := #[]
  for _ in [:info.numFields] do
    let .forallE name domain body _ := fields | throwError "model decoding: constructor {ctor}"
    out := out.push (name, domain)
    fields := body.lowerLooseBVars 1 1
  return (mkAppN (.const ctor levels) params, out)

partial def decodeSort (sort : Sexp) : DecodeM Expr := do
  match sort with
  | .atom "Int" => return int
  | .atom "Bool" => return prop
  | .atom s =>
    let some type := (← read).symbols.sorts[s]? | fail m!"unknown sort {s}"
    return type
  | .list #[.atom "Array", index, element] =>
    return .forallE `i (← decodeSort index) (← decodeSort element) .default
  | _ => fail m!"unsupported sort {sort}"

private def chain (args : Array Value) (op : Value → Value → DecodeM Expr) : DecodeM Value := do
  if args.size < 2 then fail m!"comparison needs two arguments"
  let mut out := #[]
  for i in [:args.size - 1] do out := out.push (← op args[i]! args[i+1]!)
  return formula (mkAndN out.toList)

private def requireInt (v : Value) : DecodeM Expr := do
  unless v.type == int do fail m!"expected an Int, got {v.expr}"
  return v.expr

private def requireProp (v : Value) : DecodeM Expr := do
  unless v.type.isProp do fail m!"expected a formula, got {v.expr}"
  return v.expr

mutual

partial def decodeTerm (term : Sexp) : DecodeM Value := do
  match term with
  | .atom "true" => return formula (mkConst ``True)
  | .atom "false" => return formula (mkConst ``False)
  | .atom s =>
    if let some n := s.toNat? then return integer (mkIntLit n)
    if let some v := (← read).locals[s]? then return v
    if let some c := (← read).symbols.constructors[s]? then return ← construct c #[]
    if (← read).macros.contains s then return ← expand s #[]
    fail m!"unknown symbol {s}"
  | .list items =>
    if items[0]? == some (.atom "!") && items.size ≥ 2 then return ← decodeTerm items[1]!
    decodeCompound term

partial def decodeCompound (term : Sexp) : DecodeM Value := do
  match term with
  | .list #[.atom "let", .list bindings, body] =>
    let mut locals := (← read).locals
    for binding in bindings do
      let .list #[.atom name, value] := binding | fail m!"bad let binding {binding}"
      locals := locals.insert name (← decodeTerm value)
    withReader (fun ctx => { ctx with locals := locals }) (decodeTerm body)
  | .list #[.atom q, .list binders, body] =>
    if q != "exists" && q != "forall" then decodeApp term
    else quantifier (q == "exists") binders.toList body
  | .list #[.list #[.atom "_", .atom "is", .atom c], x] => tester c (← decodeTerm x)
  | _ => decodeApp term

partial def decodeApp (term : Sexp) : DecodeM Value := do
  let .list items := term | fail m!"bad term {term}"
  let some (Sexp.atom head) := items[0]? | fail m!"unsupported application {term}"
  let args ← items[1:].toArray.mapM decodeTerm
  match head, args with
  | "not", #[a] => return formula (mkNot (← requireProp a))
  | "and", _ => return formula (mkAndN (← args.mapM requireProp).toList)
  | "or", _ =>
    let ps ← args.mapM requireProp
    return formula (if ps.isEmpty then mkConst ``False else ps[:ps.size - 1].foldr mkOr ps.back!)
  | "=>", _ =>
    let ps ← args.mapM requireProp
    if ps.isEmpty then fail m!"empty implication"
    return formula (ps[:ps.size - 1].foldr (fun p q => .forallE `h p q .default) ps.back!)
  | "xor", #[a, b] => return formula (mkNot (mkIff (← requireProp a) (← requireProp b)))
  | "ite", #[c, a, b] =>
    let c ← requireProp c
    if a.type.isProp then
      return formula (mkOr (mkAnd c (← requireProp a)) (mkAnd (mkNot c) (← requireProp b)))
    let b ← b.at a.type
    let u ← getLevel a.type
    let e := mkApp5 (.const ``ite [u]) a.type c (mkApp (mkConst ``Classical.propDecidable) c) a.expr b
    return { expr := e, type := a.type }
  | "=", _ =>
    chain args fun a b => do
      if a.type.isProp then return mkIff (← requireProp a) (← requireProp b)
      mkEq a.expr (← b.at a.type)
  | "distinct", _ =>
    let mut out := #[]
    for i in [:args.size] do
      for j in [i+1:args.size] do
        out := out.push (mkNot (← mkEq args[i]!.expr (← args[j]!.at args[i]!.type)))
    return formula (mkAndN out.toList)
  | "<=", _ => chain args fun a b => return mkIntLE (← requireInt a) (← requireInt b)
  | "<", _ => chain args fun a b => return mkIntLT (← requireInt a) (← requireInt b)
  | ">=", _ => chain args fun a b => return mkIntLE (← requireInt b) (← requireInt a)
  | ">", _ => chain args fun a b => return mkIntLT (← requireInt b) (← requireInt a)
  | "-", #[a] => return integer (mkIntNeg (← requireInt a))
  | "-", _ => arith mkIntSub args
  | "+", _ => arith mkIntAdd args
  | "*", _ => arith mkIntMul args
  | "div", #[a, b] => return integer (mkIntDiv (← requireInt a) (← requireInt b))
  | "mod", #[a, b] => return integer (mkIntMod (← requireInt a) (← requireInt b))
  | "abs", #[a] => return integer (mkIntNatCast (mkApp (mkConst ``Int.natAbs) (← requireInt a)))
  | "select", #[array, index] =>
    let .forallE _ domain codomain _ ← whnf array.type | fail m!"select on a non-array {array.expr}"
    normalize (mkApp array.expr (← index.at domain)) codomain
  | _, _ =>
    let symbols := (← read).symbols
    if let some c := symbols.constructors[head]? then return ← construct c args
    if let some s := symbols.selectors[head]? then
      let #[x] := args | fail m!"selector {head} takes one argument"
      return ← select s x
    if (← read).macros.contains head then return ← expand head args
    fail m!"unsupported function {head}"

partial def arith (op : Expr → Expr → Expr) (args : Array Value) : DecodeM Value := do
  let xs ← args.mapM requireInt
  let some first := xs[0]? | fail m!"empty arithmetic"
  return integer (xs[1:].foldl op first)

partial def quantifier (isExists : Bool) (binders : List Sexp) (body : Sexp) : DecodeM Value := do
  match binders with
  | [] => decodeTerm body
  | .list #[.atom name, sort] :: rest =>
    let type ← decodeSort sort
    withLocalDeclD (.mkSimple name) type fun x => do
      let value ← normalize x type
      let inner ← withReader (fun ctx => { ctx with locals := ctx.locals.insert name value })
        (quantifier isExists rest body)
      let inner ← requireProp inner
      if isExists then
        return formula (mkApp2 (.const ``Exists [← getLevel type]) type (← mkLambdaFVars #[x] inner))
      return formula (← mkForallFVars #[x] inner)
  | b :: _ => fail m!"bad binder {b}"

partial def construct (c : Constructor) (args : Array Value) : DecodeM Value := do
  let (head, fields) ← ctorFields c.type c.ctor
  unless fields.size == args.size do fail m!"constructor {c.ctor} applied to {args.size} arguments"
  let values ← (args.zip fields).mapM fun (a, (_, t)) => a.at t
  return { expr := mkAppN head values, type := c.type }

/-- `((_ is C) x)` as `∃ fields, x = C fields`. -/
partial def tester (symbol : String) (x : Value) : DecodeM Value := do
  let some c := (← read).symbols.constructors[symbol]? | fail m!"unknown tester {symbol}"
  let (head, fields) ← ctorFields c.type c.ctor
  let x ← x.at c.type
  let decls := fields.map fun (n, t) => (n, fun (_ : Array Expr) => pure t)
  withLocalDeclsD decls fun xs => do
    let mut result ← mkEq x (mkAppN head xs)
    for v in xs.reverse do
      let t ← inferType v
      result := mkApp2 (.const ``Exists [← getLevel t]) t (← mkLambdaFVars #[v] result)
    return formula result

/-- A selector: a projection on structure-like types, else a case split that is `default` on
the other constructors (SMT leaves those values unspecified). -/
partial def select (s : Selector) (x : Value) : DecodeM Value := do
  let x ← x.at s.type
  let (_, fields) ← ctorFields s.type s.ctor
  let fieldType := fields[s.field]!.2
  let .const ind levels := s.type.getAppFn | fail m!"bad datatype {s.type}"
  if (← getConstInfoInduct ind).ctors.length == 1 && !(← getConstInfoInduct ind).isRec then
    return ← normalize (.proj ind s.field x) fieldType
  let info ← getConstInfoInduct ind
  let u ← getLevel fieldType
  let motive := Expr.lam `x s.type fieldType .default
  let some inst ← synthInstance? (mkApp (.const ``Inhabited [u]) fieldType)
    | fail m!"selector on {ind} needs an Inhabited instance for {fieldType}"
  let default := mkApp2 (.const ``Inhabited.default [u]) fieldType inst
  let minors ← info.ctors.toArray.mapM fun ctor => do
    let (_, fs) ← ctorFields s.type ctor
    let decls := fs.map fun (n, t) => (n, fun (_ : Array Expr) => pure t)
    withLocalDeclsD decls fun xs =>
      mkLambdaFVars xs (if ctor == s.ctor then xs[s.field]! else default)
  let casesOn := mkAppN (.const (mkCasesOnName ind) (u :: levels)) s.type.getAppArgs
  normalize (mkAppN (mkApp2 casesOn motive x) minors) fieldType

/-- Expand a model-defined function at its arguments. -/
partial def expand (name : String) (args : Array Value) : DecodeM Value := do
  let some m := (← read).macros[name]? | fail m!"unknown function {name}"
  unless m.params.size == args.size do fail m!"{name} applied to {args.size} arguments"
  let mut locals : Std.HashMap String Value := {}
  for (param, _) in m.params, arg in args do locals := locals.insert param arg
  -- The body sees only its own parameters, and not itself.
  withReader (fun ctx => { ctx with locals := locals, macros := ctx.macros.erase name })
    (decodeTerm m.body)

end

/-- A `define-fun` command: name, parameters with sorts, result sort, body. -/
def parseDefineFun (command : Sexp) : Except String (String × Macro × Sexp) :=
  match command with
  | .list #[.atom "define-fun", .atom name, .list params, result, body] => do
    let params ← params.mapM fun
      | .list #[.atom p, sort] => pure (p, sort)
      | p => throw s!"bad parameter {p}"
    return (name, { params, body }, result)
  | _ => throw s!"expected define-fun, got {command}"

end Flex.SMT
