import Lean

/-! PatternStrSearcherABAsSearcherANextMatch and its dependencies, copied from flex-benchmarks/pattern. -/

-- LeanProofs.Flux.Prelude
-- FLUX LIBRARY [DO NOT MODIFY] --
abbrev BitVec_shiftLeft { n : Nat } (x s : BitVec n) : BitVec n := BitVec.shiftLeft x (s.toNat)
abbrev BitVec_ushiftRight { n : Nat } (x s : BitVec n) : BitVec n := BitVec.ushiftRight x (s.toNat)
abbrev BitVec_sshiftRight { n : Nat } (x s : BitVec n) : BitVec n := BitVec.sshiftRight x (s.toNat)
abbrev BitVec_uge { n : Nat } (x y : BitVec n) := (BitVec.ult x y).not
abbrev BitVec_sge { n : Nat } (x y : BitVec n) := (BitVec.slt x y).not
abbrev BitVec_ugt { n : Nat } (x y : BitVec n) := (BitVec.ule x y).not
abbrev BitVec_sgt { n : Nat } (x y : BitVec n) := (BitVec.sle x y).not
abbrev BitVec_zeroExtend {n : Nat} (extra : Nat) (x : BitVec n) : BitVec (n + extra) := BitVec.zeroExtend (n + extra) x
abbrev BitVec_signExtend {n : Nat} (extra : Nat) (x : BitVec n) : BitVec (n + extra) := BitVec.signExtend (n + extra) x
abbrev SmtMap (t0 t1 : Type) [Inhabited t0] [BEq t0] [Inhabited t1] : Type := t0 -> t1
abbrev SmtMap_default { t0 t1: Type } (v : t1) [Inhabited t0] [BEq t0] [Inhabited t1] : SmtMap t0 t1 := fun _ => v
abbrev SmtMap_store { t0 t1 : Type } [Inhabited t0] [BEq t0] [Inhabited t1] (m : SmtMap t0 t1) (k : t0) (v : t1) : SmtMap t0 t1 :=
  fun x => if x == k then v else m x
abbrev SmtMap_select { t0 t1 : Type } [Inhabited t0] [BEq t0] [Inhabited t1] (m : SmtMap t0 t1) (k : t0) := m k

-- LeanProofs.Flux.Struct.PatternStrSearcher
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure PatternStrSearcher  where
  mkPatternStrSearcher₀ ::
    n : Int 
    mh : (SmtMap Int Int) 
    k : Int 
    mn : (SmtMap Int Int) 
    tag : Int 
    p : Int 
    e : Int 
    crit : Int 
    critb : Int 
    period : Int 
    mem : Int 
    memb : Int 


end F

-- LeanProofs.Flux.Struct.PatternStrSearcherImpl
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure PatternStrSearcherImpl  where
  mkPatternStrSearcherImpl₀ ::
    tag : Int 
    p : Int 
    e : Int 
    crit : Int 
    critb : Int 
    period : Int 
    mem : Int 
    memb : Int 


end F

-- LeanProofs.Flux.Struct.PatternSearchStep
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure PatternSearchStep  where
  mkPatternSearchStep₀ ::
    k : Int 
    a : Int 
    b : Int 


end F

-- LeanProofs.Flux.Struct.PatternTwoWaySearcher
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure PatternTwoWaySearcher  where
  mkPatternTwoWaySearcher₀ ::
    crit : Int 
    critb : Int 
    period : Int 
    pos : Int 
    end_ : Int 
    mem : Int 
    memb : Int 


end F

-- LeanProofs.Flux.Struct.OptionOption
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure OptionOption (t0 : Type) [Inhabited t0] where
  mkOptionOption₀ ::
    is_some : Prop 
    val : t0 


end F

-- LeanProofs.Flux.Struct.PatternPair
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure PatternPair  where
  mkPatternPair₀ ::
    a : Int 
    b : Int 


end F

-- LeanProofs.Flux.Struct.Tupleₓ₀
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure Tupleₓ₀  where
  mk ::


end F

-- LeanProofs.Flux.Struct.GhostGSlice
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure GhostGSlice  where
  mkGhostGSlice₀ ::
    len : Int 
    m : (SmtMap Int Int) 


end F

-- LeanProofs.Flux.Struct.GhostGStr
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure GhostGStr  where
  mkGhostGStr₀ ::
    len : Int 
    m : (SmtMap Int Int) 


end F

-- LeanProofs.Flux.Struct.GhostGhostBytes
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure GhostGhostBytes  where
  mkGhostGhostBytes₀ ::
    m : (SmtMap Int Int) 


end F

-- LeanProofs.Flux.Struct.OpsControlFlowControlFlow
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure OpsControlFlowControlFlow  where
  mkOpsControlFlowControlFlow₀ ::
    is_continue : Prop 


end F

-- LeanProofs.Flux.Struct.OpsRangeRange
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure OpsRangeRange (t0 : Type) [Inhabited t0] where
  mkOpsRangeRange₀ ::
    start : t0 
    end_ : t0 


end F

-- LeanProofs.Flux.Struct.PatternCharSearcher
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure PatternCharSearcher  where
  mkPatternCharSearcher₀ ::
    n : Int 
    m : (SmtMap Int Int) 
    f : Int 
    b : Int 
    c : Int 


end F

-- LeanProofs.Flux.Struct.SliceIterIter
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure SliceIterIter (t0 : Type) [Inhabited t0] where
  mkSliceIterIter₀ ::
    idx : Int 
    len : Int 
    m : (SmtMap Int t0) 


end F

-- LeanProofs.User.Fun.FluxSpecsDflt
open Classical
set_option linter.unusedVariables false


namespace F

-- The structures flux generates have no `Inhabited` instance, but `OptionOption (t0 : Type) [Inhabited t0]`
-- needs one for its payload type. They are provided here (this file is ours: flux does not regenerate it, and
-- every verification condition that mentions `Option::None` imports it). Add a line when flux generates a new
-- structure that is the payload of an `Option`.
deriving instance Inhabited for GhostGSlice
deriving instance Inhabited for GhostGStr
deriving instance Inhabited for GhostGhostBytes
deriving instance Inhabited for OpsControlFlowControlFlow
deriving instance Inhabited for PatternCharSearcher
deriving instance Inhabited for PatternPair
deriving instance Inhabited for PatternSearchStep
deriving instance Inhabited for PatternStrSearcher
deriving instance Inhabited for PatternStrSearcherImpl
deriving instance Inhabited for PatternTwoWaySearcher
deriving instance Inhabited for Tupleₓ₀
deriving instance Inhabited for OpsRangeRange
deriving instance Inhabited for OptionOption
deriving instance Inhabited for SliceIterIter

-- The default payload of `None`: any element.
noncomputable def flux_specs_dflt : {t0 : Type} -> [Inhabited t0] -> Int -> t0 := fun _ => default


end F

-- LeanProofs.User.Fun.GhostUtf8Ok
open Classical
set_option linter.unusedVariables false


namespace F

-- A UTF-8 continuation byte.
def Cont (x : Int) : Prop := 0x80 ≤ x ∧ x ≤ 0xBF

-- The bytes `b0 b1 b2 b3` start with one well-formed scalar value of `k` bytes (RFC 3629, Table 3-7).
-- The bytes past the first `k` are ignored.
inductive Seq : Int → Int → Int → Int → Int → Prop
  | one {b0 b1 b2 b3 : Int} : 0 ≤ b0 → b0 ≤ 0x7F → Seq b0 b1 b2 b3 1
  | two {b0 b1 b2 b3 : Int} : 0xC2 ≤ b0 → b0 ≤ 0xDF → Cont b1 → Seq b0 b1 b2 b3 2
  | three_e0 {b0 b1 b2 b3 : Int} : b0 = 0xE0 → 0xA0 ≤ b1 → b1 ≤ 0xBF → Cont b2 → Seq b0 b1 b2 b3 3
  | three_mid {b0 b1 b2 b3 : Int} : ((0xE1 ≤ b0 ∧ b0 ≤ 0xEC) ∨ b0 = 0xEE ∨ b0 = 0xEF) →
      Cont b1 → Cont b2 → Seq b0 b1 b2 b3 3
  | three_ed {b0 b1 b2 b3 : Int} : b0 = 0xED → 0x80 ≤ b1 → b1 ≤ 0x9F → Cont b2 → Seq b0 b1 b2 b3 3
  | four_f0 {b0 b1 b2 b3 : Int} : b0 = 0xF0 → 0x90 ≤ b1 → b1 ≤ 0xBF → Cont b2 → Cont b3 →
      Seq b0 b1 b2 b3 4
  | four_mid {b0 b1 b2 b3 : Int} : 0xF1 ≤ b0 → b0 ≤ 0xF3 → Cont b1 → Cont b2 → Cont b3 →
      Seq b0 b1 b2 b3 4
  | four_f4 {b0 b1 b2 b3 : Int} : b0 = 0xF4 → 0x80 ≤ b1 → b1 ≤ 0x8F → Cont b2 → Cont b3 →
      Seq b0 b1 b2 b3 4

-- `m[a..b)` is a sequence of well-formed scalar values.
inductive Utf8 (m : SmtMap Int Int) : Int → Int → Prop
  | nil (a : Int) : Utf8 m a a
  | cons (a k b : Int) : Seq (m a) (m (a + 1)) (m (a + 2)) (m (a + 3)) k → Utf8 m (a + k) b →
      Utf8 m a b

-- `m[0..n)` is valid UTF-8.
noncomputable def ghost_utf8_ok : (SmtMap Int Int) -> Int -> Prop :=
  fun m n => Utf8 m 0 n


end F

-- LeanProofs.User.Fun.GhostMapShift
open Classical
set_option linter.unusedVariables false


namespace F

-- `m` seen from offset `k`: `ghost_map_shift m k i = m (i + k)`.
noncomputable def ghost_map_shift : (SmtMap Int Int) -> Int -> (SmtMap Int Int) :=
  fun m k i => m (i + k)


end F

-- LeanProofs.User.Fun.GhostPerOk
open Classical
set_option linter.unusedVariables false


namespace F

-- `m[lo..hi)` has period `p`.
noncomputable def ghost_per_ok : (SmtMap Int Int) -> Int -> Int -> Int -> Prop :=
  fun m lo hi p => ∀ t : Int, lo ≤ t → t + p < hi → m t = m (t + p)


end F

-- LeanProofs.User.Fun.GhostBytesEq
open Classical
set_option linter.unusedVariables false


namespace F

-- `m1[o1..o1+k)` and `m2[o2..o2+k)` are equal.
noncomputable def ghost_bytes_eq : (SmtMap Int Int) -> Int -> (SmtMap Int Int) -> Int -> Int -> Prop :=
  fun m1 o1 m2 o2 k => ∀ j : Int, 0 ≤ j → j < k → m1 (o1 + j) = m2 (o2 + j)


end F

-- LeanProofs.Flux.Fun.GhostIsBoundary
open Classical
set_option linter.unusedVariables false


namespace F

noncomputable def ghost_is_boundary (a'₄ : (SmtMap Int Int)) (a'₅ : Int) (a'₆ : Int) : Prop :=
  ((((0 ≤ a'₆) ∧ (a'₆ ≤ a'₅)) ∧ (ghost_utf8_ok a'₄ a'₆)) ∧ (ghost_utf8_ok (ghost_map_shift a'₄ a'₆) (a'₅ - a'₆)))


end F

-- LeanProofs.Flux.Fun.GhostTwStatic
open Classical
set_option linter.unusedVariables false


namespace F

noncomputable def ghost_tw_static (a'₇₃ : (SmtMap Int Int)) (a'₇₄ : Int) (a'₇₅ : Int) (a'₇₆ : Int) (a'₇₇ : Int) (a'₇₈ : Int) (a'₇₉ : Int) : Prop :=
  (((((((((1 ≤ a'₇₄) ∧ (0 ≤ a'₇₅)) ∧ (a'₇₅ ≤ a'₇₄)) ∧ (0 ≤ a'₇₆)) ∧ (a'₇₆ ≤ a'₇₄)) ∧ (1 ≤ a'₇₇)) ∧ ((0 < a'₇₅) -> (a'₇₇ ≤ a'₇₄))) ∧ ((a'₇₈ = 18446744073709551615) -> ((a'₇₉ = 18446744073709551615) ∧ (a'₇₇ ≤ a'₇₄)))) ∧ ((a'₇₈ ≠ 18446744073709551615) -> (((((a'₇₉ ≠ 18446744073709551615) ∧ (a'₇₅ ≤ a'₇₇)) ∧ (a'₇₇ ≤ a'₇₄)) ∧ (a'₇₄ ≤ (a'₇₆ + a'₇₇))) ∧ (ghost_per_ok a'₇₃ 0 a'₇₄ a'₇₇))))


end F

-- LeanProofs.Flux.Fun.GhostTwDyn
open Classical
set_option linter.unusedVariables false


namespace F

noncomputable def ghost_tw_dyn (a'₈₀ : (SmtMap Int Int)) (a'₈₁ : Int) (a'₈₂ : (SmtMap Int Int)) (a'₈₃ : Int) (a'₈₄ : Int) (a'₈₅ : Int) (a'₈₆ : Int) (a'₈₇ : Int) : Prop :=
  ((((((0 ≤ a'₈₄) ∧ (a'₈₄ ≤ a'₈₁)) ∧ (0 ≤ a'₈₅)) ∧ (a'₈₅ ≤ a'₈₁)) ∧ ((a'₈₆ ≠ 18446744073709551615) -> ((a'₈₆ ≤ a'₈₃) ∧ ((a'₈₄ = a'₈₁) ∨ (((a'₈₄ + a'₈₆) ≤ a'₈₁) ∧ (ghost_bytes_eq a'₈₀ a'₈₄ a'₈₂ 0 a'₈₆)))))) ∧ ((a'₈₇ ≠ 18446744073709551615) -> ((a'₈₇ ≤ a'₈₃) ∧ ((a'₈₅ = 0) ∨ (((a'₈₇ < a'₈₃) -> (a'₈₃ ≤ a'₈₅)) ∧ (ghost_bytes_eq a'₈₀ ((a'₈₅ - a'₈₃) + a'₈₇) a'₈₂ a'₈₇ (a'₈₃ - a'₈₇)))))))


end F

-- LeanProofs.Flux.Fun.GhostStrInv
open Classical
set_option linter.unusedVariables false


namespace F

noncomputable def ghost_str_inv (a'₅₆ : Int) (a'₅₇ : (SmtMap Int Int)) (a'₅₈ : Int) (a'₅₉ : (SmtMap Int Int)) (a'₆₀ : Int) (a'₆₁ : Int) (a'₆₂ : Int) (a'₆₃ : Int) (a'₆₄ : Int) (a'₆₅ : Int) (a'₆₆ : Int) (a'₆₇ : Int) : Prop :=
  (((((ghost_utf8_ok a'₅₇ a'₅₆) ∧ (ghost_utf8_ok a'₅₉ a'₅₈)) ∧ (ghost_is_boundary a'₅₇ a'₅₆ a'₆₁)) ∧ (ghost_is_boundary a'₅₇ a'₅₆ a'₆₂)) ∧ (if (a'₆₀ = 0) then (a'₅₈ = 0) else (((ghost_tw_static a'₅₉ a'₅₈ a'₆₃ a'₆₄ a'₆₅ a'₆₆ a'₆₇) ∧ (ghost_tw_dyn a'₅₇ a'₅₆ a'₅₉ a'₅₈ a'₆₁ a'₆₂ a'₆₆ a'₆₇)) ∧ ((a'₆₇ ≠ 18446744073709551615) -> ((a'₆₇ < a'₅₈) -> (ghost_is_boundary a'₅₉ a'₅₈ a'₆₇))))))


end F

-- LeanProofs.Flux.VC.PatternStrSearcherABAsSearcherANextMatch
open Classical
set_option linter.unusedVariables false


namespace F



def PatternStrSearcherABAsSearcherANextMatch := ∃ k4 : (a0 : Int) -> (a1 : (SmtMap Int Int)) -> (a2 : Int) -> (a3 : (SmtMap Int Int)) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : (SmtMap Int Int)) -> (a14 : Int) -> (a15 : (SmtMap Int Int)) -> (a16 : Int) -> (a17 : Int) -> (a18 : Int) -> (a19 : Int) -> (a20 : Int) -> (a21 : Int) -> (a22 : Int) -> (a23 : Int) -> (a24 : Int) -> (a25 : Int) -> Prop, ∃ k10 : (a0 : Int) -> (a1 : (SmtMap Int Int)) -> (a2 : Int) -> (a3 : (SmtMap Int Int)) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : (SmtMap Int Int)) -> (a16 : Int) -> (a17 : (SmtMap Int Int)) -> (a18 : Int) -> (a19 : Int) -> (a20 : Int) -> (a21 : Int) -> (a22 : Int) -> (a23 : Int) -> (a24 : Int) -> (a25 : Int) -> (a26 : Int) -> (a27 : (SmtMap Int Int)) -> (a28 : Int) -> (a29 : (SmtMap Int Int)) -> (a30 : Int) -> (a31 : Int) -> (a32 : Int) -> (a33 : Int) -> (a34 : Int) -> (a35 : Int) -> (a36 : Int) -> (a37 : Int) -> (a38 : Int) -> (a39 : Int) -> (a40 : Int) -> (a41 : Int) -> (a42 : Int) -> Prop, ∃ k8 : (a0 : Int) -> (a1 : Int) -> (a2 : (SmtMap Int Int)) -> (a3 : Int) -> (a4 : (SmtMap Int Int)) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> (a16 : (SmtMap Int Int)) -> (a17 : Int) -> (a18 : (SmtMap Int Int)) -> (a19 : Int) -> (a20 : Int) -> (a21 : Int) -> (a22 : Int) -> (a23 : Int) -> (a24 : Int) -> (a25 : Int) -> (a26 : Int) -> (a27 : Int) -> (a28 : (SmtMap Int Int)) -> (a29 : Int) -> (a30 : (SmtMap Int Int)) -> (a31 : Int) -> (a32 : Int) -> (a33 : Int) -> (a34 : Int) -> (a35 : Int) -> (a36 : Int) -> (a37 : Int) -> (a38 : Int) -> (a39 : Int) -> (a40 : Int) -> (a41 : Int) -> (a42 : Int) -> (a43 : Int) -> Prop, ∃ k9 : (a0 : Int) -> (a1 : Int) -> (a2 : (SmtMap Int Int)) -> (a3 : Int) -> (a4 : (SmtMap Int Int)) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> (a16 : (SmtMap Int Int)) -> (a17 : Int) -> (a18 : (SmtMap Int Int)) -> (a19 : Int) -> (a20 : Int) -> (a21 : Int) -> (a22 : Int) -> (a23 : Int) -> (a24 : Int) -> (a25 : Int) -> (a26 : Int) -> (a27 : Int) -> (a28 : (SmtMap Int Int)) -> (a29 : Int) -> (a30 : (SmtMap Int Int)) -> (a31 : Int) -> (a32 : Int) -> (a33 : Int) -> (a34 : Int) -> (a35 : Int) -> (a36 : Int) -> (a37 : Int) -> (a38 : Int) -> (a39 : Int) -> (a40 : Int) -> (a41 : Int) -> (a42 : Int) -> (a43 : Int) -> Prop, ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Prop) -> (a4 : Int) -> (a5 : (SmtMap Int Int)) -> (a6 : Int) -> (a7 : (SmtMap Int Int)) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> (a16 : Int) -> (a17 : Int) -> (a18 : Int) -> (a19 : (SmtMap Int Int)) -> (a20 : Int) -> (a21 : (SmtMap Int Int)) -> (a22 : Int) -> (a23 : Int) -> (a24 : Int) -> (a25 : Int) -> (a26 : Int) -> (a27 : Int) -> (a28 : Int) -> (a29 : Int) -> (a30 : Int) -> (a31 : (SmtMap Int Int)) -> (a32 : Int) -> (a33 : (SmtMap Int Int)) -> (a34 : Int) -> (a35 : Int) -> (a36 : Int) -> (a37 : Int) -> (a38 : Int) -> (a39 : Int) -> (a40 : Int) -> (a41 : Int) -> (a42 : Int) -> (a43 : Int) -> (a44 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Prop) -> (a4 : Int) -> (a5 : (SmtMap Int Int)) -> (a6 : Int) -> (a7 : (SmtMap Int Int)) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> (a16 : Int) -> (a17 : Int) -> (a18 : Int) -> (a19 : (SmtMap Int Int)) -> (a20 : Int) -> (a21 : (SmtMap Int Int)) -> (a22 : Int) -> (a23 : Int) -> (a24 : Int) -> (a25 : Int) -> (a26 : Int) -> (a27 : Int) -> (a28 : Int) -> (a29 : Int) -> (a30 : Int) -> (a31 : (SmtMap Int Int)) -> (a32 : Int) -> (a33 : (SmtMap Int Int)) -> (a34 : Int) -> (a35 : Int) -> (a36 : Int) -> (a37 : Int) -> (a38 : Int) -> (a39 : Int) -> (a40 : Int) -> (a41 : Int) -> (a42 : Int) -> (a43 : Int) -> (a44 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Prop) -> (a5 : Int) -> (a6 : (SmtMap Int Int)) -> (a7 : Int) -> (a8 : (SmtMap Int Int)) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> (a16 : Int) -> (a17 : Int) -> (a18 : Int) -> (a19 : Int) -> (a20 : (SmtMap Int Int)) -> (a21 : Int) -> (a22 : (SmtMap Int Int)) -> (a23 : Int) -> (a24 : Int) -> (a25 : Int) -> (a26 : Int) -> (a27 : Int) -> (a28 : Int) -> (a29 : Int) -> (a30 : Int) -> (a31 : Int) -> (a32 : (SmtMap Int Int)) -> (a33 : Int) -> (a34 : (SmtMap Int Int)) -> (a35 : Int) -> (a36 : Int) -> (a37 : Int) -> (a38 : Int) -> (a39 : Int) -> (a40 : Int) -> (a41 : Int) -> (a42 : Int) -> (a43 : Int) -> (a44 : Int) -> (a45 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Prop) -> (a5 : Int) -> (a6 : (SmtMap Int Int)) -> (a7 : Int) -> (a8 : (SmtMap Int Int)) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> (a16 : Int) -> (a17 : Int) -> (a18 : Int) -> (a19 : Int) -> (a20 : (SmtMap Int Int)) -> (a21 : Int) -> (a22 : (SmtMap Int Int)) -> (a23 : Int) -> (a24 : Int) -> (a25 : Int) -> (a26 : Int) -> (a27 : Int) -> (a28 : Int) -> (a29 : Int) -> (a30 : Int) -> (a31 : Int) -> (a32 : (SmtMap Int Int)) -> (a33 : Int) -> (a34 : (SmtMap Int Int)) -> (a35 : Int) -> (a36 : Int) -> (a37 : Int) -> (a38 : Int) -> (a39 : Int) -> (a40 : Int) -> (a41 : Int) -> (a42 : Int) -> (a43 : Int) -> (a44 : Int) -> (a45 : Int) -> Prop, ∃ k5 : (a0 : Prop) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : (SmtMap Int Int)) -> (a10 : Int) -> (a11 : (SmtMap Int Int)) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> (a16 : Int) -> (a17 : Int) -> (a18 : Int) -> (a19 : Int) -> (a20 : Int) -> (a21 : Int) -> (a22 : Int) -> (a23 : Int) -> (a24 : Int) -> (a25 : Int) -> (a26 : Int) -> (a27 : Int) -> Prop, ∃ k6 : (a0 : Int) -> (a1 : Prop) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : (SmtMap Int Int)) -> (a11 : Int) -> (a12 : (SmtMap Int Int)) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> (a16 : Int) -> (a17 : Int) -> (a18 : Int) -> (a19 : Int) -> (a20 : Int) -> (a21 : Int) -> (a22 : Int) -> (a23 : Int) -> (a24 : Int) -> (a25 : Int) -> (a26 : Int) -> (a27 : Int) -> (a28 : Int) -> Prop, ∃ k7 : (a0 : Int) -> (a1 : Prop) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : (SmtMap Int Int)) -> (a11 : Int) -> (a12 : (SmtMap Int Int)) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> (a16 : Int) -> (a17 : Int) -> (a18 : Int) -> (a19 : Int) -> (a20 : Int) -> (a21 : Int) -> (a22 : Int) -> (a23 : Int) -> (a24 : Int) -> (a25 : Int) -> (a26 : Int) -> (a27 : Int) -> (a28 : Int) -> Prop, 
 ∀ (s₀ : PatternStrSearcher),
  ((ghost_str_inv (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀))) ->
   ((0 ≤ (PatternStrSearcher.n s₀)) ∧ ((PatternStrSearcher.n s₀) ≤ 9223372036854775807) ∧ (ghost_utf8_ok (PatternStrSearcher.mh s₀) (PatternStrSearcher.n s₀))) ->
    ((0 ≤ (PatternStrSearcher.k s₀)) ∧ ((PatternStrSearcher.k s₀) ≤ 9223372036854775807) ∧ (ghost_utf8_ok (PatternStrSearcher.mn s₀) (PatternStrSearcher.k s₀))) ->
     (∀ (p₀ : Int),
      ∀ (e₀ : Int),
       (((PatternStrSearcherImpl.mkPatternStrSearcherImpl₀ (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀)) = (PatternStrSearcherImpl.mkPatternStrSearcherImpl₀ 0 p₀ e₀ 0 0 0 0 0))) ->
        ((k4 (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) 0 p₀ e₀ 0 0 0 0 0 (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀) p₀ e₀)) ∧
        (∀ (a'₃ : PatternStrSearcher),
         ((k4 (PatternStrSearcher.n a'₃) (PatternStrSearcher.mh a'₃) (PatternStrSearcher.k a'₃) (PatternStrSearcher.mn a'₃) (PatternStrSearcher.tag a'₃) (PatternStrSearcher.p a'₃) (PatternStrSearcher.e a'₃) (PatternStrSearcher.crit a'₃) (PatternStrSearcher.critb a'₃) (PatternStrSearcher.period a'₃) (PatternStrSearcher.mem a'₃) (PatternStrSearcher.memb a'₃) (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀) p₀ e₀)) ->
          ((ghost_str_inv (PatternStrSearcher.n a'₃) (PatternStrSearcher.mh a'₃) (PatternStrSearcher.k a'₃) (PatternStrSearcher.mn a'₃) (PatternStrSearcher.tag a'₃) (PatternStrSearcher.p a'₃) (PatternStrSearcher.e a'₃) (PatternStrSearcher.crit a'₃) (PatternStrSearcher.critb a'₃) (PatternStrSearcher.period a'₃) (PatternStrSearcher.mem a'₃) (PatternStrSearcher.memb a'₃))) ∧
          (∀ (t₀ : PatternStrSearcher),
           (((PatternStrSearcher.n t₀) = (PatternStrSearcher.n a'₃)) ∧ ((PatternStrSearcher.mh t₀) = (PatternStrSearcher.mh a'₃)) ∧ ((PatternStrSearcher.k t₀) = (PatternStrSearcher.k a'₃)) ∧ ((PatternStrSearcher.mn t₀) = (PatternStrSearcher.mn a'₃)) ∧ (ghost_str_inv (PatternStrSearcher.n t₀) (PatternStrSearcher.mh t₀) (PatternStrSearcher.k t₀) (PatternStrSearcher.mn t₀) (PatternStrSearcher.tag t₀) (PatternStrSearcher.p t₀) (PatternStrSearcher.e t₀) (PatternStrSearcher.crit t₀) (PatternStrSearcher.critb t₀) (PatternStrSearcher.period t₀) (PatternStrSearcher.mem t₀) (PatternStrSearcher.memb t₀))) ->
            ∀ (r₀ : PatternSearchStep),
             (((((PatternSearchStep.k r₀) = 0) ∨ ((PatternSearchStep.k r₀) = 1)) -> (((((PatternSearchStep.a r₀) ≤ (PatternSearchStep.b r₀)) ∧ ((PatternSearchStep.b r₀) ≤ (PatternStrSearcher.n a'₃))) ∧ (ghost_is_boundary (PatternStrSearcher.mh a'₃) (PatternStrSearcher.n a'₃) (PatternSearchStep.a r₀))) ∧ (ghost_is_boundary (PatternStrSearcher.mh a'₃) (PatternStrSearcher.n a'₃) (PatternSearchStep.b r₀))))) ->
              (∀ (a₀ : Int),
               ∀ (b₀ : Int),
                ((r₀ = (PatternSearchStep.mkPatternSearchStep₀ 0 a₀ b₀))) ->
                 ((a₀ ≥ 0)) ->
                  ((a₀ ≤ 18446744073709551615)) ->
                   ((b₀ ≥ 0)) ->
                    ((b₀ ≤ 18446744073709551615)) ->
                     ((k10 (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀) p₀ e₀ (PatternStrSearcher.n a'₃) (PatternStrSearcher.mh a'₃) (PatternStrSearcher.k a'₃) (PatternStrSearcher.mn a'₃) (PatternStrSearcher.tag a'₃) (PatternStrSearcher.p a'₃) (PatternStrSearcher.e a'₃) (PatternStrSearcher.crit a'₃) (PatternStrSearcher.critb a'₃) (PatternStrSearcher.period a'₃) (PatternStrSearcher.mem a'₃) (PatternStrSearcher.memb a'₃) (PatternStrSearcher.n t₀) (PatternStrSearcher.mh t₀) (PatternStrSearcher.k t₀) (PatternStrSearcher.mn t₀) (PatternStrSearcher.tag t₀) (PatternStrSearcher.p t₀) (PatternStrSearcher.e t₀) (PatternStrSearcher.crit t₀) (PatternStrSearcher.critb t₀) (PatternStrSearcher.period t₀) (PatternStrSearcher.mem t₀) (PatternStrSearcher.memb t₀) (PatternSearchStep.k r₀) (PatternSearchStep.a r₀) (PatternSearchStep.b r₀) a₀ b₀)) ∧
                     ((k8 a₀ (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀) p₀ e₀ (PatternStrSearcher.n a'₃) (PatternStrSearcher.mh a'₃) (PatternStrSearcher.k a'₃) (PatternStrSearcher.mn a'₃) (PatternStrSearcher.tag a'₃) (PatternStrSearcher.p a'₃) (PatternStrSearcher.e a'₃) (PatternStrSearcher.crit a'₃) (PatternStrSearcher.critb a'₃) (PatternStrSearcher.period a'₃) (PatternStrSearcher.mem a'₃) (PatternStrSearcher.memb a'₃) (PatternStrSearcher.n t₀) (PatternStrSearcher.mh t₀) (PatternStrSearcher.k t₀) (PatternStrSearcher.mn t₀) (PatternStrSearcher.tag t₀) (PatternStrSearcher.p t₀) (PatternStrSearcher.e t₀) (PatternStrSearcher.crit t₀) (PatternStrSearcher.critb t₀) (PatternStrSearcher.period t₀) (PatternStrSearcher.mem t₀) (PatternStrSearcher.memb t₀) (PatternSearchStep.k r₀) (PatternSearchStep.a r₀) (PatternSearchStep.b r₀) a₀ b₀)) ∧
                     ((k9 b₀ (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀) p₀ e₀ (PatternStrSearcher.n a'₃) (PatternStrSearcher.mh a'₃) (PatternStrSearcher.k a'₃) (PatternStrSearcher.mn a'₃) (PatternStrSearcher.tag a'₃) (PatternStrSearcher.p a'₃) (PatternStrSearcher.e a'₃) (PatternStrSearcher.crit a'₃) (PatternStrSearcher.critb a'₃) (PatternStrSearcher.period a'₃) (PatternStrSearcher.mem a'₃) (PatternStrSearcher.memb a'₃) (PatternStrSearcher.n t₀) (PatternStrSearcher.mh t₀) (PatternStrSearcher.k t₀) (PatternStrSearcher.mn t₀) (PatternStrSearcher.tag t₀) (PatternStrSearcher.p t₀) (PatternStrSearcher.e t₀) (PatternStrSearcher.crit t₀) (PatternStrSearcher.critb t₀) (PatternStrSearcher.period t₀) (PatternStrSearcher.mem t₀) (PatternStrSearcher.memb t₀) (PatternSearchStep.k r₀) (PatternSearchStep.a r₀) (PatternSearchStep.b r₀) a₀ b₀)) ∧
                     ((k0 0 a₀ b₀ True (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀) p₀ e₀ (PatternStrSearcher.n a'₃) (PatternStrSearcher.mh a'₃) (PatternStrSearcher.k a'₃) (PatternStrSearcher.mn a'₃) (PatternStrSearcher.tag a'₃) (PatternStrSearcher.p a'₃) (PatternStrSearcher.e a'₃) (PatternStrSearcher.crit a'₃) (PatternStrSearcher.critb a'₃) (PatternStrSearcher.period a'₃) (PatternStrSearcher.mem a'₃) (PatternStrSearcher.memb a'₃) (PatternStrSearcher.n t₀) (PatternStrSearcher.mh t₀) (PatternStrSearcher.k t₀) (PatternStrSearcher.mn t₀) (PatternStrSearcher.tag t₀) (PatternStrSearcher.p t₀) (PatternStrSearcher.e t₀) (PatternStrSearcher.crit t₀) (PatternStrSearcher.critb t₀) (PatternStrSearcher.period t₀) (PatternStrSearcher.mem t₀) (PatternStrSearcher.memb t₀) (PatternSearchStep.k r₀) (PatternSearchStep.a r₀) (PatternSearchStep.b r₀))) ∧
                     (((k10 (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀) p₀ e₀ (PatternStrSearcher.n a'₃) (PatternStrSearcher.mh a'₃) (PatternStrSearcher.k a'₃) (PatternStrSearcher.mn a'₃) (PatternStrSearcher.tag a'₃) (PatternStrSearcher.p a'₃) (PatternStrSearcher.e a'₃) (PatternStrSearcher.crit a'₃) (PatternStrSearcher.critb a'₃) (PatternStrSearcher.period a'₃) (PatternStrSearcher.mem a'₃) (PatternStrSearcher.memb a'₃) (PatternStrSearcher.n t₀) (PatternStrSearcher.mh t₀) (PatternStrSearcher.k t₀) (PatternStrSearcher.mn t₀) (PatternStrSearcher.tag t₀) (PatternStrSearcher.p t₀) (PatternStrSearcher.e t₀) (PatternStrSearcher.crit t₀) (PatternStrSearcher.critb t₀) (PatternStrSearcher.period t₀) (PatternStrSearcher.mem t₀) (PatternStrSearcher.memb t₀) (PatternSearchStep.k r₀) (PatternSearchStep.a r₀) (PatternSearchStep.b r₀) a₀ b₀)) ->
                      ∀ (a'₈ : Int),
                       ((k8 a'₈ (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀) p₀ e₀ (PatternStrSearcher.n a'₃) (PatternStrSearcher.mh a'₃) (PatternStrSearcher.k a'₃) (PatternStrSearcher.mn a'₃) (PatternStrSearcher.tag a'₃) (PatternStrSearcher.p a'₃) (PatternStrSearcher.e a'₃) (PatternStrSearcher.crit a'₃) (PatternStrSearcher.critb a'₃) (PatternStrSearcher.period a'₃) (PatternStrSearcher.mem a'₃) (PatternStrSearcher.memb a'₃) (PatternStrSearcher.n t₀) (PatternStrSearcher.mh t₀) (PatternStrSearcher.k t₀) (PatternStrSearcher.mn t₀) (PatternStrSearcher.tag t₀) (PatternStrSearcher.p t₀) (PatternStrSearcher.e t₀) (PatternStrSearcher.crit t₀) (PatternStrSearcher.critb t₀) (PatternStrSearcher.period t₀) (PatternStrSearcher.mem t₀) (PatternStrSearcher.memb t₀) (PatternSearchStep.k r₀) (PatternSearchStep.a r₀) (PatternSearchStep.b r₀) a₀ b₀)) ->
                        ∀ (a'₉ : Int),
                         ((k9 a'₉ (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀) p₀ e₀ (PatternStrSearcher.n a'₃) (PatternStrSearcher.mh a'₃) (PatternStrSearcher.k a'₃) (PatternStrSearcher.mn a'₃) (PatternStrSearcher.tag a'₃) (PatternStrSearcher.p a'₃) (PatternStrSearcher.e a'₃) (PatternStrSearcher.crit a'₃) (PatternStrSearcher.critb a'₃) (PatternStrSearcher.period a'₃) (PatternStrSearcher.mem a'₃) (PatternStrSearcher.memb a'₃) (PatternStrSearcher.n t₀) (PatternStrSearcher.mh t₀) (PatternStrSearcher.k t₀) (PatternStrSearcher.mn t₀) (PatternStrSearcher.tag t₀) (PatternStrSearcher.p t₀) (PatternStrSearcher.e t₀) (PatternStrSearcher.crit t₀) (PatternStrSearcher.critb t₀) (PatternStrSearcher.period t₀) (PatternStrSearcher.mem t₀) (PatternStrSearcher.memb t₀) (PatternSearchStep.k r₀) (PatternSearchStep.a r₀) (PatternSearchStep.b r₀) a₀ b₀)) ->
                          ((k3 0 a₀ b₀ True (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀) p₀ e₀ (PatternStrSearcher.n a'₃) (PatternStrSearcher.mh a'₃) (PatternStrSearcher.k a'₃) (PatternStrSearcher.mn a'₃) (PatternStrSearcher.tag a'₃) (PatternStrSearcher.p a'₃) (PatternStrSearcher.e a'₃) (PatternStrSearcher.crit a'₃) (PatternStrSearcher.critb a'₃) (PatternStrSearcher.period a'₃) (PatternStrSearcher.mem a'₃) (PatternStrSearcher.memb a'₃) (PatternStrSearcher.n t₀) (PatternStrSearcher.mh t₀) (PatternStrSearcher.k t₀) (PatternStrSearcher.mn t₀) (PatternStrSearcher.tag t₀) (PatternStrSearcher.p t₀) (PatternStrSearcher.e t₀) (PatternStrSearcher.crit t₀) (PatternStrSearcher.critb t₀) (PatternStrSearcher.period t₀) (PatternStrSearcher.mem t₀) (PatternStrSearcher.memb t₀) (PatternSearchStep.k r₀) (PatternSearchStep.a r₀) (PatternSearchStep.b r₀))) ∧
                          ((k1 a'₈ 0 a₀ b₀ True (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀) p₀ e₀ (PatternStrSearcher.n a'₃) (PatternStrSearcher.mh a'₃) (PatternStrSearcher.k a'₃) (PatternStrSearcher.mn a'₃) (PatternStrSearcher.tag a'₃) (PatternStrSearcher.p a'₃) (PatternStrSearcher.e a'₃) (PatternStrSearcher.crit a'₃) (PatternStrSearcher.critb a'₃) (PatternStrSearcher.period a'₃) (PatternStrSearcher.mem a'₃) (PatternStrSearcher.memb a'₃) (PatternStrSearcher.n t₀) (PatternStrSearcher.mh t₀) (PatternStrSearcher.k t₀) (PatternStrSearcher.mn t₀) (PatternStrSearcher.tag t₀) (PatternStrSearcher.p t₀) (PatternStrSearcher.e t₀) (PatternStrSearcher.crit t₀) (PatternStrSearcher.critb t₀) (PatternStrSearcher.period t₀) (PatternStrSearcher.mem t₀) (PatternStrSearcher.memb t₀) (PatternSearchStep.k r₀) (PatternSearchStep.a r₀) (PatternSearchStep.b r₀))) ∧
                          ((k2 a'₉ 0 a₀ b₀ True (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀) p₀ e₀ (PatternStrSearcher.n a'₃) (PatternStrSearcher.mh a'₃) (PatternStrSearcher.k a'₃) (PatternStrSearcher.mn a'₃) (PatternStrSearcher.tag a'₃) (PatternStrSearcher.p a'₃) (PatternStrSearcher.e a'₃) (PatternStrSearcher.crit a'₃) (PatternStrSearcher.critb a'₃) (PatternStrSearcher.period a'₃) (PatternStrSearcher.mem a'₃) (PatternStrSearcher.memb a'₃) (PatternStrSearcher.n t₀) (PatternStrSearcher.mh t₀) (PatternStrSearcher.k t₀) (PatternStrSearcher.mn t₀) (PatternStrSearcher.tag t₀) (PatternStrSearcher.p t₀) (PatternStrSearcher.e t₀) (PatternStrSearcher.crit t₀) (PatternStrSearcher.critb t₀) (PatternStrSearcher.period t₀) (PatternStrSearcher.mem t₀) (PatternStrSearcher.memb t₀) (PatternSearchStep.k r₀) (PatternSearchStep.a r₀) (PatternSearchStep.b r₀)))
                          )
                     ) ∧
              (∀ (a₁ : Int),
               ∀ (b₁ : Int),
                ((r₀ = (PatternSearchStep.mkPatternSearchStep₀ 1 a₁ b₁))) ->
                 ((a₁ ≥ 0)) ->
                  ((a₁ ≤ 18446744073709551615)) ->
                   ((b₁ ≥ 0)) ->
                    ((b₁ ≤ 18446744073709551615)) ->
                     (k4 (PatternStrSearcher.n t₀) (PatternStrSearcher.mh t₀) (PatternStrSearcher.k t₀) (PatternStrSearcher.mn t₀) (PatternStrSearcher.tag t₀) (PatternStrSearcher.p t₀) (PatternStrSearcher.e t₀) (PatternStrSearcher.crit t₀) (PatternStrSearcher.critb t₀) (PatternStrSearcher.period t₀) (PatternStrSearcher.mem t₀) (PatternStrSearcher.memb t₀) (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀) p₀ e₀)) ∧
              (((r₀ = (PatternSearchStep.mkPatternSearchStep₀ 2 0 0))) ->
               (k0 2 0 0 False (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀) p₀ e₀ (PatternStrSearcher.n a'₃) (PatternStrSearcher.mh a'₃) (PatternStrSearcher.k a'₃) (PatternStrSearcher.mn a'₃) (PatternStrSearcher.tag a'₃) (PatternStrSearcher.p a'₃) (PatternStrSearcher.e a'₃) (PatternStrSearcher.crit a'₃) (PatternStrSearcher.critb a'₃) (PatternStrSearcher.period a'₃) (PatternStrSearcher.mem a'₃) (PatternStrSearcher.memb a'₃) (PatternStrSearcher.n t₀) (PatternStrSearcher.mh t₀) (PatternStrSearcher.k t₀) (PatternStrSearcher.mn t₀) (PatternStrSearcher.tag t₀) (PatternStrSearcher.p t₀) (PatternStrSearcher.e t₀) (PatternStrSearcher.crit t₀) (PatternStrSearcher.critb t₀) (PatternStrSearcher.period t₀) (PatternStrSearcher.mem t₀) (PatternStrSearcher.memb t₀) (PatternSearchStep.k r₀) (PatternSearchStep.a r₀) (PatternSearchStep.b r₀))) ∧
              (∀ (a'₁₂ : PatternSearchStep),
               ∀ (a'₁₃ : Prop),
                ∀ (a'₁₄ : Tupleₓ₀),
                 ((k0 (PatternSearchStep.k a'₁₂) (PatternSearchStep.a a'₁₂) (PatternSearchStep.b a'₁₂) a'₁₃ (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀) p₀ e₀ (PatternStrSearcher.n a'₃) (PatternStrSearcher.mh a'₃) (PatternStrSearcher.k a'₃) (PatternStrSearcher.mn a'₃) (PatternStrSearcher.tag a'₃) (PatternStrSearcher.p a'₃) (PatternStrSearcher.e a'₃) (PatternStrSearcher.crit a'₃) (PatternStrSearcher.critb a'₃) (PatternStrSearcher.period a'₃) (PatternStrSearcher.mem a'₃) (PatternStrSearcher.memb a'₃) (PatternStrSearcher.n t₀) (PatternStrSearcher.mh t₀) (PatternStrSearcher.k t₀) (PatternStrSearcher.mn t₀) (PatternStrSearcher.tag t₀) (PatternStrSearcher.p t₀) (PatternStrSearcher.e t₀) (PatternStrSearcher.crit t₀) (PatternStrSearcher.critb t₀) (PatternStrSearcher.period t₀) (PatternStrSearcher.mem t₀) (PatternStrSearcher.memb t₀) (PatternSearchStep.k r₀) (PatternSearchStep.a r₀) (PatternSearchStep.b r₀))) ->
                  (((k3 (PatternSearchStep.k a'₁₂) (PatternSearchStep.a a'₁₂) (PatternSearchStep.b a'₁₂) a'₁₃ (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀) p₀ e₀ (PatternStrSearcher.n a'₃) (PatternStrSearcher.mh a'₃) (PatternStrSearcher.k a'₃) (PatternStrSearcher.mn a'₃) (PatternStrSearcher.tag a'₃) (PatternStrSearcher.p a'₃) (PatternStrSearcher.e a'₃) (PatternStrSearcher.crit a'₃) (PatternStrSearcher.critb a'₃) (PatternStrSearcher.period a'₃) (PatternStrSearcher.mem a'₃) (PatternStrSearcher.memb a'₃) (PatternStrSearcher.n t₀) (PatternStrSearcher.mh t₀) (PatternStrSearcher.k t₀) (PatternStrSearcher.mn t₀) (PatternStrSearcher.tag t₀) (PatternStrSearcher.p t₀) (PatternStrSearcher.e t₀) (PatternStrSearcher.crit t₀) (PatternStrSearcher.critb t₀) (PatternStrSearcher.period t₀) (PatternStrSearcher.mem t₀) (PatternStrSearcher.memb t₀) (PatternSearchStep.k r₀) (PatternSearchStep.a r₀) (PatternSearchStep.b r₀))) ->
                   ∀ (a'₁₅ : Int),
                    ((k1 a'₁₅ (PatternSearchStep.k a'₁₂) (PatternSearchStep.a a'₁₂) (PatternSearchStep.b a'₁₂) a'₁₃ (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀) p₀ e₀ (PatternStrSearcher.n a'₃) (PatternStrSearcher.mh a'₃) (PatternStrSearcher.k a'₃) (PatternStrSearcher.mn a'₃) (PatternStrSearcher.tag a'₃) (PatternStrSearcher.p a'₃) (PatternStrSearcher.e a'₃) (PatternStrSearcher.crit a'₃) (PatternStrSearcher.critb a'₃) (PatternStrSearcher.period a'₃) (PatternStrSearcher.mem a'₃) (PatternStrSearcher.memb a'₃) (PatternStrSearcher.n t₀) (PatternStrSearcher.mh t₀) (PatternStrSearcher.k t₀) (PatternStrSearcher.mn t₀) (PatternStrSearcher.tag t₀) (PatternStrSearcher.p t₀) (PatternStrSearcher.e t₀) (PatternStrSearcher.crit t₀) (PatternStrSearcher.critb t₀) (PatternStrSearcher.period t₀) (PatternStrSearcher.mem t₀) (PatternStrSearcher.memb t₀) (PatternSearchStep.k r₀) (PatternSearchStep.a r₀) (PatternSearchStep.b r₀))) ->
                     ∀ (a'₁₆ : Int),
                      ((k2 a'₁₆ (PatternSearchStep.k a'₁₂) (PatternSearchStep.a a'₁₂) (PatternSearchStep.b a'₁₂) a'₁₃ (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀) p₀ e₀ (PatternStrSearcher.n a'₃) (PatternStrSearcher.mh a'₃) (PatternStrSearcher.k a'₃) (PatternStrSearcher.mn a'₃) (PatternStrSearcher.tag a'₃) (PatternStrSearcher.p a'₃) (PatternStrSearcher.e a'₃) (PatternStrSearcher.crit a'₃) (PatternStrSearcher.critb a'₃) (PatternStrSearcher.period a'₃) (PatternStrSearcher.mem a'₃) (PatternStrSearcher.memb a'₃) (PatternStrSearcher.n t₀) (PatternStrSearcher.mh t₀) (PatternStrSearcher.k t₀) (PatternStrSearcher.mn t₀) (PatternStrSearcher.tag t₀) (PatternStrSearcher.p t₀) (PatternStrSearcher.e t₀) (PatternStrSearcher.crit t₀) (PatternStrSearcher.critb t₀) (PatternStrSearcher.period t₀) (PatternStrSearcher.mem t₀) (PatternStrSearcher.memb t₀) (PatternSearchStep.k r₀) (PatternSearchStep.a r₀) (PatternSearchStep.b r₀))) ->
                       (((a'₁₅ ≤ (PatternStrSearcher.n s₀))) ∧
                       ((ghost_is_boundary (PatternStrSearcher.mh s₀) (PatternStrSearcher.n s₀) a'₁₅))
                       ) ∧
                       (((a'₁₆ ≤ (PatternStrSearcher.n s₀))) ∧
                       ((ghost_is_boundary (PatternStrSearcher.mh s₀) (PatternStrSearcher.n s₀) a'₁₆))
                       )
                       ) ∧
                  ((((PatternStrSearcher.n t₀) = (PatternStrSearcher.n s₀))) ∧
                  (((PatternStrSearcher.mh t₀) = (PatternStrSearcher.mh s₀))) ∧
                  (((PatternStrSearcher.k t₀) = (PatternStrSearcher.k s₀))) ∧
                  (((PatternStrSearcher.mn t₀) = (PatternStrSearcher.mn s₀)))
                  )
                  )
              )
          )
        ) ∧
     (∀ (crit₀ : Int),
      ∀ (critb₀ : Int),
       ∀ (period₀ : Int),
        ∀ (p₁ : Int),
         ∀ (e₁ : Int),
          ∀ (mem₀ : Int),
           ∀ (memb₀ : Int),
            (((PatternStrSearcherImpl.mkPatternStrSearcherImpl₀ (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀)) = (PatternStrSearcherImpl.mkPatternStrSearcherImpl₀ 1 p₁ e₁ crit₀ critb₀ period₀ mem₀ memb₀))) ->
             ((crit₀ ≥ 0)) ->
              ((crit₀ ≤ 18446744073709551615)) ->
               ((critb₀ ≥ 0)) ->
                ((critb₀ ≤ 18446744073709551615)) ->
                 ((period₀ ≥ 0)) ->
                  ((period₀ ≤ 18446744073709551615)) ->
                   ∀ (a'₂₄ : Int),
                    ((a'₂₄ ≥ 0)) ->
                     ((a'₂₄ ≤ 18446744073709551615)) ->
                      ((p₁ ≥ 0)) ->
                       ((p₁ ≤ 18446744073709551615)) ->
                        ((e₁ ≥ 0)) ->
                         ((e₁ ≤ 18446744073709551615)) ->
                          ((mem₀ ≥ 0)) ->
                           ((mem₀ ≤ 18446744073709551615)) ->
                            ((memb₀ ≥ 0)) ->
                             ((memb₀ ≤ 18446744073709551615)) ->
                              (((mem₀ ≠ 18446744073709551615)) ->
                               (((ghost_tw_static (PatternStrSearcher.mn s₀) (PatternStrSearcher.k s₀) crit₀ critb₀ period₀ mem₀ memb₀)) ∧
                               ((ghost_tw_dyn (PatternStrSearcher.mh s₀) (PatternStrSearcher.n s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.k s₀) p₁ e₁ mem₀ memb₀)) ∧
                               ((False <-> (mem₀ = 18446744073709551615)))
                               ) ∧
                               (∀ (r₁ : (OptionOption PatternPair)),
                                ∀ (t₁ : PatternTwoWaySearcher),
                                 (((PatternTwoWaySearcher.crit t₁) = crit₀) ∧ ((PatternTwoWaySearcher.critb t₁) = critb₀) ∧ ((PatternTwoWaySearcher.period t₁) = period₀) ∧ ((PatternTwoWaySearcher.end_ t₁) = e₁) ∧ (((PatternTwoWaySearcher.mem t₁) = 18446744073709551615) <-> (mem₀ = 18446744073709551615)) ∧ ((PatternTwoWaySearcher.memb t₁) = memb₀) ∧ (ghost_tw_dyn (PatternStrSearcher.mh s₀) (PatternStrSearcher.n s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.k s₀) (PatternTwoWaySearcher.pos t₁) (PatternTwoWaySearcher.end_ t₁) (PatternTwoWaySearcher.mem t₁) (PatternTwoWaySearcher.memb t₁)) ∧ (p₁ ≤ (PatternTwoWaySearcher.pos t₁)) ∧ ((((if (OptionOption.is_some r₁) then 0 else 2) = 0) ∨ ((if (OptionOption.is_some r₁) then 0 else 2) = 1)) -> ((PatternTwoWaySearcher.pos t₁) = (PatternPair.b (OptionOption.val r₁)))) ∧ ((((if (OptionOption.is_some r₁) then 0 else 2) ≠ 0) ∧ ((if (OptionOption.is_some r₁) then 0 else 2) ≠ 1)) -> ((PatternTwoWaySearcher.pos t₁) = (PatternStrSearcher.n s₀)))) ->
                                  ((False -> (((if (OptionOption.is_some r₁) then 0 else 2) = 0) ∨ ((if (OptionOption.is_some r₁) then 0 else 2) = 1)))) ->
                                   ((((if (OptionOption.is_some r₁) then 0 else 2) = 0) -> (((((ghost_bytes_eq (PatternStrSearcher.mh s₀) (PatternPair.a (OptionOption.val r₁)) (PatternStrSearcher.mn s₀) 0 (PatternStrSearcher.k s₀)) ∧ ((PatternPair.b (OptionOption.val r₁)) = ((PatternPair.a (OptionOption.val r₁)) + (PatternStrSearcher.k s₀)))) ∧ ((PatternPair.b (OptionOption.val r₁)) ≤ (PatternStrSearcher.n s₀))) ∧ (p₁ ≤ (PatternPair.a (OptionOption.val r₁)))) ∧ (False -> ((PatternPair.a (OptionOption.val r₁)) = p₁))))) ->
                                    ((((if (OptionOption.is_some r₁) then 0 else 2) = 1) -> (((((PatternPair.a (OptionOption.val r₁)) = p₁) ∧ ((PatternPair.a (OptionOption.val r₁)) ≤ (PatternPair.b (OptionOption.val r₁)))) ∧ ((PatternPair.b (OptionOption.val r₁)) ≤ (PatternStrSearcher.n s₀))) ∧ (False ∨ ((PatternPair.b (OptionOption.val r₁)) = (PatternStrSearcher.n s₀)))))) ->
                                     (((1 ≤ (PatternStrSearcher.k s₀))) ∧
                                     (((OptionOption.is_some r₁) -> (((ghost_bytes_eq (PatternStrSearcher.mh s₀) (PatternPair.a (OptionOption.val r₁)) (PatternStrSearcher.mn s₀) 0 (PatternStrSearcher.k s₀)) ∧ ((PatternPair.b (OptionOption.val r₁)) = ((PatternPair.a (OptionOption.val r₁)) + (PatternStrSearcher.k s₀)))) ∧ ((PatternPair.b (OptionOption.val r₁)) ≤ (PatternStrSearcher.n s₀)))))
                                     ) ∧
                                     (∀ (o₀ : (OptionOption Tupleₓ₀)),
                                      (((OptionOption.is_some o₀) = (OptionOption.is_some r₁)) ∧ ((¬(OptionOption.is_some o₀)) -> ((OptionOption.val o₀) = (flux_specs_dflt (t0 := Tupleₓ₀) 0)))) ->
                                       ((k5 (OptionOption.is_some o₀) (PatternTwoWaySearcher.crit t₁) (PatternTwoWaySearcher.critb t₁) (PatternTwoWaySearcher.period t₁) (PatternTwoWaySearcher.pos t₁) (PatternTwoWaySearcher.end_ t₁) (PatternTwoWaySearcher.mem t₁) (PatternTwoWaySearcher.memb t₁) (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀) crit₀ critb₀ period₀ p₁ e₁ mem₀ memb₀ a'₂₄)) ∧
                                       (∀ (x₀ : Int),
                                        ((x₀ ≤ (PatternStrSearcher.n s₀)) ∧ (ghost_is_boundary (PatternStrSearcher.mh s₀) (PatternStrSearcher.n s₀) x₀)) ->
                                         ∀ (y₀ : Int),
                                          ((y₀ ≤ (PatternStrSearcher.n s₀)) ∧ (ghost_is_boundary (PatternStrSearcher.mh s₀) (PatternStrSearcher.n s₀) y₀)) ->
                                           ((k6 x₀ (OptionOption.is_some o₀) (PatternTwoWaySearcher.crit t₁) (PatternTwoWaySearcher.critb t₁) (PatternTwoWaySearcher.period t₁) (PatternTwoWaySearcher.pos t₁) (PatternTwoWaySearcher.end_ t₁) (PatternTwoWaySearcher.mem t₁) (PatternTwoWaySearcher.memb t₁) (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀) crit₀ critb₀ period₀ p₁ e₁ mem₀ memb₀ a'₂₄)) ∧
                                           ((k7 y₀ (OptionOption.is_some o₀) (PatternTwoWaySearcher.crit t₁) (PatternTwoWaySearcher.critb t₁) (PatternTwoWaySearcher.period t₁) (PatternTwoWaySearcher.pos t₁) (PatternTwoWaySearcher.end_ t₁) (PatternTwoWaySearcher.mem t₁) (PatternTwoWaySearcher.memb t₁) (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀) crit₀ critb₀ period₀ p₁ e₁ mem₀ memb₀ a'₂₄))
                                           )
                                       )
                                     )
                               ) ∧
                              (((¬(mem₀ ≠ 18446744073709551615))) ->
                               (((ghost_tw_static (PatternStrSearcher.mn s₀) (PatternStrSearcher.k s₀) crit₀ critb₀ period₀ mem₀ memb₀)) ∧
                               ((ghost_tw_dyn (PatternStrSearcher.mh s₀) (PatternStrSearcher.n s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.k s₀) p₁ e₁ mem₀ memb₀)) ∧
                               ((True <-> (mem₀ = 18446744073709551615)))
                               ) ∧
                               (∀ (r₂ : (OptionOption PatternPair)),
                                ∀ (t₂ : PatternTwoWaySearcher),
                                 (((PatternTwoWaySearcher.crit t₂) = crit₀) ∧ ((PatternTwoWaySearcher.critb t₂) = critb₀) ∧ ((PatternTwoWaySearcher.period t₂) = period₀) ∧ ((PatternTwoWaySearcher.end_ t₂) = e₁) ∧ (((PatternTwoWaySearcher.mem t₂) = 18446744073709551615) <-> (mem₀ = 18446744073709551615)) ∧ ((PatternTwoWaySearcher.memb t₂) = memb₀) ∧ (ghost_tw_dyn (PatternStrSearcher.mh s₀) (PatternStrSearcher.n s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.k s₀) (PatternTwoWaySearcher.pos t₂) (PatternTwoWaySearcher.end_ t₂) (PatternTwoWaySearcher.mem t₂) (PatternTwoWaySearcher.memb t₂)) ∧ (p₁ ≤ (PatternTwoWaySearcher.pos t₂)) ∧ ((((if (OptionOption.is_some r₂) then 0 else 2) = 0) ∨ ((if (OptionOption.is_some r₂) then 0 else 2) = 1)) -> ((PatternTwoWaySearcher.pos t₂) = (PatternPair.b (OptionOption.val r₂)))) ∧ ((((if (OptionOption.is_some r₂) then 0 else 2) ≠ 0) ∧ ((if (OptionOption.is_some r₂) then 0 else 2) ≠ 1)) -> ((PatternTwoWaySearcher.pos t₂) = (PatternStrSearcher.n s₀)))) ->
                                  ((False -> (((if (OptionOption.is_some r₂) then 0 else 2) = 0) ∨ ((if (OptionOption.is_some r₂) then 0 else 2) = 1)))) ->
                                   ((((if (OptionOption.is_some r₂) then 0 else 2) = 0) -> (((((ghost_bytes_eq (PatternStrSearcher.mh s₀) (PatternPair.a (OptionOption.val r₂)) (PatternStrSearcher.mn s₀) 0 (PatternStrSearcher.k s₀)) ∧ ((PatternPair.b (OptionOption.val r₂)) = ((PatternPair.a (OptionOption.val r₂)) + (PatternStrSearcher.k s₀)))) ∧ ((PatternPair.b (OptionOption.val r₂)) ≤ (PatternStrSearcher.n s₀))) ∧ (p₁ ≤ (PatternPair.a (OptionOption.val r₂)))) ∧ (False -> ((PatternPair.a (OptionOption.val r₂)) = p₁))))) ->
                                    ((((if (OptionOption.is_some r₂) then 0 else 2) = 1) -> (((((PatternPair.a (OptionOption.val r₂)) = p₁) ∧ ((PatternPair.a (OptionOption.val r₂)) ≤ (PatternPair.b (OptionOption.val r₂)))) ∧ ((PatternPair.b (OptionOption.val r₂)) ≤ (PatternStrSearcher.n s₀))) ∧ (False ∨ ((PatternPair.b (OptionOption.val r₂)) = (PatternStrSearcher.n s₀)))))) ->
                                     (((1 ≤ (PatternStrSearcher.k s₀))) ∧
                                     (((OptionOption.is_some r₂) -> (((ghost_bytes_eq (PatternStrSearcher.mh s₀) (PatternPair.a (OptionOption.val r₂)) (PatternStrSearcher.mn s₀) 0 (PatternStrSearcher.k s₀)) ∧ ((PatternPair.b (OptionOption.val r₂)) = ((PatternPair.a (OptionOption.val r₂)) + (PatternStrSearcher.k s₀)))) ∧ ((PatternPair.b (OptionOption.val r₂)) ≤ (PatternStrSearcher.n s₀)))))
                                     ) ∧
                                     (∀ (o₁ : (OptionOption Tupleₓ₀)),
                                      (((OptionOption.is_some o₁) = (OptionOption.is_some r₂)) ∧ ((¬(OptionOption.is_some o₁)) -> ((OptionOption.val o₁) = (flux_specs_dflt (t0 := Tupleₓ₀) 0)))) ->
                                       ((k5 (OptionOption.is_some o₁) (PatternTwoWaySearcher.crit t₂) (PatternTwoWaySearcher.critb t₂) (PatternTwoWaySearcher.period t₂) (PatternTwoWaySearcher.pos t₂) (PatternTwoWaySearcher.end_ t₂) (PatternTwoWaySearcher.mem t₂) (PatternTwoWaySearcher.memb t₂) (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀) crit₀ critb₀ period₀ p₁ e₁ mem₀ memb₀ a'₂₄)) ∧
                                       (∀ (x₁ : Int),
                                        ((x₁ ≤ (PatternStrSearcher.n s₀)) ∧ (ghost_is_boundary (PatternStrSearcher.mh s₀) (PatternStrSearcher.n s₀) x₁)) ->
                                         ∀ (y₁ : Int),
                                          ((y₁ ≤ (PatternStrSearcher.n s₀)) ∧ (ghost_is_boundary (PatternStrSearcher.mh s₀) (PatternStrSearcher.n s₀) y₁)) ->
                                           ((k6 x₁ (OptionOption.is_some o₁) (PatternTwoWaySearcher.crit t₂) (PatternTwoWaySearcher.critb t₂) (PatternTwoWaySearcher.period t₂) (PatternTwoWaySearcher.pos t₂) (PatternTwoWaySearcher.end_ t₂) (PatternTwoWaySearcher.mem t₂) (PatternTwoWaySearcher.memb t₂) (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀) crit₀ critb₀ period₀ p₁ e₁ mem₀ memb₀ a'₂₄)) ∧
                                           ((k7 y₁ (OptionOption.is_some o₁) (PatternTwoWaySearcher.crit t₂) (PatternTwoWaySearcher.critb t₂) (PatternTwoWaySearcher.period t₂) (PatternTwoWaySearcher.pos t₂) (PatternTwoWaySearcher.end_ t₂) (PatternTwoWaySearcher.mem t₂) (PatternTwoWaySearcher.memb t₂) (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀) crit₀ critb₀ period₀ p₁ e₁ mem₀ memb₀ a'₂₄))
                                           )
                                       )
                                     )
                               ) ∧
                              (∀ (a'₃₅ : (OptionOption Tupleₓ₀)),
                               ∀ (a'₃₆ : PatternTwoWaySearcher),
                                ((k5 (OptionOption.is_some a'₃₅) (PatternTwoWaySearcher.crit a'₃₆) (PatternTwoWaySearcher.critb a'₃₆) (PatternTwoWaySearcher.period a'₃₆) (PatternTwoWaySearcher.pos a'₃₆) (PatternTwoWaySearcher.end_ a'₃₆) (PatternTwoWaySearcher.mem a'₃₆) (PatternTwoWaySearcher.memb a'₃₆) (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀) crit₀ critb₀ period₀ p₁ e₁ mem₀ memb₀ a'₂₄)) ->
                                 (∀ (a'₃₇ : Int),
                                  ((k6 a'₃₇ (OptionOption.is_some a'₃₅) (PatternTwoWaySearcher.crit a'₃₆) (PatternTwoWaySearcher.critb a'₃₆) (PatternTwoWaySearcher.period a'₃₆) (PatternTwoWaySearcher.pos a'₃₆) (PatternTwoWaySearcher.end_ a'₃₆) (PatternTwoWaySearcher.mem a'₃₆) (PatternTwoWaySearcher.memb a'₃₆) (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀) crit₀ critb₀ period₀ p₁ e₁ mem₀ memb₀ a'₂₄)) ->
                                   ∀ (a'₃₈ : Int),
                                    ((k7 a'₃₈ (OptionOption.is_some a'₃₅) (PatternTwoWaySearcher.crit a'₃₆) (PatternTwoWaySearcher.critb a'₃₆) (PatternTwoWaySearcher.period a'₃₆) (PatternTwoWaySearcher.pos a'₃₆) (PatternTwoWaySearcher.end_ a'₃₆) (PatternTwoWaySearcher.mem a'₃₆) (PatternTwoWaySearcher.memb a'₃₆) (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) (PatternStrSearcher.tag s₀) (PatternStrSearcher.p s₀) (PatternStrSearcher.e s₀) (PatternStrSearcher.crit s₀) (PatternStrSearcher.critb s₀) (PatternStrSearcher.period s₀) (PatternStrSearcher.mem s₀) (PatternStrSearcher.memb s₀) crit₀ critb₀ period₀ p₁ e₁ mem₀ memb₀ a'₂₄)) ->
                                     (((a'₃₇ ≤ (PatternStrSearcher.n s₀))) ∧
                                     ((ghost_is_boundary (PatternStrSearcher.mh s₀) (PatternStrSearcher.n s₀) a'₃₇))
                                     ) ∧
                                     (((a'₃₈ ≤ (PatternStrSearcher.n s₀))) ∧
                                     ((ghost_is_boundary (PatternStrSearcher.mh s₀) (PatternStrSearcher.n s₀) a'₃₈))
                                     )
                                     ) ∧
                                 ((((PatternStrSearcher.n s₀) = (PatternStrSearcher.n s₀))) ∧
                                 (((PatternStrSearcher.mh s₀) = (PatternStrSearcher.mh s₀))) ∧
                                 (((PatternStrSearcher.k s₀) = (PatternStrSearcher.k s₀))) ∧
                                 (((PatternStrSearcher.mn s₀) = (PatternStrSearcher.mn s₀))) ∧
                                 ((ghost_str_inv (PatternStrSearcher.n s₀) (PatternStrSearcher.mh s₀) (PatternStrSearcher.k s₀) (PatternStrSearcher.mn s₀) 1 (PatternTwoWaySearcher.pos a'₃₆) (PatternTwoWaySearcher.end_ a'₃₆) (PatternTwoWaySearcher.crit a'₃₆) (PatternTwoWaySearcher.critb a'₃₆) (PatternTwoWaySearcher.period a'₃₆) (PatternTwoWaySearcher.mem a'₃₆) (PatternTwoWaySearcher.memb a'₃₆)))
                                 )
                                 )
                              )
     
end F
