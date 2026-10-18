import Lean

open Lean Meta

register_option flex.standardQualifiers : Bool := {
  defValue := true
  descr := "Include the standard Int, Nat, and Bool qualifier bank in fix."
}

namespace Flex.PA.StandardQualifiers

-- The fixed integer bank used by the arithmetic benchmarks.
def intEqZero (x : Int) : Prop := x = 0
def intPos (x : Int) : Prop := 0 < x
def intNonneg (x : Int) : Prop := 0 ≤ x
def intNeg (x : Int) : Prop := x < 0
def intNonpos (x : Int) : Prop := x ≤ 0
def intEq (x y : Int) : Prop := x = y
-- Reversed comparisons share the same syntax as their forward instances.
def intGt (x y : Int) : Prop := y < x
def intGe (x y : Int) : Prop := y ≤ x
def intLt (x y : Int) : Prop := x < y
def intLe (x y : Int) : Prop := x ≤ y
def intLePred (x y : Int) : Prop := x ≤ y - 1

def natEqZero (x : Nat) : Prop := x = 0
def natPos (x : Nat) : Prop := 0 < x
def natEq (x y : Nat) : Prop := x = y
def natLt (x y : Nat) : Prop := x < y
def natLe (x y : Nat) : Prop := x ≤ y

def boolTrue (x : Bool) : Prop := x = true
def boolFalse (x : Bool) : Prop := x = false
def boolEq (x y : Bool) : Prop := x = y

end Flex.PA.StandardQualifiers

open Flex.PA.StandardQualifiers in
/-- Return the fixed bank unless explicitly disabled. -/
def getStandardQualifiers : MetaM (Array Expr) := do
  unless flex.standardQualifiers.get (← getOptions) do return #[]
  return #[``intEqZero, ``intPos, ``intNonneg, ``intNeg, ``intNonpos,
    ``intEq, ``intGt, ``intGe, ``intLt, ``intLe, ``intLePred,
    ``natEqZero, ``natPos, ``natEq, ``natLt, ``natLe,
    ``boolTrue, ``boolFalse, ``boolEq].map fun name => mkConst name
