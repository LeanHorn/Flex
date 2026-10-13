import Flex.VCG.SystemFRK.Generator.Constraints

/-! Fuel-indexed semantic specifications for the mutually recursive generator. -/
namespace SystemFRK

def SynthSound (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (fuel : Nat) : Prop :=
  ∀ context assumptions expression state final constraint type,
    synthFuel signature context fuel expression state = .ok ((constraint, type), final) →
    Entails signature model assignment context assumptions constraint →
    HasType signature model assignment context assumptions expression type ∧ type.InScope context

def CheckSound (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (fuel : Nat) : Prop :=
  ∀ context assumptions expression state final constraint type,
    checkFuel signature context fuel expression type state = .ok (constraint, final) →
    Entails signature model assignment context assumptions constraint →
    HasType signature model assignment context assumptions expression type

end SystemFRK
