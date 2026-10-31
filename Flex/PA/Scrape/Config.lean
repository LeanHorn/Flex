import Lean

/-! Scraping modes, budgets, and reported candidates. -/

open Lean Meta

inductive PAScrapeMode where
  | no | basic | standard | deep
  deriving BEq, Inhabited

/-- Limits apply per invocation, except guard atoms per clause and candidates per κ. -/
structure PAScrapeLimits where
  maxParams : Nat := 3
  maxQualifiers : Nat := 128
  maxNodes : Nat := 20000
  maxDepth : Nat := 64
  maxDefinitions : Nat := 16
  maxDefinitionDepth : Nat := 2
  maxCandidatesPerKappa : Nat := 2048
  maxInstancesPerKappa : Nat := 8192
  maxGuardedQualifiers : Nat := 32
  maxGuardAtoms : Nat := 12
  maxGuardPairs : Nat := 256
  maxObservationQualifiers : Nat := 16
  maxObservationPairs : Nat := 256
  maxObservationBinders : Nat := 1
  maxAnchoredCandidatesPerKappa : Nat := 64
  maxAnchoredAttempts : Nat := 256
  maxAnchoredNodes : Nat := 5000
  /-- Optional broader search; extra candidates can increase certification cost. -/
  maxCompoundCandidatesPerKappa : Nat := 0
  maxEndpointCandidatesPerKappa : Nat := 16
  maxAccumulatorCandidatesPerKappa : Nat := 16
  maxAlgebraCandidatesPerKappa : Nat := 16
  maxAffineCandidatesPerKappa : Nat := 16
  maxMeasureCandidatesPerKappa : Nat := 16
  maxStateGuardedCandidatesPerKappa : Nat := 16
  maxFragmentCandidatesPerKappa : Nat := 16
  maxRegionCandidatesPerKappa : Nat := 16
  maxPrefixCandidatesPerKappa : Nat := 16
  maxWorklistCandidatesPerKappa : Nat := 16
  maxRelationalCandidatesPerKappa : Nat := 16

structure PAScrapeConfig extends PAScrapeLimits where
  mode : PAScrapeMode := .no
  defs : Array Name := #[]

/-- A source-derived qualifier with its original predicate-slot assignment. -/
structure PAAnchoredQualifier where
  kvar : MVarId
  qualifier : Expr
  slots : List Nat
  origin : String

structure PAScrapeResult where
  qualifiers : Array Expr := #[]
  origins : Array String := #[]
  /-- Observation relations form the final, lowest-priority segment. -/
  observationCount : Nat := 0
  anchored : Array PAAnchoredQualifier := #[]
  visitedNodes : Nat := 0
  inspectedDefinitions : Nat := 0
  rejected : Nat := 0
  limitsHit : Array String := #[]

initialize Lean.registerTraceClass `flex.scrape
