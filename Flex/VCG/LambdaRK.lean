import Flex.VCG.LambdaRK.VCGen
import Flex.VCG.LambdaRK.Judgments
import Flex.VCG.LambdaRK.BindingLemmas
import Flex.VCG.LambdaRK.SemanticTyping
import Flex.VCG.LambdaRK.SemanticsLemmas
import Flex.VCG.LambdaRK.LogicalLemmas
import Flex.VCG.LambdaRK.EnvironmentLemmas
import Flex.VCG.LambdaRK.TypeIndexLemmas
import Flex.VCG.LambdaRK.ContextLemmas
import Flex.VCG.LambdaRK.StructuralOrder
import Flex.VCG.LambdaRK.SubstitutionLemmas
import Flex.VCG.LambdaRK.DatatypeAdequacy
import Flex.VCG.LambdaRK.RecursionLemmas
import Flex.VCG.LambdaRK.SyntaxEqualityLemmas

/-!
# λRK development frontend

Explicit System F, regular positive datatypes, pattern matching, structural
recursion, and integer-valued measures. `LambdaRK.generate` checks a closed
program against an annotated type and computes its Horn constraints.

This import contains executable definitions and declarative specifications.
The remaining full-language proof obligations require a separate, explicit
import of `Flex.VCG.LambdaRK.DraftTheorems`.
See `Demo.LambdaRK` for the two development
examples and `Demo.LambdaRKChecks` for checker regressions.
-/
