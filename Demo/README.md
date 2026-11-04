# RQ4: foundational verifiers

| Material | Source |
| --- | --- |
| STLC examples, including maximum and its inferred refinement | [STLC.lean](STLC.lean) |
| Imp's 25 programs, contracts, generated CHCs, and 15 automatic proofs | [Imp.lean](Imp.lean) |
| Imp generation soundness: `generate_sound` | [Imp mechanization](../Flex/VCG/Imp.lean#L255) |
| STLC generation soundness: `topVC_decl_sound` | [Soundness.lean](../Flex/VCG/STLC/Soundness.lean#L565) |
| STLC refinement safety: `type_safety` | [Safety.lean](../Flex/VCG/STLC/Safety.lean#L759) |

Paper examples:

- **Maximum:** [`exMax` and `max_inferred`](STLC.lean#L171).
- **Fibonacci:** [program](Imp.lean#L133), [specification and generated VC](Imp.lean#L547), [automatic proof](Imp.lean#L825).
- **Imp collection:** programs come first, followed by [contracts](Imp.lean#L472) and [automatic proofs](Imp.lean#L783). It contains 26 loop predicates; Fix infers 15 and fully proves those 15 programs without supplied invariants or program-specific qualifiers. The other ten programs remain open cases.

The [final section of Imp.lean](Imp.lean#L905) preserves the older integer-store
While examples separately; these are outside the 25-program paper collection.
