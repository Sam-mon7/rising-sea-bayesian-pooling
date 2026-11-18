# Bayesian forecast pooling in Lean

Can two experts each give a calibrated probability for an event, disagree, and still have their combined information summarized by a fixed weighted average after a change of scale? **Yes.** The two projects here formalize countable counterexamples to conjectures about pooling Bayesian forecasts. Both use Lean 4.19.0 and a pinned mathlib.

## The two results

| Project | Result | Lean source | Verification |
| --- | --- | --- | --- |
| [Two experts](RisingSea/README.md) | One experiment works for every choice of positive expert weights summing to one. For each choice there is a single continuous increasing scale on which the weighted average gives the exact joint posterior. | [Main theorems](RisingSea/RisingSea.lean) | [Build and axiom audit](RisingSea/verification.txt) |
| [The prior and two experts](PriorPool/README.md) | The prior and both experts can all receive strictly positive weight. For a fixed scale the coefficients in the example are unique. A finite continuous extension of the scale at either endpoint forces agreement with the prior almost surely. | [Counterexample](PriorPool/PriorPool.lean) · [Endpoint theorems](PriorPool/PriorPool/Bounded.lean) | [Build and axiom audit](PriorPool/verification.txt) |

The common construction puts a binary event on an integer path. One expert observes the even endpoint of an edge and the other observes the odd endpoint. Either report alone leaves two possible edges. Together the reports identify one edge. Its event probability lies strictly between the two individual forecasts, which makes it possible to construct the required change of scale by interpolation.

The conjectures appear in §4.5, p. 283 of Dawid, DeGroot and Mortera. Satopää's alternating-partition example is a close antecedent. Weatherson gave a binary strict-betweenness example with report-dependent weights. The project notes explain how these constructions relate to the formal statements. Priority for the fixed-weight results remains unconfirmed. [Dawid, DeGroot and Mortera](https://doi.org/10.1007/BF02562628) · [Satopää, Example 3.10](https://arxiv.org/pdf/1706.06006v1#page=16) · [Weatherson, §1](https://doi.org/10.26686/ajl.v23i2.9691)

## Reproduce the checks

With Lean's toolchain manager installed, run the following from the repository root. Each project has its own pinned manifest and includes all of its local proof sources.

```sh
cd RisingSea
lake exe cache get
lake build
lake env lean -DwarningAsError=true Audit.lean

cd ../PriorPool
lake exe cache get
lake build
lake env lean -DwarningAsError=true PriorAudit.lean
```

Each audit checks the transitive dependencies of the named theorems and fails on any axiom outside `propext`, `Classical.choice`, and `Quot.sound`. The verification transcripts include SHA-256 hashes of the checked files.
