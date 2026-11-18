# When can a Bayesian pool give positive weight to the prior?

**All three weights can be positive.** Dawid, DeGroot and Mortera asked whether a compatible Bayesian pooling rule could ever give strictly positive coefficients to the prior and to both expert probabilities in their equation (24). They stated this as a further conjecture in the last sentence of §4.5. Their framework includes continuous increasing links on the open probability interval, notably the logit in equation (17). [Original paper, §4.3 and §4.5, p. 283](https://doi.org/10.1007/BF02562628)

## What the main theorem says

Let A be a binary event, p its prior probability, X and Y two reports, and Z the probability of A conditional on learning both reports. There is **one** countable probability experiment with p = 1/2 and the following properties.

- Both reports are calibrated for A. Learning X alone gives posterior X, and likewise for Y. At every world the joint posterior Z lies strictly between X and Y. Every nonempty event has positive probability.
- For **every** prescribed triple u, a, b > 0 with u+a+b = 1, there is a continuous strictly increasing bijection g from (0,1) onto ℝ for which g(p) = 1 and

  `g(Z) = u g(p) + a g(X) + b g(Y)`  at every world.

- Once the experiment and g are fixed, those three coefficients are unique among **all real triples** giving the same equality. In particular, dropping the prior and refitting the two coefficients cannot reproduce the same forecasts on this scale.

The link can depend on the prescribed weights. The prior, law, event, experts, and joint posterior stay fixed. Coefficient uniqueness here concerns this experiment and link. Identifying the prior across all laws compatible with a given pooling formula is a separate question on the same page of the paper. The theorem uses mathlib's conditional expectation of the event indicator given each report and the ordered pair of reports. Its name is `RisingSea.PriorPool.all_three_positive` in `PriorPool.lean`.

## Why the construction works

Use the integer path from the earlier rising-sea framework. Give each edge n positive mass and a strictly increasing conditional event probability qₙ. Each expert learns one endpoint, even for the first expert and odd for the second. The posterior vₙ at vertex n averages the probabilities on its two incident edges. Consequently

```text
vₙ < qₙ < vₙ₊₁.
```

The increasing vₙ identify the vertices, and the two vertices identify the edge. Choose the edge masses symmetrically about vertex zero and choose reflected event probabilities to sum to one. This makes both the actual prior and v₀ equal to 1/2. The vₙ approach 0 and 1 at the two ends.

To make room for the prior weight, first send vertex n to tₙ = n B^|n| with B = 2 + 1/a + 1/b. The centered prior is now zero. On every edge, `a·t_even + b·t_odd` lies strictly between its two transformed endpoints, even though a+b is strictly less than one. For example, on a positive edge, the weighted larger endpoint alone exceeds the smaller one. Reflection handles the negative tail.

Map each qₙ to that interior value by increasing interpolation. The earlier library's order-isomorphism theorem performs all of these interpolations at once. Translate the resulting scale by one. Because the three weights sum to one, the translated identity holds with g(p) = 1. To identify the coefficients, compare edges −1 and 0, which share the even report, then edges 0 and 1, which share the odd report. These comparisons determine the two expert coefficients. The nonzero transformed prior then determines the remaining one.

**One worked edge.** For u = a = b = 1/3, edge zero has prior 1/2, even report 1/2, odd report 31/40 and joint posterior 3/4. Here B = 8. The construction sends the prior and those reports to 1, 1 and 9, and sends the joint posterior to 11/3. Thus its three transformed contributions are 1/3, 1/3 and 3.

## Where the conjectured impossibility holds

There is a general obstruction when the link has a finite continuous extension at either endpoint. In an arbitrary probability space with interior forecasts and a genuine prior p, the pooling identity then forces X = Y = Z = p almost surely. The two endpoint theorems are `right_endpoint_rigidity` and `left_endpoint_rigidity` in `PriorPool/Bounded.lean`.

For the upper endpoint, let M be the essential supremum of Z. Both individual reports are conditional means of Z, hence both are at most M almost surely. When the transformed upper end is finite, taking the essential supremum bounds g(M) above by u g(p) + (1−u) g(M). Positive u forces M ≤ p. Since the mean of Z is p, equality follows almost surely. The lower endpoint gives the other direction. The counterexample's link diverges at both ends. Its realized probabilities are all strictly interior.

## Literature and novelty

The normalized two-expert question addressed by the earlier project sets the prior weight to zero. The new question specifically requires u > 0. Gneiting and Ranjan's generalized-pooling theorem concerns continuous outcome distributions and explicitly discusses the outstanding binary case. Their Bernoulli probit example uses expert weights greater than one. [Gneiting and Ranjan, §3.2](https://arxiv.org/pdf/1106.1638#page=17)

Satopää's 2017 preprint already contains the alternating-partition geometry for a continuous target, with report-dependent arithmetic weights. It is a close antecedent. The present result adds a binary experiment with a verified prior, an unbounded change of scale for prescribed positive prior and expert weights, coefficient identification, and the endpoint obstruction. Weatherson's later binary example establishes strict betweenness using weights that vary with the reports. The search found no earlier paper explicitly giving the three-positive-coefficient result. Historical priority remains unconfirmed. [Satopää, Example 3.10](https://arxiv.org/pdf/1706.06006v1#page=16) · [Weatherson, §1](https://doi.org/10.26686/ajl.v23i2.9691)

## Reproduce

With Lean's toolchain manager installed, run these commands in the unpacked directory.

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true PriorAudit.lean
```

Lean 4.19.0 and mathlib are pinned. The archive includes the earlier framework used by the proof. The axiom audit checks the transitive dependencies of the principal results, and `verification.txt` records the commands, exit codes and source hashes.
