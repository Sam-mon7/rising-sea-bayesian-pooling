# A countable counterexample in Bayesian forecast pooling

Two Bayesian experts can each be calibrated for the same event, disagree on every outcome, and have their **exact joint posterior** equal a fixed-weight average of their reports after one continuous, strictly increasing change of scale. The probability law and the two experts can be chosen once for every weight. The change of scale can depend on the weight and the law. It stays fixed across observations.

This supplies a counterexample to the normalized, zero-intercept form of the generalized-linear pooling conjecture of Dawid, DeGroot and Mortera. They asked whether such a rule forces at least one expert to add no information about the event once the other report is known. Gneiting and Ranjan later singled out binary outcomes as a case still beyond their theorem for continuous outcome distributions. [Dawid, DeGroot and Mortera, §§3–4, especially p. 283](https://doi.org/10.1007/BF02562628) · [Gneiting and Ranjan, §3.2](https://arxiv.org/pdf/1106.1638)

## Exact statement

There exist a probability measure on the countable space ℤ × {false, true}, a binary event A, and reports X and Y in (0, 1). Write Z = P(A | X, Y). At every world,

- P(A | X) = X and P(A | Y) = Y.
- Either X < Z < Y or Y < Z < X.

For each fixed weight 0 < a < 1 there is one continuous, strictly increasing g on ℝ such that g(Z) = a g(X) + (1 − a) g(Y) at **all** worlds.

Every nonempty event in the model has positive probability, including every realized individual and joint report fibre. Dropping either report changes the posterior with probability one. The quantified statement appears in `all_weights_one_experiment`. The equal-weight case is restated directly using mathlib's conditional expectations in `conditional_expectation_counterexample`.

## The construction

Give every integer edge n, joining vertices n and n+1, positive mass pₙ. The masses sum to one. Conditional on that edge, the event is true with probability qₙ, where the qₙ form a strictly increasing sequence in (0, 1). The two worlds on edge n have masses pₙqₙ and pₙ(1−qₙ).

One expert sees the even endpoint of the edge. The other sees the odd endpoint. A vertex n belongs to precisely two edges, so its posterior is

```text
vₙ = (pₙ₋₁ qₙ₋₁ + pₙ qₙ) / (pₙ₋₁ + pₙ).
```

Positive weights give qₙ₋₁ < vₙ < qₙ. Shifting this inequality one place gives **vₙ < qₙ < vₙ₊₁**. The vertex posteriors increase strictly, so reporting a posterior identifies its vertex. Together the two reports identify the edge, and conditioning on both gives exactly qₙ.

This is the reusable part of the argument. Choose any target rₙ strictly inside each gap (vₙ, vₙ₊₁). On that gap, join (vₙ, vₙ), (qₙ, rₙ), and (vₙ₊₁, vₙ₊₁) by straight lines. Use the identity outside the gaps. All the pieces together define one increasing bijection of ℝ. Its inverse moves each rₙ back to qₙ, and the order isomorphism gives continuity even at accumulation points.

Now take rₙ to be the desired weighted mean of the two reports on edge n. The map fixes the reports and sends the joint posterior to their weighted mean. This last step is the entire pooling argument once the interpolation theorem is available.

## One report pair in exact arithmetic

The witness in `Weights.lean` enumerates the integers as 0, −1, 1, −2, 2, … and assigns successive masses 1/2, 1/4, 1/8, …. It uses qₙ = (1 + n/(1+|n|))/2. On edge 0 the reports are **5/12** and **11/20**. The joint posterior is **1/2**. The midpoint construction fixes the two reports and sends 1/2 to their arithmetic midpoint, **29/60**. The theorem `example_edge_zero` checks the three posterior values.

## Literature and scope

Zhang proved that strict betweenness forces agreement on a finite probability domain. Weatherson gave an infinite Gaussian example with an observation-dependent arithmetic weight. Satopää's earlier Example 3.8 used alternating partitions and obtained strict betweenness for conditional means of a continuous target. The present proof uses the related alternating-partition idea for a binary event and constructs a single link for a prescribed weight. Priority for the fixed-link result has not been established. [Zhang, Theorem 2 and footnote 13](https://doi.org/10.1007/s11238-025-10092-6) · [Weatherson, §1](https://doi.org/10.26686/ajl.v23i2.9691) · [Satopää, Example 3.8](https://arxiv.org/pdf/1706.06006)

The search also identified three research questions with different mathematical obstacles. I selected pooling because it has a published conjecture with explicit quantifiers, and both the Bayesian semantics and the counterexample can be checked end to end.

| Area | Question identified in the literature |
| --- | --- |
| Geometry of coherent posteriors | Can a nonatomic joint law of two Bayesian posteriors be uniquely exposed by a continuous payoff? Kravchenko distinguishes exposed laws from extreme laws and identifies the nonatomic exposed case as open. [Kravchenko, introduction](https://arxiv.org/pdf/2405.04375) |
| Universal Bayesian sequence prediction | Can a universal lower semicomputable semimeasure outside the universal-mixture class predict the fair-coin conditional probabilities on every fair-coin Martin-Löf random sequence? The failure for universal mixtures motivated this narrower question. [Lattimore and Hutter, conclusion](https://www.hutter1.net/publ/mnonconvx.pdf) |
| Statistical versus computational limits | For a uniformly planted clique of size n^(1/2−ε), with 0 < ε < 1/2, can a polynomial-time algorithm recover its location with high probability? The conjectured square-root barrier persists alongside improved algorithms at the square-root scale. [Kunisky and Mao](https://arxiv.org/abs/2609.24780) |

## Reproduce the verification

From this directory, with Lean's toolchain manager installed, run

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Audit.lean
```

`lean-toolchain` selects Lean 4.19.0 and `lake-manifest.json` pins mathlib and its dependencies. `Audit.lean` prints the transitive axiom dependencies of the main results. The recorded run is in `verification.txt`.
