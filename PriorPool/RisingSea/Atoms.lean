import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! A countable binary experiment. Observation cells have ordinary positive-probability
Bayes ratios, calculated from a single probability measure on the sample space. -/

namespace RisingSea

open MeasureTheory Set
open scoped ENNReal

abbrev World := ℤ × Bool

def truth : Set World := {ω | ω.2 = true}

def edgeCell (n : ℤ) : Set World := {ω | ω.1 = n}

def pairCell (n : ℤ) : Set World := edgeCell (n - 1) ∪ edgeCell n

noncomputable section

private def edgeLayer (p q : ℤ → ℝ) (n : ℤ) : Measure World :=
  ENNReal.ofReal (p n * q n) • Measure.dirac (n, true) +
  ENNReal.ofReal (p n * (1 - q n)) • Measure.dirac (n, false)

def edgeLaw (p q : ℤ → ℝ) : Measure World := Measure.sum (edgeLayer p q)

def posterior (μ : Measure World) (cell : Set World) : ℝ :=
  (μ (truth ∩ cell)).toReal / (μ cell).toReal

/-- The cell ratio agrees with mathlib's conditional measure. -/
theorem posterior_eq_cond (μ : Measure World) (cell : Set World) :
    posterior μ cell = ((ProbabilityTheory.cond μ cell) truth).toReal := by
  rw [posterior, ProbabilityTheory.cond_apply (Set.to_countable cell).measurableSet,
    Set.inter_comm cell truth, ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv, mul_comm]

variable {p q : ℤ → ℝ}

private lemma splitMass (hp : ∀ n, 0 < p n) (hq : ∀ n, 0 < q n ∧ q n < 1) (n : ℤ) :
    ENNReal.ofReal (p n * q n) + ENNReal.ofReal (p n * (1 - q n)) =
      ENNReal.ofReal (p n) := by
  rw [← ENNReal.ofReal_add (mul_nonneg (hp n).le (hq n).1.le)
    (mul_nonneg (hp n).le (sub_nonneg.mpr (hq n).2.le))]
  congr 1
  ring

theorem edgeLaw_probability (hp : ∀ n, 0 < p n) (hs : HasSum p 1)
    (hq : ∀ n, 0 < q n ∧ q n < 1) : IsProbabilityMeasure (edgeLaw p q) := by
  constructor
  rw [edgeLaw, Measure.sum_apply_of_countable]
  simp only [edgeLayer, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
    (Set.mem_univ _), smul_eq_mul, mul_one, splitMass hp hq]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (hp n).le) hs.summable, hs.tsum_eq,
    ENNReal.ofReal_one]

theorem mass_edgeCell (hp : ∀ n, 0 < p n) (hq : ∀ n, 0 < q n ∧ q n < 1) (n : ℤ) :
    edgeLaw p q (edgeCell n) = ENNReal.ofReal (p n) := by
  classical
  rw [edgeLaw, Measure.sum_apply_of_countable, tsum_eq_single n]
  · simpa [edgeLayer, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply, edgeCell,
      Set.indicator_apply, smul_eq_mul] using splitMass hp hq n
  · intro k hk
    simp [edgeLayer, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply, edgeCell,
      Set.indicator_apply, smul_eq_mul, hk]

theorem mass_truth_edgeCell (p q : ℤ → ℝ) (n : ℤ) :
    edgeLaw p q (truth ∩ edgeCell n) = ENNReal.ofReal (p n * q n) := by
  classical
  rw [edgeLaw, Measure.sum_apply_of_countable, tsum_eq_single n]
  · simp [edgeLayer, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply, edgeCell,
      truth, Set.indicator_apply, smul_eq_mul]
  · intro k hk
    simp [edgeLayer, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply, edgeCell,
      truth, Set.indicator_apply, smul_eq_mul, hk]

/-- Every nonempty event has positive mass, including each binary outcome on each edge. -/
theorem edgeLaw_pos_of_nonempty (hp : ∀ n, 0 < p n) (hq : ∀ n, 0 < q n ∧ q n < 1)
    {s : Set World} (hs : s.Nonempty) : 0 < edgeLaw p q s := by
  classical
  obtain ⟨⟨n, b⟩, hmem⟩ := hs
  have hl : 0 < edgeLayer p q n {(n, b)} := by
    cases b <;>
      simp [edgeLayer, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply,
        Set.indicator_apply, smul_eq_mul, ENNReal.ofReal_pos,
        mul_pos (hp n) (hq n).1, mul_pos (hp n) (sub_pos.mpr (hq n).2)]
  have hle : edgeLayer p q n ≤ edgeLaw p q := Measure.le_sum _ n
  exact (hl.trans_le (hle _)).trans_le (measure_mono (Set.singleton_subset_iff.mpr hmem))

private lemma edge_disjoint (n : ℤ) : Disjoint (edgeCell (n - 1)) (edgeCell n) := by
  rw [Set.disjoint_left]
  intro ω h₁ h₂
  change ω.1 = n - 1 at h₁
  change ω.1 = n at h₂
  omega

theorem mass_pairCell (hp : ∀ n, 0 < p n) (hq : ∀ n, 0 < q n ∧ q n < 1) (n : ℤ) :
    edgeLaw p q (pairCell n) = ENNReal.ofReal (p (n-1) + p n) := by
  rw [pairCell, measure_union (edge_disjoint n) (Set.to_countable _).measurableSet,
    mass_edgeCell hp hq, mass_edgeCell hp hq, ENNReal.ofReal_add (hp _).le (hp _).le]

theorem mass_truth_pairCell (hp : ∀ n, 0 < p n) (hq : ∀ n, 0 < q n ∧ q n < 1) (n : ℤ) :
    edgeLaw p q (truth ∩ pairCell n) =
      ENNReal.ofReal (p (n-1) * q (n-1) + p n * q n) := by
  rw [pairCell, Set.inter_union_distrib_left,
    measure_union ((edge_disjoint n).mono Set.inter_subset_right Set.inter_subset_right)
      (Set.to_countable _).measurableSet,
    mass_truth_edgeCell, mass_truth_edgeCell, ENNReal.ofReal_add
      (mul_nonneg (hp _).le (hq _).1.le) (mul_nonneg (hp _).le (hq _).1.le)]

theorem posterior_edgeCell (hp : ∀ n, 0 < p n) (hq : ∀ n, 0 < q n ∧ q n < 1) (n : ℤ) :
    posterior (edgeLaw p q) (edgeCell n) = q n := by
  rw [posterior, mass_edgeCell hp hq, mass_truth_edgeCell, ENNReal.toReal_ofReal (hp n).le,
    ENNReal.toReal_ofReal (mul_nonneg (hp n).le (hq n).1.le)]
  exact (div_eq_iff (hp n).ne').mpr (mul_comm _ _)

theorem posterior_pairCell (hp : ∀ n, 0 < p n) (hq : ∀ n, 0 < q n ∧ q n < 1) (n : ℤ) :
    posterior (edgeLaw p q) (pairCell n) =
      (p (n-1) * q (n-1) + p n * q n) / (p (n-1) + p n) := by
  rw [posterior, mass_truth_pairCell hp hq, mass_pairCell hp hq,
    ENNReal.toReal_ofReal (add_nonneg (mul_nonneg (hp _).le (hq _).1.le)
      (mul_nonneg (hp _).le (hq _).1.le)),
    ENNReal.toReal_ofReal (add_nonneg (hp _).le (hp _).le)]

end
end RisingSea
