import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Logic.Equiv.Nat
import Mathlib.Order.Interval.Set.IsoIoo
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import RisingSea.Path

namespace RisingSea

/-- The zigzag enumeration of the integers transfers a geometric law to the path. -/
noncomputable def exampleMass (n : ℤ) : ℝ :=
  1 / 2 / 2 ^ (Equiv.intEquivNat n)

/-- A strictly increasing bounded conditional probability on the integer path. -/
noncomputable def exampleRate (n : ℤ) : ℝ :=
  (1 + (n : ℝ) / (1 + |(n : ℝ)|)) / 2

/-- A probability mass positive on every edge of the integer path and a
strictly increasing sequence of conditional probabilities on those edges. -/
theorem example_path_data :
    (∀ n, 0 < exampleMass n) ∧ HasSum exampleMass 1 ∧ StrictMono exampleRate ∧
      (∀ n, 0 < exampleRate n ∧ exampleRate n < 1) := by
  let e := orderIsoIooNegOneOne ℝ
  let u (n : ℤ) : ℝ := (e (n : ℝ)).val
  have hrate (n : ℤ) : exampleRate n = (1 + u n) / 2 := by
    unfold exampleRate u e orderIsoIooNegOneOne
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    unfold exampleMass
    positivity
  · exact (Equiv.intEquivNat.hasSum_iff
      (f := fun n : ℕ ↦ (1 : ℝ) / 2 / 2 ^ n)).mpr (hasSum_geometric_two' 1)
  · intro i j hij
    have hij' : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    have hu : u i < u j := e.strictMono hij'
    rw [hrate, hrate]
    linarith
  · intro n
    have hu : -1 < u n ∧ u n < 1 := (e (n : ℝ)).property
    rw [hrate]
    constructor <;> linarith [hu.1, hu.2]

theorem exists_path_data :
    ∃ (p q : ℤ → ℝ), (∀ n, 0 < p n) ∧ HasSum p 1 ∧ StrictMono q ∧
      (∀ n, 0 < q n ∧ q n < 1) :=
  ⟨exampleMass, exampleRate, example_path_data⟩

/-- On edge zero the left, joint, and right posteriors are three distinct fractions. -/
theorem example_edge_zero :
    leftReport exampleMass exampleRate 0 = 5 / 12 ∧
    exampleRate 0 = 1 / 2 ∧
    rightReport exampleMass exampleRate 0 = 11 / 20 := by
  have hm₀ : exampleMass 0 = 1 / 2 := by
    change (1 : ℝ) / 2 / 2 ^ (0 : ℕ) = _
    norm_num
  have hmNeg : exampleMass (-1) = 1 / 4 := by
    change (1 : ℝ) / 2 / 2 ^ (1 : ℕ) = _
    norm_num
  have hmPos : exampleMass 1 = 1 / 8 := by
    change (1 : ℝ) / 2 / 2 ^ (2 : ℕ) = _
    norm_num
  change vertex exampleMass exampleRate 0 = _ ∧ exampleRate 0 = _ ∧
    vertex exampleMass exampleRate 1 = _
  norm_num [vertex, exampleRate, hm₀, hmNeg, hmPos]

end RisingSea
