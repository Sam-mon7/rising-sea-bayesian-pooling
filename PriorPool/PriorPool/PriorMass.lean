import RisingSea.Atoms

/-! The involution exchanging the two sides of a symmetric path pairs the
event mass on each edge with its complementary event mass on the other. -/

namespace RisingSea.PriorPool

open MeasureTheory Set
open scoped ENNReal

private def reflect : ℤ ≃ ℤ where
  toFun n := -1 - n
  invFun n := -1 - n
  left_inv n := by dsimp; omega
  right_inv n := by dsimp; omega

theorem truth_prior_half {p q : ℤ → ℝ}
    (hp : ∀ n, 0 < p n) (hs : HasSum p 1)
    (hq : ∀ n, 0 < q n ∧ q n < 1)
    (hps : ∀ n, p (-1 - n) = p n)
    (hqs : ∀ n, q (-1 - n) = 1 - q n) :
    ((edgeLaw p q) truth).toReal = 1 / 2 := by
  let f (n : ℤ) := p n * q n
  have hf0 (n : ℤ) : 0 ≤ f n := mul_nonneg (hp n).le (hq n).1.le
  have hsum : Summable f := Summable.of_nonneg_of_le hf0
    (fun n => mul_le_of_le_one_right (hp n).le (hq n).2.le) hs.summable
  have hrefl (n : ℤ) : f n + f (reflect n) = p n := by
    change p n * q n + p (-1 - n) * q (-1 - n) = p n
    rw [hps, hqs]
    ring
  have hadd : (∑' n, f n) + (∑' n, f n) = 1 := calc
    _ = (∑' n, f n) + (∑' n, f (reflect n)) := by rw [reflect.tsum_eq f]
    _ = ∑' n, (f n + f (reflect n)) := (hsum.tsum_add (reflect.summable_iff.mpr hsum)).symm
    _ = _ := by simpa only [hrefl] using hs.tsum_eq
  have hcover : truth = ⋃ n : ℤ, truth ∩ edgeCell n := by
    ext w
    constructor
    · intro hw
      exact Set.mem_iUnion.mpr ⟨w.1, hw, rfl⟩
    · intro hw
      obtain ⟨_, h, _⟩ := Set.mem_iUnion.mp hw
      exact h
  have hd : Pairwise (fun i j : ℤ => Disjoint (truth ∩ edgeCell i) (truth ∩ edgeCell j)) := by
    intro i j hij
    refine Set.disjoint_left.mpr (fun w hi hj => hij ?_)
    exact hi.2.symm.trans hj.2
  calc
    _ = (∑' n, ENNReal.ofReal (f n)).toReal := by
      congr 1
      calc
        edgeLaw p q truth = edgeLaw p q (⋃ n : ℤ, truth ∩ edgeCell n) := congrArg _ hcover
        _ = _ := by rw [measure_iUnion hd (fun n => (Set.to_countable _).measurableSet)]
                    simp only [mass_truth_edgeCell, f]
    _ = ∑' n, f n := by rw [← ENNReal.ofReal_tsum_of_nonneg hf0 hsum,
                             ENNReal.toReal_ofReal (tsum_nonneg hf0)]
    _ = _ := by linarith

end RisingSea.PriorPool
