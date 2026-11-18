import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Interpolation of an interlacing chain

A continuous increasing change of scale can send one chosen interior point
of each of a sequence of disjoint intervals to another while fixing all
endpoints. We use the midpoint as the target for a fixed-weight opinion pool.
-/

namespace RisingSea

noncomputable section

/-- The two affine branches meet at `u`, whose image is `v`. -/
private def warp (a b u v t : ℝ) : ℝ :=
  if t ≤ u then v + (t - u) * ((v - a) / (u - a))
  else v + (t - u) * ((b - v) / (b - u))

private theorem warp_at_knot (a b u v : ℝ) : warp a b u v u = v := by
  simp [warp]

private theorem warp_strict {a b u v : ℝ}
    (hu : a < u ∧ u < b) (hv : a < v ∧ v < b) : StrictMono (warp a b u v) := by
  have leftPos := div_pos (sub_pos.mpr hv.1) (sub_pos.mpr hu.1)
  have rightPos := div_pos (sub_pos.mpr hv.2) (sub_pos.mpr hu.2)
  intro s t hst
  by_cases hs : s ≤ u
  · by_cases ht : t ≤ u
    · simp only [warp, if_pos hs, if_pos ht, add_lt_add_iff_left]
      exact mul_lt_mul_of_pos_right (sub_lt_sub_right hst _) leftPos
    · simp only [warp, if_pos hs, if_neg ht, add_lt_add_iff_left]
      exact (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) leftPos.le).trans_lt
        (mul_pos (sub_pos.mpr (lt_of_not_ge ht)) rightPos)
  · have ht : ¬ t ≤ u := fun h => hs (hst.le.trans h)
    simp only [warp, if_neg hs, if_neg ht, add_lt_add_iff_left]
    exact mul_lt_mul_of_pos_right (sub_lt_sub_right hst _) rightPos

private theorem warp_fixes {a b u v : ℝ}
    (hu : a < u ∧ u < b) : warp a b u v a = a ∧ warp a b u v b = b := by
  constructor
  · simp only [warp, if_pos hu.1.le]
    field_simp [ne_of_gt (sub_pos.mpr hu.1)]
    ring
  · simp only [warp, if_neg (not_le.mpr hu.2)]
    field_simp [ne_of_gt (sub_pos.mpr hu.2)]

private theorem warp_inverse {a b u v : ℝ}
    (hu : a < u ∧ u < b) (hv : a < v ∧ v < b) (t : ℝ) :
    warp a b v u (warp a b u v t) = t := by
  have hm := warp_strict hu hv
  by_cases h : t ≤ u
  · have h' : warp a b u v t ≤ v := by simpa only [warp_at_knot] using hm.monotone h
    rw [warp, if_pos h', warp, if_pos h]
    field_simp [ne_of_gt (sub_pos.mpr hu.1), ne_of_gt (sub_pos.mpr hv.1)]
    ring
  · have h' : ¬ warp a b u v t ≤ v := by
      simpa only [warp_at_knot, not_le] using hm (lt_of_not_ge h)
    rw [warp, if_neg h', warp, if_neg h]
    field_simp [ne_of_gt (sub_pos.mpr hu.2), ne_of_gt (sub_pos.mpr hv.2)]
    ring

private abbrev InCell (x : ℤ → ℝ) (n : ℤ) (t : ℝ) :=
  x n < t ∧ t < x (n + 1)

private theorem cell_unique {x : ℤ → ℝ} (hx : StrictMono x) {n m : ℤ} {t : ℝ}
    (hn : InCell x n t) (hm : InCell x m t) : n = m := by
  apply le_antisymm <;> by_contra! h
  · exact (not_lt_of_ge (hx.monotone (show m + 1 ≤ n by omega)))
      (hn.1.trans hm.2)
  · exact (not_lt_of_ge (hx.monotone (show n + 1 ≤ m by omega)))
      (hm.1.trans hn.2)

private def interpolate (x q r : ℤ → ℝ) (t : ℝ) : ℝ := by
  classical
  exact if h : ∃ n, InCell x n t then
    warp (x h.choose) (x (h.choose + 1)) (q h.choose) (r h.choose) t
  else t

private theorem interpolate_in {x q r : ℤ → ℝ} (hx : StrictMono x) {n : ℤ} {t : ℝ}
    (hn : InCell x n t) :
    interpolate x q r t = warp (x n) (x (n + 1)) (q n) (r n) t := by
  classical
  have h : ∃ m, InCell x m t := ⟨n, hn⟩
  simp only [interpolate, dif_pos h, cell_unique hx h.choose_spec hn]

private theorem interpolate_out {x q r : ℤ → ℝ} {t : ℝ}
    (ht : ¬ ∃ n, InCell x n t) : interpolate x q r t = t := by
  classical
  simp only [interpolate, dif_neg ht]

private theorem interpolate_mem {x q r : ℤ → ℝ} (hx : StrictMono x)
    (hq : ∀ n, InCell x n (q n)) (hr : ∀ n, InCell x n (r n))
    {n : ℤ} {t : ℝ} (ht : InCell x n t) : InCell x n (interpolate x q r t) := by
  rw [interpolate_in hx ht]
  have hs := warp_strict (hq n) (hr n)
  have hfix := warp_fixes (v := r n) (hq n)
  exact ⟨by simpa only [hfix.1] using hs ht.1, by simpa only [hfix.2] using hs ht.2⟩

private theorem interpolate_strict {x q r : ℤ → ℝ} (hx : StrictMono x)
    (hq : ∀ n, InCell x n (q n)) (hr : ∀ n, InCell x n (r n)) :
    StrictMono (interpolate x q r) := by
  intro s t hst
  by_cases hs : ∃ n, InCell x n s
  · obtain ⟨n, hn⟩ := hs
    have hs' := interpolate_mem hx hq hr hn
    by_cases hsame : t < x (n + 1)
    · have ht : InCell x n t := ⟨hn.1.trans hst, hsame⟩
      rw [interpolate_in hx hn, interpolate_in hx ht]
      exact warp_strict (hq n) (hr n) hst
    · have hnt : x (n + 1) ≤ t := le_of_not_gt hsame
      by_cases ht : ∃ m, InCell x m t
      · obtain ⟨m, hm⟩ := ht
        have hind : n < m := by
          by_contra! h
          have hle := hx.monotone (show m + 1 ≤ n + 1 by omega)
          exact (not_lt_of_ge hnt) (hm.2.trans_le hle)
        exact hs'.2.trans ((hx.monotone (show n + 1 ≤ m by omega)).trans_lt
          (interpolate_mem hx hq hr hm).1)
      · rw [interpolate_out ht]
        exact hs'.2.trans_le hnt
  · rw [interpolate_out hs]
    by_cases ht : ∃ m, InCell x m t
    · obtain ⟨m, hm⟩ := ht
      have hsm : s ≤ x m := by
        by_contra! h
        exact hs ⟨m, h, hst.trans hm.2⟩
      exact hsm.trans_lt (interpolate_mem hx hq hr hm).1
    · simpa only [interpolate_out ht] using hst

/-- Prescribe the image of one interior point in each gap. A single increasing
order isomorphism realizes the prescriptions and fixes all dividing points. -/
theorem exists_interlacing_orderIso (x q r : ℤ → ℝ) (hx : StrictMono x)
    (hq : ∀ n, x n < q n ∧ q n < x (n + 1))
    (hr : ∀ n, x n < r n ∧ r n < x (n + 1)) :
    ∃ g : ℝ ≃o ℝ, (∀ n, g (x n) = x n) ∧ (∀ n, g (q n) = r n) := by
  let g := interpolate x q r
  have gm : StrictMono g := interpolate_strict hx hq hr
  have gs : Function.Surjective g := by
    intro t
    by_cases h : ∃ n, InCell x n t
    · obtain ⟨n, hn⟩ := h
      refine ⟨interpolate x r q t, ?_⟩
      change interpolate x q r _ = t
      rw [interpolate_in hx (interpolate_mem hx hr hq hn), interpolate_in hx hn]
      exact warp_inverse (hr n) (hq n) t
    · exact ⟨t, interpolate_out h⟩
  refine ⟨gm.orderIsoOfSurjective g gs, ?_, ?_⟩
  · intro n
    apply interpolate_out
    rintro ⟨m, hm⟩
    have hmn : m < n := hx.lt_iff_lt.mp hm.1
    have hnm : n < m + 1 := hx.lt_iff_lt.mp hm.2
    omega
  · intro n
    change interpolate x q r (q n) = r n
    rw [interpolate_in hx (hq n), warp_at_knot]

/-- Move all chosen knots to the midpoints of their respective cells, at once,
by a single continuous strictly increasing link function on the real line. -/
theorem exists_midpoint_link (x q : ℤ → ℝ) (hx : StrictMono x)
    (hq : ∀ n, x n < q n ∧ q n < x (n + 1)) :
    ∃ g : ℝ → ℝ, Continuous g ∧ StrictMono g ∧
      (∀ n, g (x n) = x n) ∧ (∀ n, g (q n) = (x n + x (n + 1)) / 2) := by
  let r := fun n : ℤ => (x n + x (n + 1)) / 2
  have hr (n : ℤ) : x n < r n ∧ r n < x (n + 1) := by
    have h := hx (show n < n + 1 by omega)
    dsimp [r]
    constructor <;> linarith
  obtain ⟨g, hfix, hmid⟩ := exists_interlacing_orderIso x q r hx hq hr
  exact ⟨g, g.continuous, g.strictMono, hfix, hmid⟩

end
end RisingSea
