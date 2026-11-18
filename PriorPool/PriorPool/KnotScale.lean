import Mathlib.Data.Int.LeastGreatest
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import RisingSea.Link

/-! Piecewise affine interpolation between two doubly infinite increasing
sequences. The source sequence exhausts the open unit interval and the target
sequence exhausts the real line. Thus the scale is continuous on all interior
probabilities and has an inverse there. -/

namespace RisingSea.PriorPool

open Set

private theorem find_band {x : ℤ → ℝ} (hx : StrictMono x) (y : ℝ)
    (hc : (∃ n, x n ≤ y) ∧ ∃ n, y < x n) :
    ∃ n, y ∈ Ico (x n) (x (n+1)) := by
  obtain ⟨b, hb⟩ := hc.2
  have bound : ∀ z : ℤ, x z ≤ y → z ≤ b :=
    fun z hz => (hx.lt_iff_lt.mp (hz.trans_lt hb)).le
  obtain ⟨n, hn, hmax⟩ := Int.exists_greatest_of_bdd ⟨b, bound⟩ hc.1
  refine ⟨n, hn, lt_of_not_ge ?_⟩
  intro h
  have hle := hmax (n+1) h
  omega

private theorem band_unique {x : ℤ → ℝ} (hx : StrictMono x) {n m : ℤ} {y : ℝ}
    (hn : y ∈ Ico (x n) (x (n+1))) (hm : y ∈ Ico (x m) (x (m+1))) : n = m := by
  have h₁ := hx.lt_iff_lt.mp (hn.1.trans_lt hm.2)
  have h₂ := hx.lt_iff_lt.mp (hm.1.trans_lt hn.2)
  omega

private noncomputable def straight (a b c d y : ℝ) := c + (y-a) * ((d-c)/(b-a))

private theorem straight_mono {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    StrictMono (straight a b c d) := by
  intro y z hyz
  exact add_lt_add_left (mul_lt_mul_of_pos_right (sub_lt_sub_right hyz _)
    (div_pos (sub_pos.mpr hcd) (sub_pos.mpr hab))) _

private theorem straight_band {a b c d y : ℝ} (hab : a < b) (hcd : c < d)
    (hy : y ∈ Ico a b) : straight a b c d y ∈ Ico c d := by
  have h := straight_mono hab hcd
  have hleft : straight a b c d a = c := by simp [straight]
  have hright : straight a b c d b = d := by
    unfold straight
    field_simp [ne_of_gt (sub_pos.mpr hab)]
  exact ⟨by simpa only [hleft] using h.monotone hy.1,
    by simpa only [hright] using h hy.2⟩

private theorem straight_inverse {a b c d : ℝ} (hab : a < b) (hcd : c < d) (y : ℝ) :
    straight a b c d (straight c d a b y) = y := by
  unfold straight
  field_simp [ne_of_gt (sub_pos.mpr hab), ne_of_gt (sub_pos.mpr hcd)]
  ring

/-- A single increasing order isomorphism sends every source knot to the
corresponding target knot. In particular it is a continuous link on (0,1). -/
theorem exists_knot_scale (x t : ℤ → ℝ) (hx : StrictMono x) (ht : StrictMono t)
    (h01 : ∀ n, x n ∈ Ioo 0 1)
    (hxc : ∀ y ∈ Ioo (0 : ℝ) 1, (∃ n, x n ≤ y) ∧ ∃ n, y < x n)
    (htc : ∀ y : ℝ, (∃ n, t n ≤ y) ∧ ∃ n, y < t n) :
    ∃ g : Ioo (0 : ℝ) 1 ≃o ℝ, ∀ n, g ⟨x n, h01 n⟩ = t n := by
  classical
  let idx (y : Ioo (0 : ℝ) 1) := (find_band hx y (hxc y y.property)).choose
  have hidx (y : Ioo (0 : ℝ) 1) : (y : ℝ) ∈ Ico (x (idx y)) (x (idx y + 1)) :=
    (find_band hx y (hxc y y.property)).choose_spec
  let g (y : Ioo (0 : ℝ) 1) :=
    straight (x (idx y)) (x (idx y+1)) (t (idx y)) (t (idx y+1)) y
  have hstep (n : ℤ) : n < n+1 := by omega
  have hlocal (y : Ioo (0 : ℝ) 1) {n : ℤ} (hy : (y : ℝ) ∈ Ico (x n) (x (n+1))) :
      g y = straight (x n) (x (n+1)) (t n) (t (n+1)) y := by
    simp only [g, band_unique hx (hidx y) hy]
  have himage (y : Ioo (0 : ℝ) 1) : g y ∈ Ico (t (idx y)) (t (idx y+1)) :=
    straight_band (hx (hstep _)) (ht (hstep _)) (hidx y)
  have gm : StrictMono g := by
    intro u v huv
    have huv' : (u : ℝ) < v := huv
    have hi := hx.lt_iff_lt.mp (((hidx u).1.trans_lt huv').trans (hidx v).2)
    by_cases he : idx u = idx v
    · have hv := hlocal v (n := idx u) (he ▸ hidx v)
      rw [hlocal u (hidx u), hv]
      exact straight_mono (hx (hstep _)) (ht (hstep _)) huv'
    · have hs : idx u + 1 ≤ idx v := by omega
      exact (himage u).2.trans_le ((ht.monotone hs).trans (himage v).1)
  have gs : Function.Surjective g := by
    intro y
    obtain ⟨n, hn⟩ := find_band ht y (htc y)
    let w := straight (t n) (t (n+1)) (x n) (x (n+1)) y
    have hw : w ∈ Ico (x n) (x (n+1)) := straight_band (ht (hstep n)) (hx (hstep n)) hn
    have hw01 : w ∈ Ioo 0 1 := ⟨(h01 n).1.trans_le hw.1, hw.2.trans (h01 _).2⟩
    refine ⟨⟨w, hw01⟩, ?_⟩
    rw [hlocal _ hw]
    exact straight_inverse (hx (hstep n)) (ht (hstep n)) y
  refine ⟨gm.orderIsoOfSurjective g gs, fun n => ?_⟩
  change g ⟨x n, h01 n⟩ = t n
  rw [hlocal _ (show x n ∈ Ico (x n) (x (n+1)) from ⟨le_rfl, hx (hstep _)⟩)]
  simp [straight]

/-- Match the two endpoint sequences and one additional interior point in each
gap. The first change of scale fixes the endpoints' images. The interlacing
interpolation theorem then adjusts the interior points on the target scale. -/
theorem exists_interlaced_knot_scale (x t q r : ℤ → ℝ) (hx : StrictMono x) (ht : StrictMono t)
    (h01 : ∀ n, x n ∈ Ioo 0 1) (hq01 : ∀ n, q n ∈ Ioo 0 1)
    (hxc : ∀ y ∈ Ioo (0 : ℝ) 1, (∃ n, x n ≤ y) ∧ ∃ n, y < x n)
    (htc : ∀ y : ℝ, (∃ n, t n ≤ y) ∧ ∃ n, y < t n)
    (hq : ∀ n, x n < q n ∧ q n < x (n+1))
    (hr : ∀ n, t n < r n ∧ r n < t (n+1)) :
    ∃ g : Ioo (0 : ℝ) 1 ≃o ℝ, (∀ n, g ⟨x n, h01 n⟩ = t n) ∧
      (∀ n, g ⟨q n, hq01 n⟩ = r n) := by
  obtain ⟨g, hgrid⟩ := exists_knot_scale x t hx ht h01 hxc htc
  let z (n : ℤ) := g ⟨q n, hq01 n⟩
  have hz (n : ℤ) : t n < z n ∧ z n < t (n+1) := by
    rw [← hgrid n, ← hgrid (n+1)]
    exact ⟨g.strictMono (show (⟨x n, h01 n⟩ : Ioo (0:ℝ) 1) < ⟨q n, hq01 n⟩ from (hq n).1),
      g.strictMono (show (⟨q n, hq01 n⟩ : Ioo (0:ℝ) 1) < ⟨x (n+1), h01 (n+1)⟩ from (hq n).2)⟩
  obtain ⟨h, hfix, hmove⟩ := RisingSea.exists_interlacing_orderIso t z r ht hz hr
  refine ⟨g.trans h, fun n => ?_, hmove⟩
  change h (g ⟨x n, h01 n⟩) = t n
  rw [hgrid, hfix]

end RisingSea.PriorPool
