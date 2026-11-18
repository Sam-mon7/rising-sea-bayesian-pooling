import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic.Linarith

/-! A positive fixed anchor contracts the interval of possible pooled forecasts. -/

namespace RisingSea.PriorPool

open Filter MeasureTheory Set
open scoped MeasureTheory

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

private theorem conditional_interval {n : MeasurableSpace Ω} (hn : n ≤ m) {Z : Ω → ℝ}
    (hZ : Integrable Z μ) {l u : ℝ}
    (hl : ∀ᵐ w ∂μ, l ≤ Z w) (hu : ∀ᵐ w ∂μ, Z w ≤ u) :
    ∀ᵐ w ∂μ, μ[Z|n] w ∈ Icc l u := by
  have hlo := condExp_mono (m := n) (integrable_const l) hZ hl
  have hup := condExp_mono (m := n) hZ (integrable_const u) hu
  rw [condExp_const hn] at hlo hup
  exact hlo.and hup

private theorem upper_anchor {Z X Y : Ω → ℝ} {g : ℝ → ℝ}
    (h01 : ∀ᵐ w ∂μ, Z w ∈ Icc (0 : ℝ) 1)
    (hXY : ∀ᵐ w ∂μ, X w ≤ (ae μ).limsup Z ∧ Y w ≤ (ae μ).limsup Z)
    (hc : Continuous g) (hg : Monotone g) {p a b c : ℝ}
    (hcpos : 0 < c) (ha : 0 ≤ a) (hb : 0 ≤ b) (hsum : c + a + b = 1)
    (hpool : ∀ᵐ w ∂μ, g (Z w) ≤ c * g p + a * g (X w) + b * g (Y w)) :
    g ((ae μ).limsup Z) ≤ g p := by
  let u := (ae μ).limsup Z
  have hbdUp : (ae μ).IsBoundedUnder (· ≤ ·) Z := ⟨1, h01.mono fun _ h => h.2⟩
  have hbdLo : (ae μ).IsBoundedUnder (· ≥ ·) Z := ⟨0, h01.mono fun _ h => h.1⟩
  have hgbdLo : (ae μ).IsBoundedUnder (· ≥ ·) (g ∘ Z) :=
    ⟨g 0, h01.mono fun _ h => hg h.1⟩
  have hu : g u ≤ c * g p + a * g u + b * g u := by
    calc
      g u = (ae μ).limsup (g ∘ Z) :=
        hg.map_limsup_of_continuousAt Z hc.continuousAt hbdUp hbdLo.isCoboundedUnder_le
      _ ≤ _ := ?_
    apply limsup_le_of_le hgbdLo.isCoboundedUnder_le
    filter_upwards [hpool, hXY] with w hp hxy
    exact hp.trans (add_le_add (add_le_add_left (mul_le_mul_of_nonneg_left (hg hxy.1) ha) _)
      (mul_le_mul_of_nonneg_left (hg hxy.2) hb))
  change g u ≤ g p
  by_contra! h
  nlinarith [mul_pos hcpos (sub_pos.mpr h), congrArg (fun t : ℝ => t * g u) hsum]

/-- An anchor of positive weight makes a bounded posterior pool trivial when the link
extends continuously and strictly increasingly across the probability endpoints.
Here the anchor can be any real number. Calibration forces all three forecasts to equal it. -/
theorem bounded_link_rigidity
    {mX mY : MeasurableSpace Ω} (hmX : mX ≤ m) (hmY : mY ≤ m)
    {Z X Y : Ω → ℝ} (hZ : Integrable Z μ) (h01 : ∀ᵐ w ∂μ, Z w ∈ Icc (0 : ℝ) 1)
    (hX : X =ᵐ[μ] μ[Z|mX]) (hY : Y =ᵐ[μ] μ[Z|mY])
    {g : ℝ → ℝ} (hc : Continuous g) (hg : StrictMono g)
    {p a b c : ℝ} (hcpos : 0 < c) (ha : 0 ≤ a) (hb : 0 ≤ b) (hsum : c + a + b = 1)
    (hpool : ∀ᵐ w ∂μ, g (Z w) = c * g p + a * g (X w) + b * g (Y w)) :
    ∀ᵐ w ∂μ, Z w = p ∧ X w = p ∧ Y w = p := by
  let F := ae μ
  let u := F.limsup Z
  let l := F.liminf Z
  have hbdUp : F.IsBoundedUnder (· ≤ ·) Z := ⟨1, h01.mono fun _ h => h.2⟩
  have hbdLo : F.IsBoundedUnder (· ≥ ·) Z := ⟨0, h01.mono fun _ h => h.1⟩
  have hZu : ∀ᵐ w ∂μ, Z w ≤ u := eventually_le_limsup hbdUp
  have hZl : ∀ᵐ w ∂μ, l ≤ Z w := eventually_liminf_le hbdLo
  have hCX := conditional_interval (m := m) (μ := μ) hmX hZ hZl hZu
  have hCY := conditional_interval (m := m) (μ := μ) hmY hZ hZl hZu
  have hXY : ∀ᵐ w ∂μ, X w ∈ Icc l u ∧ Y w ∈ Icc l u := by
    filter_upwards [hX, hY, hCX, hCY] with w hx hy hcx hcy
    exact ⟨hx ▸ hcx, hy ▸ hcy⟩
  have hgbdUp : F.IsBoundedUnder (· ≤ ·) (g ∘ Z) :=
    ⟨g 1, h01.mono fun _ h => hg.monotone h.2⟩
  have hup : u ≤ p := hg.le_iff_le.mp (upper_anchor (m := m) (μ := μ) h01 (hXY.mono fun _ h =>
    ⟨h.1.2, h.2.2⟩) hc hg.monotone hcpos ha hb hsum (hpool.mono fun _ h => h.le))
  have hl : c * g p + a * g l + b * g l ≤ g l := by
    calc
      _ ≤ F.liminf (g ∘ Z) := ?_
      _ = g l := (hg.monotone.map_liminf_of_continuousAt Z hc.continuousAt
        hbdUp.isCoboundedUnder_ge hbdLo).symm
    apply le_liminf_of_le hgbdUp.isCoboundedUnder_ge
    filter_upwards [hpool, hXY] with w hp hxy
    exact (add_le_add (add_le_add_left
      (mul_le_mul_of_nonneg_left (hg.monotone hxy.1.1) ha) _)
      (mul_le_mul_of_nonneg_left (hg.monotone hxy.2.1) hb)).trans hp.ge
  have hlp : p ≤ l := hg.le_iff_le.mp (le_of_not_gt (by
    intro h
    nlinarith [mul_pos hcpos (sub_pos.mpr h), congrArg (fun t : ℝ => t * g l) hsum]))
  filter_upwards [hZl, hZu, hXY] with w hzlo hzup hxy
  exact ⟨le_antisymm (hzup.trans hup) (hlp.trans hzlo),
    le_antisymm (hxy.1.2.trans hup) (hlp.trans hxy.1.1),
    le_antisymm (hxy.2.2.trans hup) (hlp.trans hxy.2.1)⟩

/-- The Bayesian specialization. The two reports condition on sub-sigma-algebras of the
joint information. An indicator of a measurable event is one permitted bounded outcome. -/
theorem bounded_bayesian_pool_rigidity
    {mX mY mJ : MeasurableSpace Ω} (hmX : mX ≤ mJ) (hmY : mY ≤ mJ) (hmJ : mJ ≤ m)
    {F : Ω → ℝ} (hi : Integrable F μ) (hr : ∀ᵐ w ∂μ, F w ∈ Icc (0 : ℝ) 1)
    {g : ℝ → ℝ} (hc : Continuous g) (hg : StrictMono g)
    {p a b c : ℝ} (hcpos : 0 < c) (ha : 0 ≤ a) (hb : 0 ≤ b) (hsum : c + a + b = 1)
    (hpool : ∀ᵐ w ∂μ, g (μ[F|mJ] w) =
      c * g p + a * g (μ[F|mX] w) + b * g (μ[F|mY] w)) :
    ∀ᵐ w ∂μ, μ[F|mJ] w = p ∧ μ[F|mX] w = p ∧ μ[F|mY] w = p :=
  bounded_link_rigidity (m := m) (μ := μ) (hmX.trans hmJ) (hmY.trans hmJ) integrable_condExp
    (conditional_interval (m := m) (μ := μ) hmJ hi (hr.mono fun _ h => h.1) (hr.mono fun _ h => h.2))
    (condExp_condExp_of_le hmX hmJ).symm (condExp_condExp_of_le hmY hmJ).symm
    hc hg hcpos ha hb hsum hpool

/-- A finite right endpoint suffices when the anchor is the true prior. There is
no bound on the link as probabilities decrease to zero. All probabilities used
in the pool are in the half-open interval on which the link is specified. -/
theorem right_endpoint_rigidity
    {mX mY : MeasurableSpace Ω} (hmX : mX ≤ m) (hmY : mY ≤ m)
    {Z X Y : Ω → ℝ} (hZ : Integrable Z μ)
    (hr : ∀ᵐ w ∂μ, Z w ∈ Ioc (0 : ℝ) 1 ∧ X w ∈ Ioc (0 : ℝ) 1 ∧ Y w ∈ Ioc (0 : ℝ) 1)
    (hX : X =ᵐ[μ] μ[Z|mX]) (hY : Y =ᵐ[μ] μ[Z|mY])
    {g : ℝ → ℝ} (hc : ContinuousOn g (Ioc 0 1)) (hg : StrictMonoOn g (Ioc 0 1))
    {p a b c : ℝ} (hp : p ∈ Ioc (0 : ℝ) 1) (hprior : ∫ w, Z w ∂μ = p)
    (hcpos : 0 < c) (ha : 0 ≤ a) (hb : 0 ≤ b) (hsum : c + a + b = 1)
    (hpool : ∀ᵐ w ∂μ, g (Z w) = c * g p + a * g (X w) + b * g (Y w)) :
    ∀ᵐ w ∂μ, Z w = p ∧ X w = p ∧ Y w = p := by
  let clip (x : ℝ) := max p (min x 1)
  let G := g ∘ clip
  have hclip (x : ℝ) : clip x ∈ Ioc (0 : ℝ) 1 :=
    ⟨hp.1.trans_le (le_max_left _ _), max_le hp.2 (min_le_right _ _)⟩
  have hclip_p : clip p = p := by simp [clip, min_eq_left hp.2]
  have hGc : Continuous G :=
    hc.comp_continuous (continuous_const.max (continuous_id.min continuous_const)) hclip
  have hGm : Monotone G := fun x y h => hg.monotoneOn (hclip x) (hclip y)
    (max_le_max_left _ (min_le_min_right _ h))
  have hGp : G p = g p := congrArg g hclip_p
  have hfloor (x : ℝ) : g p ≤ G x :=
    hg.monotoneOn hp (hclip x) (le_max_left _ _)
  have hraise {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) : g x ≤ G x :=
    hg.monotoneOn hx (hclip x) (by simp [clip, min_eq_left hx.2])
  have hbound : ∀ᵐ w ∂μ, G (Z w) ≤ c * G p + a * G (X w) + b * G (Y w) := by
    filter_upwards [hr, hpool] with w hw hh
    rw [hGp]
    by_cases hl : Z w ≤ p
    · have hz : G (Z w) ≤ g p := (hGm hl).trans_eq hGp
      calc
        _ ≤ g p := hz
        _ = c * g p + a * g p + b * g p := by
          nlinarith [congrArg (fun t : ℝ => t * g p) hsum]
        _ ≤ _ := add_le_add (add_le_add_left (mul_le_mul_of_nonneg_left (hfloor _) ha) _)
          (mul_le_mul_of_nonneg_left (hfloor _) hb)
    · have hz : G (Z w) = g (Z w) := by
        simp [G, clip, min_eq_left hw.1.2, max_eq_right (le_of_not_ge hl)]
      rw [hz, hh]
      exact add_le_add (add_le_add_left (mul_le_mul_of_nonneg_left (hraise hw.2.1) ha) _)
        (mul_le_mul_of_nonneg_left (hraise hw.2.2) hb)
  have h01 : ∀ᵐ w ∂μ, Z w ∈ Icc (0 : ℝ) 1 := hr.mono fun _ h => mem_Icc_of_Ioc h.1
  let u := (ae μ).limsup Z
  have hub : (ae μ).IsBoundedUnder (· ≤ ·) Z := ⟨1, h01.mono fun _ h => h.2⟩
  have hZu : ∀ᵐ w ∂μ, Z w ≤ u := eventually_le_limsup hub
  have hZ0 : ∀ᵐ w ∂μ, 0 ≤ Z w := h01.mono fun _ h => h.1
  have hCX := conditional_interval (m := m) (μ := μ) hmX hZ hZ0 hZu
  have hCY := conditional_interval (m := m) (μ := μ) hmY hZ hZ0 hZu
  have hupper : G u ≤ G p := by
    apply upper_anchor (m := m) (μ := μ) h01 _ hGc hGm hcpos ha hb hsum hbound
    filter_upwards [hX, hY, hCX, hCY] with w hx hy hcx hcy
    exact ⟨hx ▸ hcx.2, hy ▸ hcy.2⟩
  have hle : Z ≤ᵐ[μ] fun _ => p := by
    filter_upwards [hZu, hr] with w hz hw
    exact (hg.le_iff_le hw.1 hp).mp
      ((hraise hw.1).trans ((hGm hz).trans (hupper.trans_eq hGp)))
  have heq : Z =ᵐ[μ] fun _ => p := (integral_eq_iff_of_ae_le hZ (integrable_const p) hle).mp
    (by simpa using hprior)
  have hx := hX.trans (condExp_congr_ae (m := mX) heq)
  have hy := hY.trans (condExp_congr_ae (m := mY) heq)
  rw [condExp_const hmX] at hx
  rw [condExp_const hmY] at hy
  exact heq.and (hx.and hy)

/-- The corresponding result for a finite left endpoint, by complementing all probabilities. -/
theorem left_endpoint_rigidity
    {mX mY : MeasurableSpace Ω} (hmX : mX ≤ m) (hmY : mY ≤ m)
    {Z X Y : Ω → ℝ} (hZ : Integrable Z μ)
    (hr : ∀ᵐ w ∂μ, Z w ∈ Ico (0 : ℝ) 1 ∧ X w ∈ Ico (0 : ℝ) 1 ∧ Y w ∈ Ico (0 : ℝ) 1)
    (hX : X =ᵐ[μ] μ[Z|mX]) (hY : Y =ᵐ[μ] μ[Z|mY])
    {g : ℝ → ℝ} (hc : ContinuousOn g (Ico 0 1)) (hg : StrictMonoOn g (Ico 0 1))
    {p a b c : ℝ} (hp : p ∈ Ico (0 : ℝ) 1) (hprior : ∫ w, Z w ∂μ = p)
    (hcpos : 0 < c) (ha : 0 ≤ a) (hb : 0 ≤ b) (hsum : c + a + b = 1)
    (hpool : ∀ᵐ w ∂μ, g (Z w) = c * g p + a * g (X w) + b * g (Y w)) :
    ∀ᵐ w ∂μ, Z w = p ∧ X w = p ∧ Y w = p := by
  let R (x : ℝ) := 1 - x
  have hR : Continuous R := continuous_const.sub continuous_id
  have hRR (x : ℝ) : R (R x) = x := by simp [R]
  have hRin {x : ℝ} (hx : x ∈ Ico 0 1) : R x ∈ Ioc 0 1 :=
    ⟨sub_pos.mpr hx.2, sub_le_self _ hx.1⟩
  have hRout {x : ℝ} (hx : x ∈ Ioc 0 1) : R x ∈ Ico 0 1 :=
    ⟨sub_nonneg.mpr hx.2, sub_lt_self _ hx.1⟩
  have hreflect {n : MeasurableSpace Ω} (hn : n ≤ m) {S : Ω → ℝ}
      (hs : S =ᵐ[μ] μ[Z|n]) : R ∘ S =ᵐ[μ] μ[R ∘ Z|n] := by
    have hsub := condExp_sub (integrable_const (1 : ℝ)) hZ n
    rw [condExp_const hn] at hsub
    filter_upwards [hs, hsub] with w hw hs'
    simpa only [Function.comp_apply, R, hw, Pi.sub_apply] using hs'.symm
  let G (x : ℝ) := -g (R x)
  have hGc : ContinuousOn G (Ioc 0 1) :=
    (hc.comp hR.continuousOn (fun _ hx => hRout hx)).neg
  have hGm : StrictMonoOn G (Ioc 0 1) := fun _ hx _ hy hxy =>
    neg_lt_neg (hg (hRout hy) (hRout hx) (sub_lt_sub_left hxy _))
  have hZ' : Integrable (R ∘ Z) μ := (integrable_const (1 : ℝ)).sub hZ
  have hprior' : ∫ w, R (Z w) ∂μ = R p := by
    dsimp [R]
    rw [integral_sub (integrable_const _) hZ, hprior]
    simp
  have hpool' : ∀ᵐ w ∂μ, G (R (Z w)) =
      c * G (R p) + a * G (R (X w)) + b * G (R (Y w)) := by
    filter_upwards [hpool] with w h
    simp only [G, hRR, mul_neg]
    linarith
  have hrig := right_endpoint_rigidity (m := m) (μ := μ) hmX hmY hZ'
    (hr.mono fun _ h => ⟨hRin h.1, hRin h.2.1, hRin h.2.2⟩)
    (hreflect hmX hX) (hreflect hmY hY) hGc hGm (hRin hp) hprior' hcpos ha hb hsum hpool'
  filter_upwards [hrig] with w h
  simpa [Function.comp_def, R] using h

end RisingSea.PriorPool
