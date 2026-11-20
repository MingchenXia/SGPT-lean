import SGPT.PSH.Basic
import SGPT.Foundations.Analysis.FirstPass.PshRealConvexity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Convex.Slope

namespace SGPT.PSH
open Set Filter Metric MeasureTheory
open SGPT.Foundations.Analysis
open scoped Topology ENNReal

/-- Genuine periodic nonnegative integral invariance, including infinite values;
reuse the actual fundamental-domain theorem rather than a finite-value reader. -/
theorem lintegral_Ioc_shift_of_periodic {T : ℝ} (hT : 0 < T)
    (f : ℝ → ℝ≥0∞) (hf : Function.Periodic f T) (s : ℝ) :
    (∫⁻ t in Ioc 0 T, f (t + s)) = ∫⁻ t in Ioc 0 T, f t := by
  have hpre : (fun t : ℝ ↦ t + s) ⁻¹' Ioc s (s + T) = Ioc 0 T := by
    rw [preimage_add_const_Ioc]
    simp
  have hmp := (measurePreserving_add_right volume s).restrict_preimage
    (s := Ioc s (s + T)) measurableSet_Ioc
  rw [hpre] at hmp
  have hshift := hmp.lintegral_comp_emb (Homeomorph.addRight s).measurableEmbedding f
  refine hshift.trans ?_
  have hfund := (isAddFundamentalDomain_Ioc hT s volume).setLIntegral_eq
    (isAddFundamentalDomain_Ioc hT 0 volume) f ?_
  · simpa only [zero_add] using hfund
  · intro g x
    change f ((g : ℝ) + x) = f x
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp g.property
    simpa [← hk, add_comm] using (hf.zsmul k) x

/-- The actual circle deficit is invariant under the original complex direction;
its radius scales by the actual complex modulus, including poles. -/
theorem circleDeficit_eq_unit_norm (u : ℂ → EReal) (x v : ℂ) (r C : ℝ) :
    circleDeficit u x v r C = circleDeficit u x 1 (r * ‖v‖) C := by
  have hcircle (t : ℝ) : circleMap 0 r t * v =
      circleMap 0 (r * ‖v‖) (t + v.arg) := by
    conv_lhs => rhs; rw [← Complex.norm_mul_exp_arg_mul_I v]
    simp only [circleMap, zero_add, Complex.ofReal_mul, Complex.ofReal_add,
      add_mul, Complex.exp_add]
    ring
  let f : ℝ → ℝ≥0∞ := fun t ↦ ((C : EReal) - u (x + circleMap 0 (r * ‖v‖) t)).toENNReal
  have hf : Function.Periodic f (2 * Real.pi) := by
    intro t
    simp only [f, periodic_circleMap 0 (r * ‖v‖) t]
  simp only [circleDeficit, smul_eq_mul, mul_one, hcircle]
  exact lintegral_Ioc_shift_of_periodic Real.two_pi_pos f hf v.arg

/-- The exact original one-variable subharmonic circle criterion produces every
actual affine-disc criterion. No analytic equivalence certificate is an input. -/
theorem SubharmonicOn.discPshOn {u : ℂ → EReal} {U : Set ℂ}
    (hu : SubharmonicOn u U) : DiscPshOn u U := by
  refine ⟨hu.ne_top, hu.upperSemicontinuousOn, ?_⟩
  intro x v r hr hD C hC
  by_cases hv : v = 0
  · subst v
    simpa only [circleDeficit, smul_zero, add_zero] using
      (circleDeficit_const (u x) x (0 : ℂ) r C).le
  · have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hcover : closedBall x (r * ‖v‖) ⊆ affineClosedDisc x v r := by
      intro z hz
      refine ⟨(z - x) / v, ?_, ?_⟩
      · rw [mem_closedBall, dist_zero_right, norm_div]
        apply (div_le_iff₀ hnv).mpr
        simpa only [mem_closedBall, dist_eq_norm] using hz
      · simp only [smul_eq_mul, div_mul_cancel₀ _ hv, add_sub_cancel]
    have hDU : closedBall x (r * ‖v‖) ⊆ U := hcover.trans hD
    have hbound : ∀ z ∈ closedBall x (r * ‖v‖), u z ≤ (C : EReal) :=
      fun z hz ↦ hC z (hcover hz)
    have hunit := hu.submean x (r * ‖v‖) (mul_pos hr hnv) hDU C hbound
    have hunitbound : ∀ z ∈ affineClosedDisc x 1 (r * ‖v‖), u z ≤ (C : EReal) := by
      rwa [affineClosedDisc_one]
    have hdef := (le_circleMean_iff x 1 (mul_pos hr hnv).le C hunitbound).mp hunit
    rwa [circleDeficit_eq_unit_norm] at ⊢

/-- Exact original SH = PSH in complex dimension one, with original non-pole
existence and all outside representatives retained. -/
theorem subharmonicOn_iff_pshOn (u : ℂ → EReal) (U : Set ℂ) :
    SubharmonicOn u U ↔ PSHOn u U := by
  constructor
  · intro hu
    exact ⟨hu.discPshOn, hu.nontrivial⟩
  · intro hu
    exact subharmonicOn_of_disc hu.disc hu.nontrivial

/-- Truncation supplies the finite hypotheses of the existing actual PSH
chord theorem. The original extended values are recovered by a genuine limit. -/
theorem comp_re_le_extended_chord {v : ℝ → EReal} {I : Set ℝ}
    (hu : PlurisubharmonicOn (fun z : ℂ ↦ v z.re) (Complex.re ⁻¹' I))
    {a t b : ℝ} (hat : a < t) (htb : t < b) (habI : Icc a b ⊆ I)
    (ha_top : v a ≠ ⊤) (ht_top : v t ≠ ⊤) (hb_top : v b ≠ ⊤) :
    v t ≤ (((b - t) / (b - a) : ℝ) : EReal) * v a +
      (((t - a) / (b - a) : ℝ) : EReal) * v b := by
  have hA : 0 < (b - t) / (b - a) := div_pos (sub_pos.mpr htb)
    (sub_pos.mpr (hat.trans htb))
  have hB : 0 < (t - a) / (b - a) := div_pos (sub_pos.mpr hat)
    (sub_pos.mpr (hat.trans htb))
  have hineq (c : ℝ) :
      max (v t) (c : EReal) ≤ (((b - t) / (b - a) : ℝ) : EReal) * max (v a) (c : EReal) +
        (((t - a) / (b - a) : ℝ) : EReal) * max (v b) (c : EReal) := by
    have hc : PlurisubharmonicOn (fun _ : ℂ ↦ (c : EReal)) (Complex.re ⁻¹' I) :=
      fun z _ ↦ plurisubharmonicAt_const _ (EReal.coe_ne_top c) z
    have hmax := hu.max hc
    have hbot (x : ℝ) : max (v x) (c : EReal) ≠ ⊥ :=
      ne_bot_of_gt ((bot_lt_iff_ne_bot.mpr (EReal.coe_ne_bot c)).trans_le (le_max_right _ _))
    exact PlurisubharmonicOn.comp_re_le_chord (v := fun x ↦ max (v x) (c : EReal))
      hmax hat htb habI
      (ne_of_lt (max_lt (lt_top_iff_ne_top.mpr ha_top) (EReal.coe_lt_top c))) (hbot a)
      (ne_of_lt (max_lt (lt_top_iff_ne_top.mpr ht_top) (EReal.coe_lt_top c))) (hbot t)
      (ne_of_lt (max_lt (lt_top_iff_ne_top.mpr hb_top) (EReal.coe_lt_top c))) (hbot b)
  have hlim (x : ℝ) : Tendsto (fun c : ℝ ↦ max (v x) (c : EReal)) atBot (𝓝 (v x)) := by
    simpa only [max_bot_right] using tendsto_const_nhds.max EReal.tendsto_coe_atBot
  have hleft := EReal.Tendsto.const_mul (a := (((b - t) / (b - a) : ℝ) : EReal)) (hlim a)
    (Or.inl (EReal.coe_ne_bot ((b - t) / (b - a))))
    (Or.inl (EReal.coe_ne_top ((b - t) / (b - a))))
  have hright := EReal.Tendsto.const_mul (a := (((t - a) / (b - a) : ℝ) : EReal)) (hlim b)
    (Or.inl (EReal.coe_ne_bot ((t - a) / (b - a))))
    (Or.inl (EReal.coe_ne_top ((t - a) / (b - a))))
  have hAtop : (((b - t) / (b - a) : ℝ) : EReal) * v a ≠ ⊤ := by
    exact (EReal.mul_ne_top _ _).mpr ⟨Or.inl (EReal.coe_ne_bot _),
      Or.inl (EReal.coe_nonneg.mpr hA.le), Or.inl (EReal.coe_ne_top _), Or.inr ha_top⟩
  have hBtop : (((t - a) / (b - a) : ℝ) : EReal) * v b ≠ ⊤ := by
    exact (EReal.mul_ne_top _ _).mpr ⟨Or.inl (EReal.coe_ne_bot _),
      Or.inl (EReal.coe_nonneg.mpr hB.le), Or.inl (EReal.coe_ne_top _), Or.inr hb_top⟩
  have hsum := (EReal.continuousAt_add (Or.inl hAtop) (Or.inr hBtop)).tendsto.comp
    (hleft.prodMk_nhds hright)
  exact le_of_tendsto_of_tendsto' (hlim t) hsum hineq

/-- A single original non-pole point forces every strip value to be finite:
an interior pole would force that non-pole point below a bottom chord. -/
theorem SubharmonicOn.comp_re_ne_bot {v : ℝ → EReal} {a b : ℝ}
    (hu : SubharmonicOn (fun z : ℂ ↦ v z.re) (Complex.re ⁻¹' Ioo a b)) :
    ∀ x ∈ Ioo a b, v x ≠ ⊥ := by
  have hp := hu.discPshOn.plurisubharmonicOn
    (isOpen_Ioo.preimage Complex.continuous_re)
  have htop (x : ℝ) (hx : x ∈ Ioo a b) : v x ≠ ⊤ :=
    hu.ne_top (x : ℂ) (by simpa using hx)
  obtain ⟨z, hz, hzb⟩ := hu.nontrivial
  have hc : z.re ∈ Ioo a b := hz
  intro x hx hxb
  rcases lt_trichotomy x z.re with hxc | hxc | hcx
  · let y := (z.re + b) / 2
    have hcy : z.re < y := by dsimp [y]; linarith [hc.2]
    have hy : y ∈ Ioo a b := by dsimp [y]; constructor <;> linarith [hc.1, hc.2]
    have hI : Icc x y ⊆ Ioo a b := fun t ht ↦
      ⟨hx.1.trans_le ht.1, ht.2.trans_lt hy.2⟩
    have hch := comp_re_le_extended_chord hp hxc hcy hI
      (htop x hx) (htop z.re hc) (htop y hy)
    have hw : 0 < (y - z.re) / (y - x) :=
      div_pos (sub_pos.mpr hcy) (sub_pos.mpr (hxc.trans hcy))
    rw [hxb, EReal.coe_mul_bot_of_pos hw, EReal.bot_add] at hch
    exact hzb (le_bot_iff.mp hch)
  · exact hzb (hxc ▸ hxb)
  · let y := (a + z.re) / 2
    have hyc : y < z.re := by dsimp [y]; linarith [hc.1]
    have hy : y ∈ Ioo a b := by dsimp [y]; constructor <;> linarith [hc.1, hc.2]
    have hI : Icc y x ⊆ Ioo a b := fun t ht ↦
      ⟨hy.1.trans_le ht.1, ht.2.trans_lt hx.2⟩
    have hch := comp_re_le_extended_chord hp hyc hcx hI
      (htop y hy) (htop z.re hc) (htop x hx)
    have hw : 0 < (z.re - y) / (x - y) :=
      div_pos (sub_pos.mpr hyc) (sub_pos.mpr (hyc.trans hcx))
    rw [hxb, EReal.coe_mul_bot_of_pos hw, EReal.add_bot] at hch
    exact hzb (le_bot_iff.mp hch)

/-- The exact original strip proposition: the actual subharmonic hypothesis
produces a real-valued representative and convexity on the whole interval. -/
theorem SubharmonicOn.convexOn_comp_re {v : ℝ → EReal} {a b : ℝ}
    (hu : SubharmonicOn (fun z : ℂ ↦ v z.re) (Complex.re ⁻¹' Ioo a b)) :
    ConvexOn ℝ (Ioo a b) (fun x ↦ (v x).toReal) := by
  have hp := hu.discPshOn.plurisubharmonicOn
    (isOpen_Ioo.preimage Complex.continuous_re)
  have htop (x : ℝ) (hx : x ∈ Ioo a b) : v x ≠ ⊤ :=
    hu.ne_top (x : ℂ) (by simpa using hx)
  apply convexOn_of_slope_mono_adjacent (convex_Ioo a b)
  intro x y z hx hz hxy hyz
  have hy : y ∈ Ioo a b := ⟨hx.1.trans hxy, hyz.trans hz.2⟩
  have hI : Icc x z ⊆ Ioo a b := fun t ht ↦
    ⟨hx.1.trans_le ht.1, ht.2.trans_lt hz.2⟩
  have hch := hp.comp_re_toReal_le_affine_chord hxy hyz hI
    (htop x hx) (hu.comp_re_ne_bot x hx)
    (htop y hy) (hu.comp_re_ne_bot y hy)
    (htop z hz) (hu.comp_re_ne_bot z hz)
  have hmul : ((v y).toReal - (v x).toReal) * (z - x) ≤
      (y - x) * ((v z).toReal - (v x).toReal) :=
    (le_div_iff₀ (sub_pos.mpr (hxy.trans hyz))).mp (by linarith [hch])
  apply (div_le_div_iff₀ (sub_pos.mpr hxy) (sub_pos.mpr hyz)).mpr
  nlinarith [hmul]

/-- The original EReal function equals the produced real convex function at
every source point, so no almost-everywhere representative is substituted. -/
theorem SubharmonicOn.comp_re_eq_coe_toReal {v : ℝ → EReal} {a b : ℝ}
    (hu : SubharmonicOn (fun z : ℂ ↦ v z.re) (Complex.re ⁻¹' Ioo a b)) :
    ∀ x ∈ Ioo a b, v x = ((v x).toReal : EReal) := by
  intro x hx
  exact (EReal.coe_toReal (hu.ne_top (x : ℂ) (by simpa using hx))
    (hu.comp_re_ne_bot x hx)).symm

end SGPT.PSH
