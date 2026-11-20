import SGPT.Envelopes.DNTRegRooftop
import SGPT.Okounkov.TranscendentalWNRegDNTEnvelope
import SGPT.Envelopes.SourceObstacleConcentration
import SGPT.PSH.SourceCapacity
import SGPT.Envelopes.SourceMinimalEnvelopeLocalBounds

/-!
# `C^{1,1̄}` regularity of `P_θ(f)` when `{θ}` is a Kähler class

Source `thm:DNT23_C11bar` (`author/chapter_npp.tex`, lines 1493–1499; Di Nezza–
Trapani): for a smooth closed real `(1,1)`-form `θ` representing a big class and
`f ∈ C^{1,1̄}(X)`, `P_θ(f) ∈ C^{1,1̄}(X \ nK({θ}))`; in particular
`V_θ ∈ C^{1,1̄}(X \ nK({θ}))`.

This file proves the theorem when the class `{θ}` is a **Kähler class** (`θ + ddᶜρ` is a Kähler
form for a smooth `ρ`; Kähler classes are big) and `f` is **smooth**: then `P_θ(f)` is real-valued
and `C^{1,1̄}` on all of `X`, hence on `X \ nK({θ})` (`IsCOneOneBarOn`, `C^{1,1̄}` on a subset;
`nK({θ})` is the book's non-Kähler locus `sourceNonKahlerLocus` of `def:nKlocus`, the
intersection of the polar loci of the Kähler currents with analytic singularities in `{θ}`).
The proof is a change of reference form: `v ↦ v - ρ` is a bijection from `θ`-psh to
`(θ + ddᶜρ)`-psh functions, so `P_θ(f) = P_{θ + ddᶜρ}(f - ρ) + ρ` (`rooftopEnvelope_shift`), and
Berman's estimate (`isCOneOneBar_envelopeReal`, WN-REG) applies to the Kähler form `θ + ddᶜρ`.

## Main results

* `IsCOneOneBarOn`, `IsCOneOneBar.isCOneOneBarOn`, `IsCOneOneBar.add_chartSmooth`.
* `rooftopEnvelope_shift`: `P_θ(f) = P_{θ + ddᶜρ}(f - ρ) + ρ`.
* `envelopeReal_isCOneOneBarOn_of_kahlerClass` and `minimalEnvelope_isCOneOneBarOn_of_kahlerClass`
  (source `thm:DNT23_C11bar` for a Kähler class and a smooth `f`, and its "in particular").
* `thetaPshSupremum_eq_rooftopEnvelope_zero`: `V_θ = sup{φ ∈ PSH(X,θ) : φ ≤ 0} = P_θ(0)` when
  `PSH(X,θ) ≠ ∅`.
* `sourceObstacleEnvelope_isCOneOneBarOn_of_kahlerClass`,
  `sourceMinimalEnvelope_isCOneOneBarOn_of_kahlerClass`: the same statements for the source
  objects `P_θ(f) = sourceRelativeEnvelope θ ⊤ f` (`def:Pthetaf`) and
  `V_θ = sourceMinimalEnvelope θ` (`eq:Vtheta`).
* `sourceObstacleEnvelope_min_isCOneOneBar`: `prop:DR16_C11bar` for smooth obstacles
  (`DNTRegRooftop.isCOneOneBar_envelopeReal_min`) with the source envelope.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace SGPT.Envelopes.DNTReg

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Okounkov.TranscendentalWNReg

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-! ### `C^{1,1̄}` on an open subset -/

/-- **`C^{1,1̄}(U)`** for a subset `U`: `f` is continuous on `U` and, in every holomorphic chart,
its distributional complex Hessian is locally bounded on the part of the chart over `U`. -/
def IsCOneOneBarOn (U : Set Y) (f : Y → ℝ) : Prop :=
  ContinuousOn f U ∧ ∀ e : ComplexChart N Y,
    HasLocallyBoundedComplexHessianOn (fun z => f (e.val.symm z))
      (e.val.target ∩ e.val.symm ⁻¹' U)

omit [IsComplexManifold N Y] in
theorem IsCOneOneBar.isCOneOneBarOn {f : Y → ℝ} (hf : IsCOneOneBar (N := N) f) (U : Set Y) :
    IsCOneOneBarOn (N := N) U f :=
  ⟨hf.1.continuousOn, fun e K hK hKU => hf.2 e K hK (hKU.trans inter_subset_left)⟩

/-- A `C^{1,1̄}` function plus a chart-smooth function is `C^{1,1̄}`. -/
theorem IsCOneOneBar.add_chartSmooth {f ρ : Y → ℝ} (hf : IsCOneOneBar (N := N) f)
    (hρ : ChartSmooth (n := N) ρ) : IsCOneOneBar (N := N) (fun y => f y + ρ y) := by
  refine ⟨hf.1.add (YauUniformEstimate.continuous_of_chartSmooth hρ), fun e K hK hKt => ?_⟩
  obtain ⟨C₁, hC₁⟩ := hf.2 e K hK hKt
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_line_le_of_isCompact (ddcClosedForm ρ hρ).val e hK hKt
  refine ⟨C₁ + Real.pi * C₂, fun φ hφ hφK v => ?_⟩
  have hφc : HasCompactSupport φ := hK.of_isClosed_subset (isClosed_tsupport φ) hφK
  have hsupp : tsupport φ ⊆ e.val.target := hφK.trans hKt
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hLc : Continuous fun z => leviForm φ z v := continuous_leviForm hφ2 v
  have hsub : ∀ w, Function.support (fun x => realHessian φ x w w) ⊆ tsupport φ :=
    fun w x hx => support_iteratedFDeriv_subset (𝕜 := ℝ) (n := 2) (f := φ) fun h => hx (by
      simp [realHessian, h])
  have hLsub : Function.support (fun z => leviForm φ z v) ⊆ tsupport φ := by
    intro z hz
    by_contra hzφ
    apply hz
    have h1 : realHessian φ z v v = 0 := by
      by_contra h
      exact hzφ (hsub v h)
    have h2 : realHessian φ z (Complex.I • v) (Complex.I • v) = 0 := by
      by_contra h
      exact hzφ (hsub (Complex.I • v) h)
    show leviForm φ z v = 0
    simp only [leviForm, h1, h2, add_zero, zero_div]
  have hLcs : HasCompactSupport fun z => leviForm φ z v := hφc.mono' hLsub
  have hLsupp : tsupport (fun z => leviForm φ z v) ⊆ e.val.target :=
    (closure_minimal hLsub (isClosed_tsupport φ)).trans hsupp
  have hfc : ContinuousOn (fun z => f (e.val.symm z)) e.val.target :=
    hf.1.comp_continuousOn e.val.continuousOn_symm
  have hρc : ContinuousOn (fun z => ρ (e.val.symm z)) e.val.target := (hρ e).continuousOn
  have hI₁ := integrable_mul_of_continuousOn e.val.open_target hfc hLc hLcs hLsupp
  have hI₂ := integrable_mul_of_continuousOn e.val.open_target hρc hLc hLcs hLsupp
  have hsplit : ∫ z, (f (e.val.symm z) + ρ (e.val.symm z)) * leviForm φ z v =
      (∫ z, f (e.val.symm z) * leviForm φ z v) + ∫ z, ρ (e.val.symm z) * leviForm φ z v := by
    rw [← integral_add hI₁ hI₂]
    congr 1
    funext z
    ring
  have hibp := integral_mul_leviForm_eq e.val.open_target (hρ e) hφ hφc hsupp v
  -- the smooth part
  have hρbound : |∫ z, ρ (e.val.symm z) * leviForm φ z v| ≤
      Real.pi * C₂ * ‖v‖ ^ 2 * ∫ z, |φ z| := by
    rw [hibp]
    have hpt : ∀ z, |leviForm (fun w => ρ (e.val.symm w)) z v * φ z| ≤
        Real.pi * C₂ * ‖v‖ ^ 2 * |φ z| := by
      intro z
      by_cases hz : z ∈ K
      · have hzt := hKt hz
        have hline := hC₂ z hz v
        rw [ddc_line_eq hρ e hzt v, abs_div, abs_of_pos Real.pi_pos,
          div_le_iff₀ Real.pi_pos] at hline
        rw [abs_mul]
        have := mul_le_mul_of_nonneg_right hline (abs_nonneg (φ z))
        nlinarith [abs_nonneg (φ z)]
      · have hφz : φ z = 0 := by
          by_contra h
          exact hz (hφK (subset_tsupport φ h))
        simp [hφz]
    calc |∫ z, leviForm (fun w => ρ (e.val.symm w)) z v * φ z|
        ≤ ∫ z, |leviForm (fun w => ρ (e.val.symm w)) z v * φ z| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ z, Real.pi * C₂ * ‖v‖ ^ 2 * |φ z| := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _) ?_
            (Eventually.of_forall hpt)
          exact (hφ.continuous.abs.integrable_of_hasCompactSupport hφc.abs).const_mul _
      _ = Real.pi * C₂ * ‖v‖ ^ 2 * ∫ z, |φ z| := integral_const_mul _ _
  have h1 := hC₁ φ hφ hφK v
  rw [hsplit]
  calc |(∫ z, f (e.val.symm z) * leviForm φ z v) + ∫ z, ρ (e.val.symm z) * leviForm φ z v|
      ≤ |∫ z, f (e.val.symm z) * leviForm φ z v| + |∫ z, ρ (e.val.symm z) * leviForm φ z v| :=
        abs_add_le _ _
    _ ≤ C₁ * ‖v‖ ^ 2 * (∫ z, |φ z|) + Real.pi * C₂ * ‖v‖ ^ 2 * ∫ z, |φ z| :=
        add_le_add h1 hρbound
    _ = (C₁ + Real.pi * C₂) * ‖v‖ ^ 2 * ∫ z, |φ z| := by ring

/-! ### Changing the reference form by a smooth potential -/

theorem ereal_sub_coe_add_coe (a : EReal) (r : ℝ) : a - (r : EReal) + (r : EReal) = a := by
  induction a using EReal.rec with
  | bot => rw [EReal.bot_sub, EReal.bot_add]
  | top => rw [EReal.top_sub_coe, EReal.top_add_coe]
  | coe s => rw [← EReal.coe_sub, ← EReal.coe_add, sub_add_cancel]

theorem ereal_add_coe_sub_coe (a : EReal) (r : ℝ) : a + (r : EReal) - (r : EReal) = a := by
  induction a using EReal.rec with
  | bot => rw [EReal.bot_add, EReal.bot_sub]
  | top => rw [EReal.top_add_coe, EReal.top_sub_coe]
  | coe s => rw [← EReal.coe_add, ← EReal.coe_sub, add_sub_cancel_right]

theorem upperSemicontinuous_add_coe {u : Y → EReal} (hu : UpperSemicontinuous u) {ρ : Y → ℝ}
    (hρ : Continuous ρ) : UpperSemicontinuous fun x => u x + (ρ x : EReal) := by
  refine hu.add' (continuous_coe_real_ereal.comp hρ).upperSemicontinuous fun x => ?_
  exact EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))

theorem upperSemicontinuous_sub_coe {u : Y → EReal} (hu : UpperSemicontinuous u) {ρ : Y → ℝ}
    (hρ : Continuous ρ) : UpperSemicontinuous fun x => u x - (ρ x : EReal) := by
  have h := upperSemicontinuous_add_coe hu (ρ := fun x => -ρ x) hρ.neg
  have hfun : (fun x => u x - (ρ x : EReal)) = fun x => u x + ((-ρ x : ℝ) : EReal) := by
    funext x
    rw [EReal.coe_neg, sub_eq_add_neg]
  rw [hfun]
  exact h

/-- **Change of reference form**: for a closed real `(1,1)`-form `θ` and a chart-smooth `ρ`,
`P_θ(f) = P_{θ + ddᶜρ}(f - ρ) + ρ`. -/
theorem rooftopEnvelope_shift (θ : ClosedRealOneOneForm N Y) {ρ : Y → ℝ}
    (hρ : ChartSmooth (n := N) ρ) (f : Y → ℝ) (x : Y) :
    rooftopEnvelope θ.val (fun y => (f y : EReal)) x =
      rooftopEnvelope (θ + ddcClosedForm ρ hρ).val (fun y => ((f y - ρ y : ℝ) : EReal)) x +
        (ρ x : EReal) := by
  have hρc : Continuous ρ := YauUniformEstimate.continuous_of_chartSmooth hρ
  have hρn : ChartSmooth (n := N) (fun y => -ρ y) := fun e => (hρ e).neg
  -- `θ`-psh `↦` `(θ + ddᶜρ)`-psh
  have hto : ∀ u : Y → EReal, IsThetaPshPotential θ.val u →
      IsThetaPshPotential (θ + ddcClosedForm ρ hρ).val (fun y => u y - (ρ y : EReal)) := by
    intro u hu
    refine thetaPshPotential_sub_smooth hρ (fun e z hz => ?_) hu
    rw [ClosedRealOneOneForm.coeff_add, ddcClosedForm_coeff]
  -- `(θ + ddᶜρ)`-psh `↦` `θ`-psh
  have hfrom : ∀ w : Y → EReal, IsThetaPshPotential (θ + ddcClosedForm ρ hρ).val w →
      IsThetaPshPotential θ.val (fun y => w y + (ρ y : EReal)) := by
    intro w hw
    have h := thetaPshPotential_sub_smooth (θ := (θ + ddcClosedForm ρ hρ).val) (η := θ.val)
      hρn (fun e z hz => ?_) hw
    · have hfun : (fun y => w y - ((-ρ y : ℝ) : EReal)) = fun y => w y + (ρ y : EReal) := by
        funext y
        rw [EReal.coe_neg, sub_eq_add_neg, neg_neg]
      rw [hfun] at h
      exact h
    · rw [ClosedRealOneOneForm.coeff_add, ddcClosedForm_coeff,
        smoothDDC_neg (h := fun y => ρ (e.val.symm y)) e.val.open_target (hρ e) hz,
        add_neg_cancel_right]
  apply le_antisymm
  · -- `≤`
    have hle : rooftopEnvelope θ.val (fun y => (f y : EReal)) ≤
        fun x => rooftopEnvelope (θ + ddcClosedForm ρ hρ).val
          (fun y => ((f y - ρ y : ℝ) : EReal)) x + (ρ x : EReal) := by
      refine (rooftopEnvelope_le_iff (upperSemicontinuous_add_coe
        (upperSemicontinuous_rooftopEnvelope _ _) hρc)).mpr fun u hu huf => ?_
      have hu' := hto u hu
      have huf' : QuasiEverywhere (n := N)
          (fun y => u y - (ρ y : EReal) ≤ ((f y - ρ y : ℝ) : EReal)) :=
        huf.mono fun y hy => by
          rw [EReal.coe_sub]
          exact EReal.sub_le_sub hy le_rfl
      have hle := le_rooftopEnvelope hu' huf'
      intro y
      have h := add_le_add (hle y) (le_refl (ρ y : EReal))
      rwa [ereal_sub_coe_add_coe] at h
    exact hle x
  · -- `≥`
    have hle : rooftopEnvelope (θ + ddcClosedForm ρ hρ).val
        (fun y => ((f y - ρ y : ℝ) : EReal)) ≤
        fun x => rooftopEnvelope θ.val (fun y => (f y : EReal)) x - (ρ x : EReal) := by
      refine (rooftopEnvelope_le_iff (upperSemicontinuous_sub_coe
        (upperSemicontinuous_rooftopEnvelope _ _) hρc)).mpr fun w hw hwf => ?_
      have hw' := hfrom w hw
      have hwf' : QuasiEverywhere (n := N) (fun y => w y + (ρ y : EReal) ≤ (f y : EReal)) :=
        hwf.mono fun y hy => by
          have h := add_le_add hy (le_refl (ρ y : EReal))
          rwa [← EReal.coe_add, sub_add_cancel] at h
      have hle := le_rooftopEnvelope hw' hwf'
      intro y
      have h := EReal.sub_le_sub (hle y) (le_refl (ρ y : EReal))
      rwa [ereal_add_coe_sub_coe] at h
    have h := add_le_add (hle x) (le_refl (ρ x : EReal))
    rwa [ereal_sub_coe_add_coe] at h

/-! ### `thm:DNT23_C11bar` for a Kähler class and a smooth obstacle -/

/-- **Source `thm:DNT23_C11bar`, Kähler class and smooth obstacle.**  On a compact connected
complex manifold, let `θ` be a closed real `(1,1)`-form whose class is Kähler (`θ + ddᶜρ` is a
Kähler form for a chart-smooth `ρ`) and let `f` be chart-smooth.  Then `P_θ(f)` is real-valued
and `C^{1,1̄}` on `X`, in particular on `X \ nK({θ})`. -/
theorem envelopeReal_isCOneOneBarOn_of_kahlerClass [CompactSpace Y] [ConnectedSpace Y]
    (θ : ClosedRealOneOneForm N Y) {ρ : Y → ℝ} (hρ : ChartSmooth (n := N) ρ)
    (hK : (θ + ddcClosedForm ρ hρ).val.IsKahler) {f : Y → ℝ} (hf : ChartSmooth (n := N) f) :
    (∀ x, rooftopEnvelope θ.val (fun y => (f y : EReal)) x =
      ((envelopeReal θ f x : ℝ) : EReal)) ∧
    IsCOneOneBar (N := N) (envelopeReal θ f) ∧
    IsCOneOneBarOn (N := N)
      (SGPT.PSH.VariableComplexAtlas.sourceNonKahlerLocus (RealBottChern.ofRepresentative θ))ᶜ
      (envelopeReal θ f) := by
  set A : KahlerBackground N Y := ⟨θ + ddcClosedForm ρ hρ, hK⟩ with hAdef
  have hfρ : ChartSmooth (n := N) (fun y => f y - ρ y) := fun e => (hf e).sub (hρ e)
  obtain ⟨a, Λ, ha, hΛ, hBer⟩ := bermanSmoothEnvelopeStatement N Y A
  obtain ⟨S, hS0, hS⟩ := exists_ddc_line_le_of_chartSmooth A hfρ
  obtain ⟨B, hB⟩ := YauContinuityMethod.exists_abs_le hfρ
  have hreal := (hBer _ hfρ S hS0 hS (-B) fun y => (abs_le.mp (hB y)).1).1
  have hshift : ∀ x, rooftopEnvelope θ.val (fun y => (f y : EReal)) x =
      ((envelopeReal A.form (fun y => f y - ρ y) x + ρ x : ℝ) : EReal) := by
    intro x
    rw [rooftopEnvelope_shift θ hρ f x, EReal.coe_add]
    congr 1
    exact hreal x
  have heq : envelopeReal θ f = fun x => envelopeReal A.form (fun y => f y - ρ y) x + ρ x := by
    funext x
    simp only [envelopeReal] at hshift ⊢
    rw [hshift x, EReal.toReal_coe]
  have hC := IsCOneOneBar.add_chartSmooth (isCOneOneBar_envelopeReal A hfρ) hρ
  rw [← heq] at hC
  refine ⟨fun x => ?_, hC, IsCOneOneBar.isCOneOneBarOn hC _⟩
  rw [hshift x, heq]

/-- **Source `thm:DNT23_C11bar`, "in particular", Kähler class.**  If the class of `θ` is Kähler,
then `V_θ = P_θ(0)` is real-valued and `C^{1,1̄}` on `X`, in particular on `X \ nK({θ})`. -/
theorem minimalEnvelope_isCOneOneBarOn_of_kahlerClass [CompactSpace Y] [ConnectedSpace Y]
    (θ : ClosedRealOneOneForm N Y) {ρ : Y → ℝ} (hρ : ChartSmooth (n := N) ρ)
    (hK : (θ + ddcClosedForm ρ hρ).val.IsKahler) :
    (∀ x, rooftopEnvelope θ.val (fun _ => ((0 : ℝ) : EReal)) x =
      ((envelopeReal θ (fun _ => 0) x : ℝ) : EReal)) ∧
    IsCOneOneBar (N := N) (envelopeReal θ (fun _ => 0)) ∧
    IsCOneOneBarOn (N := N)
      (SGPT.PSH.VariableComplexAtlas.sourceNonKahlerLocus (RealBottChern.ofRepresentative θ))ᶜ
      (envelopeReal θ (fun _ => 0)) :=
  envelopeReal_isCOneOneBarOn_of_kahlerClass θ hρ hK (f := fun _ => 0)
    (fun _ => contDiffOn_const)

/-! ### The source objects `P_θ(f)` and `V_θ` -/

/-- **`V_θ = P_θ(0)`**: on a compact connected manifold with a Kähler form, if `PSH(X,θ) ≠ ∅`
then `sup{φ ∈ PSH(X,θ) : φ ≤ 0}` is the envelope `P_θ(0)`. -/
theorem thetaPshSupremum_eq_rooftopEnvelope_zero [MeasurableSpace Y] [BorelSpace Y]
    [CompactSpace Y] [ConnectedSpace Y] (w : KahlerBackground N Y) (θ : ClosedRealOneOneForm N Y)
    {φ : Y → EReal} (hφ : IsThetaPshPotential θ.val φ) :
    thetaPshSupremum θ.val = rooftopEnvelope θ.val (fun _ => ((0 : ℝ) : EReal)) := by
  have hP := isThetaPshPotential_rooftopEnvelope_of_continuous w θ
    (f := fun _ => (0 : ℝ)) continuous_const hφ
  apply le_antisymm
  · refine thetaPshSupremum_le_iff.mpr fun u hu hu0 => ?_
    refine le_rooftopEnvelope hu (quasiEverywhere_of_forall fun x => ?_)
    rw [EReal.coe_zero]
    exact hu0 x
  · refine le_thetaPshSupremum hP fun x => ?_
    have h := rooftopEnvelope_le_of_isThetaPshPotential (f := fun _ => (0 : ℝ))
      continuous_const hP x
    rw [EReal.coe_zero] at h
    exact h

section Source

open SGPT.PSH SGPT.PSH.VariableComplexAtlas

variable [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]

omit [MeasurableSpace Y] [BorelSpace Y] in
/-- **Source `thm:DNT23_C11bar`, Kähler class and smooth obstacle, with the source envelope
`P_θ(f) = sourceRelativeEnvelope θ ⊤ f`** (`def:Pthetaf`): if `θ + ddᶜρ` is a Kähler form for a
chart-smooth `ρ` and `f` is chart-smooth, then `P_θ(f)` is real-valued and its real version is
`C^{1,1̄}` on `X \ nK({θ})` (indeed on `X`). -/
theorem sourceObstacleEnvelope_isCOneOneBarOn_of_kahlerClass
    (θ : AtlasClosedRealOneOneForm (ofFixedModel N Y)) {ρ : Y → ℝ} (hρ : ChartSmooth (n := N) ρ)
    (hK : (atlasClosedFormToNative θ + ddcClosedForm ρ hρ).val.IsKahler) {f : Y → ℝ}
    (hf : ChartSmooth (n := N) f) :
    (∀ x, sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x =
      (((sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x).toReal : ℝ) : EReal)) ∧
    IsCOneOneBarOn (N := N)
      (sourceNonKahlerLocus (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))ᶜ
      (fun x => (sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x).toReal) := by
  obtain ⟨hreal, -, hC⟩ := envelopeReal_isCOneOneBarOn_of_kahlerClass
    (atlasClosedFormToNative θ) hρ hK hf
  rw [sourceObstacleEnvelope_eq_native]
  exact ⟨fun x => by rw [hreal x, EReal.toReal_coe], hC⟩

/-- **Source `thm:DNT23_C11bar`, "in particular", Kähler class, with the source
`V_θ = sourceMinimalEnvelope θ = sup{φ ∈ PSH(X,θ) : φ ≤ 0}`**: if `θ + ddᶜρ` is a Kähler form for a
chart-smooth `ρ`, then `V_θ` is real-valued and its real version is `C^{1,1̄}` on `X \ nK({θ})`
(indeed on `X`). -/
theorem sourceMinimalEnvelope_isCOneOneBarOn_of_kahlerClass (w : KahlerBackground N Y)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel N Y)) {ρ : Y → ℝ} (hρ : ChartSmooth (n := N) ρ)
    (hK : (atlasClosedFormToNative θ + ddcClosedForm ρ hρ).val.IsKahler) :
    (∀ x, sourceMinimalEnvelope θ x = (((sourceMinimalEnvelope θ x).toReal : ℝ) : EReal)) ∧
    IsCOneOneBarOn (N := N)
      (sourceNonKahlerLocus (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))ᶜ
      (fun x => (sourceMinimalEnvelope θ x).toReal) := by
  set θn := atlasClosedFormToNative θ with hθn
  obtain ⟨hreal, -, hC⟩ := minimalEnvelope_isCOneOneBarOn_of_kahlerClass θn hρ hK
  -- `ρ` is `θ`-psh, so `PSH(X,θ) ≠ ∅`
  have hρpsh : IsThetaPshPotential θn.val (fun y => (ρ y : EReal)) := by
    have h := thetaPshPotential_sub_smooth (θ := (θn + ddcClosedForm ρ hρ).val) (η := θn.val)
      (f := fun y => -ρ y) (fun e => (hρ e).neg) (fun e z hz => ?_)
      (u := fun _ => (0 : EReal)) ?_
    · have hfun : (fun y => (0 : EReal) - ((-ρ y : ℝ) : EReal)) =
          fun y => (ρ y : EReal) := by
        funext y
        rw [← EReal.coe_zero, ← EReal.coe_sub, zero_sub, neg_neg]
      rw [hfun] at h
      exact h
    · rw [ClosedRealOneOneForm.coeff_add, ddcClosedForm_coeff,
        smoothDDC_neg (h := fun y => ρ (e.val.symm y)) e.val.open_target (hρ e) hz,
        add_neg_cancel_right]
    · exact (LocalPotentials.isThetaPshPotential_zero_iff _).mpr
        (KahlerBackground.isSemipositive ⟨θn + ddcClosedForm ρ hρ, hK⟩)
  have hV : sourceMinimalEnvelope θ = rooftopEnvelope θn.val (fun _ => ((0 : ℝ) : EReal)) := by
    rw [sourceMinimalEnvelope_eq_native]
    exact thetaPshSupremum_eq_rooftopEnvelope_zero w θn hρpsh
  rw [hV]
  have heq : (fun x => (rooftopEnvelope θn.val (fun _ => ((0 : ℝ) : EReal)) x).toReal) =
      envelopeReal θn (fun _ => 0) := rfl
  rw [heq]
  exact ⟨fun x => by rw [hreal x, EReal.toReal_coe], hC⟩

omit [MeasurableSpace Y] [BorelSpace Y] in
/-- **Source `prop:DR16_C11bar`, smooth obstacles, with the source envelope
`P_ω(min{f₁, f₂}) = sourceRelativeEnvelope ω ⊤ min{f₁, f₂}`** (`def:Pthetaf`): for a Kähler form
`ω` and chart-smooth `f₁, f₂`, the envelope is real-valued and its real version is `C^{1,1̄}(X)`. -/
theorem sourceObstacleEnvelope_min_isCOneOneBar
    (w : AtlasClosedRealOneOneForm (ofFixedModel N Y))
    (hK : (atlasClosedFormToNative w).val.IsKahler) {f₁ f₂ : Y → ℝ}
    (h₁ : ChartSmooth (n := N) f₁) (h₂ : ChartSmooth (n := N) f₂) :
    (∀ x, sourceRelativeEnvelope w (fun _ => ⊤) (fun y => ((min (f₁ y) (f₂ y) : ℝ) : EReal)) x =
      (((sourceRelativeEnvelope w (fun _ => ⊤)
        (fun y => ((min (f₁ y) (f₂ y) : ℝ) : EReal)) x).toReal : ℝ) : EReal)) ∧
    IsCOneOneBar (N := N) (fun x => (sourceRelativeEnvelope w (fun _ => ⊤)
      (fun y => ((min (f₁ y) (f₂ y) : ℝ) : EReal)) x).toReal) := by
  obtain ⟨hreal, hC⟩ := isCOneOneBar_envelopeReal_min ⟨atlasClosedFormToNative w, hK⟩ h₁ h₂
  rw [sourceObstacleEnvelope_eq_native]
  exact ⟨fun x => by rw [hreal x, EReal.toReal_coe], hC⟩

end Source

end SGPT.Envelopes.DNTReg
