import SGPT.PSH.SourceTestCurveFiniteEnergyLegendre
import SGPT.PSH.SourceTestCurveShift
import SGPT.PSH.SourceTestCurveLegendreBounded
import SGPT.PSH.SourceRadialEnergy

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter Topology MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
  {φ : M → EReal} {hφ : SourceModelPotential θ φ}

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem sub_finite_cancel {a b : EReal} {c : ℝ}
    (h : a - (c : EReal) = b - (c : EReal)) : a = b := by
  apply le_antisymm
  · apply (EReal.addLECancellable_coe (-c)).add_le_add_iff_right.mp
    simpa only [sub_eq_add_neg, ← EReal.coe_neg] using h.le
  · apply (EReal.addLECancellable_coe (-c)).add_le_add_iff_right.mp
    simpa only [sub_eq_add_neg, ← EReal.coe_neg] using h.ge

omit [ConnectedSpace M] in
private theorem actual_energy_add_const (omega : KahlerBackground n M)
    (u : M → EReal) (c : ℝ) :
    sourceRelativeEnergy θ φ (fun x => u x + (c : EReal)) hφ =
      sourceRelativeEnergy θ φ u hφ +
        ((c * (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal : ℝ) : EReal) := by
  rw [sourceRelativeEnergy_eq_native,
    SingularModelEnergyExtendedTranslation.energy_add_const omega u c,
    sourceRelativeEnergy_eq_native]
  rfl

/-- Actual defining energy identity at EVERY cutoff and original assigned time,
including zero and negative-infinite test-curve energies. -/
theorem SourceTestCurve.legendre_assigned_energy_identity (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (t : Ici (0 : ℝ)) :
    sourceRelativeEnergy θ φ (sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata t) hφ =
      (t.1 : EReal) * sourceTestCurveEnergy omega hφ Γ hΓ := by
  let V := (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal
  have hb := (Γ.shift_based_iff hφ Γ.max).mpr hΓ
  have hz := (source_test_curve_zero_cutoff_normalization omega hφ Γ hΓ).1
  have hnorm := (Γ.shift Γ.max).legendre_assigned_energy_identity_normalized omega hb hz t
  have htranslate : sourceRelativeEnergy θ φ
      (sourceTestCurveLegendreRay (Γ.shift Γ.max).toSourceTestCurvePredata t) hφ =
      sourceRelativeEnergy θ φ (sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata t) hφ -
        ((t.1 * Γ.max * V : ℝ) : EReal) := by
    have hfun : sourceTestCurveLegendreRay (Γ.shift Γ.max).toSourceTestCurvePredata t =
        fun x => sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata t x -
          ((t.1 * Γ.max : ℝ) : EReal) := Γ.toSourceTestCurvePredata.shift_legendreRay Γ.max t
    rw [hfun]
    have hfn : (fun x => sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata t x -
        ((t.1 * Γ.max : ℝ) : EReal)) =
        (fun x => sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata t x +
          ((-(t.1 * Γ.max) : ℝ) : EReal)) := by
      funext x
      simp only [sub_eq_add_neg, EReal.coe_neg]
    rw [hfn, actual_energy_add_const omega]
    simp only [neg_mul, EReal.coe_neg, sub_eq_add_neg, V]
  rw [Γ.shift_energy omega hφ hΓ Γ.max,
    EReal.mul_sub_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr t.2) (EReal.coe_ne_top _),
    ← EReal.coe_mul] at hnorm
  have hh : sourceRelativeEnergy θ φ (sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata t) hφ -
        ((t.1 * Γ.max * V : ℝ) : EReal) =
      (t.1 : EReal) * sourceTestCurveEnergy omega hφ Γ hΓ -
        ((t.1 * Γ.max * V : ℝ) : EReal) := by
    simpa only [mul_assoc, V] using htranslate.symm.trans hnorm
  exact sub_finite_cancel hh

/-- Every positive original RAW transform has the same defining identity. -/
theorem SourceTestCurve.legendre_energy_identity (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    {t : ℝ} (ht : 0 < t) :
    sourceRelativeEnergy θ φ (sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t) hφ =
      (t : EReal) * sourceTestCurveEnergy omega hφ Γ hΓ := by
  simpa only [sourceTestCurveLegendreRay, sourceTestCurveLegendreWithInitial, if_neg ht.ne'] using
    Γ.legendre_assigned_energy_identity omega hΓ ⟨t, ht.le⟩

/-- Genuine original finite TC energy produces actual E1 at EVERY positive time. -/
theorem SourceTestCurve.legendre_finiteEnergy (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hE : Γ ∈ SourceFiniteEnergyTestCurves omega θ φ hφ) {t : ℝ} (ht : 0 < t) :
    SourceRelativeFiniteEnergy θ φ (sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t) hφ := by
  apply (sourceRelativeFiniteEnergy_iff_bot_lt_energy omega
    (source_test_curve_legendre_fullMass_whole omega Γ hΓ t ht)).mpr
  obtain ⟨hb, hbot, htop⟩ := sourceTestCurveEnergy_finite_of_mem omega hφ Γ hE
  have hco : ((sourceTestCurveEnergy omega hφ Γ hΓ).toReal : EReal) =
      sourceTestCurveEnergy omega hφ Γ hΓ := EReal.coe_toReal htop hbot
  rw [Γ.legendre_energy_identity omega hΓ ht, ← hco, ← EReal.coe_mul]
  exact EReal.bot_lt_coe _

/-- Finite readback formula on ALL original assigned times and cutoffs. -/
theorem SourceTestCurve.legendre_realEnergy_identity (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hE : Γ ∈ SourceFiniteEnergyTestCurves omega θ φ hφ) (t : Ici (0 : ℝ)) :
    sourceRelativeEnergy θ φ (sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata t) hφ =
      ((t.1 * (sourceTestCurveEnergy omega hφ Γ hΓ).toReal : ℝ) : EReal) := by
  obtain ⟨hb, hbot, htop⟩ := sourceTestCurveEnergy_finite_of_mem omega hφ Γ hE
  have hco : ((sourceTestCurveEnergy omega hφ Γ hΓ).toReal : EReal) =
      sourceTestCurveEnergy omega hφ Γ hΓ := EReal.coe_toReal htop hbot
  rw [Γ.legendre_assigned_energy_identity omega hΓ t]
  conv_lhs => rw [← hco]
  rw [← EReal.coe_mul]

/-- Exact original finite-energy ray restriction at EVERY original cutoff. -/
theorem SourceTestCurve.legendre_finiteEnergy_ray_iff (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ) :
    sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata ∈ sourceFiniteEnergyRays omega θ φ hφ ↔
      Γ ∈ SourceFiniteEnergyTestCurves omega θ φ hφ := by
  constructor
  · intro hRay
    have hf := hRay.1.2 ⟨1, by norm_num⟩ (by norm_num)
    have hbot := (sourceRelativeFiniteEnergy_iff_bot_lt_energy omega hf.1).mp hf
    rw [Γ.legendre_assigned_energy_identity omega hΓ ⟨1, by norm_num⟩,
      EReal.coe_one, one_mul] at hbot
    exact ⟨hΓ, hbot⟩
  · intro hE
    have hg := (source_test_curve_legendre_geodesic_whole omega Γ hΓ).1
    refine ⟨⟨hg.1, ?_⟩, hg.2⟩
    intro t ht
    simpa only [sourceTestCurveLegendreRay, sourceTestCurveLegendreWithInitial,
      if_neg (ne_of_gt ht)] using Γ.legendre_finiteEnergy omega hΓ hE ht

private theorem finiteEnergy_inverse_mem (omega : KahlerBackground n M)
    {ℓ : SourceRayFamily M} (h : ℓ ∈ sourceFiniteEnergyRays omega θ φ hφ) :
    sourceRayLegendreTestCurve omega ⟨h.1.1, h.2⟩ ∈ SourceFiniteEnergyTestCurves omega θ φ hφ := by
  let hR : ℓ ∈ sourceGeodesicRays omega θ φ hφ := ⟨h.1.1, h.2⟩
  let Γ := sourceRayLegendreTestCurve omega hR
  have hb : Γ ∈ SourceTestCurvesBased θ φ hφ := (source_ray_legendre_test_curve_whole omega hR).1
  apply (Γ.legendre_finiteEnergy_ray_iff omega hb).mp
  change sourceTestCurveLegendreRay (sourceRayLegendreTestCurve omega hR).toSourceTestCurvePredata ∈ _
  rw [sourceRayLegendre_right_inverse omega hR]
  exact h

/-- The ACTUAL original finite-energy subtypes and SAME original inverse maps. -/
def sourceTestCurveFiniteEnergyLegendreEquiv (omega : KahlerBackground n M)
    (φ : M → EReal) (hφ : SourceModelPotential θ φ) :
    {Γ : SourceTestCurve θ // Γ ∈ SourceFiniteEnergyTestCurves omega θ φ hφ} ≃
      {ℓ : SourceRayFamily M // ℓ ∈ sourceFiniteEnergyRays omega θ φ hφ} where
  toFun Γ := ⟨sourceTestCurveLegendreRay Γ.1.toSourceTestCurvePredata,
    (Γ.1.legendre_finiteEnergy_ray_iff omega Γ.2.1).mpr Γ.2⟩
  invFun ℓ := ⟨sourceRayLegendreTestCurve omega ⟨ℓ.2.1.1, ℓ.2.2⟩,
    finiteEnergy_inverse_mem omega ℓ.2⟩
  left_inv Γ := Subtype.ext (sourceTestCurveLegendre_left_inverse omega Γ.1 Γ.2.1)
  right_inv ℓ := Subtype.ext (sourceRayLegendre_right_inverse omega ⟨ℓ.2.1.1, ℓ.2.2⟩)

omit [ConnectedSpace M] in
private theorem actual_model_energy_zero (omega : KahlerBackground n M) :
    sourceRelativeEnergy θ φ φ hφ = 0 := by
  rw [sourceRelativeEnergy_eq_native,
    SingularModelEnergyCocycle.energy_eq_of_relativeEInfinity omega _ hφ.toNative
      ⟨hφ.toNative.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩,
    RelativeEnergy.relativeEnergyOfMinimalType_self, EReal.coe_zero]

/-- The ORIGINAL defining radial limsup equals the SAME test-curve energy. -/
theorem source_test_curve_legendre_radial_energy_identity (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hE : Γ ∈ SourceFiniteEnergyTestCurves omega θ φ hφ) :
    sourceTestCurveEnergy omega hφ Γ hΓ = sourceRadialEnergy omega
      ⟨sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata,
        (source_test_curve_legendre_geodesic_whole omega Γ hΓ).1⟩ := by
  have hone : sourceRelativeEnergy θ φ
      (sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata ⟨1, by norm_num⟩) hφ =
      sourceTestCurveEnergy omega hφ Γ hΓ := by
    simpa only [EReal.coe_one, one_mul] using
      Γ.legendre_assigned_energy_identity omega hΓ ⟨1, by norm_num⟩
  have hbase : sourceTestCurveLimit Γ.toSourceTestCurvePredata = φ := hΓ
  have hzero : sourceRelativeEnergy θ φ
      (sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata ⟨0, by norm_num⟩) hφ = 0 := by
    have hf : sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata ⟨0, by norm_num⟩ = φ := by
      simp [sourceTestCurveLegendreRay, sourceTestCurveLegendreWithInitial, hbase]
    rw [hf]
    exact actual_model_energy_zero omega
  obtain ⟨hb, hbot, htop⟩ := sourceTestCurveEnergy_finite_of_mem omega hφ Γ hE
  rw [sourceRadialEnergy_eq omega]
  change sourceTestCurveEnergy omega hφ Γ hΓ =
    if sourceRelativeEnergy θ φ (sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata ⟨1, by norm_num⟩) hφ = ⊥
    then ⊥ else (((sourceRelativeEnergy θ φ
      (sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata ⟨1, by norm_num⟩) hφ).toReal -
      (sourceRelativeEnergy θ φ
        (sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata ⟨0, by norm_num⟩) hφ).toReal : ℝ) : EReal)
  rw [hone, if_neg hbot, hzero, EReal.toReal_zero, sub_zero]
  exact (EReal.coe_toReal htop hbot).symm

end SGPT.PSH.VariableComplexAtlas
