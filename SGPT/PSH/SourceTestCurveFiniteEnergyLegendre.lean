import SGPT.PSH.SourceTestCurveRegularizationLegendreLimit
import SGPT.PSH.SourceTestCurveLegendreGeodesic
import Mathlib.Topology.Instances.EReal.Lemmas

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

/-- Genuine decreasing extended-energy continuity at the ACTUAL raw transform.
No finite-energy membership of the original limit is assumed. -/
theorem SourceTestCurve.regularization_rawEnergy_tendsto (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hmax : Γ.max = 0) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun k => sourceRelativeEnergy θ φ
      (sourceTestCurveRawLegendre
        (sourceTestCurveRegularizationSequence omega Γ hΓ hmax k).toSourceTestCurvePredata t) hφ)
      atTop (𝓝 (sourceRelativeEnergy θ φ
        (sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t) hφ)) := by
  let G := sourceTestCurveRegularizationSequence omega Γ hΓ hmax
  let u := fun k => sourceTestCurveRawLegendre (G k).toSourceTestCurvePredata t
  have hui (k : ℕ) : SourceRelativePSH θ φ (u k) := by
    obtain ⟨hu, horder, _⟩ := source_test_curve_legendre_fullMass_whole omega (G k)
      (sourceTestCurveRegularizationSequence_bounded omega Γ hΓ hmax k).1 t ht
    exact ⟨hu, horder⟩
  have hanti (x : M) : Antitone (fun k => u k x) := fun i j hij =>
    sourceTestCurveRegularizationSequence_rawLegendre_antitone omega Γ hΓ hmax t hij x
  have heq : (fun x => ⨅ k, u k x) = sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t := by
    funext x
    exact sourceTestCurveRegularizationSequence_rawLegendre_iInf omega Γ hΓ hmax ht x
  have hne := sourceThetaPSH_ne_bot (Γ.toSourceTestCurvePredata.rawLegendre_thetaPSH omega ht)
  have hx : ∃ x, (⨅ k, u k x) ≠ ⊥ := by
    by_contra h
    apply hne
    rw [← heq]
    funext x
    exact not_ne_iff.mp (not_exists.mp h x)
  have hh := (sourceRelativeEnergy_directed_decreasing_net (hφ := hφ) omega hui hanti hx).2.2
  simpa only [heq] using hh

/-- The normalized actual energy identity for EVERY original based test curve,
including the genuine negative-infinite energy branch. -/
theorem SourceTestCurve.legendre_energy_identity_normalized (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hmax : Γ.max = 0) {t : ℝ} (ht : 0 < t) :
    sourceRelativeEnergy θ φ (sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t) hφ =
      (t : EReal) * sourceTestCurveEnergy omega hφ Γ hΓ := by
  let G := sourceTestCurveRegularizationSequence omega Γ hΓ hmax
  have hscaled := EReal.Tendsto.const_mul (a := (t : EReal))
    (sourceTestCurveRegularizationSequence_energy_tendsto omega Γ hΓ hmax)
    (Or.inl (EReal.coe_ne_bot t)) (Or.inl (EReal.coe_ne_top t))
  have heq (k : ℕ) : sourceRelativeEnergy θ φ
      (sourceTestCurveRawLegendre (G k).toSourceTestCurvePredata t) hφ =
      (t : EReal) * sourceTestCurveEnergy omega hφ (G k)
        (sourceTestCurveRegularizationSequence_bounded omega Γ hΓ hmax k).1 :=
    ((G k).boundedLegendre_energy_identity omega
      (sourceTestCurveRegularizationSequence_bounded omega Γ hΓ hmax k)
      (show (G k).max = 0 from rfl) ht).1
  have hs : Tendsto (fun k => sourceRelativeEnergy θ φ
      (sourceTestCurveRawLegendre (G k).toSourceTestCurvePredata t) hφ) atTop
      (𝓝 ((t : EReal) * sourceTestCurveEnergy omega hφ Γ hΓ)) := by
    simpa only [heq] using hscaled
  exact tendsto_nhds_unique (Γ.regularization_rawEnergy_tendsto omega hΓ hmax ht) hs

omit [ConnectedSpace M] in
private theorem actual_model_energy_zero (omega : KahlerBackground n M) :
    sourceRelativeEnergy θ φ φ hφ = 0 := by
  rw [sourceRelativeEnergy_eq_native,
    SingularModelEnergyCocycle.energy_eq_of_relativeEInfinity omega _ hφ.toNative
      ⟨hφ.toNative.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩,
    RelativeEnergy.relativeEnergyOfMinimalType_self, EReal.coe_zero]

/-- EVERY original nonnegative assigned time, including the actual model at zero. -/
theorem SourceTestCurve.legendre_assigned_energy_identity_normalized (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hmax : Γ.max = 0) (t : Ici (0 : ℝ)) :
    sourceRelativeEnergy θ φ (sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata t) hφ =
      (t.1 : EReal) * sourceTestCurveEnergy omega hφ Γ hΓ := by
  by_cases hz : t.1 = 0
  · have hbase : sourceTestCurveLimit Γ.toSourceTestCurvePredata = φ := hΓ
    have hzero : sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata t = φ := by
      simp only [sourceTestCurveLegendreRay, sourceTestCurveLegendreWithInitial, if_pos hz, hbase]
    rw [hzero, actual_model_energy_zero omega, hz, EReal.coe_zero, zero_mul]
  · simpa only [sourceTestCurveLegendreRay, sourceTestCurveLegendreWithInitial, if_neg hz] using
      Γ.legendre_energy_identity_normalized omega hΓ hmax (lt_of_le_of_ne t.2 (Ne.symm hz))

/-- Original finite test-curve energy PRODUCES the genuine own-measure E1 class
of EVERY actual positive raw slice, using its independently proved full mass. -/
theorem SourceTestCurve.legendre_finiteEnergy_normalized (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hmax : Γ.max = 0) (hE : Γ ∈ SourceFiniteEnergyTestCurves omega θ φ hφ)
    {t : ℝ} (ht : 0 < t) :
    SourceRelativeFiniteEnergy θ φ (sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t) hφ := by
  apply (sourceRelativeFiniteEnergy_iff_bot_lt_energy omega
    (source_test_curve_legendre_fullMass_whole omega Γ hΓ t ht)).mpr
  obtain ⟨hb, hbot, htop⟩ := sourceTestCurveEnergy_finite_of_mem omega hφ Γ hE
  have hco : ((sourceTestCurveEnergy omega hφ Γ hΓ).toReal : EReal) =
      sourceTestCurveEnergy omega hφ Γ hΓ := EReal.coe_toReal htop hbot
  rw [Γ.legendre_energy_identity_normalized omega hΓ hmax ht, ← hco, ← EReal.coe_mul]
  exact EReal.bot_lt_coe _

/-- Actual finite energy is read back ONLY after original class membership
has excluded BOTH infinite endpoints of the defining test-curve energy. -/
theorem SourceTestCurve.legendre_realEnergy_identity_normalized (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hmax : Γ.max = 0) (hE : Γ ∈ SourceFiniteEnergyTestCurves omega θ φ hφ)
    {t : ℝ} (ht : 0 < t) :
    sourceRelativeEnergy θ φ (sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t) hφ =
      ((t * (sourceTestCurveEnergy omega hφ Γ hΓ).toReal : ℝ) : EReal) := by
  obtain ⟨hb, hbot, htop⟩ := sourceTestCurveEnergy_finite_of_mem omega hφ Γ hE
  have hco : ((sourceTestCurveEnergy omega hφ Γ hΓ).toReal : EReal) =
      sourceTestCurveEnergy omega hφ Γ hΓ := EReal.coe_toReal htop hbot
  rw [Γ.legendre_energy_identity_normalized omega hΓ hmax ht]
  conv_lhs => rw [← hco]
  rw [← EReal.coe_mul]

/-- True E1 of the ACTUAL time-one raw transform forces original finite
TC energy by pointwise order, defining-energy order and the actual MCT limit. -/
theorem SourceTestCurve.legendre_timeOne_finiteEnergy_iff_normalized (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hmax : Γ.max = 0) :
    SourceRelativeFiniteEnergy θ φ (sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata 1) hφ ↔
      Γ ∈ SourceFiniteEnergyTestCurves omega θ φ hφ := by
  constructor
  · intro hf
    have hbot := (sourceRelativeFiniteEnergy_iff_bot_lt_energy omega hf.1).mp hf
    have hlim := (sourceTestCurveRegularizationSequence_legendreOne_energy_tendsto omega Γ hΓ hmax).1
    have hlo (k : ℕ) : sourceRelativeEnergy θ φ
        (sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata 1) hφ ≤
        sourceRelativeEnergy θ φ (sourceTestCurveRawLegendre
          (sourceTestCurveRegularizationSequence omega Γ hΓ hmax k).toSourceTestCurvePredata 1) hφ := by
      apply sourceRelativeEnergy_mono
      intro x
      rw [← sourceTestCurveRegularizationSequence_rawLegendre_iInf omega Γ hΓ hmax
        (by norm_num : (0 : ℝ) < 1) x]
      exact iInf_le _ k
    exact ⟨hΓ, hbot.trans_le (ge_of_tendsto' hlim hlo)⟩
  · intro hE
    exact Γ.legendre_finiteEnergy_normalized omega hΓ hmax hE (by norm_num)

/-- The original finite-energy ray collection is equivalent to original
finite TC energy, with ALL positive slices and the actual initial model. -/
theorem SourceTestCurve.legendre_finiteEnergy_ray_iff_normalized (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hmax : Γ.max = 0) :
    sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata ∈ sourceFiniteEnergyRays omega θ φ hφ ↔
      Γ ∈ SourceFiniteEnergyTestCurves omega θ φ hφ := by
  constructor
  · intro hRay
    apply (Γ.legendre_timeOne_finiteEnergy_iff_normalized omega hΓ hmax).mp
    have hf := hRay.1.2 ⟨1, by norm_num⟩ (by norm_num)
    simpa only [sourceTestCurveLegendreRay, sourceTestCurveLegendreWithInitial,
      if_neg (by norm_num : (1 : ℝ) ≠ 0)] using hf
  · intro hE
    have hg := (source_test_curve_legendre_geodesic_whole omega Γ hΓ).1
    refine ⟨⟨hg.1, ?_⟩, hg.2⟩
    intro t ht
    simpa only [sourceTestCurveLegendreRay, sourceTestCurveLegendreWithInitial,
      if_neg (ne_of_gt ht)] using Γ.legendre_finiteEnergy_normalized omega hΓ hmax hE ht

end SGPT.PSH.VariableComplexAtlas
