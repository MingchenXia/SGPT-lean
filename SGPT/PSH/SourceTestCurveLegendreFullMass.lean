import SGPT.PSH.SourceTestCurveLegendrePSH
import SGPT.PSH.SourceTestCurveBasedness
import SGPT.Envelopes.SourceRelativeEnergyClosure

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The same original raw transform lies below its actual limit plus the
finite cutoff constant, including all poles of the original limit. -/
theorem SourceTestCurvePredata.rawLegendre_le_limit_add
    (Γ : SourceTestCurvePredata θ) {t : ℝ} (ht : 0 ≤ t) :
    sourceTestCurveRawLegendre Γ t ≤
      fun x ↦ sourceTestCurveLimit Γ x + ((t * Γ.max : ℝ) : EReal) := by
  intro x
  rw [Γ.rawLegendre_eq_iSup_open t x]
  apply iSup_le
  intro τ
  rw [add_comm ((t * τ.1 : ℝ) : EReal)]
  have hlim : Γ.potential τ x ≤ sourceTestCurveLimit Γ x := by
    simpa only [sourceTestCurveAt_of_lt Γ (show τ.1 < Γ.max from τ.2)] using
      Γ.at_le_limit τ.1 x
  exact add_le_add hlim
    (EReal.coe_le_coe (mul_le_mul_of_nonneg_left τ.2.le ht))

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- The actual ordinary envelope of the literal raw slice is exactly the
original source limit, manufactured from the original test curve alone. -/
theorem SourceTestCurve.rawLegendre_envelope_eq_limit
    (omega : KahlerBackground n M) (Γ : SourceTestCurve θ) {t : ℝ} (ht : 0 < t) :
    sourceSingularityEnvelope θ (sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t) =
      sourceTestCurveLimit Γ.toSourceTestCurvePredata := by
  have hF := Γ.toSourceTestCurvePredata.rawLegendre_thetaPSH omega ht
  have hP := sourceOrdinaryEnvelope_genuine hF
  apply le_antisymm
  · have hmore : SGPT.PSH.SingularityLE
        (sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t)
        (sourceTestCurveLimit Γ.toSourceTestCurvePredata) :=
      ⟨t * Γ.max, fun x _ ↦ Γ.toSourceTestCurvePredata.rawLegendre_le_limit_add ht.le x⟩
    exact (sourceOrdinaryEnvelope_mono hmore).trans_eq (Γ.limit_model omega).choose_spec.1.symm
  · change uscRegularization (fun x ↦ ⨆ τ, Γ.potential τ x) ≤ _
    apply uscRegularization_le
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp hP).1.quasiPlurisubharmonic.upperSemicontinuous
    intro x
    apply iSup_le
    intro τ
    have hmore : SGPT.PSH.SingularityLE (Γ.potential τ)
        (sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t) := by
      refine ⟨-(t * τ.1), fun y _ ↦ ?_⟩
      have hy : Γ.potential τ y + ((t * τ.1 : ℝ) : EReal) ≤
          sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t y := by
        rw [Γ.toSourceTestCurvePredata.rawLegendre_eq_iSup_open t y, add_comm]
        exact le_iSup (fun σ : Iio Γ.max ↦ ((t * σ.1 : ℝ) : EReal) + Γ.potential σ y) τ
      simpa only [sub_eq_add_neg, EReal.coe_neg] using
        (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _))
          (Or.inl (EReal.coe_ne_top _))).mpr hy
    exact (Γ.fixedPoint τ ▸ sourceOrdinaryEnvelope_mono (θ := θ) hmore) x

/-- ENTIRE original cor:GammastarP in its original additive-constant full-mass
class, with SAME actual PSH functions, model and non-pluripolar masses. -/
theorem source_test_curve_legendre_fullMass_whole
    (omega : KahlerBackground n M) (Γ : SourceTestCurve θ)
    {φ : M → EReal} {hφ : SourceModelPotential θ φ}
    (hbased : Γ ∈ SourceTestCurvesBased θ φ hφ) :
    ∀ t : ℝ, 0 < t → SourceRelativeFullMass θ φ
      (sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t) hφ := by
  intro t ht
  apply (sourceRelativeFullMass_iff_envelope_eq omega
    (Γ.toSourceTestCurvePredata.rawLegendre_thetaPSH omega ht)).mpr
  exact (Γ.rawLegendre_envelope_eq_limit omega ht).trans hbased

end SGPT.PSH.VariableComplexAtlas
