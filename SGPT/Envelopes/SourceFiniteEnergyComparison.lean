import SGPT.Envelopes.SourceMixedEnergyIntegrability

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending DiagonalMass GlobalNonPluripolar GlobalDiagonalScaling
open RelativeEnergy RelativeDarvasDistance RelativePreceqClasses MongeAmpereEnergyDecreasing
open SingularModelEnergyTruncation SingularModelFiniteEnergyMixedGap

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Common finite translation leaves the actual canonical signed difference unchanged. -/
theorem sourceCanonicalDifference_common_translation (a b : EReal) (c : ℝ) :
    canonicalERealDiffToReal (a + (c : EReal)) (b + (c : EReal)) =
      canonicalERealDiffToReal a b := by
  cases a <;> cases b <;>
    simp [canonicalERealDiffToReal, poleModifiedERealDiffToReal,
      ← EReal.coe_add, ← EReal.coe_sub]

section NativeNormalized

variable {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal} {hφ : IsModelPotential θ φ}

/-- The two actual moving diagonal integrals converge for unordered normalized E1 endpoints.
The normalization is only used at this intermediate truncation step. -/
theorem sourceNormalizedFiniteEnergy_moving_endpoint_limits
    (ω : KahlerBackground n M) (hu : RelativeFiniteEnergy θ φ u hφ)
    (hv : RelativeFiniteEnergy θ φ v hφ) :
    (Tendsto (fun j => ∫ x, canonicalERealDiffToReal (truncation φ u j x) (truncation φ v j x)
        ∂diagonalPotentialMeasure θ (truncation φ u j)
          (relativeEInfinity_truncation hφ.plurisubharmonic hu.1.plurisubharmonic
            (preceq_of_relativePSH hu.1.relativePSH).2 j).1)
      atTop (𝓝 (∫ x, canonicalERealDiffToReal (u x) (v x)
        ∂diagonalPotentialMeasure θ u hu.1.plurisubharmonic))) ∧
    (Tendsto (fun j => ∫ x, canonicalERealDiffToReal (truncation φ u j x) (truncation φ v j x)
        ∂diagonalPotentialMeasure θ (truncation φ v j)
          (relativeEInfinity_truncation hφ.plurisubharmonic hv.1.plurisubharmonic
            (preceq_of_relativePSH hv.1.relativePSH).2 j).1)
      atTop (𝓝 (∫ x, canonicalERealDiffToReal (u x) (v x)
        ∂diagonalPotentialMeasure θ v hv.1.plurisubharmonic))) := by
  have htrue := SingularModelFiniteEnergyMixedTruncation.tendsto_integral_canonicalDiff_truncations
    ω hu hv (fun _ => true)
  have hfalse := SingularModelFiniteEnergyMixedTruncation.tendsto_integral_canonicalDiff_truncations
    ω hu hv (fun _ => false)
  simpa only [binaryMixedMeasure, Bool.true_eq, Bool.false_eq_true, ↓reduceIte,
    diagonalPotentialMeasure] using
    And.intro htrue hfalse

/-- Actual finite-formula endpoint bounds pass through the produced unordered moving limits. -/
theorem sourceNormalizedFiniteEnergy_endpoint_bounds
    (ω : KahlerBackground n M) (hu : RelativeFiniteEnergy θ φ u hφ)
    (hv : RelativeFiniteEnergy θ φ v hφ) :
    (∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂diagonalPotentialMeasure θ u hu.1.plurisubharmonic) ≤
        (energy θ φ hφ u).toReal - (energy θ φ hφ v).toReal ∧
    (energy θ φ hφ u).toReal - (energy θ φ hφ v).toReal ≤
      ∫ x, canonicalERealDiffToReal (u x) (v x)
        ∂diagonalPotentialMeasure θ v hv.1.plurisubharmonic := by
  let hp := hφ.plurisubharmonic
  let htu := fun j => relativeEInfinity_truncation hp hu.1.plurisubharmonic
    (preceq_of_relativePSH hu.1.relativePSH).2 j
  let htv := fun j => relativeEInfinity_truncation hp hv.1.plurisubharmonic
    (preceq_of_relativePSH hv.1.relativePSH).2 j
  have hTu := energy_tendsto_truncation ω θ hφ hu.1.plurisubharmonic
    (preceq_of_relativePSH hu.1.relativePSH).2
  have hTv := energy_tendsto_truncation ω θ hφ hv.1.plurisubharmonic
    (preceq_of_relativePSH hv.1.relativePSH).2
  rw [← SingularModelFiniteEnergyPreceq.coe_toReal_energy ω (preceq_of_relativeFiniteEnergy hu)] at hTu
  rw [← SingularModelFiniteEnergyPreceq.coe_toReal_energy ω (preceq_of_relativeFiniteEnergy hv)] at hTv
  have hE := (EReal.tendsto_coe.mp hTu).sub (EReal.tendsto_coe.mp hTv)
  have hi := sourceNormalizedFiniteEnergy_moving_endpoint_limits ω hu hv
  have hb (j : ℕ) := SingularModelEnergyCocycle.integral_le_relativeEnergyOfMinimalType_sub_le
    ω θ hp (htu j).1 (htv j).1 (htu j).2 (htv j).2
  exact ⟨le_of_tendsto_of_tendsto' hi.1 hE (fun j => (hb j).1),
    le_of_tendsto_of_tendsto' hE hi.2 (fun j => (hb j).2)⟩

end NativeNormalized

variable {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ u v : M → EReal}
  {hφ : SourceModelPotential θ φ}

/-- Both original E1 endpoint inequalities hold for the entire singularity-order source class.
No ordering, bounded model, normalized representative or integrability certificate is an input. -/
theorem sourceRelativeFiniteEnergy_endpoint_bounds
    (ω : KahlerBackground n M) (hu : SourceRelativeFiniteEnergy θ φ u hφ)
    (hv : SourceRelativeFiniteEnergy θ φ v hφ) :
    (∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂sourcePotentialNonPluripolarMeasure θ u hu.1.choose) ≤
        (sourceRelativeEnergy θ φ u hφ).toReal - (sourceRelativeEnergy θ φ v hφ).toReal ∧
    (sourceRelativeEnergy θ φ u hφ).toReal - (sourceRelativeEnergy θ φ v hφ).toReal ≤
      ∫ x, canonicalERealDiffToReal (u x) (v x)
        ∂sourcePotentialNonPluripolarMeasure θ v hv.1.choose := by
  have hnu := (sourceRelativeFiniteEnergy_iff_native θ φ u hφ).mp hu
  have hnv := (sourceRelativeFiniteEnergy_iff_native θ φ v hφ).mp hv
  obtain ⟨c, hcu, hcv⟩ := exists_common_add_le hnu.1.relativePSHPreceq hnv.1.relativePSHPreceq
  have hb := sourceNormalizedFiniteEnergy_endpoint_bounds ω
    (hnu.relativeFiniteEnergy_add ω hcu) (hnv.relativeFiniteEnergy_add ω hcv)
  rw [SingularModelFiniteRealEnergy.toReal_energy_add_const ω hnu c,
    SingularModelFiniteRealEnergy.toReal_energy_add_const ω hnv c,
    DiagonalMeasureRegularity.diagonalPotentialMeasure_add_const _ hnu.1.plurisubharmonic c,
    DiagonalMeasureRegularity.diagonalPotentialMeasure_add_const _ hnv.1.plurisubharmonic c] at hb
  simp only [sourceCanonicalDifference_common_translation, add_sub_add_right_eq_sub] at hb
  simpa only [sourceRelativeEnergy_eq_native, sourcePotentialNonPluripolarMeasure] using hb

omit [ConnectedSpace M] in
/-- Canonical and ordinary signed differences agree on every independent actual E1 diagonal. -/
theorem sourceRelativeFiniteEnergy_diagonal_difference_ae {w : M → EReal}
    (hu : SourceRelativeFiniteEnergy θ φ u hφ) (hv : SourceRelativeFiniteEnergy θ φ v hφ)
    (hw : SourceRelativeFiniteEnergy θ φ w hφ) :
    (fun x => canonicalERealDiffToReal (u x) (v x)) =ᵐ[
      sourcePotentialNonPluripolarMeasure θ w hw.1.choose]
      (fun x => (u x).toReal - (v x).toReal) := by
  have hpole (a : M → EReal) (ha : (ofFixedModel n M).IsThetaPSH θ a) :
      ∀ᵐ x ∂sourcePotentialNonPluripolarMeasure θ w hw.1.choose, a x ≠ ⊥ := by
    apply ae_iff.mpr
    simpa only [not_not, ← sourceMixedNonPluripolarMeasure_diagonal] using
      sourceMixedNonPluripolarMeasure_pole_null (fun _ : Fin n => hw.1.choose) ha
  filter_upwards [hpole u hu.1.choose, hpole v hv.1.choose] with x hub hvb
  rw [← EReal.coe_toReal
      (((isThetaPSH_iff_nativeThetaPotential θ u).mp hu.1.choose).1.quasiPlurisubharmonic.ne_top x) hub,
    ← EReal.coe_toReal
      (((isThetaPSH_iff_nativeThetaPotential θ v).mp hv.1.choose).1.quasiPlurisubharmonic.ne_top x) hvb]
  simp only [canonicalERealDiffToReal_coe_coe, EReal.toReal_coe]

/-- Literal original signed endpoint integrals satisfy both whole unordered E1 bounds. -/
theorem sourceRelativeFiniteEnergy_endpoint_bounds_toReal
    (ω : KahlerBackground n M) (hu : SourceRelativeFiniteEnergy θ φ u hφ)
    (hv : SourceRelativeFiniteEnergy θ φ v hφ) :
    (∫ x, (u x).toReal - (v x).toReal
      ∂sourcePotentialNonPluripolarMeasure θ u hu.1.choose) ≤
        (sourceRelativeEnergy θ φ u hφ).toReal - (sourceRelativeEnergy θ φ v hφ).toReal ∧
    (sourceRelativeEnergy θ φ u hφ).toReal - (sourceRelativeEnergy θ φ v hφ).toReal ≤
      ∫ x, (u x).toReal - (v x).toReal
        ∂sourcePotentialNonPluripolarMeasure θ v hv.1.choose := by
  have hb := sourceRelativeFiniteEnergy_endpoint_bounds ω hu hv
  rwa [integral_congr_ae (sourceRelativeFiniteEnergy_diagonal_difference_ae hu hv hu),
    integral_congr_ae (sourceRelativeFiniteEnergy_diagonal_difference_ae hu hv hv)] at hb

end SGPT.PSH.VariableComplexAtlas
