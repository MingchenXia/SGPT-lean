import SGPT.PSH.SourceIModelTestCurves
import SGPT.Envelopes.SourcePositiveMassCurrents
import SGPT.Foundations.Analysis.Pending.IEnvelopeIncreasingRegularizedSupremum

/-! # The original endpoint limits of I-model test curves

The negative-infinity limit is the literal spatial USC supremum of the
original open slices.  An explicit cofinal sequence supplies the sequence
needed by the genuine native increasing I-envelope theorem.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- Actual original subcutoff parameters cofinal towards negative infinity. -/
def sourceTestCurveExhaustingParameter (Γ : SourceTestCurvePredata θ) (j : ℕ) :
    Iio Γ.max :=
  ⟨Γ.max - ((j : ℝ) + 1), by
    change Γ.max - ((j : ℝ) + 1) < Γ.max
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith⟩

/-- The same genuine source slices increase along the explicit exhaustion. -/
theorem SourceTestCurvePredata.exhaustingPotential_monotone
    (Γ : SourceTestCurvePredata θ) :
    Monotone (fun j : ℕ ↦ Γ.potential (sourceTestCurveExhaustingParameter Γ j)) := by
  intro j k hjk x
  apply Γ.antitone x
  change Γ.max - ((k : ℝ) + 1) ≤ Γ.max - ((j : ℝ) + 1)
  have hcast : (j : ℝ) ≤ k := by exact_mod_cast hjk
  linarith

/-- Cofinality identifies the entire raw supremum, at every original point. -/
theorem SourceTestCurvePredata.exhaustingPotential_iSup_eq
    (Γ : SourceTestCurvePredata θ) :
    (⨆ j : ℕ, Γ.potential (sourceTestCurveExhaustingParameter Γ j)) =
      ⨆ τ : Iio Γ.max, Γ.potential τ := by
  apply le_antisymm
  · exact iSup_le fun j ↦ le_iSup Γ.potential (sourceTestCurveExhaustingParameter Γ j)
  · apply iSup_le
    intro τ
    obtain ⟨j, hj⟩ := exists_nat_gt (Γ.max - τ.1)
    have hparam : sourceTestCurveExhaustingParameter Γ j ≤ τ := by
      change Γ.max - ((j : ℝ) + 1) ≤ τ.1
      linarith
    exact (show Γ.potential τ ≤ Γ.potential (sourceTestCurveExhaustingParameter Γ j)
      from fun x ↦ Γ.antitone x hparam).trans
        (le_iSup (fun j : ℕ ↦ Γ.potential (sourceTestCurveExhaustingParameter Γ j)) j)

/-- The regularized exhaustion is exactly the original limit function. -/
theorem SourceTestCurvePredata.exhaustingPotential_regularized_eq
    (Γ : SourceTestCurvePredata θ) :
    uscRegularization (⨆ j : ℕ, Γ.potential (sourceTestCurveExhaustingParameter Γ j)) =
      sourceTestCurveLimit Γ := by
  rw [Γ.exhaustingPotential_iSup_eq]
  apply congrArg uscRegularization
  funext x
  exact iSup_apply

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- The actual source limit remains I-model; positive mass and bigness are
produced from the original test curve, with no limit-model certificate. -/
theorem SourceTestCurve.limit_iModel (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hI : SourceTestCurveIsIModel Γ) :
    sourceIModel θ (sourceTestCurveLimit Γ.toSourceTestCurvePredata) := by
  let v : ℕ → M → EReal := fun j ↦
    Γ.potential (sourceTestCurveExhaustingParameter Γ.toSourceTestCurvePredata j)
  have hv (j : ℕ) : IsThetaPshPotential (atlasClosedFormToNative θ).val (v j) :=
    Γ.native_thetaPSH _
  have hu : IsThetaPshPotential (atlasClosedFormToNative θ).val
      (sourceTestCurveLimit Γ.toSourceTestCurvePredata) :=
    (isThetaPSH_iff_nativeThetaPotential θ _).mp Γ.limit_thetaPSH
  have hbig := sourcePositiveMass_isBig omega Γ.limit_thetaPSH Γ.positiveLimitMass
  have hpos : DiagonalMass.HasPositivePotentialMass (atlasClosedFormToNative θ)
      (sourceTestCurveLimit Γ.toSourceTestCurvePredata) hu := Γ.positiveLimitMass
  have hlim := IEnvelopeIncreasingRegularizedSupremum.iSingularityEnvelope_regularized_iSup_eq
    omega (atlasClosedFormToNative θ) hbig hv
    Γ.toSourceTestCurvePredata.exhaustingPotential_monotone hu
    Γ.toSourceTestCurvePredata.exhaustingPotential_regularized_eq hpos
  have hfixed (j : ℕ) : IEnvelope.iSingularityEnvelope (atlasClosedFormToNative θ).val
      (v j) = v j := (hI _).2.symm
  simp only [hfixed] at hlim
  apply (sourceIModel_iff_native θ _).mpr
  exact ⟨hu, Γ.toSourceTestCurvePredata.exhaustingPotential_regularized_eq.symm.trans hlim⟩

/-- Whole original prop:GammaminfImodel on its actual positive-union domain. -/
theorem source_i_model_test_curve_limit_whole (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceIModelTestCurvesPositive θ) :
    sourceIModel θ (sourceTestCurveLimit Γ.toSourceTestCurvePredata) :=
  Γ.limit_iModel omega ((sourceIModelTestCurvesPositive_iff_slices omega Γ).mp hΓ)

omit [BorelSpace M] in
/-- The original cutoff infimum remains I-model, even when its mass is zero. -/
theorem SourceTestCurve.cutoff_iModel (Γ : SourceTestCurve θ)
    (hI : SourceTestCurveIsIModel Γ) :
    sourceIModel θ (sourceTestCurveCutoff Γ.toSourceTestCurvePredata) := by
  have : Nonempty (Iio Γ.max) :=
    ⟨⟨Γ.max - 1, by change Γ.max - 1 < Γ.max; linarith⟩⟩
  have hraw : (⨅ r : Iio Γ.max, Γ.potential r) =
      sourceTestCurveCutoff Γ.toSourceTestCurvePredata := by
    funext x
    exact iInf_apply
  apply (sourceIModel_iff_native θ _).mpr
  rw [← hraw]
  exact ActualIEnvelopeOrderInfimum.isIModelPotential_iInf_of_isThetaPshPotential
    (atlasClosedFormToNative θ) hI
    (hraw.symm ▸ (isThetaPSH_iff_nativeThetaPotential θ _).mp Γ.cutoff_thetaPSH)

end SGPT.PSH.VariableComplexAtlas
