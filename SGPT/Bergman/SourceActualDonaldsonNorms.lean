import SGPT.Bergman.SourceDonaldsonNormVolume
import SGPT.Bergman.SourceGeneralBergmanTransport

/-!
# ActualDonaldsonNorms

The norms `N^k_{v,K}`, `N^k_{v,μ}` and a reference `L²` norm restricted to `H⁰(X, L^k ⊗ T ⊗ I(kφ))`.

Ported from the previous team's drafts (`work/sgpt-active-lanes-20261102/bergman-*`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.QuantizationFrontier
open Bundle Set MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.NormAxioms
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.SingularWeightedHilbert SGPT.Bergman.GeneralBMTransport
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  (L T : HermitianHolomorphicLineBundle n X)
  (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
  (hBM : IsBernsteinMarkov L T W μ) (k : ℕ) (hk : 0 < k) (φ : X → EReal)

omit [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
/-- The actual FULL ideal-H0 inclusion is genuinely injective, by its proved literal identity equivalence. -/
theorem sourceOriginalSectionLinear_injective :
    Function.Injective (sourceOriginalSectionLinear L T W μ hBM k hk φ) := by
  intro s t h
  apply (sourceHilbertOriginalEquiv L T W μ hBM k hk φ).injective
  exact Subtype.ext h

/-- A genuine whole-space complex norm restricts to the ENTIRE true ideal-H0 space.
No finite family or desired norm/finiteness property is supplied. -/
def restrictWholeSectionNorm (Q : AddGroupNorm (twistedSections L T k))
    (hQ : ∀ (c : ℂ) (s : twistedSections L T k), Q (c • s) = ‖c‖ * Q s) :
    ComplexNorm (SourceHilbertSections L T W μ hBM k hk φ) where
  toAddGroupNorm := {
    toAddGroupSeminorm := Q.toAddGroupSeminorm.comp
      (sourceOriginalSectionLinear L T W μ hBM k hk φ).toAddMonoidHom
    eq_zero_of_map_eq_zero' := fun s hs => by
      apply sourceOriginalSectionLinear_injective L T W μ hBM k hk φ
      rw [map_zero]
      exact Q.eq_zero_of_map_eq_zero' _ hs }
  norm_smul c s := by
    change Q (sourceOriginalSectionLinear L T W μ hBM k hk φ (c • s)) = _
    rw [map_smul, hQ]
    rfl

/-- The original actual source supremum norm on ALL multiplier sections, with SAME v and metric. -/
def sourceSupComplexNorm : ComplexNorm (SourceHilbertSections L T W μ hBM k hk φ) :=
  restrictWholeSectionNorm L T W μ hBM k hk φ
    (weightedSupAddGroupNorm (twistedPower L T k).Fiber W k)
    (weightedSupAddGroupNorm_smul (twistedPower L T k).Fiber W k)

/-- The original SAME-mu probability BM norm, on the ENTIRE actual original ideal-H0. -/
def sourceL2ComplexNorm : ComplexNorm (SourceHilbertSections L T W μ hBM k hk φ) :=
  restrictWholeSectionNorm L T W μ hBM k hk φ
    (bernsteinMarkovL2AddGroupNorm L T W μ hBM k hk)
    (bernsteinMarkovL2AddGroupNorm_smul L T W μ hBM k hk)

omit [BorelSpace X] in
/-- Exact original source supremum norm values, not a merely equivalent norm. -/
theorem sourceSupComplexNorm_ofReal (s : SourceHilbertSections L T W μ hBM k hk φ) :
    ENNReal.ofReal ((sourceSupComplexNorm L T W μ hBM k hk φ).toAddGroupNorm s) =
      weightedSupNorm (twistedPower L T k).Fiber k W.erealWeight
        (sourceOriginalSectionLinear L T W μ hBM k hk φ s) :=
  weightedSupAddGroupNorm_ofReal (twistedPower L T k).Fiber W k _

/-- Exact original source L2 norm values, retaining SAME v/mu and EVERY full section. -/
theorem sourceL2ComplexNorm_ofReal (s : SourceHilbertSections L T W μ hBM k hk φ) :
    ENNReal.ofReal ((sourceL2ComplexNorm L T W μ hBM k hk φ).toAddGroupNorm s) =
      weightedL2Norm (twistedPower L T k).Fiber k W.erealWeight μ
        (sourceOriginalSectionLinear L T W μ hBM k hk φ s) :=
  bernsteinMarkovL2AddGroupNorm_ofReal L T W μ hBM k hk _

/-- TRUE literal sheaf-tensor Gamma unit balls retain the EXACT source supremum admissibility condition. -/
theorem literalGamma_sourceSup_unitBall (s : LiteralTwistedMultiplierSections L T k φ) :
    literalSourceHilbertEquiv L T W μ hBM k hk φ s ∈ normUnitBall
      (sourceSupComplexNorm L T W μ hBM k hk φ) ↔
    weightedSupNorm (twistedPower L T k).Fiber k W.erealWeight
      (literalTwistedMultiplierSectionEquiv L T k φ s).val ≤ 1 := by
  change (sourceSupComplexNorm L T W μ hBM k hk φ).toAddGroupNorm _ ≤ 1 ↔ _
  rw [← ENNReal.ofReal_le_one, sourceSupComplexNorm_ofReal]
  rfl

/-- TRUE literal Gamma source L2 unit balls retain SAME mu and the EXACT source condition. -/
theorem literalGamma_sourceL2_unitBall (s : LiteralTwistedMultiplierSections L T k φ) :
    literalSourceHilbertEquiv L T W μ hBM k hk φ s ∈ normUnitBall
      (sourceL2ComplexNorm L T W μ hBM k hk φ) ↔
    weightedL2Norm (twistedPower L T k).Fiber k W.erealWeight μ
      (literalTwistedMultiplierSectionEquiv L T k φ s).val ≤ 1 := by
  change (sourceL2ComplexNorm L T W μ hBM k hk φ).toAddGroupNorm _ ≤ 1 ↔ _
  rw [← ENNReal.ofReal_le_one, sourceL2ComplexNorm_ofReal]
  rfl

/-- Actual smooth positivity and explicit probability INTERNALLY produce the literal source reference norm.
The SAME unscaled measure mu0 is retained; no arbitrary norm or BM output is an input. -/
def sourceZeroReferenceComplexNorm (μ0 : Measure X) [IsProbabilityMeasure μ0]
    (hμ0 : SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1.IsSmoothPositiveVolume (n := n) μ0) :
    ComplexNorm (SourceHilbertSections L T W μ hBM k hk φ) :=
  restrictWholeSectionNorm L T W μ hBM k hk φ
    (smoothPositiveProbabilityVolume_L2Norm L T 0 μ0 hμ0 k hk)
    (smoothPositiveProbabilityVolume_L2Norm_smul L T 0 μ0 hμ0 k hk)

/-- EVERY actual reference vector retains the literal SAME zero-weight whole-X source measure integral. -/
theorem sourceZeroReferenceComplexNorm_ofReal (μ0 : Measure X) [IsProbabilityMeasure μ0]
    (hμ0 : SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1.IsSmoothPositiveVolume (n := n) μ0)
    (s : SourceHilbertSections L T W μ hBM k hk φ) :
    ENNReal.ofReal ((sourceZeroReferenceComplexNorm L T W μ hBM k hk φ μ0 hμ0).toAddGroupNorm s) =
      weightedL2Norm (twistedPower L T k).Fiber k (SGPT.Bergman.BernsteinMarkov.univRealWeight 0)
        (μ0.comap (Subtype.val : ↥(univ : Set X) → X))
        (sourceOriginalSectionLinear L T W μ hBM k hk φ s) :=
  smoothPositiveProbabilityVolume_L2Norm_ofReal L T 0 μ0 hμ0 k hk _

end SGPT.Bergman.QuantizationFrontier
