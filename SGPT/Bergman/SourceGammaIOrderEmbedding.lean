import SGPT.Bergman.SourceIdealOrderSectionInclusion

/-!
# GammaIOrderEmbedding

The inclusion of multiplier-ideal section spaces induced by `φ ⪯_I ψ`, preserving values, weighted norms and densities (used in source `rmk:Bergman:L797`).

Ported from the previous team's drafts (`work/sgpt-active-lanes-20261102/bergman-*`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.IdealOrderMonotonicity
open Bundle Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.NormAxioms
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.SingularWeightedHilbert
open HermitianHolomorphicLineBundle

section AbstractTransport
variable {A B E : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B] [AddCommGroup E] [Module ℂ E]
  (S U : Submodule ℂ E) (h : S ≤ U) (eA : A ≃ₗ[ℂ] S) (eB : B ≃ₗ[ℂ] U)

/-- Linear transport of an actual subspace inclusion through proved linear equivalences. -/
def submoduleTransport : A →ₗ[ℂ] B :=
  eB.symm.toLinearMap.comp ((Submodule.inclusion h).comp eA.toLinearMap)

/-- The true inverse law retains the original ambient vector, without reducing the equivalences. -/
theorem submoduleTransport_val (a : A) :
    (eB (submoduleTransport S U h eA eB a)).val = (eA a).val :=
  congrArg Subtype.val (eB.apply_symm_apply ((Submodule.inclusion h) (eA a)))
end AbstractTransport

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (L T : HermitianHolomorphicLineBundle n X) {φ ψ : X → EReal}
  (hI : sourceIOrder (ofFixedModel n X) φ ψ) (k : ℕ) (hk : 0 < k)

/-- A genuine complex linear map on the LITERAL original tensor-ideal Gamma spaces,
produced from the actual proved full-submodule inclusion and BOTH genuine Gamma maps. -/
def originalGammaIOrderInclusion :
    LiteralTwistedMultiplierSections L T k φ →ₗ[ℂ] LiteralTwistedMultiplierSections L T k ψ :=
  submoduleTransport _ _ (fullIdealSections_le_of_sourceIOrder L T hI k hk)
    (literalTwistedMultiplierSectionEquiv L T k φ)
    (literalTwistedMultiplierSectionEquiv L T k ψ)

set_option backward.isDefEq.respectTransparency false in
/-- The actual Gamma map retains the SAME entire original section, not only a selected set of coordinates. -/
theorem originalGammaIOrderInclusion_section (s : LiteralTwistedMultiplierSections L T k φ) :
    (literalTwistedMultiplierSectionEquiv L T k ψ
      (originalGammaIOrderInclusion L T hI k hk s)).val =
        (literalTwistedMultiplierSectionEquiv L T k φ s).val :=
  submoduleTransport_val _ _ (fullIdealSections_le_of_sourceIOrder L T hI k hk)
    (literalTwistedMultiplierSectionEquiv L T k φ)
    (literalTwistedMultiplierSectionEquiv L T k ψ) s

set_option backward.isDefEq.respectTransparency false in
/-- Genuine injectivity on ALL actual original Gamma sections, internally proved. -/
theorem originalGammaIOrderInclusion_injective : Function.Injective (originalGammaIOrderInclusion L T hI k hk) := by
  intro s t hst
  apply (literalTwistedMultiplierSectionEquiv L T k φ).injective
  apply Subtype.ext
  have h := congrArg (fun u : LiteralTwistedMultiplierSections L T k ψ =>
    (literalTwistedMultiplierSectionEquiv L T k ψ u).val) hst
  simpa only [originalGammaIOrderInclusion_section] using h

/-- EVERY same original fiber value is preserved by the actual literal Gamma embedding. -/
theorem originalGammaIOrderInclusion_eval (s : LiteralTwistedMultiplierSections L T k φ) (x : X) :
    (literalTwistedMultiplierSectionEquiv L T k ψ
      (originalGammaIOrderInclusion L T hI k hk s)).val x =
        (literalTwistedMultiplierSectionEquiv L T k φ s).val x :=
  congrArg (fun u : twistedSections L T k => u x) (originalGammaIOrderInclusion_section L T hI k hk s)

/-- The original SAME-v weighted supremum norm is preserved exactly, with no new norm assumption. -/
theorem originalGammaIOrderInclusion_supNorm
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (s : LiteralTwistedMultiplierSections L T k φ) :
    weightedSupNorm (twistedPower L T k).Fiber k W.erealWeight
        (literalTwistedMultiplierSectionEquiv L T k ψ (originalGammaIOrderInclusion L T hI k hk s)).val =
      weightedSupNorm (twistedPower L T k).Fiber k W.erealWeight
        (literalTwistedMultiplierSectionEquiv L T k φ s).val :=
  congrArg (weightedSupNorm (twistedPower L T k).Fiber k W.erealWeight)
    (originalGammaIOrderInclusion_section L T hI k hk s)

variable [MeasurableSpace X]

/-- EXACT original SAME-v, SAME-mu norm preservation on the true literal Gamma spaces.
This holds for any actual measure and hence for the original BM probability, without smooth-volume strengthening. -/
theorem originalGammaIOrderInclusion_L2Norm
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
    (s : LiteralTwistedMultiplierSections L T k φ) :
    weightedL2Norm (twistedPower L T k).Fiber k W.erealWeight μ
        (literalTwistedMultiplierSectionEquiv L T k ψ (originalGammaIOrderInclusion L T hI k hk s)).val =
      weightedL2Norm (twistedPower L T k).Fiber k W.erealWeight μ
        (literalTwistedMultiplierSectionEquiv L T k φ s).val :=
  congrArg (weightedL2Norm (twistedPower L T k).Fiber k W.erealWeight μ)
    (originalGammaIOrderInclusion_section L T hI k hk s)

omit [MeasurableSpace X] in
/-- EVERY original same-metric weighted point density is retained at the SAME point of K. -/
theorem originalGammaIOrderInclusion_density
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X)
    (s : LiteralTwistedMultiplierSections L T k φ) (x : W.carrier) :
    weightedSectionDensity (twistedPower L T k).Fiber k W.erealWeight
        (literalTwistedMultiplierSectionEquiv L T k ψ (originalGammaIOrderInclusion L T hI k hk s)).val x =
      weightedSectionDensity (twistedPower L T k).Fiber k W.erealWeight
        (literalTwistedMultiplierSectionEquiv L T k φ s).val x :=
  congrArg (fun u : twistedSections L T k => weightedSectionDensity (twistedPower L T k).Fiber k W.erealWeight u x)
    (originalGammaIOrderInclusion_section L T hI k hk s)

end SGPT.Bergman.IdealOrderMonotonicity
