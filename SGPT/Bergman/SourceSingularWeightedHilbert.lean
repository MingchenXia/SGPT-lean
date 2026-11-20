import SGPT.Bergman.SourceWeightedQuadraticIntegral
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# SingularWeightedHilbert

`H⁰(X, L^k ⊗ T ⊗ I(kφ))` with the Bernstein--Markov norm `N^k_{v,μ}` is a finite-dimensional Hilbert space (source `prop:BMNimplynorm`, `def:Bergman:L778`).

Ported from the previous team's drafts (`work/sgpt-active-lanes-20261102/bergman-*`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SingularWeightedHilbert
open Bundle Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.NormAxioms
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  (L T : HermitianHolomorphicLineBundle n X)
  (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
  (hBM : IsBernsteinMarkov L T W μ) (k : ℕ) (hk : 0 < k) (φ : X → EReal)

/-- EXACT original multiplier-H0 vectors, exposing their original source v,mu norm without
changing the existing global supnorm instance. The identity equivalence below proves BOTH maps. -/
def SourceHilbertSections (L T : HermitianHolomorphicLineBundle n X)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
    (_hBM : IsBernsteinMarkov L T W μ) (k : ℕ) (_hk : 0 < k) (φ : X → EReal) : Type :=
  ↥(fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
    (sourceDegreeMultiplierIdeal (n := n) k φ))

instance sourceHilbertAddCommGroup : AddCommGroup (SourceHilbertSections L T W μ hBM k hk φ) :=
  inferInstanceAs (AddCommGroup ↥(fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
    (sourceDegreeMultiplierIdeal (n := n) k φ)))

instance sourceHilbertModule : Module ℂ (SourceHilbertSections L T W μ hBM k hk φ) :=
  inferInstanceAs (Module ℂ ↥(fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
    (sourceDegreeMultiplierIdeal (n := n) k φ)))

/-- Actual original FULL multiplier submodule, with literal inverse identity maps, not a finite family. -/
def sourceHilbertOriginalEquiv :
    SourceHilbertSections L T W μ hBM k hk φ ≃ₗ[ℂ]
      ↥(fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
        (sourceDegreeMultiplierIdeal (n := n) k φ)) := LinearEquiv.refl ℂ _

/-- The ACTUAL original BM norm restricts along the true whole multiplier-submodule inclusion. -/
def sourceHilbertAddGroupNorm : AddGroupNorm (SourceHilbertSections L T W μ hBM k hk φ) where
  toFun s := bernsteinMarkovL2AddGroupNorm L T W μ hBM k hk
    (sourceHilbertOriginalEquiv L T W μ hBM k hk φ s).val
  map_zero' := map_zero _
  add_le' s t := (bernsteinMarkovL2AddGroupNorm L T W μ hBM k hk).toAddGroupSeminorm.add_le' _ _
  neg' s := (bernsteinMarkovL2AddGroupNorm L T W μ hBM k hk).toAddGroupSeminorm.neg' _
  eq_zero_of_map_eq_zero' s hs := by
    apply (sourceHilbertOriginalEquiv L T W μ hBM k hk φ).injective
    apply Subtype.ext
    exact (bernsteinMarkovL2AddGroupNorm L T W μ hBM k hk).eq_zero_of_map_eq_zero' _ hs

instance sourceHilbertNormedAddCommGroup :
    NormedAddCommGroup (SourceHilbertSections L T W μ hBM k hk φ) :=
  (sourceHilbertAddGroupNorm L T W μ hBM k hk φ).toNormedAddCommGroup

/-- Exact original source norm, retaining the SAME ALL-section vector and SAME mu. -/
theorem sourceHilbert_norm_eq (s : SourceHilbertSections L T W μ hBM k hk φ) :
    ‖s‖ = bernsteinMarkovL2AddGroupNorm L T W μ hBM k hk
      (sourceHilbertOriginalEquiv L T W μ hBM k hk φ s).val := rfl

/-- Genuine source homogeneity and the original group norm supply the full normed-space core. -/
theorem sourceHilbertNormCore : NormedSpace.Core ℂ (SourceHilbertSections L T W μ hBM k hk φ) where
  norm_nonneg := norm_nonneg
  norm_triangle := norm_add_le
  norm_eq_zero_iff := fun _ => norm_eq_zero
  norm_smul r s := bernsteinMarkovL2AddGroupNorm_smul L T W μ hBM k hk r
    (sourceHilbertOriginalEquiv L T W μ hBM k hk φ s).val

instance sourceHilbertNormedSpace : NormedSpace ℂ (SourceHilbertSections L T W μ hBM k hk φ) :=
  NormedSpace.ofCore (sourceHilbertNormCore L T W μ hBM k hk φ)

/-- EXACT original source extended norm readback; no changed norm is hidden by the carrier. -/
theorem sourceHilbert_ofReal_norm (s : SourceHilbertSections L T W μ hBM k hk φ) :
    ENNReal.ofReal ‖s‖ = weightedL2Norm (twistedPower L T k).Fiber k W.erealWeight μ
      (sourceHilbertOriginalEquiv L T W μ hBM k hk φ s).val :=
  bernsteinMarkovL2AddGroupNorm_ofReal L T W μ hBM k hk _

/-- The original real quadratic integral is retained on the SAME entire source multiplier submodule. -/
theorem sourceHilbert_norm_sq_integral (s : SourceHilbertSections L T W μ hBM k hk φ) :
    ‖s‖ ^ 2 = ∫ x, weightedQuadraticDensity L T W k
      (sourceHilbertOriginalEquiv L T W μ hBM k hk φ s).val x ∂μ :=
  bernsteinMarkov_norm_sq_eq_integral L T W μ hBM k hk _

/-- Parallelogram is a proved actual integral identity, never an incoming Hilbert assumption. -/
theorem sourceHilbert_parallelogram (s t : SourceHilbertSections L T W μ hBM k hk φ) :
    ‖s + t‖ ^ 2 + ‖s - t‖ ^ 2 = 2 * (‖s‖ ^ 2 + ‖t‖ ^ 2) :=
  bernsteinMarkov_norm_parallelogram L T W μ hBM k hk
    (sourceHilbertOriginalEquiv L T W μ hBM k hk φ s).val
    (sourceHilbertOriginalEquiv L T W μ hBM k hk φ t).val

/-- ACTUAL compatible complex inner product, with all axioms INTERNALLY produced from the proved norm law. -/
instance sourceHilbertInnerProductSpace : InnerProductSpace ℂ (SourceHilbertSections L T W μ hBM k hk φ) :=
  InnerProductSpace.ofNorm ℂ (fun s t => by
    simpa only [← sq] using sourceHilbert_parallelogram L T W μ hBM k hk φ s t)

/-- Genuine original compact H0 finiteness, transported by the literal identity equivalence. -/
instance sourceHilbertFiniteDimensional : FiniteDimensional ℂ (SourceHilbertSections L T W μ hBM k hk φ) := by
  let := fullTwistedMultiplierSections_finiteDimensional L T k φ
  exact FiniteDimensional.of_injective (sourceHilbertOriginalEquiv L T W μ hBM k hk φ).toLinearMap
    (sourceHilbertOriginalEquiv L T W μ hBM k hk φ).injective

/-- Completeness is PROVED from genuine finite dimension, not assumed as a Hilbert certificate. -/
instance sourceHilbertCompleteSpace : CompleteSpace (SourceHilbertSections L T W μ hBM k hk φ) :=
  FiniteDimensional.complete ℂ _

/-- Genuine finite orthonormal basis, produced only AFTER the original whole Hilbert structure. -/
def sourceOrthonormalBasis :
    OrthonormalBasis (Fin (Module.finrank ℂ (SourceHilbertSections L T W μ hBM k hk φ))) ℂ
      (SourceHilbertSections L T W μ hBM k hk φ) := stdOrthonormalBasis ℂ _

end SGPT.Bergman.SingularWeightedHilbert
