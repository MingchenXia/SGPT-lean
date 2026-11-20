import SGPT.Foundations.PublishedEnvelope.Char0.NativeProperModification
import SGPT.Foundations.PublishedEnvelope.Char0.BPIntegralTarget
import SGPT.Foundations.PublishedEnvelope.ComplexGeometry.Germs.SchemeNativeBirationalModification

/-! # The SAME original BP morphism is an actual native analytic modification -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Foundations.PublishedEnvelope.Char0.NativeBPModification

open CategoryTheory AlgebraicGeometry ComplexSchemes HolomorphicGerms
open SGPT.Foundations.PublishedAnalysis.Pluripotential
open SGPT.Foundations.PublishedAnalysis.AnalyticGeometry.AnalyticModificationLocalDiscrepancy
open scoped Topology Manifold

variable {R : Type} [CommRing R] [IsDomain R]
  (f : Spec (.of R) ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (I : Ideal R) (hI : I ≠ ⊥)

private instance originalBPSmooth : SmoothOfRelativeDimension n
    ((SGPT.Support.PublishedPrincipalization.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f) :=
  affinePrincipalization_smoothOfRelativeDimension f n I hI

private instance originalBPProper :
    IsProper (SGPT.Support.PublishedPrincipalization.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : IsLocallyNoetherian (Spec (.of R)) := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsLocallyNoetherian (affinePrincipalizationTriple f n I hI).X.left := by
    change IsLocallyNoetherian (Spec (.of R))
    infer_instance
  exact (SGPT.Support.PublishedPrincipalization.Sequence.BP (affinePrincipalizationTriple f n I hI)).isProper_composite

private instance originalBPSeparated : IsSeparated
    ((SGPT.Support.PublishedPrincipalization.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f) := by
  let π := (SGPT.Support.PublishedPrincipalization.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite
  let : IsProper π := originalBPProper f n I hI
  have hπ : IsSeparated π := inferInstance
  have hf : IsSeparated f := inferInstance
  exact IsSeparated.stableUnderComposition.comp_mem π f hπ hf
private instance originalBPQuasiCompact : QuasiCompact
    ((SGPT.Support.PublishedPrincipalization.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f) := by
  let π := (SGPT.Support.PublishedPrincipalization.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite
  let : IsProper π := originalBPProper f n I hI
  let : IsAffineHom f := isAffineHom_of_isAffine f
  have hf : QuasiCompact f := inferInstance
  exact @quasiCompact_comp _ _ _ π f inferInstance hf
private instance originalBPIntegral :
    IsIntegral (SGPT.Support.PublishedPrincipalization.Sequence.BP (affinePrincipalizationTriple f n I hI)).last :=
  affinePrincipalization_isIntegral_last f n I hI

local instance originalBaseTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance originalBPTopology : TopologicalSpace (SchemeComplexPoint
    ((SGPT.Support.PublishedPrincipalization.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f)) :=
  schemeAnalyticPointTopology _
local instance originalBaseCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticComplexChartedSpace f n
local instance originalBPCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint
    ((SGPT.Support.PublishedPrincipalization.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f)) :=
  schemeAnalyticComplexChartedSpace _ n
local instance originalBaseManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticComplex_isComplexManifold f n
local instance originalBPManifold : IsComplexManifold n (SchemeComplexPoint
    ((SGPT.Support.PublishedPrincipalization.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f)) :=
  schemeAnalyticComplex_isComplexManifold _ n

/-- The SAME original BP composite is an actual analytic modification in its actual native
manifolds. Properness, analytic exceptional sets, empty interior and the holomorphic inverse
are all derived internally from the original algebraic geometry. -/
theorem affinePrincipalization_isAnalyticModification :
    let S := SGPT.Support.PublishedPrincipalization.Sequence.BP (affinePrincipalizationTriple f n I hI)
    IsAnalyticModification (n := n) (schemeComplexPointMap (S.composite ≫ f) f S.composite rfl) := by
  let S := SGPT.Support.PublishedPrincipalization.Sequence.BP (affinePrincipalizationTriple f n I hI)
  let U := (specIdealSheaf I).support.compl
  let : IsIso (S.composite ∣_ U) := affinePrincipalization_isIso_restrict f n I hI
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : IsNoetherianRing R := isLocallyNoetherian_Spec.mp
    (LocallyOfFiniteType.isLocallyNoetherian f)
  exact schemeNative_isAnalyticModification_of_isIso_restrict f S.composite n U
    (nonempty_compl_support_specIdealSheaf I hI)
    (NativeProperModification.blowupSequence_isProper f S)

end SGPT.Foundations.PublishedEnvelope.Char0.NativeBPModification
