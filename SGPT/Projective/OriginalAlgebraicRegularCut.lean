import SGPT.Projective.OriginalPositiveLineRestriction
import SGPT.Projective.AlgebraicNativeCutDimension
import SGPT.Foundations.Schemes.NativeProjectiveCutGeometry

/-! The actual SAME original algebraic regular cut, with genuine full
readers and original smooth dimension, ready for iteration.
Blueprint: original-algebraic-regular-cut.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.NAPotential.GAGAMult SGPT.NAPotential.Berkovich
open SGPT.BDivisor.NSKodaira
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.AnalyticSectionProducts HermitianHolomorphicLineBundle
open scoped Topology Manifold ContDiff

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension (n + 1) f] [IsSeparated f] [QuasiCompact f]
  (E : ClosedProjectiveEmbedding f)

local instance originalCutTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance originalCutCharts : ChartedSpace (ComplexModel (n + 1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (n + 1)
local instance originalCutManifold : IsComplexManifold (n + 1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (n + 1)

/-- Output DATA of one actual original algebraic cut. No period or degree equality field. -/
structure OriginalRegularCut (P : OriginalPositiveLine f (n + 1) E) where
  nativeCut : NativeRegularCut P.native
  originalSection : bundlePowerGlobalSections P.sheaf nativeCut.power
  coefficient : ∀ (j : P.atlas.I) (p : SchemeComplexPoint f),
    schemeComplexPointImage f p ∈ P.atlas.opens j →
    sectionCoefficient
      (positivePower (schemeHermitianLineBundle f (n + 1) E P.atlas P.metric) (nativeCut.power - 1)).Fiber
      (positivePowerAtlasFrame (schemeHermitianAtlasFrame f (n + 1) E P.atlas P.metric (P.atlas.frame j))
        (nativeCut.power - 1)).val nativeCut.cuttingSection p =
      schemeOpenRegularFunction f (n + 1) E (P.atlas.opens j) (algCoef (P.atlas.frame j) nativeCut.power originalSection) p
  ideal : ∀ (p : SchemeComplexPoint f) (g : SchemeComplexPoint f → ℂ),
    (analytificationIdeal f (n + 1) E (sectionZeroIdealSheaf (P.atlas.tensorPower nativeCut.power) originalSection)).mem p g ↔
      (nativeSectionIdeal
        (positivePower (schemeHermitianLineBundle f (n + 1) E P.atlas P.metric) (nativeCut.power - 1))
          nativeCut.cuttingSection).mem p g
  smooth : SmoothOfRelativeDimension n
    (sectionZeroι (P.atlas.tensorPower nativeCut.power) originalSection ≫ f)

/-- The genuine original producers manufacture this actual original cut before any test form. -/
theorem exists_originalRegularCut (P : OriginalPositiveLine f (n + 1) E) :
    Nonempty (OriginalRegularCut f n E P) := by
  obtain ⟨D, σ, hread, hideal, hdim, _⟩ :=
    exists_same_algebraic_regular_cut_dimension f (n + 1) E P.atlas P.metric (Nat.succ_pos n) P.positive
  exact ⟨⟨D, σ, hread, hideal, by simpa only [Nat.add_sub_cancel] using hdim⟩⟩

namespace OriginalRegularCut
variable {f n E} {P : OriginalPositiveLine f (n + 1) E} (C : OriginalRegularCut f n E P)

/-- The SAME actual original zero scheme, with its genuine scheme structure. -/
def scheme : Scheme.{0} := sectionZeroSubscheme (P.atlas.tensorPower C.nativeCut.power) C.originalSection

/-- The ACTUAL original section-zero inclusion. -/
def inclusion : C.scheme ⟶ X := sectionZeroι (P.atlas.tensorPower C.nativeCut.power) C.originalSection

instance inclusion_closedImmersion : IsClosedImmersion C.inclusion :=
  inferInstanceAs (IsClosedImmersion (sectionZeroι (P.atlas.tensorPower C.nativeCut.power) C.originalSection))

instance smooth_relative : SmoothOfRelativeDimension n (C.inclusion ≫ f) := C.smooth

/-- The literal original zero inclusion followed by the original projective embedding. -/
def embedding : ClosedProjectiveEmbedding (C.inclusion ≫ f) :=
  E.sectionZero (P.atlas.tensorPower C.nativeCut.power) C.originalSection

/-- Restrict ANY remaining original positive physical line to the SAME actual original cut. -/
def restrictLine (Q : OriginalPositiveLine f (n + 1) E) :
    OriginalPositiveLine (C.inclusion ≫ f) n C.embedding :=
  Q.restrict (n := n) f C.inclusion (n + 1) E C.embedding

end OriginalRegularCut
end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
