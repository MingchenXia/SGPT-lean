import SGPT.NAPotential.ProjectiveGraphProductComparison
import SGPT.NAPotential.ProjectiveGraphOriginalClosure
import SGPT.NAPotential.NativeImmersionLocalImage
import SGPT.NAPotential.GraphProjectiveIdealTrace

/-!
# The SAME original product graph map parametrizes its SAME original global graph locally

All graph, point, image and topology dictionaries are proved for the original
objects. No local-image or graph certificate is supplied.
Blueprint: `projective-graph-product-local.tex`.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProductLocal

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open SGPT.Okounkov SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.NAPotential.FSPos
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open ProjectiveGraphProjection ProjectiveGraphAnalyticMap ProjectiveGraphLiteralImmersion
open ProjectiveGraphProductComparison ProjectiveGraphOriginalClosure ProjectiveGraphSegre
open ProjectiveGraphAnalyticZero ProjectiveGraphRelationCore
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology
attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)} {m s : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] [IsProper f]
  (E : ClosedProjectiveEmbedding f) (j : Fin (E.ambientDimension + 1))
  [hU : Nonempty (coordOpen E j)] (b : Fin s → X.functionField)
  (W : (Spec (.of (Algebra.adjoin Γ(X, coordOpen E j) (Set.range b)))).Opens) [Nonempty W]
  [hsm : SmoothOfRelativeDimension (m + 1)
    (openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W)]

local instance sourceTopology : TopologicalSpace (SchemeComplexPoint
    (openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W)) := schemeAnalyticPointTopology _
local instance nativeTopology : TopologicalSpace (SchemeComplexPoint
    (polynomialProjStructureMap ℂ (segreDim E.ambientDimension s))) := schemeAnalyticPointTopology _

include hsm in
/-- **The actual original local-image field of ProductGraphData**, for SAME U_j,b,W and the SAME original full-relation Γ. -/
theorem openGraphMap_local
    (p : SchemeComplexPoint (openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W))
    (O : Set (SchemeComplexPoint (openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W)))
    (hO : O ∈ 𝓝 p) :
    ∃ V ∈ 𝓝 (openGraphMap (f := f) (m := m) (coordOpen E j) (isAffineOpen_coordOpen E j) b W p),
      globalRelationGraph (m := m) E b ∩ V ⊆
        openGraphMap (f := f) (m := m) (coordOpen E j) (isAffineOpen_coordOpen E j) b W '' O := by
  let g := openGraphMap (f := f) (m := m) (coordOpen E j) (isAffineOpen_coordOpen E j) b W
  let a := schemeComplexPointMap _ _ (literalOpenProjectiveMap E j hU b W)
    (literalOpenProjectiveMap_overBase E j hU b W)
  let G := productNativeMap (m := m) (s := s) E
  obtain ⟨V, hV, hlocal⟩ := SGPT.NAPotential.NativeImmersionLocalImage.pointMap_local
    _ _ (literalOpenProjectiveMap E j hU b W) (literalOpenProjectiveMap_overBase E j hU b W)
      (m + 1) (segreDim E.ambientDimension s) p O hO
  have hGp : G (g p) = a p := productNativeMap_openGraphMap (m := m) E j b W p
  have hnhds : G ⁻¹' V ∈ 𝓝 (g p) := by
    apply (continuous_productNativeMap (m := m) (s := s) E).continuousAt.preimage_mem_nhds
    change V ∈ 𝓝 (G (g p))
    rw [hGp]
    exact hV
  refine ⟨G ⁻¹' V, hnhds, ?_⟩
  intro z hz
  have hclosure : schemeComplexPointImage
      (polynomialProjStructureMap ℂ (segreDim E.ambientDimension s)) (G z) ∈
        closure (Set.range (literalOpenProjectiveMap E j hU b W)) := by
    let := schemeFunctionFieldAlgebra f
    rw [closure_range_literalOpenProjectiveMap E j b W]
    apply (SGPT.NAPotential.GraphProjectiveIdealTrace.inverse_mem_zeroLocus_iff
      (segreDim E.ambientDimension s) (relationCore (A := ℂ) (rationalSegreCoordinates E b))
        (segreAmbientMap (m := m) E z)).mpr
    exact hz.1
  obtain ⟨q, hqO, hq⟩ := hlocal ⟨hclosure, hz.2⟩
  refine ⟨q, hqO, ?_⟩
  apply productNativeMap_injective (m := m) (s := s) E
  exact (productNativeMap_openGraphMap (m := m) E j b W q).trans hq

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProductLocal
