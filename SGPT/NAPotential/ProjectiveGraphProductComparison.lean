import SGPT.NAPotential.ProjectiveGraphProductDifferential
import SGPT.NAPotential.ProjectiveGraphProjectiveHomeomorph

/-! # The actual original graph ambient maps continuously and injectively to native projective space
Blueprint: `projective-graph-product-local.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProductComparison

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open SGPT.Okounkov SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.NAPotential.FSPos
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open ProjectiveGraphProjection ProjectiveGraphAnalyticMap ProjectiveGraphLiteralImmersion
open ProjectiveGraphCentredChart ProjectiveGraphProductDifferential ProjectiveGraphProjectiveHomeomorph
open ProjectiveGraphSegre
open SGPT.Foundations.Analysis.FirstPass

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m s : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] [IsProper f] (E : ClosedProjectiveEmbedding f)
local instance nativeTopology : TopologicalSpace (SchemeComplexPoint
    (polynomialProjStructureMap ℂ (segreDim E.ambientDimension s))) := schemeAnalyticPointTopology _

/-- The actual original ambient product's original Segre image as the SAME native projective point. -/
def productNativeMap (z : graphAmbient f m s) :
    SchemeComplexPoint (polynomialProjStructureMap ℂ (segreDim E.ambientDimension s)) :=
  (originalProjectiveHomeomorph (segreDim E.ambientDimension s)).symm (segreAmbientMap E z)

/-- The actual original ambient/native comparison is continuous in the original analytic topologies. -/
theorem continuous_productNativeMap : Continuous (productNativeMap (m := m) (s := s) E) :=
  (originalProjectiveHomeomorph (segreDim E.ambientDimension s)).symm.continuous.comp
    (contMDiff_segreAmbientMap (m := m) (s := s) E).continuous

/-- The original actual ambient Segre map is injective. -/
theorem segreAmbientMap_injective : Function.Injective (segreAmbientMap (m := m) (s := s) E) := by
  intro z w h
  have he : (projectivePoint f E (m + 1) z.1, z.2) = (projectivePoint f E (m + 1) w.1, w.2) :=
    segreMap_injective h
  have h1 : projectivePoint f E (m + 1) z.1 = projectivePoint f E (m + 1) w.1 :=
    congrArg (fun q : ComplexProjectiveSpace E.ambientDimension × ComplexProjectiveSpace s => q.1) he
  have h2 : z.2 = w.2 :=
    congrArg (fun q : ComplexProjectiveSpace E.ambientDimension × ComplexProjectiveSpace s => q.2) he
  exact Prod.ext ((injective_projectivePoint f E (m + 1)) h1) h2

/-- The actual original ambient/native comparison is injective, without a supplied point dictionary. -/
theorem productNativeMap_injective : Function.Injective (productNativeMap (m := m) (s := s) E) :=
  (originalProjectiveHomeomorph (segreDim E.ambientDimension s)).symm.injective.comp
    (segreAmbientMap_injective (m := m) (s := s) E)

variable [IsIntegral X] (j : Fin (E.ambientDimension + 1)) [hU : Nonempty (coordOpen E j)]
  (b : Fin s → X.functionField)
  (W : (Spec (.of (Algebra.adjoin Γ(X, coordOpen E j) (Set.range b)))).Opens)

/-- **The actual ORIGINAL product graph map becomes the SAME native original immersion**, as literal point functions. -/
theorem productNativeMap_openGraphMap
    (p : SchemeComplexPoint (openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W)) :
    productNativeMap (m := m) E
      (openGraphMap (f := f) (m := m) (coordOpen E j) (isAffineOpen_coordOpen E j) b W p) =
        schemeComplexPointMap _ _ (literalOpenProjectiveMap E j hU b W)
          (literalOpenProjectiveMap_overBase E j hU b W) p := by
  apply (originalProjectiveHomeomorph (segreDim E.ambientDimension s)).injective
  rw [productNativeMap, Homeomorph.apply_symm_apply, originalProjectiveHomeomorph_apply]
  exact (originalSegre_native_square (m := m) E j b W p).symm

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProductComparison
