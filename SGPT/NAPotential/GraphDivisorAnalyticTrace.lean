import SGPT.NAPotential.GraphDivisorResidueIdeal
import SGPT.NAPotential.ProjectiveGraphNativeReadback
import SGPT.NAPotential.ProjectiveGraphNativePoint

/-!
# Exact native divisor trace under the actual original graph map

Complete blueprint: `graph-divisor-analytic-trace.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.GraphDivisorAnalyticTrace

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes Set Filter
open SGPT.NAPotential.AlgPrimes3 GraphDivisorResidueIdeal
open ProjectiveGraphProjection ProjectiveGraphAnalyticMap ProjectiveGraphNativeReadback
open ProjectiveGraphPointEvaluation
open ProjectiveGraphLiteralImmersion ProjectiveGraphCentredChart ProjectiveGraphCoordinateCharts
open ProjectiveGraphSegre
open SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.NAPotential.FSPos SGPT.Okounkov
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold

/-- The ACTUAL native image point belongs to the ORIGINAL prime closure precisely
when its actual original coefficient map kills that prime. -/
theorem nativePoint_mem_closure_iff (B : CommRingCat.{0})
    (q : Spec (.of ℂ) ⟶ Spec B) (z : Spec B) :
    q default ∈ closure {z} ↔ ∀ a ∈ z.asIdeal, (Spec.preimage q).hom a = 0 := by
  rw [PrimeSpectrum.closure_singleton]
  conv_lhs => rw [← Spec.map_preimage q]
  rw [Spec.map_apply, PrimeSpectrum.mem_zeroLocus]
  have hzero (t : Spec (.of ℂ)) : t.asIdeal = ⊥ := by
    have h : t = (⟨(⊥ : Ideal ℂ), inferInstance⟩ : PrimeSpectrum ℂ) := Subsingleton.elim _ _
    rw [h]
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.coe_comap, Set.subset_def,
    Set.mem_preimage, SetLike.mem_coe, hzero, Ideal.mem_bot]

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)} {m : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] [IsProper f]

local instance pointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance pointCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance pointManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable (E : ClosedProjectiveEmbedding f) (j : Fin (E.ambientDimension + 1))
  [hU : Nonempty (coordOpen E j)] {s : ℕ} (b : Fin s → X.functionField)

/-- The actual global divisor in the ORIGINAL product ambient, defined by the SAME
literal native coordinate vector and ORIGINAL prime ideal. -/
def productDivisorLocus
    (p : Ideal (Algebra.adjoin Γ(X, coordOpen E j) (Set.range b))) :
    Set (graphAmbient f m s) := by
  let := affineChartAlgebra f (coordOpen E j)
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionField_affineChartScalarTower f (coordOpen E j)
  exact segreAmbientMap (m := m) E ⁻¹' divisorZeroLocus p (literalCoordinates E j hU b)

/-- Actual original Segre pullback makes the produced global divisor analytic. -/
theorem isComplexAnalyticSubset_productDivisorLocus
    (p : Ideal (Algebra.adjoin Γ(X, coordOpen E j) (Set.range b))) :
    IsComplexAnalyticSubset (n := (m + 1) + s) (productDivisorLocus (m := m) E j b p) := by
  let := affineChartAlgebra f (coordOpen E j)
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionField_affineChartScalarTower f (coordOpen E j)
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
    (contMDiff_segreAmbientMap (m := m) E)
    (isComplexAnalyticSubset_divisorZeroLocus p (literalCoordinates E j hU b))

variable (W : (Spec (.of (Algebra.adjoin Γ(X, coordOpen E j) (Set.range b)))).Opens)

/-- The ACTUAL graph-point evaluator preserves actual complex scalars. -/
def graphPointAlgEval
    (y : SchemeComplexPoint (openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W)) :
    letI := affineChartAlgebra f (coordOpen E j)
    letI := schemeFunctionFieldAlgebra f
    letI := schemeFunctionField_affineChartScalarTower f (coordOpen E j)
    Algebra.adjoin Γ(X, coordOpen E j) (Set.range b) →ₐ[ℂ] ℂ := by
  let := affineChartAlgebra f (coordOpen E j)
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionField_affineChartScalarTower f (coordOpen E j)
  refine {
    toRingHom := graphPointEval (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W y
    commutes' := ?_ }
  intro c
  rw [graphPointEval_eq_native E j b W y]
  let q : SchemeComplexPoint
      (affineStructuralMap ℂ (.of (Algebra.adjoin Γ(X, coordOpen E j) (Set.range b)))) :=
    schemeComplexPointMap _ _ W.ι (by
      rw [← projection_structure E j hU b]
      exact (Category.assoc _ _ _).symm) y
  exact (ProjectiveGraphNativePoint.affinePointAlgebra q).commutes c

/-- Actual product-map membership in the produced global divisor is EXACTLY vanishing
of the actual native point evaluator on the original actual prime ideal. -/
theorem openGraphMap_mem_productDivisorLocus_iff
    (p : Ideal (Algebra.adjoin Γ(X, coordOpen E j) (Set.range b)))
    (y : SchemeComplexPoint (openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W)) :
    openGraphMap (f := f) (m := m) (coordOpen E j) (isAffineOpen_coordOpen E j) b W y ∈
      productDivisorLocus (m := m) E j b p ↔
        ∀ a ∈ p, graphPointEval (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W y a = 0 := by
  let := affineChartAlgebra f (coordOpen E j)
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionField_affineChartScalarTower f (coordOpen E j)
  change segreAmbientMap (m := m) E
      (openGraphMap (f := f) (m := m) (coordOpen E j) (isAffineOpen_coordOpen E j) b W y) ∈
    divisorZeroLocus p (literalCoordinates E j hU b) ↔ _
  rw [segreAmbientMap_openGraphMap_eq (m := m) E j b W y]
  exact divisorZeroLocus_iff_primeVanishing p (literalCoordinates E j hU b)
    (coordSegrePivot E j s) (literalCoordinates_pivot E j hU b)
    (adjoin_literalCoordinates E j hU b) (graphPointAlgEval E j b W y)

/-- The ORIGINAL actual graph map pulls the PRODUCED global analytic divisor back
EXACTLY to the actual native prime closure in the SAME original open. -/
theorem openGraphMap_preimage_productDivisorLocus
    (z : Spec (.of (Algebra.adjoin Γ(X, coordOpen E j) (Set.range b)))) (hzW : z ∈ W) :
    (openGraphMap (f := f) (m := m) (coordOpen E j) (isAffineOpen_coordOpen E j) b W) ⁻¹'
        productDivisorLocus (m := m) E j b z.asIdeal =
      schemeNativeAlgebraicTrace (openStructureMap (f := f) (coordOpen E j)
        (isAffineOpen_coordOpen E j) b W) (closure {(⟨z, hzW⟩ : W.toScheme)}) := by
  have hclosure : closure {(⟨z, hzW⟩ : W.toScheme)} = W.ι ⁻¹' closure {z} := by
    simpa only [Set.image_singleton, Scheme.Opens.ι_apply] using
      (W.ι.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image
        {(⟨z, hzW⟩ : W.toScheme)})
  ext y
  rw [Set.mem_preimage, openGraphMap_mem_productDivisorLocus_iff (m := m) E j b W z.asIdeal y]
  change (∀ a ∈ z.asIdeal,
    graphPointEval (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W y a = 0) ↔
    schemeComplexPointImage (openStructureMap (f := f) (coordOpen E j)
      (isAffineOpen_coordOpen E j) b W) y ∈ closure {(⟨z, hzW⟩ : W.toScheme)}
  rw [hclosure, graphPointEval_eq_native E j b W y]
  have h := nativePoint_mem_closure_iff
    (.of (Algebra.adjoin Γ(X, coordOpen E j) (Set.range b))) (y.val ≫ W.ι) z
  simpa only [Scheme.Hom.comp_apply, schemeComplexPointImage, Set.mem_preimage] using h.symm

end SGPT.NAPotential.GraphDivisorAnalyticTrace
