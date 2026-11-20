import SGPT.NAPotential.ProjectiveGraphEmbedding

/-!
# Actual native graph-chart coordinate readback

The actual quotient/chart map reads every original homogeneous fraction as its
literal graph evaluation. Native Proj functoriality gives the same scheme square.
Blueprint: `projective-graph-chart-readback.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphChartReadback

open MvPolynomial AlgebraicGeometry CategoryTheory HomogeneousLocalization
open ProjectiveGraphRelations ProjectiveGraphQuotient ProjectiveGraphEmbedding

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable {σ A K : Type u} [CommRing A] [CommRing K] [Algebra A K]

/-- The actual native polynomial pivot chart's degree-zero ring. -/
abbrev PolynomialChartRing := HomogeneousLocalization.Away (homogeneousSubmodule (Option σ) A) (X none)

/-- The actual quotient chart map followed by the actual literal graph evaluation equivalence. -/
def coordinateReadback (b : σ → K) : PolynomialChartRing (σ := σ) (A := A) →+* Algebra.adjoin A (Set.range b) :=
  (graphChartRingEquiv b).toRingHom.comp
    (HomogeneousLocalization.Away.map
      (GradedGraphQuotient.gradedMk (homogeneousSubmodule (Option σ) A) (graphRelationIdeal (A := A) b)) (X none))

/-- Every original homogeneous fraction has its actual original graph value in the literal A[b]. -/
theorem coordinateReadback_mk (b : σ → K) (n : ℕ) (p : MvPolynomial (Option σ) A) (hp : p.IsHomogeneous n) :
    coordinateReadback b (HomogeneousLocalization.Away.mk (homogeneousSubmodule (Option σ) A)
      (isHomogeneous_X A none) n p (by simpa using hp)) = graphEval b p := by
  have hmap := HomogeneousLocalization.Away.map_mk
    (GradedGraphQuotient.gradedMk (homogeneousSubmodule (Option σ) A) (graphRelationIdeal (A := A) b))
    (X none) (isHomogeneous_X A none) n p (by simpa using hp)
  exact (congrArg (chartEval (A := A) b) hmap).trans (chartEval_mk b n p hp)

/-- The actual affine graph immersion is the actual evaluation spectrum map followed by the native quotient chart map. -/
theorem affineGraphChartImmersion_eq (b : σ → K) :
    affineGraphChartImmersion (A := A) b =
      Spec.map (CommRingCat.ofHom (graphChartRingEquiv (A := A) b).toRingHom) ≫
        Proj.awayι (graphGrading (A := A) b) (chartCoordinate (A := A) b) (chartCoordinate_mem (A := A) b) one_pos := by
  change (Spec.map (CommRingCat.ofHom (graphChartRingEquiv (A := A) b).toRingHom) ≫
    (Proj.basicOpenIsoSpec (graphGrading (A := A) b) (chartCoordinate (A := A) b) (chartCoordinate_mem (A := A) b) one_pos).inv) ≫
      (graphChartOpen (A := A) b).ι = _
  exact Category.assoc _ _ _

/-- **Exact native graph-coordinate square**, without a supplied readback certificate. -/
theorem affineGraphEmbedding_eq (b : σ → K) :
    affineGraphChartImmersion (A := A) b ≫ graphInclusion (A := A) b =
      Spec.map (CommRingCat.ofHom (coordinateReadback (A := A) b)) ≫
        Proj.awayι (homogeneousSubmodule (Option σ) A) (X none) (isHomogeneous_X A none) one_pos := by
  rw [affineGraphChartImmersion_eq, Category.assoc]
  have hsq := Proj.awayι_comp_map
    (GradedGraphQuotient.gradedMk (homogeneousSubmodule (Option σ) A) (graphRelationIdeal (A := A) b))
    (GradedGraphQuotient.irrelevant_le_map (homogeneousSubmodule (Option σ) A) (relationIdeal (A := A) b))
    one_pos (X none) (isHomogeneous_X A none)
  change Proj.awayι (graphGrading (A := A) b) (chartCoordinate (A := A) b) (chartCoordinate_mem (A := A) b) one_pos ≫
    graphInclusion (A := A) b = _ at hsq
  rw [hsq, ← Category.assoc, ← Spec.map_comp]
  rfl

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphChartReadback
