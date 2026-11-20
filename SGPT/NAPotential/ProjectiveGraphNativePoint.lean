import SGPT.NAPotential.ProjectiveGraphNativeReadback

/-!
# Actual normalized-generator projective maps have their actual native vector points

Blueprint: `projective-graph-native-readback.tex`.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphNativePoint

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes MvPolynomial
open ProjectiveGraphAffineImmersion ProjectiveGraphSegreAlgebra
attribute [local instance] MvPolynomial.gradedAlgebra

variable {B : Type} [CommRing B] [Algebra ℂ B] {N : ℕ}

/-- An actual affine complex point supplies its original complex algebra evaluator. -/
def affinePointAlgebra (q : SchemeComplexPoint (affineStructuralMap ℂ (.of B))) : B →ₐ[ℂ] ℂ where
  __ := (Spec.preimage q.val).hom
  commutes' c := by
    have h := congrArg (fun k => Spec.preimage k) q.property
    rw [Spec.preimage_comp] at h
    simp only [SGPT.Foundations.Schemes.affineStructuralMap, Spec.preimage_map, Spec.preimage_id] at h
    have hc := congrArg (fun k : CommRingCat.of ℂ ⟶ CommRingCat.of ℂ => k c) h
    change (Spec.preimage q.val).hom ((algebraMap ℂ B) c) = c at hc
    exact hc

/-- Actual native coordinate evaluation is exactly the original normalized native vector evaluator. -/
theorem coordinateEvaluation_affinePoint (v : Fin (N + 1) → B) (p : Fin (N + 1)) (hp : v p = 1)
    (q : SchemeComplexPoint (affineStructuralMap ℂ (.of B))) :
    (affinePointAlgebra q).comp (coordinateEvaluation v p) =
      polynomialProjVectorChartAlgebraPoint N p (fun k => affinePointAlgebra q (v k)) := by
  apply AlgHom.ext
  intro x
  change affinePointAlgebra q (aeval (pivotTail v p) (polynomialProjCoordinateDehomogenization ℂ N p x)) =
    aeval (polynomialProjVectorRatios N p (fun k => affinePointAlgebra q (v k)))
      (polynomialProjCoordinateDehomogenization ℂ N p x)
  rw [comp_aeval_apply]
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  simp only [aeval_X, pivotTail, polynomialProjVectorRatios, hp, map_one, div_one]

/-- **The actual native normalized-generator projective map has exactly its original native vector point**. -/
theorem projectiveMap_point (v : Fin (N + 1) → B) (p : Fin (N + 1)) (hp : v p = 1)
    (q : SchemeComplexPoint (affineStructuralMap ℂ (.of B))) :
    schemeComplexPointMap _ _ (projectiveMap v p) (projectiveMap_structure v p) q =
      polynomialProjVectorChartPoint N p (fun k => affinePointAlgebra q (v k)) := by
  apply Subtype.ext
  rw [polynomialProjVectorChartPoint_val]
  change q.val ≫ (ProjectiveGraphAffineImmersion.affineCoordinateMap v p ≫ polynomialProjCoordinateImmersion ℂ N p) = _
  rw [← Category.assoc]
  have hs : q.val ≫ ProjectiveGraphAffineImmersion.affineCoordinateMap v p =
      Spec.map (CommRingCat.ofHom (polynomialProjVectorChartAlgebraPoint N p
        (fun k => affinePointAlgebra q (v k))).toRingHom) := by
    calc
      _ = Spec.map (Spec.preimage q.val) ≫ ProjectiveGraphAffineImmersion.affineCoordinateMap v p :=
        congrArg (fun k => k ≫ ProjectiveGraphAffineImmersion.affineCoordinateMap v p) (Spec.map_preimage q.val).symm
      _ = _ := by
        rw [ProjectiveGraphAffineImmersion.affineCoordinateMap, ← Spec.map_comp]
        exact congrArg (fun k : polynomialProjCoordinateRing ℂ N p →ₐ[ℂ] ℂ =>
          Spec.map (CommRingCat.ofHom k.toRingHom)) (coordinateEvaluation_affinePoint v p hp q)
  rw [hs]

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphNativePoint
