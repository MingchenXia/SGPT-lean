import SGPT.NAPotential.ProjectiveGraphSegreAlgebra
import SGPT.NAPotential.NativeSchemeImmersion
import SGPT.Foundations.Schemes.PolynomialProjectiveCanonical

/-!
# Literal normalized generators give the actual native projective immersion

The source map is built directly from genuine homogeneous chart dehomogenization
and literal evaluation, with closed immersion proved from algebra generation.
Blueprint: `projective-graph-affine-immersion.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphAffineImmersion

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes MvPolynomial
open ProjectiveGraphSegreAlgebra
attribute [local instance] MvPolynomial.gradedAlgebra

variable {B : Type} [CommRing B] [Algebra ℂ B] {N : ℕ}

/-- Literal evaluation on the actual native projective pivot coordinate ring. -/
def coordinateEvaluation (v : Fin (N + 1) → B) (p : Fin (N + 1)) :
    polynomialProjCoordinateRing ℂ N p →ₐ[ℂ] B :=
  (aeval (pivotTail v p)).comp (polynomialProjCoordinateDehomogenization ℂ N p)

/-- Every actual native homogeneous ratio reads its literal normalized coordinate. -/
theorem coordinateEvaluation_ratio (v : Fin (N + 1) → B) (p : Fin (N + 1)) (hp : v p = 1)
    (i : Fin (N + 1)) :
    coordinateEvaluation v p (polynomialProjCoordinateRatio ℂ N p i) = v i := by
  refine Fin.succAboveCases p ?_ (fun j => ?_) i
  · rw [polynomialProjCoordinateRatio_self, map_one, hp]
  · simp only [coordinateEvaluation, AlgHom.comp_apply,
      polynomialProjCoordinateDehomogenization_ratio, aeval_X, pivotTail]

/-- The original normalized algebra generators manufacture surjectivity of the actual chart map. -/
theorem coordinateEvaluation_surjective (v : Fin (N + 1) → B) (p : Fin (N + 1)) (hp : v p = 1)
    (hgen : Algebra.adjoin ℂ (Set.range v) = ⊤) : Function.Surjective (coordinateEvaluation v p) := by
  have heval : Function.Surjective (aeval (pivotTail v p) : MvPolynomial (Fin N) ℂ →ₐ[ℂ] B) := by
    rw [← AlgHom.range_eq_top, aeval_range, adjoin_pivotTail v p hp, hgen]
  intro b
  obtain ⟨q, rfl⟩ := heval b
  refine ⟨polynomialProjRatioMap ℂ N p q, ?_⟩
  simp only [coordinateEvaluation, AlgHom.comp_apply,
    polynomialProjCoordinateDehomogenization_ratioMap]

/-- The actual spectrum map of that literal coordinate evaluation. -/
def affineCoordinateMap (v : Fin (N + 1) → B) (p : Fin (N + 1)) :
    Spec (.of B) ⟶ Spec (.of (polynomialProjCoordinateRing ℂ N p)) :=
  Spec.map (CommRingCat.ofHom (coordinateEvaluation v p).toRingHom)

/-- Actual native projective map of the original normalized generators. -/
def projectiveMap (v : Fin (N + 1) → B) (p : Fin (N + 1)) : Spec (.of B) ⟶ polynomialProj ℂ N :=
  affineCoordinateMap v p ≫ polynomialProjCoordinateImmersion ℂ N p

/-- Its actual affine factor is a closed immersion, proved from the actual generators. -/
theorem affineCoordinateMap_isClosedImmersion (v : Fin (N + 1) → B) (p : Fin (N + 1))
    (hp : v p = 1) (hgen : Algebra.adjoin ℂ (Set.range v) = ⊤) :
    IsClosedImmersion (affineCoordinateMap v p) :=
  IsClosedImmersion.spec_of_surjective _ (coordinateEvaluation_surjective v p hp hgen)

/-- The actual literal normalized-generator projective map is an immersion. -/
theorem projectiveMap_isImmersion (v : Fin (N + 1) → B) (p : Fin (N + 1))
    (hp : v p = 1) (hgen : Algebra.adjoin ℂ (Set.range v) = ⊤) : IsImmersion (projectiveMap v p) := by
  let := affineCoordinateMap_isClosedImmersion v p hp hgen
  dsimp only [projectiveMap]
  infer_instance

/-- The actual normalized-coordinate map preserves the given complex-algebra structure. -/
theorem projectiveMap_structure (v : Fin (N + 1) → B) (p : Fin (N + 1)) :
    projectiveMap v p ≫ polynomialProjStructureMap ℂ N = affineStructuralMap ℂ (.of B) := by
  rw [projectiveMap, Category.assoc, polynomialProjCoordinateImmersion_structure]
  simp only [affineCoordinateMap, affineStructuralMap, ← Spec.map_comp]
  congr 1
  ext c
  exact (coordinateEvaluation v p).commutes c

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphAffineImmersion
