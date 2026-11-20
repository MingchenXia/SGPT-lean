import SGPT.NAPotential.ProjectiveGraphSegreAlgebra
import SGPT.NAPotential.ProjectiveGraphQuotient
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Actual native Proj of the original full homogeneous relation quotient

Both coordinate-renaming maps preserve the genuine quotient grading. Native
Proj functoriality then identifies the original quotient's actual pivot open.
Blueprint: `projective-graph-pivot-scheme.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphPivotScheme

open MvPolynomial AlgebraicGeometry CategoryTheory
open ProjectiveGraphRelations ProjectiveGraphRelationCore ProjectiveGraphSegreAlgebra ProjectiveGraphQuotient

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A K : Type} [CommRing A] [CommRing K] [Algebra A K] {N : ℕ}

/-- The original full homogeneous relation quotient, before any coordinate permutation. -/
abbrev RelationRing (v : Fin (N + 1) → K) :=
  MvPolynomial (Fin (N + 1)) A ⧸ (relationCore (A := A) v).toIdeal

/-- Its actual quotient grading, given by images of original homogeneous polynomials. -/
abbrev relationGrading (v : Fin (N + 1) → K) : ℕ → Submodule A (RelationRing (A := A) v) :=
  GradedGraphQuotient.grading (homogeneousSubmodule (Fin (N + 1)) A) (relationCore (A := A) v).toIdeal

instance relationGradedRing (v : Fin (N + 1) → K) : GradedRing (relationGrading (A := A) v) :=
  GradedGraphQuotient.gradedRing _ _ (relationCore (A := A) v).isHomogeneous

/-- Original coordinate renaming descends and preserves every actual quotient homogeneous degree. -/
def pivotMap (v : Fin (N + 1) → K) (p : Fin (N + 1)) (hp : v p = 1) :
    graphGrading (A := A) (pivotTail v p) →+*ᵍ relationGrading (A := A) v where
  __ := (pivotQuotientEquiv (A := A) v p hp).toRingHom
  map_mem hx := by
    obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hx
    refine Submodule.mem_map.mpr ⟨rename (finSuccEquiv' p).symm q, hq.rename_isHomogeneous, ?_⟩
    rfl

/-- The inverse original coordinate renaming also preserves every actual quotient homogeneous degree. -/
def pivotInv (v : Fin (N + 1) → K) (p : Fin (N + 1)) (hp : v p = 1) :
    relationGrading (A := A) v →+*ᵍ graphGrading (A := A) (pivotTail v p) where
  __ := (pivotQuotientEquiv (A := A) v p hp).symm.toRingHom
  map_mem hx := by
    obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hx
    refine Submodule.mem_map.mpr ⟨rename (finSuccEquiv' p) q, hq.rename_isHomogeneous, ?_⟩
    apply (pivotQuotientEquiv (A := A) v p hp).injective
    change (pivotQuotientEquiv (A := A) v p hp) (Ideal.Quotient.mk _ (rename (finSuccEquiv' p) q)) =
      (pivotQuotientEquiv (A := A) v p hp)
        ((pivotQuotientEquiv (A := A) v p hp).symm (Ideal.Quotient.mk _ q))
    rw [AlgEquiv.apply_symm_apply]
    change Ideal.Quotient.mk _ (rename (finSuccEquiv' p).symm (rename (finSuccEquiv' p) q)) = _
    rw [rename_rename, Equiv.symm_comp_self, rename_id_apply]

theorem pivotInv_comp_pivotMap (v : Fin (N + 1) → K) (p : Fin (N + 1)) (hp : v p = 1) :
    (pivotInv (A := A) v p hp).comp (pivotMap v p hp) = .id (graphGrading (A := A) (pivotTail v p)) := by
  ext x
  exact (pivotQuotientEquiv (A := A) v p hp).symm_apply_apply x

theorem pivotMap_comp_pivotInv (v : Fin (N + 1) → K) (p : Fin (N + 1)) (hp : v p = 1) :
    (pivotMap (A := A) v p hp).comp (pivotInv v p hp) = .id (relationGrading (A := A) v) := by
  ext x
  exact (pivotQuotientEquiv (A := A) v p hp).apply_symm_apply x

/-- An actual graded inverse provides every positive-degree element needed for native Proj functoriality. -/
theorem irrelevant_le_map_of_inverse {B C σ τ : Type*} [CommRing B] [CommRing C]
    [SetLike σ B] [AddSubgroupClass σ B] [SetLike τ C] [AddSubgroupClass τ C]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜) (hfg : ∀ x, f (g x) = x) :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f := by
  apply (HomogeneousIdeal.irrelevant_le _).mpr
  intro i hi x hx
  have hmem : g x ∈ HomogeneousIdeal.irrelevant 𝒜 :=
    HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hi (g.map_mem hx)
  change x ∈ Ideal.map f.toRingHom (HomogeneousIdeal.irrelevant 𝒜).toIdeal
  rw [← hfg x]
  exact Ideal.mem_map_of_mem _ hmem

/-- The actual native Proj of the original relation quotient. -/
def relationScheme (v : Fin (N + 1) → K) : Scheme := Proj (relationGrading (A := A) v)

/-- Original coordinate renaming gives an actual native scheme isomorphism of the two genuine quotients. -/
def pivotProjIso (v : Fin (N + 1) → K) (p : Fin (N + 1)) (hp : v p = 1) :
    graphScheme (A := A) (pivotTail v p) ≅ relationScheme (A := A) v where
  hom := Proj.map (pivotInv (A := A) v p hp)
    (irrelevant_le_map_of_inverse _ (pivotMap v p hp) (pivotQuotientEquiv (A := A) v p hp).symm_apply_apply)
  inv := Proj.map (pivotMap (A := A) v p hp)
    (irrelevant_le_map_of_inverse _ (pivotInv v p hp) (pivotQuotientEquiv (A := A) v p hp).apply_symm_apply)
  hom_inv_id := by
    simp only [← Proj.map_comp, pivotInv_comp_pivotMap, Proj.map_id, graphScheme]
  inv_hom_id := by
    simp only [← Proj.map_comp, pivotMap_comp_pivotInv, Proj.map_id, relationScheme]

/-- The actual original pivot coordinate class. -/
def originalPivot (v : Fin (N + 1) → K) (p : Fin (N + 1)) : RelationRing (A := A) v :=
  Ideal.Quotient.mk _ (X p)

theorem pivotMap_chartCoordinate (v : Fin (N + 1) → K) (p : Fin (N + 1)) (hp : v p = 1) :
    pivotMap (A := A) v p hp (chartCoordinate (A := A) (pivotTail v p)) = originalPivot (A := A) v p := by
  change Ideal.Quotient.mk _ (rename (finSuccEquiv' p).symm (X none)) = _
  simp [originalPivot, finSuccEquiv']

/-- The genuine pivot basic open in the original full relation quotient. -/
def originalPivotOpen (v : Fin (N + 1) → K) (p : Fin (N + 1)) : (relationScheme (A := A) v).Opens :=
  Proj.basicOpen (relationGrading v) (originalPivot v p)

theorem preimage_pivotChart (v : Fin (N + 1) → K) (p : Fin (N + 1)) (hp : v p = 1) :
    (pivotProjIso (A := A) v p hp).inv ⁻¹ᵁ graphChartOpen (A := A) (pivotTail v p) =
      originalPivotOpen (A := A) v p := by
  change Proj.basicOpen (relationGrading v)
    (pivotMap (A := A) v p hp (chartCoordinate (A := A) (pivotTail v p))) = _
  rw [pivotMap_chartCoordinate]
  rfl

/-- **Actual original quotient pivot chart** is the native spectrum of its remaining coordinate algebra. -/
def originalPivotChartSchemeIso (v : Fin (N + 1) → K) (p : Fin (N + 1)) (hp : v p = 1) :
    (originalPivotOpen (A := A) v p).toScheme ≅ Spec (.of (Algebra.adjoin A (Set.range (pivotTail v p)))) :=
  (Scheme.isoOfEq _ (preimage_pivotChart (A := A) v p hp).symm) ≪≫
    ((pivotProjIso (A := A) v p hp).inv.preimageIso _) ≪≫ graphChartSchemeIso (A := A) (pivotTail v p)

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphPivotScheme
