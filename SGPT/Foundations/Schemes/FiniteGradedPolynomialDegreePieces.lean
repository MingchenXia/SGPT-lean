import SGPT.Foundations.Schemes.FiniteShiftedGradedPresentation
import SGPT.Foundations.Schemes.PolynomialCoordinateLocalization

/-! # Actual degree pieces of finite graded polynomial modules

True finite homogeneous covers prove finite degree pieces and a single lower
support bound. The coordinate index type may be empty. No Hilbert-series or
resolution certificate is assumed.
-/

universe u

open DirectSum

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section PolynomialPieces

variable {K I : Type u} [Field K] [Fintype I]

omit [Fintype I] in
/-- Actual integral weight one agrees with the usual natural homogeneous degree. -/
theorem polynomialIntegralGrading_nat_eq (m : ℕ) :
    polynomialIntegralGrading (K := K) (I := I) (m : ℤ) =
      MvPolynomial.homogeneousSubmodule I K m := by
  rw [polynomialIntegralGrading, MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported,
    MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  congr 1
  ext d
  have h : Finsupp.weight (fun _ : I => (1 : ℤ)) d = (d.degree : ℤ) := by
    simp [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum]
  simp only [Set.mem_ofPred_eq, h, Nat.cast_inj]

omit [Fintype I] in
/-- An actual negative integral polynomial degree has no monomials. -/
theorem polynomialIntegralGrading_eq_bot_of_neg (m : ℤ) (hm : m < 0) :
    polynomialIntegralGrading (K := K) (I := I) m = ⊥ := by
  apply le_antisymm
  · intro p hp
    change p = 0
    apply MvPolynomial.IsWeightedHomogeneous.eq_zero_of_no_monomials hp
    intro d hd
    have h : Finsupp.weight (fun _ : I => (1 : ℤ)) d = (d.degree : ℤ) := by
      simp [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum]
    rw [h] at hd
    have : (0 : ℤ) ≤ (d.degree : ℤ) := Int.natCast_nonneg _
    omega
  · exact bot_le

/-- Every actual integral polynomial degree piece is finite over the true field. -/
theorem polynomialIntegralGrading_finite (m : ℤ) :
    Module.Finite K (polynomialIntegralGrading (K := K) (I := I) m) := by
  by_cases hm : 0 ≤ m
  · have he : m = (m.toNat : ℤ) := (Int.toNat_of_nonneg hm).symm
    rw [he, polynomialIntegralGrading_nat_eq]
    exact homogeneousPolynomialPiece_finite m.toNat
  · rw [polynomialIntegralGrading_eq_bot_of_neg m (lt_of_not_ge hm)]
    infer_instance

end PolynomialPieces

section ShiftedFreeCoefficients

variable {K R J : Type u} [CommRing K] [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) (δ : J → ℤ)

/-- A true shifted free degree piece is the literal product of its coefficient pieces. -/
def finiteShiftedFreePieceCoefficientsEquiv (m : ℤ) :
    finiteShiftedFreePiece 𝒜 δ m ≃ₗ[K] (j : J) → 𝒜 (m - δ j) where
  toFun a j := ⟨a.val j, a.property j⟩
  invFun a := ⟨fun j => (a j : R), fun j => (a j).property⟩
  left_inv _a := rfl
  right_inv _a := rfl
  map_add' _a _b := rfl
  map_smul' _c _a := rfl

end ShiftedFreeCoefficients

section ShiftedPolynomial

variable {K I J : Type u} [Field K] [Fintype I] [Fintype J] (δ : J → ℤ)

/-- Every actual finite shifted polynomial degree piece is finite over the true field. -/
theorem finiteShiftedPolynomialPiece_finite (m : ℤ) :
    Module.Finite K
      (finiteShiftedFreePiece (polynomialIntegralGrading (K := K) (I := I)) δ m) := by
  let : ∀ j : J, Module.Finite K
      (polynomialIntegralGrading (K := K) (I := I) (m - δ j)) :=
    fun j => polynomialIntegralGrading_finite (m - δ j)
  exact Module.Finite.equiv
    (finiteShiftedFreePieceCoefficientsEquiv
      (polynomialIntegralGrading (K := K) (I := I)) δ m).symm

omit [Fintype I] [Fintype J] in
/-- Below every genuine shift, the actual shifted polynomial degree piece is zero. -/
theorem finiteShiftedPolynomialPiece_eq_bot_of_lt_shifts (m : ℤ)
    (hm : ∀ j, m < δ j) :
    finiteShiftedFreePiece (polynomialIntegralGrading (K := K) (I := I)) δ m = ⊥ := by
  apply le_antisymm
  · intro a ha
    change a = 0
    funext j
    have hj := ha j
    rw [polynomialIntegralGrading_eq_bot_of_neg (m - δ j) (sub_neg.mpr (hm j))] at hj
    exact hj
  · exact bot_le

end ShiftedPolynomial

section DegreeCover

variable {K R J M : Type u} [CommRing K] [CommRing R] [Algebra K R]
  [Fintype J] [DecidableEq J] [AddCommGroup M]
  [Module K M] [Module R M] [IsScalarTower K R M]
  (𝒜 : ℤ → Submodule K R) [GradedRing 𝒜]
  (ℳ : ℤ → Submodule K M) [SetLike.GradedSMul 𝒜 ℳ]
  (δ : J → ℤ) (g : J → M) (hg : ∀ j, g j ∈ ℳ (δ j))

omit [DecidableEq J] in
/-- The literal true-field-linear restriction of the actual homogeneous free cover. -/
def finiteHomogeneousPresentationDegreeMap (m : ℤ) :
    finiteShiftedFreePiece 𝒜 δ m →ₗ[K] ℳ m :=
  (((finiteHomogeneousPresentationMap (R := R) g).restrictScalars K).comp
    (finiteShiftedFreePiece 𝒜 δ m).subtype).codRestrict _ (by
      intro a
      exact finiteHomogeneousPresentationMap_homogeneous 𝒜 ℳ δ g hg m a a.property)

/-- A genuine homogeneous cover is surjective on each actual degree piece. -/
theorem finiteHomogeneousPresentationDegreeMap_surjective [DirectSum.Decomposition ℳ]
    (hs : Function.Surjective (finiteHomogeneousPresentationMap (R := R) g)) (m : ℤ) :
    Function.Surjective (finiteHomogeneousPresentationDegreeMap 𝒜 ℳ δ g hg m) := by
  intro v
  obtain ⟨a, ha, hav⟩ := homogeneousMap_surjectiveDegree (finiteShiftedFreePiece 𝒜 δ) ℳ
    (finiteHomogeneousPresentationMap (R := R) g)
    (finiteHomogeneousPresentationMap_homogeneous 𝒜 ℳ δ g hg) hs m v v.property
  exact ⟨⟨a, ha⟩, Subtype.ext hav⟩

end DegreeCover

section FiniteGradedPolynomial

variable {K I M : Type u} [Field K] [hI : Fintype I]
  [AddCommGroup M] [Module K M] [Module (MvPolynomial I K) M]
  [hTower : IsScalarTower K (MvPolynomial I K) M]
  (ℳ : ℤ → Submodule K M) [hDecomp : DirectSum.Decomposition ℳ]
  [hGraded : SetLike.GradedSMul (polynomialIntegralGrading (K := K) (I := I)) ℳ]
  [hFinite : Module.Finite (MvPolynomial I K) M]

include hI hTower hDecomp hGraded hFinite

/-- Every true finite graded polynomial module has finite actual degree pieces. -/
theorem finiteGradedPolynomialPiece_finite (m : ℤ) : Module.Finite K (ℳ m) := by
  classical
  obtain ⟨s, δ, hg, hs, _⟩ :=
    finiteShiftedGradedPresentation_exists (polynomialIntegralGrading (K := K) (I := I)) ℳ
  let := finiteShiftedPolynomialPiece_finite (K := K) (I := I) δ m
  exact Module.Finite.of_surjective
    (finiteHomogeneousPresentationDegreeMap
      (polynomialIntegralGrading (K := K) (I := I)) ℳ δ (fun j : s => (j : M)) hg m)
    (finiteHomogeneousPresentationDegreeMap_surjective
      (polynomialIntegralGrading (K := K) (I := I)) ℳ δ _ hg hs m)

omit hTower in
/-- One true homogeneous cover gives a fixed lower support bound for the actual module. -/
theorem finiteGradedPolynomialPiece_eventually_eq_bot :
    ∃ b : ℤ, ∀ m : ℤ, m < b → ℳ m = ⊥ := by
  classical
  obtain ⟨s, δ, hg, hs, _⟩ :=
    finiteShiftedGradedPresentation_exists (polynomialIntegralGrading (K := K) (I := I)) ℳ
  let b : ℤ := Finset.univ.inf' (by simp : (Finset.univ : Finset (Option s)).Nonempty)
    (fun j => j.elim 0 δ)
  refine ⟨b, fun m hm => ?_⟩
  have hfree := finiteShiftedPolynomialPiece_eq_bot_of_lt_shifts (K := K) (I := I) δ m
    (fun j => lt_of_lt_of_le hm
      (Finset.inf'_le (f := fun j : Option s => j.elim 0 δ) (Finset.mem_univ (some j))))
  apply le_antisymm
  · intro v hv
    change v = 0
    obtain ⟨a, ha, hav⟩ := homogeneousMap_surjectiveDegree
      (finiteShiftedFreePiece (polynomialIntegralGrading (K := K) (I := I)) δ) ℳ
      (finiteHomogeneousPresentationMap (R := MvPolynomial I K) (fun j : s => (j : M)))
      (finiteHomogeneousPresentationMap_homogeneous
        (polynomialIntegralGrading (K := K) (I := I)) ℳ δ _ hg) hs m v hv
    rw [hfree] at ha
    have ha0 : a = 0 := ha
    rw [ha0, map_zero] at hav
    exact hav.symm
  · exact bot_le

end FiniteGradedPolynomial

end

end SGPT.Foundations.Schemes
