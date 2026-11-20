import SGPT.NAPotential.ProjectiveGraphAffineImmersion
import SGPT.NAPotential.ProjectiveGraphRelationCore
import Mathlib.AlgebraicGeometry.FunctionField

/-! # The actual generic image of the literal normalized graph algebra
Blueprint: `projective-graph-generic-prime.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphGenericPrime

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes MvPolynomial Set
open ProjectiveGraphAffineImmersion ProjectiveGraphSegreAlgebra ProjectiveGraphRelationCore
attribute [local instance] MvPolynomial.gradedAlgebra

variable {B : Type} [CommRing B] [IsDomain B] [Algebra ℂ B] {N : ℕ}

omit [IsDomain B] in
/-- Actual chart dehomogenization and the original normalized coordinates agree on every polynomial. -/
theorem aeval_dehomogenization (v : Fin (N + 1) → B) (p : Fin (N + 1)) (hp : v p = 1)
    (q : MvPolynomial (Fin (N + 1)) ℂ) :
    aeval (pivotTail v p) (polynomialProjDehomogenization ℂ N p q) = aeval v q := by
  have h : (aeval (pivotTail v p)).comp (polynomialProjDehomogenization ℂ N p) = aeval v := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.succAboveCases p ?_ (fun a => ?_) i
    · simp only [AlgHom.comp_apply, polynomialProjDehomogenization,
        polynomialProjDehomogenizationVariable_self, aeval_X, hp, map_one]
    · simp only [AlgHom.comp_apply, polynomialProjDehomogenization,
        polynomialProjDehomogenizationVariable_succAbove, aeval_X, pivotTail]
  exact AlgHom.congr_fun h q

/-- The actual native normalized projective map's original generic point. -/
def genericImage (v : Fin (N + 1) → B) (p : Fin (N + 1)) : polynomialProj ℂ N :=
  projectiveMap v p (genericPoint (Spec (.of B)))

/-- Positive-degree original equations at the actual generic image are exactly actual original algebra relations. -/
theorem genericImage_mem_positive (v : Fin (N + 1) → B) (p : Fin (N + 1)) (hp : v p = 1)
    (d : ℕ) (hd : 0 < d) (q : MvPolynomial (Fin (N + 1)) ℂ) (hq : q.IsHomogeneous d) :
    q ∈ (genericImage v p).asHomogeneousIdeal ↔ aeval v q = 0 := by
  let G := homogeneousSubmodule (Fin (N + 1)) ℂ
  let e := coordinateEvaluation v p
  have hk : (Spec.map (CommRingCat.ofHom e.toRingHom) (genericPoint (Spec (.of B)))).asIdeal =
      RingHom.ker e.toRingHom := by
    rw [genericPoint_eq_bot_of_affine]
    rfl
  have hopen : genericImage v p ∈ Proj.basicOpen G q ↔
      e (HomogeneousLocalization.Away.isLocalizationElem (isHomogeneous_X ℂ p) hq) ≠ 0 := by
    change (Spec.map (CommRingCat.ofHom e.toRingHom) (genericPoint (Spec (.of B)))) ∈
      polynomialProjCoordinateImmersion ℂ N p ⁻¹ᵁ Proj.basicOpen G q ↔ _
    rw [polynomialProjCoordinateImmersion,
      Proj.awayι_preimage_basicOpen G (isHomogeneous_X ℂ p) one_pos hq hd,
      PrimeSpectrum.mem_basicOpen, hk]
    rfl
  have helem : HomogeneousLocalization.Away.isLocalizationElem (isHomogeneous_X ℂ p) hq =
      HomogeneousLocalization.Away.mk G (isHomogeneous_X ℂ p) d q (by simpa [G] using hq) := by
    apply HomogeneousLocalization.val_injective
    simp only [HomogeneousLocalization.Away.isLocalizationElem,
      HomogeneousLocalization.Away.val_mk, pow_one]
  have heval : e (HomogeneousLocalization.Away.isLocalizationElem (isHomogeneous_X ℂ p) hq) = aeval v q := by
    rw [helem]
    change aeval (pivotTail v p) (polynomialProjCoordinateDehomogenization ℂ N p
      (HomogeneousLocalization.Away.mk G (isHomogeneous_X ℂ p) d q (by simpa [G] using hq))) = _
    rw [polynomialProjCoordinateDehomogenization_mk ℂ N p d q hq, aeval_dehomogenization v p hp]
  simpa only [Proj.mem_basicOpen, heval, not_not] using not_congr hopen

/-- All original homogeneous equations, including degree zero, have the exact actual generic relation condition. -/
theorem genericImage_mem (v : Fin (N + 1) → B) (p : Fin (N + 1)) (hp : v p = 1)
    (d : ℕ) (q : MvPolynomial (Fin (N + 1)) ℂ) (hq : q.IsHomogeneous d) :
    q ∈ (genericImage v p).asHomogeneousIdeal ↔ aeval v q = 0 := by
  cases d with
  | succ d => exact genericImage_mem_positive v p hp _ (Nat.succ_pos _) q hq
  | zero =>
    have hXp : MvPolynomial.X p ∉ (genericImage v p).asHomogeneousIdeal := by
      rw [genericImage_mem_positive v p hp 1 one_pos (MvPolynomial.X p) (isHomogeneous_X ℂ p), aeval_X, hp]
      exact one_ne_zero
    have hprod : (q * MvPolynomial.X p).IsHomogeneous 1 := by
      simpa using hq.mul (isHomogeneous_X ℂ p)
    have hmem : q ∈ (genericImage v p).asHomogeneousIdeal ↔
        q * MvPolynomial.X p ∈ (genericImage v p).asHomogeneousIdeal :=
      ⟨fun h => Ideal.mul_mem_right _ _ h,
        fun h => ((genericImage v p).isPrime.mem_or_mem h).resolve_right hXp⟩
    rw [hmem, genericImage_mem_positive v p hp 1 one_pos _ hprod, map_mul, aeval_X, hp, mul_one]

/-- **The actual native generic-image prime is EXACTLY the full original homogeneous relation ideal**. -/
theorem genericImage_ideal (v : Fin (N + 1) → B) (p : Fin (N + 1)) (hp : v p = 1) :
    (genericImage v p).asHomogeneousIdeal = relationCore (A := ℂ) v := by
  apply HomogeneousIdeal.ext'
  intro d q hq
  rw [genericImage_mem v p hp d q hq]
  exact ⟨fun h => Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨d, hq⟩ h,
    fun h => relationCore_le_ker v h⟩


/-- The actual image of an integral scheme is generically dense in precisely its image closure. -/
theorem closure_range_eq_generic {M Y : Scheme.{0}} [IsIntegral M] (h : M ⟶ Y) :
    closure (Set.range h) = closure ({h (genericPoint M)} : Set Y) := by
  apply le_antisymm
  · apply closure_minimal _ isClosed_closure
    rintro _ ⟨x, rfl⟩
    exact specializes_iff_mem_closure.mp
      (((genericPoint_spec M).specializes (Set.mem_univ x)).map h.continuous)
  · exact closure_mono (Set.singleton_subset_iff.mpr ⟨_, rfl⟩)

/-- **The SAME literal actual normalized graph map has exactly its full relation zero locus as image closure**. -/
theorem closure_range_projectiveMap (v : Fin (N + 1) → B) (p : Fin (N + 1)) (hp : v p = 1) :
    closure (Set.range (projectiveMap v p)) = ProjectiveSpectrum.zeroLocus
      (homogeneousSubmodule (Fin (N + 1)) ℂ) ((relationCore (A := ℂ) v).toIdeal : Set _) := by
  rw [closure_range_eq_generic, ← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    ProjectiveSpectrum.vanishingIdeal_singleton]
  change ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin (N + 1)) ℂ)
    ((genericImage v p).asHomogeneousIdeal.toIdeal : Set (MvPolynomial (Fin (N + 1)) ℂ)) = _
  rw [genericImage_ideal v p hp]

/-- **EVERY prescribed nonempty graph open has the SAME full homogeneous relation zero locus as image closure**. -/
theorem closure_range_openProjectiveMap (v : Fin (N + 1) → B) (p : Fin (N + 1)) (hp : v p = 1)
    (W : (Spec (.of B)).Opens) [Nonempty W] :
    closure (Set.range (W.ι ≫ projectiveMap v p)) = ProjectiveSpectrum.zeroLocus
      (homogeneousSubmodule (Fin (N + 1)) ℂ) ((relationCore (A := ℂ) v).toIdeal : Set _) := by
  rw [closure_range_eq_generic, Scheme.Hom.comp_apply,
    genericPoint_eq_of_isOpenImmersion W.ι]
  exact (closure_range_eq_generic (projectiveMap v p)).symm.trans (closure_range_projectiveMap v p hp)

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphGenericPrime
