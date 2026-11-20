import SGPT.Foundations.Schemes.FiniteProductCechCohomology

/-! # Genuine positive-twist vanishing for polynomial coordinate complexes

Nonnegative homogeneous degree removes the actual all-negative Laurent
survivor, including the top coordinate intersection. The actual contraction
then proves native positive cohomology vanishing. Actual homogeneous
localization and finite-product comparisons transport it to true finite
shifted free graded modules with a uniform threshold.

The nonaugmented degree-zero cohomology is retained. The cardinal-zero
differential is the actual augmentation map, not a zero incoming map.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {K I : Type u} [Field K] [LinearOrder I] [Fintype I] [Nonempty I]

omit [LinearOrder I] in
/-- Actual all-negative Laurent exponents cannot have nonnegative total degree. -/
theorem negativeIntegralHomogeneousExponents_eq_empty_of_nonneg (m : ℤ) (hm : 0 ≤ m) :
    negativeIntegralHomogeneousExponents (I := I) m = ∅ := by
  classical
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro α ⟨hdeg, hneg⟩
  have hsum : (∑ i, α i) < 0 := by
    simpa using Finset.sum_lt_sum_of_nonempty
      (s := (Finset.univ : Finset I)) Finset.univ_nonempty
      (f := α) (g := fun _ => (0 : ℤ)) (fun i _ => hneg i)
  rw [hdeg] at hsum
  exact (not_lt_of_ge hm) hsum

omit [LinearOrder I] in
/-- The literal Laurent survivor vanishes at every actual subset in nonnegative degree. -/
theorem polynomialLaurentCechSurvivor_eq_zero_of_nonneg (m : ℤ) (hm : 0 ≤ m)
    (c : subsetCechCube (polynomialLaurentCechDiagram (K := K) (I := I) m))
    (S : Finset I) :
    polynomialLaurentCechSurvivor m c S = 0 := by
  classical
  apply Subtype.ext
  apply (AddMonoidAlgebra.coeffLinearEquiv K).injective
  apply Finsupp.ext
  intro α
  change (polynomialLaurentCechSurvivor m c S).val.coeff α = 0
  rw [polynomialLaurentCechSurvivor_coeff]
  split_ifs with hindex
  · by_contra hcoeff
    have hallowed := (AddMonoidAlgebra.mem_supported.mp (c S).property)
      (Finsupp.mem_support_iff.mpr hcoeff)
    have hneg : α ∈ negativeIntegralHomogeneousExponents (I := I) m :=
      ⟨hallowed.1, (projectiveLaurentContractionIndex_none_iff α).mp hindex⟩
    rw [negativeIntegralHomogeneousExponents_eq_empty_of_nonneg m hm] at hneg
    exact hneg
  · rfl

omit [LinearOrder I] in
/-- The actual survivor on every cardinal piece, including the top, is zero. -/
theorem polynomialLaurentCechCardSurvivor_eq_zero_of_nonneg (m : ℤ) (hm : 0 ≤ m)
    (n : ℕ)
    (c : subsetCechCardPiece (polynomialLaurentCechDiagram (K := K) (I := I) m) (n + 1)) :
    polynomialLaurentCechCardSurvivor m n c = 0 := by
  apply Subtype.ext
  funext S
  exact polynomialLaurentCechSurvivor_eq_zero_of_nonneg m hm c.val S

omit [Nonempty I] in
/-- The genuine contraction is zero on the actual cardinal-zero term. -/
theorem polynomialLaurentCechContraction_cardZero (m : ℤ)
    (c : subsetCechCardPiece (polynomialLaurentCechDiagram (K := K) (I := I) m) 0) :
    polynomialLaurentCechContraction m c.val = 0 := by
  classical
  funext S
  change (polynomialLaurentCechContraction m c.val S) = 0
  simp only [polynomialLaurentCechContraction, LinearMap.pi_apply, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  have hc : c.val (insert j S) = 0 := c.property (insert j S) (by simp)
  change subsetCechSign S j • polynomialLaurentCechContractionTerm m S j
    (c.val (insert j S)) = 0
  rw [hc, map_zero, smul_zero]

/-- The true cardinal-zero augmentation differential is injective in nonnegative degree. -/
theorem polynomialLaurentCechCardDifferential_zero_injective_of_nonneg
    (m : ℤ) (hm : 0 ≤ m) :
    Function.Injective
      (subsetCechCardDifferential (polynomialLaurentCechDiagram (K := K) (I := I) m) 0) := by
  intro c c' h
  have hd : subsetCechDifferential (polynomialLaurentCechDiagram m) c.val =
      subsetCechDifferential (polynomialLaurentCechDiagram m) c'.val :=
    congrArg Subtype.val h
  have hp : polynomialLaurentCechSurvivor m c.val = 0 := by
    funext S
    exact polynomialLaurentCechSurvivor_eq_zero_of_nonneg m hm c.val S
  have hp' : polynomialLaurentCechSurvivor m c'.val = 0 := by
    funext S
    exact polynomialLaurentCechSurvivor_eq_zero_of_nonneg m hm c'.val S
  have hc := polynomialLaurentCechContraction_identity m c.val
  have hc' := polynomialLaurentCechContraction_identity m c'.val
  rw [polynomialLaurentCechContraction_cardZero m c, map_zero, zero_add, hp, add_zero] at hc
  rw [polynomialLaurentCechContraction_cardZero m c', map_zero, zero_add, hp', add_zero] at hc'
  apply Subtype.ext
  rw [← hc, ← hc', hd]

/-- The literal contraction produces a primitive for every actual cardinal cycle. -/
theorem polynomialLaurentCechCardToCycles_surjective_of_nonneg (m : ℤ) (hm : 0 ≤ m)
    (n : ℕ) :
    Function.Surjective (polynomialLaurentCechCardToCycles (K := K) (I := I) m n) := by
  intro c
  refine ⟨polynomialLaurentCechCardContraction m n c.val, ?_⟩
  apply Subtype.ext
  have h := polynomialLaurentCechCardCycles_identity m n c
  rw [polynomialLaurentCechCardSurvivor_eq_zero_of_nonneg m hm n, add_zero] at h
  exact h

/-- Every actual cardinal Laurent short complex is natively exact in nonnegative degree. -/
theorem polynomialLaurentCechCardShortComplex_exact_of_nonneg (m : ℤ) (hm : 0 ≤ m)
    (n : ℕ) :
    (polynomialLaurentCechCardShortComplex (K := K) (I := I) m n).Exact := by
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro c hc
  obtain ⟨b, hb⟩ := polynomialLaurentCechCardToCycles_surjective_of_nonneg
    (K := K) (I := I) m hm n ⟨c, hc⟩
  exact ⟨b, congrArg Subtype.val hb⟩

/-- The actual nonaugmented Laurent complex is exact at every positive native degree. -/
theorem polynomialLaurentCechComplex_exactAt_of_nonneg (m : ℤ) (hm : 0 ≤ m) (n : ℕ) :
    (polynomialLaurentCechComplex (K := K) (I := I) m).ExactAt (n + 1) := by
  apply (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2)
    (CochainComplex.prev_nat_succ n) (CochainComplex.next ℕ (n + 1))).mpr
  rw [polynomialLaurentCechComplex_sc'_eq]
  exact polynomialLaurentCechCardShortComplex_exact_of_nonneg (K := K) (I := I) m hm (n + 1)

/-- Genuine nonnegative total degree kills all actual positive Laurent cohomology. -/
theorem polynomialLaurentCechComplex_homology_isZero_of_nonneg
    (m : ℤ) (hm : 0 ≤ m) (n : ℕ) :
    IsZero ((polynomialLaurentCechComplex (K := K) (I := I) m).homology (n + 1)) :=
  (polynomialLaurentCechComplex_exactAt_of_nonneg (K := K) (I := I) m hm n).isZero_homology

/-- Actual polynomial homogeneous localization has zero positive cohomology in nonnegative degree. -/
theorem polynomialCoordinateHomogeneousCech_exactAt_of_nonneg
    (m : ℤ) (hm : 0 ≤ m) (n : ℕ) :
    (subsetCechComplex
      (polynomialCoordinateHomogeneousDiagram (K := K) (I := I) m)).ExactAt (n + 1) :=
  (polynomialLaurentCechComplex_exactAt_of_nonneg (K := K) (I := I) m hm n).of_iso
    (polynomialCoordinateHomogeneousCechLaurentIso m).symm

/-- Native positive homogeneous polynomial cohomology vanishes, including the top degree. -/
theorem polynomialCoordinateHomogeneousCech_homology_isZero_of_nonneg
    (m : ℤ) (hm : 0 ≤ m) (n : ℕ) :
    IsZero ((subsetCechComplex
      (polynomialCoordinateHomogeneousDiagram (K := K) (I := I) m)).homology (n + 1)) :=
  (polynomialCoordinateHomogeneousCech_exactAt_of_nonneg (K := K) (I := I) m hm n).isZero_homology

section ShiftedFree

variable {A : Type u} [Fintype A] [DecidableEq A] (δ : A → ℤ)

/-- Actual finite shifted free positive cohomology is zero above all actual generator shifts. -/
theorem finiteShiftedPolynomialCoordinateCech_homology_isZero_of_shift_le
    (m : ℤ) (hm : ∀ a, δ a ≤ m) (n : ℕ) :
    IsZero
      ((homogeneousCoordinateCechComplex (polynomialIntegralGrading (K := K) (I := I))
        (finiteShiftedFreePiece (polynomialIntegralGrading (K := K) (I := I)) δ)
        (fun i => (MvPolynomial.X i : MvPolynomial I K)) polynomialCoordinate_X_degree m).homology
          (n + 1)) := by
  let F := fun a => polynomialCoordinateHomogeneousDiagram (K := K) (I := I) (m - δ a)
  let _ : ∀ a, Subsingleton ((subsetCechComplex (F a)).homology (n + 1)) :=
    fun a => ModuleCat.subsingleton_of_isZero
      (polynomialCoordinateHomogeneousCech_homology_isZero_of_nonneg
        (K := K) (I := I) (m - δ a) (sub_nonneg.mpr (hm a)) n)
  have hz : IsZero (ModuleCat.of K (∀ a, (subsetCechComplex (F a)).homology (n + 1))) :=
    ModuleCat.isZero_of_subsingleton _
  exact (hz.of_iso (actualFiniteProductCechHomologyPiIso F (n + 1))).of_iso
    (HomologicalComplex.homologyMapIso
      (finiteShiftedPolynomialCoordinateCechProductIso (K := K) (I := I) δ m) (n + 1))

/-- One genuine integer threshold works for every positive cohomological degree and later twist. -/
theorem finiteShiftedPolynomialCoordinateCech_homology_eventually_isZero :
    ∃ b : ℤ, ∀ m : ℤ, b ≤ m → ∀ n : ℕ,
      IsZero
        ((homogeneousCoordinateCechComplex (polynomialIntegralGrading (K := K) (I := I))
          (finiteShiftedFreePiece (polynomialIntegralGrading (K := K) (I := I)) δ)
          (fun i => (MvPolynomial.X i : MvPolynomial I K)) polynomialCoordinate_X_degree m).homology
            (n + 1)) := by
  classical
  let b : ℤ := Finset.univ.sup' (by simp : (Finset.univ : Finset (Option A)).Nonempty)
    (fun a => a.elim 0 δ)
  refine ⟨b, fun m hm n =>
    finiteShiftedPolynomialCoordinateCech_homology_isZero_of_shift_le δ m ?_ n⟩
  intro a
  exact le_trans (Finset.le_sup' (f := fun a : Option A => a.elim 0 δ)
    (Finset.mem_univ (some a))) hm

end ShiftedFree

end

end SGPT.Foundations.Schemes
