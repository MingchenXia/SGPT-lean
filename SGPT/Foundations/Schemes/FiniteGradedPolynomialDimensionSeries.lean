import SGPT.Foundations.Schemes.PolynomialCoordinateDeletion
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.WellKnown

/-! # Actual dimension series of finite graded polynomial modules

The literal native degree dimensions define a rational-coefficient series.
Genuine coordinate exactness supplies its recurrence, including the boundary
coefficient. Empty coordinates give actual finite support.
-/

universe u

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section InheritedSupport

variable {K R M : Type u} [CommRing K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]
  (ℳ : ℤ → Submodule K M) (p : Submodule R M)

/-- A true homogeneous submodule piece inherits actual zero ambient degree. -/
theorem homogeneousSubmodulePiece_eq_bot_of_eq_bot (m : ℤ) (hm : ℳ m = ⊥) :
    homogeneousSubmodulePiece ℳ p m = ⊥ := by
  apply le_antisymm
  · intro v hv
    change (v : M) ∈ ℳ m at hv
    rw [hm] at hv
    change v = 0
    exact Subtype.ext hv
  · exact bot_le

/-- A true native quotient piece inherits actual zero ambient degree. -/
theorem homogeneousRingQuotientPiece_eq_bot_of_eq_bot (m : ℤ) (hm : ℳ m = ⊥) :
    homogeneousRingQuotientPiece ℳ p m = ⊥ := by
  rw [homogeneousRingQuotientPiece, hm, Submodule.map_bot]

end InheritedSupport

section ActualDimensions

variable {K M : Type u} [Field K] [AddCommGroup M] [Module K M]
  (ℳ : ℤ → Submodule K M)

/-- The literal true degree dimensions as a native rational-coefficient power series. -/
def actualGradedDimensionSeries (b : ℤ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (Module.finrank K (ℳ (b + (n : ℤ))) : ℚ))

/-- Each coefficient is exactly the actual native degree dimension. -/
theorem actualGradedDimensionSeries_coeff (b : ℤ) (n : ℕ) :
    PowerSeries.coeff n (actualGradedDimensionSeries ℳ b) =
      (Module.finrank K (ℳ (b + (n : ℤ))) : ℚ) := PowerSeries.coeff_mk _ _

end ActualDimensions

section CoordinateSeries

variable {K I M : Type u} [Field K] [hI : Fintype I]
  [AddCommGroup M] [Module K M] [Module (MvPolynomial I K) M]
  [hTower : IsScalarTower K (MvPolynomial I K) M]
  (ℳ : ℤ → Submodule K M) [hDecomp : DirectSum.Decomposition ℳ]
  [hGraded : SetLike.GradedSMul (polynomialIntegralGrading (K := K) (I := I)) ℳ]
  [hFinite : Module.Finite (MvPolynomial I K) M]

include hI hTower hDecomp hGraded hFinite

/-- Actual native coordinate exactness gives the real dimension-series recurrence, including its boundary. -/
theorem finiteGradedPolynomialDimensionSeries_coordinate_recurrence (i : I) (b : ℤ)
    (hb : ℳ (b - 1) = ⊥) :
    (1 - PowerSeries.X) * actualGradedDimensionSeries ℳ b =
      actualGradedDimensionSeries
        (homogeneousRingQuotientPiece ℳ
          (LinearMap.range (LinearMap.lsmul (MvPolynomial I K) M (MvPolynomial.X i)))) b -
      PowerSeries.X * actualGradedDimensionSeries
        (homogeneousSubmodulePiece ℳ
          (LinearMap.ker (LinearMap.lsmul (MvPolynomial I K) M (MvPolynomial.X i)))) b := by
  apply PowerSeries.ext
  intro n
  rw [sub_mul, one_mul, map_sub, map_sub]
  cases n with
  | zero =>
    simp only [PowerSeries.coeff_zero_X_mul, sub_zero, actualGradedDimensionSeries_coeff,
      Int.natCast_zero]
    have h := finiteGradedPolynomialCoordinate_finrank_recurrence ℳ i (b - 1)
    have he : 1 + (b - 1) = b := by omega
    have hU := homogeneousSubmodulePiece_eq_bot_of_eq_bot ℳ
      (LinearMap.ker (LinearMap.lsmul (MvPolynomial I K) M (MvPolynomial.X i))) (b - 1) hb
    rw [he, hb, hU, finrank_bot, finrank_bot, add_zero, zero_add] at h
    have hE0 := congrArg (fun m : ℤ => (Module.finrank K (ℳ m) : ℚ)) (add_zero b)
    have hV0 := congrArg (fun m : ℤ => (Module.finrank K
      (homogeneousRingQuotientPiece ℳ
        (LinearMap.range (LinearMap.lsmul (MvPolynomial I K) M (MvPolynomial.X i))) m) : ℚ))
      (add_zero b)
    exact hE0.trans ((congrArg (fun n : ℕ => (n : ℚ)) h).trans hV0.symm)
  | succ n =>
    simp only [PowerSeries.coeff_succ_X_mul, actualGradedDimensionSeries_coeff]
    have h := finiteGradedPolynomialCoordinate_finrank_recurrence ℳ i (b + (n : ℤ))
    have he : 1 + (b + (n : ℤ)) = b + ((n + 1 : ℕ) : ℤ) := by omega
    rw [he] at h
    have hQ := congrArg (fun a : ℕ => (a : ℚ)) h
    push_cast at hQ ⊢
    linarith

end CoordinateSeries

section EmptyPolynomialPieces

variable {K I J : Type u} [Field K] [IsEmpty I]

/-- With genuinely no variables, the actual polynomial grading is supported only in degree zero. -/
theorem polynomialIntegralGrading_eq_bot_of_isEmpty_of_ne_zero (m : ℤ) (hm : m ≠ 0) :
    polynomialIntegralGrading (K := K) (I := I) m = ⊥ := by
  apply le_antisymm
  · intro p hp
    change p = 0
    apply MvPolynomial.IsWeightedHomogeneous.eq_zero_of_no_monomials hp
    intro d hd
    have hd0 : d = 0 := Subsingleton.elim _ _
    rw [hd0, map_zero] at hd
    exact hm hd.symm
  · exact bot_le

/-- An actual zero-variable shifted coefficient degree vanishes off its genuine shifts. -/
theorem finiteShiftedPolynomialPiece_eq_bot_of_isEmpty_of_ne_shifts (δ : J → ℤ) (m : ℤ)
    (hm : ∀ j, m ≠ δ j) :
    finiteShiftedFreePiece (polynomialIntegralGrading (K := K) (I := I)) δ m = ⊥ := by
  apply le_antisymm
  · intro v hv
    change v = 0
    funext j
    have hj := hv j
    rw [polynomialIntegralGrading_eq_bot_of_isEmpty_of_ne_zero (m - δ j)
      (sub_ne_zero.mpr (hm j))] at hj
    exact hj
  · exact bot_le

end EmptyPolynomialPieces

section EmptyGradedModule

variable {K I M : Type u} [Field K] [hEmpty : IsEmpty I]
  [AddCommGroup M] [Module K M] [Module (MvPolynomial I K) M]
  [hTower : IsScalarTower K (MvPolynomial I K) M]
  (ℳ : ℤ → Submodule K M) [hDecomp : DirectSum.Decomposition ℳ]
  [hGraded : SetLike.GradedSMul (polynomialIntegralGrading (K := K) (I := I)) ℳ]
  [hFinite : Module.Finite (MvPolynomial I K) M]

include hEmpty hTower hDecomp hGraded hFinite

omit hTower in
/-- A genuine finite homogeneous cover gives actual upper support when there are no variables. -/
theorem finiteGradedPolynomialPiece_eventually_eq_bot_of_isEmpty :
    ∃ c : ℤ, ∀ m : ℤ, c < m → ℳ m = ⊥ := by
  classical
  obtain ⟨s, δ, hg, hs, _⟩ :=
    finiteShiftedGradedPresentation_exists (polynomialIntegralGrading (K := K) (I := I)) ℳ
  let c : ℤ := Finset.univ.sup' (by simp : (Finset.univ : Finset (Option s)).Nonempty)
    (fun j => j.elim 0 δ)
  refine ⟨c, fun m hm => ?_⟩
  have hfree := finiteShiftedPolynomialPiece_eq_bot_of_isEmpty_of_ne_shifts
    (K := K) (I := I) δ m (fun j => ne_of_gt (lt_of_le_of_lt
      (Finset.le_sup' (f := fun j : Option s => j.elim 0 δ) (Finset.mem_univ (some j))) hm))
  apply le_antisymm
  · intro v hv
    change v = 0
    obtain ⟨w, hw, hwv⟩ := homogeneousMap_surjectiveDegree
      (finiteShiftedFreePiece (polynomialIntegralGrading (K := K) (I := I)) δ) ℳ
      (finiteHomogeneousPresentationMap (R := MvPolynomial I K) (fun j : s => (j : M)))
      (finiteHomogeneousPresentationMap_homogeneous
        (polynomialIntegralGrading (K := K) (I := I)) ℳ δ _ hg) hs m v hv
    rw [hfree] at hw
    have hw0 : w = 0 := hw
    rw [hw0, map_zero] at hwv
    exact hwv.symm
  · exact bot_le

omit hTower in
/-- The actual dimension series of a true zero-variable finite graded module is a genuine polynomial. -/
theorem finiteGradedPolynomialDimensionSeries_eq_polynomial_of_isEmpty (b : ℤ) :
    ∃ P : Polynomial ℚ, actualGradedDimensionSeries ℳ b = (P : PowerSeries ℚ) := by
  obtain ⟨c, hc⟩ := finiteGradedPolynomialPiece_eventually_eq_bot_of_isEmpty (I := I) ℳ
  let N : ℕ := (c - b + 1).toNat
  refine ⟨PowerSeries.trunc N (actualGradedDimensionSeries ℳ b), ?_⟩
  apply PowerSeries.ext
  intro n
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  by_cases hn : n < N
  · rw [if_pos hn]
  · rw [if_neg hn, actualGradedDimensionSeries_coeff]
    have hz : ℳ (b + (n : ℤ)) = ⊥ := hc _ (by dsimp [N] at hn; omega)
    rw [hz, finrank_bot]
    rfl

end EmptyGradedModule

end

end SGPT.Foundations.Schemes
