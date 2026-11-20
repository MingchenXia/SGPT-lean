import SGPT.Foundations.Schemes.HomogeneousScalarKernelQuotient
import Mathlib.Algebra.MvPolynomial.Rename

/-! # Genuine deletion of a killed polynomial coordinate

The actual smaller-ring action is restriction along coordinate inclusion.
Polynomial evaluation on the complement shows that true finite generators
still span after a coordinate which acts as zero is removed.
-/

universe u

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section FactoredScalars

variable {R S N : Type u} [CommRing R] [CommRing S] [AddCommGroup N]
  [Module R N] [Module S N]

/-- True finite generators remain finite when each scalar action comes from the smaller ring. -/
theorem moduleFinite_of_factored_scalar_action [Module.Finite S N]
    (h : ∀ s : S, ∃ r : R, ∀ v : N, s • v = r • v) : Module.Finite R N := by
  classical
  obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule S N).FG)
  refine ⟨t, le_antisymm le_top ?_⟩
  intro v _hv
  have hv : v ∈ Submodule.span S (t : Set N) := ht ▸ Submodule.mem_top
  clear _hv
  induction hv using Submodule.span_induction with
  | mem v hv => exact Submodule.subset_span hv
  | zero => exact Submodule.zero_mem _
  | add v w _ _ hv hw => exact Submodule.add_mem _ hv hw
  | smul s v _ hv =>
    obtain ⟨r, hr⟩ := h s
    rw [hr v]
    exact Submodule.smul_mem _ r hv

end FactoredScalars

section PolynomialActions

variable {K I J N : Type u} [CommRing K] [AddCommGroup N]
  [Module (MvPolynomial I K) N]

/-- Genuine complement evaluation has the same action when the omitted coordinates kill the module. -/
theorem polynomialRenameKillCompl_smul (f : J → I) (hf : Function.Injective f)
    (hk : ∀ i : I, i ∉ Set.range f → ∀ v : N, (MvPolynomial.X i : MvPolynomial I K) • v = 0)
    (p : MvPolynomial I K) (v : N) :
    p • v = MvPolynomial.rename f (MvPolynomial.killCompl hf p) • v := by
  classical
  induction p using MvPolynomial.induction_on generalizing v with
  | C c => rw [MvPolynomial.killCompl_C, MvPolynomial.rename_C]
  | add p q hp hq => simp only [map_add, add_smul, hp, hq]
  | mul_X p i hp =>
    by_cases hi : i ∈ Set.range f
    · obtain ⟨j, rfl⟩ := hi
      have hX : MvPolynomial.rename f (MvPolynomial.killCompl hf
          (MvPolynomial.X (f j) : MvPolynomial I K)) = MvPolynomial.X (f j) := by
        rw [show (MvPolynomial.X (f j) : MvPolynomial I K) =
          MvPolynomial.rename f (MvPolynomial.X j) from (MvPolynomial.rename_X f j).symm,
          MvPolynomial.killCompl_rename_app]
      simp only [map_mul, mul_smul, hX, hp]
    · have hX : MvPolynomial.killCompl hf (MvPolynomial.X i : MvPolynomial I K) = 0 := by
        rw [MvPolynomial.killCompl, MvPolynomial.aeval_X, dif_neg hi]
      simp only [map_mul, hX, mul_zero, map_zero, zero_smul, mul_smul, hk i hi v, smul_zero]

variable (K I N)

/-- The true smaller polynomial ring acts through literal inclusion of all remaining coordinates. -/
@[instance_reducible]
def polynomialDeletedCoordinateModule (i : I) : Module (MvPolynomial {j : I // j ≠ i} K) N :=
  Module.compHom N (MvPolynomial.rename (fun j : {j : I // j ≠ i} => (j : I))).toRingHom

variable {K I N}

/-- An actual killed coordinate transfers true finite generators to the actual smaller-ring action. -/
theorem polynomialKilledCoordinate_finite (i : I) [Module.Finite (MvPolynomial I K) N]
    (hx : ∀ v : N, (MvPolynomial.X i : MvPolynomial I K) • v = 0) :
    letI := polynomialDeletedCoordinateModule K I N i
    Module.Finite (MvPolynomial {j : I // j ≠ i} K) N := by
  let := polynomialDeletedCoordinateModule K I N i
  apply moduleFinite_of_factored_scalar_action (S := MvPolynomial I K)
  intro p
  refine ⟨MvPolynomial.killCompl (fun a b h => Subtype.ext h) p, fun v => ?_⟩
  change p • v = MvPolynomial.rename (fun j : {j : I // j ≠ i} => (j : I))
    (MvPolynomial.killCompl (fun a b h => Subtype.ext h) p) • v
  apply polynomialRenameKillCompl_smul
  intro j hj w
  have hji : j = i := by
    by_contra hji
    exact hj ⟨⟨j, hji⟩, rfl⟩
  subst j
  exact hx w

end PolynomialActions

section DeletedCoordinateGrading

variable {K I J N : Type u} [Field K]

/-- Literal coordinate renaming preserves the actual integral polynomial degree. -/
theorem polynomialIntegralGrading_rename (f : J → I) (m : ℤ) (p : MvPolynomial J K)
    (hp : p ∈ polynomialIntegralGrading (K := K) (I := J) m) :
    MvPolynomial.rename f p ∈ polynomialIntegralGrading (K := K) (I := I) m := by
  by_cases hm : 0 ≤ m
  · have he : m = (m.toNat : ℤ) := (Int.toNat_of_nonneg hm).symm
    rw [he, polynomialIntegralGrading_nat_eq] at hp ⊢
    exact hp.rename_isHomogeneous (f := f)
  · have hp0 : p = 0 := by
      rw [polynomialIntegralGrading_eq_bot_of_neg m (lt_of_not_ge hm)] at hp
      exact hp
    rw [hp0, map_zero]
    exact Submodule.zero_mem _

variable [AddCommGroup N] [Module K N] [Module (MvPolynomial I K) N]
  (ℳ : ℤ → Submodule K N)
  [hGraded : SetLike.GradedSMul (polynomialIntegralGrading (K := K) (I := I)) ℳ]

include hGraded in
/-- The genuine original graded action restricts to the actual smaller polynomial ring. -/
theorem polynomialDeletedCoordinateGradedSMul (i : I) :
    letI := polynomialDeletedCoordinateModule K I N i
    SetLike.GradedSMul (polynomialIntegralGrading (K := K) (I := {j : I // j ≠ i})) ℳ := by
  let := polynomialDeletedCoordinateModule K I N i
  refine ⟨?_⟩
  intro a m p v hp hv
  change MvPolynomial.rename (fun j : {j : I // j ≠ i} => (j : I)) p • v ∈ ℳ (a +ᵥ m)
  exact SetLike.GradedSMul.smul_mem (polynomialIntegralGrading_rename _ a p hp) hv

omit hGraded in
/-- The actual restricted smaller-ring action retains the true structural field scalar tower. -/
theorem polynomialDeletedCoordinateScalarTower [hTower : IsScalarTower K (MvPolynomial I K) N]
    (i : I) :
    letI := polynomialDeletedCoordinateModule K I N i
    IsScalarTower K (MvPolynomial {j : I // j ≠ i} K) N := by
  let := polynomialDeletedCoordinateModule K I N i
  apply IsScalarTower.of_algebraMap_smul
  intro c v
  change MvPolynomial.rename (fun j : {j : I // j ≠ i} => (j : I)) (MvPolynomial.C c) • v = c • v
  rw [MvPolynomial.rename_C]
  exact IsScalarTower.algebraMap_smul (R := K) (A := MvPolynomial I K) c v

end DeletedCoordinateGrading

section ActualCoordinateKernelQuotient

variable {K I M : Type u} [Field K] [Fintype I]
  [AddCommGroup M] [Module (MvPolynomial I K) M]

/-- The genuine coordinate annihilator is finite over the literal smaller coordinate ring. -/
theorem polynomialCoordinateKernelDeleted_finite (i : I) [Module.Finite (MvPolynomial I K) M] :
    letI := polynomialDeletedCoordinateModule K I
      (LinearMap.ker (LinearMap.lsmul (MvPolynomial I K) M (MvPolynomial.X i))) i
    Module.Finite (MvPolynomial {j : I // j ≠ i} K)
      (LinearMap.ker (LinearMap.lsmul (MvPolynomial I K) M (MvPolynomial.X i))) := by
  let := scalarKernel_finite (M := M) (MvPolynomial.X i : MvPolynomial I K)
  exact polynomialKilledCoordinate_finite i (scalarKernel_smul_eq_zero (M := M) (MvPolynomial.X i))

omit [Fintype I] in
/-- The genuine coordinate-image quotient is finite over the literal smaller coordinate ring. -/
theorem polynomialCoordinateQuotientDeleted_finite (i : I) [Module.Finite (MvPolynomial I K) M] :
    letI := polynomialDeletedCoordinateModule K I
      (M ⧸ LinearMap.range (LinearMap.lsmul (MvPolynomial I K) M (MvPolynomial.X i))) i
    Module.Finite (MvPolynomial {j : I // j ≠ i} K)
      (M ⧸ LinearMap.range (LinearMap.lsmul (MvPolynomial I K) M (MvPolynomial.X i))) := by
  let := scalarQuotient_finite (M := M) (MvPolynomial.X i : MvPolynomial I K)
  exact polynomialKilledCoordinate_finite i (scalarQuotient_smul_eq_zero (M := M) (MvPolynomial.X i))

end ActualCoordinateKernelQuotient

section ActualDeletedCoordinateGradings

variable {K I M : Type u} [Field K] [AddCommGroup M]
  [Module K M] [Module (MvPolynomial I K) M] [IsScalarTower K (MvPolynomial I K) M]
  (ℳ : ℤ → Submodule K M)
  [hGraded : SetLike.GradedSMul (polynomialIntegralGrading (K := K) (I := I)) ℳ]

include hGraded

/-- The actual annihilator's native degree pieces have the genuine smaller-coordinate graded action. -/
theorem polynomialCoordinateKernelDeletedGradedSMul (i : I) :
    letI := polynomialDeletedCoordinateModule K I
      (LinearMap.ker (LinearMap.lsmul (MvPolynomial I K) M (MvPolynomial.X i))) i
    SetLike.GradedSMul (polynomialIntegralGrading (K := K) (I := {j : I // j ≠ i}))
      (homogeneousSubmodulePiece ℳ
        (LinearMap.ker (LinearMap.lsmul (MvPolynomial I K) M (MvPolynomial.X i)))) :=
  polynomialDeletedCoordinateGradedSMul
    (homogeneousSubmodulePiece ℳ
      (LinearMap.ker (LinearMap.lsmul (MvPolynomial I K) M (MvPolynomial.X i)))) i

/-- The actual native quotient's degree pieces have the genuine smaller-coordinate graded action. -/
theorem polynomialCoordinateQuotientDeletedGradedSMul (i : I) :
    letI := polynomialDeletedCoordinateModule K I
      (M ⧸ LinearMap.range (LinearMap.lsmul (MvPolynomial I K) M (MvPolynomial.X i))) i
    SetLike.GradedSMul (polynomialIntegralGrading (K := K) (I := {j : I // j ≠ i}))
      (homogeneousRingQuotientPiece ℳ
        (LinearMap.range (LinearMap.lsmul (MvPolynomial I K) M (MvPolynomial.X i)))) :=
  polynomialDeletedCoordinateGradedSMul
    (homogeneousRingQuotientPiece ℳ
      (LinearMap.range (LinearMap.lsmul (MvPolynomial I K) M (MvPolynomial.X i)))) i

end ActualDeletedCoordinateGradings

end

end SGPT.Foundations.Schemes
