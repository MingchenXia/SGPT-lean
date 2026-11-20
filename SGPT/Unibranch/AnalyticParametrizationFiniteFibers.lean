import SGPT.Foundations.Analysis.Pending.GermParametrizationData
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Set.Finite.Range

/-! Actual monic-coordinate fibers, INCLUDING the discriminant.
Blueprint: analytic-parametrization-finite-fibers.tex. -/
set_option autoImplicit false
noncomputable section
open Set Polynomial
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.Pending.GermParametrizationData
namespace SGPT.Unibranch.AnalyticParametrization

/-- The actual monic coordinate equation has finitely many roots, without
simple-root, discriminant or positive-degree assumptions. -/
theorem monicEval_zeroSet_finite {E : Type*} (q : ℕ) (a : ℕ → E → ℂ) (x : E) :
    {t : ℂ | monicEval q a x t = 0}.Finite := by
  classical
  let p : ℂ[X] := X^q+∑ j : Fin q,C (a j x)*X^(j : ℕ)
  have hmonic : p.Monic := Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)
  have heval : monicEval q a x = fun t => p.eval t := by
    funext t
    simp [p,monicEval,Polynomial.eval_finsetSum,Finset.sum_range]
  have heq : {t : ℂ | monicEval q a x t = 0} = (p.roots.toFinset : Set ℂ) := by
    ext t
    simp [heval,Polynomial.mem_roots hmonic.ne_zero]
  rw [heq]
  exact Finset.finite_toSet _

/-- The ENTIRE actual coordinate projection fiber is finite, on ALL base
points including the discriminant, from the SAME actual monic relations. -/
theorem finite_fiber_of_monic_coordinates {n : ℕ} {A : Set (ComplexModel n)}
    (P : ParametrizationData A) (x : ComplexModel P.dim) :
    (A ∩ Metric.ball 0 P.rad ∩ coordinateProjection n P.dim ⁻¹' {x}).Finite := by
  classical
  let choices : Fin n → Set ℂ := fun i => if hi : i.val < P.dim
    then {x ⟨i.val,hi⟩} else {t | monicEval (P.s i) (P.e i) x t = 0}
  have hchoices : ∀ i,(choices i).Finite := by
    intro i
    by_cases hi : i.val < P.dim
    · simpa only [choices,dif_pos hi] using Set.finite_singleton (x ⟨i.val,hi⟩)
    · simpa only [choices,dif_neg hi] using monicEval_zeroSet_finite (P.s i) (P.e i) x
  let analyticParamCoordinateChoicesFintype (i : Fin n) : Fintype (choices i) := (hchoices i).fintype
  let G : (∀ i : Fin n,choices i) → ComplexModel n :=
    fun q => WithLp.toLp 2 (fun i => (q i).val)
  have hG : (range G).Finite := Set.finite_range G
  apply hG.subset
  intro z hz
  have hproj : coordinateProjection n P.dim z = x := hz.2
  have hcoord : ∀ i,z i ∈ choices i := by
    intro i
    by_cases hi : i.val < P.dim
    · change z i ∈ (if h : i.val < P.dim then {x ⟨i.val,h⟩} else _)
      rw [dif_pos hi]
      have h := congrArg (fun w : ComplexModel P.dim => w ⟨i.val,hi⟩) hproj
      change z i = x ⟨i.val,hi⟩
      simpa only [coordinateProjection_apply,dif_pos i.isLt] using h
    · change z i ∈ (if h : i.val < P.dim then _ else {t | monicEval (P.s i) (P.e i) x t = 0})
      rw [dif_neg hi]
      have h := P.e_eq_zero z hz.1.1 hz.1.2 i (Nat.le_of_not_gt hi)
      rwa [hproj] at h
  refine ⟨fun i => ⟨z i,hcoord i⟩,?_⟩
  apply WithLp.ofLp_injective 2
  funext i
  rfl

end SGPT.Unibranch.AnalyticParametrization
