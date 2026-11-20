import SGPT.Projective.Sections
import Mathlib.Algebra.MvPolynomial.Polynomial

/-! Actual homogeneous dehomogenization in the original projective coordinates.
Kernel status and retained attempts are recorded separately in the owned check packets. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.BDivisor.ProjectiveCurveEscapeNext

open SGPT.Projective

/-- The actual substitution `Z₀ = 1`, retaining the other two original variables. -/
def actualDehomogenize0 :
    MvPolynomial (Fin 3) ℂ →+* MvPolynomial (Fin 2) ℂ :=
  (Polynomial.evalRingHom 1).comp (MvPolynomial.finSuccEquiv ℂ 2).toRingHom

theorem actualDehomogenize0_eval (P : MvPolynomial (Fin 3) ℂ) (z : Fin 2 → ℂ) :
    MvPolynomial.eval z (actualDehomogenize0 P) =
      MvPolynomial.eval (Fin.cons 1 z) P := by
  change MvPolynomial.eval z (Polynomial.eval 1 (MvPolynomial.finSuccEquiv ℂ 2 P)) = _
  have heq : (fun i : Fin 3 => Fin.cases (1 : ℂ) z i) = Fin.cons 1 z := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  have h := MvPolynomial.eval_polynomial_eval_finSuccEquiv (x := z) P 1
  simp only [map_one] at h
  rw [heq] at h
  exact h

/-- Dehomogenization at one is injective on each actual homogeneous degree. -/
theorem homogeneous_eq_zero_of_actualDehomogenize0_eq_zero
    {P : MvPolynomial (Fin 3) ℂ} {d : ℕ} (hP : P.IsHomogeneous d)
    (hD : actualDehomogenize0 P = 0) : P = 0 := by
  classical
  have hz (z : Fin 2 → ℂ) : MvPolynomial.eval (Fin.cons 1 z) P = 0 := by
    rw [← actualDehomogenize0_eval, hD, map_zero]
  apply MvPolynomial.funext
  intro v
  simp only [map_zero]
  let q : Polynomial ℂ :=
    Polynomial.map (MvPolynomial.eval (fun i : Fin 2 => v i.succ))
      (MvPolynomial.finSuccEquiv ℂ 2 P)
  have hqeval (t : ℂ) : q.eval t =
      MvPolynomial.eval (Fin.cons t (fun i : Fin 2 => v i.succ)) P := by
    exact (MvPolynomial.eval_eq_eval_mv_eval' (fun i : Fin 2 => v i.succ) t P).symm
  have hqt (t : ℂ) (ht : t ≠ 0) : q.eval t = 0 := by
    let u : Fin 3 → ℂ := Fin.cons 1 (fun i : Fin 2 => t⁻¹ * v i.succ)
    have hu : t • u = Fin.cons t (fun i : Fin 2 => v i.succ) := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [u]
      · simp [u, Pi.smul_apply, smul_eq_mul, ht]
    rw [hqeval, ← hu, ComplexProjectiveSpace.eval_smul_of_isHomogeneous hP]
    change t ^ d * MvPolynomial.eval (Fin.cons 1 (fun i : Fin 2 => t⁻¹ * v i.succ)) P = 0
    rw [hz, mul_zero]
  have hq0 : q = 0 := by
    apply Polynomial.eq_of_infinite_eval_eq q 0
    apply (Set.infinite_univ.sdiff (Set.finite_singleton (0 : ℂ))).mono
    intro t ht
    have ht0 : t ≠ 0 := by simpa only [Set.mem_singleton_iff] using ht.2
    change q.eval t = (0 : Polynomial ℂ).eval t
    simpa only [Polynomial.eval_zero] using hqt t ht0
  have hvcons : Fin.cons (v 0) (fun i : Fin 2 => v i.succ) = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  calc
    MvPolynomial.eval v P = q.eval (v 0) := by
      rw [hqeval, hvcons]
    _ = 0 := by simp only [hq0, Polynomial.eval_zero]

theorem actualDehomogenize0_ne_zero
    {P : MvPolynomial (Fin 3) ℂ} {d : ℕ} (hP : P.IsHomogeneous d) (hP0 : P ≠ 0) :
    actualDehomogenize0 P ≠ 0 :=
  fun h => hP0 (homogeneous_eq_zero_of_actualDehomogenize0_eq_zero hP h)

/-- Encode the first variable as the inner `X`, the second as the outer `Y`. -/
def actualBivariateEncode :
    MvPolynomial (Fin 2) ℂ →+* Polynomial (Polynomial ℂ) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp (Polynomial.C : ℂ →+* Polynomial ℂ))
    ![Polynomial.C Polynomial.X, Polynomial.X]

/-- The actual reverse polynomial substitution, used to prove injectivity. -/
def actualBivariateDecode :
    Polynomial (Polynomial ℂ) →+* MvPolynomial (Fin 2) ℂ :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)) (MvPolynomial.X 1)

theorem actualBivariateDecode_encode (P : MvPolynomial (Fin 2) ℂ) :
    actualBivariateDecode (actualBivariateEncode P) = P := by
  have hcomp : actualBivariateDecode.comp actualBivariateEncode = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [actualBivariateDecode, actualBivariateEncode]
    · intro i
      fin_cases i <;> simp [actualBivariateDecode, actualBivariateEncode]
  exact DFunLike.congr_fun hcomp P

theorem actualBivariateEncode_injective : Function.Injective actualBivariateEncode :=
  Function.LeftInverse.injective actualBivariateDecode_encode

theorem actualBivariateEncode_eval (P : MvPolynomial (Fin 2) ℂ) (x y : ℂ) :
    (actualBivariateEncode P).eval₂ (Polynomial.evalRingHom x) y =
      MvPolynomial.eval ![x, y] P := by
  have hcomp :
      (Polynomial.eval₂RingHom (Polynomial.evalRingHom x) y).comp actualBivariateEncode =
        MvPolynomial.eval ![x, y] := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [actualBivariateEncode]
    · intro i
      fin_cases i <;> simp [actualBivariateEncode]
  exact DFunLike.congr_fun hcomp P

theorem actualBivariateEncode_dehomogenize_ne_zero
    {P : MvPolynomial (Fin 3) ℂ} {d : ℕ} (hP : P.IsHomogeneous d) (hP0 : P ≠ 0) :
    actualBivariateEncode (actualDehomogenize0 P) ≠ 0 := by
  intro h
  apply actualDehomogenize0_ne_zero hP hP0
  apply actualBivariateEncode_injective
  simpa only [map_zero] using h

end SGPT.BDivisor.ProjectiveCurveEscapeNext
