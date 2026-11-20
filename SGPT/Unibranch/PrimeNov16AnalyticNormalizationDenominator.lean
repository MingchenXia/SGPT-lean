import SGPT.Unibranch.PrimeNov16AnalyticIntegralClosure
import Mathlib.RingTheory.Localization.Integer

/-! Actual common denominator for the canonical normal analytic branch algebra.
No finite-algebra or desired denominator certificate is supplied.
Blueprint: prime-nov16-analytic-normalization-denominator.tex. -/
set_option autoImplicit false
noncomputable section
open scoped nonZeroDivisors
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationDenominator

/-- An actual finite submodule of the actual fraction ring has one denominator
clearing ALL of its elements, not just a provided tuple. -/
theorem exists_universal_denominator_of_finite_closure
    (A : Type*) [CommRing A] [IsDomain A]
    [Module.Finite A (integralClosure A (FractionRing A))] :
    ∃ h : A, h ≠ 0 ∧ ∀ x : integralClosure A (FractionRing A),
      ∃ a : A, algebraMap A (FractionRing A) a =
        algebraMap A (FractionRing A) h * (x : FractionRing A) := by
  classical
  let B := integralClosure A (FractionRing A)
  obtain ⟨N,s,hs⟩ := Module.Finite.exists_fin (R := A) (M := B)
  obtain ⟨h,hh⟩ := IsLocalization.exist_integer_multiples_of_finite A⁰
    (fun i : Fin N => (s i : FractionRing A))
  let S : Submodule A B := {
    carrier := fun x => IsLocalization.IsInteger A ((h : A) • (x : FractionRing A))
    zero_mem' := by
      change IsLocalization.IsInteger A ((h : A) • (0 : FractionRing A))
      simpa using (IsLocalization.isInteger_zero (R := A) (S := FractionRing A))
    add_mem' := by
      intro x y hx hy
      change IsLocalization.IsInteger A ((h : A) • ((x : FractionRing A) + (y : FractionRing A)))
      rw [smul_add]
      exact IsLocalization.isInteger_add hx hy
    smul_mem' := by
      intro a x hx
      change IsLocalization.IsInteger A ((h : A) • (a • (x : FractionRing A)))
      rw [smul_comm]
      exact IsLocalization.isInteger_smul hx }
  have hspan : Submodule.span A (Set.range s) ≤ S := by
    apply Submodule.span_le.mpr
    rintro x ⟨i,rfl⟩
    exact hh i
  rw [hs] at hspan
  refine ⟨h,nonZeroDivisors.ne_zero h.property,?_⟩
  intro x
  have hx := hspan (show x ∈ (⊤ : Submodule A B) from trivial)
  obtain ⟨a,ha⟩ := hx
  exact ⟨a,by simpa only [Algebra.smul_def] using ha⟩

/-- Original analytic prime input alone internally manufactures a nonzero
universal denominator for its SAME canonical integral-closure algebra. -/
theorem exists_analytic_germ_universal_denominator {n : ℕ}
    (P : Ideal (HolGerm (ComplexModel n))) [P.IsPrime] :
    ∃ h : HolGerm (ComplexModel n) ⧸ P, h ≠ 0 ∧
      ∀ x : integralClosure (HolGerm (ComplexModel n) ⧸ P)
          (FractionRing (HolGerm (ComplexModel n) ⧸ P)),
        ∃ a : HolGerm (ComplexModel n) ⧸ P,
          algebraMap _ (FractionRing (HolGerm (ComplexModel n) ⧸ P)) a =
            algebraMap _ (FractionRing (HolGerm (ComplexModel n) ⧸ P)) h *
              (x : FractionRing (HolGerm (ComplexModel n) ⧸ P)) := by
  have := PrimeNov16AnalyticIntegralClosure.finite_analytic_germ_integralClosure P
  exact exists_universal_denominator_of_finite_closure _

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationDenominator
