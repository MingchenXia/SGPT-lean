import SGPT.Unibranch.PrimeNov16AnalyticNormalizationFiniteCalculus

/-! Actual polynomial surjectivity for analytic germ quotients from monic
coordinate relations, not from a supplied finite analytic mapping theorem.
Blueprint: prime-nov16-analytic-normalization-polynomial-calculus.tex. -/
set_option autoImplicit false
noncomputable section
open Polynomial
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HolGerm GermAlgebraicParametrization GermMinimalPolynomial
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationPolynomialCalculus

theorem exists_distinguished_relation {d n : ℕ}
    (Q : Ideal (HolGerm (ComplexModel n)))
    (y : HolGerm (ComplexModel n)) (hy : HolGerm.eval y = 0)
    {P : (HolGerm (ComplexModel d))[X]} (hP : P.Monic)
    (hmem : evalGerm n P y ∈ Q) :
    ∃ W : (HolGerm (ComplexModel d))[X], IsWeierstrass W ∧ evalGerm n W y ∈ Q := by
  obtain ⟨W,V,hW,hW0,_hdeg,hPV,hV0⟩ := exists_eq_isWeierstrass_mul hP
  have hunit : IsUnit (evalGerm n V y) := by
    rw [isUnit_iff_eval_ne_zero, evalGerm, hom_eval₂, hy, eval₂_at_zero,
      RingHom.comp_apply, eval_projGerm]
    exact hV0
  refine ⟨W,⟨hW,hW0⟩,?_⟩
  rw [hPV, evalGerm, eval₂_mul] at hmem
  exact (Ideal.mul_unit_mem_iff_mem Q hunit).1 hmem

/-- EVERY actual germ admits polynomial readback using ONLY fibre variables. -/
theorem every_germ_polynomial_modulo {d n : ℕ} (hdn : d ≤ n)
    (Q : Ideal (HolGerm (ComplexModel n)))
    (hmonic : ∀ k (hk : k < n), d ≤ k →
      ∃ P : (HolGerm (ComplexModel d))[X], P.Monic ∧
        evalGerm n P (coordGerm n k hk) ∈ Q)
    (g : HolGerm (ComplexModel n)) :
    ∃ R : MvPolynomial (Fin n) (HolGerm (ComplexModel d)),
      (∀ m ∈ R.support, ∀ i : Fin n, i.val < d → m i = 0) ∧
      g - MvPolynomial.eval₂ (projGerm n d) coord R ∈ Q := by
  classical
  have hfamily : ∀ k : Fin n, ∃ W : (HolGerm (ComplexModel d))[X],
      d ≤ k.val → IsWeierstrass W ∧ evalGerm n W (coord k) ∈ Q := by
    intro k
    by_cases hdk : d ≤ k.val
    · obtain ⟨P,hP,hmem⟩ := hmonic k.val k.isLt hdk
      obtain ⟨W,hW,hWmem⟩ := exists_distinguished_relation Q (coord k)
        (by simp [coord,coordGerm,HolGerm.eval_mk]) hP hmem
      exact ⟨W,fun _ => ⟨hW,hWmem⟩⟩
    · exact ⟨X,fun h => (hdk h).elim⟩
  choose W hW using hfamily
  obtain ⟨R,q,hR,hg⟩ := exists_reduce hdn W (fun k hk => (hW k hk).1) g
  refine ⟨R,hR,?_⟩
  rw [hg,add_sub_cancel_left]
  apply Q.sum_mem
  intro k _hk
  split_ifs with hdk
  · exact Q.mul_mem_left _ (hW k hdk).2
  · exact Q.zero_mem

/-- Literal surjectivity onto the actual analytic quotient. -/
theorem polynomial_evaluation_surjective {d n : ℕ} (hdn : d ≤ n)
    (Q : Ideal (HolGerm (ComplexModel n)))
    (hmonic : ∀ k (hk : k < n), d ≤ k →
      ∃ P : (HolGerm (ComplexModel d))[X], P.Monic ∧
        evalGerm n P (coordGerm n k hk) ∈ Q) :
    Function.Surjective (fun R : MvPolynomial (Fin n) (HolGerm (ComplexModel d)) =>
      Ideal.Quotient.mk Q (MvPolynomial.eval₂ (projGerm n d) coord R)) := by
  intro x
  obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨R,_hR,hg⟩ := every_germ_polynomial_modulo hdn Q hmonic g
  exact ⟨R,(Ideal.Quotient.eq.mpr hg).symm⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationPolynomialCalculus
