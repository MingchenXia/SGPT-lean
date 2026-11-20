import SGPT.Foundations.Analysis.Pending.GermMinimalPolynomial

/-! Actual finite analytic calculus from ordinary coordinate monic relations.
Blueprint: prime-nov16-analytic-normalization-finite-calculus.tex. -/
set_option autoImplicit false
noncomputable section
open Polynomial
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HolGerm GermAlgebraicParametrization GermMinimalPolynomial
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationFiniteCalculus

theorem evalGerm_coordinate {d n k : ℕ} (hdk : d ≤ k) (hk : k < n)
    {W : (HolGerm (ComplexModel d))[X]} (hW : W.Monic) :
    evalGerm n W (coordGerm n k hk) =
      weierstrassGerm n k hk W.natDegree (fun j => projGerm k d (W.coeff j)) := by
  rw [evalGerm, eval₂_eq_sum_range, Finset.sum_range_succ, hW.coeff_natDegree,
    map_one, one_mul, weierstrassGerm]
  simp only [projGerm_projGerm hdk]
  exact add_comm _ _

/-- Ordinary monic relations manufacture actual distinguished coordinate
relations, including for nonprime ideals and noninjective base maps. -/
theorem hasWeierstrassPolynomial_of_monic {d n k : ℕ}
    (Q : Ideal (HolGerm (ComplexModel n))) (hdk : d ≤ k) (hk : k < n)
    {P : (HolGerm (ComplexModel d))[X]} (hP : P.Monic)
    (hmem : evalGerm n P (coordGerm n k hk) ∈ Q) :
    HasWeierstrassPolynomial Q k hk := by
  obtain ⟨W,V,hW,hW0,_hdeg,hPV,hV0⟩ := exists_eq_isWeierstrass_mul hP
  have hy : HolGerm.eval (coordGerm n k hk) = 0 := by
    simp [coordGerm, HolGerm.eval_mk]
  have hunit : IsUnit (evalGerm n V (coordGerm n k hk)) := by
    rw [isUnit_iff_eval_ne_zero, evalGerm, hom_eval₂, hy, eval₂_at_zero,
      RingHom.comp_apply, eval_projGerm]
    exact hV0
  have hWmem : evalGerm n W (coordGerm n k hk) ∈ Q := by
    rw [hPV, evalGerm, eval₂_mul] at hmem
    exact (Ideal.mul_unit_mem_iff_mem Q hunit).1 hmem
  refine ⟨W.natDegree,fun j => projGerm k d (W.coeff j),?_,?_⟩
  · intro j hj
    rw [eval_projGerm]
    exact hW0 j hj
  · rwa [← evalGerm_coordinate hdk hk hW]

/-- Genuine analytic division produces finiteness of the SAME actual germ
quotient; no desired finite algebra or stalk equivalence is supplied. -/
theorem quotientStructureMap_finite_of_monic {d n : ℕ} (hdn : d ≤ n)
    (Q : Ideal (HolGerm (ComplexModel n)))
    (hmonic : ∀ k (hk : k < n), d ≤ k →
      ∃ P : (HolGerm (ComplexModel d))[X], P.Monic ∧
        evalGerm n P (coordGerm n k hk) ∈ Q) :
    (quotientStructureMap Q d).Finite := by
  obtain ⟨N,m,hm⟩ := exists_finite_generators hdn Q (fun k hk hdk => by
    obtain ⟨P,hP,hmem⟩ := hmonic k hk hdk
    exact hasWeierstrassPolynomial_of_monic Q hdk hk hP hmem)
  exact quotientStructureMap_finite_of_generators hm

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationFiniteCalculus
