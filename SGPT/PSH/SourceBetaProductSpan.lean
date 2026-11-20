import SGPT.PSH.SemipositiveSquareDecomposition
import SGPT.Foundations.Analysis.Pending.NaturalRealPPPositiveSpanDictionary

/-! The REAL span of literal book decomposable beta products is EXACTLY the
usual pure (p,p) space, with an actual producer for every cone generator. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.ComplexCurrentDraft
open Finset
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open StronglyPositiveForms LocalProductCurrents TopDegreeDensity
open SGPT.PSH.BookCurrent

/-- Literal source testing products, with no replacement generating cone. -/
def sourceBetaSpan (n q : ℕ) : Submodule ℝ (RealForm n (2*q)) :=
  Submodule.span ℝ (Set.range (betaProduct (n := n) (q := q)))

theorem betaProduct_snoc {n q : ℕ} (bs : Fin q → ComplexModel n →L[ℂ] ℂ)
    (b : ComplexModel n →L[ℂ] ℂ) :
    betaProduct (Fin.snoc bs b) = coordinateWedge (betaProduct bs) (oneOneSquare b) := by
  simp only [betaProduct,wedgeProd_succ,Fin.snoc_castSucc,Fin.snoc_last]

/-- Actual exterior bilinearity produces the next literal source products. -/
theorem sourceBetaSpan_wedge_square {n q : ℕ} {P : RealForm n (2*q)}
    (hP : P ∈ sourceBetaSpan n q) (b : ComplexModel n →L[ℂ] ℂ) :
    coordinateWedge P (oneOneSquare b) ∈ sourceBetaSpan n (q+1) := by
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨bs,rfl⟩ := hx
    rw [← betaProduct_snoc]
    exact Submodule.subset_span ⟨Fin.snoc bs b,rfl⟩
  | zero =>
    rw [← wedgeBilin_apply,map_zero,LinearMap.zero_apply]
    exact (sourceBetaSpan n (q+1)).zero_mem
  | add x y _ _ hx hy =>
    rw [coordinateWedge_add_left]
    exact (sourceBetaSpan n (q+1)).add_mem hx hy
  | smul a x _ hx =>
    rw [coordinateWedge_smul_left]
    exact (sourceBetaSpan n (q+1)).smul_mem a hx

/-- The Gram decomposition is consumed to manufacture the genuine semipositive
wedge step, without a supplied square-span or output certificate. -/
theorem sourceBetaSpan_wedge_semipositive {n q : ℕ} {P : RealForm n (2*q)}
    (hP : P ∈ sourceBetaSpan n q) {B : RealForm n 2}
    (hB : IsSemipositiveOneOne B) :
    coordinateWedge P B ∈ sourceBetaSpan n (q+1) := by
  classical
  obtain ⟨bs,hbs⟩ := semipositive_exists_source_square_decomposition hB
  rw [hbs,← wedgeBilin_apply,map_smul,map_sum]
  apply (sourceBetaSpan n (q+1)).smul_mem
  apply (sourceBetaSpan n (q+1)).sum_mem
  intro l _
  exact sourceBetaSpan_wedge_square hP (bs l)

/-- Every actual positive cone tensor belongs to the real span of the EXACT
source decomposable products, all n and every q including q=0 and q>n. -/
theorem spCone_subset_sourceBetaSpan (n : ℕ) : ∀ q : ℕ,
    (spCone (n := n) q : Set (RealForm n (2*q))) ⊆
      (sourceBetaSpan n q : Set (RealForm n (2*q)))
  | 0 => by
    have hs : Submodule.span ℝ {coordinateWedgeUnit} ≤ sourceBetaSpan n 0 := by
      apply Submodule.span_le.mpr
      intro P hP
      rw [Set.mem_singleton_iff.mp hP]
      exact Submodule.subset_span ⟨isEmptyElim,rfl⟩
    intro P hP
    exact hs (PointedCone.hull_le_span ℝ {coordinateWedgeUnit} hP)
  | q+1 => by
    let G : Set (RealForm n (2*(q+1))) :=
      {R | ∃ P ∈ spCone (n := n) q, ∃ B : RealForm n 2,
        IsSemipositiveOneOne B ∧ R=coordinateWedge P B}
    have hs : Submodule.span ℝ G ≤ sourceBetaSpan n (q+1) := by
      apply Submodule.span_le.mpr
      intro R hR
      obtain ⟨P,hP,B,hB,rfl⟩ := hR
      exact sourceBetaSpan_wedge_semipositive (spCone_subset_sourceBetaSpan n q hP) hB
    intro R hR
    exact hs (PointedCone.hull_le_span ℝ G hR)

/-- PROVED actual equality with the established real pure-type constant space. -/
theorem sourceBetaSpan_eq_formSpan (n q : ℕ) : sourceBetaSpan n q = formSpan n q := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro P ⟨bs,rfl⟩
    exact betaProduct_mem_formSpan bs
  · exact Submodule.span_le.mpr (spCone_subset_sourceBetaSpan n q)

/-- Literal source products span the USUAL actual pure (q,q) tensors. -/
theorem mem_sourceBetaSpan_iff_actual_pure {n q : ℕ} (P : RealForm n (2*q)) :
    P ∈ sourceBetaSpan n q ↔
      NaturalRealAlternatingComplexification.IsPureRealPP q
        (P.toAlternatingMap.domDomCongr (finCongr (two_mul q))) := by
  rw [sourceBetaSpan_eq_formSpan]
  exact NaturalRealPPPositiveSpanDictionary.mem_formSpan_iff_pureRealPP P

end SGPT.PSH.ComplexCurrentDraft
