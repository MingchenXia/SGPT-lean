import SGPT.Foundations.Analysis.Pending.NaturalPurePPPositiveSpanInclusion
import SGPT.Foundations.Analysis.Pending.NaturalComplexPureExteriorPreservation

/-!
# The actual usual real pure (p,p) space equals original formSpan

Pure type is the genuine all-subset condition on the constructed unique
complexification. The original cone recursion is proved to preserve that
condition. Combined with the full pure-to-span theorem, this gives both
true pointwise inclusions in every dimension and degree. No global Green,
closed-range or Bott--Chern theorem is asserted.
-/

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.NaturalRealPPPositiveSpanDictionary

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open NaturalComplexBidegreeTransport NaturalRealAlternatingComplexification
open NaturalComplexifiedRealSpan NaturalComplexPureExteriorPreservation
open NaturalPurePPPositiveSpanInclusion NaturalRealPPSubmodule
open NaturalComplexExteriorProductTransport

def realPureSpace (n p : ℕ) : Submodule ℝ (StronglyPositiveForms.RealForm n (2 * p)) :=
  ((pureEigenblockSpace n (2 * p) p).restrictScalars ℝ).comap (realExtension n (2 * p))

theorem mem_realPureSpace_iff_pureRealPP {n p : ℕ}
    (A : StronglyPositiveForms.RealForm n (2 * p)) :
    A ∈ realPureSpace n p ↔
      IsPureRealPP p (A.toAlternatingMap.domDomCongr (finCongr (two_mul p))) := by
  change realExtension n (2 * p) A ∈ pureEigenblockSpace n (2 * p) p ↔ _
  unfold IsPureRealPP
  rw [complexify_domDomCongr]
  let e : Fin (2 * p) ≃ Fin (p + p) := finCongr (two_mul p)
  constructor
  · intro hA
    exact (mem_pureEigenblockSpace_iff_bidegree _).mp
      (domDomCongr_mem_pureEigenblockSpace _ hA e)
  · intro hA
    have ht := domDomCongr_mem_pureEigenblockSpace _
      ((mem_pureEigenblockSpace_iff_bidegree _).mpr hA) e.symm
    have he : ((realExtension n (2 * p) A).domDomCongr e).domDomCongr e.symm =
        realExtension n (2 * p) A := by
      ext v
      simp [AlternatingMap.domDomCongr_apply, Function.comp_def]
    change ((realExtension n (2 * p) A).domDomCongr e).domDomCongr e.symm ∈
      pureEigenblockSpace n (2 * p) p at ht
    rw [he] at ht
    exact ht

theorem unit_mem_realPureSpace (n : ℕ) :
    (coordinateWedgeUnit : StronglyPositiveForms.RealForm n 0) ∈ realPureSpace n 0 := by
  change realExtension n 0 coordinateWedgeUnit ∈ pureEigenblockSpace n 0 0
  intro S hS v hp hm
  have hS₀ : S = ∅ := Subsingleton.elim _ _
  exact False.elim (hS (by rw [hS₀]; rfl))

theorem coordinateWedge_mem_realPureSpace {n p : ℕ}
    (A : StronglyPositiveForms.RealForm n (2 * p)) (hA : A ∈ realPureSpace n p)
    (β : StronglyPositiveForms.RealForm n 2) (hβ : IsOneOne β) :
    coordinateWedge A β ∈ realPureSpace n (p + 1) := by
  have ht : IsPureBidegree 1 1 (realExtension n 2 β) :=
    (isOneOne_iff_pureRealPP β).mp hβ
  have hb : realExtension n 2 β ∈ pureEigenblockSpace n 2 1 :=
    (mem_pureEigenblockSpace_iff_bidegree _).mpr ht
  change complexify (coordinateWedge A β).toAlternatingMap ∈
    pureEigenblockSpace n (2 * p + 2) (p + 1)
  rw [complexify_coordinateWedge]
  exact complexWedge_mem_pureEigenblockSpace _ _ hA hb

theorem spCone_le_realPureSpace (n : ℕ) : ∀ p : ℕ,
    (StronglyPositiveForms.spCone (n := n) p : Set (StronglyPositiveForms.RealForm n (2 * p))) ⊆
      (realPureSpace n p : Set (StronglyPositiveForms.RealForm n (2 * p)))
  | 0 => by
    have hs : Submodule.span ℝ {coordinateWedgeUnit} ≤ realPureSpace n 0 := by
      apply Submodule.span_le.mpr
      intro A hA
      have h : A = coordinateWedgeUnit := Set.mem_singleton_iff.mp hA
      rw [h]
      exact unit_mem_realPureSpace n
    intro A hA
    exact hs (PointedCone.hull_le_span ℝ {coordinateWedgeUnit} hA)
  | p + 1 => by
    let G : Set (StronglyPositiveForms.RealForm n (2 * (p + 1))) :=
      {R | ∃ A ∈ StronglyPositiveForms.spCone (n := n) p,
        ∃ β : StronglyPositiveForms.RealForm n 2,
          StronglyPositiveForms.IsSemipositiveOneOne β ∧ R = coordinateWedge A β}
    have hs : Submodule.span ℝ G ≤ realPureSpace n (p + 1) := by
      apply Submodule.span_le.mpr
      intro R hR
      obtain ⟨A, hA, β, hβ, rfl⟩ := hR
      exact coordinateWedge_mem_realPureSpace A (spCone_le_realPureSpace n p hA) β hβ.1
    intro R hR
    exact hs (PointedCone.hull_le_span ℝ G hR)

theorem formSpan_eq_realPureSpace (n p : ℕ) :
    LocalProductCurrents.formSpan n p = realPureSpace n p := by
  apply le_antisymm
  · change Submodule.span ℝ (StronglyPositiveForms.spCone (n := n) p : Set (StronglyPositiveForms.RealForm n (2 * p))) ≤ realPureSpace n p
    exact Submodule.span_le.mpr (spCone_le_realPureSpace n p)
  · intro A hA
    exact formSpan_mem_of_pureRealPP A ((mem_realPureSpace_iff_pureRealPP A).mp hA)

theorem mem_formSpan_iff_pureRealPP {n p : ℕ}
    (A : StronglyPositiveForms.RealForm n (2 * p)) :
    A ∈ LocalProductCurrents.formSpan n p ↔
      IsPureRealPP p (A.toAlternatingMap.domDomCongr (finCongr (two_mul p))) := by
  rw [formSpan_eq_realPureSpace]
  exact mem_realPureSpace_iff_pureRealPP A

end SGPT.Foundations.Analysis.Pending.NaturalRealPPPositiveSpanDictionary
