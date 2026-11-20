import SGPT.Unibranch.NativeNov16NormalSectionDivision
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphSheafCancellation

/-! Actual normal division manufactures genuine selector sections and full original clopen source pieces.
Blueprint: prime-nov16-analytic-normalization-original-selector-sections.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory Opposite
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSelectorSections

private theorem section_cancel {X : TopCat} (S : X.Sheaf CommRingCat) (W : Opens X)
    (Q : (S.presheaf.obj (op W)).carrier)
    (hd : ∀ x ∈ W,IsDomain (S.presheaf.stalk x).carrier)
    (hq : ∀ x (hx : x ∈ W),S.presheaf.germ W x hx Q ≠ 0)
    (a b : (S.presheaf.obj (op W)).carrier) (he : Q*a=Q*b) : a=b := by
  apply TopCat.Presheaf.section_ext S W a b
  intro x hx
  let := hd x hx
  apply mul_left_cancel₀ (hq x hx)
  simpa only [map_mul] using congrArg (S.presheaf.germ W x hx) he

theorem exists_actual_selector_sections {X : TopCat} (S : X.Sheaf CommRingCat)
    (W : Opens X) {k : ℕ} (Q : (S.presheaf.obj (op W)).carrier)
    (num : Fin k → (S.presheaf.obj (op W)).carrier)
    (hn : ∀ x ∈ W,IsDomain (S.presheaf.stalk x).carrier ∧ IsIntegrallyClosed (S.presheaf.stalk x).carrier)
    (hq : ∀ x (hx : x ∈ W),S.presheaf.germ W x hx Q ≠ 0)
    (hid : ∀ i,(num i)^2=Q*num i) (hsum : ∑ i,num i=Q)
    (horth : ∀ i j,i ≠ j → num i*num j=0) :
    ∃ e : Fin k → (S.presheaf.obj (op W)).carrier,
      (∀ i,num i=Q*e i) ∧ (∀ i,(e i)^2=e i) ∧ (∑ i,e i=1) ∧
      ∀ i j,i ≠ j → e i*e j=0 := by
  classical
  have he : ∀ i : Fin k,∃ ei : (S.presheaf.obj (op W)).carrier,num i=Q*ei := by
    intro i
    let c : Fin 2 → (S.presheaf.obj (op W)).carrier := fun j => if j.val=0 then 0 else -1
    have hrel : (num i)^2+∑ j : Fin 2,c j*Q^(2-j.val)*(num i)^j.val=0 := by
      simpa [c,Fin.sum_univ_two,sub_eq_add_neg] using sub_eq_zero.mpr (hid i)
    obtain ⟨ei,hei,_hunique⟩ := NativeNov16NormalSectionDivision.exists_unique_divisor_of_cleared_relation
      S W c (num i) Q hn hq hrel
    exact ⟨ei,hei⟩
  choose e heq using he
  have hc := section_cancel S W Q (fun x hx => (hn x hx).1) hq
  refine ⟨e,heq,?_,?_,?_⟩
  · intro i
    apply hc
    apply hc
    calc
      Q*(Q*(e i)^2)=(Q*e i)^2 := by ring
      _=(num i)^2 := by rw [← heq i]
      _=Q*num i := hid i
      _=Q*(Q*e i) := by rw [heq i]
  · apply hc
    calc
      Q*(∑ i,e i)=∑ i,Q*e i := Finset.mul_sum _ _ _
      _=∑ i,num i := Finset.sum_congr rfl fun i _ => (heq i).symm
      _=Q := hsum
      _=Q*1 := by rw [mul_one]
  · intro i j hij
    apply hc
    apply hc
    calc
      Q*(Q*(e i*e j))=(Q*e i)*(Q*e j) := by ring
      _=num i*num j := by rw [← heq i,← heq j]
      _=0 := horth i j hij
      _=Q*(Q*0) := by simp

open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceResidue
open HironakaActualAnalyticSubspaceLocalFunctions
open PrimeNov16AnalyticNormalizationGraphSheafCancellation

def original_value_hom {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (C : Set M) (W : Opens (TopCat.of C)) (p : W) :
    ((actualSubspaceSheaf (n := n) C).presheaf.obj (op W)).carrier →+* ℂ :=
  (actualSubspaceStalkEval (n := n) C p.val).comp
    ((actualSubspaceSheaf (n := n) C).presheaf.germ W p.val p.property).hom

theorem exists_actual_clopen_selector_cover {n k : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (C : Set M) (W : Opens (TopCat.of C))
    (e : Fin k → ((actualSubspaceSheaf (n := n) C).presheaf.obj (op W)).carrier)
    (hid : ∀ i,(e i)^2=e i) (hsum : ∑ i,e i=1)
    (horth : ∀ i j,i ≠ j → e i*e j=0) :
    ∃ V : Fin k → Opens (TopCat.of C),∃ hVW : ∀ i,V i ≤ W,
      (∀ i,IsClosed ((Subtype.val : W → C) ⁻¹' (V i : Set C))) ∧
      (∀ p : W,∃ i,p.val ∈ V i) ∧
      Pairwise (fun i j => Disjoint (V i : Set C) (V j : Set C)) ∧
      (∀ i,∀ p : W,p.val ∈ V i ↔ original_value_hom C W p (e i)=1) ∧
      ∀ i,(actualSubspaceSheaf (n := n) C).presheaf.map (homOfLE (hVW i)).op (e i)=1 := by
  classical
  let E : Fin k → W → ℂ := fun i p => original_value_hom C W p (e i)
  have hcont (i : Fin k) : Continuous (E i) := actual_section_values_continuous C W (e i)
  have hroot (i : Fin k) (p : W) : E i p=0 ∨ E i p=1 := by
    have he : (E i p)^2=E i p := by
      simpa only [map_pow] using congrArg (original_value_hom C W p) (hid i)
    have hp : E i p*(E i p-1)=0 := by
      calc
        E i p*(E i p-1)=(E i p)^2-E i p := by ring
        _=0 := sub_eq_zero.mpr he
    rcases mul_eq_zero.mp hp with h|h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  let R : Fin k → Set W := fun i => {p | E i p=1}
  have hRopen (i : Fin k) : IsOpen (R i) := by
    have he : R i=(E i) ⁻¹' ({0} : Set ℂ)ᶜ := by
      ext p
      change E i p=1 ↔ E i p ≠ 0
      constructor
      · intro h; rw [h]; exact one_ne_zero
      · intro h; exact (hroot i p).resolve_left h
    rw [he]
    exact isClosed_singleton.isOpen_compl.preimage (hcont i)
  have hRclosed (i : Fin k) : IsClosed (R i) := isClosed_eq (hcont i) continuous_const
  let V : Fin k → Opens (TopCat.of C) := fun i =>
    ⟨Subtype.val '' R i,W.isOpen.isOpenMap_subtype_val _ (hRopen i)⟩
  have hVW (i : Fin k) : V i ≤ W := by
    rintro p ⟨q,_hq,rfl⟩
    exact q.property
  have hmem (i : Fin k) (p : W) : p.val ∈ V i ↔ E i p=1 := by
    constructor
    · rintro ⟨q,hq,he⟩
      have hqp : q=p := Subtype.ext he
      exact hqp ▸ hq
    · intro hp
      exact ⟨p,hp,rfl⟩
  refine ⟨V,hVW,?_,?_,?_,hmem,?_⟩
  · intro i
    change IsClosed (Subtype.val ⁻¹' (Subtype.val '' R i))
    rw [Set.preimage_image_eq _ Subtype.val_injective]
    exact hRclosed i
  · intro p
    have hs : ∑ i,E i p=1 := by
      simpa only [map_sum,map_one] using congrArg (original_value_hom C W p) hsum
    have hex : ∃ i,E i p ≠ 0 := by
      by_contra hh
      push Not at hh
      have hz : (∑ i,E i p)=0 := Finset.sum_eq_zero fun i _ => hh i
      exact zero_ne_one (hz.symm.trans hs)
    obtain ⟨i,hi⟩ := hex
    exact ⟨i,(hmem i p).mpr ((hroot i p).resolve_left hi)⟩
  · intro i j hij
    apply disjoint_left.mpr
    rintro p ⟨u,hu,rfl⟩ ⟨v,hv,hvu⟩
    have hvu' : v=u := Subtype.ext hvu
    subst v
    have he : E i u*E j u=0 := by
      simpa only [map_mul,map_zero] using congrArg (original_value_hom C W u) (horth i j hij)
    rw [hu,hv,one_mul] at he
    exact one_ne_zero he
  · intro i
    apply actualSubspaceSection_ext_eval C (V i)
    intro p hp
    rw [(actualSubspaceSheaf (n := n) C).presheaf.germ_res_apply,map_one,map_one]
    exact (hmem i ⟨p,hVW i hp⟩).mp hp

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSelectorSections
