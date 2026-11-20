import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSelectorSections
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSectionDensity

/-! Genuine selector sections internally manufacture full closed-component landing on entire original clopen pieces.
Blueprint: prime-nov16-analytic-normalization-original-selector-landing.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory Opposite
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSelectorLanding
open HironakaActualAnalyticSubspace
open PrimeNov16AnalyticNormalizationOriginalSelectorSections
open PrimeNov16AnalyticNormalizationOriginalSectionDensity

theorem exists_actual_selector_landing_cover {n k : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (C : Set M) (W : Opens (TopCat.of C)) {T : Type} [TopologicalSpace T]
    (f : W → T) (hf : Continuous f) (B : Fin k → Set T) (hB : ∀ i,IsClosed (B i))
    (hcover : ∀ p : W,∃ i,f p ∈ B i) (num : Fin k → T → ℂ)
    (hvan : ∀ i j,i ≠ j → ∀ x ∈ B j,num i x=0)
    (Q : ((actualSubspaceSheaf (n := n) C).presheaf.obj (op W)).carrier)
    (e : Fin k → ((actualSubspaceSheaf (n := n) C).presheaf.obj (op W)).carrier)
    (hq : ∀ p : C,∀ hp : p ∈ W,(actualSubspaceSheaf (n := n) C).presheaf.germ W p hp Q ≠ 0)
    (hid : ∀ i,(e i)^2=e i) (hsum : ∑ i,e i=1)
    (horth : ∀ i j,i ≠ j → e i*e j=0)
    (hrel : ∀ i,∀ p : W,original_value_hom C W p Q*original_value_hom C W p (e i)=num i (f p)) :
    ∃ V : Fin k → Opens (TopCat.of C),∃ hVW : ∀ i,V i ≤ W,
      (∀ i,IsClosed ((Subtype.val : W → C) ⁻¹' (V i : Set C))) ∧
      (∀ p : W,∃ i,p.val ∈ V i) ∧
      Pairwise (fun i j => Disjoint (V i : Set C) (V j : Set C)) ∧
      (∀ i,(actualSubspaceSheaf (n := n) C).presheaf.map (homOfLE (hVW i)).op (e i)=1) ∧
      ∀ i,∀ p : W,p.val ∈ V i → f p ∈ B i := by
  obtain ⟨V,hVW,hClosed,hCover,hDisjoint,hMem,hOne⟩ :=
    exists_actual_clopen_selector_cover C W e hid hsum horth
  have hDense : Dense {p : W | original_value_hom C W p Q ≠ 0} :=
    original_section_nonzero_dense C W Q hq
  refine ⟨V,hVW,hClosed,hCover,hDisjoint,hOne,?_⟩
  intro i p hp
  let A : Opens W := ⟨(Subtype.val : W → C) ⁻¹' (V i : Set C),
    (V i).isOpen.preimage continuous_subtype_val⟩
  have hDenseA : Dense {a : A | original_value_hom C W a.val Q ≠ 0} :=
    hDense.preimage A.isOpen.isOpenMap_subtype_val
  let p0 : A := ⟨p,hp⟩
  have hc : IsClosed {a : A | f a.val ∈ B i} :=
    (hB i).preimage (hf.comp continuous_subtype_val)
  change p0 ∈ {a : A | f a.val ∈ B i}
  apply closure_minimal (s := {a : A | original_value_hom C W a.val Q ≠ 0}) _ hc (hDenseA p0)
  intro a ha
  obtain ⟨j,hj⟩ := hcover a.val
  by_cases hji : j=i
  · exact hji ▸ hj
  · have he := hrel i a.val
    rw [(hMem i a.val).mp a.property,mul_one,hvan i j (Ne.symm hji) _ hj] at he
    exact (ha he).elim

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSelectorLanding
