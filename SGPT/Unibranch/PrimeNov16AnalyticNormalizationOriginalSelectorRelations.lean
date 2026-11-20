import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSelectorSections

/-! Literal branch identities manufacture actual WHOLE numerator relations, not assumed certificates.
Blueprint: prime-nov16-analytic-normalization-original-selector-relations.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory Opposite
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSelectorRelations
open PrimeNov16AnalyticNormalizationOriginalSelectorSections
open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceLocalFunctions

theorem actual_whole_selector_numerator_relations {n k : ℕ} {M T : Type}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (C : Set M) (W : Opens (TopCat.of C)) (f : W → T)
    (B : Fin k → Set T) (hcover : ∀ p : W,∃ i,f p ∈ B i)
    (D : T → ℂ) (N : Fin k → T → ℂ)
    (hvan : ∀ i j,i ≠ j → ∀ x ∈ B j,N i x=0)
    (hbranch : ∀ i,∀ x ∈ B i,D x=N i x)
    (q : ((actualSubspaceSheaf (n := n) C).presheaf.obj (op W)).carrier)
    (s : Fin k → ((actualSubspaceSheaf (n := n) C).presheaf.obj (op W)).carrier)
    (hq : ∀ p : W,original_value_hom C W p q=D (f p))
    (hs : ∀ i,∀ p : W,original_value_hom C W p (s i)=N i (f p)) :
    (∀ i,(s i)^2=q*s i) ∧ (∑ i,s i)=q ∧ ∀ i j,i ≠ j → s i*s j=0 := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro i
    apply actualSubspaceSection_ext_eval C W
    intro y hy
    let p : W := ⟨y,hy⟩
    change original_value_hom C W p ((s i)^2)=original_value_hom C W p (q*s i)
    rw [map_pow,map_mul,hs,hq]
    obtain ⟨j,hj⟩ := hcover p
    by_cases hij : i=j
    · subst j
      rw [hbranch i _ hj,pow_two]
    · rw [hvan i j hij _ hj]
      simp
  · apply actualSubspaceSection_ext_eval C W
    intro y hy
    let p : W := ⟨y,hy⟩
    change original_value_hom C W p (∑ i,s i)=original_value_hom C W p q
    rw [map_sum,hq]
    obtain ⟨j,hj⟩ := hcover p
    calc
      _ = original_value_hom C W p (s j) := by
        apply Finset.sum_eq_single j
        · intro i _hi hij
          rw [hs,hvan i j hij _ hj]
        · intro hjfalse
          exact (hjfalse (Finset.mem_univ j)).elim
      _ = D (f p) := (hs j p).trans (hbranch j _ hj).symm
  · intro i j hij
    apply actualSubspaceSection_ext_eval C W
    intro y hy
    let p : W := ⟨y,hy⟩
    change original_value_hom C W p (s i*s j)=original_value_hom C W p 0
    rw [map_mul,map_zero,hs,hs]
    obtain ⟨l,hl⟩ := hcover p
    by_cases hil : i=l
    · subst l
      rw [hvan j i (Ne.symm hij) _ hl,mul_zero]
    · rw [hvan i l hil _ hl,zero_mul]

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSelectorRelations
