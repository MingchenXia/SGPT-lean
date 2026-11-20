import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSelectorLanding

/-! Literal common-denominator branch separation manufactures actual disjoint good base opens.
Blueprint: prime-nov16-analytic-normalization-original-good-branch-opens.tex. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGoodBranchOpens

theorem exists_actual_good_branch_opens {T : Type} [TopologicalSpace T] {k : ℕ}
    (B : Fin k → Set T) (hB : ∀ i,IsClosed (B i))
    (hcover : ∀ x : T,∃ i,x ∈ B i) (Q : T → ℂ) (hQ : Continuous Q)
    (hzero : ∀ i j,i ≠ j → ∀ x ∈ B i,x ∈ B j → Q x=0) :
    ∃ V : Fin k → Opens T,
      (∀ i x,x ∈ V i ↔ Q x ≠ 0 ∧ x ∈ B i) ∧
      Pairwise (fun i j => Disjoint (V i : Set T) (V j : Set T)) ∧
      ∀ x : T,Q x ≠ 0 ↔ ∃ i,x ∈ V i := by
  classical
  let V : Fin k → Opens T := fun i =>
    ⟨{x | Q x ≠ 0} ∩ ⋂ j : Fin k,{x | j=i ∨ x ∉ B j},by
      apply (isClosed_eq hQ continuous_const).isOpen_compl.inter
      apply isOpen_iInter_of_finite
      intro j
      by_cases hji : j=i
      · have he : {x : T | j=i ∨ x ∉ B j}=univ := by ext x; simp [hji]
        rw [he]
        exact isOpen_univ
      · have he : {x : T | j=i ∨ x ∉ B j}=(B j)ᶜ := by ext x; simp [hji]
        rw [he]
        exact (hB j).isOpen_compl⟩
  have hmem : ∀ i x,x ∈ V i ↔ Q x ≠ 0 ∧ x ∈ B i := by
    intro i x
    constructor
    · rintro ⟨hx,hothers⟩
      obtain ⟨j,hj⟩ := hcover x
      have he : j=i := by
        by_contra hji
        exact ((mem_iInter.mp hothers j).resolve_left hji) hj
      exact ⟨hx,he ▸ hj⟩
    · rintro ⟨hx,hi⟩
      refine ⟨hx,mem_iInter.mpr fun j => ?_⟩
      by_cases hji : j=i
      · exact Or.inl hji
      · exact Or.inr fun hj => hx (hzero i j (Ne.symm hji) x hi hj)
  refine ⟨V,hmem,?_,?_⟩
  · intro i j hij
    apply disjoint_left.mpr
    intro x hxi hxj
    exact ((hmem i x).mp hxi).1
      (hzero i j hij x ((hmem i x).mp hxi).2 ((hmem j x).mp hxj).2)
  · intro x
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := hcover x
      exact ⟨i,(hmem i x).mpr ⟨hx,hi⟩⟩
    · rintro ⟨i,hi⟩
      exact ((hmem i x).mp hi).1

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGoodBranchOpens
