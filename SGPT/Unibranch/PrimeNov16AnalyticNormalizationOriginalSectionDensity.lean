import SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphSheafCancellation

/-! Actual original nonzero whole-section germs manufacture dense genuine value nonvanishing.
Blueprint: prime-nov16-analytic-normalization-original-section-density.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory Opposite
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSectionDensity
open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceResidue
open HironakaActualAnalyticSubspaceLocalFunctions

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem original_section_nonzero_dense (C : Set M) (W : Opens (TopCat.of C))
    (s : ((actualSubspaceSheaf (n := n) C).presheaf.obj (op W)).carrier)
    (hs : ∀ x : C,∀ hx : x ∈ W,
      (actualSubspaceSheaf (n := n) C).presheaf.germ W x hx s ≠ 0) :
    Dense {p : W | actualSubspaceStalkEval (n := n) C p.val
      ((actualSubspaceSheaf (n := n) C).presheaf.germ W p.val p.property s) ≠ 0} := by
  intro p
  rw [mem_closure_iff]
  intro O hO hpO
  by_contra hempty
  let V : Opens (TopCat.of C) := ⟨Subtype.val '' O,W.isOpen.isOpenMap_subtype_val O hO⟩
  have hVW : V ≤ W := by
    rintro x ⟨q,_hq,rfl⟩
    exact q.property
  let F := (actualSubspaceSheaf (n := n) C).presheaf
  let sV := F.map (homOfLE hVW).op s
  have hsV : sV=0 := by
    apply actualSubspaceSection_eq_zero_of_eval
    intro x hx
    obtain ⟨q,hq,rfl⟩ := hx
    have hzero : actualSubspaceStalkEval (n := n) C q.val
        (F.germ W q.val q.property s)=0 := by
      by_contra hn
      exact hempty ⟨q,hq,hn⟩
    change actualSubspaceStalkEval (n := n) C q.val (F.germ V q.val _ (F.map _ s))=0
    rw [F.germ_res_apply]
    exact hzero
  have hpV : p.val ∈ V := ⟨p,hpO,rfl⟩
  apply hs p.val p.property
  have he := F.germ_res_apply (homOfLE hVW) p.val hpV s
  change F.germ V p.val hpV sV=F.germ W p.val p.property s at he
  rw [hsV,map_zero] at he
  exact he.symm

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSectionDensity
