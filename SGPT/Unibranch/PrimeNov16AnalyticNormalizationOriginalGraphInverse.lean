import SGPT.Unibranch.PrimeNov16AnalyticNormalizationGoodIso
import SGPT.Unibranch.Resolution

/-! Actual full native good inverse for the SAME literal denominator graph.
Blueprint: prime-nov16-analytic-normalization-original-graph-inverse.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGraphInverse
open SourceReducedComplexSpace
open PrimeNov16AnalyticNormalizationDenominatorGraph
open PrimeNov16AnalyticNormalizationGoodIso
open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceOpenRestriction

theorem original_graph_isIsoOver {n k : ℕ} (U : Opens (ComplexModel n)) {C : Set U}
    (hC : IsComplexAnalyticSubset (n := n) C)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (hG : ∀ i,DifferentiableOn ℂ (G i) U) :
    IsIsoOver (projection U hC H G hH hG) {b | H b.val.val ≠ 0} := by
  let e := goodIso U hC H G hH hG
  let j := actualOpenSubspaceMap (n := n+k) (graphClosure U C H G) (goodWide U H hH)
  let a := actualOpenSubspaceMap (n := n) C (goodBase U H hH)
  have he : j ≫ (projection U hC H G hH hG).hom.left=e.inv ≫ a := by
    have h := goodIso_hom_over U hC H G hH hG
    change (e.hom ≫ j) ≫ (projection U hC H G hH hG).hom.left=a at h
    calc
      _ = e.inv ≫ ((e.hom ≫ j) ≫ (projection U hC H G hH hG).hom.left) := by simp
      _ = _ := congrArg (fun f => e.inv ≫ f) h
  refine ⟨_,j,inferInstance,?_,?_,?_⟩
  · ext p
    constructor
    · rintro ⟨x,rfl⟩
      exact x.val.property
    · intro hp
      exact ⟨⟨⟨p.val,hp⟩,p.property⟩,rfl⟩
  · rw [he]
    infer_instance
  · rw [he]
    ext b
    constructor
    · rintro ⟨x,rfl⟩
      exact (e.inv.base x).val.property
    · intro hb
      let x : ((Subtype.val : goodBase U H hH → U) ⁻¹' C) := ⟨⟨b.val,hb⟩,b.property⟩
      refine ⟨e.hom.base x,?_⟩
      have hx : e.inv.base (e.hom.base x)=x :=
        congrArg (fun f => f.base x) e.hom_inv_id
      change a.base (e.inv.base (e.hom.base x))=b
      rw [hx]
      rfl

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGraphInverse
