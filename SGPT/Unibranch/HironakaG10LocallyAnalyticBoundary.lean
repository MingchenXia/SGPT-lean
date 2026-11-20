import SGPT.Unibranch.HironakaG10LocalSupportAnalytic
import SGPT.Unibranch.HironakaG10LocallyAnalyticTrace
import SGPT.Unibranch.HironakaG10AnalyticStratumBoundary

/-! # Local analytic Hironaka boundary for an actual flattener -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open SGPT.Foundations.Analysis.FirstPass

namespace SGPT.Unibranch.HironakaG10LocallyAnalyticBoundary

open SGPT.Unibranch.SourceReducedComplexSpace
  SGPT.Unibranch.HironakaG10LocalSupportAnalytic
  SGPT.Unibranch.HironakaG10LocallyAnalyticTrace
  SGPT.Unibranch.HironakaG10HirLocalFlattener
  SGPT.Unibranch.HironakaG10NativeAnalyticClosureDifference
  SGPT.Unibranch.HironakaG10RelativeNonflatStrata
  SGPT.Unibranch.HironakaG10AnalyticStratumBoundary
open SGPT.Foundations.Analysis.Pending.ClosureDifferenceAnalytic

noncomputable section

/-- For an actual local flattener, if a positive stratum is locally analytic on the domain
  then its Hironaka boundary has native analytic charts at every point of the
  flattener domain. No global analyticity of the flattener support is assumed. -/
theorem locallyAnalytic_stratumBoundary
    {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) (B : Set X.obj.left)
    (Z : LocalFlattener f) (i : ℕ)
    (hS : IsLocallyAnalyticOn X Z.V (strata f B (i + 1))) (x : X.obj.left) (hx : x ∈ Z.V) :
    ∃ e : LocalEmbedding X, x ∈ range e.toPoint ∧ range e.toPoint ⊆ Z.V ∧
      ∃ A : Set e.ambient, IsComplexAnalyticSubset (n := e.dim) A ∧
        e.toPoint ⁻¹' stratumBoundary f B Z.V Z.support i = Subtype.val ⁻¹' A := by
  obtain ⟨e,he,heV,A,hA,htrace⟩ := local_support_analytic Z x hx
  let SA : Set e.ambient := Subtype.val '' (e.toPoint ⁻¹' strata f B (i + 1))
  let SZ : Set e.ambient := Subtype.val '' (e.toPoint ⁻¹' Z.support)
  have hSA : IsComplexAnalyticSubset (n := e.dim) SA := analytic_image_local_trace hS e heV
  have hSZ : IsComplexAnalyticSubset (n := e.dim) SZ := by
    dsimp [SZ]
    rw [htrace, Set.image_preimage_eq_inter_range, Subtype.range_coe]
    exact hA.inter e.analytic
  refine ⟨e,he,heV,closure (SA \ SZ) ∩ SZ,
    (isComplexAnalyticSubset_closure_diff hSA hSZ).inter hSZ, ?_⟩
  have heW : e.toPoint ⁻¹' Z.V = univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro z
    exact heV ⟨z,rfl⟩
  have hdiff : e.toPoint ⁻¹' ((strata f B (i + 1) ∩ Z.V) \ Z.support) =
      (e.toPoint ⁻¹' strata f B (i + 1)) \ (e.toPoint ⁻¹' Z.support) := by
    rw [Set.preimage_sdiff, Set.preimage_inter, heW, Set.inter_univ]
  change e.toPoint ⁻¹' (closure ((strata f B (i + 1) ∩ Z.V) \ Z.support) ∩ Z.support) = _
  rw [Set.preimage_inter, e.isOpenEmbedding_toPoint.isOpenMap.preimage_closure_eq_closure_preimage
    e.isOpenEmbedding_toPoint.continuous, hdiff,
    Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
    Set.image_sdiff Subtype.val_injective]
  dsimp [SA, SZ]
  rw [Set.preimage_image_eq _ Subtype.val_injective]

end
end SGPT.Unibranch.HironakaG10LocallyAnalyticBoundary
