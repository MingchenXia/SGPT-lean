import SGPT.PSH.PrimeNov16OriginalComponentModification

/-! Actual lift of a marked original component, with pairing/dimension/map derived.
Full blueprint first: `prime-nov16-original-prime-models.tex`. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.PSH.PrimeNov16OriginalMarkedComponentLift
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  HironakaResolutionSpaceComplex HironakaReducedComplexAnalyticSpaces
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  AnalyticModificationLocalDiscrepancy BlowupTowers
open SGPT.Unibranch SourceReducedComplexSpace OriginalNativeModification OriginalSmoothSourceAnalytic

private theorem analytic_union {X : SourceReducedComplexSpace} {A B : Set X.obj.left}
    (hA : X.IsAnalyticSubset A) (hB : X.IsAnalyticSubset B) : X.IsAnalyticSubset (A ∪ B) := by
  intro x
  let e := LocalEmbedding.ofPoint X x
  refine ⟨e, LocalEmbedding.mem_range_ofPoint X x,
    (Subtype.val '' (e.toPoint ⁻¹' A)) ∪ (Subtype.val '' (e.toPoint ⁻¹' B)),
    ConstantRankImage.IsComplexAnalyticSubset.union
      (hA.analytic_image_localEmbedding e) (hB.analytic_image_localEmbedding e), ?_⟩
  rw [preimage_union, preimage_union, preimage_image_eq _ Subtype.val_injective,
    preimage_image_eq _ Subtype.val_injective]

private theorem identity_pb (Y : SourceReducedComplexSpace) : IsProperBimeromorphic (𝟙 Y) := by
  refine ⟨isProperMap_id, ∅, isAnalyticSubset_empty, by simp, by simp, ?_⟩
  exact IsIsoOver.id_of_isOpen Y (by simp)

theorem exists_actual_marked_component_lift
    {Y S : SourceReducedComplexSpace} (hS : S.IsSmooth) (hY : Y.IsSmooth)
    (G : S ⟶ Y) (hG : IsProperBimeromorphic G)
    (cY : ConnectedComponents Y.obj.left) {n : ℕ} (M : CMfd n)
    (I : wholeModel (n := n) M ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hY cY) :
    ∃ (cS : ConnectedComponents S.obj.left) (N : CMfd n)
      (J : wholeModel (n := n) N ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hS cS)
      (F : wholeModel (n := n) N ⟶ wholeModel (n := n) M),
      IsProperBimeromorphic F ∧
      F ≫ (I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY cY) =
        J.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hS cS ≫ G := by
  obtain ⟨E₀, E₁, hE₀, hE₁, hi₀, _hi₁, ht₀, ht₁, pair, hpair⟩ :=
    PrimeNov16OriginalComponentPairing.exists_original_good_component_pairing hS hY G (𝟙 Y) hG (identity_pb Y)
  let B := E₀ ∪ E₁
  have hBa : Y.IsAnalyticSubset B := analytic_union hE₀ hE₁
  have hBt : interior B = ∅ := ht₁
  obtain ⟨m, N, ⟨J⟩⟩ := HironakaG1NoncompactSmoothComponentModel.exists_component_manifold_model hS (pair cY)
  obtain ⟨hdim, F, hF, hfull⟩ :=
    PrimeNov16OriginalComponentModification.exists_actual_native_component_modification
      hS hY G hG B hBa hBt hi₀ ht₀ (pair cY) cY (hpair cY) N M J I
  subst m
  exact ⟨pair cY, N, J, F, hF, hfull⟩

end SGPT.PSH.PrimeNov16OriginalMarkedComponentLift
