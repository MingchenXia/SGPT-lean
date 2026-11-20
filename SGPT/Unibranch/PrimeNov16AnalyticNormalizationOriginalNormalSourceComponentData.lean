import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNormalSourceSelectors
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalComponentTargetLift
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalComponentTargetRange
import SGPT.Unibranch.NativeNov16GraphPullbackScalarValues

/-! Actual normal source selector pieces internally produce EXACT raw targets and genuine pulled-H regularity.
Blueprint: prime-nov16-analytic-normalization-original-normal-source-component-data.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNormalSourceComponentData
open NativeNov16SectionCoordinateMorphism NativeNov16GraphPullbackScalarValues
open PrimeNov16AnalyticNormalizationOriginalNormalSourceSelectors
open PrimeNov16AnalyticNormalizationOriginalGraphPresentation
open PrimeNov16AnalyticNormalizationOriginalGraphTargetRefinement
open PrimeNov16AnalyticNormalizationOriginalCommonGraphMap
open PrimeNov16AnalyticNormalizationOriginalComponentTargetLift
open PrimeNov16AnalyticNormalizationOriginalComponentTargetRange
open PrimeNov16AnalyticNormalizationOriginalCoordinateWindowInclusion
open PrimeNov16AnalyticNormalizationOriginalProperRestriction
open PrimeNov16AnalyticNormalizationOriginalBaseScalarSections
open PrimeNov16AnalyticNormalizationOriginalSelectorSections
open PrimeNov16AnalyticNormalizationLocalGraph
open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceResidue
open HironakaActualAnalyticSubspaceLocalFunctions
open SourceReducedComplexSpace

theorem exists_actual_component_data {m n k : ℕ} {Z : Set (ComplexModel n)}
    (Ps : Opens (ComplexModel m)) (Cs : Set Ps) (hCs : IsComplexAnalyticSubset (n := m) Cs)
    (Ws : Opens (TopCat.of Cs)) (Pt : Opens (ComplexModel n))
    (hZ : IsComplexAnalyticSubset (n := n) ((Subtype.val : Pt → ComplexModel n) ⁻¹' Z))
    (B : Fin k → Set (ComplexModel n))
    (hB : ∀ i,IsComplexAnalyticSubset (n := n) ((Subtype.val : Pt → ComplexModel n) ⁻¹' B i))
    (hBZ : ∀ i,((Subtype.val : Pt → ComplexModel n) ⁻¹' B i) ⊆ ((Subtype.val : Pt → ComplexModel n) ⁻¹' Z))
    (hcover : ∀ b ∈ ((Subtype.val : Pt → ComplexModel n) ⁻¹' Z),∃ i,b.val ∈ B i)
    (d : ∀ i,GraphPresentation n (B i)) (hDP : ∀ i,ballDomain (n := n) (d i).radius ≤ Pt)
    (g : ∀ i,(d i).target ⟶ sourceReducedComplexSpaceModel Pt ((Subtype.val : Pt → ComplexModel n) ⁻¹' Z) hZ)
    (U : Opens (sourceReducedComplexSpaceModel Pt ((Subtype.val : Pt → ComplexModel n) ⁻¹' Z) hZ).obj.left)
    [ParacompactSpace U]
    (hcoord : ∀ i,∀ t : (d i).target.obj.left,((g i).hom.left.base t).val.val=t.val.val.val)
    (hRange : ∀ i,∀ x : (sourceReducedComplexSpaceModel Pt ((Subtype.val : Pt → ComplexModel n) ⁻¹' Z) hZ).obj.left,
      x ∈ U → (x ∈ range (g i).hom.left.base ↔ x.val.val ∈ B i))
    (f : coordinateSource Ps Cs hCs Ws ⟶ coordinateSource Pt ((Subtype.val : Pt → ComplexModel n) ⁻¹' Z) hZ U)
    (Ω : Opens (ComplexModel n)) (Q : ComplexModel n → ℂ) (T : Fin k → ComplexModel n → ℂ)
    (hQ : DifferentiableOn ℂ Q Ω) (hT : ∀ i,DifferentiableOn ℂ (T i) Ω)
    (hH : ∀ i,DifferentiableOn ℂ (d i).denominator Ω)
    (hland : ∀ b : ((Subtype.val : Pt → ComplexModel n) ⁻¹' Z),b ∈ U → b.val.val ∈ Ω)
    (hvan : ∀ i j,i ≠ j → ∀ b : Pt,b.val ∈ B j → b.val ∈ Ω → T i b.val=0)
    (hbranch : ∀ i,∀ b : Pt,b.val ∈ B i → b.val ∈ Ω → Q b.val=T i b.val*(d i).denominator b.val)
    (hnormal : ∀ x ∈ Ws,IsDomain ((actualSubspaceSheaf (n := m) Cs).presheaf.stalk x).carrier ∧
      IsIntegrallyClosed ((actualSubspaceSheaf (n := m) Cs).presheaf.stalk x).carrier)
    (hreg : ∀ x (hx : x ∈ Ws),(actualSubspaceSheaf (n := m) Cs).presheaf.germ Ws x hx
      (pulledPartialScalar Ps Cs hCs Ws Pt ((Subtype.val : Pt → ComplexModel n) ⁻¹' Z) hZ U f Ω Q hQ hland) ≠ 0) :
    ∃ (V : Fin k → Opens (TopCat.of Cs)) (hVW : ∀ i,V i ≤ Ws),
      (∀ i,IsClosed ((Subtype.val : Ws → Cs) ⁻¹' (V i : Set Cs))) ∧
      (∀ p : Ws,∃ i,p.val ∈ V i) ∧
      Pairwise (fun i j => Disjoint (V i : Set Cs) (V j : Set Cs)) ∧
      ∃ F : ∀ i,coordinateSource Ps Cs hCs (V i) ⟶ (commonGraph (d i) (g i) U).target,
        (∀ i,F i ≫ commonComponent (d i) (g i) U=windowInclusion Ps Cs hCs (V i) Ws (hVW i) ≫ f) ∧
        ∀ i,∀ x (hx : x ∈ V i),(actualSubspaceSheaf (n := m) Cs).presheaf.germ (V i) x hx
          (pulledBaseScalar (commonGraph (d i) (g i) U) Ps Cs hCs (V i) (F i)
            (d i).denominator (d i).denominator_holo) ≠ 0 := by
  classical
  let Ct := (Subtype.val : Pt → ComplexModel n) ⁻¹' Z
  obtain ⟨e,V,hVW,_heq,_hei,_heSum,_heOrth,_hFactor,hClosed,hCover,hDisjoint,_hOne,hHi,hG⟩ :=
    exists_actual_normal_source_selectors Ps Cs hCs Ws Pt Ct hZ U f
      (fun i => (Subtype.val : Pt → ComplexModel n) ⁻¹' B i) hB hBZ hcover Ω Q T
      (fun i => (d i).denominator) hQ hT hH hland hvan hbranch hnormal hreg
  choose G hGT _hGUniq using hG
  let σ (i : Fin k) : coordinateSource Ps Cs hCs (V i) ⟶ restrictedBase U :=
    windowInclusion Ps Cs hCs (V i) Ws (hVW i) ≫ f
  have htri (i : Fin k) : G i ≫ OriginalClosedSubspaceFactorization.inclusion (hB i) hZ (hBZ i)=
      σ i ≫ baseInclusion U := by
    exact hGT i
  have hLift (i : Fin k) := exists_unique_component_target_lift (d i) Pt (hB i) hZ (hBZ i) (hDP i)
    (g i) U (hcoord i) (hRange i) (coordinateSource Ps Cs hCs (V i)) (G i) (σ i) (htri i)
  choose F hF _hFuniq using hLift
  have hSquare (i : Fin k) : F i ≫ commonComponent (d i) (g i) U=σ i := by
    have he : (F i ≫ commonComponent (d i) (g i) U) ≫ baseInclusion U=σ i ≫ baseInclusion U := by
      rw [Category.assoc,componentTarget_triangle (d i) Pt (hB i) hZ (hBZ i) (hDP i) (g i) U (hcoord i),
        ← Category.assoc,hF i,htri i]
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply (cancel_mono (baseInclusion U).hom.left).mp
    exact congrArg (fun a => a.hom.left) he
  refine ⟨V,hVW,hClosed,hCover,hDisjoint,F,hSquare,?_⟩
  intro i
  have hEq : (actualSubspaceSheaf (n := m) Cs).presheaf.map (homOfLE (hVW i)).op
      (pulledPartialScalar Ps Cs hCs Ws Pt Ct hZ U f Ω (d i).denominator (hH i) hland)=
      pulledBaseScalar (commonGraph (d i) (g i) U) Ps Cs hCs (V i) (F i)
        (d i).denominator (d i).denominator_holo := by
    apply actualSubspaceSection_ext_eval Cs (V i)
    intro x hx
    let p : V i := ⟨x,hx⟩
    let pW : Ws := ⟨x,hVW i hx⟩
    have hCompCoord (b : (commonGraph (d i) (g i) U).target.obj.left) :
        ((commonComponent (d i) (g i) U).hom.left.base b).val.val.val=b.val.val.val := by
      have hs := congrArg (fun a => (a.hom.left.base b).val.val) (commonComponent_square (d i) (g i) U)
      have ht := targetEmbedding_point (d i) _ (commonBaseOpen_le (d i) (g i) U) b
      exact hs.trans ((hcoord i _).trans (congrArg (fun a => a.val.val) ht))
    have hpW : (windowInclusion Ps Cs hCs (V i) Ws (hVW i)).hom.left.base p=pW :=
      Subtype.ext (windowInclusion_point Ps Cs hCs (V i) Ws (hVW i) p)
    have hpt := congrArg (fun a => (a.hom.left.base p).val.val.val) (hSquare i)
    have hCoord : ((F i).hom.left.base p).val.val.val=(f.hom.left.base pW).val.val.val :=
      (hCompCoord ((F i).hom.left.base p)).symm.trans
        (hpt.trans (congrArg (fun a => (f.hom.left.base a).val.val.val) hpW))
    have hRes := congrArg (actualSubspaceStalkEval (n := m) Cs x)
      ((actualSubspaceSheaf (n := m) Cs).presheaf.germ_res_apply (homOfLE (hVW i)) x hx
        (pulledPartialScalar Ps Cs hCs Ws Pt Ct hZ U f Ω (d i).denominator (hH i) hland))
    exact hRes.trans ((pulledPartialScalar_value Ps Cs hCs Ws Pt Ct hZ U f Ω (d i).denominator (hH i) hland pW).trans
      ((congrArg (d i).denominator hCoord).symm.trans
        (pulledBaseScalar_value (commonGraph (d i) (g i) U) Ps Cs hCs (V i) (F i)
          (d i).denominator (d i).denominator_holo p).symm))
  intro x hx
  have hn := hHi i x hx
  exact hEq ▸ hn

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNormalSourceComponentData
