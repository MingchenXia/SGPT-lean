import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalComponentGoodInverse
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGoodBranchOpens
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCoproductGoodInverse
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalIntegralGeometry

/-! SAME primitive actual integral family internally constructs its full original common good inverse.
Blueprint: prime-nov16-analytic-normalization-original-family-good-inverse.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace Topology CategoryTheory AlgebraicGeometry
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalFamilyGoodInverse
open PrimeNov16AnalyticNormalizationOriginalGraphPresentation
open PrimeNov16AnalyticNormalizationOriginalGraphTargetRefinement
open PrimeNov16AnalyticNormalizationOriginalCommonGraphMap
open PrimeNov16AnalyticNormalizationOriginalComponentTargetLift
open PrimeNov16AnalyticNormalizationOriginalComponentTargetRange
open PrimeNov16AnalyticNormalizationOriginalComponentGoodInverse
open PrimeNov16AnalyticNormalizationOriginalGoodBranchOpens
open PrimeNov16AnalyticNormalizationOriginalCoproductGoodInverse
open PrimeNov16AnalyticNormalizationOriginalIntegralGeometry
open PrimeNov16AnalyticNormalizationOriginalProperRestriction
open PrimeNov16AnalyticNormalizationLocalGraph
open PrimeNov16AnalyticNormalizationDenominatorGraph
open HironakaG1NativeDisjointCoproduct
open SourceReducedComplexSpace

theorem actual_family_common_good_inverse {n k : ℕ} {Z : Set (ComplexModel n)}
    (B : Fin k → Set (ComplexModel n)) (P : Opens (ComplexModel n))
    (hB : ∀ i,IsComplexAnalyticSubset (n := n) ((Subtype.val : P → ComplexModel n) ⁻¹' B i))
    (hZ : IsComplexAnalyticSubset (n := n) ((Subtype.val : P → ComplexModel n) ⁻¹' Z))
    (hBZ : ∀ i,((Subtype.val : P → ComplexModel n) ⁻¹' B i) ⊆ ((Subtype.val : P → ComplexModel n) ⁻¹' Z))
    (d : ∀ i,GraphPresentation n (B i))
    (hDP : ∀ i,ballDomain (n := n) (d i).radius ≤ P)
    (g : ∀ i,(d i).target ⟶ sourceReducedComplexSpaceModel P ((Subtype.val : P → ComplexModel n) ⁻¹' Z) hZ)
    (hg : ∀ i,Topology.IsEmbedding (g i).hom.left.base)
    (hcoord : ∀ i,∀ b : (d i).target.obj.left,((g i).hom.left.base b).val.val=b.val.val.val)
    (U : Opens (sourceReducedComplexSpaceModel P ((Subtype.val : P → ComplexModel n) ⁻¹' Z) hZ).obj.left)
    [ParacompactSpace U]
    (hRange : ∀ i,∀ x : (sourceReducedComplexSpaceModel P ((Subtype.val : P → ComplexModel n) ⁻¹' Z) hZ).obj.left,
      x ∈ U → (x ∈ range (g i).hom.left.base ↔ x.val.val ∈ B i))
    (hcover : ∀ x : (restrictedBase U).obj.left,∃ i,x.val.val.val ∈ B i)
    (deg : ∀ i,Fin (d i).arity → ℕ)
    (a : ∀ i,Fin (d i).arity → ℕ → ComplexModel n → ℂ)
    (ha : ∀ i j l,l < deg i j → DifferentiableOn ℂ (a i j l) (ballDomain (n := n) (d i).radius))
    (hm : ∀ i,∀ p : (d i).graph.obj.left,∀ j,GermParametrizationData.monicEval (deg i j) (a i j)
      (baseProjection n (d i).arity p.val.val) (fibreProjection n (d i).arity p.val.val j)=0)
    (Q : (restrictedBase U).obj.left → ℂ) (hQ : Continuous Q)
    (hzero : ∀ i j,i ≠ j → ∀ x : (restrictedBase U).obj.left,
      x.val.val.val ∈ B i → x.val.val.val ∈ B j → Q x=0)
    (hHi : ∀ i,∀ x : (restrictedBase U).obj.left,x.val.val.val ∈ B i → Q x ≠ 0 →
      (d i).denominator x.val.val.val ≠ 0) :
    let Y : Fin k → SourceReducedComplexSpace := fun i => (commonGraph (d i) (g i) U).source
    let F : ∀ i,Y i ⟶ restrictedBase U := fun i => commonMap (d i) (g i) U
    IsIsoOver (desc Y F) {x | Q x ≠ 0} := by
  classical
  let X := sourceReducedComplexSpaceModel P ((Subtype.val : P → ComplexModel n) ⁻¹' Z) hZ
  let Y : Fin k → SourceReducedComplexSpace := fun i => (commonGraph (d i) (g i) U).source
  let F : ∀ i,Y i ⟶ restrictedBase U := fun i => commonMap (d i) (g i) U
  have hClosed (i : Fin k) : IsClosed {x : (restrictedBase U).obj.left | x.val.val.val ∈ B i} :=
    ((hB i).isClosed.preimage continuous_subtype_val).preimage continuous_subtype_val
  obtain ⟨V,hmem,hdisj,hVcover⟩ := exists_actual_good_branch_opens
    (fun i => {x : (restrictedBase U).obj.left | x.val.val.val ∈ B i}) hClosed hcover Q hQ hzero
  let G : Opens (restrictedBase U).obj.left := ⟨{x | Q x ≠ 0},(isClosed_eq hQ continuous_const).isOpen_compl⟩
  let W : Fin k → Opens X.obj.left := fun i =>
    ⟨(Subtype.val : U → X.obj.left) '' {x : U | x ∈ V i},U.isOpen.isOpenMap_subtype_val _
      (show IsOpen {x : U | x ∈ V i} from (V i).isOpen)⟩
  have hWU (i : Fin k) : W i ≤ U := by
    rintro _ ⟨x,_hx,rfl⟩
    exact x.property
  have hWmem (i : Fin k) (x : (restrictedBase U).obj.left) : x.val ∈ W i ↔ x ∈ V i := by
    constructor
    · rintro ⟨y,hy,hyx⟩
      exact (Subtype.ext hyx : y=x) ▸ hy
    · intro hx
      exact ⟨x,hx,rfl⟩
  have hWB (i : Fin k) : ∀ x : X.obj.left,x ∈ W i → x.val.val ∈ B i := by
    rintro _ ⟨x,hx,rfl⟩
    exact ((hmem i x).mp hx).2
  have hWpc (i : Fin k) : ParacompactSpace (W i) := by
    change ParacompactSpace {x : {z : P | z.val ∈ Z} // x ∈ W i}
    infer_instance
  have hIso (i : Fin k) : IsIsoOver (F i) (V i) := by
    let : ParacompactSpace (W i : Opens (sourceReducedComplexSpaceModel P ((Subtype.val : P → ComplexModel n) ⁻¹' Z) hZ).obj.left) := hWpc i
    have hi := commonMap_isIsoOver_original_good (d i) P (hB i) hZ (hBZ i) (hDP i) (g i) U
      (hcoord i) (hRange i) (W i) (hWU i) (hWB i) (by
        intro b hb
        let x := (commonComponent (d i) (g i) U).hom.left.base b
        have hxV : x ∈ V i := (hWmem i x).mp hb
        have hne := hHi i x ((hmem i x).mp hxV).2 ((hmem i x).mp hxV).1
        have ht := congrArg (fun m => (m.hom.left.base b).val.val)
          (componentTarget_triangle (d i) P (hB i) hZ (hBZ i) (hDP i) (g i) U (hcoord i))
        have hc : x.val.val.val=b.val.val.val := ht.trans
          (componentTargetInclusion_point (d i) P (hB i) hZ (hDP i) (g i) U b)
        exact (congrArg (d i).denominator hc) ▸ hne)
    have he : (baseInclusion U).hom.left.base ⁻¹' (W i : Set X.obj.left)=(V i : Set (restrictedBase U).obj.left) := by
      ext x
      exact hWmem i x
    exact he ▸ hi
  have hclRange (i : Fin k) : IsClosed ((Subtype.val : U → X.obj.left) ⁻¹' range (g i).hom.left.base) := by
    have hc : IsClosed {x : U | x.val.val.val ∈ B i} := hClosed i
    have he : (Subtype.val : U → X.obj.left) ⁻¹' range (g i).hom.left.base=
        {x : U | x.val.val.val ∈ B i} := by
      ext x
      exact hRange i x.val x.property
    exact he.symm ▸ hc
  have hpF : ∀ i,IsProperMap (F i).hom.left.base := fun i =>
    commonMap_proper (d i) (g i) U (actual_graph_projection_proper (d i) (deg i) (a i) (ha i) (hm i))
      (hg i) (hclRange i)
  let : ParacompactSpace G := by
    change ParacompactSpace {x : {b : {z : P | z.val ∈ Z} // b ∈ U} // Q x ≠ 0}
    infer_instance
  apply coproduct_isIsoOver_actual_good Y F hpF G V (fun x hx => (hVcover x).mp hx) hdisj _ hIso
  intro i p hp
  apply (hmem i _).mpr
  refine ⟨hp,?_⟩
  let b := (commonGraph (d i) (g i) U).map.hom.left.base p
  have ht := congrArg (fun m => m.hom.left.base b)
    (componentTarget_triangle (d i) P (hB i) hZ (hBZ i) (hDP i) (g i) U (hcoord i))
  have hBp := ((componentTargetInclusion (d i) P (hB i) hZ (hDP i) (g i) U).hom.left.base b).property
  have he : ((commonComponent (d i) (g i) U).hom.left.base b).val.val.val=
      ((componentTargetInclusion (d i) P (hB i) hZ (hDP i) (g i) U).hom.left.base b).val.val :=
    congrArg (fun x => x.val.val) ht
  change ((commonComponent (d i) (g i) U).hom.left.base b).val.val.val ∈ B i
  exact he.symm ▸ hBp

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalFamilyGoodInverse
