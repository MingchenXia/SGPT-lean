import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalResolutionNormalizationLift
import SGPT.Unibranch.ComplexSpaceAnalyticPreimage
import SGPT.Unibranch.EmbeddedCommonResolutionGeneral
import SGPT.Foundations.Analysis.Pending.ConstantRankImage
import Mathlib.Topology.Maps.Proper.Basic

/-! The SAME chosen resolution lift is an actual resolution, retaining arbitrary smooth-centre blowups.
Blueprint: prime-nov16-analytic-normalization-original-resolution-lift-properties.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HironakaReducedComplexAnalyticSpaces HironakaIntrinsicComplexAnalyticRegularLocus
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalResolutionLiftProperties
open SourceReducedComplexSpace
open PrimeNov16AnalyticNormalizationOriginalResolutionNormalizationLift
open PrimeNov16AnalyticNormalizationOriginalGoodDensity

private theorem analytic_union {X : SourceReducedComplexSpace} {A B : Set X.obj.left}
    (hA : X.IsAnalyticSubset A) (hB : X.IsAnalyticSubset B) : X.IsAnalyticSubset (A ∪ B) := by
  intro x
  let e := LocalEmbedding.ofPoint X x
  let j : sourceReducedComplexSpaceModel e.ambient e.carrier e.analytic ⟶ X :=
    ObjectProperty.homMk (Over.homMk e.map e.overPoint)
  have hA' : (sourceReducedComplexSpaceModel e.ambient e.carrier e.analytic).IsAnalyticSubset
      (e.toPoint ⁻¹' A) := hA.preimage j
  have hB' : (sourceReducedComplexSpaceModel e.ambient e.carrier e.analytic).IsAnalyticSubset
      (e.toPoint ⁻¹' B) := hB.preimage j
  refine ⟨e,LocalEmbedding.mem_range_ofPoint X x,
    (Subtype.val '' (e.toPoint ⁻¹' A)) ∪ (Subtype.val '' (e.toPoint ⁻¹' B)),
    ConstantRankImage.IsComplexAnalyticSubset.union
      (isComplexAnalyticSubset_image_of_isAnalyticSubset_model hA')
      (isComplexAnalyticSubset_image_of_isAnalyticSubset_model hB'),?_⟩
  rw [Set.preimage_union,Set.preimage_union,
    Set.preimage_image_eq _ Subtype.val_injective,Set.preimage_image_eq _ Subtype.val_injective]

private theorem cancel_good_inverse {X Y N : SourceReducedComplexSpace}
    (p : N ⟶ X) (f : Y ⟶ X) (l : Y ⟶ N) (ht : l ≫ p=f)
    (Q : Set X.obj.left) (hp : IsIsoOver p Q) (hf : IsIsoOver f Q) :
    IsIsoOver l (p.hom.left.base ⁻¹' Q) := by
  obtain ⟨V,j,hj,hjr,hjf,hjfr⟩ := hf
  obtain ⟨W,k,hk,hkr,hkp,_hkpr⟩ := hp
  let : LocallyRingedSpace.IsOpenImmersion j := hj
  let : LocallyRingedSpace.IsOpenImmersion k := hk
  let : LocallyRingedSpace.IsOpenImmersion (j ≫ f.hom.left) := hjf
  let : LocallyRingedSpace.IsOpenImmersion (k ≫ p.hom.left) := hkp
  have htp : l.hom.left ≫ p.hom.left=f.hom.left := congrArg (fun g => g.hom.left) ht
  let g := j ≫ l.hom.left
  have hgp : g ≫ p.hom.left=j ≫ f.hom.left := by
    dsimp only [g]
    rw [Category.assoc,htp]
  have hr : range g.base ⊆ range k.base := by
    rintro _ ⟨v,rfl⟩
    rw [hkr]
    have hv : (j ≫ f.hom.left).base v ∈ Q := by rw [← hjfr];exact ⟨v,rfl⟩
    exact Eq.ndrec (motive := fun x : X.obj.left => x ∈ Q) hv
      (congrArg (fun a => a.base v) hgp).symm
  let a := LocallyRingedSpace.IsOpenImmersion.lift k g hr
  have hak : a ≫ k=g := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hr
  have hap : a ≫ (k ≫ p.hom.left)=j ≫ f.hom.left :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun t => t ≫ p.hom.left) hak).trans hgp)
  let : LocallyRingedSpace.IsOpenImmersion (a ≫ (k ≫ p.hom.left)) := hap.symm ▸ hjf
  have ha : LocallyRingedSpace.IsOpenImmersion a :=
    HironakaG10ChowStrictTransformCalculus.isOpenImmersion_of_comp a (k ≫ p.hom.left)
  let : LocallyRingedSpace.IsOpenImmersion a := ha
  have hg : LocallyRingedSpace.IsOpenImmersion g := by rw [← hak];infer_instance
  refine ⟨V,j,hj,?_,hg,?_⟩
  · rw [hjr]
    ext y
    have he := congrArg (fun z => z ∈ Q) (congrArg (fun t => t.hom.left.base y) ht).symm
    exact ⟨Eq.mp he,Eq.mpr he⟩
  · apply subset_antisymm
    · intro n hn
      rw [← hkr]
      exact hr hn
    · intro n hn
      have hn' : n ∈ range k.base := by rw [hkr];exact hn
      obtain ⟨w,hw⟩ := hn'
      have hpw : p.hom.left.base n ∈ range (j ≫ f.hom.left).base := by rw [hjfr];exact hn
      obtain ⟨v,hv⟩ := hpw
      refine ⟨v,?_⟩
      have haw : a.base v=w := by
        apply hkp.base_open.injective
        calc
          (k ≫ p.hom.left).base (a.base v) = (j ≫ f.hom.left).base v := congrArg (fun t => t.base v) hap
          _ = p.hom.left.base n := hv
          _ = (k ≫ p.hom.left).base w := congrArg p.hom.left.base hw.symm
      have hvk := congrArg (fun t => t.base v) hak
      exact hvk.symm.trans ((congrArg k.base haw).trans hw)

theorem resolutionLift_isResolution {X Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (hf : IsResolution f) : IsResolution (resolutionLift f hf) := by
  let N := NativeNov16NormalizationSpace.source X
  let p : N ⟶ X := NativeNov16NormalizationSpace.projection X
  let l : Y ⟶ N := resolutionLift f hf
  have ht : l ≫ p=f := resolutionLift_projection f hf
  let : T2Space N.obj.left := N.property.1
  have hproper : IsProperMap l.hom.left.base := by
    let lf : Y.obj.left → N.obj.left := l.hom.left.base
    let pf : N.obj.left → X.obj.left := p.hom.left.base
    have he : pf ∘ lf=f.hom.left.base :=
      congrArg (fun t => (fun y : Y.obj.left => t.hom.left.base y)) ht
    have hc : IsProperMap (pf ∘ lf) := he.symm ▸ hf.2.1
    exact isProperMap_of_comp_of_t2 (f := lf) (g := pf)
      l.hom.left.base.hom.continuous p.hom.left.base.hom.continuous hc
  obtain ⟨Z,hZa,hZ,hfZ,hfi⟩ := hf.2.2
  let S : Set X.obj.left := intrinsicSingularLocus X.obj
  let Q : Set X.obj.left := Zᶜ ∩ intrinsicRegularLocus X.obj
  have hQo : IsOpen Q := hZa.isClosed.isOpen_compl.inter (isOpen_intrinsicRegularLocus X.obj)
  have hQd : Dense Q :=
    (interior_eq_empty_iff_dense_compl.mp hZ).inter_of_isOpen_right
      (OriginalIntrinsicSingularLocus.dense_intrinsicRegularLocus X) (isOpen_intrinsicRegularLocus X.obj)
  have hfD : Dense (f.hom.left.base ⁻¹' Zᶜ) := by
    simpa only [Set.preimage_compl] using (interior_eq_empty_iff_dense_compl.mp hfZ)
  have hfQ : IsIsoOver f Q := hfi.of_isOpen_subset hQo (fun _ hx => hx.1)
  have hpQ : IsIsoOver p Q :=
    (NativeNov16NormalizationExistence.isIsoOver_intrinsicRegularLocus X).of_isOpen_subset hQo (fun _ hx => hx.2)
  have hdF : Dense (f.hom.left.base ⁻¹' Q) :=
    dense_preimage_of_actual_good_inverse f Zᶜ hfi hfD Q hQd
  have hdP : Dense (p.hom.left.base ⁻¹' Q) :=
    dense_preimage_of_actual_good_inverse p (intrinsicRegularLocus X.obj)
      (NativeNov16NormalizationExistence.isIsoOver_intrinsicRegularLocus X)
      (NativeNov16NormalizationExistence.dense_preimage_intrinsicRegularLocus X) Q hQd
  have hQc : (Z ∪ S)ᶜ=Q := by simp only [S,Q,Set.compl_union,intrinsicSingularLocus,compl_compl]
  refine ⟨hf.1,hproper,p.hom.left.base ⁻¹' (Z ∪ S),
    (analytic_union hZa (OriginalIntrinsicSingularLocus.isAnalyticSubset_intrinsicSingularLocus X)).preimage p,?_,?_,?_⟩
  · apply interior_eq_empty_iff_dense_compl.mpr
    simpa only [← Set.preimage_compl,hQc] using hdP
  · apply interior_eq_empty_iff_dense_compl.mpr
    have he : l.hom.left.base ⁻¹' (p.hom.left.base ⁻¹' Q)=f.hom.left.base ⁻¹' Q := by
      ext y
      have he := congrArg (fun z => z ∈ Q) (congrArg (fun t => t.hom.left.base y) ht)
      exact ⟨Eq.mp he,Eq.mpr he⟩
    have hd : Dense (l.hom.left.base ⁻¹' (p.hom.left.base ⁻¹' Q)) := he.symm ▸ hdF
    simpa only [← Set.preimage_compl,hQc] using hd
  · have hi := cancel_good_inverse p f l ht Q hpQ hfQ
    simpa only [← Set.preimage_compl,hQc] using hi
end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalResolutionLiftProperties
