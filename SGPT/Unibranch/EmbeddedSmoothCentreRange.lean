import SGPT.Unibranch.SmoothCentreModification
import SGPT.Unibranch.EmbeddedCommonResolutionGeneralAnalyticSubsets
import SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspaceRegularityConverse
import SGPT.Foundations.Analysis.Pending.HironakaEmbeddedNativeMorphism
import SGPT.Foundations.Analysis.Pending.CodimOnePartCanonical

/-! Smooth closed centers of a reduced embedded space are submanifolds of the ambient manifold. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Unibranch

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SourceReducedComplexSpace HironakaResolutionSpaceComplex HironakaReducedComplexAnalyticSpaces
open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
open HironakaActualAnalyticSubspaceManifoldCharts HironakaActualAnalyticSubspaceRegularityConverse
open HironakaActualHolomorphicStalkSurjection HironakaEmbeddedNativeMorphism
open scoped Topology Manifold ContDiff

private theorem openImmersion_lift_of_range {A B T : LocallyRingedSpace}
    (f : A ⟶ T) (g : B ⟶ T) [LocallyRingedSpace.IsOpenImmersion f]
    [LocallyRingedSpace.IsOpenImmersion g] (h : range g.base ⊆ range f.base) :
    LocallyRingedSpace.IsOpenImmersion (LocallyRingedSpace.IsOpenImmersion.lift f g h) := by
  let : IsIso (pullback.snd f g) :=
    LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset f g h
  dsimp only [LocallyRingedSpace.IsOpenImmersion.lift]
  infer_instance

private theorem inclusion_overPoint {d : ℕ} (O : Opens (ComplexModel d)) :
    ChartedSpace.locallyRingedSpaceMap (Subtype.val : O → ComplexModel d)
      (contMDiff_subtype_val (I := 𝓘(ℂ, ComplexModel d))) ≫
        ambientPointMap d (ComplexModel d) = ambientPointMap d O :=
  (ChartedSpace.locallyRingedSpace_comp (IM := 𝓘(ℂ, ComplexModel d))
    (IN := 𝓘(ℂ, ComplexModel d)) (IP := 𝓘(ℂ, ComplexModel 0))
    contMDiff_subtype_val
    (show ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel 0) ∞
      (fun _ : ComplexModel d => (0 : ComplexModel 0)) from contMDiff_const)).symm

/-- The given closed center immersion has its original ambient range as a closed submanifold. -/
theorem isClosedSubmanifold_ambientImage_of_smoothCentre
    {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {W : Set M} (hW : IsComplexAnalyticSubset (n := n) W)
    {S : SourceReducedComplexSpace} (i : S ⟶ ofClosedAnalytic W hW) (hS : S.IsSmooth)
    (hclosed : Topology.IsClosedEmbedding i.hom.left.base)
    (hstalk : ∀ s : S.obj.left, Function.Surjective (i.hom.left.stalkMap s)) :
    IsClosedSubmanifold n ((Subtype.val : W → M) '' range i.hom.left.base) := by
  let F : S.obj.left → M := fun s => (i.hom.left.base s).val
  have hF : Topology.IsClosedEmbedding F := hW.isClosed.isClosedEmbedding_subtypeVal.comp hclosed
  rw [← Set.range_comp]
  change IsClosedSubmanifold n (range F)
  refine ⟨hF.isClosed_range, ?_⟩
  rintro _ ⟨s, rfl⟩
  obtain ⟨d, O, j, hj, hjp, z, hz⟩ := hS s
  let : LocallyRingedSpace.IsOpenImmersion j := hj
  let x := F s
  let e := chartDiffeo (n := n) x
  let L := chartModelMap (n := n) W x
  have hL : LocallyRingedSpace.IsOpenImmersion L := inferInstance
  let P : Opens O := ⟨(j ≫ i.hom.left).base ⁻¹' range L.base,
    hL.base_open.isOpen_range.preimage
      (j ≫ i.hom.left).base.hom.continuous⟩
  have hzP : z ∈ P := by
    change i.hom.left.base (j.base z) ∈ range L.base
    rw [hz]
    exact mem_range_chartModelMap (n := n) W (i.hom.left.base s).property
  let O' : Opens (ComplexModel d) :=
    ⟨(Subtype.val : O → ComplexModel d) '' (P : Set O),
      O.isOpen.isOpenMap_subtype_val _ P.isOpen⟩
  let a := ChartedSpace.locallyRingedSpaceMap (Subtype.val : O → ComplexModel d)
    (contMDiff_subtype_val (I := 𝓘(ℂ, ComplexModel d)))
  let b := ChartedSpace.locallyRingedSpaceMap (Subtype.val : O' → ComplexModel d)
    (contMDiff_subtype_val (I := 𝓘(ℂ, ComplexModel d)))
  have hab : range b.base ⊆ range a.base := by
    rintro _ ⟨u, rfl⟩
    obtain ⟨v, _, hv⟩ := u.property
    exact ⟨v, hv⟩
  let k := LocallyRingedSpace.IsOpenImmersion.lift a b hab
  let : LocallyRingedSpace.IsOpenImmersion k := openImmersion_lift_of_range a b hab
  have hk : k ≫ a = b := LocallyRingedSpace.IsOpenImmersion.lift_fac a b hab
  have hkval (u : O') : (k.base u).val = u.val := congrArg (fun g => g.base u) hk
  have hkP (u : O') : k.base u ∈ P := by
    obtain ⟨v, hv, hvu⟩ := u.property
    have he : k.base u = v := Subtype.ext ((hkval u).trans hvu.symm)
    rwa [he]
  let z' : O' := ⟨z.val, ⟨z, hzP, rfl⟩⟩
  have hkz : k.base z' = z := Subtype.ext (hkval z')
  let J := k ≫ j
  let : LocallyRingedSpace.IsOpenImmersion J := inferInstance
  have hJz : J.base z' = s := (congrArg j.base hkz).trans hz
  have hJp : J ≫ S.obj.hom = ambientPointMap d O' := by
    dsimp only [J]
    rw [Category.assoc, hjp, ← inclusion_overPoint O, ← Category.assoc, hk]
    exact inclusion_overPoint O'
  have hr : range (J ≫ i.hom.left).base ⊆ range L.base := by
    rintro _ ⟨u, rfl⟩
    exact hkP u
  let G := LocallyRingedSpace.IsOpenImmersion.lift L (J ≫ i.hom.left) hr
  have hG : G ≫ L = J ≫ i.hom.left :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac L (J ≫ i.hom.left) hr
  have hLp : L ≫ subspacePointMap (n := n) W =
      subspacePointMap (n := n) (chartTrace (n := n) W x) :=
    chartModelMap_point (n := n) W x
  have hiPoint : i.hom.left ≫ subspacePointMap (n := n) W = S.obj.hom :=
    Over.w i.hom
  have hGp : G ≫ subspacePointMap (n := n) (chartTrace (n := n) W x) = ambientPointMap d O' := by
    rw [← hLp, ← Category.assoc, hG, Category.assoc, hiPoint]
    exact hJp
  let g : O' → chartImage (n := n) x := fun u => (G.base u).val
  have hg : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel n) ∞ g :=
    contMDiff_native_source_pointMap G hGp
  have hkG : Function.Surjective (G.stalkMap z') := by
    have hcomp : Function.Surjective ((J ≫ i.hom.left).stalkMap z') := by
      rw [LocallyRingedSpace.stalkMap_comp]
      exact ((ConcreteCategory.isIso_iff_bijective (J.stalkMap z')).mp inferInstance).2.comp
        (hstalk (J.base z'))
    rw [← hG, LocallyRingedSpace.stalkMap_comp] at hcomp
    intro y
    obtain ⟨a₀, ha₀⟩ := hcomp y
    exact ⟨L.stalkMap (G.base z') a₀, ha₀⟩
  let sub := actualSubspaceInclusion (n := n) (chartTrace (n := n) W x)
  have hgG : ChartedSpace.locallyRingedSpaceMap g hg = G ≫ sub := by
    let E := actualSubspaceUnivIso (n := d) (M := O')
    have hpoint : (E.hom ≫ G) ≫ subspacePointMap (n := n) (chartTrace (n := n) W x) =
        subspacePointMap (n := d) (univ : Set O') := by
      rw [Category.assoc, hGp]
      rfl
    have hact : actualSubspaceMap hg
        (fun u (_ : u ∈ (univ : Set O')) => (G.base u).property) = E.hom ≫ G :=
      original_morphism_eq_actualSubspaceMap _ hpoint
    apply (cancel_epi E.hom).mp
    rw [← Category.assoc, ← hact]
    exact actualSubspaceMap_inclusion hg
      (fun u (_ : u ∈ (univ : Set O')) => (G.base u).property)
  have hsurj : Function.Surjective ((ChartedSpace.locallyRingedSpaceMap g hg).stalkMap z') := by
    rw [hgG, LocallyRingedSpace.stalkMap_comp]
    exact hkG.comp (actualSubspaceInclusionRingedHom_stalk_surjective
      (chartTrace (n := n) W x) (G.base z'))
  obtain ⟨A, hA, hzA, hAO, hreg⟩ := exists_regular_local_image_of_stalk_surjective hg z' hsurj
  let A' : Set O' := Subtype.val ⁻¹' A
  have hJOI : LocallyRingedSpace.IsOpenImmersion J := inferInstance
  have hOpenJ : IsOpen (J.base '' A') :=
    hJOI.base_open.isOpenMap _ (hA.preimage continuous_subtype_val)
  obtain ⟨U, hU, hJU⟩ := hF.isInducing.isOpen_iff.mp hOpenJ
  have hGpt (u : O') : ((e.symm (g u)).val : M) = F (J.base u) :=
    congrArg (fun l => (l.base u).val) hG
  let B : Set (chartImage (n := n) x) := chartTrace (n := n) (range F) x
  let Q : Set (chartImage (n := n) x) := (fun y => (e.symm y).val) ⁻¹' U
  have hQ : IsOpen Q := hU.preimage (continuous_subtype_val.comp e.symm.continuous)
  have hB : g '' A' = B ∩ Q := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨⟨J.base u, (hGpt u).symm⟩, ?_⟩
      change (e.symm (g u)).val ∈ U
      rw [hGpt u]
      change J.base u ∈ F ⁻¹' U
      rw [hJU]
      exact ⟨u, hu, rfl⟩
    · rintro ⟨⟨s', hs'⟩, hyU⟩
      have hsJ : s' ∈ J.base '' A' := by
        rw [← hJU]
        change F s' ∈ U
        rw [hs']
        exact hyU
      obtain ⟨u, hu, rfl⟩ := hsJ
      refine ⟨u, hu, ?_⟩
      apply e.symm.injective
      exact Subtype.ext ((hGpt u).trans hs')
  have hRA : RegularAtDim (n := n) (g '' A') (g z') d := by
    apply AnalyticSubsetOpens.regularAtDim_image_val_iff.mp
    have himage : (Subtype.val : chartImage (n := n) x → ComplexModel n) '' (g '' A') =
        actualOpenVectorExtension O' (fun u : O' => (g u).val) '' A := by
      ext y
      constructor
      · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
        exact ⟨u.val, hu, actualOpenVectorExtension_apply O' _ u⟩
      · rintro ⟨a₀, ha₀, rfl⟩
        let u : O' := ⟨a₀, hAO ha₀⟩
        refine ⟨g u, ⟨u, ha₀, rfl⟩, ?_⟩
        change (g u).val = actualOpenVectorExtension O' (fun w => (g w).val) u.val
        exact (actualOpenVectorExtension_apply O' (fun w => (g w).val) u).symm
    rw [himage]
    exact hreg _ ⟨z'.val, hzA, actualOpenVectorExtension_apply O' _ z'⟩
  have hzQ : g z' ∈ Q := (hB ▸ (show g z' ∈ g '' A' from ⟨z', hzA, rfl⟩)).2
  have hBreg : RegularAtDim (n := n) B (g z') d :=
    RegularPointDimension.regularAtDim_of_inter_eq hQ hzQ
      (by rw [hB, inter_assoc, inter_self]) hRA
  have hpt : (e.symm (g z')).val = x := (hGpt z').trans (congrArg F hJz)
  let D : Set (chartDomain (n := n) x) := (Subtype.val : chartDomain (n := n) x → M) ⁻¹' range F
  have hB' : RegularAtDim (n := n) (e.symm ⁻¹' D) (g z') d := hBreg
  have hlocal : RegularAtDim (n := n) D (e.symm (g z')) d :=
    (CodimOnePartCanonical.regularAtDim_preimage_iff e.symm (A := D) (x := g z')).mp hB'
  refine ⟨d, ?_⟩
  change RegularAtDim (n := n) (range F) x d
  rw [← hpt]
  exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hlocal

end SGPT.Unibranch
