import SGPT.Unibranch.HironakaG10OpenCoherentProjectionFlatOpen
import SGPT.Unibranch.ComplexSpaceLocalEmbedding
import SGPT.Unibranch.HironakaG10ChowFlatteningDriver
import SGPT.Unibranch.Resolution
import SGPT.Foundations.Analysis.Pending.HironakaGraphBaseChangeElimination
import SGPT.Foundations.Analysis.Pending.HironakaVanishingQuotientOriginalSubspaceBridge
import SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspaceManifoldCharts

/-! Native flat-locus openness over a smooth original complex space.
All coherent graph ideals, generator windows and full map squares are derived
from ordinary morphisms; the smooth chart dimension is local. -/

set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.HironakaG10SmoothTargetFlatOpen
noncomputable section
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.Pending
  HironakaActualWholeStalkHolomorphicPullback HironakaActualOpenIntrinsicHS
  HironakaActualAnalyticSubspaceOpenRestriction HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaGraphBaseChangeElimination HironakaNonreducedAnalyticQuotientModel
  HironakaVanishingQuotientOriginalSubspaceBridge HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceManifoldCharts
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspaceLocalFunctions
  SourceReducedComplexSpace

private theorem flat_stalk_precomp_iso_iff {P Q S : LocallyRingedSpace}
    (e : P ≅ Q) (g : Q ⟶ S) (x : P) :
    ((e.hom ≫ g).stalkMap x).hom.Flat ↔ (g.stalkMap (e.hom.base x)).hom.Flat := by
  rw [LocallyRingedSpace.stalkMap_comp]
  exact RingHom.Flat.comp_iff_of_bijective_left
    ((ConcreteCategory.isIso_iff_bijective (e.hom.stalkMap x)).mp inferInstance)

private theorem flat_stalk_postcomp_iff {P Q S : LocallyRingedSpace}
    (f : P ⟶ Q) (g : Q ⟶ S) (x : P)
    (hg : Function.Bijective (g.stalkMap (f.base x))) :
    ((f ≫ g).stalkMap x).hom.Flat ↔ (f.stalkMap x).hom.Flat := by
  rw [LocallyRingedSpace.stalkMap_comp]
  exact RingHom.Flat.comp_iff_of_bijective_right hg

private theorem open_inclusion_stalk_bijective {d : ℕ} (V : Opens (ComplexModel d)) (x : V) :
    Function.Bijective ((ChartedSpace.locallyRingedSpaceMap (IM := 𝓘(ℂ, ComplexModel d))
      (IN := 𝓘(ℂ, ComplexModel d)) (Subtype.val : V → ComplexModel d)
      contMDiff_subtype_val).stalkMap x) := by
  let j := ChartedSpace.locallyRingedSpaceMap (IM := 𝓘(ℂ, ComplexModel d))
    (IN := 𝓘(ℂ, ComplexModel d)) (Subtype.val : V → ComplexModel d) contMDiff_subtype_val
  have hs (a : actualComplexStructureStalk (n := d) x.val) :
      actualStalkChartEquiv (n := d) x (j.stalkMap x a) =
        actualStalkChartEquiv (n := d) x.val a := by
    rw [actualNativeStalk_chart_pullback, actualHolomorphicGermPullback_val]
    rfl
  constructor
  · intro a b hab
    apply (actualStalkChartEquiv (n := d) x.val).injective
    rw [← hs a, ← hs b, hab]
  · intro b
    refine ⟨(actualStalkChartEquiv (n := d) x.val).symm
      (actualStalkChartEquiv (n := d) x b), ?_⟩
    apply (actualStalkChartEquiv (n := d) x).injective
    rw [hs, RingEquiv.apply_symm_apply]

theorem isOpen_flatLocus_coherentMap {n d : ℕ} (U : Opens (ComplexModel n))
    (V : Opens (ComplexModel d)) (I : GermIdeal n U) (hI : I.IsCoherent)
    (f : U → V) (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel d) ∞ f) :
    IsOpen {x : I.zeroLocus |
      ((quotientInclusion I hI ≫ ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x).hom.Flat} := by
  let J := graphIdeal U V f I
  let hJ := graphIdeal_coherent U V f hf I hI
  let e := graphQuotientIso U V f hf I hI
  let p := HironakaG10OpenCoherentProjectionFlatOpen.projection d n (graphOpen U V) J hJ
  let g := quotientInclusion I hI ≫ ChartedSpace.locallyRingedSpaceMap f hf
  let j := ChartedSpace.locallyRingedSpaceMap (IM := 𝓘(ℂ, ComplexModel d))
    (IN := 𝓘(ℂ, ComplexModel d)) (Subtype.val : V → ComplexModel d) contMDiff_subtype_val
  have hcomp : e.hom ≫ p = g ≫ j := by
    have hproj : ChartedSpace.locallyRingedSpaceMap
        (fun w : graphOpen U V => HironakaRelativeNormalIdeal.tangentProjection d n w.val)
        ((HironakaRelativeNormalIdeal.tangentProjection d n).contDiff.contMDiff.comp contMDiff_subtype_val) =
      ChartedSpace.locallyRingedSpaceMap (graphTarget U V) (graphTarget_holomorphic U V) ≫ j := by
      dsimp only [j]
      rw [← ChartedSpace.locallyRingedSpace_comp]
      rfl
    change e.hom ≫ (quotientInclusion J hJ ≫ _) = g ≫ j
    rw [hproj, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ j) (graphQuotientIso_base U V f hf I hI)
  have hflat (x : I.zeroLocus) : (g.stalkMap x).hom.Flat ↔ (p.stalkMap (e.hom.base x)).hom.Flat := by
    rw [← flat_stalk_postcomp_iff g j x (open_inclusion_stalk_bijective V (g.base x)), ← hcomp]
    exact flat_stalk_precomp_iso_iff e p x
  have hset : {x : I.zeroLocus | (g.stalkMap x).hom.Flat} =
      e.hom.base ⁻¹' {z | (p.stalkMap z).hom.Flat} := by
    ext x
    exact hflat x
  change IsOpen {x : I.zeroLocus | (g.stalkMap x).hom.Flat}
  rw [hset]
  exact (HironakaG10OpenCoherentProjectionFlatOpen.isOpen_flatLocus_projection
    d n (graphOpen U V) J hJ).preimage e.hom.base.hom.continuous

theorem isOpen_flatLocus_model_to_manifold {n d : ℕ} (U : Opens (ComplexModel n))
    (V : Opens (ComplexModel d)) (C : Set U) (hC : IsComplexAnalyticSubset (n := n) C)
    (f : U → V) (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel d) ∞ f) :
    IsOpen {x : C |
      ((actualSubspaceInclusion (n := n) C ≫ ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x).hom.Flat} := by
  let I := vanishingIdeal (n := n) C
  let hI := CartanIrreducible.cartanCoherence C hC
  let e := vanishingQuotientOriginalSubspaceIso C hC
  let g := actualSubspaceInclusion (n := n) C ≫ ChartedSpace.locallyRingedSpaceMap f hf
  let q := quotientInclusion I hI ≫ ChartedSpace.locallyRingedSpaceMap f hf
  have hcomp : e.inv ≫ q = g := by
    rw [← Category.assoc]
    exact congrArg (· ≫ ChartedSpace.locallyRingedSpaceMap f hf) (bridge_inv_inclusion C hC)
  have hset : {x : C | (g.stalkMap x).hom.Flat} =
      e.inv.base ⁻¹' {z | (q.stalkMap z).hom.Flat} := by
    ext x
    rw [← hcomp]
    exact flat_stalk_precomp_iso_iff e.symm q x
  change IsOpen {x : C | (g.stalkMap x).hom.Flat}
  rw [hset]
  exact (isOpen_flatLocus_coherentMap U V I hI f hf).preimage e.inv.base.hom.continuous

theorem isOpen_flatLocus_modelMap {n d : ℕ} (U : Opens (ComplexModel n))
    (V : Opens (ComplexModel d)) (C : Set U) (hC : IsComplexAnalyticSubset (n := n) C)
    (f : U → V) (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel d) ∞ f) :
    IsOpen {x : C |
      ((actualSubspaceMap hf (fun _ _ => mem_univ _) :
        actualSubspaceLocallyRingedSpace (n := n) C ⟶
          actualSubspaceLocallyRingedSpace (n := d) (Set.univ : Set V)).stalkMap x).hom.Flat} := by
  let g := actualSubspaceMap hf (C := C) (D := Set.univ) (fun _ _ => mem_univ _)
  let e := actualSubspaceUnivIso (n := d) (M := V)
  have hcomp : g ≫ e.hom = actualSubspaceInclusion (n := n) C ≫
      ChartedSpace.locallyRingedSpaceMap f hf := (actualSubspaceMap_inclusion hf _).symm
  have hset : {x : C | (g.stalkMap x).hom.Flat} =
      {x : C | ((actualSubspaceInclusion (n := n) C ≫
        ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x).hom.Flat} := by
    ext x
    rw [← hcomp]
    exact (flat_stalk_postcomp_iff g e.hom x
      ((ConcreteCategory.isIso_iff_bijective (e.hom.stalkMap (g.base x))).mp inferInstance)).symm
  change IsOpen {x : C | (g.stalkMap x).hom.Flat}
  rw [hset]
  exact isOpen_flatLocus_model_to_manifold U V C hC f hf

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual stalk-flat locus of an ordinary morphism to a smooth original
complex space is open. The smooth dimension and all graph data are local. -/
theorem isOpen_flatLocus {X Y : SourceReducedComplexSpace} (p : Y ⟶ X) (hX : X.IsSmooth) :
    IsOpen {y : Y.obj.left | (p.hom.left.stalkMap y).hom.Flat} := by
  classical
  rw [isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨d, V, i, hi, hip, v, hv⟩ := hX (p.hom.left.base y)
  let _ : LocallyRingedSpace.IsOpenImmersion i := hi
  let eX : LocalEmbedding X :=
    { dim := d
      ambient := V
      carrier := Set.univ
      analytic := isComplexAnalyticSubset_univ (n := d)
      map := (actualSubspaceUnivIso (n := d) (M := V)).hom ≫ i
      isOpenImmersion := by
        change LocallyRingedSpace.IsOpenImmersion
          ((actualSubspaceUnivIso (n := d) (M := V)).hom ≫ i)
        infer_instance
      overPoint := by
        change ((actualSubspaceUnivIso (n := d) (M := V)).hom ≫ i) ≫ X.obj.hom =
          subspacePointMap (n := d) (Set.univ : Set V)
        rw [Category.assoc, hip]
        rfl }
  let _ : LocallyRingedSpace.IsOpenImmersion eX.map := eX.isOpenImmersion
  let eY := LocalEmbedding.ofPoint Y y
  obtain ⟨c, hc⟩ := LocalEmbedding.mem_range_ofPoint Y y
  let F := eY.map ≫ p.hom.left
  have hF : F ≫ X.obj.hom = (modelOver eY.ambient eY.carrier).hom := by
    dsimp only [F]
    rw [Category.assoc, Over.w p.hom]
    exact eY.overPoint
  have hFc : F.base c ∈ range eX.toPoint := by
    refine ⟨⟨v, mem_univ _⟩, ?_⟩
    change i.base v = p.hom.left.base (eY.toPoint c)
    rw [hc]
    exact hv
  obtain ⟨W, hW, hcW, hWU, G, hG, hGV, hfac⟩ :=
    LocalEmbedding.exists_contDiffOn_factor F hF eX c hFc
  let U : Opens (ComplexModel eY.dim) := ⟨W, hW⟩
  have hUV : U ≤ eY.ambient := hWU
  let e := eY.restrict U hUV
  let _ : LocallyRingedSpace.IsOpenImmersion e.map := e.isOpenImmersion
  let f : U → V := fun z => ⟨G z.val, hGV z.property⟩
  have hf : ContMDiff 𝓘(ℂ, ComplexModel eY.dim) 𝓘(ℂ, ComplexModel d) ∞ f := by
    apply (ContMDiff.subtypeVal_comp_iff V f).mp
    intro z
    exact contMDiffAt_subtype_iff.mpr ((hG.contDiffAt (hW.mem_nhds z.property)).contMDiffAt)
  let g := actualSubspaceMap hf (C := e.carrier) (D := Set.univ) (fun _ _ => mem_univ _)
  have hbase (z : e.carrier) : eX.toPoint (g.base z) = p.hom.left.base (e.toPoint z) := by
    let w : eY.carrier := ⟨Opens.inclusion hUV z.val, z.property⟩
    obtain ⟨a, ha, hpa⟩ := hfac w z.val.property
    have hga : g.base z = a := by
      apply Subtype.ext
      apply Subtype.ext
      exact ha.symm
    rw [hga, hpa]
    rfl
  let R := e.map ≫ p.hom.left
  have hrange : range R.base ⊆ range eX.map.base := by
    rintro _ ⟨z, rfl⟩
    exact ⟨g.base z, hbase z⟩
  let H := LocallyRingedSpace.IsOpenImmersion.lift eX.map R hrange
  have hHfac : H ≫ eX.map = R := LocallyRingedSpace.IsOpenImmersion.lift_fac eX.map R hrange
  have hHp : H ≫ subspacePointMap (n := d) (Set.univ : Set V) =
      subspacePointMap (n := e.dim) e.carrier := by
    calc
      _ = H ≫ (eX.map ≫ X.obj.hom) := congrArg (H ≫ ·) eX.overPoint.symm
      _ = R ≫ X.obj.hom := by rw [← Category.assoc, hHfac]
      _ = _ := by
        dsimp only [R]
        rw [Category.assoc, Over.w p.hom]
        exact e.overPoint
  have hgH : g = H := by
    apply actualSubspaceMap_eq_of_base_eq g H
    · exact actualSubspaceMap_point hf _
    · exact hHp
    · ext z
      apply eX.toPoint_injective
      have hh := congrArg (fun k => k.base z) hHfac
      exact (hbase z).trans hh.symm
  have hwhole : g ≫ eX.map = e.map ≫ p.hom.left := by
    rw [hgH]
    exact hHfac
  have hflat (z : e.carrier) : (g.stalkMap z).hom.Flat ↔
      (p.hom.left.stalkMap (e.toPoint z)).hom.Flat := by
    have hxbij := (ConcreteCategory.isIso_iff_bijective (eX.map.stalkMap (g.base z))).mp
      (LocallyRingedSpace.IsOpenImmersion.stalk_iso eX.map (g.base z))
    have hybij := (ConcreteCategory.isIso_iff_bijective (e.map.stalkMap z)).mp
      (LocallyRingedSpace.IsOpenImmersion.stalk_iso e.map z)
    calc
      _ ↔ ((g ≫ eX.map).stalkMap z).hom.Flat :=
        (flat_stalk_postcomp_iff g eX.map z hxbij).symm
      _ ↔ ((e.map ≫ p.hom.left).stalkMap z).hom.Flat := Iff.of_eq
        (congrArg (fun k => (k.stalkMap z).hom.Flat) hwhole)
      _ ↔ _ := by
        rw [LocallyRingedSpace.stalkMap_comp]
        exact RingHom.Flat.comp_iff_of_bijective_left hybij
  have hopen : IsOpen {z : e.carrier | (g.stalkMap z).hom.Flat} :=
    isOpen_flatLocus_modelMap U V e.carrier e.analytic f hf
  let cU : e.carrier := ⟨⟨c.val.val, hcW⟩, c.property⟩
  have hcU : e.toPoint cU = y := by
    change (eY.restrict U hUV).toPoint cU = y
    rw [LocalEmbedding.restrict_toPoint]
    exact hc
  have hfc : (g.stalkMap cU).hom.Flat :=
    (hflat cU).mpr (by rw [hcU]; exact hy)
  have himg := e.isOpenEmbedding_toPoint.isOpenMap _ hopen
  refine mem_of_superset (himg.mem_nhds ⟨cU, hfc, hcU⟩) ?_
  rintro _ ⟨z, hz, rfl⟩
  exact (hflat z).mp hz

theorem isClosed_nonflatImage {X Y : SourceReducedComplexSpace} (p : Y ⟶ X)
    (hX : X.IsSmooth) (hp : IsProperMap p.hom.left.base) :
    IsClosed (HironakaG10ChowStrictFlatLocus.nonflatImage p) :=
  HironakaG10ChowFlatteningDriver.isClosed_nonflatImage p hp (isOpen_flatLocus p hX)

end
end SGPT.Unibranch.HironakaG10SmoothTargetFlatOpen
