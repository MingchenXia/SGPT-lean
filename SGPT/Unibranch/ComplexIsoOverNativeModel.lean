import SGPT.Unibranch.ComplexSpaceSmoothPSHMaximum

/-! Actual native models at the SAME point over the original isomorphism locus.
Blueprint: complex-iso-over-native-model.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.SourceReducedComplexSpace

private theorem lift_isOpenImmersion {A B T : LocallyRingedSpace}
    (f : A ⟶ T) (g : B ⟶ T)
    [LocallyRingedSpace.IsOpenImmersion f] [LocallyRingedSpace.IsOpenImmersion g]
    (h : range g.base ⊆ range f.base) :
    LocallyRingedSpace.IsOpenImmersion (LocallyRingedSpace.IsOpenImmersion.lift f g h) := by
  let isoNativeLiftPullback : IsIso (pullback.snd f g) :=
    LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset f g h
  dsimp only [LocallyRingedSpace.IsOpenImmersion.lift]
  infer_instance

private theorem inclusion_isOpenImmersion {d : ℕ} {T V : Opens (ComplexModel d)} (hTV : T ≤ V) :
    LocallyRingedSpace.IsOpenImmersion
      (ChartedSpace.locallyRingedSpaceMap (IM := 𝓘(ℂ,ComplexModel d))
        (IN := 𝓘(ℂ,ComplexModel d)) (Opens.inclusion hTV) (contMDiff_inclusion hTV)) := by
  let jV := ChartedSpace.locallyRingedSpaceMap (Subtype.val : V → ComplexModel d)
    (contMDiff_subtype_val (I := 𝓘(ℂ,ComplexModel d)))
  let jT := ChartedSpace.locallyRingedSpaceMap (Subtype.val : T → ComplexModel d)
    (contMDiff_subtype_val (I := 𝓘(ℂ,ComplexModel d)))
  have hRange : range jT.base ⊆ range jV.base := by
    rintro _ ⟨t,rfl⟩
    exact ⟨Opens.inclusion hTV t,rfl⟩
  have hcomp : ChartedSpace.locallyRingedSpaceMap (IM := 𝓘(ℂ,ComplexModel d))
      (IN := 𝓘(ℂ,ComplexModel d)) (Opens.inclusion hTV) (contMDiff_inclusion hTV) ≫ jV = jT := rfl
  have h := lift_isOpenImmersion jV jT hRange
  rwa [← LocallyRingedSpace.IsOpenImmersion.lift_uniq jV jT hRange _ hcomp] at h

theorem IsIsoOver.native_model_of_target {X Y : SourceReducedComplexSpace}
    {π : Y ⟶ X} {U : Set X.obj.left} (hiso : IsIsoOver π U)
    (y : Y.obj.left) (hy : π.hom.left.base y ∈ U) (d : ℕ) (V : Opens (ComplexModel d))
    (i : ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel d) V ⟶ X.obj.left)
    (hi : LocallyRingedSpace.IsOpenImmersion i) (hp : i ≫ X.obj.hom = ambientPointMap d V)
    (hx : π.hom.left.base y ∈ range i.base) :
    ∃ (T : Opens (ComplexModel d))
      (a : ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel d) T ⟶ Y.obj.left),
      LocallyRingedSpace.IsOpenImmersion a ∧ a ≫ Y.obj.hom = ambientPointMap d T ∧
      y ∈ range a.base := by
  obtain ⟨W,j,hj,hjr,hk,hkr⟩ := hiso
  let k := j ≫ π.hom.left
  have hU : IsOpen U := hkr ▸ hk.base_open.isOpen_range
  obtain ⟨v,hiv⟩ := hx
  let D : Set V := i.base ⁻¹' U
  have hD : IsOpen D := hU.preimage i.base.hom.continuous
  have hvD : v ∈ D := by change i.base v ∈ U;rwa [hiv]
  have hS : IsOpen ((Subtype.val : V → ComplexModel d) '' D) :=
    V.isOpen.isOpenMap_subtype_val D hD
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hS v.val ⟨v,hvD,rfl⟩
  let T : Opens (ComplexModel d) := ⟨ball v.val r,isOpen_ball⟩
  have hTV : T ≤ V := by
    intro z hz
    obtain ⟨q,_hq,rfl⟩ := hball hz
    exact q.property
  let I := ChartedSpace.locallyRingedSpaceMap (IM := 𝓘(ℂ,ComplexModel d))
    (IN := 𝓘(ℂ,ComplexModel d)) (Opens.inclusion hTV) (contMDiff_inclusion hTV)
  let F := I ≫ i
  let nativeTargetModelOI : LocallyRingedSpace.IsOpenImmersion i := hi
  let nativeIsoSourceOI : LocallyRingedSpace.IsOpenImmersion j := hj
  let nativeIsoTargetOI : LocallyRingedSpace.IsOpenImmersion k := hk
  let nativeModelInclusionOI : LocallyRingedSpace.IsOpenImmersion I := inclusion_isOpenImmersion hTV
  have hF : LocallyRingedSpace.IsOpenImmersion F := by dsimp only [F];infer_instance
  let nativeRestrictedModelOI : LocallyRingedSpace.IsOpenImmersion F := hF
  have hFp : F ≫ X.obj.hom = ambientPointMap d T := by
    rw [show F = I ≫ i from rfl,Category.assoc,hp]
    exact (ChartedSpace.locallyRingedSpace_comp (IM := 𝓘(ℂ,ComplexModel d))
      (IN := 𝓘(ℂ,ComplexModel d)) (IP := 𝓘(ℂ,ComplexModel 0))
      (contMDiff_inclusion hTV) contMDiff_const).symm
  have hRange : range F.base ⊆ range k.base := by
    rintro _ ⟨z,rfl⟩
    rw [show range k.base = U from hkr]
    obtain ⟨q,hq,hqz⟩ := hball z.property
    have hqeq : q = Opens.inclusion hTV z := Subtype.ext hqz
    change i.base (Opens.inclusion hTV z) ∈ U
    rwa [← hqeq]
  let L := LocallyRingedSpace.IsOpenImmersion.lift k F hRange
  have hL : L ≫ k = F := LocallyRingedSpace.IsOpenImmersion.lift_fac k F hRange
  have hLOI : LocallyRingedSpace.IsOpenImmersion L := lift_isOpenImmersion k F hRange
  let nativeModelLiftOI : LocallyRingedSpace.IsOpenImmersion L := hLOI
  let a := L ≫ j
  have ha : LocallyRingedSpace.IsOpenImmersion a := by dsimp only [a];infer_instance
  have haπ : a ≫ π.hom.left = F := by simpa only [a,k,Category.assoc] using hL
  have hap : a ≫ Y.obj.hom = ambientPointMap d T := by
    rw [← Over.w π.hom,← Category.assoc,haπ,hFp]
  let t : T := ⟨v.val,mem_ball_self hr⟩
  have hFt : F.base t = π.hom.left.base y := by
    change i.base (Opens.inclusion hTV t) = π.hom.left.base y
    have he : Opens.inclusion hTV t = v := Subtype.ext rfl
    rw [he,hiv]
  obtain ⟨w,hjw⟩ : y ∈ range j.base := by rw [hjr];exact hy
  have hLw : L.base t = w := by
    apply hk.base_open.injective
    calc
      k.base (L.base t) = F.base t := congrArg (fun q => q.base t) hL
      _ = π.hom.left.base y := hFt
      _ = k.base w := by change π.hom.left.base y = π.hom.left.base (j.base w);rw [hjw]
  refine ⟨T,a,ha,hap,t,?_⟩
  change j.base (L.base t) = y
  rw [hLw,hjw]

end SGPT.Unibranch.SourceReducedComplexSpace
