import SGPT.Unibranch.ComplexSpaceUnibranchComponents
import SGPT.Unibranch.ComplexSpacePSHMaximum
import SGPT.Unibranch.ComplexSpaceUnibranchFibers

/-! Genuine original singular pole propagation and internally produced
PSH finite-locus density. Accepted local resolution is reused read-only.
Blueprint: complex-space-unibranch-psh-density.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
namespace SGPT.Unibranch.SourceReducedComplexSpace

/-- Original intrinsic unibranchness transports along the SAME actual
open-immersion stalk isomorphism, including its integral-closure reading. -/
theorem IsUnibranch.of_openImmersion {X V : SourceReducedComplexSpace}
    (hX : X.IsUnibranch) (j : V ⟶ X) (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) :
    V.IsUnibranch := by
  let singularUnibranchOpenImmersion : LocallyRingedSpace.IsOpenImmersion j.hom.left := hj
  intro v
  let E := (asIso (j.hom.left.stalkMap v)).commRingCatIsoToRingEquiv
  exact (sourceUnibranchReducedRing_iff_of_ringEquiv E).mp (hX (j.hom.left.base v))

private theorem discCriterion_of_locallyAmbient {X : SourceReducedComplexSpace}
    {φ : X.obj.left → EReal} (hφ : ∀ x,X.IsLocallyAmbientPSHAt φ x)
    (f : unitDisc ⟶ X)
    (hne : ∃ t ∈ Metric.ball (0 : ℂ) 1,discPullback f φ t ≠ ⊥) :
    SGPT.PSH.SubharmonicOn (discPullback f φ) (Metric.ball (0 : ℂ) 1) := by
  have hD := discPshOn_modelPullback hφ f.hom.left (Over.w f.hom)
  have hL := hD.comp_affine discCoordinate 0
  rw [discCoordinate_preimage] at hL
  have heq : (fun t : ℂ => modelPullback f.hom.left φ (0+discCoordinate t)) =
      discPullback f φ := by
    funext t
    simp [discPullback]
  rw [heq] at hL
  exact SGPT.PSH.subharmonicOn_of_disc hL hne

private theorem discPullback_comp {X Y : SourceReducedComplexSpace}
    (f : unitDisc ⟶ Y) (F : Y ⟶ X) (φ : X.obj.left → EReal) :
    discPullback (f ≫ F) φ = discPullback f (fun y => φ (F.hom.left.base y)) := by
  funext t
  unfold discPullback modelPullback
  split_ifs <;> rfl

/-- Actual original unibranch pole propagation, using accepted local
resolution READ ONLY and produced connected FULL inverse neighborhoods. -/
theorem isClosed_setOf_eventually_eq_bot_of_isUnibranch
    {X : SourceReducedComplexSpace} (hX : X.IsUnibranch) {φ : X.obj.left → EReal}
    (hφ : ∀ x,X.IsLocallyAmbientPSHAt φ x) :
    IsClosed {x : X.obj.left | ∀ᶠ y in 𝓝 x,φ y = ⊥} := by
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨V,j,hj,hxj,T,ρ,hρ⟩ := SGPT.Unibranch.exists_local_resolution X x
  obtain ⟨v,hv⟩ := hxj
  have hV := hX.of_openImmersion j hj
  obtain ⟨U,hU,hvU,_hUN,hpreU⟩ :=
    hρ.2.exists_connected_preimage_neighborhood hV v isOpen_univ trivial
  let F : T ⟶ X := ρ ≫ j
  let u : T.obj.left → EReal := fun t => φ (F.hom.left.base t)
  have htop : ∀ t,u t ≠ ⊤ := fun t => (hφ _).ne_top
  have husc : UpperSemicontinuous u :=
    UpperSemicontinuous.comp (fun p => (hφ p).upperSemicontinuousAt) F.hom.left.base.hom.continuous
  have hdisc : ∀ f : unitDisc ⟶ T,
      (∃ t ∈ Metric.ball (0 : ℂ) 1,discPullback f u t ≠ ⊥) →
        SGPT.PSH.SubharmonicOn (discPullback f u) (Metric.ball (0 : ℂ) 1) := by
    intro f hf
    have heq := discPullback_comp f F φ
    have hn : ∃ t ∈ Metric.ball (0 : ℂ) 1,discPullback (f ≫ F) φ t ≠ ⊥ := by
      simpa only [heq] using hf
    have h := discCriterion_of_locallyAmbient hφ (f ≫ F) hn
    simpa only [heq] using h
  let Q : Set T.obj.left := {t | ∀ᶠ r in 𝓝 t,u r = ⊥}
  have hQ : IsClopen Q :=
    ⟨isClosed_setOf_eventually_eq_bot hρ.1.hasDomainCharts htop husc hdisc,
      isOpen_setOfPred_eventually_nhds⟩
  have hjU : IsOpen (j.hom.left.base '' U) := hj.base_open.isOpenMap _ hU
  have hxU : x ∈ j.hom.left.base '' U := ⟨v,hvU,hv⟩
  obtain ⟨p,⟨w,hw,hwp⟩,hpS⟩ := mem_closure_iff.mp hx _ hjU hxU
  obtain ⟨q,hq⟩ := hρ.2.surjective w
  have hqU : q ∈ ρ.hom.left.base ⁻¹' U := by change ρ.hom.left.base q ∈ U;rw [hq];exact hw
  have hFq : F.hom.left.base q = p := by
    change j.hom.left.base (ρ.hom.left.base q) = p
    rw [hq,hwp]
  have hqQ : q ∈ Q := by
    change ∀ᶠ t in 𝓝 q,φ (F.hom.left.base t) = ⊥
    have ht := (F.hom.left.base.hom.continuous.continuousAt (x := q)).tendsto
    rw [hFq] at ht
    exact ht.eventually hpS
  have hAll : ρ.hom.left.base ⁻¹' U ⊆ Q :=
    (hpreU.isPreconnected.subset_connectedComponent hqU).trans (hQ.connectedComponent_subset hqQ)
  refine Filter.mem_of_superset (hjU.mem_nhds hxU) ?_
  rintro p ⟨w,hw,rfl⟩
  obtain ⟨t,ht⟩ := hρ.2.surjective w
  have htU : t ∈ ρ.hom.left.base ⁻¹' U := by change ρ.hom.left.base t ∈ U;rw [ht];exact hw
  have hbot : ∀ᶠ r in 𝓝 t,u r = ⊥ := hAll htU
  have hb := hbot.self_of_nhds
  change φ (j.hom.left.base (ρ.hom.left.base t)) = ⊥ at hb
  rwa [ht] at hb

/-- The ORIGINAL PSH component clause internally makes the literal finite
locus dense on the SAME original unibranch topology. -/
theorem IsPSH.dense_finite_of_isUnibranch {X : SourceReducedComplexSpace}
    {φ : X.obj.left → EReal} (hφ : X.IsPSH φ) (hX : X.IsUnibranch) :
    Dense {x : X.obj.left | φ x ≠ ⊥} := by
  let S : Set X.obj.left := {x | ∀ᶠ y in 𝓝 x,φ y = ⊥}
  have hSc : IsClopen S :=
    ⟨isClosed_setOf_eventually_eq_bot_of_isUnibranch hX hφ.2,isOpen_setOfPred_eventually_nhds⟩
  have hnot : ∀ x : X.obj.left,x ∉ S := by
    intro x hx
    obtain ⟨z,hzC,hzfin⟩ := hφ.1 _ (hX.isIrreducibleComponent_connectedComponent x)
    have hzb : ∀ᶠ y in 𝓝 z,φ y = ⊥ := hSc.connectedComponent_subset hx hzC
    exact hzfin hzb.self_of_nhds
  intro x
  rw [mem_closure_iff_nhds]
  intro N hN
  by_contra hne
  apply hnot x
  refine Filter.mem_of_superset hN ?_
  intro z hz
  by_contra hzb
  exact hne ⟨z,hz,hzb⟩

/-- Finite-locus density for the ORIGINAL unbounded theta-PSH predicate,
with the actual local gauge and its intrinsic unibranch model produced internally. -/
theorem IsThetaPSH.dense_finite_of_isUnibranch {X : SourceReducedComplexSpace}
    {θ : SpaceForm X 2} {φ : X.obj.left → EReal}
    (hφ : X.IsThetaPSH θ φ) (hX : X.IsUnibranch) :
    Dense {x : X.obj.left | φ x ≠ ⊥} := by
  intro x
  rw [mem_closure_iff_nhds]
  intro N hN
  obtain ⟨e,⟨c,hc⟩,_he,g,_hg,_hres,hcorr⟩ := hφ x
  let j : sourceReducedComplexSpaceModel e.ambient e.carrier e.analytic ⟶ X :=
    ObjectProperty.homMk (Over.homMk e.map e.overPoint)
  have hmodel := hX.of_openImmersion j e.isOpenImmersion
  have hd := hcorr.dense_finite_of_isUnibranch hmodel
  have hcN : j.hom.left.base ⁻¹' N ∈ 𝓝 c := by
    have ht := (j.hom.left.base.hom.continuous.continuousAt (x := c)).tendsto
    change Filter.Tendsto j.hom.left.base (𝓝 c) (𝓝 (e.toPoint c)) at ht
    rw [hc] at ht
    exact ht.eventually hN
  obtain ⟨z,hzN,hzfinite⟩ := mem_closure_iff_nhds.mp (hd c) _ hcN
  refine ⟨e.toPoint z,hzN,?_⟩
  exact (EReal.add_ne_bot_iff.mp hzfinite).2

end SGPT.Unibranch.SourceReducedComplexSpace
