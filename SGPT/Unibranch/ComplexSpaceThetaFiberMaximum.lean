import SGPT.Unibranch.ComplexSpaceThetaFiberDomain
import SGPT.Unibranch.ComplexSpaceThetaRegularity
import SGPT.Unibranch.ComplexSpaceAnalyticFiber

/-! Actual unbounded theta-PSH constant-fiber maximum principle on original
singular spaces. Blueprint: complex-space-theta-fiber-maximum.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.SourceReducedComplexSpace

/-- The actual gauge calculation gives open finite maximum loci on
original smooth sources in a literal constant base composite. -/
theorem IsThetaPSH.isOpen_maximumLocus_smooth_of_constant
    {X Y S : SourceReducedComplexSpace} (θ : SpaceForm X 2) (π : Y ⟶ X)
    {ψ : Y.obj.left → EReal} (hψ : Y.IsThetaPSH (SpaceForm.pullback θ π) ψ)
    (hS : S.IsSmooth) (f : S ⟶ Y) (x : X.obj.left)
    (hconst : ∀ s,π.hom.left.base (f.hom.left.base s) = x)
    (C : ℝ) (hbound : ∀ s,ψ (f.hom.left.base s) ≤ (C : EReal)) :
    IsOpen {s : S.obj.left | ψ (f.hom.left.base s) = (C : EReal)} := by
  rw [isOpen_iff_mem_nhds]
  intro s hs
  obtain ⟨d,U,F,hFo,hF,_hU,hcs,_hFU⟩ := hS.hasDomainCharts s univ isOpen_univ trivial
  obtain ⟨c,hc⟩ := hcs
  let Q : domainSpace U ⟶ Y := domainMorphism F hF ≫ f
  have hQc : ∀ a : (univ : Set U),π.hom.left.base (Q.hom.left.base a) = x :=
    fun a => hconst (F.base a)
  have hdisc := hψ.discPshOn_modelPullback_of_constant θ π Q x hQc
  change SGPT.Foundations.Analysis.DiscPshOn (modelPullback (F ≫ f.hom.left) ψ) U at hdisc
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp U.isOpen c.val.val c.val.property
  have hmax (w : ComplexModel d) (hw : w ∈ Metric.ball c.val.val r) :
      modelPullback (F ≫ f.hom.left) ψ w ≤ (C : EReal) := by
    simp only [modelPullback]
    split_ifs with hwU
    · exact hbound _
    · exact False.elim (hwU (hball hw))
  have heq : modelPullback (F ≫ f.hom.left) ψ c.val.val = (C : EReal) := by
    simp only [modelPullback,dif_pos c.val.property]
    change ψ (f.hom.left.base (F.base c)) = _
    rwa [hc]
  have heqBall := SingularMaximum.discPshOn_eqOn_ball_of_le_of_eq hdisc c.val.val hball hmax heq
  let B : Set (univ : Set U) := {z | z.val.val ∈ Metric.ball c.val.val r}
  have hB : IsOpen B := Metric.isOpen_ball.preimage
    (continuous_subtype_val.comp continuous_subtype_val)
  have hFB : IsOpen (F.base '' B) := hFo.base_open.isOpenMap B hB
  refine Filter.mem_of_superset (hFB.mem_nhds ⟨c,Metric.mem_ball_self hr,hc⟩) ?_
  rintro z ⟨q,hq,rfl⟩
  have hq' := heqBall hq
  simp only [modelPullback,dif_pos q.val.property] at hq'
  exact hq'

/-- Genuine singular-source maximum openness, using accepted local
resolution READ ONLY and the internally produced actual fiber-domain PSH. -/
theorem IsThetaPSH.isOpen_maximumLocus_of_constant
    {X Y S : SourceReducedComplexSpace} (θ : SpaceForm X 2) (π : Y ⟶ X)
    {ψ : Y.obj.left → EReal} (hψ : Y.IsThetaPSH (SpaceForm.pullback θ π) ψ)
    (f : S ⟶ Y) (x : X.obj.left) (hconst : ∀ s,π.hom.left.base (f.hom.left.base s) = x)
    (C : ℝ) (hbound : ∀ s,ψ (f.hom.left.base s) ≤ (C : EReal)) :
    IsOpen {s : S.obj.left | ψ (f.hom.left.base s) = (C : EReal)} := by
  rw [isOpen_iff_mem_nhds]
  intro s hs
  obtain ⟨V,j,hj,hsj,T,ρ,hρ⟩ := SGPT.Unibranch.exists_local_resolution S s
  obtain ⟨v,hv⟩ := hsj
  have hmaxopen := hψ.isOpen_maximumLocus_smooth_of_constant θ π hρ.1 (ρ ≫ j ≫ f) x
    (fun t => hconst _) C (fun t => hbound _)
  let B : Set T.obj.left := {t | ψ (f.hom.left.base (j.hom.left.base (ρ.hom.left.base t))) ≠ (C : EReal)}
  have hBc : IsClosed B := hmaxopen.isClosed_compl
  have hBim : IsClosed (ρ.hom.left.base '' B) := hρ.2.1.isClosedMap B hBc
  have hvB : v ∉ ρ.hom.left.base '' B := by
    rintro ⟨q,hq,hqv⟩
    apply hq
    rw [hqv,hv]
    exact hs
  have hU : IsOpen ((ρ.hom.left.base '' B)ᶜ) := hBim.isOpen_compl
  have hjU : IsOpen (j.hom.left.base '' (ρ.hom.left.base '' B)ᶜ) := hj.base_open.isOpenMap _ hU
  refine Filter.mem_of_superset (hjU.mem_nhds ⟨v,hvB,hv⟩) ?_
  rintro z ⟨w,hw,rfl⟩
  obtain ⟨q,hqw⟩ := hρ.2.surjective w
  by_contra hne
  apply hw
  refine ⟨q,?_,hqw⟩
  change ψ (f.hom.left.base (j.hom.left.base (ρ.hom.left.base q))) ≠ _
  rwa [hqw]

/-- Actual unbounded theta-PSH constancy on a compact connected ORIGINAL
singular source whose actual composite to the base is constant. -/
theorem IsThetaPSH.eq_const_of_compact_connected_pullback_of_constant
    {X Y S : SourceReducedComplexSpace} [CompactSpace S.obj.left] [ConnectedSpace S.obj.left]
    (θ : SpaceForm X 2) (π : Y ⟶ X) {ψ : Y.obj.left → EReal}
    (hψ : Y.IsThetaPSH (SpaceForm.pullback θ π) ψ) (f : S ⟶ Y) (x : X.obj.left)
    (hconst : ∀ s,π.hom.left.base (f.hom.left.base s) = x) :
    ∃ a : EReal,a ≠ ⊤ ∧ (fun s => ψ (f.hom.left.base s)) = fun _ => a := by
  let u : S.obj.left → EReal := fun s => ψ (f.hom.left.base s)
  have husc : UpperSemicontinuous u := UpperSemicontinuous.comp hψ.upperSemicontinuous f.hom.left.base.hom.continuous
  obtain ⟨s,-,hmax⟩ := (husc.upperSemicontinuousOn univ).exists_isMaxOn univ_nonempty isCompact_univ
  by_cases hsbot : u s = ⊥
  · refine ⟨⊥,bot_ne_top,funext fun t => le_antisymm ?_ bot_le⟩
    exact (hmax (mem_univ t)).trans_eq hsbot
  let C := (u s).toReal
  have hs : u s = (C : EReal) := (EReal.coe_toReal (hψ.ne_top _) hsbot).symm
  have hb : ∀ t,u t ≤ (C : EReal) := fun t => (hmax (mem_univ t)).trans_eq hs
  have hopen := hψ.isOpen_maximumLocus_of_constant θ π f x hconst C hb
  have hclosed : IsClosed {t : S.obj.left | u t = (C : EReal)} := by
    have heq : {t : S.obj.left | u t = (C : EReal)} = {t | (C : EReal) ≤ u t} := by
      ext t
      exact ⟨fun h => h.ge,fun h => le_antisymm (hb t) h⟩
    rw [heq]
    exact husc.isClosed_preimage (C : EReal)
  have hall := (show IsClopen {t : S.obj.left | u t = (C : EReal)} from
    ⟨hclosed,hopen⟩).eq_univ ⟨s,hs⟩
  refine ⟨(C : EReal),EReal.coe_ne_top _,funext fun t => ?_⟩
  have ht : t ∈ {t : S.obj.left | u t = (C : EReal)} := by rw [hall];trivial
  exact ht

/-- Actual theta-PSH is constant on the SAME actual connected proper fiber;
the form, original analytic fiber and unbounded gauge are unchanged. -/
theorem IsThetaPSH.eq_on_connected_proper_fiber {X Y : SourceReducedComplexSpace}
    (θ : SpaceForm X 2) (π : Y ⟶ X) (hp : IsProperMap π.hom.left.base)
    (x : X.obj.left) (hconn : IsConnected (π.hom.left.base ⁻¹' {x}))
    {ψ : Y.obj.left → EReal} (hψ : Y.IsThetaPSH (SpaceForm.pullback θ π) ψ)
    {a b : Y.obj.left} (ha : π.hom.left.base a = x) (hb : π.hom.left.base b = x) : ψ a = ψ b := by
  let singularThetaFiberCompact := analyticFiber_compact_of_proper π hp x
  let singularThetaFiberConnected := analyticFiber_connected_of_connected_fiber π x hconn
  have hconst (s : (analyticFiber π x).obj.left) :
      π.hom.left.base ((analyticFiberInclusion π x).hom.left.base s) = x := by
    have hr : (analyticFiberInclusion π x).hom.left.base s ∈
        range (analyticFiberInclusion π x).hom.left.base := ⟨s,rfl⟩
    rw [analyticFiberInclusion_range] at hr
    exact hr
  obtain ⟨c,-,hc⟩ := hψ.eq_const_of_compact_connected_pullback_of_constant θ π
    (analyticFiberInclusion π x) x hconst
  obtain ⟨a',ha'⟩ : a ∈ range (analyticFiberInclusion π x).hom.left.base := by
    rw [analyticFiberInclusion_range]
    exact ha
  obtain ⟨b',hb'⟩ : b ∈ range (analyticFiberInclusion π x).hom.left.base := by
    rw [analyticFiberInclusion_range]
    exact hb
  have hac := congrFun hc a'
  have hbc := congrFun hc b'
  change ψ ((analyticFiberInclusion π x).hom.left.base a') = c at hac
  change ψ ((analyticFiberInclusion π x).hom.left.base b') = c at hbc
  rw [ha'] at hac
  rw [hb'] at hbc
  exact hac.trans hbc.symm

/-- The genuine unbounded theta-PSH fiber theorem internally manufactures
unique USC descent of the SAME actual function to the SAME target topology. -/
theorem IsThetaPSH.exists_unique_usc_descent_of_connected_proper_fibers
    {X Y : SourceReducedComplexSpace} (θ : SpaceForm X 2) (π : Y ⟶ X)
    (hp : IsProperMap π.hom.left.base)
    (hconn : ∀ x : X.obj.left,IsConnected (π.hom.left.base ⁻¹' {x}))
    {ψ : Y.obj.left → EReal} (hψ : Y.IsThetaPSH (SpaceForm.pullback θ π) ψ) :
    ∃! φ : X.obj.left → EReal,UpperSemicontinuous φ ∧
      ∀ y : Y.obj.left,φ (π.hom.left.base y) = ψ y := by
  have hf : ∀ x : X.obj.left,∃ y : Y.obj.left,π.hom.left.base y = x := by
    intro x
    obtain ⟨y,hy⟩ := (hconn x).nonempty
    exact ⟨y,hy⟩
  choose s hs using hf
  let φ : X.obj.left → EReal := fun x => ψ (s x)
  have hread (y : Y.obj.left) : φ (π.hom.left.base y) = ψ y :=
    hψ.eq_on_connected_proper_fiber θ π hp (π.hom.left.base y) (hconn _) (hs _) rfl
  have huscφ : UpperSemicontinuous φ := by
    apply upperSemicontinuous_iff_isClosed_preimage.mpr
    intro a
    have hlevel : φ ⁻¹' Ici a = π.hom.left.base '' (ψ ⁻¹' Ici a) := by
      ext x
      constructor
      · intro hx
        refine ⟨s x,hx,hs x⟩
      · rintro ⟨y,hy,rfl⟩
        rwa [mem_preimage,hread]
    rw [hlevel]
    exact hp.isClosedMap _ (hψ.upperSemicontinuous.isClosed_preimage a)
  refine ⟨φ,⟨huscφ,hread⟩,?_⟩
  intro φ' hφ'
  funext x
  rw [← hs x,hφ'.2,hread]

end SGPT.Unibranch.SourceReducedComplexSpace
