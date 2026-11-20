import SGPT.Unibranch.KS3GoodChartShrink
import SGPT.Unibranch.KS3MonomialWeight
import SGPT.Unibranch.KS3GraphRelation
import SGPT.Foundations.Analysis.Pending.HolomorphicGermAlgebra
import SGPT.Foundations.Analysis.Pending.HironakaSingularSubspaceBlowupLift

/-!
# Good charts on a blowup from graph charts

Lane KS3 (Kähler preservation under blowups, `def:unibranch:L212`).  Let `p : Y → X` be the
blowup of `X` along an analytic subset `C` (reduced ideal), `e` a local embedding of `X` carrying
a Kähler ambient form `v` (restricting the Kähler form `ω` of `X`), `g` a graph chart of the
ideal of `C` on `e` (generators `G : O → ℂ^r`), `π : Z → O × ℂ^r` the blowup of the zero plane,
and `L` the open immersion of the strict transform `Γ'` of the graph of `G` into `Y` over the
graph chart (`KS3GraphBlowup.exists_localOpenImmersion`).  Assume that near the image of a point
`ζ ∈ Γ'` the weight `U` of `X` is `c₀ ‖G‖² + Σ_x c_x ‖B_x G‖²` with `c₀ > 0`, `c_x ≥ 0` at the
base point.  Then (`exists_goodChart`) `L(ζ)` lies in a good chart
(`KS3BlowupKahlerForm.GoodChart`) of `Y`:

* local embedding of `Y`: the chart of `Z` at `ζ`, restricted to `Γ'`, composed with `L`;
* `P` = the `O`-coordinate of `π`, `H = π₂ - G ∘ π₁` (equations of `Γ'`);
* `t = w_j` and `R = monomialWeight ∘ w` in monomial coordinates `w`
  (`KS3BlowupMonomial.exists_monomialCoords`), with `U ∘ p = |t|² R` on `Γ'`;
* `t_gen`: `t = G_{j-N} ∘ P`; `hadamard`: by the relations of `KS3GraphRelation.exists_relation`;
* density of `Γ' \ π⁻¹(zero plane)` (`dense_preimage_compl_centre`);
* positivity of `ddᶜ log R` on the kernel of `(dP, dH)` = the kernel of `dπ`
  (`KS3MonomialWeight.smoothDDC_log_monomialWeight_pos`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.KS3BlowupLocalChart

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.Pending ProductComplexManifold BlowupWeightLevi HolomorphicMaps
  HironakaResolutionSpaceComplex HironakaFiniteSectionProductGraph OriginalFiniteIdealGraphChart
  HironakaSingularSubspaceBlowupLift SourceReducedComplexSpace
  KS3GraphBlowup KS3GraphRelation KS3MonomialWeight KS3BlowupKahlerForm

open scoped ProductComplexManifold

variable {X Y : SourceReducedComplexSpace} {p : Y ⟶ X} {Cset : Set X.obj.left}
  {U : X.obj.left → ℝ} {om : SpaceForm X 2}

set_option maxHeartbeats 1000000 in
/-- **Good charts on the blowup from a graph chart.** -/
theorem exists_goodChart {e : LocalEmbedding X} (g : GraphChart (idealB Cset) (idealb Cset) e)
    (bl : ZeroPlaneBlowup (idealB Cset) (idealb Cset) g)
    (v : AmbientForm e.dim 2) (v_smooth : ContDiffOn ℝ ∞ v e.ambient)
    (v_closed : ∀ z ∈ e.ambient, extDeriv v z = 0)
    (v_pos : ∀ z ∈ e.ambient, IsOneOne (v z) ∧ IsStrictlyPositive (v z))
    (v_res : om.RestrictsTo e v)
    (L : ofClosedAnalytic (strictTransform (e.dim + g.r) bl.proj (graph e g.O g.G))
      (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
        bl.isBlowup g.hΓ) ⟶ Y)
    (hL : LocallyRingedSpace.IsOpenImmersion L.hom.left)
    (hLp : L ≫ p = EmbeddedBlowup.strictTransformMorphism bl.isBlowup g.hΓ ≫ g.chart)
    (hCset : ∀ (d : e.carrier) (hd : d.val ∈ g.O), e.toPoint d ∈ Cset ↔ g.G ⟨d.val, hd⟩ = 0)
    {ι : Type} [Fintype ι] {rr : ι → ℕ} {V₀ : Set (ComplexModel e.dim)} (hV₀ : IsOpen V₀)
    {c₀ : ComplexModel e.dim → ℝ} {c : ι → ComplexModel e.dim → ℝ}
    {Bm : (x : ι) → Fin (rr x) → Fin g.r → ComplexModel e.dim → ℂ}
    (hc₀s : ContDiffOn ℝ ∞ c₀ V₀) (hcs : ∀ x, ContDiffOn ℝ ∞ (c x) V₀)
    (hBm : ∀ x i l, DifferentiableOn ℂ (Bm x i l) V₀)
    (hweight : ∀ (d : e.carrier) (hd : d.val ∈ g.O), d.val.val ∈ V₀ →
      U (e.toPoint d) = c₀ d.val.val * ∑ l, Complex.normSq (g.G ⟨d.val, hd⟩ l) +
        ∑ x, c x d.val.val *
          ∑ i, Complex.normSq (∑ l, Bm x i l d.val.val * g.G ⟨d.val, hd⟩ l))
    (ζ : strictTransform (e.dim + g.r) bl.proj (graph e g.O g.G))
    (hζV₀ : (bl.proj ζ.val).1.val.val ∈ V₀) (hc₀pos : 0 < c₀ (bl.proj ζ.val).1.val.val)
    (hcnn : ∀ x, 0 ≤ c x (bl.proj ζ.val).1.val.val) :
    ∃ a : GoodChart p Cset U om, L.hom.left.base ζ ∈ range a.E.toPoint := by
  classical
  let ST := strictTransform (e.dim + g.r) bl.proj (graph e g.O g.G)
  have hST : IsComplexAnalyticSubset (n := e.dim + g.r) ST :=
    HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
      bl.isBlowup g.hΓ
  let stm := EmbeddedBlowup.strictTransformMorphism bl.isBlowup g.hΓ
  have hπ := bl.isBlowup.contMDiff
  -- the chart of `Z` at `ζ`
  let ψ : ComplexModel (e.dim + g.r) → bl.space := (chartAt (ComplexModel (e.dim + g.r)) ζ.val).symm
  let T₀ : Set (ComplexModel (e.dim + g.r)) := (chartAt (ComplexModel (e.dim + g.r)) ζ.val).target
  let u₀ : ComplexModel (e.dim + g.r) := chartAt (ComplexModel (e.dim + g.r)) ζ.val ζ.val
  have hu₀t : u₀ ∈ T₀ := (chartAt (ComplexModel (e.dim + g.r)) ζ.val).map_source
    (mem_chart_source _ ζ.val)
  have hψu₀ : ψ u₀ = ζ.val :=
    (chartAt (ComplexModel (e.dim + g.r)) ζ.val).left_inv (mem_chart_source _ ζ.val)
  -- the local embedding of `Y`
  let E : LocalEmbedding Y :=
    { dim := e.dim + g.r
      ambient := chartImage (n := e.dim + g.r) ζ.val
      carrier := chartTrace (n := e.dim + g.r) ST ζ.val
      analytic := isComplexAnalyticSubset_chartTrace hST ζ.val
      map := chartModelMap (n := e.dim + g.r) ST ζ.val ≫ L.hom.left
      isOpenImmersion := by
        let _ := hL
        infer_instance
      overPoint := by
        rw [Category.assoc, Over.w L.hom]
        exact chartModelMap_point (n := e.dim + g.r) ST ζ.val }
  let zpt : E.carrier → ST := fun c => (chartModelMap (n := e.dim + g.r) ST ζ.val).base c
  have hzpt : ∀ c : E.carrier, (zpt c).val = ψ c.val.val := fun _ => rfl
  have hEpt : ∀ c : E.carrier, E.toPoint c = L.hom.left.base (zpt c) := fun _ => rfl
  -- the graph and the projection to `X`
  have hgraph : ∀ c : E.carrier, bl.proj (ψ c.val.val) ∈ graph e g.O g.G := fun c =>
    (stm.hom.left.base (zpt c)).property
  have hpL : ∀ c : E.carrier, p.hom.left.base (E.toPoint c) =
      e.toPoint ⟨(bl.proj (ψ c.val.val)).1.val, (hgraph c).1⟩ := fun c =>
    congrArg (fun k => k.hom.left.base (zpt c)) hLp
  have hGS : ∀ c : E.carrier, g.G (bl.proj (ψ c.val.val)).1 = (bl.proj (ψ c.val.val)).2 :=
    fun c => (hgraph c).2.symm
  -- monomial coordinates at `ζ`
  obtain ⟨j, hj, Om, W, hOm, hζOm, hWs, -, hsnd, hfst, hinj, hker⟩ :=
    KS3BlowupMonomial.exists_monomialCoords bl.isBlowup ζ.val
  have hj' : Fin.natAdd e.dim (⟨j.1 - e.dim, by omega⟩ : Fin g.r) = j :=
    Fin.ext (by simp; omega)
  -- the extension of the generators
  let ιO : g.O → ComplexModel e.dim := fun o => o.val.val
  have hιO : ∀ o o' : g.O, chartAt (ComplexModel e.dim) o o' = ιO o' := fun _ _ => rfl
  have hιOinj : Function.Injective ιO := fun a b h => Subtype.ext (Subtype.ext h)
  have hιOopen : IsOpenMap ιO :=
    e.ambient.isOpen.isOpenMap_subtype_val.comp g.O.isOpen.isOpenMap_subtype_val
  have hιOcont : Continuous ιO := continuous_subtype_val.comp continuous_subtype_val
  let Gh : ComplexModel e.dim → ComplexModel g.r := Function.extend ιO g.G 0
  have hGh : ∀ o, ContDiffAt ℂ ∞ Gh (ιO o) :=
    contDiffAt_extend_of_contMDiff ιO hιO hιOinj g.hG
  have hGhapp : ∀ o, Gh (ιO o) = g.G o := fun o => hιOinj.extend_apply _ _ _
  -- the coordinate functions
  let Pf : ComplexModel (e.dim + g.r) → ComplexModel e.dim := fun u => (bl.proj (ψ u)).1.val.val
  let Sf : ComplexModel (e.dim + g.r) → ComplexModel g.r := fun u => (bl.proj (ψ u)).2
  let Hf : ComplexModel (e.dim + g.r) → ComplexModel g.r := fun u => Sf u - Gh (Pf u)
  let Ψ : ComplexModel (e.dim + g.r) → ComplexModel (e.dim + g.r) := fun u => W (ψ u)
  let t : ComplexModel (e.dim + g.r) → ℂ := fun u => Ψ u j
  let P₀ : ComplexModel e.dim := (bl.proj ζ.val).1.val.val
  let Q : ComplexModel (e.dim + g.r) → ComplexModel e.dim := baseMap (r := g.r) P₀
  let Rf : ComplexModel (e.dim + g.r) → ℝ := fun u => monomialWeight j Q c₀ c Bm (Ψ u)
  -- holomorphy
  have hψ : ∀ u ∈ T₀, ContMDiffAt 𝓘(ℂ, ComplexModel (e.dim + g.r))
      𝓘(ℂ, ComplexModel (e.dim + g.r)) ∞ ψ u := fun u hu =>
    (contMDiffOn_chart_symm (I := 𝓘(ℂ, ComplexModel (e.dim + g.r))) (n := ∞)).contMDiffAt
      ((chartAt (ComplexModel (e.dim + g.r)) ζ.val).open_target.mem_nhds hu)
  have hval : ContMDiff 𝓘(ℂ, ComplexModel e.dim) 𝓘(ℂ, ComplexModel e.dim) ∞
      (fun o : g.O => o.val.val) := contMDiff_subtype_val.comp contMDiff_subtype_val
  have hPf : ∀ u ∈ T₀, ContDiffAt ℂ ∞ Pf u := fun u hu =>
    contMDiffAt_iff_contDiffAt.mp
      ((((hval.comp ProductComplexManifold.contMDiff_fst).comp hπ) (ψ u)).comp u (hψ u hu))
  have hSf : ∀ u ∈ T₀, ContDiffAt ℂ ∞ Sf u := fun u hu =>
    contMDiffAt_iff_contDiffAt.mp
      (((ProductComplexManifold.contMDiff_snd.comp hπ) (ψ u)).comp u (hψ u hu))
  let Ω₀ : Set (ComplexModel (e.dim + g.r)) := T₀ ∩ ψ ⁻¹' Om
  have hΩ₀ : IsOpen Ω₀ := (chartAt (ComplexModel (e.dim + g.r)) ζ.val).isOpen_inter_preimage_symm hOm
  have hΨ : ∀ u ∈ Ω₀, ContDiffAt ℂ ∞ Ψ u := fun u hu =>
    contMDiffAt_iff_contDiffAt.mp ((hWs (ψ u) hu.2).comp u (hψ u hu.1))
  have hHf : ∀ u ∈ T₀, ContDiffAt ℂ ∞ Hf u := fun u hu =>
    (hSf u hu).sub (show ContDiffAt ℂ ∞ (Gh ∘ Pf) u from (hGh (bl.proj (ψ u)).1).comp u (hPf u hu))
  have hPfc : ContinuousOn Pf Ω₀ := fun u hu => (hPf u hu.1).continuousAt.continuousWithinAt
  let Ω : Set (ComplexModel (e.dim + g.r)) := Ω₀ ∩ Pf ⁻¹' V₀
  have hΩ : IsOpen Ω := hPfc.isOpen_inter_preimage hΩ₀ hV₀
  have hPfu₀ : Pf u₀ = P₀ := by
    show (bl.proj (ψ u₀)).1.val.val = _
    rw [hψu₀]
  have hu₀Ω : u₀ ∈ Ω := by
    refine ⟨⟨hu₀t, ?_⟩, ?_⟩
    · show ψ u₀ ∈ Om
      rw [hψu₀]
      exact hζOm
    · show Pf u₀ ∈ V₀
      rw [hPfu₀]
      exact hζV₀
  -- the base map in monomial coordinates
  have hQΨ : ∀ u ∈ Ω₀, Q (Ψ u) = Pf u := by
    intro u hu
    ext i
    rw [baseMap_apply]
    have h := hfst (ψ u) hu.2 i
    change (bl.proj (ψ u)).1.val.val i - P₀ i = W (ψ u) (Fin.castAdd g.r i) at h
    change P₀ i + W (ψ u) (Fin.castAdd g.r i) = (bl.proj (ψ u)).1.val.val i
    rw [← h]
    ring
  -- the second coordinate in monomial coordinates
  have hSt : ∀ u ∈ Ω₀, ∀ l, Sf u l = t u * hatCoord j (Ψ u) (Fin.natAdd e.dim l) := fun u hu l =>
    hsnd (ψ u) hu.2 l
  -- the base point of the chart
  have hc₀mem : (⟨u₀, hu₀t⟩ : chartImage (n := e.dim + g.r) ζ.val) ∈
      chartTrace (n := e.dim + g.r) ST ζ.val := by
    show ψ u₀ ∈ ST
    rw [hψu₀]
    exact ζ.property
  let c₀pt : E.carrier := ⟨⟨u₀, hu₀t⟩, hc₀mem⟩
  have hc₀pt : E.toPoint c₀pt = L.hom.left.base ζ := by
    rw [hEpt]
    congr 1
    exact Subtype.ext hψu₀
  -- weight data
  have hQu₀ : Q (Ψ u₀) = P₀ := (hQΨ u₀ hu₀Ω.1).trans hPfu₀
  have hRpos : 0 < Rf u₀ := by
    show 0 < monomialWeight j Q c₀ c Bm (Ψ u₀)
    refine monomialWeight_pos j hj ?_ ?_
    · rw [hQu₀]
      exact hc₀pos
    · intro x
      rw [hQu₀]
      exact hcnn x
  have hWsm := contDiffOn_monomialWeight j (contDiff_baseMap (r := g.r) P₀) hV₀ hc₀s hcs hBm
  have hΨmaps : MapsTo Ψ Ω (Q ⁻¹' V₀) := fun u hu => by
    show Q (Ψ u) ∈ V₀
    rw [hQΨ u hu.1]
    exact hu.2
  have hΨon : ContDiffOn ℂ ∞ Ψ Ω := fun u hu => (hΨ u hu.1).contDiffWithinAt
  have hRsm : ContDiffOn ℝ ∞ Rf Ω := hWsm.comp (hΨon.restrict_scalars ℝ) hΨmaps
  refine Exists.elim (KS3GoodChartShrink.exists_goodChart_of_nhds (p := p) (Cset := Cset) (U := U)
    (om := om) E c₀pt hΩ hu₀Ω e v v_smooth v_closed v_pos v_res Pf
    (fun u hu => (hPf u hu.1.1).contDiffWithinAt) (fun u _ => (bl.proj (ψ u)).1.val.property)
    (fun c _ => ⟨⟨(bl.proj (ψ c.val.val)).1.val, (hgraph c).1⟩, rfl, (hpL c).symm⟩)
    t (fun u hu => ((EuclideanSpace.proj j : ComplexModel (e.dim + g.r) →L[ℂ] ℂ).contDiff.contDiffAt.comp
      u (hΨ u hu.1)).contDiffWithinAt)
    Rf hRsm hRpos ?factor Hf (fun u hu => (hHf u hu.1.1).contDiffWithinAt) ?Hzero ?tgen ?hadamard
    ?dense ?hfib) (fun a ha => ⟨a, hc₀pt ▸ ha⟩)
  case factor =>
    intro y hy
    have hd : (bl.proj (ψ y.val.val)).1.val ∈ g.O := (bl.proj (ψ y.val.val)).1.property
    have hw := hweight ⟨(bl.proj (ψ y.val.val)).1.val, (hgraph y).1⟩ hd hy.2
    have hG : ∀ l, g.G ⟨(bl.proj (ψ y.val.val)).1.val, hd⟩ l =
        t y.val.val * hatCoord j (Ψ y.val.val) (Fin.natAdd e.dim l) := by
      intro l
      have h1 : g.G ⟨(bl.proj (ψ y.val.val)).1.val, hd⟩ = (bl.proj (ψ y.val.val)).2 := hGS y
      rw [h1]
      exact hSt _ hy.1 l
    have hfac := sum_eq_normSq_mul_monomialWeight j (Q := Q) (c₀ := c₀) (c := c) (Bm := Bm)
      (Ψ y.val.val) (t y.val.val) _ hG
    rw [hQΨ _ hy.1] at hfac
    rw [hpL y, hw]
    exact hfac
  case Hzero =>
    intro c _
    show (bl.proj (ψ c.val.val)).2 - Gh (ιO (bl.proj (ψ c.val.val)).1) = 0
    rw [hGhapp, hGS c, sub_self]
  case tgen =>
    intro c hc _
    let j' : Fin g.r := ⟨j.1 - e.dim, by omega⟩
    refine ⟨range ιO, isOpen_range_of_chart_eq ιO hιO, ⟨(bl.proj (ψ c.val.val)).1, rfl⟩,
      fun x => Gh x j', ?_, ?_, Ω₀, hΩ₀, hc.1, ?_⟩
    · rintro _ ⟨o, rfl⟩
      exact ((EuclideanSpace.proj j' : ComplexModel g.r →L[ℂ] ℂ).differentiableAt.comp _
        ((hGh o).differentiableAt (by simp))).differentiableWithinAt
    · rintro d ⟨o, ho⟩ hdC
      have hdo : d.val = o.val := (Subtype.ext ho).symm
      have hd : d.val ∈ g.O := hdo ▸ o.property
      have h0 := (hCset d hd).mp hdC
      have hoeq : o = ⟨d.val, hd⟩ := Subtype.ext hdo.symm
      show Gh d.val.val j' = 0
      rw [← ho, hGhapp, hoeq, h0]
      rfl
    · intro c' hc'
      show t c'.val.val = Gh (ιO (bl.proj (ψ c'.val.val)).1) j'
      rw [hGhapp, hGS c']
      have h := hSt _ hc' j'
      change (bl.proj (ψ c'.val.val)).2 j' = _ at h
      rw [h, hj', KS3MonomialWeight.hatCoord_self, mul_one]
  case hadamard =>
    intro c hc _ V hV hPV f hf hf0
    let oc : (Subtype.val : g.O → e.ambient) ⁻¹' e.carrier := ⟨(bl.proj (ψ c.val.val)).1, (hgraph c).1⟩
    let f' : g.O → ℂ := fun o => f o.val.val
    have hF : HolomorphicAt e.dim f (oc.val.val.val) := by
      filter_upwards [hV.mem_nhds hPV] with w hw
      exact mdifferentiableAt_iff_differentiableAt.mpr ((hf w hw).differentiableAt (hV.mem_nhds hw))
    have hf' : HolomorphicAt e.dim f' oc.val :=
      (holomorphicAt_comp_val_iff g.O).mpr ((holomorphicAt_comp_val_iff e.ambient).mpr hF)
    have hf0' : ∀ᶠ u in 𝓝 oc.val, ∀ h : u.val ∈ e.carrier,
        e.toPoint ⟨u.val, h⟩ ∈ Cset → f' u = 0 := by
      filter_upwards [(hV.preimage hιOcont).mem_nhds hPV] with u hu h hC
      exact hf0 ⟨u.val, h⟩ hu hC
    obtain ⟨A, hA, hrel⟩ := exists_relation g oc f' hf' hf0'
    let F : Fin g.r → ComplexModel e.dim → ℂ := fun l =>
      extendOpens e.ambient (extendOpens g.O (A l))
    have hFapp : ∀ l (o : g.O), F l (ιO o) = A l o := fun l o => by
      show extendOpens e.ambient (extendOpens g.O (A l)) o.val.1 = A l o
      rw [extendOpens_val, extendOpens_val]
    have hFhol : ∀ l, HolomorphicAt e.dim (F l) (ιO oc.val) := fun l =>
      (holomorphicAt_iff_extendOpens e.ambient).mp ((holomorphicAt_iff_extendOpens g.O).mp (hA l))
    have hev : ∀ᶠ w in 𝓝 (ιO oc.val), ∀ l, DifferentiableAt ℂ (F l) w :=
      Filter.eventually_all.mpr fun l =>
        (hFhol l).mono fun w hw => mdifferentiableAt_iff_differentiableAt.mp hw
    obtain ⟨S₁, hS₁sub, hS₁open, hS₁mem⟩ := mem_nhds_iff.mp hrel
    obtain ⟨S₂, hS₂sub, hS₂open, hS₂mem⟩ := mem_nhds_iff.mp hev
    let V' : Set (ComplexModel (e.dim + g.r)) := Ω₀ ∩ Pf ⁻¹' (ιO '' S₁ ∩ S₂)
    have hV' : IsOpen V' := hPfc.isOpen_inter_preimage hΩ₀ ((hιOopen _ hS₁open).inter hS₂open)
    refine ⟨V', hV', ⟨hc.1, ⟨oc.val, hS₁mem, rfl⟩, hS₂mem⟩,
      fun u => ∑ l, F l (Pf u) * hatCoord j (Ψ u) (Fin.natAdd e.dim l), ?_, ?_⟩
    · intro u hu
      refine (DifferentiableAt.fun_sum fun l _ => ?_).differentiableWithinAt
      have hFd : DifferentiableAt ℂ (F l) (Pf u) := hS₂sub hu.2.2 l
      have hPd : DifferentiableAt ℂ Pf u := (hPf u hu.1.1).differentiableAt (by simp)
      have hhd : DifferentiableAt ℂ (fun u => hatCoord j (Ψ u) (Fin.natAdd e.dim l)) u :=
        ((KS3MonomialWeight.contDiff_hatCoord j (Fin.natAdd e.dim l)).differentiable (by simp)
          (Ψ u)).comp u ((hΨ u hu.1).differentiableAt (by simp))
      exact (hFd.comp u hPd).mul hhd
    · intro c' hc'
      obtain ⟨o'', ho''S, ho''⟩ := hc'.2.1
      have ho''eq : o'' = (bl.proj (ψ c'.val.val)).1 := hιOinj ho''
      have hrel' := hS₁sub (ho''eq ▸ ho''S) (hgraph c').1
      change f (Pf c'.val.val) = ∑ l, A l (bl.proj (ψ c'.val.val)).1 *
        g.G (bl.proj (ψ c'.val.val)).1 l at hrel'
      rw [hrel', Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hGS c', hSt _ hc'.1 l]
      show A l (bl.proj (ψ c'.val.val)).1 * (t c'.val.val * _) =
        t c'.val.val * (F l (ιO (bl.proj (ψ c'.val.val)).1) * _)
      rw [hFapp]
      ring
  case dense =>
    intro c
    have hD := dense_preimage_compl_centre bl.isBlowup g.hΓ.isClosed g.hd
    have hzopen : Topology.IsOpenEmbedding zpt :=
      (inferInstance : LocallyRingedSpace.IsOpenImmersion
        (chartModelMap (n := e.dim + g.r) ST ζ.val)).base_open
    have h1 : c ∈ zpt ⁻¹' closure ((strictTransformProjection bl.isBlowup g.hΓ.isClosed).base ⁻¹'
        {x : graph e g.O g.G | x.val ∉ zeroPlane g.O g.r}) := by
      rw [hD.closure_eq]
      trivial
    rw [hzopen.isOpenMap.preimage_closure_eq_closure_preimage hzopen.continuous] at h1
    refine closure_mono ?_ h1
    intro c' hc'
    have hne : (bl.proj (ψ c'.val.val)).2 ≠ 0 := hc'
    show p.hom.left.base (E.toPoint c') ∉ Cset
    rw [hpL c', hCset _ (bl.proj (ψ c'.val.val)).1.property]
    show g.G (bl.proj (ψ c'.val.val)).1 ≠ 0
    rw [hGS c']
    exact hne
  case hfib =>
    intro ξ hξ hP0 hH0
    change fderiv ℝ Pf u₀ ξ = 0 at hP0
    change fderiv ℝ Hf u₀ ξ = 0 at hH0
    have hPd : HasFDerivAt Pf (fderiv ℝ Pf u₀) u₀ :=
      (((hPf u₀ hu₀t).differentiableAt (by simp)).restrictScalars ℝ).hasFDerivAt
    have hSd : HasFDerivAt Sf (fderiv ℝ Sf u₀) u₀ :=
      (((hSf u₀ hu₀t).differentiableAt (by simp)).restrictScalars ℝ).hasFDerivAt
    have hGd : HasFDerivAt Gh (fderiv ℝ Gh (Pf u₀)) (Pf u₀) :=
      (((hGh (bl.proj (ψ u₀)).1).differentiableAt (by simp)).restrictScalars ℝ).hasFDerivAt
    have hHd : HasFDerivAt Hf (fderiv ℝ Sf u₀ - (fderiv ℝ Gh (Pf u₀)).comp (fderiv ℝ Pf u₀)) u₀ :=
      hSd.sub (hGd.comp u₀ hPd)
    have hS0 : fderiv ℝ Sf u₀ ξ = 0 := by
      have h1 : fderiv ℝ Hf u₀ ξ = fderiv ℝ Sf u₀ ξ - fderiv ℝ Gh (Pf u₀) (fderiv ℝ Pf u₀ ξ) := by
        rw [hHd.fderiv]
        rfl
      rw [hH0, hP0, map_zero, sub_zero] at h1
      exact h1.symm
    -- `ξ` is in the kernel of `dπ`
    have hcoord : coordinateMap bl.proj (complexChartAt (n := e.dim + g.r) ζ.val)
        (complexChartAt (n := e.dim + g.r) (bl.proj ζ.val)) =
          fun u => prodModelEquiv e.dim g.r (Pf u, Sf u) := by
      funext u
      change prodModelEquiv e.dim g.r
        (chartAt (ComplexModel e.dim) (bl.proj ζ.val).1 (bl.proj (ψ u)).1,
          chartAt (ComplexModel g.r) (bl.proj ζ.val).2 (bl.proj (ψ u)).2) = _
      rw [chartAt_self_eq]
      rfl
    have hmf : mfderiv 𝓘(ℂ, ComplexModel (e.dim + g.r)) 𝓘(ℂ, ComplexModel (e.dim + g.r))
        bl.proj ζ.val ξ = 0 := by
      rw [← BlowupFibreDirection.fderiv_coordinateMap_eq_mfderiv hπ ζ.val ξ, hcoord]
      have hd : HasFDerivAt (fun u => prodModelEquiv e.dim g.r (Pf u, Sf u))
          (((prodModelEquiv e.dim g.r : (ComplexModel e.dim × ComplexModel g.r) →L[ℂ]
            ComplexModel (e.dim + g.r)).restrictScalars ℝ).comp
            ((fderiv ℝ Pf u₀).prod (fderiv ℝ Sf u₀))) u₀ :=
        ((prodModelEquiv e.dim g.r : (ComplexModel e.dim × ComplexModel g.r) →L[ℂ]
          ComplexModel (e.dim + g.r)).restrictScalars ℝ).hasFDerivAt.comp u₀ (hPd.prodMk hSd)
      rw [hd.fderiv]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, hP0, hS0,
        ContinuousLinearMap.coe_restrictScalars', ContinuousLinearEquiv.coe_coe]
      exact map_zero (prodModelEquiv e.dim g.r)
    have hv0 := hker ξ hmf
    have hvne := hinj ξ hξ
    -- the chain rule for `ddᶜ`
    let ρ : ComplexModel (e.dim + g.r) → ℝ := fun w => Real.log (monomialWeight j Q c₀ c Bm w)
    let U₁ : Set (ComplexModel (e.dim + g.r)) := Ω ∩ Rf ⁻¹' Ioi 0
    have hU₁ : IsOpen U₁ := hRsm.continuousOn.isOpen_inter_preimage hΩ isOpen_Ioi
    have hQopen : IsOpen (Q ⁻¹' V₀) := (contDiff_baseMap (r := g.r) P₀).continuous.isOpen_preimage _ hV₀
    let V₁ : Set (ComplexModel (e.dim + g.r)) :=
      Q ⁻¹' V₀ ∩ monomialWeight j Q c₀ c Bm ⁻¹' Ioi 0
    have hV₁ : IsOpen V₁ := hWsm.continuousOn.isOpen_inter_preimage hQopen isOpen_Ioi
    have hρ : ContDiffOn ℝ ∞ ρ V₁ :=
      (hWsm.mono inter_subset_left).log fun w hw => (show (0 : ℝ) < _ from hw.2).ne'
    have hmaps : MapsTo Ψ U₁ V₁ := fun u hu => ⟨hΨmaps hu.1, hu.2⟩
    have hu₀U₁ : u₀ ∈ U₁ := ⟨hu₀Ω, hRpos⟩
    have hcomp := HolomorphicDDC.smoothDDC_comp hU₁ hV₁ (hΨon.mono inter_subset_left) hρ hmaps hu₀U₁
    have hΨd : DifferentiableAt ℂ Ψ u₀ := (hΨ u₀ hu₀Ω.1).differentiableAt (by simp)
    have hI : fderiv ℝ Ψ u₀ (Complex.I • ξ) = Complex.I • fderiv ℝ Ψ u₀ ξ := by
      rw [hΨd.fderiv_restrictScalars ℝ]
      exact (fderiv ℂ Ψ u₀).map_smul Complex.I ξ
    have hvec : (⇑(fderiv ℝ Ψ u₀) ∘ ![ξ, Complex.I • ξ]) =
        ![fderiv ℝ Ψ u₀ ξ, Complex.I • fderiv ℝ Ψ u₀ ξ] := by
      funext i
      fin_cases i
      · rfl
      · exact hI
    change 0 < smoothDDC (fun u => ρ (Ψ u)) u₀ ![ξ, Complex.I • ξ]
    rw [hcomp, ContinuousAlternatingMap.compContinuousLinearMap_apply, hvec]
    refine smoothDDC_log_monomialWeight_pos j hj P₀ hV₀ hc₀s hcs hBm ?_ ?_ ?_ hvne hv0
    · show Q (Ψ u₀) ∈ V₀
      rw [hQu₀]
      exact hζV₀
    · show 0 < c₀ (Q (Ψ u₀))
      rw [hQu₀]
      exact hc₀pos
    · intro x
      show 0 ≤ c x (Q (Ψ u₀))
      rw [hQu₀]
      exact hcnn x

end SGPT.Unibranch.KS3BlowupLocalChart
