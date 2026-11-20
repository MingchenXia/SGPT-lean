import SGPT.Unibranch.KS3BlowupLocalChart
import SGPT.Unibranch.KS3PartitionOfUnity
import SGPT.Unibranch.KS3KahlerResolution
import SGPT.Unibranch.OriginalSmoothCentreBlowup
import SGPT.Unibranch.IntrinsicAnalyticCentreFiniteType

/-!
# The blowup of a compact Kähler space along a smooth centre is Kähler

Lane KS3 (Kähler preservation under blowups, `def:unibranch:L212`, step (a) of the proof of the
existence of a Kähler resolution, `appendix_unibranch.tex`, `sec:unib_ext`).  This file proves
`KS3KahlerResolution.KahlerBlowupStep`: if `p : Y → X` is the blowup of a compact Kähler space
`X` along a smooth closed subspace `C` (`IsSmoothCentreBlowup p i`), then `Y` is a Kähler space
(`kahlerBlowupStep`).

Construction (the classical `p^*ω + ε ddᶜ log(|t|² R)` argument, globalized by a Blanchard weight):

* at every point of `X` a local embedding `e_x` carrying a Kähler ambient form `v_x` of `ω`
  (`SpaceForm.IsKahler`), and a graph chart `g_x` of the reduced ideal of `C` on it (generators
  `G_x`, `KS3GraphBlowup.nonempty_graphFamily`) whose strict transform is an open piece of `Y`
  (`KS3GraphBlowup.exists_localOpenImmersion`);
* a smooth partition of unity `χ_x` on `X` subordinate to the chart domains
  (`KS3PartitionOfUnity.exists_partitionOfUnity`) and the weight `U = Σ_x χ_x ‖G_x‖²`, positive
  exactly off `C` (`weight_pos_iff`);
* near every point of `X`, in the chart `e_{x₀}` with `χ_{x₀} > 0`, the weight is
  `c₀ ‖G_{x₀}‖² + Σ_x c_x ‖B_x G_{x₀}‖²` (`exists_weight_chart`), the `B_x` coming from the
  relations between the generators of two graph charts (`exists_relation_matrix`);
* `KS3BlowupLocalChart.exists_goodChart` then gives a good chart through every point of `Y`, and
  `KS3BlowupKahlerForm.isKahlerSpace_of_goodCharts` a Kähler form on the compact space `Y`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.KS3KahlerBlowupStep

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
  HironakaSingularModuleSheafStalk HironakaIntrinsicReducedCentreIdealSheaf
  OriginalFiniteIdealGraphChart HironakaFiniteSectionProductGraph SourceReducedComplexSpace
  SmoothCentreModification KS3GraphBlowup KS3GraphRelation KS3PartitionOfUnity

open scoped ProductComplexManifold

variable {X : SourceReducedComplexSpace} {Cset : Set X.obj.left}

/-! ### The norm square of the generators of a graph chart -/

open Classical in
/-- `‖G‖²` at the points of `X` in the domain of a graph chart `g` (zero elsewhere). -/
def genNormSq {e : LocalEmbedding X} (g : GraphChart (idealB Cset) (idealb Cset) e)
    (q : X.obj.left) : ℝ :=
  if h : ∃ d : e.carrier, ∃ _hd : d.val ∈ g.O, e.toPoint d = q then
    ∑ l, Complex.normSq (g.G ⟨h.choose.val, h.choose_spec.choose⟩ l) else 0

theorem genNormSq_eq {e : LocalEmbedding X} (g : GraphChart (idealB Cset) (idealb Cset) e)
    (d : e.carrier) (hd : d.val ∈ g.O) :
    genNormSq g (e.toPoint d) = ∑ l, Complex.normSq (g.G ⟨d.val, hd⟩ l) := by
  have h : ∃ d' : e.carrier, ∃ _hd : d'.val ∈ g.O, e.toPoint d' = e.toPoint d := ⟨d, hd, rfl⟩
  unfold genNormSq
  rw [dif_pos h]
  have hcd : h.choose = d := e.toPoint_injective h.choose_spec.choose_spec
  have key : ∀ (d₁ : e.carrier) (h₁ : d₁.val ∈ g.O), d₁ = d →
      g.G ⟨d₁.val, h₁⟩ = g.G ⟨d.val, hd⟩ := by
    rintro d₁ h₁ rfl
    rfl
  rw [key _ _ hcd]

theorem genNormSq_nonneg {e : LocalEmbedding X} (g : GraphChart (idealB Cset) (idealb Cset) e)
    (q : X.obj.left) : 0 ≤ genNormSq g q := by
  unfold genNormSq
  split_ifs
  · exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  · exact le_rfl

/-- A point of a graph chart lies over `C` exactly when the generators vanish there. -/
theorem mem_iff_gen_eq_zero (hC : X.IsAnalyticSubset Cset) {e : LocalEmbedding X}
    (g : GraphChart (idealB Cset) (idealb Cset) e) (d : e.carrier) (hd : d.val ∈ g.O) :
    e.toPoint d ∈ Cset ↔ g.G ⟨d.val, hd⟩ = 0 := by
  let z : graph e g.O g.G := ⟨(⟨d.val, hd⟩, g.G ⟨d.val, hd⟩), ⟨d.property, rfl⟩⟩
  have h1 := g.ne_zero_iff z
  have h2 : (chartGraphMap e g.O g.G g.hG).base z = e.toPoint d := rfl
  have h3 : (LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf
      (idealB Cset) (idealb Cset) (e.toPoint d)) = ⊤) ↔ e.toPoint d ∈ Csetᶜ := by
    rw [← OriginalSmoothCentreBlowup.intrinsic_ideal_unitLocus_eq_compl X Cset hC]
    exact Iff.rfl
  rw [h2, h3] at h1
  change g.G ⟨d.val, hd⟩ ≠ 0 ↔ e.toPoint d ∉ Cset at h1
  tauto

theorem genNormSq_eq_zero_of_mem {e : LocalEmbedding X}
    (g : GraphChart (idealB Cset) (idealb Cset) e)
    (hCg : ∀ (d : e.carrier) (hd : d.val ∈ g.O), e.toPoint d ∈ Cset ↔ g.G ⟨d.val, hd⟩ = 0)
    {q : X.obj.left} (hq : q ∈ Cset) : genNormSq g q = 0 := by
  unfold genNormSq
  split_ifs with h
  · have h0 := (hCg h.choose h.choose_spec.choose).mp
      (by rw [h.choose_spec.choose_spec]; exact hq)
    rw [h0]
    simp
  · rfl

/-! ### Local relations between two graph charts -/

/-- A carrier point has a neighbourhood whose carrier points avoid a closed set not containing
it. -/
theorem exists_nhd_not_mem (e : LocalEmbedding X) (c : e.carrier) {K : Set X.obj.left}
    (hK : IsClosed K) (hc : e.toPoint c ∉ K) :
    ∃ V : Set (ComplexModel e.dim), IsOpen V ∧ c.val.val ∈ V ∧
      ∀ d : e.carrier, d.val.val ∈ V → e.toPoint d ∉ K := by
  have hind : Topology.IsInducing (fun d : e.carrier => d.val.val) :=
    Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  have ho : IsOpen (e.toPoint ⁻¹' Kᶜ) :=
    hK.isOpen_compl.preimage e.isOpenEmbedding_toPoint.continuous
  obtain ⟨V, hV, hVeq⟩ := hind.isOpen_iff.mp ho
  refine ⟨V, hV, ?_, fun d hd => ?_⟩
  · have : c ∈ (fun d : e.carrier => d.val.val) ⁻¹' V := by rw [hVeq]; exact hc
    exact this
  · have : d ∈ (fun d : e.carrier => d.val.val) ⁻¹' V := hd
    rw [hVeq] at this
    exact this

set_option maxHeartbeats 1000000 in
/-- **Relations between the generators of two graph charts.**  Near a common point, the
generators `G'` of a second graph chart, transported to the first chart, are holomorphic
combinations `G'_i = Σ_l B_{il} G_l` of the generators of the first one. -/
theorem exists_relation_matrix {e e' : LocalEmbedding X}
    (g : GraphChart (idealB Cset) (idealb Cset) e) (g' : GraphChart (idealB Cset) (idealb Cset) e')
    (hC' : ∀ (d : e'.carrier) (hd : d.val ∈ g'.O), e'.toPoint d ∈ Cset ↔ g'.G ⟨d.val, hd⟩ = 0)
    (c : e.carrier) (hc : c.val ∈ g.O) (c' : e'.carrier) (hc' : c'.val ∈ g'.O)
    (hcc : e'.toPoint c' = e.toPoint c) :
    ∃ V : Set (ComplexModel e.dim), IsOpen V ∧ c.val.val ∈ V ∧
      ∃ B : Fin g'.r → Fin g.r → ComplexModel e.dim → ℂ, (∀ i l, DifferentiableOn ℂ (B i l) V) ∧
        ∀ d : e.carrier, d.val.val ∈ V → ∀ hd : d.val ∈ g.O,
          ∃ d' : e'.carrier, ∃ hd' : d'.val ∈ g'.O, e'.toPoint d' = e.toPoint d ∧
            ∀ i, g'.G ⟨d'.val, hd'⟩ i = ∑ l, B i l d.val.val * g.G ⟨d.val, hd⟩ l := by
  classical
  obtain ⟨W, hW, hcW, -, Hm, hHm, -, hHpt⟩ :=
    LocalEmbedding.exists_contDiff_transition e e' c ⟨c', hcc⟩
  -- the parameter maps of the two chart domains
  let ιO : g.O → ComplexModel e.dim := fun o => o.val.val
  have hιOinj : Function.Injective ιO := fun a b h => Subtype.ext (Subtype.ext h)
  have hιOopen : IsOpenMap ιO :=
    e.ambient.isOpen.isOpenMap_subtype_val.comp g.O.isOpen.isOpenMap_subtype_val
  have hιOcont : Continuous ιO := continuous_subtype_val.comp continuous_subtype_val
  let ι' : g'.O → ComplexModel e'.dim := fun o => o.val.val
  have hι' : ∀ o o' : g'.O, chartAt (ComplexModel e'.dim) o o' = ι' o' := fun _ _ => rfl
  have hι'inj : Function.Injective ι' := fun a b h => Subtype.ext (Subtype.ext h)
  let Gh : ComplexModel e'.dim → ComplexModel g'.r := Function.extend ι' g'.G 0
  have hGh : ∀ o, ContDiffAt ℂ ∞ Gh (ι' o) := contDiffAt_extend_of_contMDiff ι' hι' hι'inj g'.hG
  have hGhapp : ∀ o, Gh (ι' o) = g'.G o := fun o => hι'inj.extend_apply _ _ _
  have hHc : Hm c.val.val = c'.val.val := by
    obtain ⟨z, hz, hzpt⟩ := hHpt c hcW
    have : z = c' := e'.toPoint_injective (hzpt.trans hcc.symm)
    rw [← hz, this]
  let W₁ : Set (ComplexModel e.dim) := W ∩ Hm ⁻¹' range ι'
  have hW₁ : IsOpen W₁ :=
    hHm.continuousOn.isOpen_inter_preimage hW (isOpen_range_of_chart_eq ι' hι')
  have hcW₁ : c.val.val ∈ W₁ := ⟨hcW, ⟨⟨c'.val, hc'⟩, hHc.symm⟩⟩
  -- the transported generators
  let f : Fin g'.r → g.O → ℂ := fun i o => Gh (Hm (ιO o)) i
  let oc : (Subtype.val : g.O → e.ambient) ⁻¹' e.carrier := ⟨⟨c.val, hc⟩, c.property⟩
  have hdiff : ∀ i, ∀ w ∈ W₁, DifferentiableAt ℂ (fun w => Gh (Hm w) i) w := by
    rintro i w ⟨hwW, o, ho⟩
    have h1 : DifferentiableAt ℂ Gh (Hm w) := by
      rw [← ho]
      exact (hGh o).differentiableAt (by simp)
    exact (EuclideanSpace.proj i : ComplexModel g'.r →L[ℂ] ℂ).differentiableAt.comp w
      (h1.comp w (((hHm w hwW).contDiffAt (hW.mem_nhds hwW)).differentiableAt (by simp)))
  have hf : ∀ i, HolomorphicAt e.dim (f i) oc.val := by
    intro i
    have hF : HolomorphicAt e.dim (fun w => Gh (Hm w) i) oc.val.val.val := by
      filter_upwards [(hW₁.mem_nhds hcW₁ : W₁ ∈ 𝓝 oc.val.val.val)] with w hw
      exact mdifferentiableAt_iff_differentiableAt.mpr (hdiff i w hw)
    exact (holomorphicAt_comp_val_iff g.O).mpr ((holomorphicAt_comp_val_iff e.ambient).mpr hF)
  have hf0 : ∀ i, ∀ᶠ u in 𝓝 oc.val, ∀ h : u.val ∈ e.carrier,
      e.toPoint ⟨u.val, h⟩ ∈ Cset → f i u = 0 := by
    intro i
    filter_upwards [(hW₁.preimage hιOcont).mem_nhds hcW₁] with u hu h hC
    obtain ⟨z, hz, hzpt⟩ := hHpt ⟨u.val, h⟩ hu.1
    obtain ⟨o', ho'⟩ := hu.2
    have hzo : z.val = o'.val := Subtype.ext (hz.trans ho'.symm)
    have hzO : z.val ∈ g'.O := by rw [hzo]; exact o'.property
    have h0 := (hC' z hzO).mp (by rw [hzpt]; exact hC)
    show Gh (Hm (ιO u)) i = 0
    rw [← ho', hGhapp]
    have : o' = ⟨z.val, hzO⟩ := Subtype.ext hzo.symm
    rw [this, h0]
    rfl
  choose A hA hrel using fun i => exists_relation g oc (f i) (hf i) (hf0 i)
  let B : Fin g'.r → Fin g.r → ComplexModel e.dim → ℂ := fun i l =>
    extendOpens e.ambient (extendOpens g.O (A i l))
  have hBapp : ∀ i l (o : g.O), B i l (ιO o) = A i l o := fun i l o => by
    show extendOpens e.ambient (extendOpens g.O (A i l)) o.val.1 = A i l o
    rw [extendOpens_val, extendOpens_val]
  have hev : ∀ᶠ w in 𝓝 c.val.val, ∀ i l, DifferentiableAt ℂ (B i l) w := by
    refine Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun l => ?_
    have h := (holomorphicAt_iff_extendOpens e.ambient).mp
      ((holomorphicAt_iff_extendOpens g.O).mp (hA i l))
    exact h.mono fun w hw => mdifferentiableAt_iff_differentiableAt.mp hw
  have hrel' : ∀ᶠ u in 𝓝 oc.val, ∀ i, u.val ∈ e.carrier → f i u = ∑ l, A i l u * g.G u l :=
    Filter.eventually_all.mpr hrel
  obtain ⟨S₁, hS₁sub, hS₁open, hS₁mem⟩ := mem_nhds_iff.mp hrel'
  obtain ⟨S₂, hS₂sub, hS₂open, hS₂mem⟩ := mem_nhds_iff.mp hev
  refine ⟨W₁ ∩ (ιO '' S₁ ∩ S₂), hW₁.inter ((hιOopen _ hS₁open).inter hS₂open),
    ⟨hcW₁, ⟨oc.val, hS₁mem, rfl⟩, hS₂mem⟩, B,
    fun i l w hw => (hS₂sub hw.2.2 i l).differentiableWithinAt, ?_⟩
  intro d hdV hd
  obtain ⟨z, hz, hzpt⟩ := hHpt d hdV.1.1
  obtain ⟨o', ho'⟩ := hdV.1.2
  have hzo : z.val = o'.val := Subtype.ext (hz.trans ho'.symm)
  have hzO : z.val ∈ g'.O := by rw [hzo]; exact o'.property
  refine ⟨z, hzO, hzpt, fun i => ?_⟩
  obtain ⟨o'', ho''S, ho''⟩ := hdV.2.1
  have ho''eq : o'' = ⟨d.val, hd⟩ := hιOinj ho''
  have hr := hS₁sub (ho''eq ▸ ho''S) i d.property
  have hzG : g'.G ⟨z.val, hzO⟩ = Gh (Hm d.val.val) := by
    rw [← hGhapp]
    exact congrArg Gh hz
  rw [hzG]
  change f i ⟨d.val, hd⟩ = _
  rw [hr]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← hBapp i l ⟨d.val, hd⟩]

/-! ### The weight in a chart -/

/-- **One term of the weight in a chart.**  Near a point `c` of a graph chart `g`, the term
`χ ‖G'‖²` of a second graph chart `g'` is `c_x ‖B G‖²` with `c_x` smooth, `c_x(c) ≥ 0` and `B`
holomorphic (`c_x = 0` if `c` is off the support of `χ`). -/
theorem exists_term_chart {e e' : LocalEmbedding X}
    (g : GraphChart (idealB Cset) (idealb Cset) e) (g' : GraphChart (idealB Cset) (idealb Cset) e')
    (hC' : ∀ (d : e'.carrier) (hd : d.val ∈ g'.O), e'.toPoint d ∈ Cset ↔ g'.G ⟨d.val, hd⟩ = 0)
    {χx : X.obj.left → ℝ} (hχnn : ∀ q, 0 ≤ χx q) (hχs : IsAmbientSmooth χx)
    {Kx : Set X.obj.left} (hKc : IsClosed Kx) (hK0 : ∀ q ∉ Kx, χx q = 0)
    (hKmem : ∀ q ∈ Kx, ∃ c' : e'.carrier,
      c'.val.val ∈ range (fun o : g'.O => o.val.val) ∧ e'.toPoint c' = q)
    (c : e.carrier) (hc : c.val ∈ g.O) :
    ∃ (rx : ℕ) (V : Set (ComplexModel e.dim)) (cx : ComplexModel e.dim → ℝ)
      (Bx : Fin rx → Fin g.r → ComplexModel e.dim → ℂ),
      IsOpen V ∧ c.val.val ∈ V ∧ ContDiffOn ℝ ∞ cx V ∧ (∀ i l, DifferentiableOn ℂ (Bx i l) V) ∧
      0 ≤ cx c.val.val ∧
      ∀ (d : e.carrier) (hd : d.val ∈ g.O), d.val.val ∈ V →
        χx (e.toPoint d) * genNormSq g' (e.toPoint d) =
          cx d.val.val * ∑ i, Complex.normSq (∑ l, Bx i l d.val.val * g.G ⟨d.val, hd⟩ l) := by
  classical
  obtain ⟨O₁, hO₁, hcO₁, Fχ, hFχ, hFχeq⟩ := hχs e c
  by_cases hcK : e.toPoint c ∈ Kx
  · obtain ⟨c', ⟨o', ho'⟩, hc'pt⟩ := hKmem _ hcK
    have hc'O : c'.val ∈ g'.O := by
      have : c'.val = o'.val := Subtype.ext ho'.symm
      rw [this]
      exact o'.property
    obtain ⟨V, hV, hcV, B, hB, hrel⟩ := exists_relation_matrix g g' hC' c hc c' hc'O hc'pt
    refine ⟨g'.r, V ∩ O₁, Fχ, B, hV.inter hO₁, ⟨hcV, hcO₁⟩, hFχ.mono inter_subset_right,
      fun i l => (hB i l).mono inter_subset_left, ?_, ?_⟩
    · rw [← hFχeq c hcO₁]
      exact hχnn _
    · intro d hd hdV
      obtain ⟨d', hd', hd'pt, hG⟩ := hrel d hdV.1 hd
      rw [hFχeq d hdV.2, ← hd'pt, genNormSq_eq g' d' hd']
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [hG i]
  · obtain ⟨V, hV, hcV, hVK⟩ := exists_nhd_not_mem e c hKc hcK
    refine ⟨0, V, 0, fun i => i.elim0, hV, hcV, contDiffOn_const, fun i => i.elim0, le_rfl, ?_⟩
    intro d hd hdV
    rw [hK0 _ (hVK d hdV), zero_mul]
    simp

/-- **The weight in a chart.**  Near a point `c` of the graph chart at `x₀`, the weight
`Σ_x χ_x ‖G_x‖²` is `c₀ ‖G_{x₀}‖² + Σ_{x ≠ x₀} c_x ‖B_x G_{x₀}‖²`. -/
theorem exists_weight_chart [DecidableEq X.obj.left] (F : GraphFamily (idealB Cset) (idealb Cset))
    (hCsetG : ∀ x (d : (F.emb x).carrier) (hd : d.val ∈ (F.chart x).O),
      (F.emb x).toPoint d ∈ Cset ↔ (F.chart x).G ⟨d.val, hd⟩ = 0)
    (Fs : Finset X.obj.left) (χ : X.obj.left → X.obj.left → ℝ) (hχnn : ∀ x q, 0 ≤ χ x q)
    (hχs : ∀ x, IsAmbientSmooth (χ x)) (Kx : X.obj.left → Set X.obj.left)
    (hKc : ∀ x, IsClosed (Kx x)) (hK0 : ∀ x, ∀ q ∉ Kx x, χ x q = 0)
    (hKmem : ∀ x, ∀ q ∈ Kx x, ∃ c : (F.emb x).carrier,
      c.val.val ∈ range (fun o : (F.chart x).O => o.val.val) ∧ (F.emb x).toPoint c = q)
    (x₀ : X.obj.left) (hx₀ : x₀ ∈ Fs) (c : (F.emb x₀).carrier) (hc : c.val ∈ (F.chart x₀).O) :
    ∃ (rr : Fs.erase x₀ → ℕ) (V₀ : Set (ComplexModel (F.emb x₀).dim))
      (c₀ : ComplexModel (F.emb x₀).dim → ℝ) (cc : Fs.erase x₀ → ComplexModel (F.emb x₀).dim → ℝ)
      (Bm : (x : Fs.erase x₀) → Fin (rr x) → Fin (F.chart x₀).r → ComplexModel (F.emb x₀).dim → ℂ),
      IsOpen V₀ ∧ c.val.val ∈ V₀ ∧ ContDiffOn ℝ ∞ c₀ V₀ ∧ (∀ x, ContDiffOn ℝ ∞ (cc x) V₀) ∧
      (∀ x i l, DifferentiableOn ℂ (Bm x i l) V₀) ∧
      c₀ c.val.val = χ x₀ ((F.emb x₀).toPoint c) ∧ (∀ x, 0 ≤ cc x c.val.val) ∧
      ∀ (d : (F.emb x₀).carrier) (hd : d.val ∈ (F.chart x₀).O), d.val.val ∈ V₀ →
        ∑ x ∈ Fs, χ x ((F.emb x₀).toPoint d) * genNormSq (F.chart x) ((F.emb x₀).toPoint d) =
          c₀ d.val.val * ∑ l, Complex.normSq ((F.chart x₀).G ⟨d.val, hd⟩ l) +
            ∑ x, cc x d.val.val *
              ∑ i, Complex.normSq (∑ l, Bm x i l d.val.val * (F.chart x₀).G ⟨d.val, hd⟩ l) := by
  classical
  obtain ⟨O₀, hO₀, hcO₀, c₀, hc₀s, hc₀eq⟩ := hχs x₀ (F.emb x₀) c
  choose rr V cc Bm hV hcV hccs hBm hccnn hterm using fun x : Fs.erase x₀ =>
    exists_term_chart (F.chart x₀) (F.chart x.val) (hCsetG x.val) (hχnn x.val) (hχs x.val)
      (hKc x.val) (hK0 x.val) (hKmem x.val) c hc
  refine ⟨rr, O₀ ∩ ⋂ x, V x, c₀, cc, Bm, hO₀.inter (isOpen_iInter_of_finite hV),
    ⟨hcO₀, mem_iInter.mpr hcV⟩, hc₀s.mono inter_subset_left,
    fun x => (hccs x).mono (inter_subset_right.trans (iInter_subset _ x)),
    fun x i l => (hBm x i l).mono (inter_subset_right.trans (iInter_subset _ x)),
    (hc₀eq c hcO₀).symm, hccnn, ?_⟩
  intro d hd hdV
  rw [← Finset.add_sum_erase Fs _ hx₀, hc₀eq d hdV.1, genNormSq_eq (F.chart x₀) d hd,
    ← Finset.sum_coe_sort (Fs.erase x₀)]
  congr 1
  exact Finset.sum_congr rfl fun x _ => hterm x d hd (mem_iInter.mp hdV.2 x)

/-- A finite family of numbers with sum one has a positive member. -/
theorem exists_pos_of_sum_eq_one {α : Type*} {s : Finset α} {f : α → ℝ}
    (h : ∑ x ∈ s, f x = 1) : ∃ x ∈ s, 0 < f x := by
  by_contra hcon
  push Not at hcon
  have : ∑ x ∈ s, f x ≤ 0 := Finset.sum_nonpos hcon
  linarith

/-! ### Kähler preservation -/

set_option maxHeartbeats 1000000 in
/-- **The blowup of a compact Kähler space along a smooth centre is Kähler.** -/
theorem kahlerBlowupStep : KS3KahlerResolution.KahlerBlowupStep := by
  intro X Y S p i hp hXc hK
  classical
  have := hXc
  obtain ⟨om, hom⟩ := hK
  set Cset : Set X.obj.left := range i.hom.left.base with hCsetdef
  have hCa : X.IsAnalyticSubset Cset := hp.2.2.2.1
  have hCint : interior Cset = ∅ := hp.2.2.2.2.1
  have hpB : IsIdealBlowup p (idealB Cset) (idealb Cset) := hp.2.2.2.2.2.1
  have hpb : IsProperBimeromorphic p := hp.2.2.2.2.2.2
  let _ : (idealB Cset).IsFiniteType :=
    IntrinsicAnalyticCentreFiniteType.intrinsicReducedCentreIdealModule_isFiniteType X Cset hCa
  have hDense : Dense {x : X.obj.left | LinearMap.range (stalkInclusionLinearMap
      X.obj.left.toSheafedSpace.sheaf (idealB Cset) (idealb Cset) x) = ⊤} := by
    change Dense {x : X.obj.left | LinearMap.range (stalkInclusionLinearMap
      X.obj.left.toSheafedSpace.sheaf (intrinsicReducedCentreIdealModule X.obj.left Cset)
      (intrinsicReducedCentreIdealInclusion X.obj.left Cset) x) = ⊤}
    rw [OriginalSmoothCentreBlowup.intrinsic_ideal_unitLocus_eq_compl X Cset hCa]
    exact interior_eq_empty_iff_dense_compl.mp hCint
  -- Kähler charts and graph charts
  choose emb hemb v hvs hvc hvp hvr using hom
  obtain ⟨F, hF⟩ := nonempty_graphFamily (idealB Cset) (idealb Cset) hDense emb hemb
  subst hF
  have hCsetG : ∀ x (d : (F.emb x).carrier) (hd : d.val ∈ (F.chart x).O),
      (F.emb x).toPoint d ∈ Cset ↔ (F.chart x).G ⟨d.val, hd⟩ = 0 := fun x d hd =>
    mem_iff_gen_eq_zero hCa (F.chart x) d hd
  choose L hLp hLopen hLrange using fun x =>
    exists_localOpenImmersion (idealB Cset) (idealb Cset) hpB F x
  -- the partition of unity and the weight
  let K : Cover X :=
    { E := F.emb
      w := fun x => ⟨(F.point x).val.1.val, (F.point x).property.1⟩
      hw := F.point_over
      U := fun x => range (fun o : (F.chart x).O => o.val.val)
      isOpen_U := fun x => isOpen_range_of_chart_eq _ (fun _ _ => rfl)
      mem_U := fun x => ⟨(F.point x).val.1, rfl⟩
      U_sub := fun x => by
        rintro _ ⟨o, rfl⟩
        exact o.val.property }
  obtain ⟨Fs, χ, hχnn, hχsum, hχs, hχsupp⟩ := exists_partitionOfUnity K
  choose Kx hKc hK0 hKmem using hχsupp
  let U : X.obj.left → ℝ := fun q => ∑ x ∈ Fs, χ x q * genNormSq (F.chart x) q
  have hU : ∀ q, 0 < U q ↔ q ∉ Cset := by
    intro q
    constructor
    · intro hpos hq
      have h0 : U q = 0 := Finset.sum_eq_zero fun x _ => by
        rw [genNormSq_eq_zero_of_mem (F.chart x) (hCsetG x) hq, mul_zero]
      linarith
    · intro hq
      obtain ⟨x₀, hx₀, hχpos⟩ := exists_pos_of_sum_eq_one (hχsum q)
      have hqK : q ∈ Kx x₀ := by
        by_contra h
        rw [hK0 x₀ q h] at hχpos
        exact lt_irrefl 0 hχpos
      obtain ⟨c, ⟨o, ho⟩, hcpt⟩ := hKmem x₀ q hqK
      have hcO : c.val ∈ (F.chart x₀).O := by
        have : c.val = o.val := Subtype.ext ho.symm
        rw [this]
        exact o.property
      have hgpos : 0 < genNormSq (F.chart x₀) q := by
        rw [← hcpt, genNormSq_eq _ c hcO, KS3FibreLevi.sum_normSq_eq_norm_sq]
        have hne : (F.chart x₀).G ⟨c.val, hcO⟩ ≠ 0 := fun h =>
          hq (hcpt ▸ (hCsetG x₀ c hcO).mpr h)
        exact pow_pos (norm_pos_iff.mpr hne) 2
      have hle := Finset.single_le_sum (f := fun x => χ x q * genNormSq (F.chart x) q)
        (fun x _ => mul_nonneg (hχnn x q) (genNormSq_nonneg _ _)) hx₀
      exact lt_of_lt_of_le (mul_pos hχpos hgpos) hle
  -- `Y` is compact
  have : CompactSpace Y.obj.left := by
    have h := hpb.1.isCompact_preimage (isCompact_univ (X := X.obj.left))
    rw [preimage_univ] at h
    exact ⟨h⟩
  refine KS3BlowupKahlerForm.isKahlerSpace_of_goodCharts (p := p) (Cset := Cset) (U := U)
    (om := om) hU ?_
  intro y
  -- a chart index with `χ_{x₀}(p y) > 0`
  obtain ⟨x₀, hx₀, hχpos⟩ := exists_pos_of_sum_eq_one (hχsum (p.hom.left.base y))
  have hyK : p.hom.left.base y ∈ Kx x₀ := by
    by_contra h
    rw [hK0 x₀ _ h] at hχpos
    exact lt_irrefl 0 hχpos
  obtain ⟨c, ⟨o, ho⟩, hcpt⟩ := hKmem x₀ _ hyK
  have hcO : c.val ∈ (F.chart x₀).O := by
    have : c.val = o.val := Subtype.ext ho.symm
    rw [this]
    exact o.property
  -- `y` lies in the strict transform of the graph chart at `x₀`
  have hyL : y ∈ range (L x₀).hom.left.base := by
    rw [hLrange x₀]
    exact ⟨⟨(⟨c.val, hcO⟩, (F.chart x₀).G ⟨c.val, hcO⟩), ⟨c.property, rfl⟩⟩, hcpt⟩
  obtain ⟨ζ, hζ⟩ := hyL
  have hgr : (F.blowup x₀).proj ζ.val ∈ graph (F.emb x₀) (F.chart x₀).O (F.chart x₀).G :=
    ((EmbeddedBlowup.strictTransformMorphism (F.blowup x₀).isBlowup
      (F.chart x₀).hΓ).hom.left.base ζ).property
  have h1 : p.hom.left.base ((L x₀).hom.left.base ζ) =
      (F.emb x₀).toPoint ⟨((F.blowup x₀).proj ζ.val).1.val, hgr.1⟩ :=
    congrArg (fun k => k.hom.left.base ζ) (hLp x₀)
  rw [hζ, ← hcpt] at h1
  have hζc : ((F.blowup x₀).proj ζ.val).1.val = c.val :=
    congrArg Subtype.val ((F.emb x₀).toPoint_injective h1).symm
  -- the weight near `c`
  obtain ⟨rr, V₀, c₀, cc, Bm, hV₀, hcV₀, hc₀s, hccs, hBm, hc₀eq, hccnn, hweight⟩ :=
    exists_weight_chart F hCsetG Fs χ hχnn hχs Kx hKc hK0 hKmem x₀ hx₀ c hcO
  obtain ⟨a, ha⟩ := KS3BlowupLocalChart.exists_goodChart (p := p) (U := U) (om := om)
    (F.chart x₀) (F.blowup x₀) (v x₀) (hvs x₀) (hvc x₀) (hvp x₀) (hvr x₀) (L x₀) (hLopen x₀)
    (hLp x₀) (hCsetG x₀) hV₀ hc₀s hccs hBm hweight ζ
    (by rw [hζc]; exact hcV₀) (by rw [hζc, hc₀eq, hcpt]; exact hχpos)
    (fun x => by rw [hζc]; exact hccnn x)
  exact ⟨a, hζ ▸ ha⟩

end SGPT.Unibranch.KS3KahlerBlowupStep
