import SGPT.Trace.RestVolTrace
import SGPT.PSH.CanonicalGrowthManifold
import SGPT.PSH.MultiplierIdealInfSkoda
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularBasics
import SGPT.Foundations.Analysis.Pending.IEnvelopeOrder
import SGPT.NAPotential.BJPrepLelongConvex

/-!
# Restricted multiplier ideals of analytic approximants

Source: `chapter_trace.tex`, proof of `thm:rest_volume`, Step 1, the chain

`Res_Y 𝓘(kφ) ⊆ Res_Y 𝓘(kφ_j) ⊆ Res_Y 𝓘_∞((1-ε)kφ_j) ⊆ 𝓘_∞((1-ε)kφ_j|_Y) ⊆ 𝓘((1-ε)kφ_j|_Y)`

for `φ ≤ φ_j`, `φ_j` with analytic singularities and `k` large (`lma:IandIinf`).

* `mem_inftyIdeal_comp_val`, `restrictIdeal_inftyIdeal_le`: `Res_W 𝓘_∞(u) ⊆ 𝓘_∞(u|_W)` (the
  book's observation `Res_Y 𝓘_∞(ψ) ⊆ 𝓘_∞(ψ|_Y)`, for every function `u`);
* `inftyIdeal_le_multiplierIdeal`: `𝓘_∞(u) ⊆ 𝓘(u)` for quasi-psh `u` (after `def:Iinfty`);
* `eventually_restrictIdeal_le_scaled`: for `φ ≤ v`, `v` quasi-psh with analytic singularities,
  `v|_W` quasi-psh and `0 < c < 1`, eventually in `k`,
  `Res_W 𝓘(kφ) ⊆ 𝓘(k · c v|_W)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.RestVol

open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SubmanifoldIdealRestriction
open SGPT.Foundations.Analysis.Pending.AnalyticBoundedMultiplierIdeal
open SGPT.Bergman.MultiplierSectionsDraft

/-! ### `𝓘_∞` is an ideal sheaf contained in the multiplier ideal sheaf -/

section Infty

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel m) M]
  [IsComplexManifold m M]

/-- `𝓘_∞(u)` contains every germ in the span of its own germs. -/
theorem mem_inftyIdeal_of_isInSpanAt {u : M → EReal} {x : M} {g : M → ℂ}
    (h : IsInSpanAt (n := m) (fun s => (SGPT.PSH.inftyIdeal (n := m) u).mem x s) x g) :
    (SGPT.PSH.inftyIdeal (n := m) u).mem x g := by
  classical
  obtain ⟨-, N, s, a, hs, ha, heq⟩ := h
  refine (SGPT.PSH.inftyIdeal_mem_congr (n := m) heq.symm).mp ?_
  have key : ∀ t : Finset (Fin N),
      (SGPT.PSH.inftyIdeal (n := m) u).mem x (fun y => ∑ i ∈ t, a i y * s i y) := by
    intro t
    induction t using Finset.induction with
    | empty => simpa using SGPT.PSH.inftyIdeal_zero_mem (n := m) u x
    | insert i t hit ih =>
      have hi := SGPT.PSH.inftyIdeal_mul_mem (n := m) (ha i) (hs i)
      have := SGPT.PSH.inftyIdeal_add_mem (n := m) hi ih
      simpa only [Finset.sum_insert hit] using this
  simpa using key Finset.univ

/-- **`𝓘_∞(u) ⊆ 𝓘(u)`** (the remark after `def:Iinfty`) for a quasi-psh function `u`. -/
theorem inftyIdeal_le_multiplierIdeal {u : M → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := m) u) :
    (SGPT.PSH.inftyIdeal (n := m) u).Le (multiplierIdeal (n := m) 1 u) := by
  intro x g hg
  obtain ⟨hgh, K, hK, hev⟩ := hg
  refine ⟨hgh, ?_⟩
  obtain ⟨U, hUsub, hU, hxU⟩ := _root_.mem_nhds_iff.mp hgh
  set e := (complexChartAt (n := m) x).val with he
  have hz : e x ∈ e.target := e.map_source (mem_complexChartAt_source x)
  have hO : IsOpen (e.target ∩ e.symm ⁻¹' U) := e.isOpen_inter_preimage_symm hU
  have hzO : e x ∈ e.target ∩ e.symm ⁻¹' U := by
    refine ⟨hz, ?_⟩
    simpa [e.left_inv (mem_complexChartAt_source x)] using hxU
  have hdon : DifferentiableOn ℂ (fun z => g (e.symm z)) (e.target ∩ e.symm ⁻¹' U) :=
    differentiableOn_comp_chartSymm x (fun y hy => (hUsub hy).mdifferentiableWithinAt)
  -- the density bound in the chart
  have hsymm : ContinuousAt e.symm (e x) := e.continuousAt_symm hz
  have hsx : e.symm (e x) = x := e.left_inv (mem_complexChartAt_source x)
  have hev' : ∀ᶠ z in 𝓝 (e x),
      multiplierDensity (chartFunction u (complexChartAt (n := m) x)) 1
        (fun z => g (e.symm z)) z ≤ ENNReal.ofReal K := by
    have := hsymm.eventually (p := fun y => multiplierDensity u 1 g y ≤ ENNReal.ofReal K)
      (by rw [hsx]; exact hev)
    exact this
  -- quasi-plurisubharmonicity near the point
  have hq : QuasiPlurisubharmonicOn (chartFunction u (complexChartAt (n := m) x)) e.target :=
    hu (complexChartAt (n := m) x)
  have hev2 : ∀ᶠ z in 𝓝 (e x), z ∈ e.target ∩ e.symm ⁻¹' U ∧
      multiplierDensity (chartFunction u (complexChartAt (n := m) x)) 1
        (fun z => g (e.symm z)) z ≤ ENNReal.ofReal K :=
    (Filter.eventually_mem_set.mpr (hO.mem_nhds hzO)).and hev'
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev2
  have hBO : Metric.ball (e x) r ⊆ e.target ∩ e.symm ⁻¹' U := fun z hz => (hball z hz).1
  refine ⟨one_pos, Metric.ball (e x) r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    hdon.mono hBO, ?_, ?_⟩
  · exact aemeasurable_multiplierDensity_restrict_of_quasiPlurisubharmonicOn Metric.isOpen_ball
      (fun y hy => hq y (hBO hy).1) one_ne_zero (hdon.mono hBO).continuousOn
  · calc (∫⁻ y in Metric.ball (e x) r,
          multiplierDensity (chartFunction u (complexChartAt (n := m) x)) 1
            (fun z => g (e.symm z)) y)
        ≤ ∫⁻ _y in Metric.ball (e x) r, ENNReal.ofReal K :=
          setLIntegral_mono' Metric.isOpen_ball.measurableSet (fun y hy => (hball y hy).2)
      _ = ENNReal.ofReal K * volume (Metric.ball (e x) r) := by
          rw [setLIntegral_const]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

end Infty

/-! ### Restriction of `𝓘_∞` -/

section Restriction

variable {n k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {W : Set X}
  [ChartedSpace (ComplexModel k) W] [IsComplexManifold k W]

/-- The restriction of a germ of `𝓘_∞(u)` lies in `𝓘_∞(u|_W)`. -/
theorem mem_inftyIdeal_comp_val
    (hval : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → X))
    {u : X → EReal} {p : W} {a : X → ℂ} (ha : (SGPT.PSH.inftyIdeal (n := n) u).mem p.1 a) :
    (SGPT.PSH.inftyIdeal (n := k) (fun y : W => u y)).mem p (fun y : W => a y) := by
  obtain ⟨hah, K, hK, hev⟩ := ha
  refine ⟨holomorphicAt_comp_val hval hah, K, hK, ?_⟩
  exact (continuous_subtype_val.continuousAt (x := p)).eventually
    (p := fun y => multiplierDensity u 1 a y ≤ ENNReal.ofReal K) hev

/-- **`Res_W 𝓘_∞(u) ⊆ 𝓘_∞(u|_W)`.** -/
theorem restrictIdeal_inftyIdeal_le
    (hval : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → X))
    (u : X → EReal) :
    (restrictIdeal (k := k) (W := W) (SGPT.PSH.inftyIdeal (n := n) u)).Le
      (SGPT.PSH.inftyIdeal (n := k) (fun y : W => u y)) := by
  intro p g hg
  rw [mem_restrictIdeal_iff] at hg
  obtain ⟨hgh, N, s, a, hs, ha, heq⟩ := hg
  apply mem_inftyIdeal_of_isInSpanAt
  refine ⟨hgh, N, s, a, fun i => ?_, ha, heq⟩
  obtain ⟨b, hb, hbeq⟩ := hs i
  rw [hbeq]
  exact mem_inftyIdeal_comp_val hval hb

/-- `Res_W` is monotone. -/
theorem restrictIdeal_mono {A B : GermIdeal n X} (h : A.Le B) :
    (restrictIdeal (k := k) (W := W) A).Le (restrictIdeal (k := k) (W := W) B) := by
  intro p g hg
  rw [mem_restrictIdeal_iff] at hg ⊢
  obtain ⟨hgh, N, s, a, hs, ha, heq⟩ := hg
  refine ⟨hgh, N, s, a, fun i => ?_, ha, heq⟩
  obtain ⟨b, hb, hbeq⟩ := hs i
  exact ⟨b, h _ _ hb, hbeq⟩

end Restriction

/-! ### The comparison of Step 1 -/

section Comparison

variable {n k : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X] {W : Set X}
  [ChartedSpace (ComplexModel k) W] [IsComplexManifold k W]

/-- **Step 1 of the proof of `thm:rest_volume`, the ideals**: let `φ ≤ v` with `v` quasi-psh with
analytic singularities and `v|_W` quasi-psh, and `0 < c < 1`. Then for all large `k`,
`Res_W 𝓘(kφ) ⊆ 𝓘(k · (c v)|_W)`. -/
theorem eventually_restrictIdeal_le_scaled
    (hval : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → X))
    {φ v : X → EReal} (hφv : φ ≤ v) (hv : ManifoldQuasiPlurisubharmonic (n := n) v)
    (hvan : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).HasRationalAnalyticChartType v)
    (hvW : ManifoldQuasiPlurisubharmonic (n := k) (fun y : W => v y))
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∀ᶠ j : ℕ in atTop,
      (restrictIdeal (k := k) (W := W) (sourceDegreeMultiplierIdeal (n := n) j φ)).Le
        (sourceDegreeMultiplierIdeal (n := k) j (fun y : W => (c : EReal) * v y)) := by
  have hε : 0 < 1 / c - 1 := by
    rw [sub_pos, lt_div_iff₀ hc0]; linarith
  obtain ⟨s₀, hs₀, hI⟩ := SGPT.PSH.MultiplierIdealInf.exists_multiplierIdeal_le_inftyIdeal hvan hε
  have htend : Tendsto (fun j : ℕ => (j : ℝ) * c) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hc0
  filter_upwards [htend.eventually_ge_atTop s₀, eventually_gt_atTop 0] with j hj hj0
  -- the inclusions on `X`
  have hscale : (j : ℝ) * c * (1 + (1 / c - 1)) = j := by field_simp; ring
  have hφv' : (sourceDegreeMultiplierIdeal (n := n) j φ).Le
      (multiplierIdeal (n := n) 1 (fun x => (((j : ℝ) * c * (1 + (1 / c - 1)) : ℝ) : EReal) * v x)) := by
    intro x g hg
    rw [sourceDegreeMultiplierIdeal_pos _ hj0] at hg
    have h1 := PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_iOrderOnManifold
      (iOrderOnManifold_of_le hv hφv) (Nat.cast_pos.mpr hj0) x g hg
    rw [hscale]
    exact (SGPT.Trace.OTExt.mem_multiplierIdeal_one_coe_mul_iff (Nat.cast_pos.mpr hj0) v x g).mpr h1
  have hX : (sourceDegreeMultiplierIdeal (n := n) j φ).Le
      (SGPT.PSH.inftyIdeal (n := n) (fun x => (((j : ℝ) * c : ℝ) : EReal) * v x)) :=
    fun x g hg => hI _ hj x g (hφv' x g hg)
  -- restriction and `𝓘_∞ ⊆ 𝓘` on `W`
  have hW1 := restrictIdeal_inftyIdeal_le (k := k) (W := W) hval
    (fun x => (((j : ℝ) * c : ℝ) : EReal) * v x)
  have hqW : ManifoldQuasiPlurisubharmonic (n := k)
      (fun y : W => (((j : ℝ) * c : ℝ) : EReal) * v y) :=
    SGPT.NAPotential.BJPrep.manifoldQuasiPlurisubharmonic_const_mul hvW
      (mul_pos (Nat.cast_pos.mpr hj0) hc0)
  have hW2 := inftyIdeal_le_multiplierIdeal hqW
  intro p g hg
  have h3 := hW2 p g (hW1 p g (restrictIdeal_mono hX p g hg))
  have hfun : (fun y : W => (((j : ℝ) * c : ℝ) : EReal) * v y) =
      fun y : W => ((j : ℝ) : EReal) * ((c : EReal) * v y) := by
    funext y
    rw [← mul_assoc, ← EReal.coe_mul]
  rw [hfun] at h3
  exact h3

end Comparison

end SGPT.Trace.RestVol
