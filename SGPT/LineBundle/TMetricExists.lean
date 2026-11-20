import SGPT.LineBundle.TMetricRescale
import SGPT.Foundations.Analysis.Pending.ChartPartition
import SGPT.Foundations.Analysis.Pending.BlanchardWeight
import SGPT.Foundations.Analysis.Pending.FactorizedWeightForm
import SGPT.Foundations.Analysis.Pending.ProductTestForms

/-!
# Every holomorphic line bundle on a compact complex manifold has a smooth Hermitian metric

Lane T-METRIC, blueprint `claude-t-metric`, node `claude-t-metric:exists-smooth`. Used for
`thm:DXmain1` (chapter *`𝓘`-good singularities*), whose twist `T` is an arbitrary holomorphic
line bundle.

A `HermitianHolomorphicLineBundle` `T` carries some continuous Hermitian metric `h_T`. On a
compact base, choose finitely many atlas frames `eₐ` and a chart-smooth partition of unity `χₐ`
with `supp χₐ ⊆ dom eₐ` (`ChartPartition.exists_chartSmooth_partitionOfUnity`), and put

  `ρ = ∑ₐ χₐ / |eₐ|²_{h_T}`  (continuous and `> 0`).

For every atlas frame `e`, `e = gₐ eₐ` with the holomorphic transition `gₐ = coordChange(e, eₐ)`,
so `ρ |e|²_{h_T} = ∑ₐ χₐ |gₐ|²` is smooth in every chart: the metric `ρ h_T` (`rescale T ρ`) is
the smooth metric `∑ₐ χₐ |·|²_{eₐ}` glued from the flat metrics of the frames.

* `frame_eq_smul`, `frameNorm_eq_mul`: `e(y) = g(y) e'(y)`, `|e(y)| = |g(y)| |e'(y)|`.
* `exists_smooth_rescale`: for compact `M`, there is a continuous `ρ > 0` such that
  `rescale T ρ` (the same holomorphic line bundle with metric `ρ h_T`) has a smooth metric.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.LineBundle.TMetric

open Bundle Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft HermitianHolomorphicLineBundle
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.PolynomialH0Growth

universe u v

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### Frame transitions -/

section Frames

variable {T : HermitianHolomorphicLineBundle.{u, v} n M}

/-- The holomorphic transition coefficient `g` with `e = g e'` on the overlap. -/
def frameTransition (e e' : AtlasFrame T) (y : M) : ℂ :=
  letI := e.property
  letI := e'.property
  e.val.coordChangeL ℂ e'.val y 1

/-- `e(y) = g(y) e'(y)` on the overlap of two atlas frames. -/
theorem frame_eq_smul (e e' : AtlasFrame T) {y : M} (hy : y ∈ e.val.baseSet ∩ e'.val.baseSet) :
    e.val.symm y 1 = frameTransition e e' y • e'.val.symm y 1 := by
  let := e.property
  let := e'.property
  have hlin : ∀ c : ℂ, e'.val.symm y c = c • e'.val.symm y 1 := by
    intro c
    rw [← Trivialization.symmₗ_apply (R := ℂ) e'.val hy.2 c,
      ← Trivialization.symmₗ_apply (R := ℂ) e'.val hy.2 1, ← map_smul, smul_eq_mul, mul_one]
  rw [frameTransition, Trivialization.coordChangeL_apply e.val e'.val hy, ← hlin,
    Trivialization.symm_apply_apply_mk e'.val hy.2]

/-- `|e(y)| = |g(y)| |e'(y)|` on the overlap of two atlas frames. -/
theorem frameNorm_eq_mul (e e' : AtlasFrame T) {y : M} (hy : y ∈ e.val.baseSet ∩ e'.val.baseSet) :
    ‖e.val.symm y 1‖ = ‖frameTransition e e' y‖ * ‖e'.val.symm y 1‖ := by
  rw [frame_eq_smul e e' hy, norm_smul]

/-- The transition coefficient is holomorphic on the overlap. -/
theorem frameTransition_mdifferentiableAt (e e' : AtlasFrame T) {y : M}
    (hy : y ∈ e.val.baseSet ∩ e'.val.baseSet) :
    MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (frameTransition e e') y := by
  let := e.property
  let := e'.property
  have h : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞
      (fun x => (e.val.coordChangeL ℂ e'.val x) (1 : ℂ)) (e.val.baseSet ∩ e'.val.baseSet) :=
    (contMDiffOn_coordChangeL e.val e'.val).clm_apply contMDiffOn_const
  exact (h.contMDiffAt ((e.val.open_baseSet.inter e'.val.open_baseSet).mem_nhds hy)).mdifferentiableAt
    (by simp)

/-- The atlas frame norm `|e'|` is continuous and positive on the frame domain, so a function
supported in the frame domain divided by `|e'|²` is continuous. -/
theorem continuous_div_frameNormSq (e' : AtlasFrame T) {χ : M → ℝ} (hχ : Continuous χ)
    (hsupp : tsupport χ ⊆ e'.val.baseSet) :
    Continuous (fun y => χ y / ‖e'.val.symm y 1‖ ^ 2) := by
  let := e'.property
  refine continuous_iff_continuousAt.mpr fun y => ?_
  by_cases hy : y ∈ e'.val.baseSet
  · have hN : ContinuousAt (fun y => ‖e'.val.symm y 1‖) y :=
      (frameNorm_continuousOn T.Fiber e'.val).continuousAt (e'.val.open_baseSet.mem_nhds hy)
    exact hχ.continuousAt.div (hN.pow 2) (pow_ne_zero 2 (frameNorm_pos T.Fiber e'.val hy).ne')
  · have hy' : y ∉ tsupport χ := fun h => hy (hsupp h)
    refine continuousAt_const.congr (f := fun _ => (0 : ℝ)) ?_
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hy'] with w hw
    rw [image_eq_zero_of_notMem_tsupport hw, zero_div]

/-- For a chart-smooth `χ` supported in the domain of `e'`, `χ |g|²` (`g` the transition from `e`
to `e'`) is smooth in every chart on the domain of `e`. -/
theorem contDiffOn_mul_normSq_frameTransition (c : ComplexChart n M) (e e' : AtlasFrame T)
    {χ : M → ℝ} (hχ : ChartSmooth (n := n) χ) (hsupp : tsupport χ ⊆ e'.val.baseSet) :
    ContDiffOn ℝ ∞ (fun z => χ (c.val.symm z) * Complex.normSq (frameTransition e e' (c.val.symm z)))
      (c.val.target ∩ c.val.symm ⁻¹' e.val.baseSet) := by
  intro z hz
  refine ContDiffAt.contDiffWithinAt ?_
  have hχz := (hχ c).contDiffAt (c.val.open_target.mem_nhds hz.1)
  by_cases hs : c.val.symm z ∈ tsupport χ
  · have hz' : c.val.symm z ∈ e'.val.baseSet := hsupp hs
    refine hχz.mul (BlanchardWeight.BlanchardData.contDiffAt_normSq_comp ?_)
    filter_upwards [(c.val.isOpen_inter_preimage_symm
      (e.val.open_baseSet.inter e'.val.open_baseSet)).mem_nhds ⟨hz.1, hz.2, hz'⟩] with w hw
    exact FactorizedWeightForm.differentiableAt_comp_chart_symm c hw.1
      (frameTransition_mdifferentiableAt e e' hw.2)
  · have heq : (fun w => χ (c.val.symm w) *
        Complex.normSq (frameTransition e e' (c.val.symm w))) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [(c.val.isOpen_inter_preimage_symm
        (isClosed_tsupport χ).isOpen_compl).mem_nhds ⟨hz.1, hs⟩] with w hw
      rw [image_eq_zero_of_notMem_tsupport hw.2, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq heq

end Frames

/-! ### The smooth metric -/

/-- **Every holomorphic line bundle on a compact complex manifold carries a smooth Hermitian
metric**: for a compact base there is a continuous `ρ > 0` such that `rescale T ρ` — the same
holomorphic line bundle as `T`, with metric `ρ h_T` — has a smooth metric
(`IsSourceSmoothHermitianMetric`). -/
theorem exists_smooth_rescale [CompactSpace M] (T : HermitianHolomorphicLineBundle.{u, v} n M) :
    ∃ (ρ : M → ℝ) (hρc : Continuous ρ) (hρ : ∀ x, 0 < ρ x),
      IsSourceSmoothHermitianMetric (rescale T ρ hρc hρ) := by
  classical
  let S : M → Opens M := fun x =>
    ⟨(trivializationAt ℂ T.Fiber x).baseSet, (trivializationAt ℂ T.Fiber x).open_baseSet⟩
  obtain ⟨m, χ, idx, hsm, hnn, hs, -, hsum⟩ :=
    ChartPartition.exists_chartSmooth_partitionOfUnity (n := n) S
      (fun x => ⟨x, mem_baseSet_trivializationAt ℂ T.Fiber x⟩)
  let E : Fin m → AtlasFrame T := fun a => ⟨trivializationAt ℂ T.Fiber (idx a), inferInstance⟩
  have hsupp : ∀ a, tsupport (χ a) ⊆ (E a).val.baseSet := hs
  let ρ : M → ℝ := fun y => ∑ a, χ a y / ‖(E a).val.symm y 1‖ ^ 2
  have hρc : Continuous ρ := continuous_finsetSum _ fun a _ =>
    continuous_div_frameNormSq (E a) (ProductTestForms.ChartSmooth.continuous (hsm a)) (hsupp a)
  have hρ : ∀ y, 0 < ρ y := by
    intro y
    have hex : ∃ a, χ a y ≠ 0 := by
      by_contra h
      push Not at h
      have hz : (∑ a, χ a y) = 0 := Finset.sum_eq_zero fun a _ => h a
      rw [hsum y] at hz
      exact one_ne_zero hz
    obtain ⟨a, ha⟩ := hex
    have hya : y ∈ (E a).val.baseSet := hsupp a (subset_tsupport _ ha)
    have hpos : 0 < χ a y / ‖(E a).val.symm y 1‖ ^ 2 := by
      let := (E a).property
      exact div_pos (lt_of_le_of_ne (hnn a y) (Ne.symm ha))
        (pow_pos (frameNorm_pos T.Fiber (E a).val hya) 2)
    exact lt_of_lt_of_le hpos (Finset.single_le_sum
      (f := fun b => χ b y / ‖(E b).val.symm y 1‖ ^ 2)
      (fun b _ => div_nonneg (hnn b y) (sq_nonneg _)) (Finset.mem_univ a))
  refine ⟨ρ, hρc, hρ, (isSourceSmoothHermitianMetric_rescale_iff T ρ hρc hρ).mpr ?_⟩
  intro c e
  have hsmooth : ContDiffOn ℝ ∞ (fun z => ∑ a, χ a (c.val.symm z) *
      Complex.normSq (frameTransition e (E a) (c.val.symm z)))
      (c.val.target ∩ c.val.symm ⁻¹' e.val.baseSet) :=
    ContDiffOn.sum fun a _ => contDiffOn_mul_normSq_frameTransition c e (E a) (hsm a) (hsupp a)
  refine hsmooth.congr fun z hz => ?_
  change (∑ a, χ a (c.val.symm z) / ‖(E a).val.symm (c.val.symm z) 1‖ ^ 2) *
      ‖e.val.symm (c.val.symm z) 1‖ ^ 2 = _
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : χ a (c.val.symm z) = 0
  · rw [ha, zero_div, zero_mul, zero_mul]
  · have hya : c.val.symm z ∈ (E a).val.baseSet := hsupp a (subset_tsupport _ ha)
    have hN : ‖(E a).val.symm (c.val.symm z) 1‖ ≠ 0 := by
      let := (E a).property
      exact (frameNorm_pos T.Fiber (E a).val hya).ne'
    rw [frameNorm_eq_mul e (E a) ⟨hz.2, hya⟩, Complex.normSq_eq_norm_sq]
    field_simp

end SGPT.LineBundle.TMetric
