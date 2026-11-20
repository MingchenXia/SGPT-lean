import SGPT.Trace.OTResSkoda
import SGPT.Trace.OTExt4Datum
import SGPT.Trace.TwistedL2MainUnitFrame

/-!
# Regularity in flattening coordinates

Blueprint `claude-ot-residue.tex`, node `claude-ot-residue:flat`.

* `chartSmooth_normSq`: for a section `G` smooth in every chart and frame and a smooth Hermitian
  metric, `|G|²` is smooth in every chart.
* `contDiffOn_comp_finv`: a function smooth in every chart is smooth in the flattening coordinates
  `ζ = Φ ∘ e` of a submanifold.
* `exists_lipschitz_flat`: hence it is Lipschitz on every compact convex subset of the flattening
  target; `convex_closedLocalDom`: the closed products `{|z'| ≤ a, |w| ≤ b}` are convex.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTRes

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal NNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.PolynomialH0Growth
open SGPT.Trace.TwistedL2 HermitianHolomorphicLineBundle
open SGPT.Trace.OTMargin (fcoord finv finv_mem continuousOn_finv)
open SGPT.Trace.OTExt4 (closedLocalDom)

/-- A `C¹` function on an open set is Lipschitz on every compact convex subset. -/
theorem exists_lipschitz_of_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {U K : Set E} (hU : IsOpen U) (hu : ContDiffOn ℝ 1 u U) (hK : IsCompact K)
    (hKU : K ⊆ U) (hKc : Convex ℝ K) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ K, ∀ y ∈ K, |u x - u y| ≤ L * ‖x - y‖ := by
  have hd : ContinuousOn (fderiv ℝ u) U := hu.continuousOn_fderiv_of_isOpen hU le_rfl
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hd.mono hKU)
  refine ⟨max C 0, le_max_right _ _, fun x hx y hy => ?_⟩
  have hdiff : ∀ z ∈ K, DifferentiableAt ℝ u z := fun z hz =>
    (hu.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds (hKU hz))
  have := hKc.norm_image_sub_le_of_norm_fderiv_le hdiff
    (fun z hz => (hC z hz).trans (le_max_left C 0)) hy hx
  rwa [Real.norm_eq_abs] at this

theorem convex_closedLocalDom (n m : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Convex ℝ (closedLocalDom n m a b) := by
  have h1 : closedLocalDom n m a b =
      (SGPT.Trace.OTExt2.tangCLM n m).restrictScalars ℝ ⁻¹' closedBall 0 a ∩
        (SGPT.Trace.OTExt2.normalCLM n m).restrictScalars ℝ ⁻¹' closedBall 0 b := by
    ext z
    simp only [closedLocalDom, mem_inter_iff, mem_preimage, mem_closedBall_zero_iff,
      ContinuousLinearMap.coe_restrictScalars', mem_ofPred_eq, SGPT.Trace.OTExt2.tanWeight,
      SGPT.Trace.OTExt2.normalWeight_eq_norm_sq]
    rw [pow_le_pow_iff_left₀ (norm_nonneg _) ha two_ne_zero,
      pow_le_pow_iff_left₀ (norm_nonneg _) hb two_ne_zero]
  rw [h1]
  exact ((convex_closedBall 0 a).linear_preimage
    ((SGPT.Trace.OTExt2.tangCLM n m).restrictScalars ℝ).toLinearMap).inter
    ((convex_closedBall 0 b).linear_preimage
      ((SGPT.Trace.OTExt2.normalCLM n m).restrictScalars ℝ).toLinearMap)

variable {n m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {W : Set X}

/-- A function smooth in every chart is smooth in the flattening coordinates. -/
theorem contDiffOn_comp_finv (F : FlatData n m X W) {h : X → ℝ} (hh : ChartSmooth (n := n) h) :
    ContDiffOn ℝ ∞ (fun z => h (finv F z)) F.flat.target := by
  have h1 : ContDiffOn ℝ ∞ F.flat.symm F.flat.target :=
    (contDiffOn_of_differentiableOn_complex F.differentiableOn_flat_symm
      F.flat.open_target).restrict_scalars ℝ
  exact (hh F.amb).comp h1 fun z hz => F.flat_source_subset (F.flat.map_target hz)

/-- A function smooth in every chart is Lipschitz, in the flattening coordinates, on every compact
convex subset of the flattening target. -/
theorem exists_lipschitz_flat (F : FlatData n m X W) {h : X → ℝ} (hh : ChartSmooth (n := n) h)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKt : K ⊆ F.flat.target) (hKc : Convex ℝ K) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ z ∈ K, ∀ z' ∈ K, |h (finv F z) - h (finv F z')| ≤ L * ‖z - z'‖ :=
  exists_lipschitz_of_contDiffOn F.flat.open_target
    ((contDiffOn_comp_finv F hh).of_le (by simp)) hK hKt hKc

section Section

variable (V : HermitianHolomorphicLineBundle.{0, 0} n X)

/-- `|G|²` is smooth in every chart, for a smooth section and a smooth metric. -/
theorem chartSmooth_normSq (hV : IsSourceSmoothHermitianMetric V) {G : (x : X) → V.Fiber x}
    (hG : IsSmoothSectionOn V G univ) : ChartSmooth (n := n) (fun x => ‖G x‖ ^ 2) := by
  intro c
  refine fun w hw => ContDiffAt.contDiffWithinAt ?_
  let e : AtlasFrame V := ⟨trivializationAt ℂ V.Fiber (c.val.symm w), inferInstance⟩
  have hwD : w ∈ chartFrameDomain V c e :=
    ⟨hw, mem_baseSet_trivializationAt ℂ V.Fiber (c.val.symm w)⟩
  have hDo : IsOpen (chartFrameDomain V c e) :=
    c.val.isOpen_inter_preimage_symm e.val.open_baseSet
  have h1 : ContDiffOn ℝ ∞ (chartCoeff V c e G) (chartFrameDomain V c e) := by
    have := hG c e
    rwa [preimage_univ, inter_univ] at this
  have h2 := hV c e
  have hprod : ContDiffOn ℝ ∞ (fun w => ‖chartCoeff V c e G w‖ ^ 2 *
      ‖e.val.symm (c.val.symm w) 1‖ ^ 2) (chartFrameDomain V c e) :=
    (h1.norm_sq ℝ).mul h2
  refine (hprod.contDiffAt (hDo.mem_nhds hwD)).congr_of_eventuallyEq ?_
  filter_upwards [hDo.mem_nhds hwD] with w' hw'
  show ‖G (c.val.symm w')‖ ^ 2 = _
  rw [norm_sq_eq_frameCoeff e hw'.2]
  rfl

end Section

end SGPT.Trace.OTRes
