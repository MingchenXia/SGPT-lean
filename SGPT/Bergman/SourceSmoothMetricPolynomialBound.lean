import SGPT.Bergman.SourcePolynomialPointEstimate
import SGPT.Bergman.SourceTensorDictionary
import SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# SmoothMetricPolynomialBound

Smooth Hermitian metrics and the global point estimate `|s(x)|²_{h^k ⊗ h_T} ≤ C kⁿ ‖s‖²_{L²}` for all sections of `L^k ⊗ T`.

Ported from the previous team's drafts (`work/sgpt-active-lanes-20261102/bergman-*`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.PolynomialH0Growth
open Bundle Set Filter Metric MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open scoped Topology Manifold ContDiff ENNReal

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The original smooth Hermitian metric condition on genuine holomorphic
frame sections, read in actual source atlas charts. Tensor66 itself only
requires continuous norms; this natural book hypothesis is explicit. It
contains NO degree/section estimates, derivative bounds or growth fields. -/
def IsSourceSmoothHermitianMetric (L : HermitianHolomorphicLineBundle n X) : Prop :=
  ∀ (c : ComplexChart n X) (e : AtlasFrame L),
    ContDiffOn ℝ ∞ (fun z => ‖e.val.symm (c.val.symm z) 1‖ ^ 2)
      (c.val.target ∩ c.val.symm ⁻¹' e.val.baseSet)

/-- Smooth positive actual frame norms manufacture C² real log potentials. -/
theorem frame_logNormSq_contDiffOn (L : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) (c : ComplexChart n X) (e : AtlasFrame L) :
    ContDiffOn ℝ 2 (fun z => Real.log (‖e.val.symm (c.val.symm z) 1‖ ^ 2))
      (c.val.target ∩ c.val.symm ⁻¹' e.val.baseSet) := by
  let := e.property
  exact ((hL c e).of_le (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) from WithTop.coe_le_coe.mpr le_top)).log (fun z hz =>
    (sq_pos_of_pos (frameNorm_pos L.Fiber e.val hz.2)).ne')

/-- Exact SAME all-degree Hermitian tensor metric under actual real log
potentials. The original coefficient is not rescaled or supplied as data. -/
theorem twistedSection_norm_sq_exp_frame (L T : HermitianHolomorphicLineBundle n X)
    (e : AtlasFrame L) (f : AtlasFrame T) (k : ℕ) (s : twistedSections L T k)
    {x : X} (hx : x ∈ e.val.baseSet) (hy : x ∈ f.val.baseSet) :
    ‖s x‖ ^ 2 = ‖((twistedPowerAtlasFrame e f k).val ⟨x, s x⟩).2‖ ^ 2 *
      Real.exp ((k : ℝ) * Real.log (‖e.val.symm x 1‖ ^ 2) +
        Real.log (‖f.val.symm x 1‖ ^ 2)) := by
  let := e.property
  let := f.property
  have ha : 0 < ‖e.val.symm x 1‖ ^ 2 := sq_pos_of_pos (frameNorm_pos L.Fiber e.val hx)
  have hb : 0 < ‖f.val.symm x 1‖ ^ 2 := sq_pos_of_pos (frameNorm_pos T.Fiber f.val hy)
  rw [twistedSection_norm_sq_frame e f k s hx hy, Real.exp_add, Real.exp_nat_mul,
    Real.exp_log ha, Real.exp_log hb]
  ring

variable [MeasurableSpace X] [BorelSpace X]

/-- True source bundle local point estimate: actual ALL H0, SAME degree,
SAME metric and actual transported smooth volume. Constants precede all k,s,x. -/
theorem exists_local_polynomial_section_bound (L T : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (μ : Measure X) (hμ : IsSmoothPositiveVolume (n := n) μ) (x : X) :
    ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ ∃ C : ℝ, 0 < C ∧
      ∀ k : ℕ, 0 < k → ∀ s : twistedSections L T k, ∀ y ∈ W,
        ENNReal.ofReal (‖s y‖ ^ 2) ≤ ENNReal.ofReal (C * (k : ℝ) ^ n) *
          ∫⁻ z, ENNReal.ofReal (‖s z‖ ^ 2) ∂μ := by
  let c := complexChartAt (n := n) x
  let e : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber x, inferInstance⟩
  let f : AtlasFrame T := ⟨trivializationAt ℂ T.Fiber x, inferInstance⟩
  let := e.property
  let := f.property
  have hx : x ∈ c.val.source := mem_complexChartAt_source x
  have he : x ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ L.Fiber x
  have hf : x ∈ f.val.baseSet := mem_baseSet_trivializationAt ℂ T.Fiber x
  let y₀ := c.val x
  have hy₀ : y₀ ∈ c.val.target := c.val.map_source hx
  have hinv : c.val.symm y₀ = x := c.val.left_inv hx
  let D := c.val.target ∩ c.val.symm ⁻¹' (e.val.baseSet ∩ f.val.baseSet)
  have hD : IsOpen D := c.val.isOpen_inter_preimage_symm (e.val.open_baseSet.inter f.val.open_baseSet)
  have hyD : y₀ ∈ D := ⟨hy₀, by
    change c.val.symm y₀ ∈ e.val.baseSet ∩ f.val.baseSet
    rw [hinv]
    exact ⟨he, hf⟩⟩
  obtain ⟨R₀, hR₀, hR₀D⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds hyD)
  let R := R₀ / 2
  have hR : 0 < R := half_pos hR₀
  have hRD : closedBall y₀ R ⊆ D :=
    (closedBall_subset_ball (half_lt_self hR₀)).trans hR₀D
  obtain ⟨ρ, hρsmooth, hρpos, hmap⟩ := hμ c
  let p : ComplexModel n → ℝ := fun z => Real.log (‖e.val.symm (c.val.symm z) 1‖ ^ 2)
  let q : ComplexModel n → ℝ := fun z => Real.log (‖f.val.symm (c.val.symm z) 1‖ ^ 2)
  have hp : ContDiffOn ℝ 2 p (ball y₀ R) :=
    (frame_logNormSq_contDiffOn L hL c e).mono
      (fun z hz => ⟨(hRD (ball_subset_closedBall hz)).1, (hRD (ball_subset_closedBall hz)).2.1⟩)
  have hq : ContDiffOn ℝ 2 q (ball y₀ R) :=
    (frame_logNormSq_contDiffOn T hT c f).mono
      (fun z hz => ⟨(hRD (ball_subset_closedBall hz)).1, (hRD (ball_subset_closedBall hz)).2.2⟩)
  have hρcont : ContinuousAt ρ y₀ :=
    hρsmooth.continuousOn.continuousAt (c.val.open_target.mem_nhds hy₀)
  obtain ⟨r, C, hr, hC, hrsub, hb⟩ := exists_local_polynomial_point_bound
    isOpen_ball (mem_ball_self hR) hp hq hρcont (hρpos _ hy₀)
  let W := c.val.source ∩ c.val ⁻¹' ball y₀ r
  have hW : IsOpen W := c.val.continuousOn.isOpen_inter_preimage c.val.open_source isOpen_ball
  have hxW : x ∈ W := ⟨hx, mem_ball_self hr⟩
  refine ⟨W, hW, hxW, C, hC, fun k hk s y hy => ?_⟩
  let t := twistedPowerAtlasFrame e f k
  let := t.property
  let F := sectionCoefficient (twistedPower L T k).Fiber t.val s ∘ c.val.symm
  have hF : DifferentiableOn ℂ F (ball y₀ R) := by
    apply (sectionCoefficient_chart_differentiable (twistedPower L T k).Fiber t.val x s).mono
    intro z hz
    have hzD := hRD (ball_subset_closedBall hz)
    exact ⟨hzD.1, twistedPowerAtlasFrame_mem e f hzD.2.1 hzD.2.2 k⟩
  have hread (z : ComplexModel n) (hz : z ∈ closedBall y₀ R) :
      ‖F z‖ ^ 2 * Real.exp (degreePotential p q k z) = ‖s (c.val.symm z)‖ ^ 2 := by
    exact (twistedSection_norm_sq_exp_frame L T e f k s (hRD hz).2.1 (hRD hz).2.2).symm
  have hpoint := hb k hk F hF (c.val y) hy.2
  rw [hread _ (ball_subset_closedBall (hrsub hy.2)), c.val.left_inv hy.1] at hpoint
  have hI : (∫⁻ z in ball y₀ R, ENNReal.ofReal (‖F z‖ ^ 2 *
      Real.exp (degreePotential p q k z) * ρ z)) ≤ ∫⁻ z, ENNReal.ofReal (‖s z‖ ^ 2) ∂μ := by
    calc
      _ ≤ ∫⁻ z in closedBall y₀ R, ENNReal.ofReal (‖F z‖ ^ 2 *
          Real.exp (degreePotential p q k z) * ρ z) := lintegral_mono_set ball_subset_closedBall
      _ = ∫⁻ z in closedBall y₀ R, ENNReal.ofReal (ρ z) *
          ENNReal.ofReal (‖s (c.val.symm z)‖ ^ 2) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet] with z hz
        rw [hread z hz, ← ENNReal.ofReal_mul (hρpos _ (hRD hz).1).le, mul_comm]
      _ = ∫⁻ z in c.val.source ∩ c.val ⁻¹' closedBall y₀ R, ENNReal.ofReal (‖s z‖ ^ 2) ∂μ := by
        exact (setLIntegral_source_inter_preimage c hρsmooth.continuousOn hmap
          (isCompact_closedBall _ _) (fun z hz => (hRD hz).1)
          (ENNReal.continuous_ofReal.comp
            ((sectionNormMap (twistedPower L T k).Fiber s).continuous.pow 2)).measurable).symm
      _ ≤ _ := setLIntegral_le_lintegral _ _
  exact hpoint.trans (mul_le_mul' le_rfl hI)

/-- Genuine compact finite-cover assembly produces one polynomial point
bound for ALL original tensor degrees, ALL full sections and ALL points. -/
theorem exists_global_polynomial_section_bound [CompactSpace X]
    (L T : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (μ : Measure X) (hμ : IsSmoothPositiveVolume (n := n) μ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k → ∀ s : twistedSections L T k, ∀ x : X,
      ENNReal.ofReal (‖s x‖ ^ 2) ≤ ENNReal.ofReal (C * (k : ℝ) ^ n) *
        ∫⁻ z, ENNReal.ofReal (‖s z‖ ^ 2) ∂μ := by
  classical
  choose W hW hxW C hC hb using exists_local_polynomial_section_bound L T hL hT μ hμ
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hW
    (fun x _ => mem_iUnion.mpr ⟨x, hxW x⟩)
  let A : ℝ := 1 + ∑ x ∈ t, C x
  have hsum : 0 ≤ ∑ x ∈ t, C x := Finset.sum_nonneg (fun x _ => (hC x).le)
  have hA : 0 < A := by dsimp only [A]; linarith
  refine ⟨A, hA, fun k hk s x => ?_⟩
  obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (ht (mem_univ x))
  have hCA : C y ≤ A := by
    have hle := Finset.single_le_sum (fun z (_ : z ∈ t) => (hC z).le) hyt
    dsimp only [A]
    linarith
  exact (hb y k hk s x hxy).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hCA (pow_nonneg (Nat.cast_nonneg _) _))) le_rfl)

end SGPT.Bergman.PolynomialH0Growth
