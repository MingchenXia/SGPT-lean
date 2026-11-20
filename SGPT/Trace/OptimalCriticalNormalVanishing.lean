import SGPT.Trace.BertiniExactNormalCoordinates
import SGPT.Trace.OTResFlat
import SGPT.Foundations.Analysis.Pending.OTSliceVanishing

/-!
# Critical normal energy forces original physical fibre vanishing

The real physical numerator and original smooth positive volume are
transported through SAME-W exact normal flattening. No arbitrary normal
coordinate, Euclidean physical norm or Hodge measure is substituted.
Blueprint: work/sgpt-resume-20261114/bert-e2-critical-vanishing/blueprint/bert-e2-critical-vanishing.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.OptimalCriticalNormalVanishing
open Set Filter MeasureTheory Bundle Metric
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1 SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open SGPT.Trace.TwistedL2 SGPT.Trace.OTMargin SGPT.Trace.BertiniExactNormalCoordinates

variable {m : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [MeasurableSpace X] [BorelSpace X]

/-- A continuous ORIGINAL real numerator with finite true-normal quotient
energy is nonpositive at an original submersion zero. -/
theorem nonpos_of_finite_critical_normal_energy {μ : Measure X}
    (hμ : IsSmoothPositiveVolume (n := m + 1) μ) {f : X → ℂ}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) ∞ f)
    {x : X} (hsub : Function.Surjective (mfderiv 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) f x))
    (hfx : f x = 0) {g : X → ℝ} (hg : Continuous g)
    (hfin : (∫⁻ y, ENNReal.ofReal (g y / ‖f y‖ ^ 2) ∂μ) ≠ ⊤) : g x ≤ 0 := by
  by_contra hpos
  rw [not_le] at hpos
  obtain ⟨hn, F, hxF, hF0, hread⟩ := exists_exact_normal_flatData hf hsub hfx
  have hidx : (⟨m + 1 - 1, Nat.sub_lt hn one_pos⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by change m + 1 - 1 = m; omega)
  have hlast : ∀ y ∈ F.ambSource, (fcoord F y) (Fin.last m) = f y := by
    intro y hy
    rw [← hidx]
    exact hread y hy
  have h0t : (0 : ComplexModel (m + 1)) ∈ F.flat.target := by
    rw [← hF0]
    exact fcoord_mem F hxF
  have hinv0 : finv F 0 = x := by
    rw [← hF0]
    exact finv_fcoord F hxF
  have hgc : ContinuousOn (fun z => g (finv F z)) F.flat.target :=
    hg.comp_continuousOn (continuousOn_finv F)
  let O := F.flat.target ∩ (fun z => g (finv F z)) ⁻¹' Ioi 0
  have hOo : IsOpen O := hgc.isOpen_inter_preimage F.flat.open_target isOpen_Ioi
  have h0O : (0 : ComplexModel (m + 1)) ∈ O := ⟨h0t, by
    change 0 < g (finv F 0)
    rwa [hinv0]⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hOo 0 h0O
  let K := closedBall (0 : ComplexModel (m + 1)) (r / 2)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKO : K ⊆ O := (closedBall_subset_ball (by linarith : r / 2 < r)).trans hball
  have hKt : K ⊆ F.flat.target := fun z hz => (hKO hz).1
  let H : X → ℝ≥0∞ := fun y => ENNReal.ofReal (g y / ‖f y‖ ^ 2)
  have hHm : Measurable H := ENNReal.measurable_ofReal.comp
    (hg.measurable.div ((hf.continuous.norm.pow 2).measurable))
  obtain ⟨C, -, hC⟩ := lintegral_le_finv_image F hμ hK hKt
  have hbound : (∫⁻ z in K, H (finv F z)) ≤ ENNReal.ofReal C * ∫⁻ y, H y ∂μ :=
    (hC H hHm).trans (mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _))
  have hfiniteK : (∫⁻ z in K, H (finv F z)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hbound
  have heqK : (∫⁻ z in K, ENNReal.ofReal (g (finv F z) / ‖z (Fin.last m)‖ ^ 2)) =
      ∫⁻ z in K, H (finv F z) := by
    refine setLIntegral_congr_fun hK.isClosed.measurableSet fun z hz => ?_
    dsimp only [H]
    rw [exact_normal_inverse hlast (hKt hz)]
  have hfiniteLast : (∫⁻ z in K, ENNReal.ofReal (g (finv F z) / ‖z (Fin.last m)‖ ^ 2)) ≠ ⊤ :=
    heqK ▸ hfiniteK
  have hBK : ball (0 : ComplexModel (m + 1)) (r / 4) ⊆ K :=
    (ball_subset_closedBall : ball (0 : ComplexModel (m + 1)) (r / 4) ⊆ closedBall 0 (r / 4)).trans
      (closedBall_subset_closedBall (by linarith : r / 4 ≤ r / 2))
  have hfiniteB : (∫⁻ z in ball (0 : ComplexModel (m + 1)) (r / 4),
      ENNReal.ofReal (‖(1 : ℂ)‖ ^ 2 * g (finv F z) / ‖z (Fin.last m)‖ ^ 2)) ≠ ⊤ := by
    simp only [norm_one, one_pow, one_mul]
    exact ne_top_of_le_ne_top hfiniteLast (lintegral_mono_set hBK)
  have hone := OTChen.eq_zero_of_lintegral_div_normSq_ne_top isOpen_ball
    (continuous_const.continuousOn : ContinuousOn (fun _ : ComplexModel (m + 1) => (1 : ℂ)) _)
    (hgc.mono (fun z hz => hKt (hBK hz)))
    (fun z hz => (hKO (hBK hz)).2) hfiniteB
    (mem_ball_self (by positivity : 0 < r / 4)) (by simp : (0 : ComplexModel (m + 1)) (Fin.last m) = 0)
  exact one_ne_zero hone

/-- The SAME physical fibre vector vanishes from its true-normal critical
energy; continuity of its SAME physical squared norm is produced. -/
theorem physical_section_eq_zero_of_finite_critical_normal_energy
    (L : HermitianHolomorphicLineBundle.{0, 0} (m + 1) X) (hL : IsSourceSmoothHermitianMetric L)
    {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := m + 1) μ) {f : X → ℂ}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) ∞ f)
    {x : X} (hsub : Function.Surjective (mfderiv 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) f x))
    (hfx : f x = 0) {U : (y : X) → L.Fiber y} (hU : IsSmoothSectionOn L U univ)
    {W : X → ℝ} (hW : Continuous W) (hWx : 0 < W x)
    (hfin : (∫⁻ y, ENNReal.ofReal (‖U y‖ ^ 2 * W y / ‖f y‖ ^ 2) ∂μ) ≠ ⊤) : U x = 0 := by
  have hN : Continuous (fun y => ‖U y‖ ^ 2) :=
    continuous_of_chartSmooth' (SGPT.Trace.OTRes.chartSmooth_normSq L hL hU)
  have hn := nonpos_of_finite_critical_normal_energy hμ hf hsub hfx (hN.mul hW) hfin
  change ‖U x‖ ^ 2 * W x ≤ 0 at hn
  have hnorm : ‖U x‖ ^ 2 = 0 := le_antisymm (nonpos_of_mul_nonpos_left hn hWx) (sq_nonneg _)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)

end SGPT.Trace.OptimalCriticalNormalVanishing
