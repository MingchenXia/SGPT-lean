import SGPT.PSH.HermitianProductsMonotonicity

/-!
# Positive scalar homogeneity of the genuine Hermitian products

Both corrected potentials and their nonclosed smooth residual are scaled.
The resulting literal current is multiplied by the expected degree power.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianProducts

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorSmooth LocalBedfordTaylorForms
  LocalBedfordTaylorCalculus LocalBedfordTaylorContinuity LocalBedfordTaylorLocality
  LocalBedfordTaylorSmoothProductDensity LocalBedfordTaylorCollar
  LocalBedfordTaylorDecreasing TopDegreeDensity ConstantFormProducts
open scoped Topology Distributions ContDiff

variable {n : ℕ} {U : Opens (ComplexModel n)}

theorem isLocallyBoundedPshOn_pos_smul {v : ComplexModel n → ℝ}
    (hv : IsLocallyBoundedPshOn U v) {c : ℝ} (hc : 0 < c) :
    IsLocallyBoundedPshOn U (fun z => c * v z) := by
  refine ⟨?_, fun z hz => ?_⟩
  · simpa only [EReal.coe_mul] using hv.1.const_mul hc
  · obtain ⟨V, hzV, hVU, C, hC⟩ := hv.2 z hz
    refine ⟨V, hzV, hVU, c * C, fun y hy => ?_⟩
    rw [abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left (hC y hy) hc.le

theorem decreasingApproximation_pos_smul
    {v : ComplexModel n → ℝ} {f : ℕ → ComplexModel n → ℝ}
    (hf : IsDecreasingApproximation U v f) {c : ℝ} (hc : 0 < c) :
    IsDecreasingApproximation U (fun z => c * v z) (fun j z => c * f j z) := by
  refine ⟨fun j => isSmoothPshOn_of_psh ((hf.1 j).1.const_smul c) ?_, ?_, ?_⟩
  · simpa only [EReal.coe_mul] using (hf.1 j).2.1.const_mul hc
  · intro z hz j k hjk
    exact mul_le_mul_of_nonneg_left (hf.2.1 z hz hjk) hc.le
  · intro z hz
    exact (hf.2.2 z hz).const_mul c

theorem wedgeProd_const_smul : ∀ (p : ℕ) (α : Fin p → RealForm n 2) (c : ℝ),
    wedgeProd p (fun i => c • α i) = c ^ p • wedgeProd p α
  | 0, _, _ => by simp only [wedgeProd_zero, pow_zero, one_smul]
  | p + 1, α, c => by
    rw [wedgeProd_succ, wedgeProd_succ, wedgeProd_const_smul p _ c,
      coordinateWedge_smul_left, coordinateWedge_smul_right, smul_smul, pow_succ]

theorem backgroundExpansion_pos_smul_smooth (p r : ℕ)
    (v : Fin p → ComplexModel n → ℝ)
    (hv : ∀ i, ContDiffOn ℝ ∞ (v i) U)
    (hvp : ∀ i, PlurisubharmonicOn (fun z => (v i z : EReal)) U)
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (hσS : ∀ z ∈ U, σ z ∈ formSpan n 1)
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) {c : ℝ} (hc : 0 < c) :
    backgroundExpansion p r (fun i z => c * v i z) (hσ.const_smul c) T =
      c ^ p • backgroundExpansion p r v hσ T := by
  have hcv : ∀ i, ContDiffOn ℝ ∞ (fun z => c * v i z) U :=
    fun i => (hv i).const_smul c
  have hcvp : ∀ i, PlurisubharmonicOn (fun z => ((c * v i z : ℝ) : EReal)) U :=
    fun i => by simpa only [EReal.coe_mul] using (hvp i).const_mul hc
  rw [backgroundExpansion_smooth p r _ hcv hcvp _
    (fun z hz => (formSpan n 1).smul_mem c (hσS z hz)) T hT hTc,
    backgroundExpansion_smooth p r v hv hvp hσ hσS T hT hTc,
    ← wedgeForm_smul]
  apply wedgeForm_congr
  intro z hz
  change wedgeProd p (fun i => ddcForm (fun y => c * v i y) z + c • σ z) =
    c ^ p • wedgeProd p (fun i => ddcForm (v i) z + σ z)
  have heq : (fun i => ddcForm (fun y => c * v i y) z + c • σ z) =
      fun i => c • (ddcForm (v i) z + σ z) := by
    funext i
    change smoothDDC (fun y => c • v i y) z + c • σ z =
      c • (smoothDDC (v i) z + σ z)
    rw [smoothDDC_smul U.isOpen (hv i) c hz, smul_add]
  rw [heq, wedgeProd_const_smul]

theorem backgroundExpansion_pos_smul_of_approximation (p r : ℕ)
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    (f : ℕ → Fin p → ComplexModel n → ℝ)
    (hf : ∀ i, IsDecreasingApproximation U (v i) (fun j => f j i))
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (hσS : ∀ z ∈ U, σ z ∈ formSpan n 1) {c : ℝ} (hc : 0 < c) :
    backgroundExpansion p r (fun i z => c * v i z) (hσ.const_smul c) T =
      c ^ p • backgroundExpansion p r v hσ T := by
  have hf' (i : Fin p) := decreasingApproximation_pos_smul (hf i) hc
  have heq (j : ℕ) := backgroundExpansion_pos_smul_smooth p r (f j)
    (fun i => ((hf i).1 j).1) (fun i => ((hf i).1 j).2.1) hσ hσS T hT hTc hc
  have hleft := backgroundExpansion_decreasing p r T hT hTc
    (fun j i z => c * f j i z) (fun i z => c * v i z)
    (fun j i => isLocallyBoundedPshOn_of_isSmoothPshOn ((hf' i).1 j))
    (fun i => isLocallyBoundedPshOn_pos_smul (hv i) hc)
    (fun i z hz => (hf' i).2.1 z hz) (fun i z hz => (hf' i).2.2 z hz) (hσ.const_smul c)
  have hright := backgroundExpansion_decreasing p r T hT hTc f v
    (fun j i => isLocallyBoundedPshOn_of_isSmoothPshOn ((hf i).1 j)) hv
    (fun i z hz => (hf i).2.1 z hz) (fun i z hz => (hf i).2.2 z hz) hσ
  ext γ φ
  apply tendsto_nhds_unique (hleft γ φ)
  simpa only [heq, LinearMap.smul_apply, _root_.smul_apply, smul_eq_mul]
    using (hright γ φ).const_mul (c ^ p)

/-- Positive scalar homogeneity of the actual nonclosed-background product
on an arbitrary open domain. -/
theorem backgroundExpansion_pos_smul (p r : ℕ)
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (hσS : ∀ z ∈ U, σ z ∈ formSpan n 1) {c : ℝ} (hc : 0 < c) :
    backgroundExpansion p r (fun i z => c * v i z) (hσ.const_smul c) T =
      c ^ p • backgroundExpansion p r v hσ T := by
  classical
  apply eq_of_local
  intro x hx
  obtain ⟨a, ha, hball⟩ := Metric.isOpen_iff.mp U.isOpen x hx
  let A : Opens (ComplexModel n) := ⟨Metric.ball x (a / 2), Metric.isOpen_ball⟩
  have hAU : A ≤ U := fun z hz => hball (Metric.ball_subset_ball (by linarith) hz)
  have hArel : RelativelyCompactIn A U := relativelyCompactIn_half_ball ha hball
  refine ⟨A, hAU, Metric.mem_ball_self (half_pos ha), ?_⟩
  change restrict hAU (backgroundExpansion p r (fun i z => c * v i z) (hσ.const_smul c) T) =
    c ^ p • restrict hAU (backgroundExpansion p r v hσ T)
  rw [backgroundExpansion_restrict hAU p r T hT hTc _
    (fun i => isLocallyBoundedPshOn_pos_smul (hv i) hc),
    backgroundExpansion_restrict hAU p r T hT hTc v hv hσ]
  have happrox : ∀ i, ∃ f : ℕ → ComplexModel n → ℝ,
      IsDecreasingApproximation A (v i) f := fun i =>
    HolomorphicPullback.exists_decreasingMollifierApproximation (hv i) hArel
  choose f hf using happrox
  exact backgroundExpansion_pos_smul_of_approximation p r (restrict hAU T)
    (isPositive_restrict hT hAU) (isClosedAny_restrict hTc hAU) v
    (fun i => isLocallyBoundedPshOn_mono (hv i) hAU) (fun j i => f i j) hf
    (hσ.mono hAU) (fun z hz => hσS z (hAU hz)) hc

end SGPT.PSH.HermitianProducts
