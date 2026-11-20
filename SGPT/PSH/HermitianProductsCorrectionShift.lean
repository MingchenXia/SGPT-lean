import SGPT.PSH.HermitianProductsRadialApproximation
import SGPT.PSH.HermitianProductsLocality
import SGPT.PSH.HermitianProductsSmoothExpansion
import SGPT.Foundations.Analysis.Pending.ActualSmoothLocalQuadraticCorrection

/-!
# Smooth PSH shifts in the actual decreasing approximation

Adding a fixed smooth PSH function preserves the explicit decreasing smooth
PSH approximation. This is the approximation input for correction
independence of the nonclosed-background expansion.
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
  LocalBedfordTaylorSmoothDensity LocalBedfordTaylorSmoothProductDensity
  LocalBedfordTaylorCollar LocalBedfordTaylorDecreasing TopDegreeDensity
open scoped Topology Distributions ContDiff

variable {n : ℕ} {U : Opens (ComplexModel n)}

/-- Every actual smooth real `ddᶜ` form has the required one-one span type;
its potential need not be PSH. -/
theorem smooth_ddcForm_mem_formSpan {g : ComplexModel n → ℝ}
    (hg : ContDiffOn ℝ ∞ g U) : ∀ z ∈ U, ddcForm g z ∈ formSpan n 1 := by
  intro z hz
  apply oneOne_mem_formSpan
  exact smoothDDC_isOneOne ((hg.contDiffAt (U.isOpen.mem_nhds hz)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))

/-- The explicit decreasing smooth PSH approximation is preserved by adding
a fixed genuine smooth PSH function; its pointwise limit changes by the same
function. -/
theorem decreasingApproximation_add_smooth_psh
    {v g : ComplexModel n → ℝ} {f : ℕ → ComplexModel n → ℝ}
    (hf : IsDecreasingApproximation U v f) (hg : ContDiffOn ℝ ∞ g U)
    (hgp : PlurisubharmonicOn (fun z => (g z : EReal)) U) :
    IsDecreasingApproximation U (fun z => v z + g z) (fun j z => f j z + g z) := by
  refine ⟨fun j => isSmoothPshOn_of_psh ((hf.1 j).1.add hg) ?_, ?_, ?_⟩
  · simpa only [EReal.coe_add] using (hf.1 j).2.1.add hgp
  · intro z hz j k hjk
    exact add_le_add (hf.2.1 z hz hjk) (le_refl (g z))
  · intro z hz
    exact (hf.2.2 z hz).add_const (g z)

/-- Smooth PSH shifts cancel against the residual in the literal expansion,
as follows from the actual smooth identity and decreasing BT continuity. -/
theorem backgroundExpansion_add_smooth_psh_of_approximation (p r : ℕ)
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    (f : ℕ → Fin p → ComplexModel n → ℝ)
    (hf : ∀ i, IsDecreasingApproximation U (v i) (fun j => f j i))
    {g : ComplexModel n → ℝ} (hg : ContDiffOn ℝ ∞ g U)
    (hgp : PlurisubharmonicOn (fun z => (g z : EReal)) U)
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (hσS : ∀ z ∈ U, σ z ∈ formSpan n 1) :
    backgroundExpansion p r (fun i z => v i z + g z)
      (hσ.sub (contDiffOn_ddcForm hg)) T = backgroundExpansion p r v hσ T := by
  classical
  have hgB := isLocallyBoundedPshOn_of_continuousOn hgp hg.continuousOn
  have hf' (i : Fin p) := decreasingApproximation_add_smooth_psh (hf i) hg hgp
  have hτS : ∀ z ∈ U, σ z - ddcForm g z ∈ formSpan n 1 :=
    fun z hz => (formSpan n 1).sub_mem (hσS z hz) (smooth_ddcForm_mem_formSpan hg z hz)
  have heq (j : ℕ) :
      backgroundExpansion p r (fun i z => f j i z + g z)
        (hσ.sub (contDiffOn_ddcForm hg)) T = backgroundExpansion p r (f j) hσ T := by
    rw [backgroundExpansion_smooth p r _ (fun i => ((hf' i).1 j).1)
      (fun i => ((hf' i).1 j).2.1) _ hτS T hT hTc,
      backgroundExpansion_smooth p r _ (fun i => ((hf i).1 j).1)
        (fun i => ((hf i).1 j).2.1) _ hσS T hT hTc]
    apply wedgeForm_congr
    intro z hz
    change wedgeProd p (fun i => ddcForm (fun y => f j i y + g y) z +
      (σ z - ddcForm g z)) = wedgeProd p (fun i => ddcForm (f j i) z + σ z)
    congr 1
    funext i
    dsimp only [ddcForm]
    rw [smoothDDC_add U.isOpen ((hf i).1 j).1 hg hz]
    abel
  have hleft := backgroundExpansion_decreasing p r T hT hTc
    (fun j i z => f j i z + g z) (fun i z => v i z + g z)
    (fun j i => isLocallyBoundedPshOn_of_isSmoothPshOn ((hf' i).1 j))
    (fun i => isLocallyBoundedPshOn_add (hv i) hgB)
    (fun i z hz => (hf' i).2.1 z hz) (fun i z hz => (hf' i).2.2 z hz)
    (hσ.sub (contDiffOn_ddcForm hg))
  have hright := backgroundExpansion_decreasing p r T hT hTc f v
    (fun j i => isLocallyBoundedPshOn_of_isSmoothPshOn ((hf i).1 j)) hv
    (fun i z hz => (hf i).2.1 z hz) (fun i z hz => (hf i).2.2 z hz) hσ
  ext γ φ
  apply tendsto_nhds_unique (hleft γ φ)
  simpa only [heq] using hright γ φ

/-- A smooth PSH correction can be changed without changing the actual
nonclosed-background current, on any open domain. -/
theorem backgroundExpansion_add_smooth_psh (p r : ℕ)
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {g : ComplexModel n → ℝ} (hg : ContDiffOn ℝ ∞ g U)
    (hgp : PlurisubharmonicOn (fun z => (g z : EReal)) U)
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (hσS : ∀ z ∈ U, σ z ∈ formSpan n 1) :
    backgroundExpansion p r (fun i z => v i z + g z)
      (hσ.sub (contDiffOn_ddcForm hg)) T = backgroundExpansion p r v hσ T := by
  classical
  have hgB := isLocallyBoundedPshOn_of_continuousOn hgp hg.continuousOn
  apply eq_of_local
  intro x hx
  obtain ⟨a, ha, hball⟩ := Metric.isOpen_iff.mp U.isOpen x hx
  let A : Opens (ComplexModel n) := ⟨Metric.ball x (a / 2), Metric.isOpen_ball⟩
  have hAU : A ≤ U := fun z hz => hball (Metric.ball_subset_ball (by linarith) hz)
  have hArel : RelativelyCompactIn A U := relativelyCompactIn_half_ball ha hball
  refine ⟨A, hAU, Metric.mem_ball_self (half_pos ha), ?_⟩
  rw [backgroundExpansion_restrict hAU p r T hT hTc _
    (fun i => isLocallyBoundedPshOn_add (hv i) hgB),
    backgroundExpansion_restrict hAU p r T hT hTc v hv]
  have happrox : ∀ i, ∃ f : ℕ → ComplexModel n → ℝ,
      IsDecreasingApproximation A (v i) f := fun i =>
    HolomorphicPullback.exists_decreasingMollifierApproximation (hv i) hArel
  choose f hf using happrox
  exact backgroundExpansion_add_smooth_psh_of_approximation p r (restrict hAU T)
    (isPositive_restrict hT hAU) (isClosedAny_restrict hTc hAU) v
    (fun i => isLocallyBoundedPshOn_mono (hv i) hAU) (fun j i => f i j) hf
    (hg.mono hAU) (hgp.mono hAU) (hσ.mono hAU) (fun z hz => hσS z (hAU hz))

/-- Changing any smooth local correction preserves the actual Hermitian
current whenever both corrected tuples are locally bounded PSH. A local
positive quadratic reduces the arbitrary smooth change to two PSH changes. -/
theorem backgroundExpansion_add_smooth (p r : ℕ)
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {g : ComplexModel n → ℝ} (hg : ContDiffOn ℝ ∞ g U)
    (hvg : ∀ i, IsLocallyBoundedPshOn U (fun z => v i z + g z))
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (hσS : ∀ z ∈ U, σ z ∈ formSpan n 1) :
    backgroundExpansion p r (fun i z => v i z + g z)
      (hσ.sub (contDiffOn_ddcForm hg)) T = backgroundExpansion p r v hσ T := by
  apply eq_of_local
  intro x hx
  obtain ⟨A, a, _, ha, hBU, hqPsh, hgqPsh⟩ :=
    ActualSmoothLocalQuadraticCorrection.exists_positive_quadratic_correction hg hx
  let B : Opens (ComplexModel n) := ⟨Metric.ball x a, Metric.isOpen_ball⟩
  have hBU : B ≤ U := hBU
  let q := ballPot A x 0
  have hq : ContDiffOn ℝ ∞ q B := (contDiff_ballPot A x 0).contDiffOn
  have hgB := hg.mono hBU
  have hσB := hσ.mono hBU
  have hσBS : ∀ z ∈ B, σ z ∈ formSpan n 1 := fun z hz => hσS z (hBU hz)
  have hTB := isPositive_restrict hT hBU
  have hTcB := isClosedAny_restrict hTc hBU
  have hvB (i : Fin p) := isLocallyBoundedPshOn_mono (hv i) hBU
  have hvgB (i : Fin p) := isLocallyBoundedPshOn_mono (hvg i) hBU
  refine ⟨B, hBU, Metric.mem_ball_self ha, ?_⟩
  rw [backgroundExpansion_restrict hBU p r T hT hTc _ hvg,
    backgroundExpansion_restrict hBU p r T hT hTc v hv]
  have h₁ := backgroundExpansion_add_smooth_psh p r (restrict hBU T) hTB hTcB
    v hvB (hgB.add hq) hgqPsh hσB hσBS
  have hτS : ∀ z ∈ B, σ z - ddcForm g z ∈ formSpan n 1 :=
    fun z hz => (formSpan n 1).sub_mem (hσBS z hz) (smooth_ddcForm_mem_formSpan hgB z hz)
  have h₂ := backgroundExpansion_add_smooth_psh p r (restrict hBU T) hTB hTcB
    (fun i z => v i z + g z) hvgB hq hqPsh
    (hσB.sub (contDiffOn_ddcForm hgB)) hτS
  calc
    _ = backgroundExpansion p r (fun i z => (v i z + g z) + q z)
        ((hσB.sub (contDiffOn_ddcForm hgB)).sub (contDiffOn_ddcForm hq))
        (restrict hBU T) := h₂.symm
    _ = backgroundExpansion p r (fun i z => v i z + (g z + q z))
        (hσB.sub (contDiffOn_ddcForm (hgB.add hq))) (restrict hBU T) := by
      apply backgroundExpansion_congr
      · intro i z _
        exact add_assoc _ _ _
      · intro z hz
        change σ z - smoothDDC g z - smoothDDC q z =
          σ z - smoothDDC (fun y => g y + q y) z
        rw [smoothDDC_add B.isOpen hgB hq hz]
        abel
    _ = _ := h₁

end SGPT.PSH.HermitianProducts
