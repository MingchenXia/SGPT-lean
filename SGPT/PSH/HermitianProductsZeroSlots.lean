import SGPT.PSH.HermitianProductsSmoothExpansion
import SGPT.PSH.HermitianProductsLocality
import SGPT.PSH.HermitianProductsCorrectionShift
import SGPT.PSH.HermitianComparisonTraceDomination
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCalculus

/-!
# Inserting actual zero-potential slots into Hermitian products

A corrected zero slot is the original smooth correction `q`. Its factor
is the actual form `ddᶜq + σ`. Smooth finite multilinearity proves the slot
identity; genuine decreasing PSH approximation and current locality extend
it to the original locally bounded corrected factors.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianProducts

open Set Filter Metric MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorForms LocalBedfordTaylorSmooth
  LocalBedfordTaylorSmoothProductDensity LocalBedfordTaylorContinuity
  LocalBedfordTaylorLocality LocalBedfordTaylorCollar LocalBedfordTaylorCalculus LocalBedfordTaylorDecreasing
  TopDegreeDensity ConstantFormProducts
open SGPT.PSH.HermitianComparisonTraceDomination
open scoped Topology Distributions ContDiff

variable {n : ℕ} {U : Opens (ComplexModel n)}

private theorem wedgeForm_cast_source {a b r k : ℕ} (hab : a = b) (h : r + k = a)
    (T : LocalProductCurrent n U a) {α : ComplexModel n → RealForm n (2 * k)}
    (hα : ContDiffOn ℝ ∞ α U) :
    wedgeForm (h.trans hab) (castLPC hab T) hα = wedgeForm h T hα := by
  subst b
  rfl

private theorem append_factor_forms (p l : ℕ)
    (v : Fin p → ComplexModel n → ℝ) (q : ComplexModel n → ℝ)
    (σ : ComplexModel n → RealForm n 2) (z : ComplexModel n) :
    (fun i => ddcForm (Fin.append v (fun _ : Fin l => q) i) z + σ z) =
      Fin.append (fun i => ddcForm (v i) z + σ z)
        (fun _ : Fin l => ddcForm q z + σ z) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left, Fin.append_left]
  · rw [Fin.append_right, Fin.append_right]

/-- Actual smooth insertion of repeated corrected-zero slots, retaining
the original current and the literal smooth residual. -/
theorem backgroundExpansion_append_correction_smooth (p l r : ℕ)
    (T : LocalProductCurrent n U (r + (p + l))) (hT : IsPositive T)
    (hTc : IsClosedAny (r + (p + l)) T)
    (v : Fin p → ComplexModel n → ℝ)
    (hv : ∀ i, ContDiffOn ℝ ∞ (v i) U)
    (hvp : ∀ i, PlurisubharmonicOn (fun z => (v i z : EReal)) U)
    {q : ComplexModel n → ℝ} (hq : ContDiffOn ℝ ∞ q U)
    (hqp : PlurisubharmonicOn (fun z => (q z : EReal)) U)
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (hσS : ∀ z ∈ U, σ z ∈ formSpan n 1) :
    backgroundExpansion (p + l) r (Fin.append v (fun _ : Fin l => q)) hσ T =
      wedgeForm rfl
        (backgroundExpansion p (r + l) v hσ
          (castLPC (by omega : r + (p + l) = (r + l) + p) T))
        (contDiffOn_formPower ((contDiffOn_ddcForm hq).add hσ) l) := by
  classical
  have hcast : r + (p + l) = (r + l) + p := by omega
  have happ : ∀ i, ContDiffOn ℝ ∞ (Fin.append v (fun _ : Fin l => q) i) U := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using hv j
    · simpa only [Fin.append_right] using hq
  have happp : ∀ i, PlurisubharmonicOn
      (fun z => (Fin.append v (fun _ : Fin l => q) i z : EReal)) U := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using hvp j
    · simpa only [Fin.append_right] using hqp
  let α : ComplexModel n → RealForm n (2 * p) :=
    fun z => wedgeProd p (fun i => ddcForm (v i) z + σ z)
  have hα : ContDiffOn ℝ ∞ α U := contDiffOn_wedgeProd p
    (fun i z => ddcForm (v i) z + σ z) (fun i => (contDiffOn_ddcForm (hv i)).add hσ)
  have hαS : ∀ z ∈ U, α z ∈ formSpan n p := by
    intro z hz
    apply wedgeProd_mem_formSpan
    intro i
    exact (formSpan n 1).add_mem (smooth_ddcForm_mem_formSpan (hv i) z hz) (hσS z hz)
  have hβ := contDiffOn_formPower ((contDiffOn_ddcForm hq).add hσ) l
  have hβS : ∀ z ∈ U, formPower (ddcForm q z + σ z) l ∈ formSpan n l := by
    intro z hz
    rw [formPower_eq_wedgeProd]
    apply wedgeProd_mem_formSpan
    intro _
    exact (formSpan n 1).add_mem (smooth_ddcForm_mem_formSpan hq z hz) (hσS z hz)
  rw [backgroundExpansion_smooth (p + l) r _ happ happp hσ hσS T hT hTc,
    backgroundExpansion_smooth p (r + l) v hv hvp hσ hσS _
      (isPositive_castLPC hcast hT) (isClosedAny_castLPC hcast hTc)]
  change wedgeForm rfl T _ = wedgeForm rfl (wedgeForm rfl (castLPC hcast T) hα) hβ
  rw [HermitianSmoothWedgeAssociation.wedgeForm_wedge rfl (castLPC hcast T) hα hβ hαS hβS,
    wedgeForm_cast_source hcast rfl T]
  apply wedgeForm_congr
  intro z _
  change wedgeProd (p + l) (fun i => ddcForm (Fin.append v (fun _ : Fin l => q) i) z + σ z) =
    wedgeTo (by omega : 2 * p + 2 * l = 2 * (p + l)) (α z)
      (formPower (ddcForm q z + σ z) l)
  rw [append_factor_forms, wedgeProd_append, formPower_eq_wedgeProd]

/-- Genuine decreasing PSH approximation preserves the inserted smooth
correction slots and the literal background current identity. -/
theorem backgroundExpansion_append_correction_of_approximation (p l r : ℕ)
    (T : LocalProductCurrent n U (r + (p + l))) (hT : IsPositive T)
    (hTc : IsClosedAny (r + (p + l)) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    (f : ℕ → Fin p → ComplexModel n → ℝ)
    (hf : ∀ i, IsDecreasingApproximation U (v i) (fun j => f j i))
    {q : ComplexModel n → ℝ} (hq : ContDiffOn ℝ ∞ q U)
    (hqp : PlurisubharmonicOn (fun z => (q z : EReal)) U)
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (hσS : ∀ z ∈ U, σ z ∈ formSpan n 1) :
    backgroundExpansion (p + l) r (Fin.append v (fun _ : Fin l => q)) hσ T =
      wedgeForm rfl
        (backgroundExpansion p (r + l) v hσ
          (castLPC (by omega : r + (p + l) = (r + l) + p) T))
        (contDiffOn_formPower ((contDiffOn_ddcForm hq).add hσ) l) := by
  have hcast : r + (p + l) = (r + l) + p := by omega
  have hqB := isLocallyBoundedPshOn_of_continuousOn hqp hq.continuousOn
  have hvapp : ∀ i, IsLocallyBoundedPshOn U (Fin.append v (fun _ : Fin l => q) i) := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using hv j
    · simpa only [Fin.append_right] using hqB
  have hfapp : ∀ j i, IsLocallyBoundedPshOn U
      (Fin.append (f j) (fun _ : Fin l => q) i) := by
    intro j i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · simpa only [Fin.append_left] using isLocallyBoundedPshOn_of_isSmoothPshOn ((hf a).1 j)
    · simpa only [Fin.append_right] using hqB
  have hanti : ∀ i z, z ∈ U → Antitone
      (fun j => Fin.append (f j) (fun _ : Fin l => q) i z) := by
    intro i z hz
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · simpa only [Fin.append_left] using (hf a).2.1 z hz
    · simpa only [Fin.append_right] using (antitone_const : Antitone (fun _ : ℕ => q z))
  have hlim : ∀ i z, z ∈ U → Tendsto
      (fun j => Fin.append (f j) (fun _ : Fin l => q) i z) atTop
      (𝓝 (Fin.append v (fun _ : Fin l => q) i z)) := by
    intro i z hz
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · simpa only [Fin.append_left] using (hf a).2.2 z hz
    · simpa only [Fin.append_right] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => q z) atTop (𝓝 (q z)))
  have hleft := backgroundExpansion_decreasing (p + l) r T hT hTc
    (fun j => Fin.append (f j) (fun _ : Fin l => q))
    (Fin.append v (fun _ : Fin l => q)) hfapp hvapp hanti hlim hσ
  have hselected := backgroundExpansion_decreasing p (r + l) (castLPC hcast T)
    (isPositive_castLPC hcast hT) (isClosedAny_castLPC hcast hTc) f v
    (fun j i => isLocallyBoundedPshOn_of_isSmoothPshOn ((hf i).1 j)) hv
    (fun i z hz => (hf i).2.1 z hz) (fun i z hz => (hf i).2.2 z hz) hσ
  have hright := weakTendsto_wedgeForm rfl hselected
    (contDiffOn_formPower ((contDiffOn_ddcForm hq).add hσ) l)
  have heq (j : ℕ) := backgroundExpansion_append_correction_smooth p l r T hT hTc
    (f j) (fun i => ((hf i).1 j).1) (fun i => ((hf i).1 j).2.1) hq hqp hσ hσS
  ext γ φ
  apply tendsto_nhds_unique (hleft γ φ)
  simpa only [heq] using hright γ φ

private theorem castLPC_restrict {a b : ℕ} (hab : a = b)
    {V : Opens (ComplexModel n)} (hVU : V ≤ U) (T : LocalProductCurrent n U a) :
    restrict hVU (castLPC hab T) = castLPC hab (restrict hVU T) := by
  subst b
  rfl

/-- Inserting corrected zero slots equals wedging with the actual smooth
background form on the entire original bounded PSH domain. All approximation
systems and relatively compact subdomains are produced internally. -/
theorem backgroundExpansion_append_correction (p l r : ℕ)
    (T : LocalProductCurrent n U (r + (p + l))) (hT : IsPositive T)
    (hTc : IsClosedAny (r + (p + l)) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {q : ComplexModel n → ℝ} (hq : ContDiffOn ℝ ∞ q U)
    (hqp : PlurisubharmonicOn (fun z => (q z : EReal)) U)
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (hσS : ∀ z ∈ U, σ z ∈ formSpan n 1) :
    backgroundExpansion (p + l) r (Fin.append v (fun _ : Fin l => q)) hσ T =
      wedgeForm rfl
        (backgroundExpansion p (r + l) v hσ
          (castLPC (by omega : r + (p + l) = (r + l) + p) T))
        (contDiffOn_formPower ((contDiffOn_ddcForm hq).add hσ) l) := by
  classical
  apply eq_of_local
  intro x hx
  obtain ⟨a, ha, hball⟩ := Metric.isOpen_iff.mp U.isOpen x hx
  let A : Opens (ComplexModel n) := ⟨ball x (a / 2), isOpen_ball⟩
  have hAU : A ≤ U := fun z hz => hball (ball_subset_ball (by linarith) hz)
  have hArel : RelativelyCompactIn A U := relativelyCompactIn_half_ball ha hball
  have happrox : ∀ i, ∃ f : ℕ → ComplexModel n → ℝ,
      IsDecreasingApproximation A (v i) f :=
    fun i => HolomorphicPullback.exists_decreasingMollifierApproximation (hv i) hArel
  choose f hf using happrox
  have hqB := isLocallyBoundedPshOn_of_continuousOn hqp hq.continuousOn
  have hvapp : ∀ i, IsLocallyBoundedPshOn U (Fin.append v (fun _ : Fin l => q) i) := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using hv j
    · simpa only [Fin.append_right] using hqB
  have hcast : r + (p + l) = (r + l) + p := by omega
  refine ⟨A, hAU, mem_ball_self (half_pos ha), ?_⟩
  rw [backgroundExpansion_restrict hAU (p + l) r T hT hTc _ hvapp hσ,
    wedgeForm_restrict hAU,
    backgroundExpansion_restrict hAU p (r + l) (castLPC hcast T)
      (isPositive_castLPC hcast hT) (isClosedAny_castLPC hcast hTc) v hv hσ,
    castLPC_restrict hcast hAU T]
  exact backgroundExpansion_append_correction_of_approximation p l r (restrict hAU T)
    (isPositive_restrict hT hAU) (isClosedAny_restrict hTc hAU) v
    (fun i => isLocallyBoundedPshOn_mono (hv i) hAU) (fun j i => f i j) hf
    (hq.mono hAU) (hqp.mono hAU) (hσ.mono hAU) (fun z hz => hσS z (hAU hz))

end SGPT.PSH.HermitianProducts
