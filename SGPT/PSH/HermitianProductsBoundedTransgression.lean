import SGPT.PSH.HermitianProductsTransgressionLimits
import SGPT.PSH.HermitianProductsRadialApproximation

/-! Distinguished-factor transgression on the original bounded PSH domain.
The actual radial mollifiers and both weak limits are produced internally. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianProducts

open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions ContDiff Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorSmooth LocalBedfordTaylorForms
  LocalBedfordTaylorCollar LocalBedfordTaylorContinuity LocalBedfordTaylorLocality
  LocalBedfordTaylorDecreasing LocalCurrentPullbackDdc
open HermitianComparisonOneFactor

variable {n : ℕ} {U : Opens (ComplexModel n)}

private theorem backgroundExpansion_cons_decreasing (p : ℕ)
    (T : LocalProductCurrent n U (1+p)) (hT : IsPositive T) (hTc : IsClosedAny (1+p) T)
    (v : ℕ → Fin p → ComplexModel n → ℝ) (v₀ : Fin p → ComplexModel n → ℝ)
    (hv : ∀ j i, IsLocallyBoundedPshOn U (v j i))
    (hv₀ : ∀ i, IsLocallyBoundedPshOn U (v₀ i))
    (a : ℕ → ComplexModel n → ℝ) (a₀ : ComplexModel n → ℝ)
    (ha : ∀ j, IsLocallyBoundedPshOn U (a j)) (ha₀ : IsLocallyBoundedPshOn U a₀)
    (hanti_v : ∀ i z, z ∈ U → Antitone fun j => v j i z)
    (hlim_v : ∀ i z, z ∈ U → Tendsto (fun j => v j i z) atTop (𝓝 (v₀ i z)))
    (hanti_a : ∀ z, z ∈ U → Antitone fun j => a j z)
    (hlim_a : ∀ z, z ∈ U → Tendsto (fun j => a j z) atTop (𝓝 (a₀ z)))
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U) :
    WeakTendsto (fun j => backgroundExpansion (p+1) 0 (Fin.cons (a j) (v j)) hσ
      (castLPC (by omega : 1+p=0+(p+1)) T))
      (backgroundExpansion (p+1) 0 (Fin.cons a₀ v₀) hσ (castLPC (by omega) T)) := by
  apply backgroundExpansion_decreasing (p+1) 0 _ (isPositive_castLPC _ hT)
    (isClosedAny_castLPC _ hTc)
  · intro j i; exact Fin.cases (ha j) (hv j) i
  · intro i; exact Fin.cases ha₀ hv₀ i
  · intro i; exact Fin.cases hanti_a hanti_v i
  · intro i; exact Fin.cases hlim_a hlim_v i

/-- Actual decreasing smooth approximations identify the bounded original
transgression. This helper uses ordinary approximation data only. -/
theorem backgroundExpansion_transgression_of_approximation (p : ℕ)
    (T : LocalProductCurrent n U (1+p)) (hT : IsPositive T) (hTc : IsClosedAny (1+p) T)
    (v : ℕ → Fin p → ComplexModel n → ℝ) (v₀ : Fin p → ComplexModel n → ℝ)
    (hv₀ : ∀ i, IsLocallyBoundedPshOn U (v₀ i))
    (hv : ∀ i, IsDecreasingApproximation U (v₀ i) (fun j => v j i))
    (a b : ℕ → ComplexModel n → ℝ) (a₀ b₀ : ComplexModel n → ℝ)
    (ha₀ : IsLocallyBoundedPshOn U a₀) (hb₀ : IsLocallyBoundedPshOn U b₀)
    (ha : IsDecreasingApproximation U a₀ a) (hb : IsDecreasingApproximation U b₀ b)
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (hσS : ∀ z ∈ U, σ z ∈ formSpan n 1) :
    backgroundExpansion (p+1) 0 (Fin.cons b₀ v₀) hσ (castLPC (by omega) T) -
      backgroundExpansion (p+1) 0 (Fin.cons a₀ v₀) hσ (castLPC (by omega) T) =
      weightedDifference (backgroundResidual p T hT hTc v₀ hv₀ hσ) a₀ b₀ (fun _ => 1) := by
  have hvb : ∀ j i, IsLocallyBoundedPshOn U (v j i) := fun j i =>
    LocalBedfordTaylorDecreasing.isLocallyBoundedPshOn_of_isSmoothPshOn ((hv i).1 j)
  have hab : ∀ j, IsLocallyBoundedPshOn U (a j) := fun j =>
    LocalBedfordTaylorDecreasing.isLocallyBoundedPshOn_of_isSmoothPshOn (ha.1 j)
  have hbb : ∀ j, IsLocallyBoundedPshOn U (b j) := fun j =>
    LocalBedfordTaylorDecreasing.isLocallyBoundedPshOn_of_isSmoothPshOn (hb.1 j)
  have hvanti := fun i => (hv i).2.1
  have hvlim := fun i => (hv i).2.2
  have hla := backgroundExpansion_cons_decreasing p T hT hTc v v₀ hvb hv₀ a a₀ hab ha₀
    hvanti hvlim ha.2.1 ha.2.2 hσ
  have hlb := backgroundExpansion_cons_decreasing p T hT hTc v v₀ hvb hv₀ b b₀ hbb hb₀
    hvanti hvlim hb.2.1 hb.2.2 hσ
  have hr := weakTendsto_backgroundResidual_weightedDifference_one_of_antitone
    p T hT hTc v v₀ hvb hv₀ a b a₀ b₀ hab ha₀ hbb hb₀ hvanti hvlim
    ha.2.1 ha.2.2 hb.2.1 hb.2.2 hσ
  have heq (j : ℕ) := backgroundExpansion_transgression_smooth p T hT hTc (v j)
    (fun i => ((hv i).1 j).1) (fun i => ((hv i).1 j).2.1)
    (ha.1 j).1 (hb.1 j).1 (ha.1 j).2.1 (hb.1 j).2.1 hσ hσS
  ext γ φ
  have hl := (hlb γ φ).sub (hla γ φ)
  have he (j : ℕ) := congrArg (fun R : LocalProductCurrent n U 0 => R γ φ) (heq j)
  simp only [LinearMap.sub_apply, _root_.sub_apply] at he
  have hr' := (hr γ φ).congr' (Eventually.of_forall fun j => (he j).symm)
  exact tendsto_nhds_unique hl hr'

private theorem castLPC_restrict_transgression {V : Opens (ComplexModel n)}
    (hVU : V ≤ U) {r s : ℕ} (h : r=s) (T : LocalProductCurrent n U r) :
    restrict hVU (castLPC h T) = castLPC h (restrict hVU T) := by
  cases h
  rfl

/-- The genuine distinguished-factor identity on the original bounded PSH
class. Local smooth approximants, their simultaneous BT limits, and the
support-localization argument are all constructed from the original inputs. -/
theorem backgroundExpansion_transgression (p : ℕ)
    (T : LocalProductCurrent n U (1+p)) (hT : IsPositive T) (hTc : IsClosedAny (1+p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {a b : ComplexModel n → ℝ} (ha : IsLocallyBoundedPshOn U a)
    (hb : IsLocallyBoundedPshOn U b)
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (hσS : ∀ z ∈ U, σ z ∈ formSpan n 1) :
    backgroundExpansion (p+1) 0 (Fin.cons b v) hσ (castLPC (by omega) T) -
      backgroundExpansion (p+1) 0 (Fin.cons a v) hσ (castLPC (by omega) T) =
      weightedDifference (backgroundResidual p T hT hTc v hv hσ) a b (fun _ => 1) := by
  classical
  ext γ φ
  obtain ⟨W, hWo, hφW, hclWU, hWc⟩ :=
    exists_open_between_and_isCompact_closure φ.hasCompactSupport U.isOpen φ.tsupport_subset
  let V : Opens (ComplexModel n) := ⟨W,hWo⟩
  have hVU : V ≤ U := subset_closure.trans hclWU
  have hV : RelativelyCompactIn V U := ⟨hWc, hclWU⟩
  have hex (i : Fin p) := HolomorphicPullback.exists_decreasingMollifierApproximation (hv i) hV
  choose f hfs hfanti hflim using hex
  obtain ⟨fa, hfas, hfaanti, hfalim⟩ :=
    HolomorphicPullback.exists_decreasingMollifierApproximation ha hV
  obtain ⟨fb, hfbs, hfbanti, hfblim⟩ :=
    HolomorphicPullback.exists_decreasingMollifierApproximation hb hV
  have hsmall := backgroundExpansion_transgression_of_approximation p (restrict hVU T)
    (isPositive_restrict hT hVU) (isClosedAny_restrict hTc hVU)
    (fun j i => f i j) v (fun i => isLocallyBoundedPshOn_mono (hv i) hVU)
    (fun i => ⟨hfs i,hfanti i,hflim i⟩) fa fb a b
    (isLocallyBoundedPshOn_mono ha hVU) (isLocallyBoundedPshOn_mono hb hVU)
    ⟨hfas,hfaanti,hfalim⟩ ⟨hfbs,hfbanti,hfblim⟩ (hσ.mono hVU)
    (fun z hz => hσS z (hVU hz))
  let φV : 𝓓(V, ℝ) := ⟨φ,φ.contDiff,φ.hasCompactSupport,hφW⟩
  have hext : extTest hVU φV = φ := by ext z; rw [extTest_apply]; rfl
  have hcons (w : ComplexModel n → ℝ) (hw : IsLocallyBoundedPshOn U w) :
      ∀ i, IsLocallyBoundedPshOn U ((Fin.cons w v : Fin (p+1) → ComplexModel n → ℝ) i) :=
    fun i => Fin.cases hw hv i
  have hdeg : 1+p=0+(p+1) := by omega
  have hrestrict (w : ComplexModel n → ℝ) (hw : IsLocallyBoundedPshOn U w) :=
    backgroundExpansion_restrict hVU (p+1) 0 (castLPC hdeg T)
      (isPositive_castLPC hdeg hT) (isClosedAny_castLPC hdeg hTc)
      (Fin.cons w v) (hcons w hw) hσ
  have hra := hrestrict a ha
  have hrb := hrestrict b hb
  rw [castLPC_restrict_transgression] at hra hrb
  have hrd := backgroundResidual_weightedDifference_one_restrict hVU p T hT hTc v hv ha hb hσ
  have he := congrArg (fun R : LocalProductCurrent n V 0 => R γ φV) hsmall
  simp only [LinearMap.sub_apply, _root_.sub_apply] at he
  rw [← hra, ← hrb, ← hrd] at he
  simpa only [LinearMap.sub_apply, _root_.sub_apply,
    LocalBedfordTaylorLocality.restrict_apply, hext] using he

end SGPT.PSH.HermitianProducts
