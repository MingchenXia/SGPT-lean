import SGPT.PSH.HermitianProductsTransgression
import SGPT.PSH.HermitianProductsDistinguishedSlot

/-!
# Actual decreasing limits of distinguished-factor transgression

The unit Borel multiplier is removed on each actual positive Hessian
current. The distinguished slot and every selected ordinary slot then
converge together by the genuine Bedford--Taylor theorem. Fixed smooth
residual powers preserve weak convergence, and the finite differences sum.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianProducts

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorForms LocalBedfordTaylorSmooth
  LocalBedfordTaylorCollar LocalBedfordTaylorContinuity LocalBedfordTaylorLocality
  LocalBedfordTaylorSmoothProductDensity
  ConstantFormProducts TopDegreeDensity
open HermitianComparisonOneFactor

variable {n : ℕ} {U : Opens (ComplexModel n)}

private theorem castLPC_trans {a b c : ℕ} (hab : a = b) (hbc : b = c)
    (T : LocalProductCurrent n U a) :
    castLPC hbc (castLPC hab T) = castLPC (hab.trans hbc) T := by
  cases hab
  cases hbc
  rfl

private theorem btProduct_castLPC {q r s : ℕ} (hrs : r = s)
    (v : Fin q → ComplexModel n → ℝ) (T : LocalProductCurrent n U (r + q)) :
    castLPC hrs (btProduct q r v T) =
      btProduct q s v (castLPC (congrArg (fun k => k + q) hrs) T) := by
  cases hrs
  rfl

/-- The actual selected current in the residual presentation has the
standard outer-Hessian degree, with every cast explicitly transported. -/
theorem backgroundResidual_current_eq_btProduct (p : ℕ)
    (T : LocalProductCurrent n U (1 + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (1 + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (s : Finset (Fin p)) :
    (backgroundResidual p T hT hTc v hv hσ s).current =
      btProduct s.card (p - s.card + 1) (fun i => v (s.orderEmbOfFin rfl i))
        (castLPC (by
          have hs : s.card ≤ p := by simpa using Finset.card_le_univ s
          omega : 1 + p = p - s.card + 1 + s.card) T) := by
  classical
  have hs : s.card ≤ p := by simpa using Finset.card_le_univ s
  change castLPC (by omega : 1 + (p - s.card) = p - s.card + 1)
      (btProduct s.card (1 + (p - s.card)) (fun i => v (s.orderEmbOfFin rfl i))
        (castLPC (by omega : 1 + p = 1 + (p - s.card) + s.card) T)) = _
  rw [btProduct_castLPC, castLPC_trans]

/-- Actual simultaneous decreasing limits of the distinguished potential
and all selected ordinary slots give the unit-weight residual limit. -/
theorem backgroundResidual_weightedDdc_one_decreasing (p : ℕ)
    (T : LocalProductCurrent n U (1 + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (1 + p) T)
    (v : ℕ → Fin p → ComplexModel n → ℝ) (v₀ : Fin p → ComplexModel n → ℝ)
    (hv : ∀ j i, IsLocallyBoundedPshOn U (v j i))
    (hv₀ : ∀ i, IsLocallyBoundedPshOn U (v₀ i))
    (u : ℕ → ComplexModel n → ℝ) (u₀ : ComplexModel n → ℝ)
    (hu : ∀ j, IsLocallyBoundedPshOn U (u j)) (hu₀ : IsLocallyBoundedPshOn U u₀)
    (hanti_v : ∀ i z, z ∈ U → Antitone (fun j => v j i z))
    (hlim_v : ∀ i z, z ∈ U → Tendsto (fun j => v j i z) atTop (𝓝 (v₀ i z)))
    (hanti_u : ∀ z, z ∈ U → Antitone (fun j => u j z))
    (hlim_u : ∀ z, z ∈ U → Tendsto (fun j => u j z) atTop (𝓝 (u₀ z)))
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (s : Finset (Fin p)) :
    WeakTendsto (fun j => weightedDdcResidual
      (backgroundResidual p T hT hTc (v j) (hv j) hσ s).current
      (backgroundResidual p T hT hTc (v j) (hv j) hσ s).smooth
      (u j) (u j) (u j) (fun _ => 1))
      (weightedDdcResidual (backgroundResidual p T hT hTc v₀ hv₀ hσ s).current
        (backgroundResidual p T hT hTc v₀ hv₀ hσ s).smooth u₀ u₀ u₀ (fun _ => 1)) := by
  classical
  have hs : s.card ≤ p := by simpa using Finset.card_le_univ s
  let d := p - s.card
  have hdegree : 1 + p = d + 1 + s.card := by dsimp [d]; omega
  let T' := castLPC hdegree T
  let w : ℕ → Fin s.card → ComplexModel n → ℝ :=
    fun j i => v j (s.orderEmbOfFin rfl i)
  let w₀ : Fin s.card → ComplexModel n → ℝ := fun i => v₀ (s.orderEmbOfFin rfl i)
  have hconv := weakTendsto_ddcMul_btProduct_of_antitone s.card d T'
    (isPositive_castLPC hdegree hT) (isClosedAny_castLPC hdegree hTc) w w₀ u u₀
    (fun j i => hv j _) (fun i => hv₀ _) hu hu₀
    (fun i z hz => hanti_v _ z hz) (fun i z hz => hlim_v _ z hz) hanti_u hlim_u
  let hα := contDiffOn_wedgeProd d (fun _ => σ) (fun _ => hσ)
  have he (j : ℕ) : weightedDdcResidual
      (backgroundResidual p T hT hTc (v j) (hv j) hσ s).current
      (backgroundResidual p T hT hTc (v j) (hv j) hσ s).smooth
      (u j) (u j) (u j) (fun _ => 1) =
      wedgeForm (Nat.zero_add d) (ddcMul (btProduct s.card (d + 1) (w j) T') (u j)) hα := by
    unfold weightedDdcResidual
    rw [mulBorel_indicator_one (isPositive_ddcMul
      (backgroundResidual p T hT hTc (v j) (hv j) hσ s).positive
      (backgroundResidual p T hT hTc (v j) (hv j) hσ s).closed (hu j)).1,
      backgroundResidual_current_eq_btProduct]
    rfl
  have he₀ : weightedDdcResidual (backgroundResidual p T hT hTc v₀ hv₀ hσ s).current
      (backgroundResidual p T hT hTc v₀ hv₀ hσ s).smooth u₀ u₀ u₀ (fun _ => 1) =
      wedgeForm (Nat.zero_add d) (ddcMul (btProduct s.card (d + 1) w₀ T') u₀) hα := by
    unfold weightedDdcResidual
    rw [mulBorel_indicator_one (isPositive_ddcMul
      (backgroundResidual p T hT hTc v₀ hv₀ hσ s).positive
      (backgroundResidual p T hT hTc v₀ hv₀ hσ s).closed hu₀).1,
      backgroundResidual_current_eq_btProduct]
    rfl
  intro γ φ
  simpa only [he, he₀] using weakTendsto_wedgeForm (Nat.zero_add d) hconv hα γ φ

/-- The actual complete finite transgression presentation converges when
both distinguished potentials and every remaining slot decrease together.
This is the direct bounded-current limit of the smooth insertion identity. -/
theorem weakTendsto_backgroundResidual_weightedDifference_one_of_antitone (p : ℕ)
    (T : LocalProductCurrent n U (1 + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (1 + p) T)
    (v : ℕ → Fin p → ComplexModel n → ℝ) (v₀ : Fin p → ComplexModel n → ℝ)
    (hv : ∀ j i, IsLocallyBoundedPshOn U (v j i))
    (hv₀ : ∀ i, IsLocallyBoundedPshOn U (v₀ i))
    (a b : ℕ → ComplexModel n → ℝ) (a₀ b₀ : ComplexModel n → ℝ)
    (ha : ∀ j, IsLocallyBoundedPshOn U (a j)) (ha₀ : IsLocallyBoundedPshOn U a₀)
    (hb : ∀ j, IsLocallyBoundedPshOn U (b j)) (hb₀ : IsLocallyBoundedPshOn U b₀)
    (hanti_v : ∀ i z, z ∈ U → Antitone (fun j => v j i z))
    (hlim_v : ∀ i z, z ∈ U → Tendsto (fun j => v j i z) atTop (𝓝 (v₀ i z)))
    (hanti_a : ∀ z, z ∈ U → Antitone (fun j => a j z))
    (hlim_a : ∀ z, z ∈ U → Tendsto (fun j => a j z) atTop (𝓝 (a₀ z)))
    (hanti_b : ∀ z, z ∈ U → Antitone (fun j => b j z))
    (hlim_b : ∀ z, z ∈ U → Tendsto (fun j => b j z) atTop (𝓝 (b₀ z)))
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U) :
    WeakTendsto (fun j => weightedDifference
      (backgroundResidual p T hT hTc (v j) (hv j) hσ) (a j) (b j) (fun _ => 1))
      (weightedDifference (backgroundResidual p T hT hTc v₀ hv₀ hσ) a₀ b₀ (fun _ => 1)) := by
  classical
  intro γ φ
  simp only [weightedDifference, LinearMap.sum_apply, _root_.sum_apply,
    LinearMap.sub_apply, _root_.sub_apply]
  apply tendsto_finsetSum
  intro s _
  exact (backgroundResidual_weightedDdc_one_decreasing p T hT hTc v v₀ hv hv₀ b b₀ hb hb₀
    hanti_v hlim_v hanti_b hlim_b hσ s γ φ).sub
      (backgroundResidual_weightedDdc_one_decreasing p T hT hTc v v₀ hv hv₀ a a₀ ha ha₀
        hanti_v hlim_v hanti_a hlim_a hσ s γ φ)

private theorem castLPC_restrict_current {V : Opens (ComplexModel n)} (hVU : V ≤ U)
    {a b : ℕ} (hab : a = b) (T : LocalProductCurrent n U a) :
    restrict hVU (castLPC hab T) = castLPC hab (restrict hVU T) := by
  cases hab
  rfl

/-- The actual selected positive current in each residual term commutes
with restriction of its original base and all original PSH factors. -/
theorem backgroundResidual_current_restrict {V : Opens (ComplexModel n)} (hVU : V ≤ U)
    (p : ℕ) (T : LocalProductCurrent n U (1 + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (1 + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (s : Finset (Fin p)) :
    restrict hVU (backgroundResidual p T hT hTc v hv hσ s).current =
      (backgroundResidual p (restrict hVU T) (isPositive_restrict hT hVU)
        (isClosedAny_restrict hTc hVU) v
        (fun i => isLocallyBoundedPshOn_mono (hv i) hVU) (hσ.mono hVU) s).current := by
  classical
  have hs : s.card ≤ p := by simpa using Finset.card_le_univ s
  rw [backgroundResidual_current_eq_btProduct, backgroundResidual_current_eq_btProduct]
  change restrict hVU
      (btProduct s.card (p - s.card + 1) (fun i => v (s.orderEmbOfFin rfl i))
        (castLPC (by omega : 1 + p = p - s.card + 1 + s.card) T)) =
    btProduct s.card (p - s.card + 1) (fun i => v (s.orderEmbOfFin rfl i))
      (castLPC (by omega : 1 + p = p - s.card + 1 + s.card) (restrict hVU T))
  rw [← btProduct_restrict hVU s.card (p - s.card + 1)
    (fun i => v (s.orderEmbOfFin rfl i))
    (castLPC (by omega : 1 + p = p - s.card + 1 + s.card) T)
    (isPositive_castLPC _ hT) (isClosedAny_castLPC _ hTc) (fun i => hv _),
    castLPC_restrict_current]

/-- Removing the true unit multiplier exposes ordinary Hessian and smooth
wedge restriction, with no new regularization data. -/
theorem weightedDdcResidual_one_restrict {V : Opens (ComplexModel n)} (hVU : V ≤ U)
    {k : ℕ} (R : LocalProductCurrent n U (k + 1)) (hR : IsPositive R)
    (hRc : IsClosedCurrent R) {α : ComplexModel n → RealForm n (2 * k)}
    (hα : ContDiffOn ℝ ∞ α U) (u a b : ComplexModel n → ℝ)
    (hu : IsLocallyBoundedPshOn U u) :
    restrict hVU (weightedDdcResidual R hα u a b (fun _ => 1)) =
      weightedDdcResidual (restrict hVU R) (hα.mono hVU) u a b (fun _ => 1) := by
  simp only [weightedDdcResidual]
  rw [mulBorel_indicator_one (isPositive_ddcMul hR hRc hu).1,
    mulBorel_indicator_one (isPositive_ddcMul (isPositive_restrict hR hVU)
      (isClosedCurrent_restrict hRc hVU) (isLocallyBoundedPshOn_mono hu hVU)).1,
    wedgeForm_restrict, ddcMul_restrict hR hVU hu]

private theorem restrict_sum_current {V : Opens (ComplexModel n)} (hVU : V ≤ U)
    {r : ℕ} {ι : Type*} [Fintype ι] (T : ι → LocalProductCurrent n U r) :
    restrict hVU (∑ i, T i) = ∑ i, restrict hVU (T i) := by
  ext γ φ
  simp only [LocalBedfordTaylorLocality.restrict_apply, LinearMap.sum_apply, _root_.sum_apply]

private theorem restrict_sub_current {V : Opens (ComplexModel n)} (hVU : V ≤ U)
    {r : ℕ} (S T : LocalProductCurrent n U r) :
    restrict hVU (S - T) = restrict hVU S - restrict hVU T := rfl

/-- The literal unweighted distinguished-factor transgression commutes
with arbitrary open restriction, for the original bounded PSH factors. -/
theorem backgroundResidual_weightedDifference_one_restrict
    {V : Opens (ComplexModel n)} (hVU : V ≤ U)
    (p : ℕ) (T : LocalProductCurrent n U (1 + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (1 + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {a b : ComplexModel n → ℝ}
    (ha : IsLocallyBoundedPshOn U a) (hb : IsLocallyBoundedPshOn U b)
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U) :
    restrict hVU (weightedDifference (backgroundResidual p T hT hTc v hv hσ) a b (fun _ => 1)) =
      weightedDifference (backgroundResidual p (restrict hVU T) (isPositive_restrict hT hVU)
        (isClosedAny_restrict hTc hVU) v (fun i => isLocallyBoundedPshOn_mono (hv i) hVU)
        (hσ.mono hVU)) a b (fun _ => 1) := by
  classical
  rw [weightedDifference, weightedDifference, restrict_sum_current]
  apply Finset.sum_congr rfl
  intro s _
  rw [restrict_sub_current,
    weightedDdcResidual_one_restrict hVU _
      (backgroundResidual p T hT hTc v hv hσ s).positive
      (backgroundResidual p T hT hTc v hv hσ s).closed _ b a b hb,
    weightedDdcResidual_one_restrict hVU _
      (backgroundResidual p T hT hTc v hv hσ s).positive
      (backgroundResidual p T hT hTc v hv hσ s).closed _ a a b ha,
    backgroundResidual_current_restrict]
  rfl

end SGPT.PSH.HermitianProducts
