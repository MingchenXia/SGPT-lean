import SGPT.PSH.HermitianProductsRadialApproximation
import SGPT.PSH.HermitianProductsSmoothExpansion
import SGPT.PSH.HermitianProductsLocality
import SGPT.Foundations.Analysis.Pending.LocalPositiveCurrentGluing

/-!
# Positivity of the actual nonclosed-background expansion

The same radial kernels regularize the corrected PSH factors and the
original positive one-one currents. For each fixed positive Euclidean error,
the smooth products are eventually positive. Decreasing Bedford--Taylor
continuity and then the zero-error limit prove positivity of the literal
finite expansion.
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
  LocalBedfordTaylorLocality LocalBedfordTaylorCalculus LocalBedfordTaylorDecreasing
  LocalBedfordTaylorCollar
open scoped Topology Distributions ContDiff

variable {n : ℕ} {U V : Opens (ComplexModel n)}

/-- Eventual positivity suffices for the actual weak-current limit. -/
theorem isPositive_of_eventually_weakTendsto {r : ℕ}
    {T : ℕ → LocalProductCurrent n U r} {T₀ : LocalProductCurrent n U r}
    (hpos : ∀ᶠ j in atTop, IsPositive (T j)) (hlim : WeakTendsto T T₀) :
    IsPositive T₀ := by
  intro ι _ γ φ hγ
  apply ge_of_tendsto (tendsto_finsetSum _ fun i _ => hlim (γ i) (φ i))
  exact hpos.mono fun j hj => hj ι γ φ hγ

/-- On a buffered domain, positivity follows from the actual positive
one-one factors and their shared radial convolution systems. -/
theorem isPositive_backgroundExpansion_of_radialSystems
    {m : ℕ} {U V : Opens (ComplexModel (m + 1))} (hVU : V ≤ U)
    (p r : ℕ) (T : LocalProductCurrent (m + 1) V (r + p))
    (hT : IsPositive T) (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel (m + 1) → ℝ)
    (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hσ11 : ∀ z ∈ U, IsOneOne (σ z))
    (hfactor : ∀ i, IsPositive
      (ddcMul (oneCurrent U) (v i) + wedgeForm rfl (oneCurrent U) hσ))
    {R : ℝ} {K : Set (ComplexModel (m + 1))}
    (S : (i : Fin p) → RadialConvolutionSystem V K (v i) R)
    (hR : 0 < R) (hK : IsCompact K) (hKU : K ⊆ U)
    (hVK : (V : Set (ComplexModel (m + 1))) ⊆ K) :
    IsPositive (backgroundExpansion p r v (hσ.mono hVU) T) := by
  classical
  let f : ℕ → Fin p → ComplexModel (m + 1) → ℝ :=
    fun j i => translationPairing volume (K.indicator (v i)) ((S i).kernel j)
  have hf (i : Fin p) : IsDecreasingApproximation V (v i) (fun j => f j i) :=
    radialSystem_isDecreasingApproximation (hv i) hVU (S i) hK hKU
  apply isPositive_backgroundExpansion_of_positive_errors p r v T
    (hσ.mono hVU) (contDiffOn_const (c := kahlerForm (m + 1)))
  intro ε hε
  have hevent : ∀ᶠ j in atTop, ∀ i z, z ∈ V → IsSemipositiveOneOne
      (smoothDDC (f j i) z + σ z + ε • kahlerForm (m + 1)) := by
    apply Filter.eventually_all.mpr
    intro i
    obtain ⟨N, hN⟩ := radial_correctedForm_eventually_semipositive
      (hv i) hσ hσ11 (hfactor i) (S i) hR hK hKU hVK ε hε
    exact Filter.eventually_atTop.mpr ⟨N, hN⟩
  apply isPositive_of_eventually_weakTendsto (T := fun j => backgroundExpansion p r (f j)
    ((hσ.mono hVU).add ((contDiffOn_const (c := kahlerForm (m + 1))).const_smul ε)) T)
  · apply hevent.mono
    intro j hj
    rw [backgroundExpansion_smooth p r (f j) (fun i => ((hf i).1 j).1)
      (fun i => ((hf i).1 j).2.1)]
    · exact isPositive_wedgeForm_smooth_product rfl hT _
        (fun i => (contDiffOn_ddcForm ((hf i).1 j).1).add
          ((hσ.mono hVU).add (contDiffOn_const.const_smul ε))) (fun i z hz => by
            simpa only [ddcForm, add_assoc] using hj i z hz)
    · intro z hz
      exact oneOne_mem_formSpan (isOneOne_add (hσ11 z (hVU hz))
        (isOneOne_smul ε isSemipositiveOneOne_kahlerForm.1))
    · exact hT
    · exact hTc
  · exact backgroundExpansion_decreasing p r T hT hTc f v
      (fun j i => isLocallyBoundedPshOn_of_isSmoothPshOn ((hf i).1 j))
      (fun i => isLocallyBoundedPshOn_mono (hv i) hVU)
      (fun i z hz => (hf i).2.1 z hz) (fun i z hz => (hf i).2.2 z hz) _

/-- The finite background expansion of actual bounded positive Hermitian
factors is a positive current. The smooth residual need not be closed. -/
theorem isPositive_backgroundExpansion
    {m : ℕ} {U : Opens (ComplexModel (m + 1))}
    (p r : ℕ) (T : LocalProductCurrent (m + 1) U (r + p))
    (hT : IsPositive T) (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel (m + 1) → ℝ)
    (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hσ11 : ∀ z ∈ U, IsOneOne (σ z))
    (hfactor : ∀ i, IsPositive
      (ddcMul (oneCurrent U) (v i) + wedgeForm rfl (oneCurrent U) hσ)) :
    IsPositive (backgroundExpansion p r v hσ T) := by
  apply LocalPositiveCurrentGluing.isPositive_of_local_restrict
  intro x hx
  obtain ⟨a, ha, hball⟩ := Metric.isOpen_iff.mp U.isOpen x hx
  let A : Opens (ComplexModel (m + 1)) := ⟨ball x (a / 2), isOpen_ball⟩
  have hAU : RelativelyCompactIn A U := relativelyCompactIn_half_ball ha hball
  obtain ⟨R, hR, V, K, hAV, hVU, hK, hKU, hVK, S, _⟩ :=
    exists_common_radial_systems hAU v hv
  refine ⟨V, hVU, hAV (mem_ball_self (half_pos ha)), ?_⟩
  rw [backgroundExpansion_restrict hVU p r T hT hTc v hv hσ]
  exact isPositive_backgroundExpansion_of_radialSystems hVU p r (restrict hVU T)
    (isPositive_restrict hT hVU) (isClosedAny_restrict hTc hVU)
    v hv hσ hσ11 hfactor S hR hK hKU hVK

end SGPT.PSH.HermitianProducts
