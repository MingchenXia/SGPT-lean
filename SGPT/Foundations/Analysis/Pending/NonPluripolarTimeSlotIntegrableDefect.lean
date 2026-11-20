import SGPT.Foundations.Analysis.Pending.NonPluripolarTimeSlotPositiveBalance
import SGPT.Foundations.Analysis.Pending.PositiveMeasureDensityBalance
import SGPT.Foundations.Analysis.Pending.NonPluripolarSignedFibreSlicing

set_option autoImplicit false

/-! # Actual signed canonical NP time-slot defect and internally produced weighted fibre integrability -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.NonPluripolarTimeSlotIntegrableDefect

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere FirstPass.MixedNonPluripolar
  BedfordTaylor BedfordTaylorTimeSlot BedfordTaylorFibreSlicing MixedDensityRankOneSlot
  MixedMongeAmpere MixedNonPluripolar NonPluripolarTimeSlotTruncationBalance
  NonPluripolarTimeSlotPositiveBalance PositiveMeasureDensityBalance
  NonPluripolarFibreSlicing NonPluripolarSignedFibreSlicing

noncomputable section

variable {n : ℕ} {Ω Q : Opens (ComplexModel (n + 1))}
  {u : Fin (n + 1) → ComplexModel (n + 1) → EReal}

/-- The actual canonical NP positive time-slot balance internally produces both sign-region density dominations. -/
theorem withDensity_timeLaplacian_le_regularizer_npMeasures
    (hQ : RelativelyCompactIn Q Ω) (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (hlast : u (Fin.last n) = fun q => (lastNormSq n q : EReal))
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {p : ComplexModel (n + 1) → ℝ} (hp : IsSmoothPsdOn Ω p)
    (hψp : IsSmoothPsdOn Ω fun q => timeLift n ψ q + p q) :
    ((mixedTruncationLimitMeasure Ω u hu).restrict Q).withDensity
      (fun q => ENNReal.ofReal (timeLaplacian ψ (q (Fin.last n)))) ≤
      (mixedTruncationLimitMeasure Ω (Function.update u (Fin.last n) fun q => ((timeLift n ψ q + p q : ℝ) : EReal))
        (plurisubharmonicOn_update_last hu hψp)).restrict Q ∧
    ((mixedTruncationLimitMeasure Ω u hu).restrict Q).withDensity
      (fun q => ENNReal.ofReal (-timeLaplacian ψ (q (Fin.last n)))) ≤
      (mixedTruncationLimitMeasure Ω (Function.update u (Fin.last n) fun q => (p q : EReal))
        (plurisubharmonicOn_update_last hu hp)).restrict Q :=
  withDensity_ofReal_le_of_add_balance
    ((continuous_timeLaplacian hψ).comp (lastCoordinate n).continuous).measurable
    (mixedTruncationLimitMeasure_timeLift_positive_balance_of_last hQ hu hlast hψ hp hψp)

/-- Natural integrability against the two actual canonical regularizer NP measures produces the signed time-Laplacian integrability and the actual time-slot defect. -/
theorem integrable_mul_timeLaplacian_and_integral_timeLift_sub
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (hlast : u (Fin.last n) = fun q => (lastNormSq n q : EReal))
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {p : ComplexModel (n + 1) → ℝ} (hp : IsSmoothPsdOn Ω p)
    (hψp : IsSmoothPsdOn Ω fun q => timeLift n ψ q + p q)
    {χ G : ComplexModel (n + 1) → ℝ}
    (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (ha : Integrable (fun q => χ q * G q)
      (mixedTruncationLimitMeasure Ω (Function.update u (Fin.last n) fun q => ((timeLift n ψ q + p q : ℝ) : EReal))
        (plurisubharmonicOn_update_last hu hψp)))
    (hb : Integrable (fun q => χ q * G q)
      (mixedTruncationLimitMeasure Ω (Function.update u (Fin.last n) fun q => (p q : EReal))
        (plurisubharmonicOn_update_last hu hp))) :
    Integrable (fun q => (χ q * G q) * timeLaplacian ψ (q (Fin.last n)))
      (mixedTruncationLimitMeasure Ω u hu) ∧
    (∫ q, χ q * G q ∂mixedTruncationLimitMeasure Ω
      (Function.update u (Fin.last n) fun q => ((timeLift n ψ q + p q : ℝ) : EReal))
      (plurisubharmonicOn_update_last hu hψp)) -
    (∫ q, χ q * G q ∂mixedTruncationLimitMeasure Ω
      (Function.update u (Fin.last n) fun q => (p q : EReal))
      (plurisubharmonicOn_update_last hu hp)) =
    ∫ q, (χ q * G q) * timeLaplacian ψ (q (Fin.last n)) ∂mixedTruncationLimitMeasure Ω u hu := by
  obtain ⟨V, hVo, hχV, hVΩ, hVc⟩ :=
    exists_open_between_and_isCompact_closure hχc Ω.isOpen hχΩ
  let Q' : Opens (ComplexModel (n + 1)) := ⟨V, hVo⟩
  have hQ' : RelativelyCompactIn Q' Ω := ⟨hVc, hVΩ⟩
  have hc : Continuous (fun q : ComplexModel (n + 1) => timeLaplacian ψ (q (Fin.last n))) :=
    (continuous_timeLaplacian hψ).comp (lastCoordinate n).continuous
  have hbalance := mixedTruncationLimitMeasure_timeLift_positive_balance_of_last hQ' hu hlast hψ hp hψp
  have hdef := integrable_mul_and_integral_sub_of_density_balance hc.measurable hbalance
    ha.restrict hb.restrict
  have hzeroH (q : ComplexModel (n + 1)) (hq : q ∉ (Q' : Set (ComplexModel (n + 1)))) : χ q * G q = 0 := by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hq (hχV h)), zero_mul]
  have hzeroHC (q : ComplexModel (n + 1)) (hq : q ∉ (Q' : Set (ComplexModel (n + 1)))) :
      (χ q * G q) * timeLaplacian ψ (q (Fin.last n)) = 0 := by rw [hzeroH q hq, zero_mul]
  have hi : Integrable (fun q => (χ q * G q) * timeLaplacian ψ (q (Fin.last n)))
      (mixedTruncationLimitMeasure Ω u hu) :=
    (show IntegrableOn (fun q => (χ q * G q) * timeLaplacian ψ (q (Fin.last n)))
      Q' (mixedTruncationLimitMeasure Ω u hu) from hdef.1).integrable_of_forall_notMem_eq_zero hzeroHC
  have hremoveH (μ : Measure (ComplexModel (n + 1))) :
      (∫ q, χ q * G q ∂μ.restrict Q') = ∫ q, χ q * G q ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hzeroH
  have hremoveHC (μ : Measure (ComplexModel (n + 1))) :
      (∫ q, (χ q * G q) * timeLaplacian ψ (q (Fin.last n)) ∂μ.restrict Q') =
        ∫ q, (χ q * G q) * timeLaplacian ψ (q (Fin.last n)) ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hzeroHC
  exact ⟨hi, by simpa only [hremoveH, hremoveHC] using hdef.2⟩

/-- The actual signed canonical NP defect produces exactly the weighted integrability needed by the genuine signed fibre theorem, including its 1/π normalization. -/
theorem integral_timeLift_sub_eq_weighted_fibre
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (hlast : u (Fin.last n) = fun q => (lastNormSq n q : EReal))
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {p : ComplexModel (n + 1) → ℝ} (hp : IsSmoothPsdOn Ω p)
    (hψp : IsSmoothPsdOn Ω fun q => timeLift n ψ q + p q)
    {χ G : ComplexModel (n + 1) → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : ∀ q, 0 ≤ χ q) (hG : Measurable G)
    (ha : Integrable (fun q => χ q * G q)
      (mixedTruncationLimitMeasure Ω (Function.update u (Fin.last n) fun q => ((timeLift n ψ q + p q : ℝ) : EReal))
        (plurisubharmonicOn_update_last hu hψp)))
    (hb : Integrable (fun q => χ q * G q)
      (mixedTruncationLimitMeasure Ω (Function.update u (Fin.last n) fun q => (p q : EReal))
        (plurisubharmonicOn_update_last hu hp))) :
    (∀ᵐ τ : ℂ, Integrable
      (fun y => (χ (fibreMap n τ y) * G (fibreMap n τ y)) *
        timeLaplacian ψ ((fibreMap n τ y) (Fin.last n)))
      (mixedTruncationLimitMeasure (fibreOpens Ω τ) (fibrePotentials u τ)
        (plurisubharmonicOn_fibrePotentials hu τ))) ∧
    Integrable (fun τ : ℂ => ∫ y,
      (χ (fibreMap n τ y) * G (fibreMap n τ y)) * timeLaplacian ψ ((fibreMap n τ y) (Fin.last n))
      ∂mixedTruncationLimitMeasure (fibreOpens Ω τ) (fibrePotentials u τ)
        (plurisubharmonicOn_fibrePotentials hu τ)) ∧
    (∫ q, χ q * G q ∂mixedTruncationLimitMeasure Ω
      (Function.update u (Fin.last n) fun q => ((timeLift n ψ q + p q : ℝ) : EReal))
      (plurisubharmonicOn_update_last hu hψp)) -
    (∫ q, χ q * G q ∂mixedTruncationLimitMeasure Ω
      (Function.update u (Fin.last n) fun q => (p q : EReal))
      (plurisubharmonicOn_update_last hu hp)) =
    (∫ τ : ℂ, ∫ y,
      (χ (fibreMap n τ y) * G (fibreMap n τ y)) * timeLaplacian ψ ((fibreMap n τ y) (Fin.last n))
      ∂mixedTruncationLimitMeasure (fibreOpens Ω τ) (fibrePotentials u τ)
        (plurisubharmonicOn_fibrePotentials hu τ)) / Real.pi := by
  have hdef := integrable_mul_timeLaplacian_and_integral_timeLift_sub hu hlast hψ hp hψp hχc hχΩ ha hb
  have hc : Continuous (fun q : ComplexModel (n + 1) => timeLaplacian ψ (q (Fin.last n))) :=
    (continuous_timeLaplacian hψ).comp (lastCoordinate n).continuous
  have hGc : Measurable (fun q => G q * timeLaplacian ψ (q (Fin.last n))) := hG.mul hc.measurable
  have hslice := integral_mul_npLimit_eq_fibre hu hlast hχ hχc hχΩ hχ0 hGc
    (by simpa only [mul_assoc] using hdef.1)
  refine ⟨?_, ?_, hdef.2.trans ?_⟩
  · simpa only [mul_assoc] using hslice.1
  · simpa only [mul_assoc] using hslice.2.1
  · simpa only [mul_assoc] using hslice.2.2

/-- The genuine time coordinate of the fibre inclusion exposes Δψ/4 outside the actual fibre integral; no division by the possibly zero coefficient or unweighted baseline integrability is used. -/
theorem integral_timeLift_sub_eq_timeLaplacian_fibre
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (hlast : u (Fin.last n) = fun q => (lastNormSq n q : EReal))
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {p : ComplexModel (n + 1) → ℝ} (hp : IsSmoothPsdOn Ω p)
    (hψp : IsSmoothPsdOn Ω fun q => timeLift n ψ q + p q)
    {χ G : ComplexModel (n + 1) → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : ∀ q, 0 ≤ χ q) (hG : Measurable G)
    (ha : Integrable (fun q => χ q * G q)
      (mixedTruncationLimitMeasure Ω (Function.update u (Fin.last n) fun q => ((timeLift n ψ q + p q : ℝ) : EReal))
        (plurisubharmonicOn_update_last hu hψp)))
    (hb : Integrable (fun q => χ q * G q)
      (mixedTruncationLimitMeasure Ω (Function.update u (Fin.last n) fun q => (p q : EReal))
        (plurisubharmonicOn_update_last hu hp))) :
    Integrable (fun τ : ℂ => timeLaplacian ψ τ * ∫ y, χ (fibreMap n τ y) * G (fibreMap n τ y)
      ∂mixedTruncationLimitMeasure (fibreOpens Ω τ) (fibrePotentials u τ)
        (plurisubharmonicOn_fibrePotentials hu τ)) ∧
    (∫ q, χ q * G q ∂mixedTruncationLimitMeasure Ω
      (Function.update u (Fin.last n) fun q => ((timeLift n ψ q + p q : ℝ) : EReal))
      (plurisubharmonicOn_update_last hu hψp)) -
    (∫ q, χ q * G q ∂mixedTruncationLimitMeasure Ω
      (Function.update u (Fin.last n) fun q => (p q : EReal))
      (plurisubharmonicOn_update_last hu hp)) =
    (∫ τ : ℂ, timeLaplacian ψ τ * ∫ y, χ (fibreMap n τ y) * G (fibreMap n τ y)
      ∂mixedTruncationLimitMeasure (fibreOpens Ω τ) (fibrePotentials u τ)
        (plurisubharmonicOn_fibrePotentials hu τ)) / Real.pi := by
  have hs := integral_timeLift_sub_eq_weighted_fibre hu hlast hψ hp hψp hχ hχc hχΩ hχ0 hG ha hb
  have hcoord (τ : ℂ) (y : ComplexModel n) : (fibreMap n τ y) (Fin.last n) = τ :=
    stripModelEquiv_symm_apply_last y τ
  have houter : (fun τ : ℂ => ∫ y,
      (χ (fibreMap n τ y) * G (fibreMap n τ y)) * timeLaplacian ψ ((fibreMap n τ y) (Fin.last n))
      ∂mixedTruncationLimitMeasure (fibreOpens Ω τ) (fibrePotentials u τ)
        (plurisubharmonicOn_fibrePotentials hu τ)) =
    (fun τ : ℂ => timeLaplacian ψ τ * ∫ y, χ (fibreMap n τ y) * G (fibreMap n τ y)
      ∂mixedTruncationLimitMeasure (fibreOpens Ω τ) (fibrePotentials u τ)
        (plurisubharmonicOn_fibrePotentials hu τ)) := by
    funext τ
    simp_rw [hcoord]
    rw [integral_mul_const]
    exact mul_comm _ _
  exact ⟨houter ▸ hs.2.1, by simpa only [houter] using hs.2.2⟩

end

end SGPT.Foundations.Analysis.Pending.NonPluripolarTimeSlotIntegrableDefect
