import SGPT.Foundations.Analysis.Pending.NonPluripolarTimeSlotTruncationBalance
import SGPT.Foundations.Analysis.Pending.IncreasingMeasureIntegrals

set_option autoImplicit false

/-! # Actual positive time-slot balance at genuine canonical NP limits -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.NonPluripolarTimeSlotPositiveBalance

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere FirstPass.MixedNonPluripolar
  FirstPass.IncreasingMeasures BedfordTaylor BedfordTaylorTimeSlot BedfordTaylorFibreSlicing
  MixedDensityRankOneSlot MixedMongeAmpere MixedNonPluripolar IncreasingMeasureIntegrals
  NonPluripolarTimeSlotTruncationBalance

noncomputable section

private theorem increasingLimit_restrict_apply_shifted
    {X : Type*} [MeasurableSpace X] (μ : ℕ → Measure X) (hμ : Monotone μ)
    (r : ℕ) {Q E : Set X} (hQ : MeasurableSet Q) (hE : MeasurableSet E) :
    (increasingLimit μ hμ).restrict Q E = ⨆ k, (μ (k + r)).restrict Q E := by
  have hshift : Monotone (fun k => μ (k + r)) := fun _ _ hkl => hμ (Nat.add_le_add_right hkl r)
  rw [Measure.restrict_apply hE]
  calc
    increasingLimit μ hμ (E ∩ Q) = increasingLimit (fun k => μ (k + r)) hshift (E ∩ Q) :=
      congrArg (fun ν : Measure X => ν (E ∩ Q)) (increasingLimit_add μ hμ r).symm
    _ = ⨆ k, μ (k + r) (E ∩ Q) :=
      increasingLimit_apply_measurable (fun k => μ (k + r)) hshift (hE.inter hQ)
    _ = _ := by simp_rw [Measure.restrict_apply hE]

private theorem increasingLimit_restrict_density_apply_shifted
    {X : Type*} [MeasurableSpace X] (μ : ℕ → Measure X) (hμ : Monotone μ)
    (r : ℕ) {Q E : Set X} (hQ : MeasurableSet Q) (hE : MeasurableSet E)
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    ((increasingLimit μ hμ).restrict Q).withDensity f E =
      ⨆ k, ((μ (k + r)).restrict Q).withDensity f E := by
  have hshift : Monotone (fun k => μ (k + r)) := fun _ _ hkl => hμ (Nat.add_le_add_right hkl r)
  calc
    ((increasingLimit μ hμ).restrict Q).withDensity f E =
        ∫⁻ q, (E ∩ Q).indicator f q ∂increasingLimit μ hμ := by
      rw [withDensity_apply _ hE, Measure.restrict_restrict hE,
        lintegral_indicator (hE.inter hQ)]
    _ = ∫⁻ q, (E ∩ Q).indicator f q ∂increasingLimit (fun k => μ (k + r)) hshift :=
      congrArg (fun ν : Measure X => ∫⁻ q, (E ∩ Q).indicator f q ∂ν)
        (increasingLimit_add μ hμ r).symm
    _ = ⨆ k, ∫⁻ q, (E ∩ Q).indicator f q ∂μ (k + r) :=
      lintegral_increasingLimit (fun k => μ (k + r)) hshift (hf.indicator (hE.inter hQ))
    _ = _ := by
      simp_rw [withDensity_apply _ hE, Measure.restrict_restrict hE,
        lintegral_indicator (hE.inter hQ)]

/-- Equality of positive stage balances passes through the genuine increasing measure limit, including infinite mass and arbitrary measurable positive densities. -/
theorem increasingLimit_restrict_add_withDensity_eq_of_shifted_balance
    {X : Type*} [MeasurableSpace X] {μa μb μE : ℕ → Measure X}
    (ha : Monotone μa) (hb : Monotone μb) (hE : Monotone μE)
    (r : ℕ) {Q : Set X} (hQ : MeasurableSet Q)
    {f g : X → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hbalance : ∀ k,
      (μa (k + r)).restrict Q + ((μE (k + r)).restrict Q).withDensity g =
        (μb (k + r)).restrict Q + ((μE (k + r)).restrict Q).withDensity f) :
    (increasingLimit μa ha).restrict Q + ((increasingLimit μE hE).restrict Q).withDensity g =
      (increasingLimit μb hb).restrict Q + ((increasingLimit μE hE).restrict Q).withDensity f := by
  apply Measure.ext
  intro E hEm
  have hrestrict (μ : ℕ → Measure X) (hμ : Monotone μ) :
      Monotone fun k => (μ (k + r)).restrict Q E := by
    intro k l hkl
    exact Measure.le_iff'.mp (Measure.restrict_mono subset_rfl (hμ (Nat.add_le_add_right hkl r))) E
  have hdensity {d : X → ℝ≥0∞} :
      Monotone fun k => ((μE (k + r)).restrict Q).withDensity d E := by
    intro k l hkl
    change ((μE (k + r)).restrict Q).withDensity d E ≤ ((μE (l + r)).restrict Q).withDensity d E
    rw [withDensity_apply _ hEm, withDensity_apply _ hEm]
    exact lintegral_mono'
      (Measure.restrict_mono subset_rfl (Measure.restrict_mono subset_rfl (hE (Nat.add_le_add_right hkl r)))) le_rfl
  rw [Measure.add_apply, Measure.add_apply,
    increasingLimit_restrict_apply_shifted μa ha r hQ hEm,
    increasingLimit_restrict_density_apply_shifted μE hE r hQ hEm hg,
    increasingLimit_restrict_apply_shifted μb hb r hQ hEm,
    increasingLimit_restrict_density_apply_shifted μE hE r hQ hEm hf,
    ENNReal.iSup_add_iSup_of_monotone (hrestrict μa ha) (hdensity (d := g)),
    ENNReal.iSup_add_iSup_of_monotone (hrestrict μb hb) (hdensity (d := f))]
  apply iSup_congr
  intro k
  simpa only [Measure.add_apply] using congrArg (fun μ : Measure X => μ E) (hbalance k)

variable {n : ℕ} {Ω Q : Opens (ComplexModel (n + 1))}
  {u : Fin (n + 1) → ComplexModel (n + 1) → EReal}

/-- The actual canonical mixed NP measures satisfy the positive time-slot balance on every natural precompact ordinary window, with all stage balances and floor levels internally produced. -/
theorem mixedTruncationLimitMeasure_timeLift_positive_balance
    (hQ : RelativelyCompactIn Q Ω) (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {p : ComplexModel (n + 1) → ℝ} (hp : IsSmoothPsdOn Ω p)
    (hψp : IsSmoothPsdOn Ω fun q => timeLift n ψ q + p q) :
    (mixedTruncationLimitMeasure Ω (Function.update u (Fin.last n) fun q => ((timeLift n ψ q + p q : ℝ) : EReal))
      (plurisubharmonicOn_update_last hu hψp)).restrict Q +
    ((mixedTruncationLimitMeasure Ω (Function.update u (Fin.last n) fun q => (lastNormSq n q : EReal))
      (plurisubharmonicOn_update_last hu (isSmoothPsdOn_lastNormSq Ω))).restrict Q).withDensity
      (fun q => ENNReal.ofReal (-timeLaplacian ψ (q (Fin.last n)))) =
    (mixedTruncationLimitMeasure Ω (Function.update u (Fin.last n) fun q => (p q : EReal))
      (plurisubharmonicOn_update_last hu hp)).restrict Q +
    ((mixedTruncationLimitMeasure Ω (Function.update u (Fin.last n) fun q => (lastNormSq n q : EReal))
      (plurisubharmonicOn_update_last hu (isSmoothPsdOn_lastNormSq Ω))).restrict Q).withDensity
      (fun q => ENNReal.ofReal (timeLaplacian ψ (q (Fin.last n)))) := by
  obtain ⟨R, hR⟩ := exists_shifted_mixedTruncationMeasure_timeLift_positive_balance hQ hu hψ hp hψp
  have hc : Continuous (fun q : ComplexModel (n + 1) => timeLaplacian ψ (q (Fin.last n))) :=
    (continuous_timeLaplacian hψ).comp (lastCoordinate n).continuous
  exact increasingLimit_restrict_add_withDensity_eq_of_shifted_balance
    (mixedTruncationMeasure_mono (plurisubharmonicOn_update_last hu hψp))
    (mixedTruncationMeasure_mono (plurisubharmonicOn_update_last hu hp))
    (mixedTruncationMeasure_mono (plurisubharmonicOn_update_last hu (isSmoothPsdOn_lastNormSq Ω)))
    (R + 1) Q.isOpen.measurableSet hc.measurable.ennreal_ofReal hc.neg.measurable.ennreal_ofReal hR

/-- When the actual original last slot is |τ|², the baseline is exactly its original canonical NP measure, ready for genuine signed fibre slicing. -/
theorem mixedTruncationLimitMeasure_timeLift_positive_balance_of_last
    (hQ : RelativelyCompactIn Q Ω) (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (hlast : u (Fin.last n) = fun q => (lastNormSq n q : EReal))
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {p : ComplexModel (n + 1) → ℝ} (hp : IsSmoothPsdOn Ω p)
    (hψp : IsSmoothPsdOn Ω fun q => timeLift n ψ q + p q) :
    (mixedTruncationLimitMeasure Ω (Function.update u (Fin.last n) fun q => ((timeLift n ψ q + p q : ℝ) : EReal))
      (plurisubharmonicOn_update_last hu hψp)).restrict Q +
    ((mixedTruncationLimitMeasure Ω u hu).restrict Q).withDensity
      (fun q => ENNReal.ofReal (-timeLaplacian ψ (q (Fin.last n)))) =
    (mixedTruncationLimitMeasure Ω (Function.update u (Fin.last n) fun q => (p q : EReal))
      (plurisubharmonicOn_update_last hu hp)).restrict Q +
    ((mixedTruncationLimitMeasure Ω u hu).restrict Q).withDensity
      (fun q => ENNReal.ofReal (timeLaplacian ψ (q (Fin.last n)))) := by
  classical
  have hEU : Function.update u (Fin.last n) (fun q => (lastNormSq n q : EReal)) = u := by
    funext i q
    by_cases hi : i = Fin.last n
    · subst i
      simp only [Function.update_self, hlast]
    · simp only [Function.update_of_ne hi]
  simpa only [hEU] using mixedTruncationLimitMeasure_timeLift_positive_balance hQ hu hψ hp hψp

end

end SGPT.Foundations.Analysis.Pending.NonPluripolarTimeSlotPositiveBalance
