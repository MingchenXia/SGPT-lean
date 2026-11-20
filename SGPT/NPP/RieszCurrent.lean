import SGPT.NPP.RieszPotential
import SGPT.Currents.PluriharmonicPotential
import SGPT.Foundations.Analysis.Pending.ActualScalarCurrentKahlerTracePairing

/-!
# The current `dd^c p_ν` of a logarithmic potential in one variable

Route for the reverse inequality of source `ex:1Dnpp` in one variable (blueprint
`claude-rc:log-potential`, part (2)).  For a finite measure `ν` carried by a compact set `K` and an
open set `W ⊆ ℂ¹` on which the logarithmic kernel stays below the level `C`, the potential
`p_ν = logPotential C ν` is a locally integrable psh function on `W`
(`isL1PshOn_logPotential`), and its current `dd^c p_ν` (TN's `ddcL1`) is the measure `ν`:
`dd^c p_ν (ω₀⁰)(φ) = ∫ φ dν` (`ddcL1_logPotential_apply_kahlerPower`).  Currents of bidimension
`(0,0)` on open subsets of `ℂ¹` are determined by their value on `ω₀⁰ = 1`
(`eq_of_apply_kahlerPower`).
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.Riesz

open Set Filter MeasureTheory SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.LocalCurrentL1Ddc
open SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
open scoped Topology ENNReal Distributions

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

/-- A constant form of degree `0` is a multiple of `ω₀⁰ = 1`. -/
theorem formSpan_zero_eq_smul_kahlerPower {n : ℕ} (γ : formSpan n 0) :
    γ = ((γ : RealForm n 0) (Fin.elim0 : Fin 0 → ComplexModel n)) • kahlerPower n 0 := by
  apply Subtype.ext
  apply ContinuousAlternatingMap.ext
  intro v
  have hv : v = (Fin.elim0 : Fin 0 → ComplexModel n) := by
    funext i
    exact Fin.elim0 i
  subst v
  simp [kahlerPower, formPower_zero, MongeAmpere.coordinateWedgeUnit]

/-- **Currents of bidimension `(0,0)` are determined by their value on `ω₀⁰`.** -/
theorem eq_of_apply_kahlerPower {n : ℕ} {W : TopologicalSpace.Opens (ComplexModel n)}
    {S T : LocalProductCurrent n W 0}
    (h : ∀ φ : 𝓓(W, ℝ), S (kahlerPower n 0) φ = T (kahlerPower n 0) φ) : S = T := by
  ext γ φ
  rw [formSpan_zero_eq_smul_kahlerPower γ]
  simp only [map_smul, smul_apply, smul_eq_mul, h]

/-- The deficit integral is finite almost everywhere on every bounded measurable set. -/
theorem ae_lintegral_kernelDeficit_lt_top {C : ℝ} {ν : Measure (ComplexModel 1)}
    [IsFiniteMeasure ν] {K : Set (ComplexModel 1)} (hK : Bornology.IsBounded K) (hνK : ν Kᶜ = 0)
    {S : Set (ComplexModel 1)} (hS : Bornology.IsBounded S) (hSm : MeasurableSet S) :
    ∀ᵐ z ∂(volume : Measure (ComplexModel 1)), z ∈ S → ∫⁻ w, kernelDeficit C z w ∂ν < ⊤ := by
  obtain ⟨R₀, hR₀⟩ := (hS.union hK).subset_closedBall 0
  set R : ℝ := max R₀ 0 with hRdef
  have hSR : S ⊆ Metric.closedBall 0 R := fun z hz =>
    Metric.closedBall_subset_closedBall (le_max_left _ _) (hR₀ (Or.inl hz))
  have hKR : ∀ w ∈ K, ‖w‖ ≤ R := fun w hw => by
    have := Metric.closedBall_subset_closedBall (le_max_left R₀ 0) (hR₀ (Or.inr hw))
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hνae : ∀ᵐ w ∂ν, w ∈ K := by rw [ae_iff]; exact hνK
  have hmeas : Measurable fun z => ∫⁻ w, kernelDeficit C z w ∂ν :=
    (measurable_kernelDeficit C).lintegral_prod_right'
  have hSfin : volume S < ⊤ :=
    (measure_mono hSR).trans_lt (measure_closedBall_lt_top (x := (0 : ComplexModel 1)))
  have hfin : ∫⁻ z in S, ∫⁻ w, kernelDeficit C z w ∂ν ≠ ⊤ := by
    rw [lintegral_lintegral_swap ((measurable_kernelDeficit C).comp measurable_id).aemeasurable]
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono_ae (hνae.mono fun w hw =>
      setLIntegral_kernelDeficit_le (C := C) hSm hSR (hKR w hw))) ?_)
    rw [lintegral_const]
    exact ENNReal.mul_lt_top (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      hSfin, lintegral_log_normSq_ball_lt_top _⟩) (measure_lt_top ν univ)
  have h1 := ae_lt_top hmeas hfin
  rwa [ae_restrict_iff' hSm] at h1

/-- **The logarithmic potential is a locally integrable psh function** on every open set on which
the kernel stays below the level. -/
theorem isL1PshOn_logPotential {C : ℝ} {ν : Measure (ComplexModel 1)} [IsFiniteMeasure ν]
    {K : Set (ComplexModel 1)} (hK : IsCompact K) (hνK : ν Kᶜ = 0)
    {W : TopologicalSpace.Opens (ComplexModel 1)}
    (hCK : ∀ z ∈ (W : Set (ComplexModel 1)), ∀ w ∈ K, logNormSq (z - w) ≤ (C : EReal)) :
    IsL1PshOn W (logPotential C ν) where
  psh := (discPshOn_logPotential hK.measurableSet hνK hCK).plurisubharmonicOn W.isOpen
  frequently_ne_bot := by
    intro x _
    rw [Filter.frequently_iff]
    intro U hU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
    have hae := ae_lintegral_kernelDeficit_lt_top (C := C) hK.isBounded hνK
      (Metric.isBounded_ball (x := x) (r := ε)) measurableSet_ball
    have hae' : ∀ᵐ z ∂(volume.restrict (Metric.ball x ε)),
        ∫⁻ w, kernelDeficit C z w ∂ν < ⊤ := (ae_restrict_iff' measurableSet_ball).mpr hae
    obtain ⟨y, hy, hyfin⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (Metric.measure_ball_pos volume x hε).ne' hae'
    exact ⟨y, hball hy, fun h => hyfin.ne ((logPotential_eq_bot_iff C ν y).mp h)⟩

open SGPT.Foundations.Analysis.Pending.XiaoPoissonLeviPositivity in
/-- **`dd^c p_ν = ν`** as currents: `dd^c p_ν (ω₀⁰)(φ) = ∫ φ dν` for every test function `φ` on
`W`. -/
theorem ddcL1_logPotential_apply_kahlerPower {C : ℝ} {ν : Measure (ComplexModel 1)}
    [IsFiniteMeasure ν] {K : Set (ComplexModel 1)} (hK : IsCompact K) (hνK : ν Kᶜ = 0)
    {W : TopologicalSpace.Opens (ComplexModel 1)}
    (hCK : ∀ z ∈ (W : Set (ComplexModel 1)), ∀ w ∈ K, logNormSq (z - w) ≤ (C : EReal))
    (φ : 𝓓(W, ℝ)) :
    ddcL1 (m := 0) W (logPotential C ν) (kahlerPower 1 0) φ = ∫ w, φ w ∂ν := by
  have hp := isL1PshOn_logPotential hK hνK hCK
  rw [ddcL1, SGPT.Currents.l1Current_eq_scalarTopCurrent hp.locallyIntegrableOn,
    ActualScalarCurrentKahlerTracePairing.ddc_scalarTopCurrent_kahlerPower_eq_sum_levi]
  simp only [distributionalLeviCLM_eq_testLevi, regularDistribution_apply, Fin.sum_univ_succ,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  rw [integral_testLevi_mul_logPotential hK hνK hCK φ]
  simp only [Nat.factorial_zero, Nat.cast_one]
  field_simp

end SGPT.NPP.Riesz
