import SGPT.Foundations.Analysis.PlurisubharmonicAE
import SGPT.Foundations.Analysis.FirstPass.ERealChordUSC

set_option autoImplicit false

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace SGPT.Foundations.Analysis.Pending.QuasiPshAlmostEverywhereComparison
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The actual quasi-PSH germ is its canonical almost-everywhere representative. -/
theorem le_of_ae_le {u v : E → EReal} {Ω : Set E}
    (hu : QuasiPlurisubharmonicOn u Ω) (hΩ : IsOpen Ω)
    (hv : UpperSemicontinuousOn v Ω) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hae : ∀ᵐ y ∂μ.restrict Ω, u y ≤ v y) : ∀ x ∈ Ω, u x ≤ v x := by
  intro x hx
  obtain ⟨p, h, hp, hh, heq⟩ := hu x hx
  obtain ⟨P, hPo, hxP, hpP⟩ := hp
  have hnbhd : {y | y ∈ Ω ∧ y ∈ P ∧ u y = p y + (h y : EReal) ∧
      ContDiffAt ℝ ∞ h y} ∈ 𝓝 x := by
    filter_upwards [hΩ.mem_nhds hx, hPo.mem_nhds hxP, heq, hh] with y hyΩ hyP hyeq hyh
    exact ⟨hyΩ, hyP, hyeq, hyh⟩
  obtain ⟨W, hWsub, hWo, hxW⟩ := _root_.mem_nhds_iff.mp hnbhd
  have hWΩ : W ⊆ Ω := fun y hy => (hWsub hy).1
  have hpW : PlurisubharmonicOn p W :=
    (hpP.plurisubharmonicOn hPo).mono fun y hy => (hWsub hy).2.1
  have hhc : ContinuousOn h W := fun y hy =>
    (hWsub hy).2.2.2.continuousAt.continuousWithinAt
  have hvc : UpperSemicontinuousOn (fun y => v y + ((-h y : ℝ) : EReal)) W :=
    (hv.mono hWΩ).add'
      (continuous_coe_real_ereal.comp_continuousOn hhc.neg).upperSemicontinuousOn
      (fun y _ => EReal.continuousAt_add
        (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _)))
  have hpae : ∀ᵐ y ∂μ.restrict W, p y ≤ v y + ((-h y : ℝ) : EReal) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hWΩ hae,
      ae_restrict_mem hWo.measurableSet] with y hy hyW
    have hle := add_le_add hy (le_rfl : ((-h y : ℝ) : EReal) ≤ ((-h y : ℝ) : EReal))
    rw [(hWsub hyW).2.2.1, add_assoc, ← EReal.coe_add, add_neg_cancel,
      EReal.coe_zero, add_zero] at hle
    exact hle
  have hle := add_le_add (hpW.le_of_ae_le hWo hvc μ hpae x hxW) (le_rfl : (h x : EReal) ≤ (h x : EReal))
  rw [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero] at hle
  rw [(hWsub hxW).2.2.1]
  exact hle

/-- No local finiteness or nondegeneracy is needed for quasi-PSH uniqueness. -/
theorem eqOn_of_ae_eq {u v : E → EReal} {Ω : Set E}
    (hu : QuasiPlurisubharmonicOn u Ω) (hv : QuasiPlurisubharmonicOn v Ω)
    (hΩ : IsOpen Ω) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hae : u =ᵐ[μ.restrict Ω] v) : EqOn u v Ω := by
  have huv := le_of_ae_le hu hΩ hv.upperSemicontinuousOn μ (hae.mono fun _ h => h.le)
  have hvu := le_of_ae_le hv hΩ hu.upperSemicontinuousOn μ (hae.mono fun _ h => h.ge)
  exact fun x hx => le_antisymm (huv x hx) (hvu x hx)

end SGPT.Foundations.Analysis.Pending.QuasiPshAlmostEverywhereComparison
