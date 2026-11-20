import SGPT.Foundations.Analysis.Pending.SkodaIntegrability
import SGPT.Foundations.Analysis.Pending.ActualUnitMultiplierLelongBound
import SGPT.Foundations.Analysis.Pending.PositiveCurrentTraceMultiplier

set_option autoImplicit false

/-! # Actual ideal order preserves the zero generic Lelong domain -/

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.IdealOrderGenericLelongZero

open FirstPass FirstPass.NonKahlerLocus FirstPass.HolomorphicIdealSheaves FirstPass.IEnvelope

noncomputable section

/-- All-positive-level actual ideal order, forward Skoda and the actual inverse
unit estimate transport the generic-zero domain without a common minimizing point. -/
theorem generic_lelong_inf_eq_zero_of_iOrder
    {n : ℕ} {M Y : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {α : SmoothRealForm n M 2} {φ ψ : M → EReal}
    (hφ : ThetaPlurisubharmonic α φ)
    (horder : IOrderOnManifold (n := n) φ ψ) (ι : Y → M)
    (hgeneric : (⨅ y : Y, lelongNumber (n := n) φ (ι y)) = 0) :
    (⨅ y : Y, lelongNumber (n := n) ψ (ι y)) = 0 := by
  classical
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    have htop (y : Y) : lelongNumber (n := n) φ (ι y) = ⊤ :=
      LelongNumberChartTransport.lelongNumber_eq_top_of_eventually_bot
        (by rw [LelongNumberChartTransport.nhdsWithin_ne_eq_bot_of_dim_eq_zero hn0]
            exact Filter.eventually_bot)
    simp only [htop, iInf_top] at hgeneric
    exact ENNReal.top_ne_zero hgeneric
  apply le_antisymm ?_ zero_le
  apply ENNReal.le_of_forall_pos_le_add
  intro a ha _
  have haR : 0 < (a : ℝ) := ha
  let d : ℝ := (Module.finrank ℝ (ComplexModel n) : ℝ)
  have hd : 0 ≤ d := Nat.cast_nonneg _
  let c : ℝ := (d + 1) / (a : ℝ)
  have hc : 0 < c := div_pos (by linarith) haR
  have hac : (a : ℝ) * c = d + 1 := by dsimp only [c]; field_simp
  have hdc : d / c ≤ (a : ℝ) := (div_le_iff₀ hc).mpr (by rw [hac]; linarith)
  have hsmall : (⨅ y : Y, lelongNumber (n := n) φ (ι y)) <
      ENNReal.ofReal (2 / c) := by
    rw [hgeneric]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨y, hy⟩ := iInf_lt_iff.mp hsmall
  have hunit := SkodaIntegrability.one_mem_multiplierIdeal_of_lelongNumber_lt hφ hc hy
  have htarget := PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_iOrderOnManifold
    horder hc (ι y) (fun _ => (1 : ℂ)) hunit
  have hν := ActualUnitMultiplierLelongBound.lelongNumber_le_of_unit_multiplierIdeal hn htarget
  have hle : (⨅ y : Y, lelongNumber (n := n) ψ (ι y)) ≤ ENNReal.ofReal (a : ℝ) :=
    (iInf_le_of_le y hν).trans (ENNReal.ofReal_le_ofReal hdc)
  simpa only [zero_add, ENNReal.ofReal_coe_nnreal] using hle

end
end SGPT.Foundations.Analysis.Pending.IdealOrderGenericLelongZero
