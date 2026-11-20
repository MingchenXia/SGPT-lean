import SGPT.PSH.HermitianBalayageFrozenCorrections
import SGPT.PSH.HermitianLocalCorrection
import SGPT.Foundations.Analysis.Pending.IncreasingTruncationReduction

/-!
# Actual bounded measurable coordinate data for frozen balayage

Coordinate maps are continuous only on their targets. The corrected real
reader is therefore extended by zero outside the actual open coordinate
domain. This supplies a globally measurable function without assumptions
on arbitrary off-target chart values, and agrees with the genuine
corrected potential everywhere on the original domain.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianBalayage

open Set Metric Filter MeasureTheory TopologicalSpace Classical
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open Hermitian
open scoped Topology ContDiff

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The actual corrected chart reader, extended measurably off its domain. -/
def correctedChartReader (e : ComplexChart (m + 1) M) (W : Opens (ComplexModel (m + 1)))
    (u : M → EReal) (q : ComplexModel (m + 1) → ℝ) : ComplexModel (m + 1) → ℝ :=
  (W : Set (ComplexModel (m + 1))).indicator (fun z => (chartFunction u e z).toReal + q z)

/-- An actual bounded nonnegative Hermitian PSH potential and a smooth
dominating correction produce genuine measurable locally bounded PSH
coordinate data for ordinary Bedford--Taylor balayage. -/
theorem correctedChartReader_measurable_locallyBoundedPsh
    {θ : SmoothRealForm (m + 1) M 2} (hθ₁ : θ.IsTypeOneOne)
    {u : M → EReal} (hu : IsFormPSH θ u)
    (e : ComplexChart (m + 1) M) {W : Opens (ComplexModel (m + 1))}
    (hW : W ≤ chartTarget e) {q : ComplexModel (m + 1) → ℝ}
    (hq : ContDiffOn ℝ ∞ q W)
    (hdom : ∀ z ∈ W, ∀ v : ComplexModel (m + 1),
      θ.coeff e z ![v, Complex.I • v] ≤ smoothDDC q z ![v, Complex.I • v])
    {S : ℝ} (hu0 : ∀ x, 0 ≤ u x) (huS : ∀ x, u x ≤ (S : EReal)) :
    Measurable (correctedChartReader e W u q) ∧
      IsLocallyBoundedPshOn W (correctedChartReader e W u q) ∧
      ∀ z ∈ W, (correctedChartReader e W u q z : EReal) =
        chartFunction u e z + (q z : EReal) := by
  let f := fun z => (chartFunction u e z).toReal + q z
  have hfinite (z : ComplexModel (m + 1)) :
      ((chartFunction u e z).toReal : EReal) = chartFunction u e z :=
    EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top S) (huS _))
      (ne_bot_of_le_ne_bot (by simp) (hu0 _))
  have hreal (z : ComplexModel (m + 1)) : (f z : EReal) =
      chartFunction u e z + (q z : EReal) := by
    rw [show f z = (chartFunction u e z).toReal + q z from rfl, EReal.coe_add, hfinite]
  have hp := chart_add_smooth_plurisubharmonicOn hθ₁ hu e hW hq hdom
  have hfp : PlurisubharmonicOn (fun z => (f z : EReal)) W := by
    intro z hz
    exact (hp z hz).congr (Eventually.of_forall (fun y => (hreal y).symm))
  have hm : Measurable (correctedChartReader e W u q) :=
    IncreasingTruncationLimit.measurable_indicator_of_upperSemicontinuousOn_coe
      W.isOpen hfp.upperSemicontinuousOn
  have hF (z : ComplexModel (m + 1)) (hz : z ∈ W) : correctedChartReader e W u q z = f z :=
    indicator_of_mem hz _
  have hFpsh : PlurisubharmonicOn (fun z => (correctedChartReader e W u q z : EReal)) W := by
    intro z hz
    apply (hfp z hz).congr
    filter_upwards [W.isOpen.mem_nhds hz] with y hy
    rw [hF y hy]
  refine ⟨hm, ⟨hFpsh, ?_⟩, fun z hz => ?_⟩
  · intro z hz
    have hqc : ContinuousAt q z := hq.continuousOn.continuousAt (W.isOpen.mem_nhds hz)
    have hnear : ∀ᶠ y in 𝓝 z, |q y| < |q z| + 1 :=
      hqc.abs.eventually (isOpen_Iio.mem_nhds (by linarith : |q z| < |q z| + 1))
    obtain ⟨V, hVsub, hVo, hzV⟩ := _root_.mem_nhds_iff.mp hnear
    refine ⟨W ⊓ ⟨V, hVo⟩, ⟨hz, hzV⟩, inf_le_left, S + (|q z| + 1), ?_⟩
    intro y hy
    have hnonneg : 0 ≤ (chartFunction u e y).toReal := by
      apply EReal.coe_le_coe_iff.mp
      rw [EReal.coe_zero, hfinite]
      exact hu0 _
    have hupper : (chartFunction u e y).toReal ≤ S := by
      apply EReal.coe_le_coe_iff.mp
      rw [hfinite]
      exact huS _
    rw [hF y hy.1]
    exact (abs_add_le _ _).trans (add_le_add
      (by simpa only [abs_of_nonneg hnonneg] using hupper) (hVsub hy.2).le)
  · rw [hF z hz]
    exact hreal z

end SGPT.PSH.HermitianBalayage
