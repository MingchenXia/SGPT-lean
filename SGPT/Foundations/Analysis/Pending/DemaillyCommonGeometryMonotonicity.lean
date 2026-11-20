import SGPT.Foundations.Analysis.Pending.DemaillyApproximationSequence
import SGPT.Foundations.Analysis.Pending.QuantitativeRegularizationSingularWeight

set_option autoImplicit false

/-! # Actual input monotonicity of fixed-geometry Demailly branches and sequences -/

open Set MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.DemaillyCommonGeometryMonotonicity
open FirstPass FirstPass.HolomorphicIdealSheaves BergmanSupWeight
  QuantitativeRegularizationChartBranch QuantitativeRegularizationFixedCover
  QuantitativeRegularizationMaxGluing DemaillyApproximationSequence
  DemaillySymmetricGluing DemaillySymmetricGluingLimit SymmetricRegularizedMaxPsh

noncomputable section

/-- Every actual chart branch is monotone in its raw input potential,
including the common off-patch zero values and all poles. -/
theorem chartBergmanBranch_mono
    {d : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel d) Z]
    (e : ComplexChart d Z) {B : Set (ComplexModel d)} (hB : MeasurableSet B)
    (ρ : ComplexModel d → ℝ) {φ ψ : Z → EReal} (h : φ ≤ ψ)
    (m : ℕ) (y : Z) :
    chartBergmanBranch e B ρ φ m y ≤ chartBergmanBranch e B ρ ψ m y := by
  classical
  unfold chartBergmanBranch
  split_ifs with hy
  · have hcorrect (z : ComplexModel d) : correctedWeight e ρ φ z ≤ correctedWeight e ρ ψ z :=
      add_le_add (h (e.val.symm z)) le_rfl
    have hweights (z : ComplexModel d) (_hz : z ∈ B) :
        multiplierWeight (m : ℝ) (correctedWeight e ρ ψ z) ≤
        multiplierWeight (m : ℝ) (correctedWeight e ρ φ z) :=
      multiplierWeight_antitone (Nat.cast_nonneg m) (hcorrect z)
    have hkernel := QuantitativeRegularizationSingularWeight.bergmanSup_antitone_weight
      hB hweights (e.val y)
    have hlog : bergmanLog B (fun z => multiplierWeight m (correctedWeight e ρ φ z)) (e.val y) ≤
        bergmanLog B (fun z => multiplierWeight m (correctedWeight e ρ ψ z)) (e.val y) :=
      ENNReal.log_monotone hkernel
    exact EReal.sub_le_sub (mul_le_mul_of_nonneg_left hlog
      (EReal.coe_nonneg.mpr (inv_nonneg.mpr (Nat.cast_nonneg m)))) le_rfl
  · exact le_rfl

/-- The actual common-geometry Demailly sequence is monotone in the raw
potential with the literal same smoothing and dyadic correction. -/
theorem seq_mono
    {d : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel d) Z]
    [IsComplexManifold d Z] (F : FixedChartCover d Z)
    (ρ : F.t → ComplexModel d → ℝ) {φ ψ : Z → EReal} (h : φ ≤ ψ)
    (E : ℝ) (k : ℕ) (y : Z) :
    seq F ρ φ E k y ≤ seq F ρ ψ E k y := by
  unfold DemaillyApproximationSequence.seq
  apply add_le_add_left
  unfold glued rglue
  apply ermax_mono
  intro j _hj
  unfold CutoffCover.branch FixedChartCover.branch
  exact add_le_add_left (chartBergmanBranch_mono (F.chart j) measurableSet_ball
    (ρ j) h (2 ^ k) y) _

end
end SGPT.Foundations.Analysis.Pending.DemaillyCommonGeometryMonotonicity
