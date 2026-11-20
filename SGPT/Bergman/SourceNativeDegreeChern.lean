import SGPT.Bergman.SourceNativeTensorChern

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Bergman.NativeHermitianMetric
open Bundle Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open scoped Topology Manifold ContDiff TensorProduct

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The exact original Chern coefficient of every actual positive tensor
power, with all physical smoothness produced internally. -/
theorem sourceNativePositivePower_chern_coeff (L : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (c : ComplexChart n X)
    {z : ComplexModel n} (hz : z ∈ c.val.target) (j : ℕ) :
    (sourceNativeFirstChernForm (positivePower L j)
        (sourceNativePositivePower_smooth L hL j)).val.coeff c z =
      ((j + 1 : ℕ) : ℝ) • (sourceNativeFirstChernForm L hL).val.coeff c z := by
  induction j with
  | zero =>
      simp only [positivePower, Nat.zero_add, Nat.cast_one, one_smul]
  | succ j ih =>
      change (sourceNativeFirstChernForm (tensor (positivePower L j) L)
        (sourceNativeTensor_smooth _ _ (sourceNativePositivePower_smooth L hL j) hL)).val.coeff c z = _
      rw [sourceNativeTensor_chern_coeff (positivePower L j) L
        (sourceNativePositivePower_smooth L hL j) hL c hz, ih]
      push_cast
      module

/-- Actual degree-k L^k tensor T, including degree0, has its original
physical Chern coefficient k*c1(L)+c1(T). -/
theorem sourceNativeTwistedPower_chern_coeff (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (c : ComplexChart n X) {z : ComplexModel n} (hz : z ∈ c.val.target) (k : ℕ) :
    (sourceNativeFirstChernForm (twistedPower L T k)
        (sourceNativeTwistedPower_smooth L T hL hT k)).val.coeff c z =
      (k : ℝ) • (sourceNativeFirstChernForm L hL).val.coeff c z +
        (sourceNativeFirstChernForm T hT).val.coeff c z := by
  cases k with
  | zero =>
      change (sourceNativeFirstChernForm (tensor unit T)
        (sourceNativeTensor_smooth _ _ sourceNativeUnit_smooth hT)).val.coeff c z = _
      rw [sourceNativeTensor_chern_coeff unit T sourceNativeUnit_smooth hT c hz,
        sourceNativeUnit_chern_coeff c hz]
      simp only [Nat.cast_zero, zero_smul, zero_add]
  | succ k =>
      change (sourceNativeFirstChernForm (tensor (positivePower L k) T)
        (sourceNativeTensor_smooth _ _ (sourceNativePositivePower_smooth L hL k) hT)).val.coeff c z = _
      rw [sourceNativeTensor_chern_coeff (positivePower L k) T
        (sourceNativePositivePower_smooth L hL k) hT c hz,
        sourceNativePositivePower_chern_coeff L hL c hz k]

/-- The native whole IsOwn reader for the TRUE original all-degree twist
now has the exact original degree Chern background as its produced output. -/
theorem sourceNativeTwistedPower_isOwn (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T) (k : ℕ) :
    SGPT.PSH.GlobalL2.IsOwnFirstChernForm (twistedPower L T k)
      ((k : ℝ) • sourceNativeFirstChernForm L hL + sourceNativeFirstChernForm T hT) := by
  intro c e z hz hzE
  have h := sourceNativeFirstChernForm_isOwn (twistedPower L T k)
    (sourceNativeTwistedPower_smooth L T hL hT k) c e z hz hzE
  rw [sourceNativeTwistedPower_chern_coeff L T hL hT c hz k] at h
  simpa only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul] using h

end SGPT.Bergman.NativeHermitianMetric
