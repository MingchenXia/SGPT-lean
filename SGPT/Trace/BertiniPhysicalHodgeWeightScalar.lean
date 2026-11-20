import SGPT.Trace.NativeCanonicalPhysicalHodgeIntegral

/-! Finite scalar weights factor out of the SAME full intrinsic physical
Hodge energy; raw sections, poles and infinite energies are retained. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical
open Set MeasureTheory
open scoped ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Trace.Bertini

variable {n : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]
  (L : HermitianHolomorphicLineBundle n Y)
  (S : ∀ y, (tensor (nativeCanonicalBundle (n := n) (X := Y)) L).Fiber y)
  (w : Y → ℝ≥0∞)

theorem nativePhysicalHodgeEnergy_weight_const_mul (c : ℝ≥0∞) (hc : c ≠ ⊤) :
    nativePhysicalHodgeEnergy L S (fun y => c * w y) = c * nativePhysicalHodgeEnergy L S w := by
  classical
  unfold nativePhysicalHodgeEnergy nativeCanonicalPartitionEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← lintegral_const_mul' c _ hc]
  apply lintegral_congr
  intro z
  unfold nativeCanonicalPhysicalCoordinateDensity
  split_ifs with hz
  · unfold nativeCanonicalPhysicalChartDensity
    dsimp only
    ac_rfl
  · simp only [mul_zero]

theorem nativePhysicalHodgeEnergy_weight_ofReal_mul (c : ℝ) :
    nativePhysicalHodgeEnergy L S (fun y => ENNReal.ofReal c * w y) =
      ENNReal.ofReal c * nativePhysicalHodgeEnergy L S w :=
  nativePhysicalHodgeEnergy_weight_const_mul L S w _ ENNReal.ofReal_ne_top

end SGPT.Trace.BertiniFamilyCanonical
