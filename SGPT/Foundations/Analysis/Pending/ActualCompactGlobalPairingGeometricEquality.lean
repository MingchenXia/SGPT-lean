import SGPT.Foundations.Analysis.Pending.ActualCompactGlobalPairingCalibration

set_option autoImplicit false

/-!
# The actual compact current pairing respects geometric equality

Only coefficients on actual chart targets affect the native pairing. No
metric or positivity is needed to forget arbitrary off-target extensions.
-/

noncomputable section

open Set TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.ActualCompactGlobalPairingGeometricEquality

open FirstPass ChartPartition ActualCompactGlobalPairingCalibration
  ActualWeightedGlobalFormChartTests

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  {k : CurrentDegree n}

/-- Actual targetwise equality suffices to preserve the native compact pairing. -/
theorem pairing_eq_of_geometricallyEq (T : GlobalCurrent n M k)
    {γ δ : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)}
    (h : γ.GeometricallyEq δ) : pairingLM T γ = pairingLM T δ := by
  classical
  obtain ⟨m, χ, idx, hχ, -, hχs, hχc, hχ1⟩ :=
    exists_chartSmooth_partitionOfUnity (n := n)
      (fun x : M => (⟨(complexChartAt (n := n) x).val.source,
        (complexChartAt (n := n) x).val.open_source⟩ : Opens M))
      (fun x => ⟨x, mem_complexChartAt_source x⟩)
  let e : Fin m → ComplexChart n M := fun i => complexChartAt (idx i)
  have htests (i : Fin m) :
      ∃ η : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget (e i))
          (Module.finrank ℝ (ComplexModel n) - k.val),
        ∀ z, η z = (e i).val.target.indicator
          (fun y => χ i ((e i).val.symm y) • γ.coeff (e i) y) z := by
    obtain ⟨η, hη, -⟩ := exists_testForm (e i) γ (χ i) (hχ i) (hχc i) (hχs i)
    exact ⟨η, hη⟩
  choose η hη using htests
  have hδ (i : Fin m) (z : ComplexModel n) :
      η i z = (e i).val.target.indicator
        (fun y => χ i ((e i).val.symm y) • δ.coeff (e i) y) z := by
    by_cases hz : z ∈ (e i).val.target
    · rw [hη i z, indicator_of_mem hz, indicator_of_mem hz, h (e i) hz]
    · rw [hη i z, indicator_of_notMem hz, indicator_of_notMem hz]
  rw [pairing_eq_sum T γ m e χ hχ hχc hχs hχ1 η hη,
    pairing_eq_sum T δ m e χ hχ hχc hχs hχ1 η hδ]

end SGPT.Foundations.Analysis.Pending.ActualCompactGlobalPairingGeometricEquality
