import SGPT.Foundations.Analysis.Pending.SingularModelDarvasDiagonalUpperComparison
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasMetricSpace

set_option autoImplicit false

/-!
# Actual singular-model diagonal criterion for Darvas convergence

An independent filter-level consequence of the actual source Theorem 4.3.1,
Xia SGPT PDF0161--0163. Actual integral finiteness is produced by the actual
upper comparison before realification. Both arbitrary-family convergence
and the native metric-topology criterion then follow from the actual exact
dimension bounds, without an integral-finiteness or convergence certificate.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularModelDarvasDiagonalTopology

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularModelFiniteEnergyDiagonalGap SingularModelDarvasMetricSpace

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal} {hφ : IsModelPotential θ φ}

/-- True integral finiteness permits the exact real source comparison. -/
theorem relativeD1_le_diagonalGapIntegral_toReal_le (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ) :
    relativeD1 θ φ hφ u v ≤
        (diagonalGapIntegral θ u v hu.1.plurisubharmonic hv.1.plurisubharmonic).toReal ∧
      (diagonalGapIntegral θ u v hu.1.plurisubharmonic hv.1.plurisubharmonic).toReal ≤
        (3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)) * relativeD1 θ φ hφ u v := by
  have hupper := SingularModelDarvasDiagonalUpperComparison.diagonalGapIntegral_le_mul_relativeD1
    omega hu hv
  have hfinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hupper
  exact ⟨(ENNReal.ofReal_le_iff_le_toReal hfinite).mp
      (SingularModelDarvasDiagonalComparison.ofReal_relativeD1_le_diagonalGapIntegral omega hu hv),
    ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg (by positivity) (SingularModelDarvasBasic.relativeD1_nonneg omega hu hv)) hupper⟩

/-- Actual diagonal zero convergence is equivalent to actual distance zero convergence for any filter. -/
theorem diagonalGapIntegral_tendsto_zero_iff {I : Type*} {F : Filter I}
    (omega : KahlerBackground n M) {ui vi : I → M → EReal}
    (hu : ∀ i, RelativeFiniteEnergyPreceq θ φ (ui i) hφ)
    (hv : ∀ i, RelativeFiniteEnergyPreceq θ φ (vi i) hφ) :
    Tendsto (fun i => diagonalGapIntegral θ (ui i) (vi i)
      (hu i).1.plurisubharmonic (hv i).1.plurisubharmonic) F (𝓝 0) ↔
      Tendsto (fun i => relativeD1 θ φ hφ (ui i) (vi i)) F (𝓝 0) := by
  have hfinite (i : I) : diagonalGapIntegral θ (ui i) (vi i)
      (hu i).1.plurisubharmonic (hv i).1.plurisubharmonic ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (SingularModelDarvasDiagonalUpperComparison.diagonalGapIntegral_le_mul_relativeD1
        omega (hu i) (hv i))
  rw [← ENNReal.tendsto_toReal_zero_iff hfinite]
  constructor
  · intro hi
    exact squeeze_zero (fun i => SingularModelDarvasBasic.relativeD1_nonneg omega (hu i) (hv i))
      (fun i => (relativeD1_le_diagonalGapIntegral_toReal_le omega (hu i) (hv i)).1) hi
  · intro hd
    have hc := (tendsto_const_nhds
      (x := (3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)))).mul hd
    simp only [mul_zero] at hc
    exact squeeze_zero (fun _ => ENNReal.toReal_nonneg)
      (fun i => (relativeD1_le_diagonalGapIntegral_toReal_le omega (hu i) (hv i)).2) hc

/-- The actual diagonal integral detects convergence for the explicitly native Darvas topology. -/
theorem tendsto_native_iff_diagonalGapIntegral_tendsto_zero {I : Type*} {F : Filter I}
    (omega : KahlerBackground n M)
    (ui : I → ModelFiniteEnergyPotential θ φ hφ) (u : ModelFiniteEnergyPotential θ φ hφ) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
    Tendsto ui F (𝓝 u) ↔
      Tendsto (fun i => diagonalGapIntegral θ (ui i).val u.val
        (ui i).property.1.plurisubharmonic u.property.1.plurisubharmonic) F (𝓝 0) := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  rw [tendsto_iff_dist_tendsto_zero]
  exact (diagonalGapIntegral_tendsto_zero_iff omega
    (fun i => (ui i).property) (fun _ => u.property)).symm

end

end SGPT.Foundations.Analysis.Pending.SingularModelDarvasDiagonalTopology
