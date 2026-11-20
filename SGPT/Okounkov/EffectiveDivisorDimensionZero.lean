import SGPT.Okounkov.EffectiveDivisorOrder
import SGPT.Okounkov.OriginalFlagGeometry
import SGPT.Foundations.Analysis.Pending.RooftopDimZero

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending DivisorExponent IdealWeightPowers
open RelativePrincipalizationSpan

/-- Genuine zero-dimensional charts and actual Cartier invertibility force
the original ideal to be the unit ideal; no nonzero divisor exists here. -/
theorem effectiveDivisor_ideal_eq_unit_of_dimension_zero {M : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel 0) M] [IsComplexManifold 0 M]
    (D : EffectiveDivisor 0 M) : D.ideal = unitIdeal 0 M := by
  have hcoh := DivisorMetric.isCoherent_of_isInvertible D.isInvertible
  apply GermIdeal.ext
  funext x g
  apply propext
  constructor
  · exact fun hg => GermIdeal.IsInvertible.holomorphicAt_mem D.isInvertible hg
  · intro hg
    obtain ⟨f, hf, hfreq⟩ := effectiveDivisor_isNonzeroAt D x
    obtain ⟨y, hy, hy0⟩ := frequently_nhds_iff.mp hfreq {x}
      (by simp) (RooftopDimZero.isOpen_singleton_of_dim_zero rfl x)
    have hfx : f x ≠ 0 := by simpa only [mem_singleton_iff.mp hy] using hy0
    have hfhol := GermIdeal.IsInvertible.holomorphicAt_mem D.isInvertible hf
    refine GermIdealTotalTransform.mem_of_isInSpanAt_mem hcoh
      (isInSpanAt_of_eq_mul hf hg (hg.mul (BlowupFlatCoordinates.HolomorphicAt.inv hfhol hfx)) ?_)
    filter_upwards [hfhol.continuousAt.eventually_ne hfx] with z hz
    simp [hz]

/-- The actual original Cartier support is empty in complex dimension zero. -/
theorem effectiveDivisor_support_eq_empty_of_dimension_zero {M : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel 0) M] [IsComplexManifold 0 M]
    (D : EffectiveDivisor 0 M) : D.support = ∅ := by
  rw [EffectiveDivisor.support, effectiveDivisor_ideal_eq_unit_of_dimension_zero D]
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have h := hx (fun _ => (1 : ℂ)) (holomorphicAt_const 1)
  exact one_ne_zero h

end SGPT.Okounkov
