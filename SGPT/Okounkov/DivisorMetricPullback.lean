import SGPT.Okounkov.ThetaCurrentPullbackCompatibility
import SGPT.Okounkov.EffectiveDivisorCurrentCompatibility
import SGPT.Okounkov.FlagLiftingExceptionalDivisor
import SGPT.Foundations.Analysis.Pending.MemberPullback
import SGPT.Foundations.Analysis.Pending.MeteredDivisorOperations

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open GermIdealTotalTransform
open GlobalCurrents CanonicalCurrentFrame GlobalPositiveCurrentACRestriction
open NaturalThetaPshGeometricCurrent LelongPoincareDivisor

/-- Actual principal ideal pullback and chart-smooth composition make the
existing metered pullback a genuine metric of the actual total transform. -/
theorem isDivisorMetric_meteredPullback {n : ℕ}
    {M Y : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] {π : Y → M}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (hint : interior (exceptionalLocus n π) = ∅)
    (D : EffectiveDivisor n M) (E : MeteredEffectiveQDivisor n M)
    (hE : DivisorMetric.IsDivisorMetric D E) :
    DivisorMetric.IsDivisorMetric (GermIdealTotalTransform.EffectiveDivisor.totalTransform hπ hint D)
      (MeteredDivisorOperations.pullback hπ hint E) := by
  intro y
  obtain ⟨U, hU, hyU, g, hg, hgen, h, hh, hw⟩ := hE (π y)
  refine ⟨π ⁻¹' U, hU.preimage hπ.continuous, hyU, g ∘ π, ?_, ?_,
    h ∘ π, fun e => MeteredDivisorOperations.contDiffOn_comp_chart_symm hπ hU hh e,
    fun z hz => ?_⟩
  · intro z hz
    exact ((hg (π z) hz).mdifferentiableAt (hU.mem_nhds hz)).comp_mdifferentiableWithinAt z
      ((hπ z).mdifferentiableAt (by simp)).mdifferentiableWithinAt
  · intro z hz f
    exact MemberPullback.pullback_mem_iff_of_generator hπ
      (InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU hg hz)
      (hgen (π z) hz) f
  · exact hw (π z) hz

/-- The genuine pulled metric representation is the complete integration
current of the actual total transform, including supported coefficients. -/
theorem thetaPotentialModificationCurrent_effectiveDivisorMetric_eq_totalTransform {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π)
    (D : EffectiveDivisor (m + 1) F.carrier)
    (E : MeteredEffectiveQDivisor (m + 1) F.carrier)
    (hE : DivisorMetric.IsDivisorMetric D E) :
    thetaPotentialModificationCurrent hπ E.curvature E.weight
      (isThetaPshPotential_effectiveDivisorMetric D E hE) =
    integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m)
      (MeteredDivisorOperations.pullback hπ.1.1 hπ.interior_exceptional_eq_empty E) := by
  let DA := GermIdealTotalTransform.EffectiveDivisor.totalTransform hπ.1.1 hπ.interior_exceptional_eq_empty D
  let EA := MeteredDivisorOperations.pullback hπ.1.1 hπ.interior_exceptional_eq_empty E
  have hEA : DivisorMetric.IsDivisorMetric DA EA :=
    isDivisorMetric_meteredPullback hπ.1.1 hπ.interior_exceptional_eq_empty D E hE
  exact thetaPotentialCurrent_effectiveDivisorMetric_eq DA EA hEA

/-- The complete pulled metric current equals the canonical whole current
of the actual ideal total transform; both metric choices are eliminated. -/
theorem thetaPotentialModificationCurrent_effectiveDivisorMetric_eq_canonicalTotalTransform
    {m : ℕ} {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π)
    (D : EffectiveDivisor (m + 1) F.carrier)
    (E : MeteredEffectiveQDivisor (m + 1) F.carrier)
    (hE : DivisorMetric.IsDivisorMetric D E) :
    thetaPotentialModificationCurrent hπ E.curvature E.weight
      (isThetaPshPotential_effectiveDivisorMetric D E hE) =
    effectiveDivisorIntegrationCurrent W
      (GermIdealTotalTransform.EffectiveDivisor.totalTransform hπ.1.1 hπ.interior_exceptional_eq_empty D) := by
  let DA := GermIdealTotalTransform.EffectiveDivisor.totalTransform hπ.1.1 hπ.interior_exceptional_eq_empty D
  let EA := MeteredDivisorOperations.pullback hπ.1.1 hπ.interior_exceptional_eq_empty E
  have hEA : DivisorMetric.IsDivisorMetric DA EA :=
    isDivisorMetric_meteredPullback hπ.1.1 hπ.interior_exceptional_eq_empty D E hE
  exact (thetaPotentialModificationCurrent_effectiveDivisorMetric_eq_totalTransform hπ D E hE).trans
    (effectiveDivisorIntegrationCurrent_eq_of_metric W DA EA hEA).symm

end SGPT.Okounkov
