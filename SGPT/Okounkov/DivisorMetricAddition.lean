import SGPT.Okounkov.EffectiveDivisorCurrentCompatibility
import SGPT.Okounkov.ThetaPotentialCurrentCombinations
import SGPT.Foundations.Analysis.Pending.MemberPullback
import SGPT.Foundations.Analysis.Pending.MeteredDivisorOperations
import SGPT.Foundations.Analysis.Pending.IdealWeightProducts
import SGPT.Foundations.Analysis.Pending.GermIdealTotalTransform

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open GlobalCurrents CanonicalCurrentFrame GlobalPositiveCurrentACRestriction
open NaturalThetaPshGeometricCurrent LelongPoincareDivisor

/-- Genuine local principal products and the existing pole-preserving
generator logarithm identity metrize the actual effective Cartier sum. -/
theorem isDivisorMetric_meteredAdd {n : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (D D' : EffectiveDivisor n M) (E E' : MeteredEffectiveQDivisor n M)
    (hE : DivisorMetric.IsDivisorMetric D E)
    (hE' : DivisorMetric.IsDivisorMetric D' E') :
    DivisorMetric.IsDivisorMetric (GermIdealTotalTransform.EffectiveDivisor.add D D')
      (MeteredDivisorOperations.add E E') := by
  intro x
  obtain ⟨U, hU, hxU, g, hg, hgen, h, hh, hw⟩ := hE x
  obtain ⟨V, hV, hxV, g', hg', hgen', h', hh', hw'⟩ := hE' x
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, fun y => g y * g' y,
    (hg.mono inter_subset_left).mul (hg'.mono inter_subset_right), ?_,
    fun y => h y + h' y, ?_, ?_⟩
  · intro y hy f
    exact MemberPullback.mul_mem_iff_of_generators (hgen y hy.1) (hgen' y hy.2)
      (InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU hg hy.1)
      (InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hV hg' hy.2) f
  · intro e
    exact ((hh e).mono fun z hz => ⟨hz.1, hz.2.1⟩).add
      ((hh' e).mono fun z hz => ⟨hz.1, hz.2.2⟩)
  · intro y hy
    have hlog : generatorLog (fun _ : Fin 1 => fun z => g z * g' z) y =
        generatorLog (fun _ : Fin 1 => g) y + generatorLog (fun _ : Fin 1 => g') y := by
      have hfamily : IdealWeightProducts.mulFamily
          (fun _ : Fin 1 => g) (fun _ : Fin 1 => g') =
          (fun _ : Fin (1 * 1) => fun z => g z * g' z) := by
        funext i z
        rfl
      have hprod := IdealWeightProducts.generatorLog_mulFamily
        (fun _ : Fin 1 => g) (fun _ : Fin 1 => g') y
      rw [hfamily] at hprod
      exact hprod
    change E.weight y + E'.weight y = _
    rw [hw y hy.1, hw' y hy.2, hlog, EReal.coe_add]
    exact add_add_add_comm _ _ _ _

/-- The complete current of the actual metered sum is the whole current
sum, using the genuine previously normalized theta-current producer. -/
theorem integrationCurrent_meteredAdd_eq {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
    [IsComplexManifold (m + 1) M]
    (D D' : EffectiveDivisor (m + 1) M)
    (E E' : MeteredEffectiveQDivisor (m + 1) M)
    (hE : DivisorMetric.IsDivisorMetric D E)
    (hE' : DivisorMetric.IsDivisorMetric D' E') :
    integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m)
        (MeteredDivisorOperations.add E E') =
      integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) E +
        integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) E' := by
  have hu := isThetaPshPotential_effectiveDivisorMetric D E hE
  have hu' := isThetaPshPotential_effectiveDivisorMetric D' E' hE'
  obtain ⟨hs, hcur⟩ := exists_thetaPotentialCurrent_add hu hu'
  calc
    integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m)
        (MeteredDivisorOperations.add E E') =
      thetaPotentialCurrent (E.curvature + E'.curvature).val
        (fun x => E.weight x + E'.weight x) hs :=
      (thetaPotentialCurrent_effectiveDivisorMetric_eq
        (GermIdealTotalTransform.EffectiveDivisor.add D D')
        (MeteredDivisorOperations.add E E') (isDivisorMetric_meteredAdd D D' E E' hE hE')).symm
    _ = thetaPotentialCurrent E.curvature.val E.weight hu +
        thetaPotentialCurrent E'.curvature.val E'.weight hu' := hcur
    _ = _ := congrArg₂ (fun A B => A + B)
      (thetaPotentialCurrent_effectiveDivisorMetric_eq D E hE)
      (thetaPotentialCurrent_effectiveDivisorMetric_eq D' E' hE')

/-- Whole-current metric independence transfers the genuine sum identity
to the canonical complete currents of the actual Cartier ideals. -/
theorem effectiveDivisorIntegrationCurrent_add_eq {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    (D D' : EffectiveDivisor (m + 1) F.carrier) :
    effectiveDivisorIntegrationCurrent F (GermIdealTotalTransform.EffectiveDivisor.add D D') =
      effectiveDivisorIntegrationCurrent F D + effectiveDivisorIntegrationCurrent F D' := by
  obtain ⟨E, _hsup, hE⟩ := DivisorMetric.exists_divisorMetric D
  obtain ⟨E', _hsup', hE'⟩ := DivisorMetric.exists_divisorMetric D'
  calc
    effectiveDivisorIntegrationCurrent F (GermIdealTotalTransform.EffectiveDivisor.add D D') =
        integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m)
          (MeteredDivisorOperations.add E E') :=
      effectiveDivisorIntegrationCurrent_eq_of_metric F
        (GermIdealTotalTransform.EffectiveDivisor.add D D')
        (MeteredDivisorOperations.add E E') (isDivisorMetric_meteredAdd D D' E E' hE hE')
    _ = _ := integrationCurrent_meteredAdd_eq D D' E E' hE hE'
    _ = _ := congrArg₂ (fun A B => A + B)
      (effectiveDivisorIntegrationCurrent_eq_of_metric F D E hE).symm
      (effectiveDivisorIntegrationCurrent_eq_of_metric F D' E' hE').symm

end SGPT.Okounkov
