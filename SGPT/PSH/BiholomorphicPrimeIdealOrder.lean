import SGPT.PSH.BiholomorphicPrimeTransport
import SGPT.PSH.LocalIntegralGeometricQDivisor
import SGPT.Foundations.Analysis.Pending.MonomialInvariantFunctorial

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff

universe u
variable {n : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]

/-- SAME actual prime preimage, ENTIRE reduced ideal image. Genuine preimage
prime Cartier geometry internally supplies coherence; no ideal/coherence
certificate or smooth/SNC hypothesis is an input. -/
theorem biholomorphic_geometricPrimeCarrier_preimage_fullIdeal (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm)
    (P : GeometricPrimeCarrier n N) :
    GermIdeal.pullback (m := n) e (vanishingIdeal (n := n) P.val) =
      vanishingIdeal (n := n) (biholomorphic_geometricPrimeCarrier_preimage e he hei P).val := by
  cases n with
  | zero => exact isEmptyElim P
  | succ m =>
    let Q := biholomorphic_geometricPrimeCarrier_preimage e he hei P
    have hcoh : (vanishingIdeal (n := m + 1) (e ⁻¹' P.val)).IsCoherent := by
      change (vanishingIdeal (n := m + 1) Q.val).IsCoherent
      rw [← geometricPrimeCarrierEffectiveDivisor_ideal Q]
      exact DivisorMetric.isCoherent_of_isInvertible
        (geometricPrimeCarrierEffectiveDivisor Q).isInvertible
    have h := MarkedIdealBiholomorphism.pullback_vanishingIdeal_preimage
      he hei e.apply_symm_apply e.symm_apply_apply (g := id) contMDiff_id P.val
    rw [Function.comp_id, BlowupControlledTransform.pullback_id hcoh] at h
    exact h.symm

/-- Original Cartier ideal and actual biholomorphism internally supply ALL
cosupport equalities; existing generic exponent transport retains the literal
first-failure/fallback definition. No order/regularity/cosupport cert is an input. -/
theorem cartierOrder_pullback_biholomorphic (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm)
    (D : EffectiveDivisor n N) (H : Set N) (x : M) :
    DivisorExponent.divExp n (GermIdeal.pullback (m := n) e D.ideal) (e ⁻¹' H) x =
      DivisorExponent.divExp n D.ideal H (e x) := by
  have hhol : ∀ y g, D.ideal.mem y g → HolomorphicAt n g y :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      (DivisorMetric.isCoherent_of_isInvertible D.isInvertible) hg
  apply MonomialInvariantFunctorial.divExp_pullback (φ := e)
    (𝔞 := D.ideal) (x' := x) (fun r => ?_) (e.map_nhds_eq x) H
  exact MarkedIdealBiholomorphism.MarkedIdeal.cosupp_pullback he hei
    e.apply_symm_apply e.symm_apply_apply (⟨univ, [], D.ideal, r⟩ : MarkedIdeals.MarkedIdeal n N) hhol

end SGPT.PSH
