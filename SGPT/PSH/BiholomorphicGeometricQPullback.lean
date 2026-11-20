import SGPT.PSH.BiholomorphicGeometricQPreimage
import SGPT.PSH.BiholomorphicPrimeIdealOrder
import SGPT.PSH.GeometricQPullbackAnyDimension
import SGPT.PSH.FiniteGroupedCartierCoefficients

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open scoped Topology Manifold ContDiff

universe u

/-- Actual proper homeomorphism geometry and BOTH original holomorphic maps
supply the COMPLETE native modification record with SAME empty exceptional sets. -/
theorem nativeAnalyticModification_of_biholomorphic {n : ℕ} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]
    (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm) :
    IsAnalyticModification (n := n) e := by
  refine ⟨he, e.isProperMap, ∅, ∅, e.symm, isClosed_empty,
    isComplexAnalyticSubset_empty, interior_empty, isClosed_empty,
    isComplexAnalyticSubset_empty, interior_empty, preimage_empty,
    hei.contMDiffOn, ?_, ?_⟩
  · intro y _hy
    exact e.apply_symm_apply y
  · intro x _hx
    exact e.symm_apply_apply x

/-- ENTIRE reduced ideal image gives equality of actual Cartier transforms;
no ideal is inferred from support and no transform/order cert is supplied. -/
theorem geometricPrimeCarrierTotalTransform_biholomorphic {m : ℕ} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    [ChartedSpace (ComplexModel (m + 1)) N] [IsComplexManifold (m + 1) N]
    (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ e.symm)
    (P : GeometricPrimeCarrier (m + 1) N) :
    geometricPrimeCarrierTotalTransform P (nativeAnalyticModification_of_biholomorphic e he hei) =
      geometricPrimeCarrierEffectiveDivisor (biholomorphic_geometricPrimeCarrier_preimage e he hei P) := by
  apply HironakaEffectiveDivisorSum.effectiveDivisor_eq_of_ideal_eq
  rw [geometricPrimeCarrierTotalTransform_ideal, geometricPrimeCarrierEffectiveDivisor_ideal]
  exact biholomorphic_geometricPrimeCarrier_preimage_fullIdeal e he hei P

private theorem biholomorphic_pullback_coefficient {m : ℕ} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    [ChartedSpace (ComplexModel (m + 1)) N] [IsComplexManifold (m + 1) N]
    (D : EffectiveGeometricQDivisor (m + 1) N) (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ e.symm)
    (Q : GeometricPrimeCarrier (m + 1) M) :
    (geometricQDivisorModificationPullback D (nativeAnalyticModification_of_biholomorphic e he hei)).coefficient Q =
      (geometricQDivisorBiholomorphicPreimage D e he hei).coefficient Q := by
  classical
  let hπ := nativeAnalyticModification_of_biholomorphic e he hei
  let I := {P // 0 < D.coefficient P}
  let E : I → EffectiveDivisor (m + 1) M := fun P => geometricPrimeCarrierTotalTransform P.val hπ
  let K := biholomorphic_geometricPrimeCarrier_equiv e he hei
  let P₀ := K.symm Q
  obtain ⟨q, hq⟩ := Q.nonempty
  let s := (D.locallyFinite_positive.point_finite (e q)).toFinset
  have hs (P : I) : P ∈ s ↔ e q ∈ P.val.val := Set.Finite.mem_toFinset _
  have hLF : LocallyFinite (fun t : (P : I) × GlobalComponents.globalComponents (n := m + 1) (E P).support =>
      (cartierComponentGeometricPrime (E t.1) t.2).val) := by
    simpa only [GeometricPrimeTransformIndex, I, E, geometricPrimeTransformCarrier,
      cartierPrimeComponent_carrier, cartierComponentGeometricPrime] using locallyFinite_geometricPrimeTransformCarriers D hπ
  have hselect (t : (P : I) × GlobalComponents.globalComponents (n := m + 1) (E P).support)
      (ht : cartierComponentGeometricPrime (E t.1) t.2 = Q) : t.1 ∈ s := by
    have hval : t.2.val = Q.val := congrArg
      (fun P : GeometricPrimeCarrier (m + 1) M => P.val) ht
    have hqB : q ∈ t.2.val := by rw [hval]; exact hq
    have hqE := GlobalComponents.subset_of_mem_globalComponents
      (cartierSupport_isComplexAnalytic (E t.1)) t.2.property hqB
    rw [show (E t.1).support = e ⁻¹' t.1.val.val from
      geometricPrimeCarrierTotalTransform_support t.1.val hπ] at hqE
    exact (hs t.1).mpr hqE
  have hread : (geometricQDivisorModificationPullback D hπ).coefficient Q =
      ∑ P ∈ s, D.coefficient P.val * (cartierGeometricPrimeCoefficient (E P) Q : ℚ) := by
    rw [geometricQDivisorModificationPullback_coefficient]
    simpa only [GeometricPrimeTransformIndex, I, E, geometricPrimeTransformCarrier,
      cartierPrimeComponent_carrier, cartierComponentGeometricPrime] using
      finite_grouped_cartier_component_coefficient E (fun P => D.coefficient P.val) hLF s Q hselect
  have hterm (P : I) : cartierGeometricPrimeCoefficient (E P) Q =
      if Q = K P.val then 1 else 0 := by
    rw [show E P = geometricPrimeCarrierEffectiveDivisor (K P.val) from
      geometricPrimeCarrierTotalTransform_biholomorphic e he hei P.val]
    exact cartierGeometricPrimeCoefficient_reduced (K P.val) Q
  have hkey (P : I) : Q = K P.val ↔ P.val = P₀ := by
    constructor
    · intro h
      apply K.injective
      exact h.symm.trans (K.apply_symm_apply Q).symm
    · intro h
      rw [h]
      exact (K.apply_symm_apply Q).symm
  have hsum : (geometricQDivisorModificationPullback D hπ).coefficient Q =
      ∑ P ∈ s, if P.val = P₀ then D.coefficient P₀ else 0 := by
    rw [hread]
    apply Finset.sum_congr rfl
    intro P _hP
    rw [hterm]
    by_cases h : P.val = P₀
    · rw [if_pos ((hkey P).mpr h), if_pos h, Nat.cast_one, mul_one, h]
    · rw [if_neg (fun heq => h ((hkey P).mp heq)), if_neg h, Nat.cast_zero, mul_zero]
  change (geometricQDivisorModificationPullback D hπ).coefficient Q = D.coefficient P₀
  rw [hsum]
  by_cases hpos : 0 < D.coefficient P₀
  · let P : I := ⟨P₀, hpos⟩
    have hqP : e q ∈ P₀.val := by
      have hc : e ⁻¹' P₀.val = Q.val :=
        congrArg (fun R : GeometricPrimeCarrier (m + 1) M => R.val) (K.apply_symm_apply Q)
      rwa [← hc] at hq
    have hPs : P ∈ s := (hs P).mpr hqP
    rw [Finset.sum_eq_single P]
    · exact if_pos rfl
    · intro R _hR hRP
      exact if_neg (fun h => hRP (Subtype.ext h))
    · intro hP
      exact (hP hPs).elim
  · have hz : D.coefficient P₀ = 0 := le_antisymm (le_of_not_gt hpos) (D.coefficient_nonneg P₀)
    simp only [hz, ite_self, Finset.sum_const_zero]

private theorem geometric_q_eq_of_coefficient {n : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {D E : EffectiveGeometricQDivisor n M} (h : D.coefficient = E.coefficient) : D = E := by
  cases D
  cases E
  cases h
  rfl

/-- ORIGINAL D and actual biholomorphism internally supply the COMPLETE
modification and finite fiber selection. The genuine grouped pullback is the
ENTIRE rational preimage divisor, including absent primes and dimension zero. -/
theorem geometricQDivisorModificationPullbackAnyDimension_biholomorphic
    {n : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]
    (D : EffectiveGeometricQDivisor n N) (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm) :
    geometricQDivisorModificationPullbackAnyDimension D (nativeAnalyticModification_of_biholomorphic e he hei) =
      geometricQDivisorBiholomorphicPreimage D e he hei := by
  apply geometric_q_eq_of_coefficient
  funext Q
  cases n with
  | zero => exact isEmptyElim Q
  | succ m => exact biholomorphic_pullback_coefficient D e he hei Q

end SGPT.PSH
