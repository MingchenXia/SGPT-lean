import SGPT.PSH.LocalIntegralOpenCoefficients

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

private theorem original_finite_global_coefficient
    (D : EffectiveGeometricQDivisor (m + 1) M) (V : Opens M)
    (s : Finset {P // 0 < D.coefficient P}) (d : ℕ)
    (a : {P // 0 < D.coefficient P} → ℕ)
    (hs : ∀ P, P ∈ s ↔ (P.val.val ∩ (V : Set M)).Nonempty)
    (ha : ∀ P ∈ s, D.coefficient P.val = (a P : ℚ) / (d : ℚ))
    (Q : GeometricPrimeCarrier (m + 1) M) (hQV : (Q.val ∩ (V : Set M)).Nonempty) :
    D.coefficient Q =
      (cartierGeometricPrimeCoefficient
        (∑ P ∈ s, a P • geometricPrimeCarrierEffectiveDivisor P.val) Q : ℚ) / (d : ℚ) := by
  classical
  rw [cartierGeometricPrimeCoefficient_finset_sum]
  by_cases hpos : 0 < D.coefficient Q
  · let QQ : {P // 0 < D.coefficient P} := ⟨Q, hpos⟩
    have hQQ : QQ ∈ s := (hs QQ).mpr hQV
    have hsum : (∑ P ∈ s, a P * cartierGeometricPrimeCoefficient
        (geometricPrimeCarrierEffectiveDivisor P.val) Q) = a QQ := by
      calc
        _ = a QQ * cartierGeometricPrimeCoefficient (geometricPrimeCarrierEffectiveDivisor QQ.val) Q := by
          apply Finset.sum_eq_single QQ
          · intro P _ hne
            have hQP : Q ≠ P.val := fun h => hne (Subtype.ext h.symm)
            rw [cartierGeometricPrimeCoefficient_reduced, if_neg hQP, mul_zero]
          · intro hnot
            exact False.elim (hnot hQQ)
        _ = a QQ := by rw [cartierGeometricPrimeCoefficient_reduced, if_pos rfl, mul_one]
    rw [hsum]
    exact ha QQ hQQ
  · have hzero : D.coefficient Q = 0 := le_antisymm (le_of_not_gt hpos) (D.coefficient_nonneg Q)
    have hsum : (∑ P ∈ s, a P * cartierGeometricPrimeCoefficient
        (geometricPrimeCarrierEffectiveDivisor P.val) Q) = 0 := by
      apply Finset.sum_eq_zero
      intro P _
      have hQP : Q ≠ P.val := by
        intro h
        have hp := P.property
        rw [← h, hzero] at hp
        exact (lt_irrefl (0 : ℚ)) hp
      rw [cartierGeometricPrimeCoefficient_reduced, if_neg hQP, mul_zero]
    rw [hsum, Nat.cast_zero, zero_div]
    exact hzero

/-- ORIGINAL D,x alone retain SAME exact V/S/local d/a/F and BOTH the
actual global-prime reader and EVERY target-open prime reader. No new
denominator, finite family or geometric data are supplied. -/
theorem exists_geometric_q_local_integral_global_open_coefficients
    (D : EffectiveGeometricQDivisor (m + 1) M) (x : M) :
    ∃ V : Opens M, x ∈ V ∧
      ∃ (s : Finset {P // 0 < D.coefficient P}) (d : ℕ)
        (a : {P // 0 < D.coefficient P} → ℕ),
        (∀ P, P ∈ s ↔ (P.val.val ∩ (V : Set M)).Nonempty) ∧ 0 < d ∧
        (∀ P ∈ s, 0 < a P ∧ D.coefficient P.val = (a P : ℚ) / (d : ℚ)) ∧
        let F := ∑ P ∈ s, a P • geometricPrimeCarrierEffectiveDivisor P.val
        (∀ P : GeometricPrimeCarrier (m + 1) M, (P.val ∩ (V : Set M)).Nonempty →
          D.coefficient P = (cartierGeometricPrimeCoefficient F P : ℚ) / (d : ℚ)) ∧
        ∀ (U : Opens M) (A : GeometricPrimeCarrier (m + 1) U),
          (A.val ∩ (Subtype.val : U → M) ⁻¹' (V : Set M)).Nonempty →
          (geometricQDivisorOpenRestriction D U).coefficient A =
            (cartierGeometricPrimeCoefficient (cartierOpenRestriction F U) A : ℚ) / (d : ℚ) := by
  obtain ⟨V, hxV, s, d, a, hs, hd, ha, hreader⟩ :=
    exists_geometric_q_local_integral_open_coefficients D x
  refine ⟨V, hxV, s, d, a, hs, hd, ha, ?_, hreader⟩
  intro P hP
  exact original_finite_global_coefficient D V s d a hs (fun P hP => (ha P hP).2) P hP

end SGPT.PSH
