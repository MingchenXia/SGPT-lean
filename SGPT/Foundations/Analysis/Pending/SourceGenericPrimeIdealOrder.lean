import SGPT.Foundations.Analysis.Pending.RawQuasiPshLelongSuperlevels
import SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization
import SGPT.Foundations.Analysis.Pending.GenuineConnectedSmoothPrimeIdealOrder

set_option autoImplicit false

/-! # Source squared-log generic minima and the original whole-prime criterion

The source reader is independently defined by squared-logarithmic growth.
Its factor two is transported on each SAME whole prime, including infinite
values. No common-resolution existence or intrinsic quotient is asserted.
-/

open Set Filter
open scoped Topology ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.SourceGenericPrimeIdealOrder

open FirstPass FirstPass.IEnvelope FirstPass.NonKahlerLocus
  SquaredLogLelongSourceNormalization AnalyticModificationLocalDiscrepancy

noncomputable section

/-- The source squared-logarithm generic minimum is attained at an actual
point of every nonempty open piece, with the source zero-dimensional convention. -/
theorem exists_source_minimum_on_open_piece
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {u : M → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    (V : ClosedIrreducibleAnalyticSubvariety n M) {U : Set M}
    (hU : IsOpen U) (hVU : (V.carrier ∩ U).Nonempty) :
    ∃ x ∈ V.carrier ∩ U, squaredLogLelongNumber (n := n) u x =
      ⨅ y ∈ V.carrier, squaredLogLelongNumber (n := n) u y := by
  cases n with
  | zero =>
    obtain ⟨x, hx⟩ := hVU
    have hpoint (y : M) : squaredLogLelongNumber (n := 0) u y = 0 := by
      simp only [squaredLogLelongNumber, if_true]
    have hinf : (⨅ y ∈ V.carrier, squaredLogLelongNumber (n := 0) u y) = 0 :=
      le_antisymm (iInf₂_le_of_le x hx.1 (by rw [hpoint])) bot_le
    exact ⟨x, hx, (hpoint x).trans hinf.symm⟩
  | succ m =>
    obtain ⟨x, hx, hmin⟩ :=
      RawQuasiPshLelongSuperlevels.exists_minimum_on_open_piece hu V hU hVU
    refine ⟨x, hx, le_antisymm ?_ ?_⟩
    · apply (ENNReal.mul_le_mul_iff_right (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mp
      rw [← lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m),
        ← iInf_lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m)]
      exact hmin.le
    · apply (ENNReal.mul_le_mul_iff_right (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mp
      rw [← lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m),
        ← iInf_lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m)]
      exact hmin.ge

/-- Original all-level multiplier order is exactly source squared-logarithm
comparison on every whole connected smooth prime of every SAME-X modification. -/
theorem iOrder_iff_all_source_prime_orders
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {u v : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    (hv : IsGlobalQuasiPshPotential (n := n) v) :
    IOrderOnManifold (n := n) u v ↔
      ∀ (Y : Type u) [TopologicalSpace Y]
        [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] (π : Y → X),
        IsAnalyticModification (n := n) π →
        ∀ E : Set Y, IsClosed E → IsConnected E →
          (∃ k : ℕ, k + 1 = n ∧ ∀ z ∈ E, RegularAtDim (n := n) E z k) →
            (⨅ z ∈ E, squaredLogLelongNumber (n := n) (fun w => v (π w)) z) ≤
              ⨅ z ∈ E, squaredLogLelongNumber (n := n) (fun w => u (π w)) z := by
  rw [GenuineConnectedSmoothPrimeIdealOrder.iOrder_iff_all_connected_smooth_prime_orders hu hv]
  constructor
  · intro horder Y _ _ _ π hπ E hclosed hconn hhyper
    cases n with
    | zero =>
      obtain ⟨k, hk, _⟩ := hhyper
      omega
    | succ m =>
      exact (iInf_lelongNumber_le_iff_squaredLog (Nat.succ_ne_zero m)
        (fun w => u (π w)) (fun w => v (π w)) E).mp
        (horder Y π hπ E hclosed hconn hhyper)
  · intro horder Y _ _ _ π hπ E hclosed hconn hhyper
    cases n with
    | zero =>
      obtain ⟨k, hk, _⟩ := hhyper
      omega
    | succ m =>
      exact (iInf_lelongNumber_le_iff_squaredLog (Nat.succ_ne_zero m)
        (fun w => u (π w)) (fun w => v (π w)) E).mpr
        (horder Y π hπ E hclosed hconn hhyper)

end

end SGPT.Foundations.Analysis.Pending.SourceGenericPrimeIdealOrder
