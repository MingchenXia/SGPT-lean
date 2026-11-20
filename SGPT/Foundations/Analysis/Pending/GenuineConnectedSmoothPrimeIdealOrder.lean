import SGPT.Foundations.Analysis.Pending.RawConnectedSmoothPrimeIdealOrder
import SGPT.Foundations.Analysis.Pending.ZeroDimensionalQuasiPshMultiplierIdeals

set_option autoImplicit false

/-! # Whole smooth prime comparison on the genuine potential domain, including dimension zero -/

open Set Filter
open scoped Topology Manifold ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.GenuineConnectedSmoothPrimeIdealOrder

open FirstPass FirstPass.IEnvelope FirstPass.NonKahlerLocus
  AnalyticModificationLocalDiscrepancy

noncomputable section

/-- The source's genuine right potential domain supplies the zero-dimensional
case internally; positive dimension retains the exact raw smooth-prime criterion. -/
theorem iOrder_iff_all_connected_smooth_prime_orders
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
            (⨅ z ∈ E, lelongNumber (n := n) (fun w => v (π w)) z) ≤
              ⨅ z ∈ E, lelongNumber (n := n) (fun w => u (π w)) z := by
  cases n with
  | zero =>
    constructor
    · intro _hI Y _ _ _ π _hπ E _hclosed _hconn hhyper
      obtain ⟨k, hk, _hreg⟩ := hhyper
      omega
    · intro _horder
      exact ZeroDimensionalQuasiPshMultiplierIdeals.iOrderOnManifold_of_genuine_right u hv
  | succ m =>
    constructor
    · intro hI Y _ _ _ π hπ E hclosed hconn hhyper
      obtain ⟨k, hk, hreg⟩ := hhyper
      have hkm : k = m := by omega
      subst k
      exact (RawConnectedSmoothPrimeIdealOrder.iOrder_iff_all_connected_smooth_prime_orders
        hu hv.1).mp hI Y π hπ E hclosed hconn hreg
    · intro horder
      apply (RawConnectedSmoothPrimeIdealOrder.iOrder_iff_all_connected_smooth_prime_orders
        hu hv.1).mpr
      intro Y _ _ _ π hπ E hclosed hconn hreg
      exact horder Y π hπ E hclosed hconn ⟨m, rfl, hreg⟩

end
end SGPT.Foundations.Analysis.Pending.GenuineConnectedSmoothPrimeIdealOrder
