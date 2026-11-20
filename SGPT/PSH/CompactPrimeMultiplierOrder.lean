import SGPT.PSH.CompactPrimeOver
import SGPT.Foundations.Analysis.Pending.IntrinsicMultiplierOrder


set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.PSH.CompactPrimeMultiplierOrder

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open FirstPass.BlowupSequences FirstPass.HolomorphicIdealSheaves CompactPrimeOver
  FixedGermNormalOrder DemaillyApproximantDivisorialLelong
  MultiplierIdealLowerBound IntrinsicMultiplierOrder
open scoped Topology Manifold ContDiff

universe u

private theorem smooth_hypersurface {m : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    (p : PrimePresentation (m + 1) X) : IsClosedConnectedSubmanifold (m + 1) p.divisor m := by
  have hdim : p.divisorDimension = m := by
    have h := p.codimension_one
    omega
  simpa only [hdim] using p.smooth

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {φ : X → EReal} {c : ℝ}

/-- The same original presentation's ENTIRE literal pulled multiplier ideal coefficient in every dimension. -/
def presentationMultiplierOrder (hφ : IsGlobalQuasiPshPotential (n := n) φ) (hc : 0 < c)
    (p : PrimePresentation n X) : ℕ := by
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero 0 p.dimension_pos)
  | succ m => exact actualMultiplierCoefficient p.modification (smooth_hypersurface p) hφ hc

/-- Every literal original common-resolution witness gives equality of actual whole-ideal readers. -/
theorem presentationMultiplierOrder_eq_of_commonResolution
    (hφ : IsGlobalQuasiPshPotential (n := n) φ) (hc : 0 < c) {p q : PrimePresentation n X}
    (h : CommonResolutionGeometry p q) :
    presentationMultiplierOrder hφ hc p = presentationMultiplierOrder hφ hc q := by
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero 0 p.dimension_pos)
  | succ m =>
    exact actualMultiplierCoefficient_eq_of_common_resolution p.modification q.modification
      h.left_modification h.right_modification h.over_base
      (smooth_hypersurface p) (smooth_hypersurface q) h.strict_equal hφ hc

/-- The accepted actual domination producer covers every original merely-holomorphic witness. -/
theorem presentationMultiplierOrder_eq_of_holomorphicCommonResolution
    (hφ : IsGlobalQuasiPshPotential (n := n) φ) (hc : 0 < c) {p q : PrimePresentation n X}
    (h : HolomorphicCommonResolutionGeometry p q) :
    presentationMultiplierOrder hφ hc p = presentationMultiplierOrder hφ hc q := by
  obtain ⟨h'⟩ := (commonResolutionRelation_iff_holomorphicCommonResolutionRelation p q).mpr ⟨h⟩
  exact presentationMultiplierOrder_eq_of_commonResolution hφ hc h'

section Compact
variable [ConnectedSpace X] [CompactSpace X]

/-- Actual ENTIRE multiplier-ideal order on the proved literal DIRECT prime quotient. -/
def directMultiplierOrder (hφ : IsGlobalQuasiPshPotential (n := n) φ) (hc : 0 < c) :
    DirectPrimeOver n X → ℕ :=
  Quot.lift (presentationMultiplierOrder hφ hc) (by
    intro p q hpq
    obtain ⟨h⟩ := hpq
    exact presentationMultiplierOrder_eq_of_commonResolution hφ hc h)

/-- Every original representative computes the actual quotient reader exactly. -/
theorem directMultiplierOrder_mk (hφ : IsGlobalQuasiPshPotential (n := n) φ) (hc : 0 < c)
    (p : PrimePresentation n X) :
    directMultiplierOrder hφ hc (Quot.mk commonResolutionRelation p : DirectPrimeOver n X) =
      presentationMultiplierOrder hφ hc p := rfl
end Compact

/-- The quotient reads the coefficient of the SAME actual original full multiplier pullback. -/
theorem directMultiplierOrder_mk_eq_actualMultiplierCoefficient {m : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    [ConnectedSpace X] [CompactSpace X] {φ : X → EReal} {c : ℝ}
    (hφ : IsGlobalQuasiPshPotential (n := m + 1) φ) (hc : 0 < c)
    (p : PrimePresentation (m + 1) X)
    (hE : IsClosedConnectedSubmanifold (m + 1) p.divisor m) :
    directMultiplierOrder hφ hc (Quot.mk commonResolutionRelation p : DirectPrimeOver (m + 1) X) =
      actualMultiplierCoefficient p.modification hE hφ hc := rfl

/-- At EVERY actual original point/flattening the class reads the ENTIRE literal original stalk order. -/
theorem directMultiplierOrder_mk_eq_originalStalkNormalOrder {m : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    [ConnectedSpace X] [CompactSpace X] {φ : X → EReal} {c : ℝ}
    (hφ : IsGlobalQuasiPshPotential (n := m + 1) φ) (hc : 0 < c)
    (p : PrimePresentation (m + 1) X)
    (hE : IsClosedConnectedSubmanifold (m + 1) p.divisor m)
    (y : p.model) (hy : y ∈ p.divisor) (Φ : DivisorFlattening (m := m) p.divisor y) :
    (directMultiplierOrder hφ hc (Quot.mk commonResolutionRelation p : DirectPrimeOver (m + 1) X) : ℕ∞) =
      originalStalkNormalOrder Φ
        (GermIdeal.pullback (m := m + 1) p.projection (multiplierIdeal (n := m + 1) c φ)) := by
  rw [directMultiplierOrder_mk_eq_actualMultiplierCoefficient hφ hc p hE]
  exact (originalStalkNormalOrder_eq_actualMultiplierCoefficient p.modification hE hφ hc y hy Φ).symm

end SGPT.PSH.CompactPrimeMultiplierOrder
