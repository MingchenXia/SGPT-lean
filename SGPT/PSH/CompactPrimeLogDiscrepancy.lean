import SGPT.PSH.CompactPrimeOver
import SGPT.Foundations.Analysis.Pending.IntrinsicJacobianCoefficient


set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.PSH.CompactPrimeLogDiscrepancy

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open FirstPass.BlowupSequences CompactPrimeOver
  IntrinsicJacobianCoefficient ConnectedJacobianCoefficient
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

/-- The SAME original presentation's actual coefficient-plus-one, with a genuinely empty n=0 branch. -/
def presentationLogDiscrepancy (p : PrimePresentation n X) : ℕ := by
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero 0 p.dimension_pos)
  | succ m => exact representedLogDiscrepancy p.modification (smooth_hypersurface p)

/-- Every original presentation reads a positive actual natural log discrepancy. -/
theorem presentationLogDiscrepancy_pos (p : PrimePresentation n X) : 0 < presentationLogDiscrepancy p := by
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero 0 p.dimension_pos)
  | succ m => exact representedLogDiscrepancy_pos p.modification (smooth_hypersurface p)

/-- Genuine original common-model geometry proves the presentation equality; no compatibility is input. -/
theorem presentationLogDiscrepancy_eq_of_commonResolution {p q : PrimePresentation n X}
    (h : CommonResolutionGeometry p q) : presentationLogDiscrepancy p = presentationLogDiscrepancy q := by
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero 0 p.dimension_pos)
  | succ m =>
    exact representedLogDiscrepancy_eq_of_common_resolution p.modification q.modification
      h.left_modification h.right_modification h.over_base
      (smooth_hypersurface p) (smooth_hypersurface q) h.strict_equal

/-- EVERY literal merely-holomorphic domination witness is covered by the accepted actual input dictionary. -/
theorem presentationLogDiscrepancy_eq_of_holomorphicCommonResolution {p q : PrimePresentation n X}
    (h : HolomorphicCommonResolutionGeometry p q) :
    presentationLogDiscrepancy p = presentationLogDiscrepancy q := by
  obtain ⟨h'⟩ := (commonResolutionRelation_iff_holomorphicCommonResolutionRelation p q).mpr ⟨h⟩
  exact presentationLogDiscrepancy_eq_of_commonResolution h'

section Compact
variable [ConnectedSpace X] [CompactSpace X]

/-- Actual positive discrepancy on the accepted DIRECT prime quotient, using proved literal relation invariance. -/
def directLogDiscrepancy : DirectPrimeOver n X → ℕ :=
  Quot.lift presentationLogDiscrepancy (by
    intro p q hpq
    obtain ⟨h⟩ := hpq
    exact presentationLogDiscrepancy_eq_of_commonResolution h)

/-- The class reads EVERY original representative exactly. -/
theorem directLogDiscrepancy_mk (p : PrimePresentation n X) :
    directLogDiscrepancy (Quot.mk commonResolutionRelation p : DirectPrimeOver n X) =
      presentationLogDiscrepancy p := rfl

/-- Actual quotient induction preserves the genuine represented positivity. -/
theorem directLogDiscrepancy_pos (E : DirectPrimeOver n X) : 0 < directLogDiscrepancy E := by
  refine Quot.inductionOn E ?_
  intro p
  exact presentationLogDiscrepancy_pos p
end Compact

/-- The actual class of EACH original presentation has its SAME internally constructed coefficient plus one. -/
theorem directLogDiscrepancy_mk_eq_actualRelativeJacobianCoefficient {m : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    [ConnectedSpace X] [CompactSpace X] (p : PrimePresentation (m + 1) X)
    (hE : IsClosedConnectedSubmanifold (m + 1) p.divisor m) :
    directLogDiscrepancy (Quot.mk commonResolutionRelation p : DirectPrimeOver (m + 1) X) =
      actualRelativeJacobianCoefficient p.modification hE + 1 := rfl

end SGPT.PSH.CompactPrimeLogDiscrepancy
