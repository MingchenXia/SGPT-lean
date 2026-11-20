import SGPT.Foundations.Schemes.NativeFlagPowerCechComparison
import Mathlib.Algebra.Group.ForwardDiff

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- Repeated TRUE Euler differences reach the actual iterated-cut sequence,
with the genuine accumulated index shift. -/
theorem NativeClosedProjectiveStratum.powerEuler_iterated_fwdDiff {N : ℕ}
    (T : NativeClosedProjectiveStratum N) (j m : ℕ) :
    ((fwdDiff (1 : ℕ))^[j] T.powerEuler) m = (T.iterated j).powerEuler (m + j) := by
  induction j generalizing m with
  | zero => simp only [Function.iterate_zero_apply, NativeClosedProjectiveStratum.iterated, Nat.add_zero]
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    change ((fwdDiff (1 : ℕ))^[j] T.powerEuler) (m + 1) -
      ((fwdDiff (1 : ℕ))^[j] T.powerEuler) m = _
    rw [ih, ih]
    have h := (T.iterated j).powerEuler_cut_difference (m + j)
    simpa only [NativeClosedProjectiveStratum.iterated, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- The ORIGINAL Fano starting embedding has the actual stage-j native Euler
sequence as its j-fold forward difference, without a terminal-value input. -/
theorem SmoothProjectiveFano.nativeRegularProjectiveFlag_iterated_euler {n : ℕ}
    (F : SmoothProjectiveFano n) (j m : ℕ) :
    ((fwdDiff (1 : ℕ))^[j] (F.nativeRegularProjectiveFlag 0).powerEuler) m =
      (F.nativeRegularProjectiveFlag j).powerEuler (m + j) :=
  NativeClosedProjectiveStratum.powerEuler_iterated_fwdDiff
    (show NativeClosedProjectiveStratum F.projective.ambientDimension from
      ⟨Over.mk F.projective.map, F.projective.closedImmersion⟩) j m

/-- The ORIGINAL Fano n-fold native Euler difference reaches its ACTUAL
Artinian terminal scheme, without supplying length or intersection values. -/
theorem SmoothProjectiveFano.nativeRegularProjectiveFlag_terminal_euler_difference {n : ℕ}
    (F : SmoothProjectiveFano n) (m : ℕ) :
    ((fwdDiff (1 : ℕ))^[n] (F.nativeRegularProjectiveFlag 0).powerEuler) m =
      (F.nativeRegularProjectiveFlag n).powerEuler (m + n) :=
  F.nativeRegularProjectiveFlag_iterated_euler n m

end
end SGPT.Foundations.Schemes
