import SGPT.Projective.Sections
import SGPT.Okounkov.CoordinateResidual
import SGPT.Foundations.Analysis.Pending.LelongChartReaderInvariance
import SGPT.Foundations.Analysis.Pending.CoordinateLogarithmLelongNormalization
import SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization
import SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy
import SGPT.Foundations.Analysis.FirstPass.LelongNumberPole

/-!
# The hyperplane class of `ℙᴺ` and the Lelong numbers of hyperplane potentials

* `SGPT.Projective.ComplexProjectiveSpace.hyperplaneClass`: the class `H = {ω_FS}` of the
  Fubini–Study form (by Chern–Weil, `c₁(O(1))` is represented by the curvature `ω_FS` of the
  Fubini–Study metric `h_FS`; in the frame `Z_i` of `O(1)` over `U_i` its weight is
  `-log |Z_i|²_{h_FS} = log(1 + ‖z‖²)`, `coordLog_affinePoint_self`); it is a big (Kähler) class;
* `lelongNumber_smul_coordLog`, `squaredLogLelongNumber_smul_coordLog`: at every point of the
  coordinate hyperplane `H_i = {Z_i = 0}` the potential `c log(|Z_i|²/‖Z‖²)` of `c [H_i]`
  has Lelong number `2c` in the native normalisation of `lelongNumber` and `c` in the book's
  normalisation (`ν([H_i], p) = 1`);
* `lelongNumber_coordLog_of_ne`: off `H_i` the Lelong number is `0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus

namespace SGPT.Projective.ComplexProjectiveSpace

variable {N : ℕ}

/-- The hyperplane class `H = c₁(O(1)) = {ω_FS}` of `ℙᴺ`. -/
def hyperplaneClass (N : ℕ) : RealBottChern N (ComplexProjectiveSpace N) :=
  RealBottChern.ofRepresentative (fsBackground (N := N)).form

/-- The hyperplane class is big (it is a Kähler class). -/
theorem isBigClass_hyperplaneClass : IsBigClass (hyperplaneClass N) :=
  Pending.PluripolarCapacityDichotomy.isBigClass_kahler fsBackground

/-- The chart of the atlas given by `U_j`. -/
def affineComplexChart (j : Fin (N + 1)) : ComplexChart N (ComplexProjectiveSpace N) :=
  ⟨affineChart j, affineChart_mem_atlas j⟩

/-- At a point of the hyperplane `H_i = {Z_i = 0}`, `c log(|Z_i|²/‖Z‖²)` has (native)
Lelong number `2c`. -/
theorem lelongNumber_smul_coordLog {i : Fin (N + 1)} {p : ComplexProjectiveSpace N}
    (hp : p.rep i = 0) {c : ℝ≥0} (hc : 0 < c) :
    lelongNumber (n := N) (fun q => ((c : ℝ) : EReal) * coordLog i q) p = 2 * (c : ℝ≥0∞) := by
  obtain ⟨j, hj⟩ := exists_rep_ne_zero p
  have hij : i ≠ j := fun h => hj (h ▸ hp)
  obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hij
  have hpj : p ∈ (affineChart j).source := (mem_affineChart_source_iff j p).mpr hj
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  rw [← Pending.LelongChartReaderInvariance.lelongNumber_chartFunction_eq
    (affineComplexChart j) hpj]
  have hz : (affineChart j p) k = 0 := by
    conv_lhs => rw [← mk_rep p]
    rw [affineChart_mk j p.rep_ne_zero hj, affineRatio_apply, hp, zero_div]
  have hfun : chartFunction (fun q => ((c : ℝ) : EReal) * coordLog (j.succAbove k) q)
      (affineComplexChart j) =
      fun z => ((c : ℝ) : EReal) * logNormSq (z k) + ((-((c : ℝ) * fsPotential z) : ℝ) : EReal) := by
    funext z
    change ((c : ℝ) : EReal) * coordLog (j.succAbove k) (affinePoint j z) = _
    rw [coordLog_affinePoint_succAbove]
    rcases eq_or_ne (logNormSq (z k)) ⊥ with hb | hb
    · rw [hb, EReal.bot_sub, EReal.coe_mul_bot_of_pos hcR, EReal.bot_add]
    · lift logNormSq (z k) to ℝ using ⟨logNormSq_ne_top _, hb⟩ with x
      rw [← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
        EReal.coe_eq_coe_iff]
      ring
  rw [hfun]
  change lelongNumber (n := N) (fun z => ((c : ℝ) : EReal) * logNormSq (z k) +
    ((-((c : ℝ) * fsPotential z) : ℝ) : EReal)) (affineChart j p) = _
  rw [Pending.CoordinateLogarithmLelongNormalization.lelongNumber_add_bounded_eq (n := N)
    (u := fun z : ComplexModel N => ((c : ℝ) : EReal) * logNormSq (z k))
    (b := fun z : ComplexModel N => -((c : ℝ) * fsPotential z))
    (boundedRealGermAt_of_continuousAt
      ((continuous_const.mul contDiff_fsPotential.continuous).neg.continuousAt))]
  exact SGPT.Okounkov.lelongNumber_scaled_logNormSq_eq k hz hc

/-- Book normalisation: at a point of `H_i`, `c log(|Z_i|²/‖Z‖²)` has Lelong number `c`;
in particular `ν([H_i], p) = 1` for `p ∈ H_i`. -/
theorem squaredLogLelongNumber_smul_coordLog {i : Fin (N + 1)} {p : ComplexProjectiveSpace N}
    (hp : p.rep i = 0) {c : ℝ≥0} (hc : 0 < c) :
    Pending.SquaredLogLelongSourceNormalization.squaredLogLelongNumber (n := N)
      (fun q => ((c : ℝ) : EReal) * coordLog i q) p = (c : ℝ≥0∞) := by
  have hN : N ≠ 0 := by
    rintro rfl
    apply p.rep_ne_zero
    funext m
    rw [show m = i from Fin.ext (by have := m.isLt; have := i.isLt; omega), hp]
    rfl
  have h := Pending.SquaredLogLelongSourceNormalization.lelongNumber_eq_two_mul_squaredLog
    (n := N) hN (fun q => ((c : ℝ) : EReal) * coordLog i q) p
  rw [lelongNumber_smul_coordLog hp hc] at h
  exact (ENNReal.mul_right_inj (by norm_num) (by norm_num)).mp h.symm

theorem lelongNumber_coordLog {i : Fin (N + 1)} {p : ComplexProjectiveSpace N}
    (hp : p.rep i = 0) : lelongNumber (n := N) (coordLog i) p = 2 := by
  have h := lelongNumber_smul_coordLog hp (c := 1) one_pos
  simpa using h

/-- Off the hyperplane `H_i`, the Lelong number of `log(|Z_i|²/‖Z‖²)` vanishes (`N ≥ 1`; for
`N = 0` the punctured neighbourhood filter is trivial). -/
theorem lelongNumber_coordLog_of_ne (hN : 0 < N) {i : Fin (N + 1)} {p : ComplexProjectiveSpace N}
    (hp : p.rep i ≠ 0) : lelongNumber (n := N) (coordLog i) p = 0 := by
  have hfin : coordLog i p ≠ ⊥ := by
    conv_lhs => rw [← mk_rep p]
    rw [Ne, coordLog_mk_eq_bot_iff]
    exact hp
  apply le_antisymm _ bot_le
  apply le_of_not_gt
  intro hpos
  exact hfin (eq_bot_of_lelongNumber_pos hN (isThetaPshPotential_coordLog i).1 hpos)

end SGPT.Projective.ComplexProjectiveSpace
