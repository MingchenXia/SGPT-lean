import SGPT.PSH.HermitianExtremalSublevels
import SGPT.Foundations.Analysis.Pending.PshRadialRegularization
import SGPT.Foundations.Analysis.Pending.AdaptedRadialKernel

/-!
# Concrete decreasing smooth regularizations at genuine PSH poles

The kernel is the explicit normalized radial bump already constructed in
the distribution regularization library. The functions below are literal
convolutions of the locally integrable real representative; pointwise
convergence retains the original negative-infinity poles.

Source: FPT, `thm:compact-complex-global-josefson`, Step 1, and CADG I.5.5.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianExtremal

open Set Metric Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.PshRadialRegularization
open SGPT.Foundations.Analysis.Pending.AdaptedRadialKernel
open scoped Topology ContDiff

variable {n : ℕ}

/-- An actual smooth nonnegative unit-mass scalar-unitary-invariant kernel. -/
def standardRadialKernel : ComplexModel n → ℝ :=
  coordinateRadialKernel volume 1 zero_lt_one 0

theorem standardRadialKernel_isRadialKernel :
    IsRadialKernel (standardRadialKernel (n := n)) := by
  refine ⟨coordinateRadialKernel_contDiff volume 1 zero_lt_one 0,
    coordinateRadialKernel_nonneg volume 1 zero_lt_one 0,
    coordinateRadialKernel_integral_one volume 1 zero_lt_one 0, ?_,
    coordinateRadialKernel_unitary volume 1 zero_lt_one 0⟩
  rw [standardRadialKernel, coordinateRadialKernel_tsupport]
  norm_num

/-- The positive convolution radii, selected before any potential. -/
def radialRadius (R : ℝ) (j : ℕ) : ℝ := R / ((j : ℝ) + 1)

theorem radialRadius_pos {R : ℝ} (hR : 0 < R) (j : ℕ) : 0 < radialRadius R j :=
  div_pos hR (by positivity)

theorem radialRadius_antitone {R : ℝ} (hR : 0 < R) : Antitone (radialRadius R) := by
  intro j k hjk
  dsimp only [radialRadius]
  gcongr

theorem radialRadius_le {R : ℝ} (hR : 0 < R) (j : ℕ) : radialRadius R j ≤ R := by
  simpa only [radialRadius, Nat.cast_zero, zero_add, div_one] using
    radialRadius_antitone hR (Nat.zero_le j)

theorem tendsto_radialRadius (R : ℝ) : Tendsto (radialRadius R) atTop (𝓝 0) := by
  have hinv : Tendsto (fun j : ℕ => ((j : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp (by
      apply Filter.tendsto_atTop.mpr
      intro b
      obtain ⟨J, hJ⟩ := exists_nat_gt b
      filter_upwards [eventually_ge_atTop J] with j hj
      have hJj : (J : ℝ) ≤ j := by exact_mod_cast hj
      linarith)
  change Tendsto (fun j : ℕ => R / ((j : ℝ) + 1)) atTop (𝓝 0)
  simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul R

/-- The actual convolution sequence for the original extended-real PSH
representative. Taking `toReal` here is justified by the proved local L1
theory inside the radial regularization theorems. -/
def radialApproximation (R : ℝ) (u : ComplexModel n → EReal) (j : ℕ) :
    ComplexModel n → ℝ :=
  radialRegularization standardRadialKernel u (radialRadius R j)

/-- A uniform geometric buffer for every point of a smaller closed ball. -/
theorem closedBall_subset_innerDomain_ball (a : ComplexModel n) {r R : ℝ}
    (hrR : r < R) : closedBall a r ⊆ innerDomain (ball a R) ((R - r) / 2) := by
  intro z hz
  refine ⟨R - r, by linarith, ?_⟩
  intro y hy
  have hza := mem_closedBall.mp hz
  have hyz := mem_ball.mp hy
  exact (dist_triangle y z a).trans_lt (by linarith)

/-- Convolution itself manufactures all regularizations used for the
compact-sublevel construction, including convergence at poles and a
uniform nonpositive upper bound. -/
theorem radialApproximation_on_ball (a : ComplexModel n) {r R : ℝ}
    (hrR : r < R) {u : ComplexModel n → EReal}
    (hu : PlurisubharmonicOn u (ball a R))
    (hne : ∃ x ∈ ball a R, u x ≠ ⊥)
    (hnonpos : ∀ x ∈ ball a R, u x ≤ 0) :
    (∀ j, ContDiffOn ℝ ∞ (radialApproximation ((R - r) / 2) u j) (closedBall a r)) ∧
    (∀ j, PlurisubharmonicOn
      (fun z => (radialApproximation ((R - r) / 2) u j z : EReal)) (closedBall a r)) ∧
    (∀ z ∈ closedBall a r, Antitone fun j => radialApproximation ((R - r) / 2) u j z) ∧
    (∀ z ∈ closedBall a r, Tendsto
      (fun j => (radialApproximation ((R - r) / 2) u j z : EReal)) atTop (𝓝 (u z))) ∧
    ∀ j z, z ∈ closedBall a r →
      u z ≤ (radialApproximation ((R - r) / 2) u j z : EReal) ∧
      radialApproximation ((R - r) / 2) u j z ≤ 0 := by
  let s : ℝ := (R - r) / 2
  have hs : 0 < s := by dsimp only [s]; linarith
  have hbuffer : closedBall a r ⊆ innerDomain (ball a R) s :=
    closedBall_subset_innerDomain_ball a hrR
  have hbuf (j : ℕ) : closedBall a r ⊆ innerDomain (ball a R) (radialRadius s j) :=
    hbuffer.trans (innerDomain_anti (radialRadius_le hs j))
  have hkernel := standardRadialKernel_isRadialKernel (n := n)
  have hconn : IsPreconnected (ball a R) := (convex_ball a R).isPreconnected
  refine ⟨fun j => (contDiffOn_radialRegularization hkernel isOpen_ball hconn hu hne
      (radialRadius_pos hs j)).mono (hbuf j),
    fun j => (plurisubharmonicOn_radialRegularization hkernel isOpen_ball hconn hu hne
      (radialRadius_pos hs j)).mono (hbuf j), ?_, ?_, ?_⟩
  · intro z hz
    exact antitone_radialRegularization_seq hkernel isOpen_ball hconn hu hne
      (radialRadius_pos hs) (radialRadius_antitone hs) (by simpa [radialRadius] using hbuffer hz)
  · intro z hz
    exact tendsto_radialRegularization_seq hkernel isOpen_ball hconn hu hne
      (radialRadius_pos hs) (tendsto_radialRadius s)
      ((innerDomain_subset hs.le) (hbuffer hz))
  · intro j z hz
    refine ⟨le_radialRegularization hkernel isOpen_ball hconn hu hne
      (radialRadius_pos hs j) (hbuf j hz), ?_⟩
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨δ, hsδ, hball⟩ := hbuffer hz
    simpa only [zero_add, radialApproximation, s] using
      radialRegularization_le hkernel isOpen_ball hconn hu hne
      hball (fun y hy => (hnonpos y (hball hy)).trans_lt (EReal.coe_pos.mpr hε))
      (radialRadius_pos hs j) ((radialRadius_le hs j).trans_lt hsδ)

end SGPT.PSH.HermitianExtremal
