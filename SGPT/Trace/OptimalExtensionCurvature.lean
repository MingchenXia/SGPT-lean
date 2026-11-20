import SGPT.Trace.OptimalExtensionODE
import SGPT.Trace.TwistedL2Twist

/-!
# Actual local Guan–Zhou curvature weights

The scalar weights are their literal integral producers. The curvature here
is exactly the existing global twisted-estimate local expression, with no
output-curvature certificate assumed. The sharp global estimate and limits
remain separate.
Blueprint: work/sgpt-resume-20261114/bert-e2-curvature/blueprint/bert-e2-curvature.tex.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.OptimalExtensionCurvature
open SGPT.Trace.OptimalExtensionODE SGPT.Trace.TwistedL2
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open Set Filter
open scoped Topology ContDiff

/-- Guan–Zhou's actual native local twisting function. -/
def localTwist {n : ℕ} (w : ℝ → ℝ) (Ψ : ComplexModel n → ℝ) (z : ComplexModel n) : ℝ :=
  twist w (-Ψ z)

/-- The positive reciprocal correction used by the existing twisted
Bochner curvature, which writes the last term as |∂a|²/b. -/
def localCorrection {n : ℕ} (w : ℝ → ℝ) (Ψ : ComplexModel n → ℝ) (z : ComplexModel n) : ℝ :=
  (correction w (-Ψ z))⁻¹

/-- The original smooth local bundle weight plus the actual scalar potential. -/
def localWeight {n : ℕ} (w : ℝ → ℝ) (Ψ p : ComplexModel n → ℝ) (z : ComplexModel n) : ℝ :=
  p z + potential w (-Ψ z)

/-- The literal Guan–Zhou curvature identity for the actual existing
twisted-curvature expression. The scalar equations have been produced from
integrals, and are not hypotheses. -/
theorem actual_local_twistedCurvature {n : ℕ} {w : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r)
    (hanti : AntitoneOn w (Ici 0)) {Ψ p : ComplexModel n → ℝ} {z : ComplexModel n}
    (hΨ : ContDiffAt ℝ 2 Ψ z) (hp : ContDiffAt ℝ 2 p z) (hz : Ψ z < 0) (v : ComplexModel n) :
    twistedCurvature (localTwist w Ψ) (localCorrection w Ψ) (localWeight w Ψ p) z v =
      twist w (-Ψ z) * leviForm p z v + leviForm Ψ z v := by
  let T : ComplexModel n → ℝ := fun y => -Ψ y
  have ht : 0 < T z := neg_pos.mpr hz
  have hT : ContDiffAt ℝ 2 T z := hΨ.neg
  have hu : ContDiffAt ℝ 2 (potential w) (T z) :=
    (contDiffAt_potential hw hpos ht).of_le (WithTop.coe_le_coe.mpr le_top)
  have hs : ContDiffAt ℝ 2 (twist w) (T z) :=
    (contDiffAt_twist hw hpos ht).of_le (WithTop.coe_le_coe.mpr le_top)
  have hLu : leviForm (fun y => potential w (T y)) z v =
      deriv (potential w) (T z) * leviForm T z v +
        deriv (deriv (potential w)) (T z) * holDerivSq T z v :=
    StokesCutoff.leviForm_comp hu hT v
  have hLs : leviForm (fun y => twist w (T y)) z v =
      deriv (twist w) (T z) * leviForm T z v +
        deriv (deriv (twist w)) (T z) * holDerivSq T z v :=
    StokesCutoff.leviForm_comp hs hT v
  have hLa : leviForm (localWeight w Ψ p) z v =
      leviForm p z v + leviForm (fun y => potential w (T y)) z v :=
    leviForm_add hp (hu.comp z hT) v
  have hD := holDerivSq_comp (hs.differentiableAt (by norm_num))
    (hT.differentiableAt (by norm_num)) v
  have h1 := first_ode hw.continuous hpos ht
  have h2 := actual_curvature_cancellation hw.continuous hpos hanti ht
  have hTL : leviForm T z v = -leviForm Ψ z v := leviForm_neg Ψ z v
  unfold twistedCurvature
  change twist w (T z) * leviForm (localWeight w Ψ p) z v -
    leviForm (fun y => twist w (T y)) z v -
    holDerivSq (fun y => twist w (T y)) z v / (correction w (T z))⁻¹ = _
  rw [hLa, hLu, hLs, hD, div_inv_eq_mul]
  calc
    _ = twist w (T z) * leviForm p z v -
        (deriv (twist w) (T z) - twist w (T z) * deriv (potential w) (T z)) * leviForm T z v +
        (curvatureCoefficient w (T z) - correction w (T z) * deriv (twist w) (T z) ^ 2) *
          holDerivSq T z v := by unfold curvatureCoefficient; ring
    _ = _ := by rw [h1, h2, hTL]; ring

theorem actual_local_twistedCurvature_nonneg {n : ℕ} {w : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r)
    (hanti : AntitoneOn w (Ici 0)) {Ψ p : ComplexModel n → ℝ} {z : ComplexModel n}
    (hΨ : ContDiffAt ℝ 2 Ψ z) (hp : ContDiffAt ℝ 2 p z) (hz : Ψ z < 0) (v : ComplexModel n)
    (hLp : 0 ≤ leviForm p z v) (hLΨ : 0 ≤ leviForm Ψ z v) :
    0 ≤ twistedCurvature (localTwist w Ψ) (localCorrection w Ψ) (localWeight w Ψ p) z v := by
  rw [actual_local_twistedCurvature hw hpos hanti hΨ hp hz v]
  exact add_nonneg (mul_nonneg (twist_pos hw.continuous hpos (neg_pos.mpr hz)).le hLp) hLΨ

theorem actual_local_twistedCurvature_pos {n : ℕ} {w : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r)
    (hanti : AntitoneOn w (Ici 0)) {Ψ p : ComplexModel n → ℝ} {z : ComplexModel n}
    (hΨ : ContDiffAt ℝ 2 Ψ z) (hp : ContDiffAt ℝ 2 p z) (hz : Ψ z < 0) (v : ComplexModel n)
    (hLp : 0 < leviForm p z v) (hLΨ : 0 ≤ leviForm Ψ z v) :
    0 < twistedCurvature (localTwist w Ψ) (localCorrection w Ψ) (localWeight w Ψ p) z v := by
  rw [actual_local_twistedCurvature hw hpos hanti hΨ hp hz v]
  exact add_pos_of_pos_of_nonneg (mul_pos (twist_pos hw.continuous hpos (neg_pos.mpr hz)) hLp) hLΨ

/-- The actual epsilon-delta annular density discharges every scalar
hypothesis of the local curvature identity. -/
theorem actual_annular_twistedCurvature {n : ℕ} {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    {Ψ p : ComplexModel n → ℝ} {z : ComplexModel n}
    (hΨ : ContDiffAt ℝ 2 Ψ z) (hp : ContDiffAt ℝ 2 p z) (hz : Ψ z < 0) (v : ComplexModel n) :
    twistedCurvature (localTwist (annularDensity ε δ) Ψ)
      (localCorrection (annularDensity ε δ) Ψ) (localWeight (annularDensity ε δ) Ψ p) z v =
      twist (annularDensity ε δ) (-Ψ z) * leviForm p z v + leviForm Ψ z v :=
  actual_local_twistedCurvature (contDiff_annularDensity ε δ)
    (fun r _ => annularDensity_pos ε hδ r)
    ((antitone_annularDensity hε hδ.le).antitoneOn (Ici 0)) hΨ hp hz v

/-- The literal correction has an actual smooth rational expression in
its original integral primitives. -/
theorem correction_eq_ratio {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) (hanti : AntitoneOn w (Ici 0))
    {t : ℝ} (ht : 0 < t) :
    correction w t = w t * mass w t / (mass w t ^ 2 - integratedMass w t * w t) := by
  have hd := hw.differentiable (by simp) t
  have hs := (deriv_twist_pos hw.continuous hpos hanti ht).ne'
  have he : correction w t = -deriv (potential w) t / deriv (twist w) t := by
    rw [correction, curvatureCoefficient_eq hw.continuous hpos ht hd]
    field_simp
  have hA := (mass_pos hw.continuous hpos ht).ne'
  have hq : mass w t ^ 2 - integratedMass w t * w t ≠ 0 := by
    have h := mass_sq_gt_weight_integratedMass hw.continuous hpos hanti ht
    nlinarith
  have hds : 1 - integratedMass w t * w t / mass w t ^ 2 ≠ 0 := by
    rwa [deriv_twist hw.continuous hpos ht] at hs
  rw [he, deriv_potential hw.continuous hpos ht, deriv_twist hw.continuous hpos ht]
  field_simp

theorem contDiffAt_correction {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) (hanti : AntitoneOn w (Ici 0))
    {t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ ∞ (correction w) t := by
  have he : correction w =ᶠ[𝓝 t]
      (fun r => w r * mass w r / (mass w r ^ 2 - integratedMass w r * w r)) := by
    filter_upwards [Ioi_mem_nhds ht] with r hr
    exact correction_eq_ratio hw hpos hanti hr
  have hq : mass w t ^ 2 - integratedMass w t * w t ≠ 0 := by
    have h := mass_sq_gt_weight_integratedMass hw.continuous hpos hanti ht
    nlinarith
  exact ((hw.contDiffAt.mul (contDiff_mass hw).contDiffAt).div
    (((contDiff_mass hw).contDiffAt.pow 2).sub
      ((contDiff_integratedMass hw).contDiffAt.mul hw.contDiffAt)) hq).congr_of_eventuallyEq he

theorem contDiffAt_inverse_correction {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) (hanti : AntitoneOn w (Ici 0))
    {t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ ∞ (fun r => (correction w r)⁻¹) t :=
  (contDiffAt_correction hw hpos hanti ht).inv
    (correction_pos hw.continuous hpos hanti ht (hw.differentiable (by simp) t)).ne'

theorem localTwist_pos {n : ℕ} {w : ℝ → ℝ} (hw : Continuous w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) {Ψ : ComplexModel n → ℝ} {z : ComplexModel n}
    (hz : Ψ z < 0) : 0 < localTwist w Ψ z := twist_pos hw hpos (neg_pos.mpr hz)

theorem localCorrection_pos {n : ℕ} {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) (hanti : AntitoneOn w (Ici 0))
    {Ψ : ComplexModel n → ℝ} {z : ComplexModel n} (hz : Ψ z < 0) :
    0 < localCorrection w Ψ z :=
  inv_pos.mpr (correction_pos hw.continuous hpos hanti (neg_pos.mpr hz) (hw.differentiable (by simp) _))

theorem contDiffAt_localTwist {n : ℕ} {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) {Ψ : ComplexModel n → ℝ} {z : ComplexModel n}
    (hΨ : ContDiffAt ℝ ∞ Ψ z) (hz : Ψ z < 0) :
    ContDiffAt ℝ ∞ (localTwist w Ψ) z :=
  (contDiffAt_twist hw hpos (neg_pos.mpr hz)).comp z hΨ.neg

theorem contDiffAt_localCorrection {n : ℕ} {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) (hanti : AntitoneOn w (Ici 0))
    {Ψ : ComplexModel n → ℝ} {z : ComplexModel n}
    (hΨ : ContDiffAt ℝ ∞ Ψ z) (hz : Ψ z < 0) :
    ContDiffAt ℝ ∞ (localCorrection w Ψ) z := by
  have h := (contDiffAt_inverse_correction hw hpos hanti (neg_pos.mpr hz)).comp z hΨ.neg
  exact h

theorem contDiffAt_localWeight {n : ℕ} {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) {Ψ p : ComplexModel n → ℝ} {z : ComplexModel n}
    (hΨ : ContDiffAt ℝ ∞ Ψ z) (hp : ContDiffAt ℝ ∞ p z) (hz : Ψ z < 0) :
    ContDiffAt ℝ ∞ (localWeight w Ψ p) z := by
  have h := (contDiffAt_potential hw hpos (neg_pos.mpr hz)).comp z hΨ.neg
  exact hp.add h

theorem exists_common_positive_band_bounds {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) (hanti : AntitoneOn w (Ici 0))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ m M : ℝ, 0 < m ∧ ∀ t ∈ Icc a b,
      m ≤ twist w t ∧ twist w t ≤ M ∧ m ≤ (correction w t)⁻¹ ∧ (correction w t)⁻¹ ≤ M := by
  have hs : ContinuousOn (twist w) (Icc a b) := fun t ht =>
    (contDiffAt_twist hw hpos (ha.trans_le ht.1)).continuousAt.continuousWithinAt
  have hc : ContinuousOn (fun t => (correction w t)⁻¹) (Icc a b) := fun t ht =>
    (contDiffAt_inverse_correction hw hpos hanti (ha.trans_le ht.1)).continuousAt.continuousWithinAt
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) (hs.inf hc)
  obtain ⟨t₁, ht₁, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) (hs.sup hc)
  refine ⟨min (twist w t₀) (correction w t₀)⁻¹, max (twist w t₁) (correction w t₁)⁻¹,
    lt_min (twist_pos hw.continuous hpos (ha.trans_le ht₀.1))
      (inv_pos.mpr (correction_pos hw.continuous hpos hanti (ha.trans_le ht₀.1)
        (hw.differentiable (by simp) _))), ?_⟩
  intro t ht
  refine ⟨(hmin ht).trans (min_le_left _ _), (le_max_left _ _).trans (hmax ht),
    (hmin ht).trans (min_le_right _ _), (le_max_right _ _).trans (hmax ht)⟩


end SGPT.Trace.OptimalExtensionCurvature
