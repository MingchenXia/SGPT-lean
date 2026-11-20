import SGPT.Trace.OTExt5Curv
import SGPT.Trace.OTExt4Step5

/-!
# The cut-off extension `G_ε = ρ(R/ε) G` and the densities of its `∂̄`

Blueprint `claude-ot-ext5.tex`, node `claude-ot-ext5:data`.  Xia, *Foundations of pluripotential
theory*, q07, proof of `thm:compact-submanifold-extension`, Step 2.

For the glued extension `G` of `lem:critical-gain-initial-gluing` and the cut-off profile
`ρ(t) = θ(2t)` (`θ = cutoffProfile`; `ρ = 1` on `t ≤ 1/2`, `ρ = 0` on `t ≥ 1`), put
`G_ε = ρ(R/ε) G` (`cutSec`).  Its `∂̄` splits as `g^{(1)} + g^{(2)}`,
`g^{(1)} = ∂̄ρ(R/ε) · G` and `g^{(2)} = ρ(R/ε) ∂̄G` (`dbarPairing_cutSec`), and

* `holDerivSq_cutR_le`: `|∂ρ(R/ε)(v)|² ≤ (2B/ε)² 1_{ε/2 ≤ R ≤ ε} |∂R(v)|²` (`B` bounds `|θ'|`);
* `holDerivSq_cutR_le_twisted`: `|∂ρ(R/ε)(v)|² ≤ 16 B² 1_{ε/2 ≤ R ≤ ε} H` whenever
  `(ε/R)|∂ψ_ε(v)|² ≤ H` (the rank-one part of `eq:global-normal-twisted-curvature`), since
  `|∂R|² = (ε + R)² |∂ψ_ε|²` and `R ≤ ε` on the shell;
* `dbar_cutSec_le`: `|⟨∂̄G_ε, v⟩|² ≤ 2 |∂ρ(R/ε)(v)|² |G|² + 2 ρ(R/ε)² D_G ω(v, iv)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTExt5

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open SGPT.Trace.TwistedL2

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-! ### The cut-off -/

/-- The profile `t ↦ θ(2t/ε)` of the cut-off `ρ(R/ε)`. -/
def cutProfile (ε t : ℝ) : ℝ := TwistedL2.cutoffProfile (2 * t / ε)

/-- The cut-off `ρ(R/ε) = θ(2R/ε)`: `1` on `{R ≤ ε/2}`, `0` on `{R ≥ ε}`. -/
def cutR (ε : ℝ) (R : X → ℝ) (x : X) : ℝ := cutProfile ε (R x)

/-- The shell `{ε/2 ≤ R ≤ ε}`. -/
def shell (ε : ℝ) (R : X → ℝ) : Set X := {x | ε / 2 ≤ R x ∧ R x ≤ ε}

theorem contDiff_cutProfile (ε : ℝ) : ContDiff ℝ ∞ (cutProfile ε) :=
  contDiff_cutoffProfile.comp ((contDiff_const.mul contDiff_id).div_const ε)

theorem cutR_nonneg (ε : ℝ) (R : X → ℝ) (x : X) : 0 ≤ cutR ε R x := cutoffProfile_nonneg _

theorem cutR_le_one (ε : ℝ) (R : X → ℝ) (x : X) : cutR ε R x ≤ 1 := cutoffProfile_le_one _

theorem cutR_eq_one {ε : ℝ} (hε : 0 < ε) {R : X → ℝ} {x : X} (hx : R x ≤ ε / 2) :
    cutR ε R x = 1 := by
  refine cutoffProfile_eq_one ?_
  rw [div_le_one hε]; linarith

theorem cutR_eq_zero {ε : ℝ} (hε : 0 < ε) {R : X → ℝ} {x : X} (hx : ε ≤ R x) :
    cutR ε R x = 0 := by
  refine cutoffProfile_eq_zero ?_
  rw [le_div_iff₀ hε]; linarith

theorem cutR_sq_le_indicator {ε : ℝ} (hε : 0 < ε) (R : X → ℝ) (x : X) :
    cutR ε R x ^ 2 ≤ {x | R x < ε}.indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : R x < ε
  · rw [indicator_of_mem (show x ∈ {x | R x < ε} from hx)]
    nlinarith [cutR_nonneg ε R x, cutR_le_one ε R x]
  · rw [indicator_of_notMem (show x ∉ {x | R x < ε} from hx), cutR_eq_zero hε (not_lt.mp hx)]
    norm_num

theorem deriv_cutProfile {ε : ℝ} (t : ℝ) :
    deriv (cutProfile ε) t = deriv TwistedL2.cutoffProfile (2 * t / ε) * (2 / ε) := by
  have h1 : HasDerivAt (fun s : ℝ => 2 * s / ε) (2 / ε) t := by
    simpa [mul_div_assoc] using (hasDerivAt_id t).const_mul (2 / ε) |>.congr_deriv (by ring)
      |>.congr_of_eventuallyEq (Eventually.of_forall fun s => by simp; ring)
  have h2 : HasDerivAt TwistedL2.cutoffProfile
      (deriv TwistedL2.cutoffProfile (2 * t / ε)) (2 * t / ε) :=
    (contDiff_cutoffProfile.differentiable (by simp) _).hasDerivAt
  exact (h2.comp t h1).deriv

theorem deriv_cutProfile_eq_zero {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : t ∉ Icc (ε / 2) ε) :
    deriv (cutProfile ε) t = 0 := by
  rw [deriv_cutProfile, deriv_cutoffProfile_eq_zero, zero_mul]
  intro h
  apply ht
  obtain ⟨h1, h2⟩ := h
  rw [le_div_iff₀ hε] at h1
  rw [div_le_iff₀ hε] at h2
  exact ⟨by linarith, by linarith⟩

theorem abs_deriv_cutProfile_le {ε : ℝ} (hε : 0 < ε) {B : ℝ}
    (hB : ∀ t, |deriv TwistedL2.cutoffProfile t| ≤ B) (t : ℝ) :
    |deriv (cutProfile ε) t| ≤ B * (2 / ε) := by
  rw [deriv_cutProfile, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / ε)]
  exact mul_le_mul_of_nonneg_right (hB _) (by positivity)

theorem chartSmooth_cutR {ε : ℝ} {R : X → ℝ} (hR : ChartSmooth (n := n) R) :
    ChartSmooth (n := n) (cutR ε R) := fun c =>
  (contDiff_cutProfile ε).comp_contDiffOn (hR c)

/-- **The cut-off derivative**: `|∂ρ(R/ε)(v)|² = ρ'(R/ε)² |∂R(v)|²`, which vanishes off the shell
and is at most `(2B/ε)² |∂R(v)|²` on it. -/
theorem holDerivSq_cutR_le {ε : ℝ} (hε : 0 < ε) {B : ℝ}
    (hB : ∀ t, |deriv TwistedL2.cutoffProfile t| ≤ B) {R : X → ℝ} (hR : ChartSmooth (n := n) R)
    (c : ComplexChart n X) {z : ComplexModel n} (hz : z ∈ c.val.target) (v : ComplexModel n) :
    holDerivSq (fun y => cutR ε R (c.val.symm y)) z v ≤
      (shell ε R).indicator (fun _ => (B * (2 / ε)) ^ 2) (c.val.symm z) *
        holDerivSq (fun y => R (c.val.symm y)) z v := by
  have hRd : DifferentiableAt ℝ (fun y => R (c.val.symm y)) z :=
    ((hR c).contDiffAt (c.val.open_target.mem_nhds hz)).differentiableAt (by simp)
  have hθd : DifferentiableAt ℝ (cutProfile ε) (R (c.val.symm z)) :=
    (contDiff_cutProfile ε).differentiable (by simp) _
  rw [show (fun y => cutR ε R (c.val.symm y)) = fun y => cutProfile ε (R (c.val.symm y)) from rfl,
    holDerivSq_comp hθd hRd v]
  have hH := holDerivSq_nonneg (fun y => R (c.val.symm y)) z v
  by_cases hs : c.val.symm z ∈ shell ε R
  · rw [indicator_of_mem hs]
    refine mul_le_mul_of_nonneg_right ?_ hH
    have h := abs_deriv_cutProfile_le hε hB (R (c.val.symm z))
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  · rw [indicator_of_notMem hs, deriv_cutProfile_eq_zero hε hs]
    simp

/-- `|∂R(v)|² = (ε + R)² |∂ log(ε + R)(v)|²`. -/
theorem holDerivSq_eq_log {ε : ℝ} (hε : 0 < ε) {R : ComplexModel n → ℝ} {z : ComplexModel n}
    (hR0 : 0 ≤ R z) (hRd : DifferentiableAt ℝ R z) (v : ComplexModel n) :
    holDerivSq R z v = (ε + R z) ^ 2 * holDerivSq (fun y => Real.log (ε + R y)) z v := by
  have hpos : 0 < ε + R z := by linarith
  have hθ : DifferentiableAt ℝ (fun t => Real.log (ε + t)) (R z) :=
    ((differentiableAt_const _).add differentiableAt_id).log hpos.ne'
  rw [show (fun y => Real.log (ε + R y)) = fun y => (fun t => Real.log (ε + t)) (R y) from rfl,
    holDerivSq_comp hθ hRd v]
  have hd : deriv (fun t => Real.log (ε + t)) (R z) = (ε + R z)⁻¹ := by
    have := ((hasDerivAt_id (R z)).const_add ε).log hpos.ne'
    simpa using this.deriv
  rw [hd, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hpos.ne', one_pow, one_mul]

/-- **The rank-one bound against the twisted curvature**: on the shell, where `R ≤ ε`,
`|∂ρ(R/ε)(v)|² ≤ 16 B² H` whenever `(ε/R)|∂ψ_ε(v)|² ≤ H`. -/
theorem holDerivSq_cutR_le_twisted {ε : ℝ} (hε : 0 < ε) {B : ℝ}
    (hB : ∀ t, |deriv TwistedL2.cutoffProfile t| ≤ B) {R : X → ℝ} (hR : ChartSmooth (n := n) R)
    (hR0 : ∀ x, 0 ≤ R x) (c : ComplexChart n X) {z : ComplexModel n} (hz : z ∈ c.val.target)
    (hRz : 0 < R (c.val.symm z)) (v : ComplexModel n) {H : ℝ}
    (hH : ε / R (c.val.symm z) * holDerivSq (fun y => Real.log (ε + R (c.val.symm y))) z v ≤ H) :
    holDerivSq (fun y => cutR ε R (c.val.symm y)) z v ≤
      (shell ε R).indicator (fun _ => 16 * B ^ 2) (c.val.symm z) * H := by
  refine (holDerivSq_cutR_le hε hB hR c hz v).trans ?_
  have hRd : DifferentiableAt ℝ (fun y => R (c.val.symm y)) z :=
    ((hR c).contDiffAt (c.val.open_target.mem_nhds hz)).differentiableAt (by simp)
  by_cases hs : c.val.symm z ∈ shell ε R
  · rw [indicator_of_mem hs, indicator_of_mem hs, holDerivSq_eq_log hε (hR0 _) hRd v]
    set r := R (c.val.symm z)
    set D := holDerivSq (fun y => Real.log (ε + R (c.val.symm y))) z v
    have hD : 0 ≤ D := holDerivSq_nonneg _ _ _
    have hrε : r ≤ ε := hs.2
    -- `D ≤ (r/ε) H ≤ H`
    have hDH : D ≤ H := by
      have h1 : D ≤ r / ε * H := by
        have : ε / r * D ≤ H := hH
        rw [div_mul_eq_mul_div, div_le_iff₀ hRz] at this
        rw [div_mul_eq_mul_div, le_div_iff₀ hε]
        linarith
      have hH0 : 0 ≤ H := le_trans (mul_nonneg (by positivity) hD) hH
      have : r / ε * H ≤ H := by
        have : r / ε ≤ 1 := (div_le_one hε).mpr hrε
        nlinarith
      linarith
    have hH0 : 0 ≤ H := le_trans hD hDH
    have h2 : (B * (2 / ε)) ^ 2 * ((ε + r) ^ 2 * D) = 4 * B ^ 2 * ((ε + r) / ε) ^ 2 * D := by
      field_simp; ring
    rw [h2]
    have h3 : ((ε + r) / ε) ^ 2 ≤ 4 := by
      have : (ε + r) / ε ≤ 2 := by rw [div_le_iff₀ hε]; linarith
      have : 0 ≤ (ε + r) / ε := by positivity
      nlinarith
    calc 4 * B ^ 2 * ((ε + r) / ε) ^ 2 * D ≤ 4 * B ^ 2 * 4 * D := by
          gcongr
      _ ≤ 16 * B ^ 2 * H := by nlinarith [sq_nonneg B]
  · rw [indicator_of_notMem hs, indicator_of_notMem hs, zero_mul, zero_mul]

/-! ### The section `G_ε` -/

section Section

variable (V : HermitianHolomorphicLineBundle.{0, 0} n X)

/-- `G_ε = ρ(R/ε) G`. -/
def cutSec (ε : ℝ) (R : X → ℝ) (G : (x : X) → V.Fiber x) : (x : X) → V.Fiber x :=
  fun x => ((cutR ε R x : ℝ) : ℂ) • G x

theorem chartCoeff_cutSec_eventuallyEq (ε : ℝ) (R : X → ℝ) (G : (x : X) → V.Fiber x)
    (c : ComplexChart n X) (e : AtlasFrame V) {z : ComplexModel n}
    (hz : z ∈ chartFrameDomain V c e) :
    chartCoeff V c e (cutSec V ε R G) =ᶠ[𝓝 z]
      fun y => ((cutR ε R (c.val.symm y) : ℝ) : ℂ) * chartCoeff V c e G y := by
  filter_upwards [(isOpen_chartFrameDomain V c e).mem_nhds hz] with y hy
  exact frameCoeff_smul_apply e hy.2 _ _

theorem isSmoothSectionOn_cutSec {ε : ℝ} {R : X → ℝ} (hR : ChartSmooth (n := n) R)
    {G : (x : X) → V.Fiber x} (hG : IsSmoothSectionOn V G univ) :
    IsSmoothSectionOn V (cutSec V ε R G) univ := by
  intro c e z hz
  have hz' : z ∈ chartFrameDomain V c e := hz.1
  refine ContDiffAt.contDiffWithinAt ?_
  refine ContDiffAt.congr_of_eventuallyEq ?_ (chartCoeff_cutSec_eventuallyEq V ε R G c e hz')
  refine (Complex.ofRealCLM.contDiff.contDiffAt.comp z
    ((chartSmooth_cutR hR c).contDiffAt (c.val.open_target.mem_nhds hz'.1))).mul ?_
  have hO : IsOpen (chartFrameDomain V c e ∩ c.val.symm ⁻¹' univ) := by
    rw [preimage_univ, inter_univ]; exact isOpen_chartFrameDomain V c e
  exact (hG c e).contDiffAt (hO.mem_nhds hz)

/-- **The splitting of `∂̄G_ε`**: `⟨∂̄G_ε, v⟩ = ⟨∂̄ρ(R/ε), v⟩ G + ρ(R/ε) ⟨∂̄G, v⟩` in coefficients. -/
theorem dbarPairing_cutSec {ε : ℝ} {R : X → ℝ} (hR : ChartSmooth (n := n) R)
    {G : (x : X) → V.Fiber x} (hG : IsSmoothSectionOn V G univ) (c : ComplexChart n X)
    (e : AtlasFrame V) {z : ComplexModel n} (hz : z ∈ chartFrameDomain V c e)
    (v : ComplexModel n) :
    dbarPairing (chartCoeff V c e (cutSec V ε R G)) z v =
      dbarPairing (fun y => ((cutR ε R (c.val.symm y) : ℝ) : ℂ)) z v * chartCoeff V c e G z +
        ((cutR ε R (c.val.symm z) : ℝ) : ℂ) * dbarPairing (chartCoeff V c e G) z v := by
  have hcd : DifferentiableAt ℝ (fun y => ((cutR ε R (c.val.symm y) : ℝ) : ℂ)) z :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp z ((chartSmooth_cutR hR c).contDiffAt
      (c.val.open_target.mem_nhds hz.1))).differentiableAt (by simp)
  have hO : IsOpen (chartFrameDomain V c e ∩ c.val.symm ⁻¹' univ) := by
    rw [preimage_univ, inter_univ]; exact isOpen_chartFrameDomain V c e
  have hgd : DifferentiableAt ℝ (chartCoeff V c e G) z :=
    ((hG c e).contDiffAt (hO.mem_nhds ⟨hz, trivial⟩)).differentiableAt (by simp)
  rw [dbarPairing_eq_dbarDir, dbarDir_congr_of_eventuallyEq
    (chartCoeff_cutSec_eventuallyEq V ε R G c e hz), dbarDir_mul hcd hgd,
    dbarPairing_eq_dbarDir, dbarPairing_eq_dbarDir]

/-- **The pointwise bound of `|∂̄G_ε|²`**: `|⟨∂̄G_ε, v⟩|²_h ≤ 2 |∂ρ(R/ε)(v)|² |G|² + 2 ρ(R/ε)² D_G ω`
for a bound `D_G` of `|∂̄G|²`. -/
theorem dbar_cutSec_le (ωb : KahlerBackground n X) {ε : ℝ} {R : X → ℝ}
    (hR : ChartSmooth (n := n) R) {G : (x : X) → V.Fiber x} (hG : IsSmoothSectionOn V G univ)
    {Dg : X → ℝ}
    (hDg : ∀ (c : ComplexChart n X) (e : AtlasFrame V), ∀ z ∈ chartFrameDomain V c e,
      ∀ v : ComplexModel n,
        ‖dbarPairing (chartCoeff V c e G) z v‖ ^ 2 * frameNormSq V e (c.val.symm z) ≤
          Dg (c.val.symm z) * kahlerQuad ωb c z v)
    (c : ComplexChart n X) (e : AtlasFrame V) {z : ComplexModel n}
    (hz : z ∈ chartFrameDomain V c e) (v : ComplexModel n) :
    ‖dbarPairing (chartCoeff V c e (cutSec V ε R G)) z v‖ ^ 2 * frameNormSq V e (c.val.symm z) ≤
      2 * (holDerivSq (fun y => cutR ε R (c.val.symm y)) z v * ‖G (c.val.symm z)‖ ^ 2) +
        2 * (cutR ε R (c.val.symm z) ^ 2 * (Dg (c.val.symm z) * kahlerQuad ωb c z v)) := by
  have := e.property
  rw [dbarPairing_cutSec V hR hG c e hz v]
  set a := dbarPairing (fun y => ((cutR ε R (c.val.symm y) : ℝ) : ℂ)) z v * chartCoeff V c e G z
  set b := ((cutR ε R (c.val.symm z) : ℝ) : ℂ) * dbarPairing (chartCoeff V c e G) z v
  have hf : 0 ≤ frameNormSq V e (c.val.symm z) := by unfold frameNormSq; positivity
  have hab : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    have := norm_add_le a b
    nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a + b), sq_nonneg (‖a‖ - ‖b‖)]
  have hcd : DifferentiableAt ℝ (fun y => cutR ε R (c.val.symm y)) z :=
    ((chartSmooth_cutR hR c).contDiffAt (c.val.open_target.mem_nhds hz.1)).differentiableAt
      (by simp)
  have ha : ‖a‖ ^ 2 * frameNormSq V e (c.val.symm z) =
      holDerivSq (fun y => cutR ε R (c.val.symm y)) z v * ‖G (c.val.symm z)‖ ^ 2 := by
    rw [norm_mul, mul_pow, SGPT.Trace.OTExt4.norm_dbarPairing_ofReal_sq hcd v, mul_assoc,
      norm_sq_eq_frameCoeff e hz.2 (G (c.val.symm z))]
    rfl
  have hb : ‖b‖ ^ 2 * frameNormSq V e (c.val.symm z) ≤
      cutR ε R (c.val.symm z) ^ 2 * (Dg (c.val.symm z) * kahlerQuad ωb c z v) := by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hDg c e z hz v) (sq_nonneg _)
  calc ‖a + b‖ ^ 2 * frameNormSq V e (c.val.symm z)
      ≤ (2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2) * frameNormSq V e (c.val.symm z) :=
        mul_le_mul_of_nonneg_right hab hf
    _ = 2 * (‖a‖ ^ 2 * frameNormSq V e (c.val.symm z)) +
          2 * (‖b‖ ^ 2 * frameNormSq V e (c.val.symm z)) := by ring
    _ ≤ _ := by rw [ha]; linarith

end Section

end SGPT.Trace.OTExt5
