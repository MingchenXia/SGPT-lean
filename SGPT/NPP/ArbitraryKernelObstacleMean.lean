import SGPT.NPP.SourceEnvelopeRadiusMinimum
import SGPT.NPP.ContactRadialSmoothing

/-!
# Genuine weak-obstacle-Hessian means for the same arbitrary radial kernel

Complete blueprint: `blueprint/src/dnt-big-arbitrary-kernel-obstacle.tex`,
written first. Actual weak Hessian positivity produces the comparison PSH
function. Its actual radial submean gives the quadratic obstacle mean bound
for the same arbitrary smooth radial kernel, with no semiconcavity assumption.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace SGPT.NPP.DNTBig

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HolomorphicPullback
open SGPT.Foundations.Analysis.Pending.PshRadialRegularization
open SGPT.Envelopes.DNTC11
open SGPT.Okounkov.TranscendentalWNReg
open SGPT.Analysis.CZ

variable {n : ℕ}

/-- The actual weak obstacle Hessian produces the actual centered quadratic
PSH comparison uniformly on the buffered chart ball. -/
theorem exists_centered_quadratic_sub_obstacle_psh
    {q : ComplexModel n → ℝ} {H : ComplexModel n → Matrix (Fin n) (Fin n) ℂ}
    {Ω : Set (ComplexModel n)} (hq : IsBoundedHessianDensityOn q H Ω)
    {c : ComplexModel n} {a : ℝ} (hball : closedBall c (4 * a) ⊆ Ω) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ComplexModel n,
      PlurisubharmonicOn (fun x => ((M * ‖x - y‖ ^ 2 + (-1) * q x : ℝ) : EReal))
        (ball c (4 * a)) := by
  let W : Set (ComplexModel n) := ball c (4 * a)
  have hWΩ : W ⊆ Ω := ball_subset_closedBall.trans hball
  obtain ⟨M, hM0, hM⟩ := hq.exists_ae_abs_hermQuad_le (isCompact_closedBall c (4 * a)) hball
  have hMW : ∀ᵐ x ∂(volume.restrict W), ∀ v, |hermQuad (H x) v| ≤ M * ‖v‖ ^ 2 :=
    ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall hM
  refine ⟨M, hM0, fun y => ?_⟩
  have hsq : ContDiffOn ℝ ∞ (fun x : ComplexModel n => ‖x - y‖ ^ 2) W :=
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).contDiffOn
  have hkd := ((isBoundedHessianDensityOn_of_contDiffOn isOpen_ball hsq).smul M).add
    ((hq.mono isOpen_ball hWΩ).smul (-1))
  refine plurisubharmonicOn_of_hermQuad_nonneg hkd fun v => ?_
  filter_upwards [hMW, ae_restrict_mem isOpen_ball.measurableSet] with x hx hxW
  rw [hermQuad_add, hermQuad_smul, hermQuad_smul]
  have hsmooth : smoothHess W (fun x : ComplexModel n => ‖x - y‖ ^ 2) x = 1 := by
    have hxWW : x ∈ W := hxW
    rw [smoothHess, if_pos hxWW]
    exact SGPT.Okounkov.TranscendentalWN.EnvelopeLocal.complexHessian_norm_sub_sq y x
  rw [hsmooth, hermQuad_one]
  have hh := hx v
  have hu := le_abs_self (hermQuad (H x) v)
  linarith

/-- An actual weak obstacle Hessian gives the quadratic mean bound for the
same arbitrary radial kernel, by actual PSH submean and the actual second moment. -/
theorem radialRegularization_sub_le_of_boundedDensity
    {ρ : ComplexModel n → ℝ} (hρ : IsRadialKernel ρ)
    {q : ComplexModel n → ℝ} {H : ComplexModel n → Matrix (Fin n) (Fin n) ℂ}
    {Ω : Set (ComplexModel n)} (hq : IsBoundedHessianDensityOn q H Ω)
    {c : ComplexModel n} {a : ℝ} (_ha : 0 < a)
    (hball : closedBall c (4 * a) ⊆ Ω) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ ball c (2 * a), ∀ r : ℝ, 0 < r → r < a →
      radialRegularization ρ (fun x => (q x : EReal)) r y - q y ≤ M * r ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := exists_centered_quadratic_sub_obstacle_psh hq hball
  refine ⟨M, hM0, fun y hy r hr hra => ?_⟩
  let W : Set (ComplexModel n) := ball c (4 * a)
  have hWΩ : W ⊆ Ω := ball_subset_closedBall.trans hball
  have hyW : y ∈ W := ball_subset_ball (by linarith) hy
  have hyInner : y ∈ innerDomain W r := by
    refine ⟨2 * a, by linarith, ?_⟩
    intro x hx
    rw [mem_ball] at hx hy ⊢
    exact (dist_triangle x y c).trans_lt (by linarith)
  let κ : ComplexModel n → ℝ := fun x => scaledKernel ρ r (x - y)
  have hκc : Continuous κ :=
    (contDiff_scaledKernel hρ r).continuous.comp (continuous_id.sub continuous_const)
  have hκs : HasCompactSupport κ :=
    (hasCompactSupport_scaledKernel hρ hr).comp_homeomorph (Homeomorph.subRight y)
  have hκball : tsupport κ ⊆ closedBall y r := tsupport_scaledKernel_translate_subset hρ hr y
  have hκW : tsupport κ ⊆ W := by
    intro x hx
    have hxy : dist x y ≤ r := hκball hx
    have hyc : dist y c < 2 * a := hy
    change dist x c < 4 * a
    have ht := dist_triangle x y c
    linarith
  have hκn : ∀ x, 0 ≤ κ x := fun x => scaledKernel_nonneg hρ hr _
  have hκI : Integrable κ := hκc.integrable_of_hasCompactSupport hκs
  have hκone : ∫ x, κ x = 1 := by
    rw [show κ = fun x => scaledKernel ρ r (x - y) from rfl,
      integral_sub_right_eq_self]
    exact integral_scaledKernel hρ hr
  have hqI : Integrable (fun x => q x * κ x) :=
    integrable_mul_of_continuousOn isOpen_ball (hq.continuousOn.mono hWΩ) hκc hκs hκW
  have hsI : Integrable (fun x : ComplexModel n => ‖x - y‖ ^ 2 * κ x) :=
    integrable_mul_of_continuousOn isOpen_univ (by fun_prop) hκc hκs (subset_univ _)
  have hmoment : (∫ x : ComplexModel n, ‖x - y‖ ^ 2 * κ x) ≤ r ^ 2 := by
    have hh := integral_mono hsI (hκI.const_mul (r ^ 2)) (fun x => by
      by_cases hx : x ∈ tsupport κ
      · have hxy : ‖x - y‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hκball hx
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hxy 2) (hκn x)
      · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero])
    simpa only [integral_const_mul, hκone, mul_one] using hh
  let k : ComplexModel n → ℝ := fun x => M * ‖x - y‖ ^ 2 + (-1) * q x
  have hkpsh : PlurisubharmonicOn (fun x => (k x : EReal)) W := hM y
  have hne : ∃ x ∈ W, (k x : EReal) ≠ ⊥ := ⟨y, hyW, EReal.coe_ne_bot _⟩
  have hsub := le_radialRegularization hρ isOpen_ball (convex_ball c (4 * a)).isPreconnected
    hkpsh hne hr hyInner
  rw [radialRegularization_eq_translationPairing hρ] at hsub
  have hsub' : -q y ≤ ∫ x, k x * κ x := by
    have hh := EReal.coe_le_coe_iff.mp hsub
    simpa only [k, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
      zero_add, neg_one_mul, translationPairing, EReal.toReal_coe] using hh
  have hkmean : (∫ x, k x * κ x) =
      M * (∫ x : ComplexModel n, ‖x - y‖ ^ 2 * κ x) - ∫ x, q x * κ x := by
    have heq : (fun x => k x * κ x) =
        fun x => M * (‖x - y‖ ^ 2 * κ x) - q x * κ x := by
      funext x
      dsimp only [k]
      ring
    rw [heq, integral_sub (hsI.const_mul M) hqI, integral_const_mul]
  rw [hkmean] at hsub'
  rw [radialRegularization_eq_translationPairing hρ]
  simp only [translationPairing, EReal.toReal_coe]
  have hweighted := mul_le_mul_of_nonneg_left hmoment hM0
  change (∫ x, q x * κ x) - q y ≤ M * r ^ 2
  linarith

/-- The same actual positive kernel compares a finite PSH function dominated
by the weak-Hessian obstacle, deriving the actual obstacle mean domination. -/
theorem radialRegularization_le_obstacle_of_boundedDensity
    {ρ : ComplexModel n → ℝ} (hρ : IsRadialKernel ρ)
    {q : ComplexModel n → ℝ} {H : ComplexModel n → Matrix (Fin n) (Fin n) ℂ}
    {Ω : Set (ComplexModel n)} (hq : IsBoundedHessianDensityOn q H Ω)
    {u : ComplexModel n → EReal} (hu : PlurisubharmonicOn u Ω)
    (huf : ∀ x ∈ Ω, u x ≠ ⊥) (huq : ∀ x ∈ Ω, u x ≤ (q x : EReal))
    {c : ComplexModel n} {a : ℝ} (ha : 0 < a)
    (hball : closedBall c (4 * a) ⊆ Ω) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ ball c (2 * a), ∀ r : ℝ, 0 < r → r < a →
      radialRegularization ρ u r y ≤ q y + M * r ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := radialRegularization_sub_le_of_boundedDensity hρ hq ha hball
  have hureal : PlurisubharmonicOn (fun x => ((u x).toReal : EReal)) Ω := by
    intro x hx
    apply (hu x hx).congr
    filter_upwards [hq.isOpen.mem_nhds hx] with y hy
    exact (EReal.coe_toReal (hu y hy).ne_top (huf y hy)).symm
  have huL := locallyIntegrableOn_of_plurisubharmonicOn_real (Ω := ⟨Ω, hq.isOpen⟩) hureal
  refine ⟨M, hM0, fun y hy r hr hra => ?_⟩
  let κ : ComplexModel n → ℝ := fun x => scaledKernel ρ r (x - y)
  have hκc : Continuous κ :=
    (contDiff_scaledKernel hρ r).continuous.comp (continuous_id.sub continuous_const)
  have hκs : HasCompactSupport κ :=
    (hasCompactSupport_scaledKernel hρ hr).comp_homeomorph (Homeomorph.subRight y)
  have hκΩ : tsupport κ ⊆ Ω := by
    intro x hx
    apply hball
    have hxy : dist x y ≤ r := tsupport_scaledKernel_translate_subset hρ hr y hx
    have hyc : dist y c < 2 * a := hy
    change dist x c ≤ 4 * a
    have ht := dist_triangle x y c
    linarith
  have huOn : IntegrableOn (fun x => (u x).toReal) (tsupport κ) :=
    (huL.mono_set hκΩ).integrableOn_isCompact hκs
  have huI : Integrable (fun x => (u x).toReal * κ x) :=
    (huOn.mul_continuousOn hκc.continuousOn hκs).integrable_of_forall_notMem_eq_zero
      fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hqI : Integrable (fun x => q x * κ x) :=
    integrable_mul_of_continuousOn hq.isOpen hq.continuousOn hκc hκs hκΩ
  have hcompare : radialRegularization ρ u r y ≤
      radialRegularization ρ (fun x => (q x : EReal)) r y := by
    rw [radialRegularization_eq_translationPairing hρ,
      radialRegularization_eq_translationPairing hρ]
    simp only [translationPairing, EReal.toReal_coe]
    apply integral_mono_ae huI hqI
    exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ tsupport κ
      · have hreal : (u x).toReal ≤ q x := by
          have hh := EReal.toReal_le_toReal (huq x (hκΩ hx)) (huf x (hκΩ hx))
            (EReal.coe_ne_top _)
          simpa only [EReal.toReal_coe] using hh
        exact mul_le_mul_of_nonneg_right hreal (scaledKernel_nonneg hρ hr _)
      · change (u x).toReal * κ x ≤ q x * κ x
        rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]
  have hh := hM y hy r hr hra
  linarith

end SGPT.NPP.DNTBig
