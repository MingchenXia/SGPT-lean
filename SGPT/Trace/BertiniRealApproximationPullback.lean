import SGPT.Trace.BertiniGlobalRealApproximation
import SGPT.Trace.BertiniRelativeBasePositivity
import SGPT.Foundations.Analysis.Pending.SubmanifoldRestrictionPositivity

/-!
# Actual native pencil pullback of the manufactured original real approximation

All weights and their uniform native pulled-X Levi bound are PRODUCED from
original genuine qpsh data, before choosing the auxiliary ample metric.
The original dd-c / pi convention is retained exactly.
Blueprint: work/sgpt-resume-20261114/bert-e2-real-pullback/blueprint/bert-e2-real-pullback.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.BertiniRealApproximationPullback
open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses HolomorphicMaps
open ManifoldTubePositivity SubmanifoldRestrictionPositivity PositivityPerturbation
open ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Trace.BertiniGlobalRealApproximation SGPT.Trace.BertiniRelativeBasePositivity
open SGPT.Trace.BertiniNormalMetric SGPT.Trace.BertiniPencilFamily
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace SGPT.Trace.Bertini

/-- Actual closed-form pullback homogeneity, including off-target coefficients. -/
theorem closed_pullback_smul {n k : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [ChartedSpace (ComplexModel k) Y] [IsComplexManifold k Y]
    {q : Y → X} (hq : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ q)
    (C : ℝ) (α : ClosedRealOneOneForm n X) :
    ClosedRealOneOneForm.pullback hq (C • α) = C • ClosedRealOneOneForm.pullback hq α := by
  apply ClosedRealOneOneForm.ext
  intro c z
  ext w
  rfl

theorem original_smooth_psh_pullback_levi_lower {n k : ℕ} {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [ChartedSpace (ComplexModel k) Y] [IsComplexManifold k Y]
    (omega : KahlerBackground n X) {q : Y → X}
    (hq : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ q)
    {u : X → ℝ} (hu : ChartSmooth (n := n) u) {C : ℝ}
    (hpsh : IsThetaPshPotential (C • omega.form).val (fun x => (u x : EReal)))
    (c : ComplexChart k Y) {z : ComplexModel k} (hz : z ∈ c.val.target) (w : ComplexModel k) :
    0 ≤ C * (SmoothRealForm.pullback hq omega.form.val).coeff c z ![w, Complex.I • w] +
      leviForm (fun y => u (q (c.val.symm y))) z w / Real.pi := by
  have hA : (C • omega.form + ddcClosedForm u hu).val.IsSemipositive := by
    intro d y hy v
    have h := (LocalPotentials.thetaPlurisubharmonic_smooth_iff (C • omega.form) u hu).mp hpsh.1 d y hy v
    simpa only [ClosedRealOneOneForm.coeff_add, ContinuousAlternatingMap.add_apply,
      ddcClosedForm_coeff] using h
  have hP := SmoothRealForm.IsSemipositive.pullback hq hA c z hz w
  change 0 ≤ (ClosedRealOneOneForm.pullback hq
    (C • omega.form + ddcClosedForm u hu)).val.coeff c z ![w, Complex.I • w] at hP
  rw [closed_pullback_add, closed_pullback_smul] at hP
  change 0 ≤ C * (SmoothRealForm.pullback hq omega.form.val).coeff c z ![w, Complex.I • w] +
    (SmoothRealForm.pullback hq (ddcClosedForm u hu).val).coeff c z ![w, Complex.I • w] at hP
  rw [pullback_ddcClosedForm_coeff hq hu c hz] at hP
  change 0 ≤ C * (SmoothRealForm.pullback hq omega.form.val).coeff c z ![w, Complex.I • w] +
    quad ((ddcClosedForm (fun y => u (q y)) (chartSmooth_comp hq hu)).val.coeff c z) w at hP
  rw [quad_ddcClosedForm_coeff (chartSmooth_comp hq hu) c hz w] at hP
  exact hP

variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
  (p : X → ComplexProjectiveSpace N) (i : Fin (N + 1)) (a v : ComplexModel N)
  (U : TopologicalSpace.Opens (ComplexModel 1))

theorem exists_actual_native_pencil_real_weights
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val))
    (omega : KahlerBackground n X) (φ : X → EReal) (hφ : IsGlobalQuasiPshPotential (n := n) φ) :
    letI := familyChartedSpace p i a v U hp hsm
    haveI := isComplexManifold_family p i a v U hp hsm
    ∃ (C : ℝ) (w : ℕ → familyIncidence p i a v U → ℝ), 0 < C ∧
      (∀ j, ChartSmooth (n := n) (w j)) ∧ (∀ q, Antitone (fun j => w j q)) ∧
      (∀ j q, φ q.val.2 ≤ (w j q : EReal)) ∧
      (∀ q, Tendsto (fun j => (w j q : EReal)) atTop (𝓝 (φ q.val.2))) ∧
      ∀ j (c : ComplexChart n (familyIncidence p i a v U)) (z : ComplexModel n), z ∈ c.val.target →
        ∀ b : ComplexModel n, -(Real.pi * C) * familyXQuad p i a v U hp hsm omega c z b ≤
          leviForm (fun y => w j (c.val.symm y)) z b := by
  let := familyChartedSpace p i a v U hp hsm
  have := isComplexManifold_family p i a v U hp hsm
  obtain ⟨C, u, hC, hu, hanti, hdom, hlim, hpsh⟩ := exists_original_global_qpsh_real_approximation omega φ hφ
  have hq := contMDiff_snd.comp (contMDiff_familyInclusion p i a v U hp hsm)
  let w : ℕ → familyIncidence p i a v U → ℝ := fun j q => u j q.val.2
  refine ⟨C, w, hC, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact chartSmooth_comp hq (hu j)
  · intro q
    exact hanti q.val.2
  · intro j q
    exact hdom j q.val.2
  · intro q
    exact hlim q.val.2
  · intro j c z hz b
    have h := original_smooth_psh_pullback_levi_lower omega hq (hu j) (hpsh j) c hz b
    change 0 ≤ C * familyXQuad p i a v U hp hsm omega c z b +
      leviForm (fun y => w j (c.val.symm y)) z b / Real.pi at h
    have hπ := mul_nonneg Real.pi_pos.le h
    rw [mul_add, mul_div_cancel₀ _ Real.pi_ne_zero] at hπ
    nlinarith

end SGPT.Trace.BertiniRealApproximationPullback
