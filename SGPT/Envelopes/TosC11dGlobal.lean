import SGPT.Envelopes.TosC11dNormal
import SGPT.Envelopes.TosC11dLocalBound

/-!
# Normal coordinates at the maximum point: the hypotheses of `local_bound`

Lane TOS-C11d (`claude-tos-c11d`, node `tos-c11d:global`).  Source: Xia, *Foundations of
pluripotential theory*, `lem:penalized-real-hessian`, Steps 1–2, for SGPT `thm:Tos_C11` (Tosatti,
Chu–Zhou).

For a chart `e`, a local potential `ρ` of `A` and normal coordinates `Φ` (`exists_normal_frame`), the
potential `ψ = ρ ∘ Φ` satisfies `NormalAt ψ` (`normalAt_of_frame`) and its metric has second and third
derivatives at `0` bounded by the bounds of the coefficients of `Φ^*A` on the real frame
(`metric_jet_bounds`).
-/

set_option autoImplicit false
-- nested spaces of continuous multilinear maps need deeper pending instance synthesis, as in
-- Mathlib's own build configuration
set_option maxSynthPendingDepth 3

noncomputable section

open Filter Set
open scoped Topology ContDiff InnerProductSpace RealInnerProductSpace ComplexConjugate

namespace SGPT.Envelopes.TosC11d

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Analysis.KahlerNormal
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity SGPT.Okounkov.TranscendentalWNReg

/-! ### Evaluation commutes with derivatives -/

section Eval

variable {n : ℕ}

/-- Evaluation `G ↦ G Y Z` of bilinear forms. -/
def evalYZ (Y Z : ComplexModel n) : (ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ Z).comp (ContinuousLinearMap.apply ℝ (ComplexModel n →L[ℝ] ℝ) Y)

theorem evalYZ_apply (Y Z : ComplexModel n) (G : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) :
    evalYZ Y Z G = G Y Z := rfl

theorem fderiv_eval_comp {G : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (hG : Differentiable ℝ G) (Y Z : ComplexModel n) :
    fderiv ℝ (fun x => G x Y Z) = fun x => (evalYZ Y Z).comp (fderiv ℝ G x) := by
  funext x
  exact ((evalYZ Y Z).hasFDerivAt.comp x (hG x).hasFDerivAt).fderiv

/-- Second and third derivatives of `x ↦ G x Y Z`. -/
theorem iter_fderiv_eval {G : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (hG : ContDiff ℝ ∞ G) (Y Z x v w t : ComplexModel n) :
    fderiv ℝ (fderiv ℝ (fun x => G x Y Z)) x v w = fderiv ℝ (fderiv ℝ G) x v w Y Z ∧
      fderiv ℝ (fderiv ℝ (fderiv ℝ (fun x => G x Y Z))) x v w t =
        fderiv ℝ (fderiv ℝ (fderiv ℝ G)) x v w t Y Z := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ G) := hG.fderiv_right (by simp)
  have h2 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ G)) := h1.fderiv_right (by simp)
  have e1 := fderiv_eval_comp (hG.differentiable (by simp)) Y Z
  set L₁ := ContinuousLinearMap.compL ℝ (ComplexModel n) _ ℝ (evalYZ Y Z) with hL₁
  have e1' : fderiv ℝ (fun x => G x Y Z) = fun x => L₁ (fderiv ℝ G x) := e1
  have e2 : fderiv ℝ (fderiv ℝ (fun x => G x Y Z)) = fun x => L₁.comp (fderiv ℝ (fderiv ℝ G) x) := by
    rw [e1']
    funext x
    exact (L₁.hasFDerivAt.comp x ((h1.differentiable (by simp)) x).hasFDerivAt).fderiv
  set L₂ := ContinuousLinearMap.compL ℝ (ComplexModel n) _ _ L₁ with hL₂
  have e2' : fderiv ℝ (fderiv ℝ (fun x => G x Y Z)) =
      fun x => L₂ (fderiv ℝ (fderiv ℝ G) x) := e2
  refine ⟨by rw [e2]; rfl, ?_⟩
  have e3 : fderiv ℝ (fderiv ℝ (fderiv ℝ (fun x => G x Y Z))) =
      fun x => L₂.comp (fderiv ℝ (fderiv ℝ (fderiv ℝ G)) x) := by
    rw [e2']
    funext x
    exact (L₂.hasFDerivAt.comp x ((h2.differentiable (by simp)) x).hasFDerivAt).fderiv
  rw [e3]
  rfl

end Eval

section Normal

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- The metric of `ψ = ρ ∘ Φ` through the pulled back form. -/
theorem metricOf_eq_pullbackField (A : KahlerBackground N Y) {e : ComplexChart N Y}
    {W : Set (ComplexModel N)} {ρ : ComplexModel N → ℝ}
    (hpot : IsSmoothLocalPotential A.form.val e W ρ) {Φ : ComplexModel N → ComplexModel N}
    (hΦ : ContDiff ℂ ∞ Φ) {ψ : ComplexModel N → ℝ} {x : ComplexModel N}
    (hψ : ψ =ᶠ[𝓝 x] fun y => ρ (Φ y)) (hx : Φ x ∈ W) (Yv Zv : ComplexModel N) :
    metricOf ψ x Yv Zv =
      Real.pi * pullbackField Φ (A.form.val.coeff e) x ![Yv, Complex.I • Zv] := by
  rw [metricOf_eq_chartMetric A hpot hΦ hψ hx, pullbackField, compContinuousLinearMap_apply_two,
    fderiv_I_smul hΦ]
  rfl

/-- **The potential in normal coordinates is normalized** (`NormalAt`). -/
theorem normalAt_of_frame (A : KahlerBackground N Y) {e : ComplexChart N Y}
    {W : Set (ComplexModel N)} {ρ : ComplexModel N → ℝ}
    (hpot : IsSmoothLocalPotential A.form.val e W ρ) {Φ : ComplexModel N → ComplexModel N}
    (hΦ : ContDiff ℂ ∞ Φ) {ψ : ComplexModel N → ℝ} (hψs : ContDiff ℝ ∞ ψ)
    (hψ : ∀ᶠ x in 𝓝 (0 : ComplexModel N), ψ =ᶠ[𝓝 x] fun y => ρ (Φ y))
    (hW : ∀ᶠ x in 𝓝 (0 : ComplexModel N), Φ x ∈ W)
    (hbij : ∀ᶠ x in 𝓝 (0 : ComplexModel N), Function.Bijective (fderiv ℝ Φ x))
    (h0 : pullbackField Φ (A.form.val.coeff e) 0 = flatForm N)
    (hd : HasFDerivAt (pullbackField Φ (A.form.val.coeff e))
      (0 : ComplexModel N →L[ℝ] CoordinateRealTwoForm N) 0) :
    NormalAt ψ := by
  have hm : ∀ᶠ x in 𝓝 (0 : ComplexModel N), metricOf ψ x =
      Real.pi • TosC11c.twoFormMetric (pullbackField Φ (A.form.val.coeff e) x) := by
    filter_upwards [hψ, hW] with x hx hxW
    ext Yv Zv
    rw [metricOf_eq_pullbackField A hpot hΦ hx hxW]
    rfl
  refine ⟨hψs, fun Yv Zv => ?_, ?_, ?_⟩
  · rw [hm.self_of_nhds, h0]
    simp only [smul_apply, TosC11c.twoFormMetric_apply, flatForm_apply, smul_eq_mul,
      Pending.ComplexHessianDeterminant.real_inner_eq_re, inner_smul_right]
    rw [Complex.mul_im, Complex.I_re, Complex.I_im]
    field_simp
    ring
  · have hL := (TosC11c.isBoundedLinearMap_twoFormMetric (n := N)).toContinuousLinearMap
    have h1 : HasFDerivAt (fun x => Real.pi • TosC11c.twoFormMetric
        (pullbackField Φ (A.form.val.coeff e) x))
        (Real.pi • ((TosC11c.isBoundedLinearMap_twoFormMetric (n := N)).toContinuousLinearMap.comp
          (0 : ComplexModel N →L[ℝ] CoordinateRealTwoForm N))) 0 :=
      ((TosC11c.isBoundedLinearMap_twoFormMetric (n := N)).toContinuousLinearMap.hasFDerivAt.comp
        0 hd).const_smul Real.pi
    rw [(h1.congr_of_eventuallyEq hm).fderiv]
    simp
  · filter_upwards [hψ, hW, hbij] with x hx hxW hxb
    intro v hv
    rw [metricOf_eq_chartMetric A hpot hΦ hx hxW]
    refine mul_pos Real.pi_pos (TosC11c.chartMetric_pos A e (hpot.2.1 hxW) _ fun h => hv ?_)
    exact hxb.1 (by rw [h, map_zero])

theorem I_smul_frameV (q : Fin N × Bool) :
    ∃ (q' : Fin N × Bool) (s : ℝ), |s| = 1 ∧ Complex.I • frameV q = s • frameV q' := by
  rcases q with ⟨k, b⟩
  cases b
  · exact ⟨(k, true), 1, by simp, by simp [frameV]⟩
  · refine ⟨(k, false), -1, by simp, ?_⟩
    simp only [frameV, if_true, Bool.false_eq_true, if_false, smul_smul, Complex.I_mul_I]
    rw [neg_one_smul, neg_one_smul]

/-- Bounds for the jets of a smooth function from those of a function proportional near `0`. -/
theorem scalar_jet_bound {m φ : ComplexModel N → ℝ} (hm : ContDiff ℝ ∞ m) {c : ℝ} (hc : c ≠ 0)
    (hev : m =ᶠ[𝓝 0] fun x => c * φ x) {C2 C3 : ℝ}
    (h2 : ‖iteratedFDeriv ℝ 2 φ 0‖ ≤ C2) (h3 : ‖iteratedFDeriv ℝ 3 φ 0‖ ≤ C3) :
    ‖fderiv ℝ (fderiv ℝ m) 0‖ ≤ |c| * C2 ∧ ‖fderiv ℝ (fderiv ℝ (fderiv ℝ m)) 0‖ ≤ |c| * C3 := by
  have hφ : φ =ᶠ[𝓝 0] fun x => c⁻¹ • m x := by
    filter_upwards [hev] with x hx
    rw [hx, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  have hφ2 := (hφ.iteratedFDeriv ℝ 2).self_of_nhds
  have hφ3 := (hφ.iteratedFDeriv ℝ 3).self_of_nhds
  rw [iteratedFDeriv_const_smul_apply'
    (hm.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))] at hφ2
  rw [iteratedFDeriv_const_smul_apply'
    (hm.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3))] at hφ3
  rw [hφ2, norm_smul, norm_inv, Real.norm_eq_abs, ← norm_iteratedFDeriv_fderiv,
    norm_iteratedFDeriv_one] at h2
  rw [hφ3, norm_smul, norm_inv, Real.norm_eq_abs, ← norm_iteratedFDeriv_fderiv,
    ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at h3
  have hc' : 0 < |c| := abs_pos.mpr hc
  rw [inv_mul_le_iff₀ hc'] at h2 h3
  exact ⟨h2, h3⟩

/-- **Jets of the metric in normal coordinates**: the second and third derivatives at `0` of the
metric of `ψ = ρ ∘ Φ` are bounded by the bounds for the coefficients of `Φ^*A` on the real frame. -/
theorem metric_jet_bounds (A : KahlerBackground N Y) {e : ComplexChart N Y}
    {W : Set (ComplexModel N)} {ρ : ComplexModel N → ℝ}
    (hpot : IsSmoothLocalPotential A.form.val e W ρ) {Φ : ComplexModel N → ComplexModel N}
    (hΦ : ContDiff ℂ ∞ Φ) {ψ : ComplexModel N → ℝ} (hψs : ContDiff ℝ ∞ ψ)
    (hψ : ∀ᶠ x in 𝓝 (0 : ComplexModel N), ψ =ᶠ[𝓝 x] fun y => ρ (Φ y))
    (hW : ∀ᶠ x in 𝓝 (0 : ComplexModel N), Φ x ∈ W) {C2 C3 : ℝ} (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3)
    (h2 : ∀ p q, ‖iteratedFDeriv ℝ 2
      (fun w => pullbackField Φ (A.form.val.coeff e) w ![frameV p, frameV q]) 0‖ ≤ C2)
    (h3 : ∀ p q, ‖iteratedFDeriv ℝ 3
      (fun w => pullbackField Φ (A.form.val.coeff e) w ![frameV p, frameV q]) 0‖ ≤ C3) :
    (∀ v, ‖fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v‖ ≤ 2 * N * (2 * N * (Real.pi * C2)) * ‖v‖) ∧
      (∀ v w, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (metricOf ψ))) 0 v w‖ ≤
        2 * N * (2 * N * (Real.pi * C3)) * ‖v‖ * ‖w‖) := by
  have hg : ContDiff ℝ ∞ (metricOf ψ) := contDiff_metricOf hψs
  -- the scalar functions
  have hscal : ∀ p q, ∃ (q' : Fin N × Bool) (s : ℝ), |s| = 1 ∧
      (fun x => metricOf ψ x (frameV p) (frameV q)) =ᶠ[𝓝 (0 : ComplexModel N)]
        fun x => (Real.pi * s) * pullbackField Φ (A.form.val.coeff e) x ![frameV p, frameV q'] := by
    intro p q
    obtain ⟨q', s, hs, hIq⟩ := I_smul_frameV q
    refine ⟨q', s, hs, ?_⟩
    filter_upwards [hψ, hW] with x hx hxW
    rw [metricOf_eq_pullbackField A hpot hΦ hx hxW, hIq, twoForm_smul_right]
    ring
  have hD : ∀ p q v w t, |fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v w (frameV p) (frameV q)| ≤
      Real.pi * C2 * ‖v‖ * ‖w‖ ∧
      |fderiv ℝ (fderiv ℝ (fderiv ℝ (metricOf ψ))) 0 v w t (frameV p) (frameV q)| ≤
        Real.pi * C3 * ‖v‖ * ‖w‖ * ‖t‖ := by
    intro p q v w t
    obtain ⟨q', s, hs, hev⟩ := hscal p q
    obtain ⟨e2, e3⟩ := iter_fderiv_eval hg (frameV p) (frameV q) 0 v w t
    have hmsm : ContDiff ℝ ∞ (fun x => metricOf ψ x (frameV p) (frameV q)) :=
      (evalYZ (frameV p) (frameV q)).contDiff.comp hg
    have hs0 : Real.pi * s ≠ 0 :=
      mul_ne_zero Real.pi_ne_zero (by intro h; rw [h] at hs; simp at hs)
    obtain ⟨hn2, hn3⟩ := scalar_jet_bound hmsm hs0 hev (h2 p q') (h3 p q')
    rw [abs_mul, abs_of_pos Real.pi_pos, hs, mul_one] at hn2 hn3
    refine ⟨?_, ?_⟩
    · rw [← e2, ← Real.norm_eq_abs]
      refine ((fderiv ℝ (fderiv ℝ (fun x => metricOf ψ x (frameV p) (frameV q))) 0).le_opNorm₂
        v w).trans ?_
      gcongr
    · rw [← e3, ← Real.norm_eq_abs]
      refine ((fderiv ℝ (fderiv ℝ (fderiv ℝ (fun x => metricOf ψ x (frameV p) (frameV q)))) 0
        v w).le_opNorm t).trans ?_
      refine (mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ (fderiv ℝ
        (fun x => metricOf ψ x (frameV p) (frameV q)))) 0).le_opNorm₂ v w) (norm_nonneg _)).trans ?_
      gcongr
  refine ⟨fun v => ?_, fun v w => ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
    have this := fun p q => (hD p q v w 0).1
    have hfb : ∀ j k,
        |fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v w (TosC11c.stdVec j) (TosC11c.stdVec k)| ≤
          Real.pi * C2 * ‖v‖ * ‖w‖ ∧
        |fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v w (TosC11c.stdVec j) (Complex.I • TosC11c.stdVec k)| ≤
          Real.pi * C2 * ‖v‖ * ‖w‖ ∧
        |fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v w (Complex.I • TosC11c.stdVec j) (TosC11c.stdVec k)| ≤
          Real.pi * C2 * ‖v‖ * ‖w‖ ∧
        |fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v w (Complex.I • TosC11c.stdVec j)
          (Complex.I • TosC11c.stdVec k)| ≤ Real.pi * C2 * ‖v‖ * ‖w‖ := fun j k =>
      ⟨this (j, false) (k, false), this (j, false) (k, true), this (j, true) (k, false),
        this (j, true) (k, true)⟩
    exact (norm_le_of_frame₂ _ (by positivity) hfb).trans (le_of_eq (by ring))
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun t => ?_
    have this := fun p q => (hD p q v w t).2
    have hfb : ∀ j k,
        |fderiv ℝ (fderiv ℝ (fderiv ℝ (metricOf ψ))) 0 v w t (TosC11c.stdVec j)
          (TosC11c.stdVec k)| ≤ Real.pi * C3 * ‖v‖ * ‖w‖ * ‖t‖ ∧
        |fderiv ℝ (fderiv ℝ (fderiv ℝ (metricOf ψ))) 0 v w t (TosC11c.stdVec j)
          (Complex.I • TosC11c.stdVec k)| ≤ Real.pi * C3 * ‖v‖ * ‖w‖ * ‖t‖ ∧
        |fderiv ℝ (fderiv ℝ (fderiv ℝ (metricOf ψ))) 0 v w t (Complex.I • TosC11c.stdVec j)
          (TosC11c.stdVec k)| ≤ Real.pi * C3 * ‖v‖ * ‖w‖ * ‖t‖ ∧
        |fderiv ℝ (fderiv ℝ (fderiv ℝ (metricOf ψ))) 0 v w t (Complex.I • TosC11c.stdVec j)
          (Complex.I • TosC11c.stdVec k)| ≤ Real.pi * C3 * ‖v‖ * ‖w‖ * ‖t‖ := fun j k =>
      ⟨this (j, false) (k, false), this (j, false) (k, true), this (j, true) (k, false),
        this (j, true) (k, true)⟩
    exact (norm_le_of_frame₂ _ (by positivity) hfb).trans (le_of_eq (by ring))

/-! ### Chart Hessians from the covariant Hessian -/

/-- **Bounds on a compact subset of a chart**: the metric of `A` is uniformly positive and bounded
with its derivative, the gradient length is `≤ ‖Du‖²/m`, and an upper bound `Λ ≥ 0` for the covariant
Hessian quotient bounds the chart Hessian (the lower bound comes from the positivity of `A + ddᶜu`). -/
theorem chart_bounds (A : KahlerBackground N Y) (e : ComplexChart N Y) {K : Set (ComplexModel N)}
    (hK : IsCompact K) (hKt : K ⊆ e.val.target) :
    ∃ m Mg Mg' : ℝ, 0 < m ∧ 0 ≤ Mg ∧ 0 ≤ Mg' ∧ ∀ (u : Y → ℝ) (hu : ChartSmooth (n := N) u),
      (∀ z ∈ K, TosC11c.gradNormSq A u e z ≤ ‖fderiv ℝ (fun w => u (e.val.symm w)) z‖ ^ 2 / m) ∧
      ((A.form + ddcClosedForm u hu).val.IsKahler → ∀ Λ CG : ℝ, 0 ≤ Λ →
        (∀ z ∈ K, ∀ v, v ≠ 0 → TosC11c.hessQuot A u e z v ≤ Λ) →
        (∀ z ∈ K, ‖fderiv ℝ (fun w => u (e.val.symm w)) z‖ ≤ CG) →
        ∀ z ∈ K, ‖fderiv ℝ (fderiv ℝ (fun w => u (e.val.symm w))) z‖ ≤
          4 * Real.pi * Mg + (Λ * Mg + 3 / 2 * Mg' * (CG / m))) := by
  have hU := e.val.open_target
  have hα := A.form.val.smooth e
  obtain ⟨m, hm, hmK⟩ := exists_pos_le_apply_I_smul hα.continuousOn
    (fun z hz => (A.isKahler.1 e z hz).2) hK hKt
  obtain ⟨Mg, hMg⟩ := hK.exists_bound_of_continuousOn
    ((TosC11c.contDiffOn_chartMetric A e).continuousOn.mono hKt)
  obtain ⟨Mg', hMg'⟩ := hK.exists_bound_of_continuousOn
    (((TosC11c.contDiffOn_chartMetric A e).continuousOn_fderiv_of_isOpen hU (by simp)).mono hKt)
  refine ⟨m, max Mg 0, max Mg' 0, hm, le_max_right _ _, le_max_right _ _, fun u hu => ?_⟩
  have hMgz : ∀ z ∈ K, ‖TosC11c.chartMetric A e z‖ ≤ max Mg 0 := fun z hz =>
    (hMg z hz).trans (le_max_left _ _)
  have hMgz' : ∀ z ∈ K, ‖fderiv ℝ (TosC11c.chartMetric A e) z‖ ≤ max Mg' 0 := fun z hz =>
    (hMg' z hz).trans (le_max_left _ _)
  have hgm : ∀ z ∈ K, ∀ v, m * ‖v‖ ^ 2 ≤ TosC11c.chartMetric A e z v v := fun z hz v => hmK z hz v
  -- the gradient vector
  have hgrad : ∀ z ∈ K, ‖TosC11c.chartGrad A u e z‖ ≤
      ‖fderiv ℝ (fun w => u (e.val.symm w)) z‖ / m ∧
      TosC11c.gradNormSq A u e z ≤ ‖fderiv ℝ (fun w => u (e.val.symm w)) z‖ ^ 2 / m := by
    intro z hz
    set G := TosC11c.chartGrad A u e z
    set L := fderiv ℝ (fun w => u (e.val.symm w)) z
    have hGG : TosC11c.chartMetric A e z G G = L G :=
      TosC11c.apply_gradVec (TosC11c.chartMetric_pos A e (hKt hz)) _ G
    have h1 := hgm z hz G
    have h2 : L G ≤ ‖L‖ * ‖G‖ := (le_abs_self _).trans (by
      rw [← Real.norm_eq_abs]; exact L.le_opNorm G)
    have hG : ‖G‖ ≤ ‖L‖ / m := by
      rw [le_div_iff₀ hm]
      rcases eq_or_lt_of_le (norm_nonneg G) with h0 | hpos
      · rw [← h0]; simp
      · nlinarith
    refine ⟨hG, ?_⟩
    show L G ≤ ‖L‖ ^ 2 / m
    calc L G ≤ ‖L‖ * ‖G‖ := h2
      _ ≤ ‖L‖ * (‖L‖ / m) := mul_le_mul_of_nonneg_left hG (norm_nonneg _)
      _ = ‖L‖ ^ 2 / m := by ring
  refine ⟨fun z hz => (hgrad z hz).2, fun hK' Λ CG hΛ hq hCG z hz => ?_⟩
  have hzt := hKt hz
  set a := fun w => u (e.val.symm w) with hadef
  have ha2 : ContDiffAt ℝ 2 a z :=
    ((hu e).contDiffAt (hU.mem_nhds hzt)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hsym : ∀ v w, fderiv ℝ (fderiv ℝ a) z v w = fderiv ℝ (fderiv ℝ a) z w v :=
    ha2.isSymmSndFDerivAt (by simp)
  have hgd : DifferentiableAt ℝ (TosC11c.chartMetric A e) z :=
    ((TosC11c.contDiffOn_chartMetric A e).contDiffAt (hU.mem_nhds hzt)).differentiableAt (by simp)
  -- the upper bound
  have hup : ∀ v, fderiv ℝ (fderiv ℝ a) z v v ≤
      (Λ * max Mg 0 + 3 / 2 * max Mg' 0 * (CG / m)) * ‖v‖ ^ 2 := by
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    have hq' := hq z hz v hv
    have hgpos := TosC11c.chartMetric_pos A e hzt v hv
    have hgle : TosC11c.chartMetric A e z v v ≤ max Mg 0 * ‖v‖ ^ 2 := by
      have := (TosC11c.chartMetric A e z).le_opNorm₂ v v
      rw [Real.norm_eq_abs] at this
      calc _ ≤ |TosC11c.chartMetric A e z v v| := le_abs_self _
        _ ≤ _ := this
        _ ≤ max Mg 0 * ‖v‖ * ‖v‖ := by gcongr; exact hMgz z hz
        _ = _ := by ring
    have hcov : TosC11b.covHess (TosC11c.chartMetric A e) a z v v (TosC11c.chartGrad A u e z) ≤
        Λ * (max Mg 0 * ‖v‖ ^ 2) := by
      have : TosC11b.covHess (TosC11c.chartMetric A e) a z v v (TosC11c.chartGrad A u e z) ≤
          Λ * TosC11c.chartMetric A e z v v := by
        rw [TosC11c.hessQuot, div_le_iff₀ hgpos] at hq'
        linarith
      exact this.trans (mul_le_mul_of_nonneg_left hgle hΛ)
    have hkos : |TosC11b.koszul (TosC11c.chartMetric A e) z v v (TosC11c.chartGrad A u e z)| ≤
        3 / 2 * max Mg' 0 * (CG / m) * ‖v‖ ^ 2 := by
      rw [TosC11c.koszul_eq hgd]
      set P := fderiv ℝ (TosC11c.chartMetric A e) z
      set G := TosC11c.chartGrad A u e z
      have hG : ‖G‖ ≤ CG / m := (hgrad z hz).1.trans (div_le_div_of_nonneg_right (hCG z hz) hm.le)
      have hP := hMgz' z hz
      have b1 : |P v v G| ≤ max Mg' 0 * ‖v‖ * ‖v‖ * (CG / m) := by
        rw [← Real.norm_eq_abs]
        calc ‖P v v G‖ ≤ ‖P v v‖ * ‖G‖ := (P v v).le_opNorm G
          _ ≤ ‖P‖ * ‖v‖ * ‖v‖ * ‖G‖ := by gcongr; exact P.le_opNorm₂ v v
          _ ≤ max Mg' 0 * ‖v‖ * ‖v‖ * (CG / m) := by gcongr
      have b2 : |P G v v| ≤ max Mg' 0 * (CG / m) * ‖v‖ * ‖v‖ := by
        rw [← Real.norm_eq_abs]
        calc ‖P G v v‖ ≤ ‖P G‖ * ‖v‖ * ‖v‖ := (P G).le_opNorm₂ v v
          _ ≤ ‖P‖ * ‖G‖ * ‖v‖ * ‖v‖ := by gcongr; exact P.le_opNorm G
          _ ≤ max Mg' 0 * (CG / m) * ‖v‖ * ‖v‖ := by gcongr
      rw [abs_div, abs_two]
      have := abs_sub (P v v G + P v v G) (P G v v)
      have := abs_add_le (P v v G) (P v v G)
      have e : 3 / 2 * max Mg' 0 * (CG / m) * ‖v‖ ^ 2 =
          (max Mg' 0 * ‖v‖ * ‖v‖ * (CG / m) + max Mg' 0 * ‖v‖ * ‖v‖ * (CG / m) +
            max Mg' 0 * (CG / m) * ‖v‖ * ‖v‖) / 2 := by ring
      rw [e]
      gcongr
      linarith
    have hdef : fderiv ℝ (fderiv ℝ a) z v v =
        TosC11b.covHess (TosC11c.chartMetric A e) a z v v (TosC11c.chartGrad A u e z) +
          TosC11b.koszul (TosC11c.chartMetric A e) z v v (TosC11c.chartGrad A u e z) := by
      rw [TosC11b.covHess]; ring
    rw [hdef]
    have := (abs_le.mp hkos).2
    nlinarith
  -- the lower bound from the positivity of `A + ddᶜu`
  have hlow : ∀ v, -(4 * Real.pi * max Mg 0 + (Λ * max Mg 0 + 3 / 2 * max Mg' 0 * (CG / m))) *
      ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ a) z v v := by
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    have hk := (hK'.1 e z hzt).2 v hv
    rw [add_ddc_line, ddc_line_eq hu e hzt] at hk
    have hAv : A.form.val.coeff e z ![v, Complex.I • v] ≤ max Mg 0 * ‖v‖ ^ 2 := by
      have := (TosC11c.chartMetric A e z).le_opNorm₂ v v
      rw [Real.norm_eq_abs] at this
      calc A.form.val.coeff e z ![v, Complex.I • v] = TosC11c.chartMetric A e z v v := rfl
        _ ≤ |TosC11c.chartMetric A e z v v| := le_abs_self _
        _ ≤ _ := this
        _ ≤ max Mg 0 * ‖v‖ * ‖v‖ := by gcongr; exact hMgz z hz
        _ = _ := by ring
    have hlev : -(Real.pi * (max Mg 0 * ‖v‖ ^ 2)) < leviForm a z v := by
      have h1 : -(max Mg 0 * ‖v‖ ^ 2) < leviForm a z v / Real.pi := by linarith
      have h2 := mul_lt_mul_of_pos_left h1 Real.pi_pos
      rw [mul_div_cancel₀ _ Real.pi_ne_zero] at h2
      linarith
    rw [leviForm, realHessian_eq_fderiv, realHessian_eq_fderiv] at hlev
    have hIv := hup (Complex.I • v)
    rw [norm_I_smul] at hIv
    nlinarith [sq_nonneg ‖v‖, Real.pi_pos]
  -- polarization
  have hquad : ∀ v, |fderiv ℝ (fderiv ℝ a) z v v| ≤
      (4 * Real.pi * max Mg 0 + (Λ * max Mg 0 + 3 / 2 * max Mg' 0 * (CG / m))) * ‖v‖ ^ 2 :=
    fun v => by
      rw [abs_le]
      refine ⟨by linarith [hlow v], ?_⟩
      have h0 : 0 ≤ 4 * Real.pi * max Mg 0 * ‖v‖ ^ 2 := by positivity
      nlinarith [hup v]
  have hpol := abs_apply_le_of_quad hsym hquad
  have hCG0 : 0 ≤ CG := (norm_nonneg _).trans (hCG z hz)
  exact ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun v w => by
    rw [Real.norm_eq_abs]; exact hpol v w

end Normal

end SGPT.Envelopes.TosC11d
