import SGPT.Envelopes.TosC11dJets
import SGPT.Envelopes.TosC11bBarrier
import SGPT.Envelopes.TosC11bLogDet

/-!
# Derivatives along lines at the centre of normal coordinates

Lane TOS-C11d (`claude-tos-c11d`, node `tos-c11d:line-calculus`).  Source: Xia, *Foundations of
pluripotential theory*, `lem:penalized-real-hessian`, Step 3, for SGPT `thm:Tos_C11` (Tosatti,
Chu–Zhou).

At the centre `0` of normal coordinates for the metric `g = metricOf ψ` (`g(0) = ⟪·, ·⟫`,
`Dg(0) = 0`) we compute, along a line `t ↦ t v`:

* the gradient vector `γ(t) = ∇a(t v)`: `γ(0) = Da(0)^♯`, `γ'(0) = (D²a(0) v)^♯` and
  `⟪V, γ''(0)⟫ = D³a(0)(v, v, V) - D²g(0)(v, v)(V, γ(0))` (`grad_line`);
* `s = Da(∇a)`: `s'(0) = 2 D²a(0)(v, γ(0))` and
  `s''(0) = 2 D³a(0)(v, v, γ(0)) + 2 ‖D²a(0) v‖² - D²g(0)(v, v)(γ(0), γ(0))` (`sFun_line`);
* the covariant Hessian `m(t) = ∇²a(t v)`: first derivative `D³a(t v) v - K'(t)` near `0` and second
  derivative `D⁴a(0)(v, v) - K''(0)` at `0`, with the Koszul term `K(t) = kosB(Dg(t v), γ(t))`,
  `K'(0) = kosB(D²g(0) v, γ(0))` and `K''(0) = kosB(D³g(0)(v, v), γ(0)) + 2 kosB(D²g(0) v, γ'(0))`
  (`cov_line`).

The covariant Hessian is a smooth field of bilinear forms because the Koszul term is a continuous
bilinear map `kosB` of `(Dg, ∇a)`.
-/

set_option autoImplicit false
-- nested spaces of continuous multilinear maps (derivatives of fields of bilinear forms) need deeper
-- pending instance synthesis, as in Mathlib's own build configuration
set_option maxSynthPendingDepth 3

noncomputable section

open Filter Set
open scoped Topology ContDiff InnerProductSpace RealInnerProductSpace ComplexOrder

namespace SGPT.Envelopes.TosC11d

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere

/-! ### Second derivatives of bilinear expressions along a curve -/

section Bilin

variable {P G H : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup G]
  [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- First and second derivatives of `t ↦ B(p t, γ t)` for a continuous bilinear `B`. -/
theorem hasDerivAt_bilin_two (B : P →L[ℝ] G →L[ℝ] H) {p p' : ℝ → P} {γ γ' : ℝ → G} {p₂ : P}
    {γ₂ : G} (hp : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt p (p' t) t) (hp' : HasDerivAt p' p₂ 0)
    (hγ : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt γ (γ' t) t) (hγ' : HasDerivAt γ' γ₂ 0) :
    (∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (fun t => B (p t) (γ t)) (B (p' t) (γ t) + B (p t) (γ' t)) t) ∧
      HasDerivAt (fun t => B (p' t) (γ t) + B (p t) (γ' t))
        (B p₂ (γ 0) + B (p' 0) (γ' 0) + (B (p' 0) (γ' 0) + B (p 0) γ₂)) 0 := by
  refine ⟨(hp.and hγ).mono fun t ht => ?_, ?_⟩
  · have h1 : HasDerivAt (fun t => B (p t)) (B (p' t)) t :=
      B.hasFDerivAt.comp_hasDerivAt t ht.1
    exact h1.clm_apply ht.2
  · have h1 : HasDerivAt (fun t => B (p' t)) (B p₂) 0 := B.hasFDerivAt.comp_hasDerivAt 0 hp'
    have h2 : HasDerivAt (fun t => B (p t)) (B (p' 0)) 0 :=
      B.hasFDerivAt.comp_hasDerivAt 0 hp.self_of_nhds
    have e1 := h1.clm_apply hγ.self_of_nhds
    have e2 := h2.clm_apply hγ'
    exact e1.add e2

end Bilin

/-! ### Derivatives of sums -/

section Sums

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_add_fun {f h : E → ℝ} (hf : Differentiable ℝ f) (hh : Differentiable ℝ h) :
    fderiv ℝ (fun x => f x + h x) = fun x => fderiv ℝ f x + fderiv ℝ h x := by
  funext x
  exact fderiv_add (hf x) (hh x)

theorem fderiv_add_fun' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f h : E → F}
    (hf : Differentiable ℝ f) (hh : Differentiable ℝ h) :
    fderiv ℝ (fun x => f x + h x) = fun x => fderiv ℝ f x + fderiv ℝ h x := by
  funext x
  exact fderiv_add (hf x) (hh x)

/-- The iterated derivatives of a sum of smooth functions. -/
theorem iter_fderiv_add {f h : E → ℝ} (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) :
    fderiv ℝ (fderiv ℝ (fun x => f x + h x)) =
        (fun x => fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ h) x) ∧
      fderiv ℝ (fderiv ℝ (fderiv ℝ (fun x => f x + h x))) =
        (fun x => fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x + fderiv ℝ (fderiv ℝ (fderiv ℝ h)) x) ∧
      fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fun x => f x + h x)))) =
        (fun x => fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) x +
          fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ h))) x) := by
  obtain ⟨f1, f2, f3⟩ := differentiable_fderiv_iter hf
  obtain ⟨h1, h2, h3⟩ := differentiable_fderiv_iter hh
  have e1 : fderiv ℝ (fun x => f x + h x) = fun x => fderiv ℝ f x + fderiv ℝ h x :=
    fderiv_add_fun (hf.differentiable (by simp)) (hh.differentiable (by simp))
  have e2 : fderiv ℝ (fderiv ℝ (fun x => f x + h x)) =
      fun x => fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ h) x := by
    rw [e1]; exact fderiv_add_fun' f1 h1
  have e3 : fderiv ℝ (fderiv ℝ (fderiv ℝ (fun x => f x + h x))) =
      fun x => fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x + fderiv ℝ (fderiv ℝ (fderiv ℝ h)) x := by
    rw [e2]; exact fderiv_add_fun' f2 h2
  refine ⟨e2, e3, ?_⟩
  rw [e3]; exact fderiv_add_fun' f3 h3

end Sums

/-! ### The Koszul term as a continuous bilinear map -/

section Koszul

variable {n : ℕ}

/-- The Koszul term `(P, G) ↦ kosForm P G` as a continuous bilinear map. -/
def kosB : (ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) →L[ℝ]
    ComplexModel n →L[ℝ] (ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ kosForm
      (fun P P' G => by ext Y Z; simp only [kosForm_apply, add_apply]; ring)
      (fun c P G => by ext Y Z; simp only [kosForm_apply, smul_apply, smul_eq_mul]; ring)
      (fun P G G' => by ext Y Z; simp only [kosForm_apply, add_apply, map_add]; ring)
      (fun c P G => by ext Y Z; simp only [kosForm_apply, smul_apply, smul_eq_mul, map_smul]; ring))
    (3 / 2) fun P G => by
      simp only [LinearMap.mk₂_apply]
      have h0 : 0 ≤ 3 / 2 * ‖P‖ * ‖G‖ := by positivity
      calc ‖kosForm P G‖ ≤ 3 / 2 * ‖P‖ * ‖G‖ := LinearMap.mkContinuous₂_norm_le _ h0 _
        _ = 3 / 2 * ‖P‖ * ‖G‖ := rfl

theorem kosB_apply (P : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (G : ComplexModel n) : kosB P G = kosForm P G := rfl

theorem kerr_eq (ψ a : ComplexModel n → ℝ) (x : ComplexModel n) :
    kerr ψ a x = kosB (fderiv ℝ (metricOf ψ) x) (grad ψ a x) := rfl

end Koszul

/-! ### Normal coordinates -/

section Normal

variable {n : ℕ} {ψ a : ComplexModel n → ℝ}

/-- Data at the centre of normal coordinates for the metric of `ψ`. -/
structure NormalAt (ψ : ComplexModel n → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ ψ
  metric_zero : ∀ Y Z, metricOf ψ 0 Y Z = ⟪Y, Z⟫
  fderiv_zero : fderiv ℝ (metricOf ψ) 0 = 0
  pos : ∀ᶠ x in 𝓝 (0 : ComplexModel n), ∀ v, v ≠ 0 → 0 < metricOf ψ x v v

theorem NormalAt.pos_zero (hN : NormalAt ψ) : ∀ v, v ≠ 0 → 0 < metricOf ψ 0 v v := fun v hv => by
  rw [hN.metric_zero, real_inner_self_eq_norm_sq]; exact pow_pos (norm_pos_iff.mpr hv) 2

/-- At the centre the gradient vector is the Riesz vector of `Da(0)`. -/
theorem NormalAt.grad_zero (hN : NormalAt ψ) (a : ComplexModel n → ℝ) :
    grad ψ a 0 = rieszInv (fderiv ℝ a 0) := by
  refine ext_inner_right ℝ fun y => ?_
  rw [inner_rieszInv, real_inner_comm, ← hN.metric_zero, metricOf_grad hN.pos_zero]

theorem NormalAt.kerr_zero (hN : NormalAt ψ) (a : ComplexModel n → ℝ) : kerr ψ a 0 = 0 := by
  rw [kerr_eq, hN.fderiv_zero, map_zero, zero_apply]

theorem NormalAt.cov_zero (hN : NormalAt ψ) (a : ComplexModel n → ℝ) :
    cov ψ a 0 = fderiv ℝ (fderiv ℝ a) 0 := by
  rw [cov, hN.kerr_zero, sub_zero]

theorem NormalAt.sFun_zero (hN : NormalAt ψ) (a : ComplexModel n → ℝ) :
    sFun ψ a 0 = ‖fderiv ℝ a 0‖ ^ 2 := by
  rw [sFun, hN.grad_zero, ← inner_rieszInv, real_inner_self_eq_norm_sq, norm_rieszInv]

theorem NormalAt.contDiffAt_grad (hN : NormalAt ψ) (ha : ContDiff ℝ ∞ a) :
    ContDiffAt ℝ 2 (grad ψ a) 0 :=
  (TosC11d.contDiffAt_grad hN.smooth ha hN.pos_zero).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

theorem eventually_line {p : ComplexModel n → Prop} (h : ∀ᶠ x in 𝓝 (0 : ComplexModel n), p x)
    (v : ComplexModel n) : ∀ᶠ t in 𝓝 (0 : ℝ), p (t • v) := by
  have hc : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 0) :=
    (continuous_id.smul continuous_const : Continuous fun t : ℝ => t • v).tendsto' 0 0 (by simp)
  exact hc.eventually h

/-- **The gradient vector along a line** at the centre of normal coordinates. -/
theorem NormalAt.grad_line (hN : NormalAt ψ) (ha : ContDiff ℝ ∞ a) (v : ComplexModel n) :
    fderiv ℝ (grad ψ a) 0 v = rieszInv (fderiv ℝ (fderiv ℝ a) 0 v) ∧
      ∀ V, ⟪V, fderiv ℝ (fderiv ℝ (grad ψ a)) 0 v v⟫ =
        fderiv ℝ (fderiv ℝ (fderiv ℝ a)) 0 v v V -
          fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v v V (grad ψ a 0) := by
  set g := metricOf ψ with hgdef
  have hg : ContDiff ℝ ∞ g := contDiff_metricOf hN.smooth
  have hg2 : ContDiffAt ℝ 2 g 0 := hg.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  obtain ⟨hγ, hγ'⟩ := line_deriv_two (hN.contDiffAt_grad ha) v
  obtain ⟨hgl, hgl'⟩ := line_deriv_two hg2 v
  obtain ⟨-, a2, a3⟩ := differentiable_fderiv_iter ha
  have hal : ∀ t : ℝ, HasDerivAt (fun s : ℝ => fderiv ℝ a (s • v))
      (fderiv ℝ (fderiv ℝ a) (t • v) v) t := fun t =>
    hasDerivAt_line ((differentiable_fderiv_iter ha).1 _)
  have hal' : HasDerivAt (fun t : ℝ => fderiv ℝ (fderiv ℝ a) (t • v) v)
      (fderiv ℝ (fderiv ℝ (fderiv ℝ a)) 0 v v) 0 := by
    have := (hasDerivAt_line (t := 0) (v := v) (a2 _)).clm_apply (hasDerivAt_const (0 : ℝ) v)
    simpa using this
  -- the identity `g(tv)(V, γ t) = Da(tv) V` near `0`
  have hid : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ V, g (t • v) V (grad ψ a (t • v)) = fderiv ℝ a (t • v) V :=
    (eventually_line hN.pos v).mono fun t ht V => metricOf_grad ht V
  -- first derivatives of both sides, near `0`
  have hd1 : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ V,
      fderiv ℝ g (t • v) v V (grad ψ a (t • v)) + g (t • v) V (fderiv ℝ (grad ψ a) (t • v) v) =
        fderiv ℝ (fderiv ℝ a) (t • v) v V := by
    filter_upwards [hid.eventually_nhds, hγ, hgl] with t ht htγ htg
    intro V
    have hL : HasDerivAt (fun s : ℝ => g (s • v) V (grad ψ a (s • v)))
        (fderiv ℝ g (t • v) v V (grad ψ a (t • v)) +
          g (t • v) V (fderiv ℝ (grad ψ a) (t • v) v)) t :=
      (htg.clm_apply (hasDerivAt_const t V)).clm_apply htγ |>.congr_deriv (by simp)
    have hR : HasDerivAt (fun s : ℝ => fderiv ℝ a (s • v) V)
        (fderiv ℝ (fderiv ℝ a) (t • v) v V) t :=
      ((hal t).clm_apply (hasDerivAt_const t V)).congr_deriv (by simp)
    exact hL.unique (hR.congr_of_eventuallyEq (ht.mono fun s hs => hs V))
  have hd10 := hd1.self_of_nhds
  simp only [zero_smul] at hd10
  have hfirst : fderiv ℝ (grad ψ a) 0 v = rieszInv (fderiv ℝ (fderiv ℝ a) 0 v) := by
    refine ext_inner_right ℝ fun V => ?_
    have := hd10 V
    rw [hN.fderiv_zero, zero_apply, zero_apply,
      zero_apply, zero_add, hN.metric_zero] at this
    rw [inner_rieszInv, real_inner_comm, this]
  refine ⟨hfirst, fun V => ?_⟩
  -- second derivatives at `0`
  have hL : HasDerivAt (fun t : ℝ =>
      fderiv ℝ g (t • v) v V (grad ψ a (t • v)) + g (t • v) V (fderiv ℝ (grad ψ a) (t • v) v))
      (fderiv ℝ (fderiv ℝ g) 0 v v V (grad ψ a 0) + fderiv ℝ g 0 v V (fderiv ℝ (grad ψ a) 0 v) +
        (fderiv ℝ g 0 v V (fderiv ℝ (grad ψ a) 0 v) +
          g 0 V (fderiv ℝ (fderiv ℝ (grad ψ a)) 0 v v))) 0 := by
    have e1 := (hgl'.clm_apply (hasDerivAt_const (0 : ℝ) V)).clm_apply hγ.self_of_nhds
    have e2 := (hgl.self_of_nhds.clm_apply (hasDerivAt_const (0 : ℝ) V)).clm_apply hγ'
    simp only [zero_smul] at e1 e2
    exact (e1.add e2).congr_deriv (by simp)
  have hR : HasDerivAt (fun t : ℝ => fderiv ℝ (fderiv ℝ a) (t • v) v V)
      (fderiv ℝ (fderiv ℝ (fderiv ℝ a)) 0 v v V) 0 :=
    (hal'.clm_apply (hasDerivAt_const (0 : ℝ) V)).congr_deriv (by simp)
  have hu := hL.unique (hR.congr_of_eventuallyEq (hd1.mono fun t ht => ht V))
  rw [hN.fderiv_zero, zero_apply, zero_apply,
    zero_apply, add_zero, zero_add, hN.metric_zero] at hu
  linarith

/-- **The squared gradient length along a line** at the centre of normal coordinates:
`s'(t) = D²a(tv)(v, γ t) + Da(tv)(γ'(t))` near `0`, `s'(0) = 2 D²a(0)(v, γ(0))` and
`s''(0) = 2 D³a(0)(v, v, γ(0)) + 2 ‖D²a(0) v‖² - D²g(0)(v, v)(γ(0), γ(0))`. -/
theorem NormalAt.sFun_line (hN : NormalAt ψ) (ha : ContDiff ℝ ∞ a) (v : ComplexModel n) :
    (∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (fun t => sFun ψ a (t • v))
      (fderiv ℝ (fderiv ℝ a) (t • v) v (grad ψ a (t • v)) +
        fderiv ℝ a (t • v) (fderiv ℝ (grad ψ a) (t • v) v)) t) ∧
    fderiv ℝ (fderiv ℝ a) ((0 : ℝ) • v) v (grad ψ a ((0 : ℝ) • v)) +
        fderiv ℝ a ((0 : ℝ) • v) (fderiv ℝ (grad ψ a) ((0 : ℝ) • v) v) =
      2 * fderiv ℝ (fderiv ℝ a) 0 v (grad ψ a 0) ∧
    HasDerivAt (fun t : ℝ => fderiv ℝ (fderiv ℝ a) (t • v) v (grad ψ a (t • v)) +
        fderiv ℝ a (t • v) (fderiv ℝ (grad ψ a) (t • v) v))
      (2 * fderiv ℝ (fderiv ℝ (fderiv ℝ a)) 0 v v (grad ψ a 0) +
        2 * ‖fderiv ℝ (fderiv ℝ a) 0 v‖ ^ 2 -
        fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v v (grad ψ a 0) (grad ψ a 0)) 0 := by
  obtain ⟨hγ, hγ'⟩ := line_deriv_two (hN.contDiffAt_grad ha) v
  obtain ⟨a1, a2, -⟩ := differentiable_fderiv_iter ha
  obtain ⟨hgr1, hgr2⟩ := hN.grad_line ha v
  have hal : ∀ t : ℝ, HasDerivAt (fun s : ℝ => fderiv ℝ a (s • v))
      (fderiv ℝ (fderiv ℝ a) (t • v) v) t := fun t => hasDerivAt_line (a1 _)
  have hal' : ∀ t : ℝ, HasDerivAt (fun t : ℝ => fderiv ℝ (fderiv ℝ a) (t • v) v)
      (fderiv ℝ (fderiv ℝ (fderiv ℝ a)) (t • v) v v) t := fun t => by
    have := (hasDerivAt_line (t := t) (v := v) (a2 _)).clm_apply (hasDerivAt_const t v)
    simpa using this
  have hG0 := hN.grad_zero a
  -- auxiliary identities at `0`
  have i1 : fderiv ℝ a 0 (fderiv ℝ (grad ψ a) 0 v) = fderiv ℝ (fderiv ℝ a) 0 v (grad ψ a 0) := by
    rw [hgr1, hG0, ← inner_rieszInv, ← inner_rieszInv, real_inner_comm]
  have i2 : fderiv ℝ (fderiv ℝ a) 0 v (fderiv ℝ (grad ψ a) 0 v) =
      ‖fderiv ℝ (fderiv ℝ a) 0 v‖ ^ 2 := by
    rw [hgr1, ← inner_rieszInv, real_inner_self_eq_norm_sq, norm_rieszInv]
  have i3 : fderiv ℝ a 0 (fderiv ℝ (fderiv ℝ (grad ψ a)) 0 v v) =
      fderiv ℝ (fderiv ℝ (fderiv ℝ a)) 0 v v (grad ψ a 0) -
        fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v v (grad ψ a 0) (grad ψ a 0) := by
    rw [← hgr2, hG0, ← inner_rieszInv]
  refine ⟨hγ.mono fun t ht => ?_, ?_, ?_⟩
  · exact ((hal t).clm_apply ht).congr_deriv rfl
  · simp only [zero_smul]
    rw [i1]; ring
  · have e1 := (hal' 0).clm_apply hγ.self_of_nhds
    have e2 := (hal 0).clm_apply hγ'
    simp only [zero_smul] at e1 e2
    refine (e1.fun_add e2).congr_deriv ?_
    rw [i2, i3]
    ring

/-- **The covariant Hessian along a line** at the centre of normal coordinates. -/
theorem NormalAt.cov_line (hN : NormalAt ψ) (ha : ContDiff ℝ ∞ a) (v : ComplexModel n) :
    (∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (fun t => cov ψ a (t • v))
      (fderiv ℝ (fderiv ℝ (fderiv ℝ a)) (t • v) v -
        (kosB (fderiv ℝ (fderiv ℝ (metricOf ψ)) (t • v) v) (grad ψ a (t • v)) +
          kosB (fderiv ℝ (metricOf ψ) (t • v)) (fderiv ℝ (grad ψ a) (t • v) v))) t) ∧
    HasDerivAt (fun t : ℝ => fderiv ℝ (fderiv ℝ (fderiv ℝ a)) (t • v) v -
        (kosB (fderiv ℝ (fderiv ℝ (metricOf ψ)) (t • v) v) (grad ψ a (t • v)) +
          kosB (fderiv ℝ (metricOf ψ) (t • v)) (fderiv ℝ (grad ψ a) (t • v) v)))
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ a))) 0 v v -
        (kosB (fderiv ℝ (fderiv ℝ (fderiv ℝ (metricOf ψ))) 0 v v) (grad ψ a 0) +
          2 • kosB (fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v) (fderiv ℝ (grad ψ a) 0 v))) 0 := by
  have hg : ContDiff ℝ ∞ (metricOf ψ) := contDiff_metricOf hN.smooth
  have hPg : ContDiffAt ℝ 2 (fderiv ℝ (metricOf ψ)) 0 :=
    ((hg.fderiv_right (m := ∞) (by simp)).contDiffAt).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  obtain ⟨hp, hp'⟩ := line_deriv_two hPg v
  obtain ⟨hγ, hγ'⟩ := line_deriv_two (hN.contDiffAt_grad ha) v
  obtain ⟨hk, hk'⟩ := hasDerivAt_bilin_two kosB hp hp' hγ hγ'
  have h2 : ContDiffAt ℝ 2 (fderiv ℝ (fderiv ℝ a)) 0 :=
    ((((ha.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp))).contDiffAt).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  obtain ⟨hA, hA'⟩ := line_deriv_two h2 v
  refine ⟨(hA.and hk).mono fun t ht => ht.1.fun_sub ht.2, ?_⟩
  refine (hA'.fun_sub hk').congr_deriv ?_
  simp only [zero_smul, hN.fderiv_zero, map_zero, zero_apply, add_zero, two_smul]
  abel

/-- The complex Hessian of the potential at the centre is the identity matrix. -/
theorem NormalAt.complexHessian_zero (hN : NormalAt ψ) : complexHessian ψ 0 = 1 := by
  ext j k
  rw [complexHessian_eq_cHm, ← metricOf, cHm, hN.metric_zero, hN.metric_zero,
    Pending.ComplexHessianDeterminant.real_inner_eq_re,
    Pending.ComplexHessianDeterminant.real_inner_eq_re]
  simp only [coordinateVector, inner_smul_right, EuclideanSpace.inner_single_right]
  by_cases hjk : j = k
  · subst hjk; simp
  · simp [Matrix.one_apply_ne hjk, Ne.symm hjk]

end Normal

/-! ### The penalized equation along a line -/

section Equation

variable {n : ℕ}

/-- **The once and twice differentiated penalized equation along a line** (FPT
`lem:penalized-real-hessian`, Step 3), at the centre of normal coordinates where
`G = H(ψ + a)(0) = diag(r)`: for every direction `u`,
`Σᵢ Re ∂_u Gᵢᵢ / rᵢ = β (Da(0) u - DF(0) u)` and
`Σᵢ Re ∂²_u Gᵢᵢ / rᵢ = Σ_{p,q} |∂_u G_{pq}|²/(r_p r_q) + β (D²a(0)(u, u) - D²F(0)(u, u)) + Σᵢ D²g(0)(u, u)(eᵢ, eᵢ)`,
written with the complex Hessians of the jets of `a` (`∂_u H(ψ)(0) = 0`). -/
theorem NormalAt.equation_line {ψ a F : ComplexModel n → ℝ} (hN : NormalAt ψ)
    (ha : ContDiff ℝ ∞ a) (hF : ContDiff ℝ ∞ F) {β : ℝ}
    (heq : ∀ᶠ x in 𝓝 (0 : ComplexModel n), (complexHessian (fun y => ψ y + a y) x).det.re =
      Real.exp (β * (a x - F x)) * (complexHessian ψ x).det.re)
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hG0 : complexHessian (fun y => ψ y + a y) 0 = Matrix.diagonal fun i => (r i : ℂ))
    (u : ComplexModel n) :
    ∑ i, (cHm (leviBil (fderiv ℝ (fderiv ℝ (fderiv ℝ a)) 0 u)) i i).re / r i =
        β * (fderiv ℝ a 0 u - fderiv ℝ F 0 u) ∧
      ∑ i, (cHm (leviBil (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ a))) 0 u u)) i i).re / r i +
          ∑ i, fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 u u (coordinateVector i) (coordinateVector i) /
            r i =
        (∑ p, ∑ q, ‖cHm (leviBil (fderiv ℝ (fderiv ℝ (fderiv ℝ a)) 0 u)) p q‖ ^ 2 / (r p * r q)) +
          β * (fderiv ℝ (fderiv ℝ a) 0 u u - fderiv ℝ (fderiv ℝ F) 0 u u) +
          ∑ i, fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 u u (coordinateVector i) (coordinateVector i) := by
  have hψ := hN.smooth
  have hf : ContDiff ℝ ∞ (fun y => ψ y + a y) := hψ.add ha
  obtain ⟨-, e3, e4⟩ := iter_fderiv_add hψ ha
  -- the matrix curves, as opaque functions
  obtain ⟨G', hG'⟩ : ∃ G' : ℝ → Matrix (Fin n) (Fin n) ℂ, ∀ t i j, G' t i j =
      cHm (leviBil (fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => ψ y + a y))) (t • u) u)) i j :=
    ⟨fun t => Matrix.of fun i j => _, fun _ _ _ => rfl⟩
  obtain ⟨G₂, hG₂⟩ : ∃ G₂ : Matrix (Fin n) (Fin n) ℂ, ∀ i j, G₂ i j =
      cHm (leviBil (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => ψ y + a y)))) 0 u u)) i j :=
    ⟨Matrix.of fun i j => _, fun _ _ => rfl⟩
  obtain ⟨K', hK'⟩ : ∃ K' : ℝ → Matrix (Fin n) (Fin n) ℂ, ∀ t i j, K' t i j =
      cHm (leviBil (fderiv ℝ (fderiv ℝ (fderiv ℝ ψ)) (t • u) u)) i j :=
    ⟨fun t => Matrix.of fun i j => _, fun _ _ _ => rfl⟩
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : Matrix (Fin n) (Fin n) ℂ, ∀ i j, K₂ i j =
      cHm (leviBil (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ ψ))) 0 u u)) i j :=
    ⟨Matrix.of fun i j => _, fun _ _ => rfl⟩
  have hGd : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i j, HasDerivAt
      (fun t => complexHessian (fun y => ψ y + a y) (t • u) i j) (G' t i j) t :=
    Eventually.of_forall fun t i j => by
      rw [hG']; exact hasDerivAt_complexHessian_line hf u t i j
  have hGd' : ∀ i j, HasDerivAt (fun t => G' t i j) (G₂ i j) 0 := fun i j => by
    simp only [hG', hG₂]; exact hasDerivAt_complexHessian_line_two hf u i j
  have hKd : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i j, HasDerivAt
      (fun t => complexHessian ψ (t • u) i j) (K' t i j) t :=
    Eventually.of_forall fun t i j => by
      rw [hK']; exact hasDerivAt_complexHessian_line hψ u t i j
  have hKd' : ∀ i j, HasDerivAt (fun t => K' t i j) (K₂ i j) 0 := fun i j => by
    simp only [hK', hK₂]; exact hasDerivAt_complexHessian_line_two hψ u i j
  have hGh : ∀ᶠ t in 𝓝 (0 : ℝ), (complexHessian (fun y => ψ y + a y) (t • u)).IsHermitian :=
    Eventually.of_forall fun t => Pending.WirtingerLogDet.isHermitian_complexHessian hf _
  have hKh : ∀ᶠ t in 𝓝 (0 : ℝ), (complexHessian ψ (t • u)).IsHermitian :=
    Eventually.of_forall fun t => Pending.WirtingerLogDet.isHermitian_complexHessian hψ _
  have hK0 : complexHessian ψ ((0 : ℝ) • u) = 1 := by rw [zero_smul]; exact hN.complexHessian_zero
  have hψ3 : leviBil (fderiv ℝ (fderiv ℝ (fderiv ℝ ψ)) 0 u) = 0 := by
    rw [← fderiv_metricOf hψ, hN.fderiv_zero, zero_apply]
  have hψ4 : leviBil (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ ψ))) 0 u u) =
      fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 u u := (fderiv_fderiv_metricOf hψ 0 u u).symm
  have hK'0 : K' 0 = 0 := by
    ext i j
    rw [hK', zero_smul, hψ3, Matrix.zero_apply]
    simp [cHm]
  have hG00 : complexHessian (fun y => ψ y + a y) ((0 : ℝ) • u) =
      Matrix.diagonal fun i => (r i : ℂ) := by rw [zero_smul]; exact hG0
  -- the logarithm of the determinant of `K`
  obtain ⟨hlK, hlK'⟩ := TosC11b.log_det_variation hKd hKd' hKh
    (by rw [hK0]; exact Matrix.PosDef.one)
  have hdetK : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < (complexHessian ψ (t • u)).det.re := by
    have hc : Continuous fun t : ℝ => (complexHessian ψ (t • u)).det.re :=
      Complex.continuous_re.comp
        ((Pending.WirtingerLogDet.contDiff_det_complexHessian hψ).continuous.comp
          (continuous_id.smul continuous_const))
    have h0 : 0 < (complexHessian ψ ((0 : ℝ) • u)).det.re := by
      rw [hK0]; simp
    exact hc.continuousAt.eventually (lt_mem_nhds h0)
  -- the function `φ`
  have haF : ∀ t : ℝ, HasDerivAt (fun t => a (t • u) - F (t • u))
      (fderiv ℝ a (t • u) u - fderiv ℝ F (t • u) u) t := fun t =>
    (hasDerivAt_line ((ha.differentiable (by simp)) _)).sub
      (hasDerivAt_line ((hF.differentiable (by simp)) _))
  have hφd : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt
      (fun t => β * (a (t • u) - F (t • u)) + Real.log (complexHessian ψ (t • u)).det.re)
      (β * (fderiv ℝ a (t • u) u - fderiv ℝ F (t • u) u) +
        ((complexHessian ψ (t • u))⁻¹ * K' t).trace.re) t :=
    hlK.mono fun t ht => ((haF t).const_mul β).add ht
  have haF' : HasDerivAt (fun t : ℝ => fderiv ℝ a (t • u) u - fderiv ℝ F (t • u) u)
      (fderiv ℝ (fderiv ℝ a) 0 u u - fderiv ℝ (fderiv ℝ F) 0 u u) 0 := by
    have h1 := (hasDerivAt_line (t := 0) (v := u)
      ((differentiable_fderiv_iter ha).1 _)).clm_apply (hasDerivAt_const (0 : ℝ) u)
    have h2 := (hasDerivAt_line (t := 0) (v := u)
      ((differentiable_fderiv_iter hF).1 _)).clm_apply (hasDerivAt_const (0 : ℝ) u)
    simp only [zero_smul, map_zero, add_zero] at h1 h2
    exact h1.sub h2
  have hφd' := (haF'.const_mul β).add hlK'
  have hlog : ∀ᶠ t in 𝓝 (0 : ℝ),
      Real.log (complexHessian (fun y => ψ y + a y) (t • u)).det.re =
        β * (a (t • u) - F (t • u)) + Real.log (complexHessian ψ (t • u)).det.re := by
    filter_upwards [eventually_line heq u, hdetK] with t ht hKt
    rw [ht, Real.log_mul (Real.exp_pos _).ne' hKt.ne', Real.log_exp]
  obtain ⟨h1, h2⟩ := TosC11b.differentiated_log_det_equation r hr hGd hGd' hGh hG00 hφd hφd' hlog
  -- decompositions of the jets of `ψ + a`
  have hG'0 : ∀ p q, G' 0 p q = cHm (leviBil (fderiv ℝ (fderiv ℝ (fderiv ℝ a)) 0 u)) p q := by
    intro p q
    rw [hG', zero_smul, e3]
    simp only [add_apply, map_add, hψ3, zero_add]
  have hG₂' : ∀ i, (G₂ i i).re =
      fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 u u (coordinateVector i) (coordinateVector i) +
        (cHm (leviBil (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ a))) 0 u u)) i i).re := by
    intro i
    rw [hG₂, e4]
    simp only [add_apply, map_add, hψ4, ← cHmL_apply, Complex.add_re]
    rw [cHmL_apply, cHm_re_diag]
  have hK₂' : ((complexHessian ψ ((0 : ℝ) • u))⁻¹ * K₂).trace.re =
      ∑ i, fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 u u (coordinateVector i) (coordinateVector i) := by
    rw [hK0, inv_one, one_mul, Matrix.trace, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.diag, hK₂, hψ4, cHm_re_diag]
  refine ⟨?_, ?_⟩
  · have hφ'0 : β * (fderiv ℝ a ((0 : ℝ) • u) u - fderiv ℝ F ((0 : ℝ) • u) u) +
        ((complexHessian ψ ((0 : ℝ) • u))⁻¹ * K' 0).trace.re =
        β * (fderiv ℝ a 0 u - fderiv ℝ F 0 u) := by
      rw [hK'0, zero_smul]; simp
    rw [← hφ'0, ← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hG'0]
  · rw [hK'0, hK₂'] at h2
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re,
      sub_zero] at h2
    have hsplit : ∑ i, (G₂ i i).re / r i =
        ∑ i, (cHm (leviBil (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ a))) 0 u u)) i i).re / r i +
          ∑ i, fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 u u (coordinateVector i) (coordinateVector i) /
            r i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hG₂', add_div]; ring
    have hpq : ∑ p, ∑ q, ‖G' 0 p q‖ ^ 2 / (r p * r q) =
        ∑ p, ∑ q, ‖cHm (leviBil (fderiv ℝ (fderiv ℝ (fderiv ℝ a)) 0 u)) p q‖ ^ 2 /
          (r p * r q) := by
      simp only [hG'0]
    rw [← hsplit, h2, hpq]
    ring

end Equation

end SGPT.Envelopes.TosC11d
