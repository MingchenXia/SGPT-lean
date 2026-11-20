import SGPT.Foundations.Analysis.Pending.BlockiLocalEstimate
import SGPT.Foundations.Analysis.Pending.AubinYauLocalStep
import SGPT.Foundations.Analysis.Pending.AubinYauUniformConstants
import SGPT.Foundations.Analysis.Pending.ConcentrationPotentialLevi
import SGPT.Okounkov.TranscendentalWNRegBeta

/-!
# The Aubin–Yau–Siu trace inequality at a point (Euclidean part)

Lane LAP-CLASS (`claude-lap-class`, nodes `lap-class:flat-aubin-yau`, `lap-class:local-trace`).
Source: Xia, *Foundations of pluripotential theory*, `lem:kahler-trace-laplacian` and
`lem:penalized-equation-trace` (chapter q10, `sec:penalized-kahler-envelopes`), the trace form of
Berman's Laplacian estimate behind SGPT `prop:DR16_C11bar` for obstacles with bounded metric
Laplacian.

Everything here happens in `ℂⁿ` at one point.  We write `levTr f x = ∑ₚ f_{pp̄}(x)` for the
coordinate trace of the complex Hessian (`levTr`, `re_trace_complexHessian`).

* `levTr_logDet_div_le` (**flat Aubin–Yau inequality**): for a smooth `u` with positive definite
  complex Hessian `H` at `x`,
  `(∑ₚ (log det H)_{pp̄}(x)) / tr H(x) ≤ Re tr(H(x)⁻¹ Hess_ℂ(log tr H)(x))`.
  It follows from Błocki's one-direction inequality (TN `blocki_local_estimate`) for each
  coordinate direction, combined through the concavity of `log`: with `λₚ = u_{pp̄}(x)/tr H(x)`,
  `log tr H - ∑ₚ λₚ log u_{pp̄}` has a local minimum at `x` (weighted AM–GM), so its complex
  Hessian is positive semidefinite there.  This replaces the Cauchy–Schwarz step of FPT
  `lem:kahler-trace-laplacian`.
* `one_sub_mul_re_trace_le` (**barrier for the inverse metric**): if `H > 0` and `H ≤ (1 + δ)·1`
  then `(1 - δ) tr G ≤ Re tr(H⁻¹ G)` for `G ≥ 0` (from `H⁻¹ - 2 + H = (1 - H) H⁻¹ (1 - H) ≥ 0`).
* `norm_sub_le_of_fderiv_eq_zero` (second-order Taylor bound with a vanishing first derivative).
* `levTr_le_of_isLocalMax` (**the maximum principle step of the trace estimate**): at a local
  maximum of `log tr Hess ψ - 2K‖w‖² - a(ψ - σ)`, with `Hess σ(0) = 1`, the lower bound
  `∑ₚ (log det Hess ψ)_{pp̄}(0) ≥ β(tr Hess ψ(0) - n - ∑ₚ F_{pp̄}(0)) - C₁` coming from the equation,
  `∑ₚ F_{pp̄}(0) ≤ S`, `a ≥ 2K + C₁` and `β > 2an`, one has `tr Hess ψ(0) ≤ 2(n + S)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Matrix Complex Metric
open scoped Topology ContDiff ComplexConjugate ComplexOrder

namespace SGPT.Envelopes.LapClass

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SemiconcaveHessian
open SGPT.Foundations.Analysis.Pending.AubinYauLocalStep
open SGPT.Foundations.Analysis.Pending.BlockiLocalEstimate

variable {n : ℕ}

/-! ### The coordinate trace of the complex Hessian -/

/-- The coordinate trace `∑ₚ f_{pp̄}(x)` of the complex Hessian, as a sum of Levi forms. -/
def levTr (f : ComplexModel n → ℝ) (x : ComplexModel n) : ℝ :=
  ∑ p, leviForm f x (coordinateVector p)

theorem coordCombination_single (p : Fin n) :
    coordCombination (Pi.single p (1 : ℂ)) = coordinateVector p := by
  simp only [coordCombination]
  rw [Finset.sum_eq_single p]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-- `u_{pp̄}(x)` is the `(p, p)` entry of the complex Hessian. -/
theorem leviForm_coordinateVector {f : ComplexModel n → ℝ} {x : ComplexModel n}
    (hf : ContDiffAt ℝ 2 f x) (p : Fin n) :
    ((leviForm f x (coordinateVector p) : ℝ) : ℂ) = complexHessian f x p p := by
  rw [← coordCombination_single, ← dotProduct_mulVec_complexHessian_eq_leviForm hf]
  simp [dotProduct, mulVec, Pi.single_apply]

/-- `Re tr Hess_ℂ f(x) = levTr f x`. -/
theorem re_trace_complexHessian {f : ComplexModel n → ℝ} {x : ComplexModel n}
    (hf : ContDiffAt ℝ 2 f x) : (complexHessian f x).trace.re = levTr f x := by
  rw [Matrix.trace, Complex.re_sum, levTr]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.diag_apply, ← leviForm_coordinateVector hf p, Complex.ofReal_re]

/-- The coordinate trace is additive. -/
theorem levTr_add {f g : ComplexModel n → ℝ} {x : ComplexModel n} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) : levTr (fun y => f y + g y) x = levTr f x + levTr g x := by
  simp only [levTr, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  exact leviForm_add (u := f) (v := g) hf hg _

theorem levTr_const_mul {f : ComplexModel n → ℝ} {x : ComplexModel n} (hf : ContDiffAt ℝ 2 f x)
    (c : ℝ) : levTr (fun y => c * f y) x = c * levTr f x := by
  simp only [levTr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  exact leviForm_smul hf c _

theorem levTr_congr {f g : ComplexModel n → ℝ} {x : ComplexModel n} (h : f =ᶠ[𝓝 x] g) :
    levTr f x = levTr g x := by
  simp only [levTr]
  refine Finset.sum_congr rfl fun p _ => ?_
  exact AubinYauUniformConstants.leviForm_congr h _

theorem leviForm_const_mul {f : ComplexModel n → ℝ} {x : ComplexModel n}
    (hf : ContDiffAt ℝ 2 f x) (c : ℝ) (v : ComplexModel n) :
    leviForm (fun y => c * f y) x v = c * leviForm f x v :=
  leviForm_smul hf c v

/-- A positive semidefinite matrix turns `Re tr(P · Hess_ℂ ·)` into a sum of Levi forms. -/
theorem exists_trace_eq_sum_leviForm {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosSemidef) :
    ∃ (m : ℕ) (w : Fin m → ComplexModel n),
      (∀ (f : ComplexModel n → ℝ) (x : ComplexModel n), ContDiffAt ℝ 2 f x →
        (P * complexHessian f x).trace.re = ∑ i, leviForm f x (w i)) ∧
      P.trace.re = ∑ i, ‖w i‖ ^ 2 := by
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hP
  exact ⟨m, fun i => coordCombination (v i), fun f x hf => re_trace_mul_complexHessian_eq_sum v hf,
    re_trace_sum_vecMulVec v⟩

/-! ### The flat Aubin–Yau inequality -/

/-- Weighted concavity of `log`: `∑ λₚ log zₚ ≤ log ∑ λₚ zₚ`. -/
theorem sum_mul_log_le_log_sum {ι : Type*} (s : Finset ι) {lam z : ι → ℝ}
    (hlam : ∀ i ∈ s, 0 ≤ lam i) (hsum : ∑ i ∈ s, lam i = 1) (hz : ∀ i ∈ s, 0 < z i) :
    ∑ i ∈ s, lam i * Real.log (z i) ≤ Real.log (∑ i ∈ s, lam i * z i) := by
  have h := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum hlam hsum (fun i hi => hz i hi)
  simpa only [smul_eq_mul] using h

/-- **The flat Aubin–Yau inequality.**  For a smooth `u` with positive definite complex Hessian `H`
at `x` (`n ≥ 1`):
`(∑ₚ (log det H)_{pp̄}(x)) / tr H(x) ≤ Re tr(H(x)⁻¹ · Hess_ℂ(log tr H)(x))`. -/
theorem levTr_logDet_div_le (hn : 0 < n) {u : ComplexModel n → ℝ} (hu : ContDiff ℝ ∞ u)
    {x : ComplexModel n} (hpos : (complexHessian u x).PosDef) :
    levTr (fun y => Real.log (complexHessian u y).det.re) x / levTr u x ≤
      ((complexHessian u x)⁻¹ * complexHessian (fun y => Real.log (levTr u y)) x).trace.re := by
  classical
  set P := (complexHessian u x)⁻¹ with hPdef
  have hP : P.PosSemidef := hpos.inv.posSemidef
  set ℓ : Fin n → ComplexModel n → ℝ := fun p y => leviForm u y (coordinateVector p) with hℓdef
  have hℓs : ∀ p, ContDiff ℝ ∞ (ℓ p) := fun p => contDiff_leviForm hu _
  have hLs : ContDiff ℝ ∞ (levTr u) := by
    have : levTr u = fun y => ∑ p, ℓ p y := rfl
    rw [this]
    exact ContDiff.sum fun p _ => hℓs p
  have hℓpos : ∀ p, 0 < ℓ p x := by
    intro p
    have hne : (Pi.single p (1 : ℂ) : Fin n → ℂ) ≠ 0 := by
      intro h
      have := congrFun h p
      simp at this
    have h1 := hpos.re_dotProduct_pos hne
    have h2 := dotProduct_mulVec_complexHessian_eq_leviForm (contDiffAt_two hu x)
      (Pi.single p (1 : ℂ))
    rw [coordCombination_single] at h2
    rw [h2] at h1
    simpa using h1
  have hLpos : 0 < levTr u x := by
    have hne : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
    exact Finset.sum_pos (fun p _ => hℓpos p) hne
  set L := levTr u x with hLdef
  set lam : Fin n → ℝ := fun p => ℓ p x / L with hlamdef
  have hlam0 : ∀ p, 0 < lam p := fun p => div_pos (hℓpos p) hLpos
  have hlam1 : ∑ p, lam p = 1 := by
    simp only [hlamdef, ← Finset.sum_div]
    exact div_self hLpos.ne'
  -- the comparison function and its local minimum
  set D : ComplexModel n → ℝ := fun y =>
    Real.log (levTr u y) - ∑ p, lam p * Real.log (ℓ p y) with hDdef
  have hev : ∀ᶠ y in 𝓝 x, ∀ p, 0 < ℓ p y := by
    rw [Filter.eventually_all]
    exact fun p => continuousAt_const.eventually_lt (hℓs p).continuous.continuousAt (hℓpos p)
  have hmin : IsLocalMax (fun y => -D y) x := by
    filter_upwards [hev] with y hy
    -- `D y ≥ D x` by the weighted AM–GM inequality
    have hDx : D x = -∑ p, lam p * Real.log (lam p) := by
      simp only [hDdef]
      have : ∀ p, Real.log (ℓ p x) = Real.log (lam p) + Real.log L := by
        intro p
        rw [← Real.log_mul (hlam0 p).ne' hLpos.ne']
        congr 1
        simp only [hlamdef]
        field_simp
      simp only [this, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hlam1, one_mul]
      ring
    have hjensen := sum_mul_log_le_log_sum Finset.univ (lam := lam)
      (z := fun p => ℓ p y / lam p) (fun p _ => (hlam0 p).le) hlam1
      (fun p _ => div_pos (hy p) (hlam0 p))
    have hsimp : ∑ p, lam p * (ℓ p y / lam p) = levTr u y := by
      simp only [levTr]
      refine Finset.sum_congr rfl fun p _ => ?_
      field_simp [(hlam0 p).ne']
      rfl
    rw [hsimp] at hjensen
    have hsplit : ∀ p, lam p * Real.log (ℓ p y / lam p) =
        lam p * Real.log (ℓ p y) - lam p * Real.log (lam p) := by
      intro p
      rw [Real.log_div (hy p).ne' (hlam0 p).ne']
      ring
    simp only [hsplit, Finset.sum_sub_distrib] at hjensen
    show -D y ≤ -D x
    rw [hDx]
    simp only [hDdef]
    linarith
  -- second-order information at the minimum
  have hlogL : ContDiffAt ℝ 2 (fun y => Real.log (levTr u y)) x :=
    (contDiffAt_two hLs x).log hLpos.ne'
  have hlogℓ : ∀ p, ContDiffAt ℝ 2 (fun y => Real.log (ℓ p y)) x := fun p =>
    (contDiffAt_two (hℓs p) x).log (hℓpos p).ne'
  have hS2 : ContDiffAt ℝ 2 (fun y => ∑ p, lam p * Real.log (ℓ p y)) x :=
    ContDiffAt.sum fun p _ => contDiffAt_const.mul (hlogℓ p)
  have hD2 : ContDiffAt ℝ 2 D x := hlogL.sub hS2
  have hlevD : ∀ v, 0 ≤ leviForm D x v := by
    intro v
    have h := SGPT.Okounkov.TranscendentalWNReg.leviForm_nonpos_of_isLocalMax hD2.neg hmin v
    have hneg : leviForm (fun y => -D y) x v = -leviForm D x v := leviForm_neg D x v
    rw [hneg] at h
    linarith
  obtain ⟨m, w, hw, -⟩ := exists_trace_eq_sum_leviForm hP
  have hTD : 0 ≤ (P * complexHessian D x).trace.re := by
    rw [hw D x hD2]
    exact Finset.sum_nonneg fun i _ => hlevD (w i)
  -- expand `T(D)`
  have hlevi : ∀ v, leviForm D x v = leviForm (fun y => Real.log (levTr u y)) x v -
      ∑ p, lam p * leviForm (fun y => Real.log (ℓ p y)) x v := by
    intro v
    have h1 := SGPT.Okounkov.TranscendentalWNReg.leviForm_sub' hlogL hS2 v
    rw [h1, ConcentrationPotentialLevi.leviForm_sum Finset.univ
      (fun p _ => contDiffAt_const.mul (hlogℓ p))]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    exact leviForm_smul (hlogℓ p) (lam p) v
  have hTD' : (P * complexHessian D x).trace.re =
      (P * complexHessian (fun y => Real.log (levTr u y)) x).trace.re -
        ∑ p, lam p * (P * complexHessian (fun y => Real.log (ℓ p y)) x).trace.re := by
    rw [hw D x hD2, hw _ x hlogL]
    simp only [hlevi, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hw _ x (hlogℓ p), Finset.mul_sum]
  -- Błocki in every coordinate direction
  have hblocki : ∀ p, leviForm (fun y => Real.log (complexHessian u y).det.re) x
      (coordinateVector p) / ℓ p x ≤
        (P * complexHessian (fun y => Real.log (ℓ p y)) x).trace.re := by
    intro p
    have hp0 : coordinateVector p ≠ (0 : ComplexModel n) := by
      intro h
      have := congrArg (fun v : ComplexModel n => v p) h
      simp [coordinateVector] at this
    exact blocki_local_estimate hu hpos hp0
  have hid : levTr (fun y => Real.log (complexHessian u y).det.re) x / L =
      ∑ p, lam p * (leviForm (fun y => Real.log (complexHessian u y).det.re) x
        (coordinateVector p) / ℓ p x) := by
    simp only [levTr, Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    have h1 := (hℓpos p).ne'
    have h2 := hLpos.ne'
    simp only [hlamdef]
    field_simp
  rw [hid]
  calc ∑ p, lam p * (leviForm (fun y => Real.log (complexHessian u y).det.re) x
        (coordinateVector p) / ℓ p x)
      ≤ ∑ p, lam p * (P * complexHessian (fun y => Real.log (ℓ p y)) x).trace.re :=
        Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hblocki p) (hlam0 p).le
    _ ≤ (P * complexHessian (fun y => Real.log (levTr u y)) x).trace.re := by linarith

/-! ### A barrier for the inverse metric -/

/-- `Re tr(M G) ≥ 0` for positive semidefinite `M`, `G`. -/
theorem re_trace_mul_nonneg {M G : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosSemidef)
    (hG : G.PosSemidef) : 0 ≤ (M * G).trace.re := by
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hG
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [trace_mul_vecMulVec]
  exact hM.re_dotProduct_nonneg _

/-- **Barrier for the inverse metric**: if `H` is positive definite with `H ≤ (1 + δ)·1` and `G` is
positive semidefinite, then `(1 - δ) Re tr G ≤ Re tr(H⁻¹ G)`. -/
theorem one_sub_mul_re_trace_le {H G : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef)
    (hG : G.PosSemidef) {δ : ℝ}
    (hδ : ∀ v : Fin n → ℂ, (star v ⬝ᵥ (H *ᵥ v)).re ≤ (1 + δ) * (star v ⬝ᵥ v).re) :
    (1 - δ) * G.trace.re ≤ (H⁻¹ * G).trace.re := by
  have hHu : IsUnit H.det := isUnit_iff_ne_zero.mpr hH.det_pos.ne'
  -- `H⁻¹ - 2 + H = (1 - H)ᴴ H⁻¹ (1 - H) ≥ 0`
  have hM : ((1 - H)ᴴ * H⁻¹ * (1 - H)).PosSemidef :=
    hH.inv.posSemidef.conjTranspose_mul_mul_same (1 - H)
  have hMeq : (1 - H)ᴴ * H⁻¹ * (1 - H) = H⁻¹ - 2 + H := by
    have hHh : Hᴴ = H := hH.isHermitian.eq
    have e1 : (1 - H) * H⁻¹ = H⁻¹ - 1 := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_nonsing_inv _ hHu]
    have e2 : (H⁻¹ - 1) * (1 - H) = H⁻¹ - 2 + H := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul,
        Matrix.nonsing_inv_mul _ hHu]
      rw [← one_add_one_eq_two]
      abel
    rw [conjTranspose_sub, conjTranspose_one, hHh, e1, e2]
  have h1 : 0 ≤ ((H⁻¹ - 2 + H) * G).trace.re := by
    rw [← hMeq]; exact re_trace_mul_nonneg hM hG
  -- `Re tr(H G) ≤ (1 + δ) Re tr G`
  have h2 : (H * G).trace.re ≤ (1 + δ) * G.trace.re := by
    obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hG
    rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum, Matrix.trace_sum, Complex.re_sum,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [trace_mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm (v i)]
    exact hδ (v i)
  have hexp : ((H⁻¹ - 2 + H) * G).trace.re =
      (H⁻¹ * G).trace.re - 2 * G.trace.re + (H * G).trace.re := by
    have h2G : ((2 : Matrix (Fin n) (Fin n) ℂ) * G).trace.re = 2 * G.trace.re := by
      rw [show (2 : Matrix (Fin n) (Fin n) ℂ) * G = G + G by rw [two_mul], Matrix.trace_add,
        Complex.add_re]
      ring
    rw [Matrix.add_mul, Matrix.sub_mul, Matrix.trace_add, Matrix.trace_sub, Complex.add_re,
      Complex.sub_re, h2G]
  rw [hexp] at h1
  linarith

/-! ### A second-order Taylor bound -/

/-- **Second-order Taylor bound**: if `f` is `C²` at `x` with `Df(x) = 0` and `‖D²f(x)‖ ≤ C`, then
`‖f y - f x‖ ≤ (C + 1) ‖y - x‖²` near `x`. -/
theorem norm_sub_le_of_fderiv_eq_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (hD : fderiv ℝ f x = 0) {C : ℝ} (hC : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C) :
    ∀ᶠ y in 𝓝 x, ‖f y - f x‖ ≤ (C + 1) * ‖y - x‖ ^ 2 := by
  have hdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
    (hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hD1 : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hlo := hD1.hasFDerivAt.isLittleO.bound (c := 1) one_pos
  have hbound : ∀ᶠ y in 𝓝 x, ‖fderiv ℝ f y‖ ≤ (C + 1) * ‖y - x‖ := by
    filter_upwards [hlo] with y hy
    rw [hD, sub_zero, one_mul] at hy
    have h1 : ‖fderiv ℝ (fderiv ℝ f) x (y - x)‖ ≤ C * ‖y - x‖ :=
      ((fderiv ℝ (fderiv ℝ f) x).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hC (norm_nonneg _))
    calc ‖fderiv ℝ f y‖ = ‖(fderiv ℝ f y - fderiv ℝ (fderiv ℝ f) x (y - x)) +
          fderiv ℝ (fderiv ℝ f) x (y - x)‖ := by rw [sub_add_cancel]
      _ ≤ ‖fderiv ℝ f y - fderiv ℝ (fderiv ℝ f) x (y - x)‖ +
          ‖fderiv ℝ (fderiv ℝ f) x (y - x)‖ := norm_add_le _ _
      _ ≤ ‖y - x‖ + C * ‖y - x‖ := add_le_add hy h1
      _ = (C + 1) * ‖y - x‖ := by ring
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hdiff.and hbound)
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  have hr : dist y x < δ := hy
  have hsub : closedBall x (dist y x) ⊆ ball x δ := closedBall_subset_ball hr
  have hC0 : 0 ≤ C := (norm_nonneg (fderiv ℝ (fderiv ℝ f) x)).trans hC
  have hmv := (convex_closedBall x (dist y x)).norm_image_sub_le_of_norm_fderiv_le
    (f := f) (C := (C + 1) * dist y x)
    (fun z hz => (hball (hsub hz)).1)
    (fun z hz => by
      refine (hball (hsub hz)).2.trans ?_
      have : ‖z - x‖ ≤ dist y x := by rw [← dist_eq_norm]; exact hz
      exact mul_le_mul_of_nonneg_left this (by linarith))
    (mem_closedBall_self dist_nonneg) (by rw [mem_closedBall])
  rw [dist_eq_norm] at hmv
  calc ‖f y - f x‖ ≤ (C + 1) * ‖y - x‖ * ‖y - x‖ := hmv
    _ = (C + 1) * ‖y - x‖ ^ 2 := by ring

/-! ### The maximum principle step -/

/-- **The maximum principle step of the trace estimate** (FPT `lem:penalized-equation-trace`,
Steps 2–3, in normal coordinates at the maximum point).  Let `ψ, σ` be smooth on `ℂⁿ` (`n ≥ 1`) with
`Hess_ℂ ψ(0) > 0` and `Hess_ℂ σ(0) = 1`, and suppose that the equation gives
`∑ₚ (log det Hess_ℂ ψ)_{pp̄}(0) ≥ β(tr Hess_ℂ ψ(0) - n - ∑ₚ F_{pp̄}(0)) - C₁` with
`∑ₚ F_{pp̄}(0) ≤ S`.  If `w ↦ log tr Hess_ℂ ψ(w) - 2K‖w‖² - a(ψ - σ)(w)` has a local maximum at
`0`, `a ≥ 2K + C₁` and `β > 2an`, then `tr Hess_ℂ ψ(0) ≤ 2(n + S)`. -/
theorem levTr_le_of_isLocalMax (hn : 0 < n) {ψ σ F : ComplexModel n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hσ : ContDiff ℝ ∞ σ)
    (hpos : (complexHessian ψ 0).PosDef) (hσ0 : complexHessian σ 0 = 1)
    {β K a C₁ S : ℝ} (hK : 0 ≤ K) (hC₁ : 0 ≤ C₁) (ha : 2 * K + C₁ ≤ a)
    (hβ : 2 * a * n < β)
    (hdetlow : β * (levTr ψ 0 - n - levTr F 0) - C₁ ≤
      levTr (fun w => Real.log (complexHessian ψ w).det.re) 0)
    (hFS : levTr F 0 ≤ S)
    (hmax : IsLocalMax (fun w => Real.log (levTr ψ w) - 2 * K * ‖w‖ ^ 2 - a * (ψ w - σ w)) 0) :
    levTr ψ 0 ≤ 2 * (n + S) := by
  classical
  set P := (complexHessian ψ 0)⁻¹ with hPdef
  have hP : P.PosSemidef := hpos.inv.posSemidef
  obtain ⟨m, w, hw, htrP⟩ := exists_trace_eq_sum_leviForm hP
  set trP := P.trace.re with htrPdef
  have htrP0 : 0 ≤ trP := by rw [htrP]; positivity
  have hψ2 := contDiffAt_two hψ (0 : ComplexModel n)
  have hσ2 := contDiffAt_two hσ (0 : ComplexModel n)
  -- `ℓ₀ = tr Hess ψ(0) > 0` and `n ≤ ℓ₀ tr P`
  have hℓpos : ∀ p : Fin n, 0 < leviForm ψ 0 (coordinateVector p) := by
    intro p
    have hne : (Pi.single p (1 : ℂ) : Fin n → ℂ) ≠ 0 := by
      intro h
      have := congrFun h p
      simp at this
    have h1 := hpos.re_dotProduct_pos hne
    have h2 := dotProduct_mulVec_complexHessian_eq_leviForm hψ2 (Pi.single p (1 : ℂ))
    rw [coordCombination_single] at h2
    rw [h2] at h1
    simpa using h1
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
  have hℓ₀ : 0 < levTr ψ 0 := Finset.sum_pos (fun p _ => hℓpos p) hne
  have hnℓ : (n : ℝ) ≤ levTr ψ 0 * trP := by
    have h1 : ∀ p : Fin n, 1 ≤ leviForm ψ 0 (coordinateVector p) * trP := by
      intro p
      have hnorm : ‖(coordinateVector p : ComplexModel n)‖ = 1 := by
        simp [coordinateVector]
      exact one_le_leviForm_mul_re_trace_inv hψ2 hpos hnorm
    have h2 := Finset.sum_le_sum fun p (_ : p ∈ Finset.univ) => h1 p
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      ← Finset.sum_mul] at h2
    exact h2
  -- the trace of the maximum
  have hL : ContDiff ℝ ∞ (levTr ψ) := by
    have : levTr ψ = fun y => ∑ p, leviForm ψ y (coordinateVector p) := rfl
    rw [this]
    exact ContDiff.sum fun p _ => contDiff_leviForm hψ _
  have hlogL : ContDiffAt ℝ 2 (fun w => Real.log (levTr ψ w)) 0 :=
    (contDiffAt_two hL 0).log hℓ₀.ne'
  have hsq : ContDiffAt ℝ 2 (fun w : ComplexModel n => ‖w‖ ^ 2) 0 :=
    (contDiff_norm_sq ℝ).contDiffAt
  have hΘ2 : ContDiffAt ℝ 2
      (fun w => Real.log (levTr ψ w) - 2 * K * ‖w‖ ^ 2 - a * (ψ w - σ w)) 0 :=
    (hlogL.sub (contDiffAt_const.mul hsq)).sub (contDiffAt_const.mul (hψ2.sub hσ2))
  have hT0 : (P * complexHessian
      (fun w => Real.log (levTr ψ w) - 2 * K * ‖w‖ ^ 2 - a * (ψ w - σ w)) 0).trace.re ≤ 0 := by
    rw [hw _ 0 hΘ2]
    exact Finset.sum_nonpos fun i _ =>
      SGPT.Okounkov.TranscendentalWNReg.leviForm_nonpos_of_isLocalMax hΘ2 hmax (w i)
  have hlevΘ : ∀ v, leviForm (fun w => Real.log (levTr ψ w) - 2 * K * ‖w‖ ^ 2 -
      a * (ψ w - σ w)) 0 v = leviForm (fun w => Real.log (levTr ψ w)) 0 v -
        2 * K * ‖v‖ ^ 2 - a * (leviForm ψ 0 v - leviForm σ 0 v) := by
    intro v
    rw [SGPT.Okounkov.TranscendentalWNReg.leviForm_sub' (hlogL.sub (contDiffAt_const.mul hsq))
      (contDiffAt_const.mul (hψ2.sub hσ2)),
      SGPT.Okounkov.TranscendentalWNReg.leviForm_sub' hlogL (contDiffAt_const.mul hsq),
      leviForm_const_mul hsq, leviForm_const_mul (hψ2.sub hσ2),
      SGPT.Okounkov.TranscendentalWNReg.leviForm_sub' hψ2 hσ2, leviForm_norm_sq]
  have hTΘ : (P * complexHessian
      (fun w => Real.log (levTr ψ w) - 2 * K * ‖w‖ ^ 2 - a * (ψ w - σ w)) 0).trace.re =
      (P * complexHessian (fun w => Real.log (levTr ψ w)) 0).trace.re - 2 * K * trP -
        a * ((P * complexHessian ψ 0).trace.re - (P * complexHessian σ 0).trace.re) := by
    rw [hw _ 0 hΘ2, hw _ 0 hlogL, hw _ 0 hψ2, hw _ 0 hσ2, htrP]
    simp only [hlevΘ, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hTψ : (P * complexHessian ψ 0).trace.re = n := by
    rw [hPdef, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hpos.det_pos.ne'),
      Matrix.trace_one]
    simp
  have hTσ : (P * complexHessian σ 0).trace.re = trP := by rw [hσ0, Matrix.mul_one]
  have hflat := levTr_logDet_div_le hn hψ hpos
  have hflat' := (div_le_div_of_nonneg_right hdetlow hℓ₀.le).trans hflat
  -- combine
  have hmain : (β * (levTr ψ 0 - n - levTr F 0) - C₁) / levTr ψ 0 -
      2 * K * trP - a * (n - trP) ≤ 0 := by
    have := hT0
    rw [hTΘ, hTψ, hTσ] at this
    linarith
  rw [div_sub' hℓ₀.ne', div_sub' hℓ₀.ne', div_le_iff₀ hℓ₀, zero_mul] at hmain
  by_contra hcon
  push Not at hcon
  have hβ0 : 0 < β := by
    have : 0 ≤ 2 * a * n := by
      have : 0 ≤ a := le_trans (by positivity) ha
      positivity
    linarith
  have hC1 : C₁ ≤ C₁ * (levTr ψ 0 * trP) := by
    have : (1 : ℝ) ≤ levTr ψ 0 * trP := le_trans (by exact_mod_cast hn) hnℓ
    nlinarith
  have hFle : levTr F 0 ≤ S := hFS
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : β * (levTr ψ 0 - n - S) ≤ a * n * levTr ψ 0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (mul_nonneg hℓ₀.le htrP0)]
  have h2 : β * levTr ψ 0 / 2 < β * (levTr ψ 0 - n - S) := by nlinarith
  have h3 : a * n * levTr ψ 0 < β * levTr ψ 0 / 2 := by nlinarith
  linarith

end SGPT.Envelopes.LapClass
