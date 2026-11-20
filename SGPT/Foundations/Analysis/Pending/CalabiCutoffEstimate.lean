import SGPT.Foundations.Analysis.Pending.CalabiLinearChange

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Calabi's third-order estimate on a ball: the cutoff argument

Let `u` be smooth on `ℂⁿ` with complex Hessian `H = (u_{jk̄})` positive definite on `ball c (2r)`,
`tr H ≤ Λ`, `tr H⁻¹ ≤ Λ` there, solving `log det H = f + εu` (`0 ≤ ε ≤ 1`) with
`|∂∂̄f|², Σ_m |∂_m∂∂̄f|² ≤ K₀` (Frobenius norms). Then the third derivatives of `u` are bounded on
`closedBall c r` by a constant depending only on `n, c, r, Λ, K₀` (`exists_sum_frob_dH_le`).

## Proof (Yau / Calabi, PSS `pss07-multiplier-krf:page-0008`–`page-0009`, interior version)

* `Q = η² S + K tr H`, `η` a bump (`1` on `closedBall c r`, `0` off `ball c (3r/2)`), `S = calabiS u`
  Calabi's quantity; `Q` attains its maximum on `closedBall c (3r/2)` at `x₀`.
* If `η(x₀) ≠ 0`, `x₀` is an interior local maximum. In the normalised coordinates of `x₀`
  (`CalabiLinearChange.exists_normalizing_clm`: `v = u ∘ L`, `H(v)(y₀) = 1`, `L y₀ = x₀`),
  `Q ∘ L = (η ∘ L)² S(v) + K tr(M H(v))` with the constant `M = (Lᵀ L̄)⁻¹`, and
  `Σ_p ∂_p∂̄_p (Q ∘ L)(y₀) ≤ 0`. Calabi's inequality (`calabi_inequality_at_one`) bounds `Δ S(v)` from
  below and `|∂S(v)|² ≤ 2 S G`; the cross term is absorbed by `η² G`; the trace term gives
  `tr(M (∂∂̄F + Σ_p X_p X_p*)) ≥ S/Λ - Λ |∂∂̄F|` (the twice differentiated equation). For `K` large this
  bounds `S(x₀)` (`calabiS_le_of_isLocalMax`).
* Hence `S ≤ Q(x₀) ≤ C` on `closedBall c r`, and `Σ_m |∂_m H|² ≤ (tr H)³ S` (`sum_frob_dH_le`).

Infrastructure: `C²` regularity of `S` where `det H ≠ 0` (`contDiffAt_calabiS`), the Leibniz rule for
`∂_v∂̄_v` (`wirt_wirt_mul`), reality of `S` and of `tr H` (`ofReal_re_calabiS`).

TN.4 B5, nonlinear track N4 (c) (the third-order Monge–Ampère estimate,
run-0171 section), blueprint `bou:yau-c3-estimate`.
-/

open Set Filter Matrix Complex Metric
open scoped Topology ContDiff ComplexConjugate ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.CalabiCutoffEstimate

open FirstPass FirstPass.MongeAmpere MixedHessian WirtingerLogDet CalabiFlatIdentity
  CalabiFlatLaplacian CalabiFlatEquation CalabiFlatInequality CalabiLinearChange

noncomputable section

/-! ### `C²` regularity -/

section Regularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*} [Fintype ι]
  [DecidableEq ι] {x : E}

/-- All entries of a matrix-valued function are `C²` at `x`. -/
def MC2At (M : E → Matrix ι ι ℂ) (x : E) : Prop := ∀ i j, ContDiffAt ℝ 2 (fun y => M y i j) x

theorem MC2At.mul {M N : E → Matrix ι ι ℂ} (hM : MC2At M x) (hN : MC2At N x) :
    MC2At (fun y => M y * N y) x := fun i j => by
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun k _ => (hM i k).mul (hN k j)

theorem MC2At.conjTranspose {M : E → Matrix ι ι ℂ} (hM : MC2At M x) :
    MC2At (fun y => (M y)ᴴ) x := fun i j => by
  simp only [conjTranspose_apply, RCLike.star_def]
  exact Complex.conjCLE.contDiff.contDiffAt.comp x (hM j i)

theorem contDiffAt_det {M : E → Matrix ι ι ℂ} (hM : MC2At M x) :
    ContDiffAt ℝ 2 (fun y => (M y).det) x := by
  simp_rw [det_eq_sum]
  exact ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun i _ => hM (σ i) i)

theorem MC2At.inv {M : E → Matrix ι ι ℂ} (hM : MC2At M x) (hx : (M x).det ≠ 0) :
    MC2At (fun y => (M y)⁻¹) x := fun i j => by
  simp_rw [inv_apply_eq]
  refine ((contDiffAt_det hM).inv hx).mul ?_
  simp_rw [adjugate_apply]
  refine contDiffAt_det fun a b => ?_
  by_cases h : a = j
  · subst h
    simp only [updateRow_self]
    exact contDiffAt_const
  · simp only [updateRow_ne h]
    exact hM a b

theorem MC2At.trace {M : E → Matrix ι ι ℂ} (hM : MC2At M x) :
    ContDiffAt ℝ 2 (fun y => (M y).trace) x := by
  simp only [Matrix.trace, Matrix.diag]
  exact ContDiffAt.sum fun i _ => hM i i

theorem contDiffAt_calabiForm {n : ℕ} {A B D : E → Mat n} {C Y : E → Fin n → Mat n}
    (hA : MC2At A x) (hB : MC2At B x) (hC : ∀ m, MC2At (fun y => C y m) x) (hD : MC2At D x)
    (hY : ∀ t, MC2At (fun y => Y y t) x) :
    ContDiffAt ℝ 2 (fun y => calabiForm (A y) (B y) (C y) (D y) (Y y)) x := by
  unfold calabiForm
  exact ContDiffAt.sum fun m _ => ContDiffAt.sum fun t _ =>
    (hA t m).mul (((hB.mul (hC m)).mul hD).mul (hY t)).trace

theorem mC2At_of_mSmooth {n : ℕ} {M : E → Mat n} (hM : MSmooth M) (x : E) : MC2At M x :=
  fun i j => (hM i j).contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

end Regularity

section CalabiS

variable {n : ℕ} {u : ComplexModel n → ℝ}

/-- `S` is `C²` where `det H ≠ 0`. -/
theorem contDiffAt_calabiS (hu : ContDiff ℝ ∞ u) {x : ComplexModel n}
    (hx : (complexHessian u x).det ≠ 0) : ContDiffAt ℝ 2 (calabiS u) x := by
  have hP := (mC2At_of_mSmooth (mSmooth_complexHessian hu) x).inv hx
  exact contDiffAt_calabiForm hP hP (fun m => mC2At_of_mSmooth (mSmooth_dH hu m) x) hP
    (fun t => (mC2At_of_mSmooth (mSmooth_dH hu t) x).conjTranspose)

theorem star_calabiS (hu : ContDiff ℝ ∞ u) (y : ComplexModel n) :
    star (calabiS u y) = calabiS u y := by
  unfold calabiS
  rw [star_calabiForm]
  have hP : ((complexHessian u y)⁻¹)ᴴ = (complexHessian u y)⁻¹ :=
    (isHermitian_complexHessian hu y).inv.eq
  simp only [hP, conjTranspose_conjTranspose]

/-- `S` is real. -/
theorem ofReal_re_calabiS (hu : ContDiff ℝ ∞ u) (y : ComplexModel n) :
    (((calabiS u y).re : ℝ) : ℂ) = calabiS u y :=
  Complex.conj_eq_iff_re.mp (star_calabiS hu y)

/-- `tr H` is real. -/
theorem ofReal_re_trace_complexHessian (hu : ContDiff ℝ ∞ u) (y : ComplexModel n) :
    (((complexHessian u y).trace.re : ℝ) : ℂ) = (complexHessian u y).trace := by
  have h : star (complexHessian u y).trace = (complexHessian u y).trace := by
    rw [← trace_conjTranspose, (isHermitian_complexHessian hu y).eq]
  exact Complex.conj_eq_iff_re.mp h

end CalabiS

/-! ### The Leibniz rule for `∂_v∂̄_v` -/

section Leibniz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {x v : E}

theorem differentiableAt_wirt {a : E → ℂ} (ha : ContDiffAt ℝ 2 a x) (c : ℂ) (w : E) :
    DifferentiableAt ℝ (wirt c w a) x := by
  have hD : DifferentiableAt ℝ (fderiv ℝ a) x :=
    (ha.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 : DifferentiableAt ℝ (fun y => fderiv ℝ a y w) x := hD.clm_apply (differentiableAt_const w)
  have h2 : DifferentiableAt ℝ (fun y => fderiv ℝ a y (I • w)) x :=
    hD.clm_apply (differentiableAt_const _)
  change DifferentiableAt ℝ (fun y => (fderiv ℝ a y w + c * fderiv ℝ a y (I • w)) / 2) x
  simp only [div_eq_mul_inv]
  exact (h1.fun_add (h2.const_mul c)).mul_const _

theorem eventually_differentiableAt {a : E → ℂ} (ha : ContDiffAt ℝ 2 a x) :
    ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ a y :=
  (ha.eventually (by simp)).mono fun _ hy => hy.differentiableAt (by norm_num)

theorem wirt_wirt_add {a b : E → ℂ} (ha : ContDiffAt ℝ 2 a x) (hb : ContDiffAt ℝ 2 b x) :
    wirt (-I) v (wirt I v (fun y => a y + b y)) x =
      wirt (-I) v (wirt I v a) x + wirt (-I) v (wirt I v b) x := by
  have hev : wirt I v (fun y => a y + b y) =ᶠ[𝓝 x] fun y => wirt I v a y + wirt I v b y := by
    filter_upwards [eventually_differentiableAt ha, eventually_differentiableAt hb] with y hay hby
    exact wirt_add hay hby
  rw [wirt_congr hev, wirt_add (differentiableAt_wirt ha I v) (differentiableAt_wirt hb I v)]

theorem wirt_wirt_const_mul {a : E → ℂ} (k : ℂ) (ha : ContDiffAt ℝ 2 a x) :
    wirt (-I) v (wirt I v (fun y => k * a y)) x = k * wirt (-I) v (wirt I v a) x := by
  have hev : wirt I v (fun y => k * a y) =ᶠ[𝓝 x] fun y => k * wirt I v a y := by
    filter_upwards [eventually_differentiableAt ha] with y hay
    exact wirt_const_mul k hay
  rw [wirt_congr hev, wirt_const_mul k (differentiableAt_wirt ha I v)]

/-- **The Leibniz rule** for `∂_v∂̄_v`. -/
theorem wirt_wirt_mul {a b : E → ℂ} (ha : ContDiffAt ℝ 2 a x) (hb : ContDiffAt ℝ 2 b x) :
    wirt (-I) v (wirt I v (fun y => a y * b y)) x =
      wirt (-I) v (wirt I v a) x * b x +
        (wirt I v a x * wirt (-I) v b x + wirt (-I) v a x * wirt I v b x) +
          a x * wirt (-I) v (wirt I v b) x := by
  have hev : wirt I v (fun y => a y * b y) =ᶠ[𝓝 x] fun y => wirt I v a y * b y + a y * wirt I v b y := by
    filter_upwards [eventually_differentiableAt ha, eventually_differentiableAt hb] with y hay hby
    exact wirt_mul hay hby
  have hda := ha.differentiableAt (by norm_num)
  have hdb := hb.differentiableAt (by norm_num)
  have hwa := differentiableAt_wirt ha I v
  have hwb := differentiableAt_wirt hb I v
  rw [wirt_congr hev, wirt_add (hwa.fun_mul hdb) (hda.fun_mul hwb), wirt_mul hwa hdb,
    wirt_mul hda hwb]
  ring

/-- `∂̄` of a real function is the conjugate of `∂`. -/
theorem wirt_I_ofReal {g : E → ℝ} (hg : DifferentiableAt ℝ g x) :
    wirt I v (fun y => (g y : ℂ)) x = conj (wirt (-I) v (fun y => (g y : ℂ)) x) := by
  have h := wirt_I_conj (v := v) (f := fun y => (g y : ℂ))
    (Complex.ofRealCLM.differentiableAt.comp x hg)
  simpa only [Complex.conj_ofReal] using h

end Leibniz

/-! ### Auxiliary bounds -/

section Aux

variable {n : ℕ}

theorem frob_add_le (A B : Mat n) : frob (A + B) ≤ 2 * frob A + 2 * frob B := by
  unfold frob
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Matrix.add_apply]
  have h := norm_add_le (A i j) (B i j)
  have h0 := norm_nonneg (A i j + B i j)
  nlinarith [norm_nonneg (A i j), norm_nonneg (B i j), sq_nonneg (‖A i j‖ - ‖B i j‖)]

theorem frob_smul_one (ε : ℝ) : frob ((ε : ℂ) • (1 : Mat n)) = n * ε ^ 2 := by
  unfold frob
  simp [Matrix.one_apply, apply_ite, Finset.sum_ite_eq]

theorem complexHessian_add_const {g : ComplexModel n → ℝ} (hg : ContDiff ℝ ∞ g) (a : ℝ) :
    complexHessian (fun z => g z + a) = complexHessian g := by
  funext z
  rw [AubinYauLocalStep.complexHessian_fun_add (AubinYauLocalStep.contDiffAt_two hg z)
    contDiffAt_const, complexHessian_const, add_zero]

theorem norm_trace_sandwich_le (L A : Mat n) :
    ‖(Lᵀ * A * L.map (starRingEnd ℂ)).trace‖ ≤ frob L * √(frob A) := by
  rw [trace_mul_comm, ← Matrix.mul_assoc]
  refine (norm_trace_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  have h : frob (L.map (starRingEnd ℂ) * Lᵀ) ≤ frob L ^ 2 := by
    refine (frob_mul_le _ _).trans (le_of_eq ?_)
    rw [frob_map_conj, frob_transpose, sq]
  calc √(frob (L.map (starRingEnd ℂ) * Lᵀ)) ≤ √(frob L ^ 2) := Real.sqrt_le_sqrt h
    _ = frob L := Real.sqrt_sq (frob_nonneg _)

theorem sum_norm_wirt_comp_clm_sq_le (L : ComplexModel n →L[ℂ] ComplexModel n)
    {g : ComplexModel n → ℂ} {y : ComplexModel n} (hg : DifferentiableAt ℝ g (L y)) :
    ∑ p, ‖wirt (-I) (coordinateVector p) (fun z => g (L z)) y‖ ^ 2 ≤
      frob (lmat L) * ∑ a, ‖wirt (-I) (coordinateVector a) g (L y)‖ ^ 2 := by
  have h : ∀ p, wirt (-I) (coordinateVector p) (fun z => g (L z)) y =
      ∑ a, lmat L a p * wirt (-I) (coordinateVector a) g (L y) := by
    intro p
    rw [wirt_comp_clm L hg, AubinYauUniformConstants.wirt_negI_sum_dir]
    rfl
  simp only [h]
  calc ∑ p, ‖∑ a, lmat L a p * wirt (-I) (coordinateVector a) g (L y)‖ ^ 2
      ≤ ∑ p, (∑ a, ‖lmat L a p‖ ^ 2) * ∑ a, ‖wirt (-I) (coordinateVector a) g (L y)‖ ^ 2 :=
        Finset.sum_le_sum fun p _ => norm_sum_mul_sq_le' _ _
    _ = frob (lmat L) * ∑ a, ‖wirt (-I) (coordinateVector a) g (L y)‖ ^ 2 := by
        rw [← Finset.sum_mul]
        congr 1
        unfold frob
        exact Finset.sum_comm

theorem re_trace_sandwich_inv_nonneg (L Y : Mat n) :
    0 ≤ ((Lᵀ * L.map (starRingEnd ℂ))⁻¹ * (Y * Yᴴ)).trace.re := by
  have hRt : Lᵀ = (L.map (starRingEnd ℂ))ᴴ := by ext; simp [conjTranspose_apply]
  rw [hRt]
  set R : Mat n := L.map (starRingEnd ℂ)
  have htr : ((Rᴴ * R)⁻¹ * (Y * Yᴴ)).trace = (frob (Rᴴ⁻¹ * Y) : ℂ) := by
    rw [← trace_mul_conjTranspose_self, conjTranspose_mul, conjTranspose_nonsing_inv,
      conjTranspose_conjTranspose, Matrix.mul_inv_rev, Matrix.mul_assoc, trace_mul_comm,
      Matrix.mul_assoc, Matrix.mul_assoc]
    simp only [Matrix.mul_assoc]
  rw [htr, Complex.ofReal_re]
  exact frob_nonneg _

/-- `-2 |α| |β| ≤ Re Σ (ᾱ β + α β̄)`. -/
theorem neg_le_re_sum_conj_mul {ι : Type*} [Fintype ι] (α β : ι → ℂ) :
    -(2 * (√(∑ p, ‖α p‖ ^ 2) * √(∑ p, ‖β p‖ ^ 2))) ≤
      (∑ p, (starRingEnd ℂ (α p) * β p + α p * starRingEnd ℂ (β p))).re := by
  have h1 : ∀ p, -(2 * (‖α p‖ * ‖β p‖)) ≤
      (starRingEnd ℂ (α p) * β p + α p * starRingEnd ℂ (β p)).re := by
    intro p
    have h2 : ‖starRingEnd ℂ (α p) * β p + α p * starRingEnd ℂ (β p)‖ ≤ 2 * (‖α p‖ * ‖β p‖) := by
      refine (norm_add_le _ _).trans ?_
      simp only [norm_mul, Complex.norm_conj]
      linarith
    have h3 := Complex.abs_re_le_norm (starRingEnd ℂ (α p) * β p + α p * starRingEnd ℂ (β p))
    have h4 := neg_abs_le (starRingEnd ℂ (α p) * β p + α p * starRingEnd ℂ (β p)).re
    linarith
  rw [Complex.re_sum]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun p => ‖α p‖) (fun p => ‖β p‖)
  calc -(2 * (√(∑ p, ‖α p‖ ^ 2) * √(∑ p, ‖β p‖ ^ 2)))
      ≤ ∑ p, -(2 * (‖α p‖ * ‖β p‖)) := by
        rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
        linarith
    _ ≤ _ := Finset.sum_le_sum fun p _ => h1 p

end Aux

/-! ### The trace term -/

section Trace

variable {n : ℕ} {v : ComplexModel n → ℝ}

/-- `Σ_p ∂_p∂̄_p tr(M H) = tr(M Σ_p ∂̄_p∂_p H)` for a constant `M`. -/
theorem sum_wirt_wirt_trace_mul (hv : ContDiff ℝ ∞ v) (M : Mat n) (y : ComplexModel n) :
    ∑ p, wirt (-I) (coordinateVector p) (wirt I (coordinateVector p)
        (fun z => (M * complexHessian v z).trace)) y = (M * ∑ p, dZ v p p y).trace := by
  have hH := mSmooth_complexHessian hv
  have hM : ∀ z, MDiffAt (fun _ : ComplexModel n => M) z := fun z i j => differentiableAt_const _
  have h1 : ∀ p, wirt I (coordinateVector p) (fun z => (M * complexHessian v z).trace) =
      fun z => (M * (dH v p z)ᴴ).trace := by
    intro p
    funext z
    rw [wirt_trace ((hM z).mul (hH.mdiffAt z)), wirtM_mul (hM z) (hH.mdiffAt z), wirtM_const,
      wirtM_I_complexHessian hv, Matrix.zero_mul, zero_add]
    rfl
  rw [Matrix.mul_sum, trace_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hX := (mSmooth_dH hv p).conjTranspose.mdiffAt y
  rw [h1 p, wirt_trace ((hM y).mul hX), wirtM_mul (hM y) hX, wirtM_const,
    wirtM_negI_conjTranspose ((mSmooth_dH hv p).mdiffAt y), Matrix.zero_mul, zero_add]
  exact congrArg (fun A => (M * A).trace) (dZ_conjTranspose hv p p y)

/-- At a point with `H = 1`, for a solution of `log det H = F`:
`Σ_p ∂̄_p∂_p H = ∂∂̄F + Σ_p X_p X_p*`. -/
theorem sum_dZ_diag {F : ComplexModel n → ℝ} (hv : ContDiff ℝ ∞ v) (hF : ContDiff ℝ ∞ F)
    {y : ComplexModel n} (hy : complexHessian v y = 1)
    (heq : ∀ᶠ z in 𝓝 y, Real.log (complexHessian v z).det.re = F z) :
    ∑ p, dZ v p p y = complexHessian F y + ∑ p, dH v p y * (dH v p y)ᴴ := by
  have h1 : ∑ p, dZ v p p y = Matrix.of fun a b => (dZ v a b y).trace :=
    sum_diag_eq_trace (fun m q => dZ v m q y) (fun m q a b => dZ_symm hv m q a b y)
      (fun m q a b => dZ_symm' hv m q a b y)
  have h2 : ∑ p, dH v p y * (dH v p y)ᴴ = Matrix.of fun t m => (dH v t y * (dH v m y)ᴴ).trace :=
    sum_mul_conjTranspose_self (fun m => dH v m y) (fun m a b => congrFun (dH_symm hv m a b) y)
  rw [h1, h2]
  ext a b
  simp only [Matrix.of_apply, Matrix.add_apply]
  rw [complexHessian_at hv hF hy heq a b]
  ring

end Trace

/-! ### The estimate at an interior maximum -/

section Max

/-- The real-number endgame at the maximum point. -/
theorem real_endgame {S G η0 A B D grad Lapa Cr LapS TT K Λ E1 E2 Bb Fb Ab : ℝ}
    (hS : 0 ≤ S) (hG : 0 ≤ G) (hη0 : 0 ≤ η0) (hη1 : η0 ≤ 1) (hA : 0 ≤ A) (hAb : A ≤ Ab)
    (hB : 0 ≤ B) (hBb : B ≤ Bb) (hD : 0 ≤ D) (hDb : D ≤ Λ * E1)
    (hgrad : grad ≤ 2 * S * G) (hLapa : |Lapa| ≤ Λ * √E2)
    (hCr : -(4 * η0 * √D * √grad) ≤ Cr) (hLapS : G - 2 * A * √S - B * S ≤ LapS)
    (hTT : S / Λ - Λ * √Fb ≤ TT) (hΛ : 1 ≤ Λ) (hK : Λ * (Λ * √E2 + 8 * Λ * E1 + Bb + 1) ≤ K)
    (htot : Lapa * S + Cr + η0 ^ 2 * LapS + K * TT ≤ 0) :
    S ≤ 4 * Ab ^ 2 + 2 * K * Λ * √Fb := by
  have hΛ0 : 0 < Λ := lt_of_lt_of_le one_pos hΛ
  have hsS := Real.sq_sqrt hS
  have hsS0 := Real.sqrt_nonneg S
  have hsD := Real.sq_sqrt hD
  have hsD0 := Real.sqrt_nonneg D
  have hsG := Real.sq_sqrt hG
  have hsG0 := Real.sqrt_nonneg G
  have hE2 := Real.sqrt_nonneg E2
  have hFb := Real.sqrt_nonneg Fb
  have hE1 : 0 ≤ Λ * E1 := hD.trans hDb
  -- the Laplacian of the cutoff
  have h1 : -(Λ * √E2 * S) ≤ Lapa * S := by
    have h := neg_abs_le Lapa
    have h' : -(Λ * √E2) ≤ Lapa := by linarith
    have := mul_le_mul_of_nonneg_right h' hS
    linarith
  -- the cross term
  have hsgrad : √grad ≤ √2 * √S * √G := by
    rw [← Real.sqrt_mul (by norm_num), ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h2 : 4 * η0 * √D * √grad ≤ η0 ^ 2 * G + 8 * D * S := by
    have h := mul_le_mul_of_nonneg_left hsgrad
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hη0) hsD0)
    have e1 : 4 * η0 * √D * (√2 * √S * √G) = 2 * (η0 * √G) * (2 * √2 * √D * √S) := by ring
    have e2 : (η0 * √G) ^ 2 = η0 ^ 2 * G := by rw [mul_pow, hsG]
    have e3 : (2 * √2 * √D * √S) ^ 2 = 8 * D * S := by
      rw [mul_pow, mul_pow, mul_pow, hs2, hsD, hsS]; ring
    have := two_mul_le_add_sq (η0 * √G) (2 * √2 * √D * √S)
    linarith
  -- the third-order term
  have h3 : η0 ^ 2 * G - (2 * A * √S + B * S) ≤ η0 ^ 2 * LapS := by
    have he : η0 ^ 2 ≤ 1 := pow_le_one₀ hη0 hη1
    have h := mul_le_mul_of_nonneg_left hLapS (sq_nonneg η0)
    have hAS : 0 ≤ 2 * A * √S + B * S :=
      add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA) hsS0) (mul_nonneg hB hS)
    have h5 : η0 ^ 2 * (2 * A * √S + B * S) ≤ 2 * A * √S + B * S := mul_le_of_le_one_left hAS he
    have e : η0 ^ 2 * (G - 2 * A * √S - B * S) =
        η0 ^ 2 * G - η0 ^ 2 * (2 * A * √S + B * S) := by ring
    linarith
  -- the trace term
  have hBb0 : 0 ≤ Bb := hB.trans hBb
  have hin : 0 ≤ Λ * √E2 + 8 * (Λ * E1) + Bb + 1 := by
    have := mul_nonneg hΛ0.le hE2
    linarith
  have hK0 : 0 ≤ K := by
    have : 0 ≤ Λ * (Λ * √E2 + 8 * Λ * E1 + Bb + 1) := by
      refine mul_nonneg hΛ0.le ?_
      have := mul_nonneg hΛ0.le hE2
      linarith
    linarith
  have h4 : K * (S / Λ) - K * (Λ * √Fb) ≤ K * TT := by
    have := mul_le_mul_of_nonneg_left hTT hK0
    linarith
  have hKS : Λ * √E2 * S + 8 * D * S + B * S + S ≤ K * (S / Λ) := by
    have hk : Λ * (Λ * √E2 + 8 * D + B + 1) ≤ K := by
      refine le_trans ?_ hK
      refine mul_le_mul_of_nonneg_left ?_ hΛ0.le
      linarith
    have hk' : Λ * √E2 + 8 * D + B + 1 ≤ K / Λ := by
      rw [le_div_iff₀ hΛ0]; linarith
    have := mul_le_mul_of_nonneg_right hk' hS
    have e : K / Λ * S = K * (S / Λ) := by ring
    linarith
  -- conclusion
  have hfin : S - 2 * A * √S ≤ K * (Λ * √Fb) := by linarith
  have hAS : 2 * A * √S ≤ 2 * A ^ 2 + S / 2 := by
    have := sq_nonneg (2 * A - √S)
    nlinarith
  have hAA : A ^ 2 ≤ Ab ^ 2 := pow_le_pow_left₀ hA hAb 2
  have e : K * (Λ * √Fb) = K * Λ * √Fb := by ring
  linarith

variable {n : ℕ}

/-- **Calabi's quantity at an interior maximum of `η² S + K tr H`** (N4.c, the core of the cutoff
argument): with the Frobenius bounds `|∂∂̄f|² ≤ K₀`, `Σ|∂∂∂̄f|² ≤ K₀` of the right-hand side of
`log det H = f + εu`, `tr H, tr H⁻¹ ≤ Λ` at the maximum point, and the bounds `E1, E2` of the cutoff,
`S(x₀) ≤ 4Λ³K₀ + 2KΛ√(2Λ²K₀ + 2n)` once `K` is large. -/
theorem calabiS_le_of_isLocalMax {u f η : ComplexModel n → ℝ} {ε Λ K₀ E1 E2 K : ℝ}
    (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f) (hη : ContDiff ℝ ∞ η)
    (hη0 : ∀ z, 0 ≤ η z) (hη1 : ∀ z, η z ≤ 1)
    (hE1 : ∀ z, ∑ a, ‖wirt (-I) (coordinateVector a) (fun y => (η y : ℂ)) z‖ ^ 2 ≤ E1)
    (hE2 : ∀ z, frob (complexHessian (fun y => η y ^ 2) z) ≤ E2)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hΛ : 1 ≤ Λ) (hK₀ : 0 ≤ K₀)
    (hK : Λ * (Λ * √E2 + 8 * Λ * E1 + (n + 2) * √(2 * Λ ^ 2 * K₀ + 2 * n) + 1) ≤ K)
    {x₀ : ComplexModel n} (hpos : (complexHessian u x₀).PosDef)
    (htr : (complexHessian u x₀).trace.re ≤ Λ) (htri : ((complexHessian u x₀)⁻¹).trace.re ≤ Λ)
    (heq : ∀ᶠ z in 𝓝 x₀, Real.log (complexHessian u z).det.re = f z + ε * u z)
    (hf2 : frob (complexHessian f x₀) ≤ K₀) (hf3 : ∑ m, frob (dH f m x₀) ≤ K₀)
    (hmax : IsLocalMax
      (fun z => η z ^ 2 * (calabiS u z).re + K * (complexHessian u z).trace.re) x₀) :
    (calabiS u x₀).re ≤ 4 * (Λ ^ 3 * K₀) + 2 * K * Λ * √(2 * Λ ^ 2 * K₀ + 2 * n) := by
  classical
  set Fb : ℝ := 2 * Λ ^ 2 * K₀ + 2 * n with hFbdef
  have hΛ0 : 0 < Λ := lt_of_lt_of_le one_pos hΛ
  have hE10 : 0 ≤ E1 := (Finset.sum_nonneg fun _ _ => sq_nonneg _).trans (hE1 0)
  have hFb0 : 0 ≤ Fb := by positivity
  -- normalised coordinates at `x₀`
  obtain ⟨L, y₀, hLy, hdet, hH1, hfL, hfLi, hMlow, hMtr⟩ := exists_normalizing_clm hu hpos
  have hfL' : frob (lmat L) ≤ Λ := by rw [hfL]; exact htri
  have hfLi' : frob (lmat L)⁻¹ ≤ Λ := by rw [hfLi]; exact htr
  have hLc : Continuous L := L.continuous
  have hv : ContDiff ℝ ∞ (fun z => u (L z)) := contDiff_comp_clm L hu
  have hfLs : ContDiff ℝ ∞ (fun z => f (L z)) := contDiff_comp_clm L hf
  have hfv : ContDiff ℝ ∞ (fun z => f (L z) + Real.log (Complex.normSq (lmat L).det)) :=
    hfLs.add contDiff_const
  have hHfv : complexHessian (fun z => f (L z) + Real.log (Complex.normSq (lmat L).det)) =
      complexHessian (fun z => f (L z)) := complexHessian_add_const hfLs _
  -- the equation in the new coordinates
  have hpull : ∀ {P : ComplexModel n → Prop}, (∀ᶠ z in 𝓝 x₀, P z) → ∀ᶠ y in 𝓝 y₀, P (L y) := by
    intro P h
    have h' : ∀ᶠ z in 𝓝 (L y₀), P z := by rw [hLy]; exact h
    exact hLc.continuousAt.tendsto.eventually h'
  have hD0 : 0 < (complexHessian u x₀).det.re := (Complex.pos_iff.mp hpos.det_pos).1
  have hDpos : ∀ᶠ z in 𝓝 x₀, 0 < (complexHessian u z).det.re := by
    have hc : Continuous (fun z => (complexHessian u z).det.re) :=
      (Complex.reCLM.contDiff.comp (contDiff_det_complexHessian hu)).continuous
    exact continuousAt_const.eventually_lt hc.continuousAt hD0
  have hnorm : 0 < Complex.normSq (lmat L).det := Complex.normSq_pos.mpr hdet
  have heqv : ∀ᶠ y in 𝓝 y₀, Real.log (complexHessian (fun z => u (L z)) y).det.re =
      (f (L y) + Real.log (Complex.normSq (lmat L).det)) + ε * u (L y) := by
    filter_upwards [hpull heq, hpull hDpos] with y hy hy'
    rw [det_complexHessian_comp_clm L hu y, Complex.re_ofReal_mul,
      Real.log_mul hnorm.ne' hy'.ne', hy]
    ring
  -- Calabi's inequality at `y₀`
  obtain ⟨G, hG0, hgrad, hlap⟩ := calabi_inequality_at_one hv hH1 hfv hε0 heqv
  rw [hHfv] at hlap
  -- Calabi's quantity
  have hSv : calabiS (fun z => u (L z)) y₀ = calabiS u x₀ := by
    rw [calabiS_comp_clm L hu hdet, hLy]
  set S : ℝ := (calabiS u x₀).re with hSdef
  have hS_eq : S = ∑ m, frob (dH (fun z => u (L z)) m y₀) := by
    rw [hSdef, ← hSv, calabiS_at_one hv hH1, Complex.ofReal_re]
  have hS0 : 0 ≤ S := by rw [hS_eq]; exact Finset.sum_nonneg fun _ _ => frob_nonneg _
  rw [hSv, ← hSdef] at hgrad hlap
  -- bounds for the right-hand side
  have hA2 : ∑ m, frob (wirtM (-I) (coordinateVector m) (complexHessian fun z => f (L z)) y₀) ≤
      Λ ^ 3 * K₀ := by
    have e : ∀ m, wirtM (-I) (coordinateVector m) (complexHessian fun z => f (L z)) y₀ =
        transform (lmat L) (fun r => dH f r (L y₀)) m := fun m => dH_comp_clm L hf m y₀
    simp only [e]
    refine (sum_frob_transform_le _ _).trans ?_
    rw [hLy]
    exact mul_le_mul (pow_le_pow_left₀ (frob_nonneg _) hfL' 3) hf3
      (Finset.sum_nonneg fun _ _ => frob_nonneg _) (by positivity)
  have hF2 : frob (complexHessian (fun z => f (L z)) y₀) ≤ Λ ^ 2 * K₀ := by
    rw [complexHessian_comp_clm L hf, hLy]
    exact (frob_sandwich_le _ _).trans
      (mul_le_mul (pow_le_pow_left₀ (frob_nonneg _) hfL' 2) hf2 (frob_nonneg _) (by positivity))
  have hFe : frob (complexHessian (fun z => f (L z)) y₀ + (ε : ℂ) • 1) ≤ Fb := by
    refine (frob_add_le _ _).trans ?_
    rw [frob_smul_one]
    have hε2 : ε ^ 2 ≤ 1 := pow_le_one₀ hε0 hε1
    have : (n : ℝ) * ε ^ 2 ≤ n := mul_le_of_le_one_right (Nat.cast_nonneg n) hε2
    rw [hFbdef]
    linarith
  -- the maximum principle for `Q ∘ L` at `y₀`
  have hdetx : (complexHessian u x₀).det ≠ 0 := hpos.det_pos.ne'
  have hQ2 : ContDiffAt ℝ 2
      (fun z => η z ^ 2 * (calabiS u z).re + K * (complexHessian u z).trace.re) x₀ := by
    have h1 : ContDiffAt ℝ 2 (fun z => η z ^ 2) x₀ := (AubinYauLocalStep.contDiffAt_two hη x₀).pow 2
    have h2 : ContDiffAt ℝ 2 (fun z => (calabiS u z).re) x₀ :=
      Complex.reCLM.contDiff.contDiffAt.comp x₀ (contDiffAt_calabiS hu hdetx)
    have h3 : ContDiffAt ℝ 2 (fun z => (complexHessian u z).trace.re) x₀ :=
      Complex.reCLM.contDiff.contDiffAt.comp x₀
        (mC2At_of_mSmooth (mSmooth_complexHessian hu) x₀).trace
    exact (h1.mul h2).add (contDiffAt_const.mul h3)
  set QL : ComplexModel n → ℝ := fun y =>
    η (L y) ^ 2 * (calabiS u (L y)).re + K * (complexHessian u (L y)).trace.re with hQLdef
  have hQL2 : ContDiffAt ℝ 2 QL y₀ := by
    have h : ContDiffAt ℝ 2
        (fun z => η z ^ 2 * (calabiS u z).re + K * (complexHessian u z).trace.re) (L y₀) := by
      rw [hLy]; exact hQ2
    exact h.comp y₀ (L.restrictScalars ℝ).contDiff.contDiffAt
  have hmaxL : IsLocalMax QL y₀ := by
    have h : IsLocalMax
        (fun z => η z ^ 2 * (calabiS u z).re + K * (complexHessian u z).trace.re) (L y₀) := by
      rw [hLy]; exact hmax
    exact h.comp_continuous hLc.continuousAt
  have htr0 : (complexHessian QL y₀).trace.re ≤ 0 := by
    have h := AubinYauMatrixBounds.re_trace_mul_complexHessian_nonpos hQL2 hmaxL
      Matrix.PosDef.one.posSemidef
    rwa [Matrix.one_mul] at h
  -- `Q ∘ L` as a complex function
  set M : Mat n := ((lmat L)ᵀ * (lmat L).map (starRingEnd ℂ))⁻¹ with hMdef
  have hreal : (fun y => ((QL y : ℝ) : ℂ)) = fun y =>
      ((η (L y) ^ 2 : ℝ) : ℂ) * calabiS (fun z => u (L z)) y +
        (K : ℂ) * (M * complexHessian (fun z => u (L z)) y).trace := by
    funext y
    simp only [hQLdef]
    push_cast
    rw [ofReal_re_calabiS hu, ofReal_re_trace_complexHessian hu, calabiS_comp_clm L hu hdet,
      trace_complexHessian_comp_clm L hu hdet]
  have hsum : (complexHessian QL y₀).trace = ∑ p, wirt (-I) (coordinateVector p)
      (wirt I (coordinateVector p) (fun y => ((QL y : ℝ) : ℂ))) y₀ := by
    simp only [Matrix.trace, Matrix.diag]
    exact Finset.sum_congr rfl fun p _ => complexHessian_eq_wirt hQL2 p p
  rw [hreal] at hsum
  -- regularity of the three pieces
  have hηL : ContDiff ℝ ∞ (fun y => η (L y)) := contDiff_comp_clm L hη
  have ha2 : ContDiffAt ℝ 2 (fun y => ((η (L y) ^ 2 : ℝ) : ℂ)) y₀ :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp y₀ ((AubinYauLocalStep.contDiffAt_two hηL y₀).pow 2)
  have hdet1 : (complexHessian (fun z => u (L z)) y₀).det ≠ 0 := by
    rw [hH1, det_one]; exact one_ne_zero
  have hS2 : ContDiffAt ℝ 2 (calabiS (fun z => u (L z))) y₀ := contDiffAt_calabiS hv hdet1
  have hT2 : ContDiffAt ℝ 2 (fun y => (M * complexHessian (fun z => u (L z)) y).trace) y₀ := by
    have hMc : MC2At (fun _ : ComplexModel n => M) y₀ := fun i j => contDiffAt_const
    exact (hMc.mul (mC2At_of_mSmooth (mSmooth_complexHessian hv) y₀)).trace
  -- the Leibniz expansion
  have hdec : ∀ p, wirt (-I) (coordinateVector p) (wirt I (coordinateVector p) (fun y =>
      ((η (L y) ^ 2 : ℝ) : ℂ) * calabiS (fun z => u (L z)) y +
        (K : ℂ) * (M * complexHessian (fun z => u (L z)) y).trace)) y₀ =
      wirt (-I) (coordinateVector p) (wirt I (coordinateVector p)
          (fun y => ((η (L y) ^ 2 : ℝ) : ℂ))) y₀ * calabiS (fun z => u (L z)) y₀ +
        (wirt I (coordinateVector p) (fun y => ((η (L y) ^ 2 : ℝ) : ℂ)) y₀ *
            wirt (-I) (coordinateVector p) (calabiS (fun z => u (L z))) y₀ +
          wirt (-I) (coordinateVector p) (fun y => ((η (L y) ^ 2 : ℝ) : ℂ)) y₀ *
            wirt I (coordinateVector p) (calabiS (fun z => u (L z))) y₀) +
        ((η (L y₀) ^ 2 : ℝ) : ℂ) * wirt (-I) (coordinateVector p) (wirt I (coordinateVector p)
          (calabiS (fun z => u (L z)))) y₀ +
        (K : ℂ) * wirt (-I) (coordinateVector p) (wirt I (coordinateVector p)
          (fun y => (M * complexHessian (fun z => u (L z)) y).trace)) y₀ := by
    intro p
    rw [wirt_wirt_add (ha2.mul hS2) (contDiffAt_const.mul hT2), wirt_wirt_mul ha2 hS2,
      wirt_wirt_const_mul _ hT2]
  rw [Finset.sum_congr rfl fun p _ => hdec p, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  -- the values at `y₀`
  have hSvS : calabiS (fun z => u (L z)) y₀ = (S : ℂ) := by rw [hSv, hSdef, ofReal_re_calabiS hu]
  have hηy : η (L y₀) = η x₀ := by rw [hLy]
  rw [hsum, hSvS, hηy] at htr0
  simp only [Complex.add_re, Complex.re_mul_ofReal, Complex.re_ofReal_mul] at htr0
  -- (i) the Laplacian of the cutoff
  have hηsq : ContDiff ℝ ∞ (fun y => η (L y) ^ 2) := hηL.pow 2
  have hLapa : |(∑ p, wirt (-I) (coordinateVector p) (wirt I (coordinateVector p)
      (fun y => ((η (L y) ^ 2 : ℝ) : ℂ))) y₀).re| ≤ Λ * √E2 := by
    have h : complexHessian (fun y => η (L y) ^ 2) y₀ =
        (lmat L)ᵀ * complexHessian (fun y => η y ^ 2) (L y₀) * (lmat L).map (starRingEnd ℂ) :=
      complexHessian_comp_clm L (hη.pow 2) y₀
    rw [hLy] at h
    have hsumH : ∑ p, wirt (-I) (coordinateVector p) (wirt I (coordinateVector p)
        (fun y => ((η (L y) ^ 2 : ℝ) : ℂ))) y₀ = (complexHessian (fun y => η (L y) ^ 2) y₀).trace := by
      simp only [Matrix.trace, Matrix.diag]
      exact Finset.sum_congr rfl fun p _ =>
        (complexHessian_eq_wirt (AubinYauLocalStep.contDiffAt_two hηsq y₀) p p).symm
    rw [hsumH, h]
    refine (Complex.abs_re_le_norm _).trans ((norm_trace_sandwich_le _ _).trans ?_)
    exact mul_le_mul hfL' (Real.sqrt_le_sqrt (hE2 x₀)) (Real.sqrt_nonneg _) hΛ0.le
  -- (ii) the cross term
  have hconj_a : ∀ p, wirt I (coordinateVector p) (fun y => ((η (L y) ^ 2 : ℝ) : ℂ)) y₀ =
      starRingEnd ℂ (wirt (-I) (coordinateVector p) (fun y => ((η (L y) ^ 2 : ℝ) : ℂ)) y₀) :=
    fun p => wirt_I_ofReal (hηsq.differentiable (by simp) y₀)
  have hdSre : DifferentiableAt ℝ (fun y => (calabiS (fun z => u (L z)) y).re) y₀ :=
    (Complex.reCLM.contDiff.contDiffAt.comp y₀ hS2).differentiableAt (by norm_num)
  have hconj_S : ∀ p, wirt I (coordinateVector p) (calabiS (fun z => u (L z))) y₀ =
      starRingEnd ℂ (wirt (-I) (coordinateVector p) (calabiS (fun z => u (L z))) y₀) := by
    intro p
    have hSre : calabiS (fun z => u (L z)) =
        fun y => (((calabiS (fun z => u (L z)) y).re : ℝ) : ℂ) :=
      funext fun y => (ofReal_re_calabiS hv y).symm
    rw [hSre]
    exact wirt_I_ofReal hdSre
  have hdηc : DifferentiableAt ℝ (fun y => ((η (L y) : ℝ) : ℂ)) y₀ :=
    (Complex.ofRealCLM.contDiff.comp hηL).differentiable (by simp) y₀
  have hda : ∀ p, wirt (-I) (coordinateVector p) (fun y => ((η (L y) ^ 2 : ℝ) : ℂ)) y₀ =
      ((2 * η x₀ : ℝ) : ℂ) * wirt (-I) (coordinateVector p) (fun y => ((η (L y) : ℝ) : ℂ)) y₀ := by
    intro p
    have e : (fun y => ((η (L y) ^ 2 : ℝ) : ℂ)) =
        fun y => ((η (L y) : ℝ) : ℂ) * ((η (L y) : ℝ) : ℂ) := by
      funext y; push_cast; ring
    rw [e, wirt_mul hdηc hdηc, hηy]
    push_cast
    ring
  set D : ℝ := ∑ p, ‖wirt (-I) (coordinateVector p) (fun y => ((η (L y) : ℝ) : ℂ)) y₀‖ ^ 2
    with hDdef
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hDb : D ≤ Λ * E1 := by
    have h : D ≤ frob (lmat L) *
        ∑ a, ‖wirt (-I) (coordinateVector a) (fun y => ((η y : ℝ) : ℂ)) (L y₀)‖ ^ 2 :=
      sum_norm_wirt_comp_clm_sq_le L (g := fun y => ((η y : ℝ) : ℂ))
        ((Complex.ofRealCLM.contDiff.comp hη).differentiable (by simp) _)
    rw [hLy] at h
    exact h.trans (mul_le_mul hfL' (hE1 x₀) (Finset.sum_nonneg fun _ _ => sq_nonneg _) hΛ0.le)
  set grad : ℝ := ∑ p, ‖wirt (-I) (coordinateVector p) (calabiS fun z => u (L z)) y₀‖ ^ 2
    with hgraddef
  have hcross : -(4 * η x₀ * √D * √grad) ≤ (∑ p,
      (wirt I (coordinateVector p) (fun y => ((η (L y) ^ 2 : ℝ) : ℂ)) y₀ *
          wirt (-I) (coordinateVector p) (calabiS fun z => u (L z)) y₀ +
        wirt (-I) (coordinateVector p) (fun y => ((η (L y) ^ 2 : ℝ) : ℂ)) y₀ *
          wirt I (coordinateVector p) (calabiS fun z => u (L z)) y₀)).re := by
    simp only [hconj_a, hconj_S]
    have h := neg_le_re_sum_conj_mul
      (fun p => wirt (-I) (coordinateVector p) (fun y => ((η (L y) ^ 2 : ℝ) : ℂ)) y₀)
      (fun p => wirt (-I) (coordinateVector p) (calabiS fun z => u (L z)) y₀)
    have hα : √(∑ p, ‖wirt (-I) (coordinateVector p) (fun y => ((η (L y) ^ 2 : ℝ) : ℂ)) y₀‖ ^ 2) =
        2 * η x₀ * √D := by
      have e : ∑ p, ‖wirt (-I) (coordinateVector p) (fun y => ((η (L y) ^ 2 : ℝ) : ℂ)) y₀‖ ^ 2 =
          (2 * η x₀) ^ 2 * D := by
        rw [hDdef, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hda p, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith [hη0 x₀] : (0 : ℝ) ≤ 2 * η x₀), mul_pow]
      rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith [hη0 x₀])]
    rw [hα] at h
    have e2 : 2 * (2 * η x₀ * √D * √grad) = 4 * η x₀ * √D * √grad := by ring
    linarith
  -- (iii) the third-order term (Calabi's inequality)
  set A : ℝ := √(∑ m, frob (wirtM (-I) (coordinateVector m) (complexHessian fun z => f (L z)) y₀))
    with hAdef
  set B : ℝ := (n + 2) * √(frob (complexHessian (fun z => f (L z)) y₀ + (ε : ℂ) • 1)) with hBdef
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hAb : A ≤ √(Λ ^ 3 * K₀) := Real.sqrt_le_sqrt hA2
  have hB0 : 0 ≤ B := by positivity
  have hBb : B ≤ (n + 2) * √Fb :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hFe) (by positivity)
  -- (iv) the trace term
  have hFF : ContDiff ℝ ∞ (fun z => (f (L z) + Real.log (Complex.normSq (lmat L).det)) +
      ε * u (L z)) := hfv.add (contDiff_const.mul hv)
  have hHF : complexHessian (fun z => (f (L z) + Real.log (Complex.normSq (lmat L).det)) +
      ε * u (L z)) y₀ = complexHessian (fun z => f (L z)) y₀ + (ε : ℂ) • 1 := by
    have h := complexHessian_add_smul hv hfv ε
    rw [h]
    beta_reduce
    rw [hHfv, hH1]
  have hTT : S / Λ - Λ * √Fb ≤ (∑ p, wirt (-I) (coordinateVector p) (wirt I (coordinateVector p)
      (fun y => (M * complexHessian (fun z => u (L z)) y).trace)) y₀).re := by
    rw [sum_wirt_wirt_trace_mul hv M y₀, sum_dZ_diag hv hFF hH1 heqv, hHF, Matrix.mul_add,
      trace_add, Matrix.mul_sum, trace_sum, Complex.add_re, Complex.re_sum]
    have h1 : -(Λ * √Fb) ≤ (M * (complexHessian (fun z => f (L z)) y₀ + (ε : ℂ) • 1)).trace.re := by
      have h := hMtr (complexHessian (fun z => f (L z)) y₀ + (ε : ℂ) • 1)
      have h' := neg_abs_le (M * (complexHessian (fun z => f (L z)) y₀ + (ε : ℂ) • 1)).trace.re
      have h'' := Complex.abs_re_le_norm (M * (complexHessian (fun z => f (L z)) y₀ + (ε : ℂ) • 1)).trace
      have h3 : frob (lmat L)⁻¹ * √(frob (complexHessian (fun z => f (L z)) y₀ + (ε : ℂ) • 1)) ≤
          Λ * √Fb :=
        mul_le_mul hfLi' (Real.sqrt_le_sqrt hFe) (Real.sqrt_nonneg _) hΛ0.le
      linarith
    have h2 : ∀ p, frob (dH (fun z => u (L z)) p y₀) / Λ ≤
        (M * (dH (fun z => u (L z)) p y₀ * (dH (fun z => u (L z)) p y₀)ᴴ)).trace.re := by
      intro p
      have hlow := hMlow (dH (fun z => u (L z)) p y₀)
      have hnn := re_trace_sandwich_inv_nonneg (lmat L) (dH (fun z => u (L z)) p y₀)
      rw [div_le_iff₀ hΛ0]
      have := mul_le_mul_of_nonneg_right hfL' hnn
      linarith
    have h3 : S / Λ ≤ ∑ p, (M * (dH (fun z => u (L z)) p y₀ *
        (dH (fun z => u (L z)) p y₀)ᴴ)).trace.re := by
      rw [hS_eq, Finset.sum_div]
      exact Finset.sum_le_sum fun p _ => h2 p
    linarith
  -- the endgame
  have hAb2 : √(Λ ^ 3 * K₀) ^ 2 = Λ ^ 3 * K₀ := Real.sq_sqrt (by positivity)
  have hfinal := real_endgame (G := G) (η0 := η x₀) (grad := grad) (E2 := E2) (Λ := Λ)
    hS0 hG0 (hη0 x₀) (hη1 x₀) hA0 hAb hB0 hBb hD0 hDb hgrad hLapa hcross hlap hTT hΛ hK htr0
  rw [hAb2] at hfinal
  exact hfinal

/-- **`|∂H|² ≤ (tr H)³ S`** where `H > 0`, and `S ≥ 0` (normalised coordinates and
`transform_inv_transform`). -/
theorem sum_frob_dH_le {u : ComplexModel n → ℝ} (hu : ContDiff ℝ ∞ u) {z : ComplexModel n}
    (hz : (complexHessian u z).PosDef) :
    0 ≤ (calabiS u z).re ∧
      ∑ m, frob (dH u m z) ≤ (complexHessian u z).trace.re ^ 3 * (calabiS u z).re := by
  obtain ⟨L, y, hLy, hdet, hH1, -, hfLi, -, -⟩ := exists_normalizing_clm hu hz
  have hv : ContDiff ℝ ∞ (fun w => u (L w)) := contDiff_comp_clm L hu
  have hS : (calabiS u z).re = ∑ m, frob (dH (fun w => u (L w)) m y) := by
    rw [← hLy, ← calabiS_comp_clm L hu hdet, calabiS_at_one hv hH1, Complex.ofReal_re]
  have hX : (fun m => dH (fun w => u (L w)) m y) = transform (lmat L) (fun r => dH u r z) := by
    funext m
    rw [dH_comp_clm L hu m y, hLy]
  refine ⟨hS ▸ Finset.sum_nonneg fun _ _ => frob_nonneg _, ?_⟩
  have h := sum_frob_transform_le (lmat L)⁻¹ (fun m => dH (fun w => u (L w)) m y)
  rw [hX, transform_inv_transform hdet, hfLi] at h
  rw [hS]
  exact h

end Max

/-! ### The estimate on a ball -/

section Ball

variable {n : ℕ}

/-- A uniform bound for a continuous compactly supported function. -/
theorem exists_norm_le_of_hasCompactSupport {F : ComplexModel n → ℂ} (hF : Continuous F)
    (hc : HasCompactSupport F) : ∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖F z‖ ^ 2 ≤ B := by
  obtain ⟨C, hC⟩ := hF.bounded_above_of_compact_support hc
  refine ⟨C ^ 2, sq_nonneg _, fun z => pow_le_pow_left₀ (norm_nonneg _) (hC z) 2⟩

/-- **Calabi's third-order estimate on a ball** (N4.c): uniform bound of the third derivatives of a
solution of `log det H = f + εu` on `closedBall c r`, from bounds on `ball c (2r)`. -/
theorem exists_sum_frob_dH_le (c : ComplexModel n) {r : ℝ} (hr : 0 < r) (Λ K₀ : ℝ) :
    ∃ C : ℝ, ∀ (u f : ComplexModel n → ℝ) (ε : ℝ), ContDiff ℝ ∞ u → ContDiff ℝ ∞ f →
      0 ≤ ε → ε ≤ 1 →
      (∀ z ∈ ball c (2 * r), (complexHessian u z).PosDef ∧
        (complexHessian u z).trace.re ≤ Λ ∧ ((complexHessian u z)⁻¹).trace.re ≤ Λ ∧
        Real.log (complexHessian u z).det.re = f z + ε * u z ∧
        frob (complexHessian f z) ≤ K₀ ∧ ∑ m, frob (dH f m z) ≤ K₀) →
      ∀ z ∈ closedBall c r, ∑ m, frob (dH u m z) ≤ C := by
  classical
  set Λ' : ℝ := max Λ 1 with hΛ'
  set K₀' : ℝ := max K₀ 0 with hK₀'
  have hΛ1 : 1 ≤ Λ' := le_max_right _ _
  have hΛ0 : 0 < Λ' := lt_of_lt_of_le one_pos hΛ1
  have hK₀0 : 0 ≤ K₀' := le_max_right _ _
  -- the cutoff
  let η : ContDiffBump c := ⟨r, 3 * r / 2, hr, by linarith⟩
  have hη : ContDiff ℝ ∞ (fun z => η z) := η.contDiff
  have hηc : ContDiff ℝ ∞ (fun z => ((η z : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hη
  have hηsc : HasCompactSupport (fun z => ((η z : ℝ) : ℂ)) :=
    η.hasCompactSupport.comp_left Complex.ofReal_zero
  -- its derivative bounds
  have hB1 : ∀ a : Fin n, ∃ B : ℝ, 0 ≤ B ∧ ∀ z,
      ‖wirt (-I) (coordinateVector a) (fun y => ((η y : ℝ) : ℂ)) z‖ ^ 2 ≤ B := fun a =>
    exists_norm_le_of_hasCompactSupport (contDiff_wirt hηc).continuous (hηsc.wirt _ _)
  choose B1 hB10 hB1 using hB1
  set E1 : ℝ := ∑ a, B1 a with hE1def
  have hE1 : ∀ z, ∑ a, ‖wirt (-I) (coordinateVector a) (fun y => ((η y : ℝ) : ℂ)) z‖ ^ 2 ≤ E1 :=
    fun z => Finset.sum_le_sum fun a _ => hB1 a z
  have hη2 : ContDiff ℝ ∞ (fun z => η z ^ 2) := hη.pow 2
  have hη2c : ContDiff ℝ ∞ (fun z => ((η z ^ 2 : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hη2
  have hη2s : HasCompactSupport (fun z => ((η z ^ 2 : ℝ) : ℂ)) := by
    have : HasCompactSupport (fun z => η z ^ 2) :=
      η.hasCompactSupport.mono fun z hz => by
        simp only [Function.mem_support] at hz ⊢
        intro h
        exact hz (by rw [h]; ring)
    exact this.comp_left Complex.ofReal_zero
  have hB2 : ∀ j k : Fin n, ∃ B : ℝ, 0 ≤ B ∧ ∀ z,
      ‖wirt (-I) (coordinateVector j) (wirt I (coordinateVector k)
        (fun y => ((η y ^ 2 : ℝ) : ℂ))) z‖ ^ 2 ≤ B := fun j k =>
    exists_norm_le_of_hasCompactSupport (contDiff_wirt (contDiff_wirt hη2c)).continuous
      ((hη2s.wirt _ _).wirt _ _)
  choose B2 hB20 hB2 using hB2
  set E2 : ℝ := ∑ j, ∑ k, B2 j k with hE2def
  have hE2 : ∀ z, frob (complexHessian (fun y => η y ^ 2) z) ≤ E2 := by
    intro z
    unfold frob
    refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
    rw [complexHessian_eq_wirt (AubinYauLocalStep.contDiffAt_two hη2 z)]
    exact hB2 j k z
  -- the constants
  set Fb : ℝ := 2 * Λ' ^ 2 * K₀' + 2 * n with hFb
  set K : ℝ := Λ' * (Λ' * √E2 + 8 * Λ' * E1 + (n + 2) * √Fb + 1) with hKdef
  have hE10 : 0 ≤ E1 := Finset.sum_nonneg fun a _ => hB10 a
  have hK0 : 0 ≤ K := by positivity
  set C₁ : ℝ := 4 * (Λ' ^ 3 * K₀') + 2 * K * Λ' * √Fb + K * Λ' with hC₁
  refine ⟨Λ' ^ 3 * C₁, ?_⟩
  intro u f ε hu hf hε0 hε1 hball z hz
  have hsub : closedBall c (3 * r / 2) ⊆ ball c (2 * r) := closedBall_subset_ball (by linarith)
  set Q : ComplexModel n → ℝ := fun w =>
    η w ^ 2 * (calabiS u w).re + K * (complexHessian u w).trace.re with hQdef
  have hQc : ContinuousOn Q (closedBall c (3 * r / 2)) := by
    intro w hw
    have hdet : (complexHessian u w).det ≠ 0 := (hball w (hsub hw)).1.det_pos.ne'
    have h2 : ContinuousAt (fun w => (calabiS u w).re) w :=
      Complex.continuous_re.continuousAt.comp (contDiffAt_calabiS hu hdet).continuousAt
    have h3 : Continuous (fun w => (complexHessian u w).trace.re) := by
      refine Complex.continuous_re.comp ?_
      simp only [Matrix.trace, Matrix.diag]
      exact continuous_finsetSum _ fun i _ => (contDiff_complexHessian_apply hu i i).continuous
    exact (((hη.continuous.continuousAt.pow 2).mul h2).add
      (continuousAt_const.mul h3.continuousAt)).continuousWithinAt
  obtain ⟨x₀, hx₀, hmaxon⟩ := (isCompact_closedBall c (3 * r / 2)).exists_isMaxOn
    ⟨c, mem_closedBall_self (by linarith)⟩ hQc
  obtain ⟨hpos₀, htr₀, htri₀, -, hf2₀, hf3₀⟩ := hball x₀ (hsub hx₀)
  have hS₀ := (sum_frob_dH_le hu hpos₀).1
  have htr₀' : (complexHessian u x₀).trace.re ≤ Λ' := htr₀.trans (le_max_left _ _)
  have htrnn : ∀ w ∈ ball c (2 * r), 0 ≤ (complexHessian u w).trace.re := fun w hw =>
    AubinYauLocalStep.re_trace_nonneg (hball w hw).1.posSemidef
  -- the value at the maximum
  have hQ₀ : Q x₀ ≤ C₁ := by
    have hKtr : K * (complexHessian u x₀).trace.re ≤ K * Λ' := mul_le_mul_of_nonneg_left htr₀' hK0
    have hrest : 0 ≤ 4 * (Λ' ^ 3 * K₀') + 2 * K * Λ' * √Fb := by positivity
    by_cases hηx : η x₀ = 0
    · simp only [hQdef, hηx]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, zero_add]
      linarith
    · have hx₀b : x₀ ∈ ball c (3 * r / 2) := by
        rw [← η.support_eq]; exact hηx
      have hmax : IsLocalMax Q x₀ :=
        hmaxon.isLocalMax (mem_of_superset (isOpen_ball.mem_nhds hx₀b) ball_subset_closedBall)
      have heq : ∀ᶠ w in 𝓝 x₀, Real.log (complexHessian u w).det.re = f w + ε * u w :=
        Filter.eventually_of_mem (isOpen_ball.mem_nhds (hsub hx₀)) fun w hw => (hball w hw).2.2.2.1
      have hS := calabiS_le_of_isLocalMax (η := fun w => η w) hu hf hη (fun w => η.nonneg)
        (fun w => η.le_one) hE1 hE2 hε0 hε1 hΛ1 hK₀0 le_rfl hpos₀ htr₀'
        (htri₀.trans (le_max_left _ _)) heq (hf2₀.trans (le_max_left _ _))
        (hf3₀.trans (le_max_left _ _)) hmax
      have hη2 : η x₀ ^ 2 * (calabiS u x₀).re ≤ (calabiS u x₀).re := by
        have h1 : η x₀ ^ 2 ≤ 1 := pow_le_one₀ η.nonneg η.le_one
        exact mul_le_of_le_one_left hS₀ h1
      simp only [hQdef]
      linarith
  -- on `closedBall c r`
  have hzD : z ∈ closedBall c (3 * r / 2) := closedBall_subset_closedBall (by linarith) hz
  obtain ⟨hposz, htrz, -, -, -, -⟩ := hball z (hsub hzD)
  have hηz : η z = 1 := η.one_of_mem_closedBall hz
  have hSz : (calabiS u z).re ≤ C₁ := by
    have h1 : Q z ≤ Q x₀ := hmaxon hzD
    have h2 : 0 ≤ K * (complexHessian u z).trace.re := mul_nonneg hK0 (htrnn z (hsub hzD))
    simp only [hQdef, hηz, one_pow, one_mul] at h1
    simp only [hQdef] at hQ₀
    linarith
  obtain ⟨hSz0, hfz⟩ := sum_frob_dH_le hu hposz
  have htrz' : (complexHessian u z).trace.re ^ 3 ≤ Λ' ^ 3 :=
    pow_le_pow_left₀ (htrnn z (hsub hzD)) (htrz.trans (le_max_left _ _)) 3
  calc ∑ m, frob (dH u m z) ≤ (complexHessian u z).trace.re ^ 3 * (calabiS u z).re := hfz
    _ ≤ Λ' ^ 3 * C₁ := mul_le_mul htrz' hSz hSz0 (by positivity)

end Ball

end

end SGPT.Foundations.Analysis.Pending.CalabiCutoffEstimate
