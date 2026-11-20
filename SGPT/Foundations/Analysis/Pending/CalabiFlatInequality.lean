import SGPT.Foundations.Analysis.Pending.CalabiFlatEquation

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Calabi's inequality at a point with `H = 1`

For `u` smooth on `ℂⁿ` solving `log det(u_{jk̄}) = f + εu` near a point `x` with `(u_{jk̄})(x) = 1`
(`f` smooth, `ε ≥ 0`), Calabi's quantity `S` (`CalabiFlatLaplacian.calabiS`) satisfies
(`calabi_inequality_at_one`): there is `G ≥ 0` (namely `|∇Γ|² + |∇̄Γ|²`) with

* `Σ_p |∂_p S|² ≤ 2 S G` (from the gradient identity `∂_p S = Σ_m ⟨∇_pΓ_m, X_m⟩ + Σ_m ⟨X_m, ∇̄_pΓ_m⟩`,
  `wirt_negI_calabiS`), and
* `Σ_p ∂_p∂̄_p S ≥ G - 2 |∂∂∂̄f| √S - (n + 2) |∂∂̄f + ε| S` (from `CalabiFlatEquation.calabi_identity`; the
  `ε`-part of the third derivatives contributes `2εS ≥ 0`),

with Frobenius norms `frob` of the derivatives of `f` at `x`. This is the elliptic case of PSS
("`ΔS ≥ -C₁S - C₂`", `pss07-multiplier-krf:page-0009`) with the squares kept, as the cutoff argument needs.

TN.4 B5, nonlinear track N4 (b), blueprint `bou:yau-c3-estimate`.
-/

open Set Filter Matrix Complex
open scoped Topology ContDiff ComplexConjugate

namespace SGPT.Foundations.Analysis.Pending.CalabiFlatInequality

open FirstPass FirstPass.MongeAmpere MixedHessian WirtingerLogDet CalabiFlatIdentity
  CalabiFlatLaplacian CalabiFlatEquation

noncomputable section

variable {n : ℕ}

/-! ### The Frobenius norm -/

section Frobenius

/-- The squared Frobenius norm `Σ_{a,b} |M_{ab}|²`. -/
def frob (M : Mat n) : ℝ := ∑ a, ∑ b, ‖M a b‖ ^ 2

theorem frob_nonneg (M : Mat n) : 0 ≤ frob M := by
  unfold frob; positivity

theorem trace_mul_conjTranspose_self (M : Mat n) : (M * Mᴴ).trace = (frob M : ℂ) := by
  rw [trace_mul_conjTranspose]
  push_cast [frob]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [RCLike.star_def, Complex.mul_conj']

theorem norm_sum_mul_sq_le' {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    ‖∑ j, a j * b j‖ ^ 2 ≤ (∑ j, ‖a j‖ ^ 2) * ∑ j, ‖b j‖ ^ 2 := by
  calc ‖∑ j, a j * b j‖ ^ 2 ≤ (∑ j, ‖a j‖ * ‖b j‖) ^ 2 := by
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp only [norm_mul]
    _ ≤ (∑ j, ‖a j‖ ^ 2) * ∑ j, ‖b j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem norm_trace_mul_conjTranspose_sq_le (A B : Mat n) :
    ‖(A * Bᴴ).trace‖ ^ 2 ≤ frob A * frob B := by
  rw [trace_mul_conjTranspose]
  have h := norm_sum_mul_sq_le' (fun p : Fin n × Fin n => A p.1 p.2)
    (fun p : Fin n × Fin n => star (B p.1 p.2))
  simp only [Fintype.sum_prod_type, norm_star] at h
  exact h

theorem norm_trace_mul_conjTranspose_le (A B : Mat n) :
    ‖(A * Bᴴ).trace‖ ≤ √(frob A) * √(frob B) := by
  rw [← Real.sqrt_mul (frob_nonneg A)]
  exact Real.le_sqrt_of_sq_le (norm_trace_mul_conjTranspose_sq_le A B)

theorem frob_conjTranspose (A : Mat n) : frob Aᴴ = frob A := by
  unfold frob
  rw [Finset.sum_comm]
  simp only [conjTranspose_apply, norm_star]

theorem norm_trace_mul_le (A B : Mat n) : ‖(A * B).trace‖ ≤ √(frob A) * √(frob B) := by
  have h := norm_trace_mul_conjTranspose_le A Bᴴ
  rwa [conjTranspose_conjTranspose, frob_conjTranspose] at h

theorem frob_mul_le (A B : Mat n) : frob (A * B) ≤ frob A * frob B := by
  unfold frob
  calc ∑ a, ∑ b, ‖(A * B) a b‖ ^ 2
      ≤ ∑ a, ∑ b, (∑ k, ‖A a k‖ ^ 2) * ∑ k, ‖B k b‖ ^ 2 := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        rw [Matrix.mul_apply]
        exact norm_sum_mul_sq_le' _ _
    _ = (∑ a, ∑ k, ‖A a k‖ ^ 2) * ∑ k, ∑ b, ‖B k b‖ ^ 2 := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.mul_sum, Finset.sum_comm]

theorem norm_entry_le (A : Mat n) (a b : Fin n) : ‖A a b‖ ≤ √(frob A) := by
  refine Real.le_sqrt_of_sq_le ?_
  unfold frob
  calc ‖A a b‖ ^ 2 ≤ ∑ b', ‖A a b'‖ ^ 2 :=
        Finset.single_le_sum (f := fun b' => ‖A a b'‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ b)
    _ ≤ ∑ a', ∑ b', ‖A a' b'‖ ^ 2 :=
        Finset.single_le_sum (f := fun a' => ∑ b', ‖A a' b'‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ a)

end Frobenius

/-! ### Bounds for the terms of Calabi's identity -/

section Bounds

variable (X : Fin n → Mat n)

theorem sqrt_frob_mul_conjTranspose_le (A : Mat n) : √(frob (A * Aᴴ)) ≤ frob A := by
  have h : frob (A * Aᴴ) ≤ frob A ^ 2 := by
    rw [sq]; nth_rewrite 2 [← frob_conjTranspose A]; exact frob_mul_le _ _
  calc √(frob (A * Aᴴ)) ≤ √(frob A ^ 2) := Real.sqrt_le_sqrt h
    _ = frob A := Real.sqrt_sq (frob_nonneg A)

theorem sqrt_frob_conjTranspose_mul_le (A : Mat n) : √(frob (Aᴴ * A)) ≤ frob A := by
  have h := sqrt_frob_mul_conjTranspose_le Aᴴ
  rwa [conjTranspose_conjTranspose, frob_conjTranspose] at h

theorem norm_sum_trace_mul_le (F3 : Fin n → Mat n) :
    ‖∑ m, (F3 m * (X m)ᴴ).trace‖ ≤ √(∑ m, frob (F3 m)) * √(∑ m, frob (X m)) :=
  (norm_sum_le _ _).trans ((Finset.sum_le_sum fun _ _ => norm_trace_mul_conjTranspose_le _ _).trans
    (Real.sum_sqrt_mul_sqrt_le _ (fun _ => frob_nonneg _) fun _ => frob_nonneg _))

theorem norm_ricTerm_le (F2 : Mat n) :
    ‖ricTerm X F2‖ ≤ (n + 2) * √(frob F2) * ∑ m, frob (X m) := by
  have hF := Real.sqrt_nonneg (frob F2)
  have hS : 0 ≤ ∑ m, frob (X m) := Finset.sum_nonneg fun _ _ => frob_nonneg _
  -- the first term
  have h1 : ‖calabiForm F2 1 X 1 (fun t => (X t)ᴴ)‖ ≤ n * √(frob F2) * ∑ m, frob (X m) := by
    unfold calabiForm
    simp only [Matrix.one_mul, Matrix.mul_one]
    calc ‖∑ m, ∑ t, F2 t m * (X m * (X t)ᴴ).trace‖
        ≤ ∑ m, ∑ t, √(frob F2) * ((frob (X m) + frob (X t)) / 2) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
          rw [norm_mul]
          refine mul_le_mul (norm_entry_le F2 t m) ?_ (norm_nonneg _) hF
          refine (norm_trace_mul_conjTranspose_le _ _).trans ?_
          have := Real.sqrt_nonneg (frob (X m))
          have := Real.sqrt_nonneg (frob (X t))
          have h1 := Real.sq_sqrt (frob_nonneg (X m))
          have h2 := Real.sq_sqrt (frob_nonneg (X t))
          nlinarith [sq_nonneg (√(frob (X m)) - √(frob (X t)))]
      _ = n * √(frob F2) * ∑ m, frob (X m) := by
          have e : ∑ i, ∑ j, (frob (X i) + frob (X j)) / 2 = (n : ℝ) * ∑ i, frob (X i) := by
            simp only [add_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_div]
            ring
          simp only [← Finset.mul_sum]
          rw [e]
          ring
  have h2 : ‖calabiForm 1 F2 X 1 (fun t => (X t)ᴴ)‖ ≤ √(frob F2) * ∑ m, frob (X m) := by
    rw [calabiForm_one, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    rw [Matrix.mul_one, Matrix.mul_assoc]
    exact (norm_trace_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left (sqrt_frob_mul_conjTranspose_le _) hF)
  have h3 : ‖calabiForm 1 1 X F2 (fun t => (X t)ᴴ)‖ ≤ √(frob F2) * ∑ m, frob (X m) := by
    rw [calabiForm_one, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    rw [Matrix.one_mul, Matrix.mul_assoc, trace_mul_comm]
    rw [Matrix.mul_assoc]
    exact (norm_trace_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left (sqrt_frob_conjTranspose_mul_le _) hF)
  unfold ricTerm
  calc _ ≤ ‖calabiForm F2 1 X 1 (fun t => (X t)ᴴ)‖ + ‖calabiForm 1 F2 X 1 (fun t => (X t)ᴴ)‖ +
        ‖calabiForm 1 1 X F2 (fun t => (X t)ᴴ)‖ := norm_add₃_le
    _ ≤ _ := by nlinarith

end Bounds

/-! ### At a point with `H = 1` -/

section AtOne

variable {u : ComplexModel n → ℝ} {x : ComplexModel n} (hu : ContDiff ℝ ∞ u)
  (hx : complexHessian u x = 1)
include hu hx

/-- `S(x) = Σ_m |X_m|²` at a point with `H = 1`. -/
theorem calabiS_at_one : calabiS u x = ((∑ m, frob (dH u m x) : ℝ) : ℂ) := by
  unfold calabiS
  rw [show (complexHessian u x)⁻¹ = invH u x from rfl, invH_eq_one hu hx, calabiForm_one]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.one_mul, Matrix.mul_one, trace_mul_conjTranspose_self]

/-- **The gradient of `S`** at a point with `H = 1`:
`∂_p S = Σ_m ⟨∇_pΓ_m, X_m⟩ + Σ_m ⟨X_m, ∇̄_pΓ_m⟩`. -/
theorem wirt_negI_calabiS (p : Fin n) :
    wirt (-I) (coordinateVector p) (calabiS u) x =
      ∑ m, (calA (fun m => dH u m x) (fun p m => dV u p m x) p m * (dH u m x)ᴴ).trace +
        ∑ m, (dH u m x * (calB (fun m => dH u m x) (fun m q => dZ u m q x) m p)ᴴ).trace := by
  have hd := det_ne_zero_of_eq_one hu hx
  have hP := mdiffAt_invH hu hd
  have hX : ∀ m, MDiffAt (fun z => dH u m z) x := fun m => (mSmooth_dH hu m).mdiffAt x
  have hXh : ∀ m, MDiffAt (fun z => (dH u m z)ᴴ) x := fun m =>
    ((mSmooth_dH hu m).conjTranspose).mdiffAt x
  have h := wirt_calabiForm (c := -I) (v := coordinateVector p) (A := invH u) (B := invH u)
    (D := invH u) (C := fun z m => dH u m z) (Y := fun z m => (dH u m z)ᴴ) hP hP hX hP hXh
  unfold calabiS
  change wirt (-I) (coordinateVector p) (fun z => calabiForm (invH u z) (invH u z)
    (fun m => dH u m z) (invH u z) (fun m => (dH u m z)ᴴ)) x = _
  have e1 : (fun t => wirtM (-I) (coordinateVector p) (fun z => (dH u t z)ᴴ) x) =
      fun t => dZ u p t x := funext fun t => wirtM_negI_dH_conjTranspose hu hx p t
  have e3 : (fun m => wirtM (-I) (coordinateVector p) (fun y => dH u m y) x) =
      fun m => dV u p m x := rfl
  rw [h, e1, e3, wirtM_negI_invH hu hx, invH_eq_one hu hx]
  have hfirst : calabiForm (-dH u p x) 1 (fun m => dH u m x) 1 (fun m => (dH u m x)ᴴ) =
      -∑ m, (lterm (fun m => dH u m x) p m * (dH u m x)ᴴ).trace := by
    unfold calabiForm lterm
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib,
      Finset.sum_mul, Matrix.smul_mul, trace_sum, trace_smul, smul_eq_mul]
    rw [Finset.sum_comm]
  rw [hfirst]
  simp only [calabiForm_one, calA, calB, conjTranspose_sub, conjTranspose_mul,
    conjTranspose_conjTranspose, dZ_conjTranspose hu, Matrix.sub_mul, Matrix.mul_sub, trace_sub,
    Finset.sum_sub_distrib, Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg,
    trace_neg, Finset.sum_neg_distrib, Matrix.mul_assoc]
  ring

omit hx in
theorem complexHessian_add_smul {f : ComplexModel n → ℝ} (hf : ContDiff ℝ ∞ f) (ε : ℝ) :
    complexHessian (fun z => f z + ε * u z) =
      fun z => complexHessian f z + (ε : ℂ) • complexHessian u z := by
  funext z
  rw [AubinYauLocalStep.complexHessian_fun_add (AubinYauLocalStep.contDiffAt_two hf z)
    (AubinYauLocalStep.contDiffAt_two (contDiff_const.mul hu) z),
    AubinYauLocalStep.complexHessian_const_mul (AubinYauLocalStep.contDiffAt_two hu z)]

omit hx in
theorem wirtM_complexHessian_add_smul {f : ComplexModel n → ℝ} (hf : ContDiff ℝ ∞ f) (ε : ℝ)
    (m : Fin n) (y : ComplexModel n) :
    wirtM (-I) (coordinateVector m) (complexHessian (fun z => f z + ε * u z)) y =
      wirtM (-I) (coordinateVector m) (complexHessian f) y + (ε : ℂ) • dH u m y := by
  rw [complexHessian_add_smul hu hf]
  ext a b
  simp only [wirtM_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [wirt_add ((mSmooth_complexHessian hf).mdiffAt y a b)
    (((mSmooth_complexHessian hu).mdiffAt y a b).const_mul _),
    wirt_const_mul _ ((mSmooth_complexHessian hu).mdiffAt y a b)]
  rfl

/-- **Calabi's inequality** at a point with `H = 1` for a solution of `log det H = f + εu`, `ε ≥ 0`:
with `G = |∇Γ|² + |∇̄Γ|² ≥ 0`, `|∂S|² ≤ 2 S G` and
`Δ'S ≥ G - 2 |∂∂∂̄f| √S - (n + 2) |∂∂̄f + ε| S`. -/
theorem calabi_inequality_at_one {f : ComplexModel n → ℝ} (hf : ContDiff ℝ ∞ f) {ε : ℝ}
    (hε : 0 ≤ ε)
    (heq : ∀ᶠ y in 𝓝 x, Real.log (complexHessian u y).det.re = f y + ε * u y) :
    ∃ G : ℝ, 0 ≤ G ∧
      ∑ p, ‖wirt (-I) (coordinateVector p) (calabiS u) x‖ ^ 2 ≤ 2 * (calabiS u x).re * G ∧
      G - 2 * √(∑ m, frob (wirtM (-I) (coordinateVector m) (complexHessian f) x)) *
          √((calabiS u x).re) -
          (n + 2) * √(frob (complexHessian f x + (ε : ℂ) • 1)) * (calabiS u x).re ≤
        (∑ p, wirt (-I) (coordinateVector p) (wirt I (coordinateVector p) (calabiS u)) x).re := by
  set X : Fin n → Mat n := fun m => dH u m x with hXdef
  set V : Fin n → Fin n → Mat n := fun p m => dV u p m x with hVdef
  set Z : Fin n → Fin n → Mat n := fun m q => dZ u m q x with hZdef
  set S : ℝ := ∑ m, frob (X m) with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => frob_nonneg _
  have hSre : (calabiS u x).re = S := by rw [calabiS_at_one hu hx, Complex.ofReal_re]
  set GA : ℝ := ∑ p, ∑ m, frob (calA X V p m) with hGA
  set GB : ℝ := ∑ m, ∑ q, frob (calB X Z m q) with hGB
  have hGA0 : 0 ≤ GA := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => frob_nonneg _
  have hGB0 : 0 ≤ GB := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => frob_nonneg _
  refine ⟨GA + GB, add_nonneg hGA0 hGB0, ?_, ?_⟩
  · -- the gradient
    rw [hSre]
    have hp : ∀ p, ‖wirt (-I) (coordinateVector p) (calabiS u) x‖ ^ 2 ≤
        2 * S * (∑ m, frob (calA X V p m) + ∑ m, frob (calB X Z m p)) := by
      intro p
      rw [wirt_negI_calabiS hu hx p]
      have h1 := norm_sum_trace_mul_le X (calA X V p)
      have h2 := norm_sum_trace_mul_le (fun m => calB X Z m p) X
      have ha := Real.sq_sqrt (Finset.sum_nonneg fun m (_ : m ∈ Finset.univ) =>
        frob_nonneg (calA X V p m))
      have hb := Real.sq_sqrt (Finset.sum_nonneg fun m (_ : m ∈ Finset.univ) =>
        frob_nonneg (calB X Z m p))
      have hs := Real.sq_sqrt hS0
      have hn := norm_add_le (∑ m, (calA X V p m * (X m)ᴴ).trace)
        (∑ m, (X m * (calB X Z m p)ᴴ).trace)
      set a := √(∑ m, frob (calA X V p m))
      set b := √(∑ m, frob (calB X Z m p))
      set r := √S
      have ha0 : 0 ≤ a := Real.sqrt_nonneg _
      have hb0 : 0 ≤ b := Real.sqrt_nonneg _
      have hr0 : 0 ≤ r := Real.sqrt_nonneg _
      have hle : ‖∑ m, (calA X V p m * (X m)ᴴ).trace + ∑ m, (X m * (calB X Z m p)ᴴ).trace‖ ≤
          a * r + r * b := hn.trans (add_le_add h1 h2)
      calc _ ≤ (a * r + r * b) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
        _ ≤ 2 * S * (a ^ 2 + b ^ 2) := by
            rw [← hs]; nlinarith [sq_nonneg (a - b), mul_nonneg hr0 hr0]
        _ = _ := by rw [ha, hb]
    calc _ ≤ ∑ p, 2 * S * (∑ m, frob (calA X V p m) + ∑ m, frob (calB X Z m p)) :=
          Finset.sum_le_sum fun p _ => hp p
      _ = 2 * S * (GA + GB) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, hGA, hGB,
            Finset.sum_comm (f := fun p m => frob (calB X Z m p))]
  · -- the Laplacian
    have hF : ContDiff ℝ ∞ (fun z => f z + ε * u z) := hf.add (contDiff_const.mul hu)
    have hid := calabi_identity hu hF hx heq
    rw [hid]
    have e3 : ∀ m, wirtM (-I) (coordinateVector m) (complexHessian fun z => f z + ε * u z) x =
        wirtM (-I) (coordinateVector m) (complexHessian f) x + (ε : ℂ) • X m := fun m =>
      wirtM_complexHessian_add_smul hu hf ε m x
    have e2 : complexHessian (fun z => f z + ε * u z) x = complexHessian f x + (ε : ℂ) • 1 := by
      rw [complexHessian_add_smul hu hf]
      beta_reduce
      rw [hx]
    simp only [e3, e2, Matrix.add_mul, Matrix.smul_mul, trace_add, trace_smul, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum, trace_mul_conjTranspose_self]
    set T0 := ∑ m, (wirtM (-I) (coordinateVector m) (complexHessian f) x * (X m)ᴴ).trace
    have hT0 := norm_sum_trace_mul_le X (fun m => wirtM (-I) (coordinateVector m) (complexHessian f) x)
    have hRic := norm_ricTerm_le X (complexHessian f x + (ε : ℂ) • 1)
    have hre1 : -‖T0‖ ≤ T0.re := neg_le_of_abs_le (Complex.abs_re_le_norm T0)
    have hre2 : (ricTerm X (complexHessian f x + (ε : ℂ) • 1)).re ≤
        ‖ricTerm X (complexHessian f x + (ε : ℂ) • 1)‖ := Complex.re_le_norm _
    rw [hSre]
    have hXS : ∑ i, (X i * (dH u i x)ᴴ).trace = (S : ℂ) := by
      rw [hSdef]; push_cast
      exact Finset.sum_congr rfl fun i _ => trace_mul_conjTranspose_self (X i)
    have hstar : ∀ z : ℂ, (z + star z).re = 2 * z.re := fun z => by
      rw [Complex.add_re, Complex.star_def, Complex.conj_re]; ring
    rw [hXS, Complex.sub_re, Complex.add_re, Complex.add_re, hstar, Complex.add_re,
      Complex.re_sum, Complex.re_sum]
    simp only [Complex.re_sum, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul,
      sub_zero]
    rw [← hGA, ← hGB]
    have hεS : 0 ≤ ε * S := mul_nonneg hε hS0
    have hB3 := Real.sqrt_nonneg (∑ m, frob (wirtM (-I) (coordinateVector m) (complexHessian f) x))
    have hsS := Real.sqrt_nonneg S
    nlinarith [hT0, hRic, hre1, hre2]

end AtOne

end

end SGPT.Foundations.Analysis.Pending.CalabiFlatInequality
