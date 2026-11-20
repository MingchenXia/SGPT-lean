import SGPT.NPP.DN4Pointwise
import SGPT.NPP.DN4Hadamard
import SGPT.NPP.DN3ParamIntegral
import SGPT.NPP.DN3RadialMass
import SGPT.NPP.DN3PsdForm

/-!
# The core joint Levi estimate of the Chern smoothing (abstract form)

Lane DN4 (`thm:DNT23_C11bar`, big classes; FPT `lem:chern-joint-smoothing`,
`chapters/inputs/q10-big-envelope-regularity.tex`, Steps 2–5, identity
`eq:chern-kernel-square-identity` and estimate `eq:chern-potential-joint-bound`).

Let `c(τ, ζ)` be a `C²` family of points of `ℂⁿ` (`τ ∈ ℂ`, `ζ ∈ ℂⁿ`), holomorphic in `ζ` at
`τ = 0` (`Φ = c(0, ·)`), and let `p` be a `C²` function, plurisubharmonic near `Φ(B̄)`.  Put
`φ(τ) = ∫ p(c(τ, ζ)) χ(|ζ|²) dζ`.  With `Ŷ = ∂_τ c`, `X̂ = ∂_τ̄ c`, `Q̂ = ∂_τ∂_τ̄ c` at `τ = 0`
(`SGPT.NPP.DN4.curveDz`, `curveDzbar`, `curveLevi`), assume that there are holomorphic vector fields
`X`, `R` on a ball `B(0, ρ)`, `ρ > 1`, vanishing at `0`, with `DΦ · X = X̂` and
`DΦ · R = Q̂ - DŶ · X`.  Then (`leviForm_integral_ge`)

  `L φ(0) ≥ -(n²(a₁ + a₂))² ∫ χ(|ζ|²) T(ζ) dζ - 4 n² b₁ ∫ (-χ₁(|ζ|²)) T(ζ) dζ`,

where `T = levTr (p ∘ Φ)` is the trace of the complex Hessian of `p ∘ Φ`, and `a₁, a₂, b₁` bound
`‖DX_m‖`, `‖D²X_m‖`, `‖DR_m‖` on the closed unit ball.

This replaces FPT Steps 2–4: no holomorphic reparametrisation of the fibre and no weight jets are
needed.  The proof: differentiate under the integral sign (`SGPT.NPP.DN3.leviForm_integral_of_contDiffOn`),
apply the pointwise identity `SGPT.NPP.DN4.leviForm_curve_eq`
`L_τ(p ∘ c) = L_p[Ŷ] + L_p[X̂] + 2 Re ∂_X ℓ + D(p ∘ Φ)(R)`, write `χ X_m = ∑_l ∂̄_l(χ₁ σ_{ml})`
and `χ R_m = ∑_l ∂̄_l(χ₁ ϱ_{ml})` with Hadamard coefficients (`SGPT.NPP.DN3.chi_mul_eq_sum_dbarDir`),
integrate by parts so that only `∂̄_l ℓ = H_p(Ŷ, DΦ e_l)` and the complex Hessian of `p ∘ Φ`
remain, and bound pointwise: the cross term is absorbed by completing the square against
`χ L_p[Ŷ]`, the remaining terms by the trace (Cauchy–Schwarz for the positive semidefinite
complex Hessian).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory Complex
open scoped Topology ContDiff ComplexConjugate

namespace SGPT.NPP.DN4

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.CauchyGreen
open SGPT.NPP.DN3 SGPT.NPP.DN2
open SGPT.Envelopes.LapClass SGPT.Envelopes.LapClass3 SGPT.Envelopes.DNTC11

variable {n : ℕ}

/-! ### The trace bound -/

/-- `L_f(x)[v] ≤ tr Hess_ℂ f(x) · ‖v‖²` for a positive semidefinite Levi form. -/
theorem leviForm_le_levTr_mul {f : ComplexModel n → ℝ} {x : ComplexModel n}
    (hf : ContDiffAt ℝ 2 f x) (hpsh : ∀ v, 0 ≤ leviForm f x v) (v : ComplexModel n) :
    leviForm f x v ≤ levTr f x * ‖v‖ ^ 2 := by
  have hH := complexHessian_isHermitian hf
  have hP : ∀ w, 0 ≤ hermQuad (complexHessian f x) w := fun w => by
    rw [hermQuad_complexHessian hf]; exact hpsh w
  have h := hermQuad_le_trace_mul hH hP v
  rwa [hermQuad_complexHessian hf, re_trace_complexHessian hf] at h

theorem leviForm_coord_le_levTr {f : ComplexModel n → ℝ} {x : ComplexModel n}
    (hpsh : ∀ v, 0 ≤ leviForm f x v) (m : Fin n) :
    leviForm f x (coordinateVector m) ≤ levTr f x :=
  Finset.single_le_sum (f := fun q => leviForm f x (coordinateVector q)) (fun q _ => hpsh _)
    (Finset.mem_univ m)

theorem levTr_nonneg {f : ComplexModel n → ℝ} {x : ComplexModel n}
    (hpsh : ∀ v, 0 ≤ leviForm f x v) : 0 ≤ levTr f x :=
  Finset.sum_nonneg fun q _ => hpsh _

theorem continuous_levTr {f : ComplexModel n → ℝ} (hf : ContDiff ℝ 2 f) : Continuous (levTr f) := by
  have : levTr f = fun y => ∑ q, leviForm f y (coordinateVector q) := rfl
  rw [this]
  refine continuous_finsetSum _ fun q _ => ?_
  simp only [leviForm, realHessian_eq_fderiv]
  have hD2c : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  exact (((hD2c.clm_apply continuous_const).clm_apply continuous_const).add
    ((hD2c.clm_apply continuous_const).clm_apply continuous_const)).div_const 4

/-! ### The radial weight -/

/-- `χ₁(t) = -(1 - t)² χ(t)` for all `t`. -/
theorem chiOne_eq_neg (t : ℝ) : chiOne n t = -((1 - t) ^ 2 * chi n t) := by
  rcases lt_or_ge t 1 with ht | ht
  · rw [← neg_chiOne_eq n ht, neg_neg]
  · rw [chiOne_eq_zero_of_le n ht, chi_eq_zero_of_le n ht, mul_zero, neg_zero]

theorem neg_chiOne_le_chi {t : ℝ} (ht : 0 ≤ t) : -chiOne n t ≤ chi n t := by
  rw [chiOne_eq_neg, neg_neg]
  rcases lt_or_ge t 1 with h | h
  · have h1 : (1 - t) ^ 2 ≤ 1 := by nlinarith
    calc (1 - t) ^ 2 * chi n t ≤ 1 * chi n t := mul_le_mul_of_nonneg_right h1 (chi_nonneg n t)
      _ = chi n t := one_mul _
  · rw [chi_eq_zero_of_le n h, mul_zero]

/-- `∂_l φ(‖s‖²) = φ'(‖s‖²) s̄_l`. -/
theorem dDir_radial {φ : ℝ → ℝ} {φ' : ℝ} {s : ComplexModel n}
    (hφ : HasDerivAt φ φ' (‖s‖ ^ 2)) (l : Fin n) :
    dDir (coordinateVector l) (fun y => ((φ (‖y‖ ^ 2) : ℝ) : ℂ)) s = φ' * conj (s l) := by
  have hd : DifferentiableAt ℝ (fun y : ComplexModel n => φ (‖y‖ ^ 2)) s :=
    (hφ.comp_hasFDerivAt s (hasStrictFDerivAt_norm_sq s).hasFDerivAt).differentiableAt
  have hdc : DifferentiableAt ℝ (fun y : ComplexModel n => ((φ (‖y‖ ^ 2) : ℝ) : ℂ)) s :=
    (Complex.ofRealCLM.differentiableAt).comp s hd
  rw [dDir_eq_conj_dbarDir_conj hdc]
  have e : (fun y : ComplexModel n => conj (((φ (‖y‖ ^ 2) : ℝ) : ℂ))) =
      fun y => ((φ (‖y‖ ^ 2) : ℝ) : ℂ) := by
    funext y; exact Complex.conj_ofReal _
  rw [e, dbarDir_radial hφ l, map_mul, Complex.conj_ofReal]

theorem dDir_chiOne_normSq (s : ComplexModel n) (l : Fin n) :
    dDir (coordinateVector l) (fun y => ((chiOne n (‖y‖ ^ 2) : ℝ) : ℂ)) s =
      chi n (‖s‖ ^ 2) * conj (s l) :=
  dDir_radial (hasDerivAt_chiOne n _) l

theorem contDiff_chi_normSq :
    ContDiff ℝ ∞ (fun y : ComplexModel n => chi n (‖y‖ ^ 2)) :=
  (contDiff_chi n).comp (contDiff_norm_sq ℝ)

theorem contDiff_chiOne_normSq :
    ContDiff ℝ ∞ (fun y : ComplexModel n => chiOne n (‖y‖ ^ 2)) :=
  (contDiff_chiOne n).comp (contDiff_norm_sq ℝ)

theorem chi_normSq_eq_zero {y : ComplexModel n} (hy : 1 ≤ ‖y‖) : chi n (‖y‖ ^ 2) = 0 :=
  chi_eq_zero_of_le n (by nlinarith)

theorem chiOne_normSq_eq_zero {y : ComplexModel n} (hy : 1 ≤ ‖y‖) : chiOne n (‖y‖ ^ 2) = 0 :=
  chiOne_eq_zero_of_le n (by nlinarith)

theorem hasCompactSupport_of_unitBall {f : ComplexModel n → ℂ}
    (hf : ∀ y : ComplexModel n, 1 < ‖y‖ → f y = 0) : HasCompactSupport f := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ComplexModel n) 1) fun y hy => ?_
  rw [mem_closedBall, dist_zero_right, not_le] at hy
  exact hf y hy

theorem hasCompactSupport_of_unitBall_real {f : ComplexModel n → ℝ}
    (hf : ∀ y : ComplexModel n, 1 < ‖y‖ → f y = 0) : HasCompactSupport f := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ComplexModel n) 1) fun y hy => ?_
  rw [mem_closedBall, dist_zero_right, not_le] at hy
  exact hf y hy

/-! ### The divergence data `χ₁ σ_{ml}` -/

/-- The Hadamard coefficients `σ_{ml} = (X_m)~_l` of a vector field. -/
def hadMat (X : ComplexModel n → ComplexModel n) (m l : Fin n) : ComplexModel n → ℂ :=
  hadamardCoeff (fun s => X s m) l

/-- `χ₁(|s|²) σ_{ml}(s)`. -/
def cutHad (X : ComplexModel n → ComplexModel n) (m l : Fin n) : ComplexModel n → ℂ :=
  fun y => ((chiOne n (‖y‖ ^ 2) : ℝ) : ℂ) * hadMat X m l y

section Had

variable {X : ComplexModel n → ComplexModel n} {ρ : ℝ}

theorem differentiableOn_coord (hX : DifferentiableOn ℂ X (ball 0 ρ)) (m : Fin n) :
    DifferentiableOn ℂ (fun s => X s m) (ball 0 ρ) :=
  ((EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin n) m).differentiable.comp_differentiableOn hX)

theorem contDiff_cutHad (hρ : 1 < ρ) (hX : DifferentiableOn ℂ X (ball 0 ρ)) (m l : Fin n) :
    ContDiff ℝ ∞ (cutHad X m l) :=
  contDiff_mul_of_tsupport_subset isOpen_ball (contDiff_ofReal_comp contDiff_chiOne_normSq)
    (contDiffOn_real_of_differentiableOn_complex
      (differentiableOn_hadamardCoeff (differentiableOn_coord hX m) l) isOpen_ball)
    (tsupport_chiOne_normSq_subset.trans (closedBall_subset_ball hρ))

theorem cutHad_eq_zero {y : ComplexModel n} (hy : 1 ≤ ‖y‖) (m l : Fin n) :
    cutHad X m l y = 0 := by
  simp [cutHad, chiOne_normSq_eq_zero hy]

theorem hasCompactSupport_cutHad (m l : Fin n) : HasCompactSupport (cutHad X m l) :=
  hasCompactSupport_of_unitBall fun _ hy => cutHad_eq_zero hy.le m l

theorem dbarDir_cutHad_eq_zero {y : ComplexModel n} (hy : 1 < ‖y‖) (v : ComplexModel n)
    (m l : Fin n) : dbarDir v (cutHad X m l) y = 0 := by
  refine image_eq_zero_of_notMem_tsupport fun h => ?_
  have h2 := (hasCompactSupport_cutHad (X := X) m l)
  have hsub : tsupport (cutHad X m l) ⊆ closedBall 0 1 := by
    refine closure_minimal (fun z hz => ?_) isClosed_closedBall
    by_contra hz'
    rw [mem_closedBall, dist_zero_right, not_le] at hz'
    exact hz (cutHad_eq_zero hz'.le m l)
  have := hsub (OTChen.tsupport_dbarDir_subset v _ h)
  rw [mem_closedBall, dist_zero_right] at this
  linarith

theorem dDir_cutHad_eq_zero {y : ComplexModel n} (hy : 1 < ‖y‖) (v : ComplexModel n)
    (m l : Fin n) : dDir v (cutHad X m l) y = 0 := by
  refine image_eq_zero_of_notMem_tsupport fun h => ?_
  have hsub : tsupport (cutHad X m l) ⊆ closedBall 0 1 := by
    refine closure_minimal (fun z hz => ?_) isClosed_closedBall
    by_contra hz'
    rw [mem_closedBall, dist_zero_right, not_le] at hz'
    exact hz (cutHad_eq_zero hz'.le m l)
  have := hsub (tsupport_dDir_subset v _ h)
  rw [mem_closedBall, dist_zero_right] at this
  linarith

/-- **The divergence formula** `χ(|s|²) X_m(s) = ∑_l ∂̄_l(χ₁ σ_{ml})(s)`, for all `s`. -/
theorem chi_mul_coord_eq_sum (hρ : 1 < ρ) (hX : DifferentiableOn ℂ X (ball 0 ρ))
    (hX0 : X 0 = 0) (m : Fin n) (s : ComplexModel n) :
    (chi n (‖s‖ ^ 2) : ℂ) * X s m = ∑ l, dbarDir (coordinateVector l) (cutHad X m l) s := by
  by_cases hs : s ∈ ball (0 : ComplexModel n) ρ
  · have hXm := differentiableOn_coord hX m
    have hXmc : ContinuousOn (fderiv ℂ (fun s => X s m)) (ball 0 ρ) :=
      (contDiffOn_of_differentiableOn_complex hXm isOpen_ball).continuousOn_fderiv_of_isOpen
        isOpen_ball (by simp)
    have h0 : (fun s => X s m) 0 = 0 := by simp [hX0]
    exact chi_mul_eq_sum_dbarDir hXm hXmc h0
      (fun l => differentiableOn_hadamardCoeff hXm l) hs
  · have hs' : 1 < ‖s‖ := by
      rw [mem_ball, dist_zero_right, not_lt] at hs; linarith
    rw [chi_normSq_eq_zero hs'.le]
    simp only [Complex.ofReal_zero, zero_mul]
    exact (Finset.sum_eq_zero fun l _ => dbarDir_cutHad_eq_zero hs' _ m l).symm

/-- `∂_m(χ₁ σ_{ml}) = χ (s̄_m σ_{ml} - (1 - |s|²)² ∂_m σ_{ml})` on `B(0, ρ)`. -/
theorem dDir_cutHad (hX : DifferentiableOn ℂ X (ball 0 ρ)) (m l : Fin n) {s : ComplexModel n}
    (hs : s ∈ ball (0 : ComplexModel n) ρ) :
    dDir (coordinateVector m) (cutHad X m l) s =
      chi n (‖s‖ ^ 2) * (conj (s m) * hadMat X m l s -
        (((1 - ‖s‖ ^ 2) ^ 2 : ℝ) : ℂ) * fderiv ℂ (hadMat X m l) s (coordinateVector m)) := by
  have hσ : DifferentiableAt ℂ (hadMat X m l) s :=
    (differentiableOn_hadamardCoeff (differentiableOn_coord hX m) l).differentiableAt
      (isOpen_ball.mem_nhds hs)
  have hχd : DifferentiableAt ℝ (fun y : ComplexModel n => ((chiOne n (‖y‖ ^ 2) : ℝ) : ℂ)) s :=
    ((contDiff_ofReal_comp (contDiff_chiOne_normSq (n := n))).differentiable (by simp)) s
  have h := dDir_mul (v := coordinateVector m) hχd (hσ.restrictScalars ℝ)
  have e : cutHad X m l = fun y => ((chiOne n (‖y‖ ^ 2) : ℝ) : ℂ) * hadMat X m l y := rfl
  rw [e, h, dDir_chiOne_normSq, dDir_eq_fderiv_of_differentiableAt hσ, chiOne_eq_neg]
  push_cast
  ring

end Had

/-! ### Regularity of the auxiliary functions -/

theorem contDiff_curveDz {c : ℂ → ComplexModel n → ComplexModel n}
    (hc : ContDiff ℝ 2 (fun q : ℂ × ComplexModel n => c q.1 q.2)) :
    ContDiff ℝ 1 (curveDz c) := by
  have hf : ContDiff ℝ 2 (Function.uncurry fun (ζ : ComplexModel n) (τ : ℂ) => c τ ζ) :=
    hc.comp (contDiff_snd.prodMk contDiff_fst)
  have hD : ContDiff ℝ 1 (fun ζ : ComplexModel n => fderiv ℝ (fun τ => c τ ζ) 0) :=
    hf.fderiv (contDiff_const (c := (0 : ℂ))) (by norm_num)
  have h1 := hD.clm_apply (contDiff_const (c := (1 : ℂ)))
  have h2 := hD.clm_apply (contDiff_const (c := I))
  exact (h1.sub (h2.const_smul I)).const_smul _

theorem contDiff_holDeriv {p : ComplexModel n → ℝ} {Φ Y : ComplexModel n → ComplexModel n}
    (hp : ContDiff ℝ 2 p) (hΦ : ContDiff ℝ 1 Φ) (hY : ContDiff ℝ 1 Y) :
    ContDiff ℝ 1 (holDeriv p Φ Y) := by
  have e : holDeriv p Φ Y = fun s =>
      (((fderiv ℝ p (Φ s) (Y s) : ℝ) : ℂ) - I * ((fderiv ℝ p (Φ s) (I • Y s) : ℝ) : ℂ)) / 2 := by
    funext s
    exact dDir_ofReal_eq ((hp.differentiable (by norm_num)) (Φ s)) (Y s)
  rw [e]
  have hDp : ContDiff ℝ 1 (fun s => fderiv ℝ p (Φ s)) :=
    (hp.fderiv_right (m := 1) (by norm_num)).comp hΦ
  have h1 : ContDiff ℝ 1 (fun s => fderiv ℝ p (Φ s) (Y s)) := hDp.clm_apply hY
  have h2 : ContDiff ℝ 1 (fun s => fderiv ℝ p (Φ s) (I • Y s)) := hDp.clm_apply (hY.const_smul I)
  exact ((Complex.ofRealCLM.contDiff.comp h1).sub
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp h2))).div_const 2

/-! ### Integration by parts -/

/-- `∫ ∂̄_v M · ∂_u f = ∫ ∂̄_v f · ∂_u M` for `C¹` `f` and compactly supported `C²` `M`. -/
theorem integral_dbarDir_mul_dDir_swap {f M : ComplexModel n → ℂ} (hf : ContDiff ℝ 1 f)
    (hM : ContDiff ℝ 2 M) (hMs : HasCompactSupport M) (u v : ComplexModel n) :
    ∫ s, dbarDir v M s * dDir u f s = ∫ s, dbarDir v f s * dDir u M s := by
  have hdbM : ContDiff ℝ 1 (dbarDir v M) := contDiff_dbarDir (k := 1) hM
  have hdM : ContDiff ℝ 1 (dDir u M) := contDiff_dDir (k := 1) hM
  rw [integral_mul_dDir_eq_neg hdbM hf (Or.inl (hasCompactSupport_dbarDir hMs v)) u]
  have e : (fun s => dbarDir v f s * dDir u M s) = fun s => dDir u M s * dbarDir v f s := by
    funext s; ring
  rw [e, integral_mul_dbarDir_eq_neg hdM hf (Or.inl (hasCompactSupport_dDir hMs u)) v]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only
  rw [dbarDir_dDir_comm (hM.contDiffAt)]


/-! ### The terms of the integrand -/

/-- `χ (L_p[Ŷ] + L_p[X̂])`. -/
def termA (p : ComplexModel n → ℝ) (c : ℂ → ComplexModel n → ComplexModel n)
    (ζ : ComplexModel n) : ℝ :=
  chi n (‖ζ‖ ^ 2) * (leviForm p (c 0 ζ) (curveDz c ζ) + leviForm p (c 0 ζ) (curveDzbar c ζ))

/-- `∑_m χ X_m ∂_m ℓ`, `ℓ = ∂p(Φ) · Ŷ`. -/
def termB (p : ComplexModel n → ℝ) (c : ℂ → ComplexModel n → ComplexModel n)
    (X : ComplexModel n → ComplexModel n) (ζ : ComplexModel n) : ℂ :=
  ∑ m, ((chi n (‖ζ‖ ^ 2) : ℂ) * X ζ m) *
    dDir (coordinateVector m) (holDeriv p (c 0) (curveDz c)) ζ

/-- `∑_m χ R_m ∂_m (p ∘ Φ)`. -/
def termC (p : ComplexModel n → ℝ) (c : ℂ → ComplexModel n → ComplexModel n)
    (R : ComplexModel n → ComplexModel n) (ζ : ComplexModel n) : ℂ :=
  ∑ m, ((chi n (‖ζ‖ ^ 2) : ℂ) * R ζ m) *
    dDir (coordinateVector m) (fun s => ((p (c 0 s) : ℝ) : ℂ)) ζ

/-- After integration by parts: `∑_{m,l} ∂̄_l ℓ · ∂_m(χ₁ σ_{ml})`. -/
def termB2 (p : ComplexModel n → ℝ) (c : ℂ → ComplexModel n → ComplexModel n)
    (X : ComplexModel n → ComplexModel n) (ζ : ComplexModel n) : ℂ :=
  ∑ m, ∑ l, dbarDir (coordinateVector l) (holDeriv p (c 0) (curveDz c)) ζ *
    dDir (coordinateVector m) (cutHad X m l) ζ

/-- After integration by parts: `-∑_{m,l} ∂̄_l ∂_m (p ∘ Φ) · χ₁ ϱ_{ml}`. -/
def termC2 (p : ComplexModel n → ℝ) (c : ℂ → ComplexModel n → ComplexModel n)
    (R : ComplexModel n → ComplexModel n) (ζ : ComplexModel n) : ℂ :=
  -∑ m, ∑ l, dbarDir (coordinateVector l)
    (dDir (coordinateVector m) (fun s => ((p (c 0 s) : ℝ) : ℂ))) ζ * cutHad R m l ζ

theorem re_ofReal_sub_I_mul_div_two (a b : ℝ) : (((a : ℂ) - I * (b : ℂ)) / 2).re = a / 2 := by
  simp

theorem re_sum_ofReal_mul (a : ℝ) (f g : Fin n → ℂ) :
    (∑ m, ((a : ℂ) * f m) * g m).re = a * (∑ m, f m * g m).re := by
  rw [← Complex.re_ofReal_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

section Core

variable {c : ℂ → ComplexModel n → ComplexModel n} {p : ComplexModel n → ℝ}
  {X R : ComplexModel n → ComplexModel n} {ρ : ℝ}

/-- **The pointwise identity**
`χ L_τ(p ∘ c)(0) = χ(L_p[Ŷ] + L_p[X̂]) + 2 Re ∑ χ X_m ∂_m ℓ + 2 Re ∑ χ R_m ∂_m (p ∘ Φ)`. -/
theorem chi_mul_leviForm_eq (hρ : 1 < ρ) (hp : ContDiff ℝ 2 p)
    (hc : ContDiff ℝ 2 (fun q : ℂ × ComplexModel n => c q.1 q.2))
    (hΦ : DifferentiableOn ℂ (c 0) (ball 0 ρ)) (hY : DifferentiableOn ℂ (curveDz c) (ball 0 ρ))
    (hX : ∀ ζ ∈ ball (0 : ComplexModel n) ρ, fderiv ℂ (c 0) ζ (X ζ) = curveDzbar c ζ)
    (hR : ∀ ζ ∈ ball (0 : ComplexModel n) ρ,
      fderiv ℂ (c 0) ζ (R ζ) = curveLevi c ζ - fderiv ℂ (curveDz c) ζ (X ζ))
    (ζ : ComplexModel n) :
    chi n (‖ζ‖ ^ 2) * leviForm (fun τ => p (c τ ζ)) 0 1 =
      termA p c ζ + 2 * (termB p c X ζ).re + 2 * (termC p c R ζ).re := by
  by_cases hζ : ζ ∈ ball (0 : ComplexModel n) ρ
  · have hopen : IsOpen (ball (0 : ComplexModel n) ρ) := isOpen_ball
    have hΦζ : DifferentiableAt ℂ (c 0) ζ := hΦ.differentiableAt (hopen.mem_nhds hζ)
    have hYζ : DifferentiableAt ℂ (curveDz c) ζ := hY.differentiableAt (hopen.mem_nhds hζ)
    have hcτ : ContDiff ℝ 2 (fun τ => c τ ζ) := hc.comp (contDiff_id.prodMk contDiff_const)
    have hc0 : ContDiff ℝ 2 (c 0) := hc.comp (contDiff_const.prodMk contDiff_id)
    have hg2 : ContDiff ℝ 2 (fun s => p (c 0 s)) := hp.comp hc0
    have h := leviForm_curve_eq hcτ.contDiffAt hp.contDiffAt hΦζ hYζ (X ζ) (R ζ) (hX ζ hζ)
      (hR ζ hζ)
    have hdX : dDir (X ζ) (holDeriv p (c 0) (curveDz c)) ζ =
        ∑ m, X ζ m * dDir (coordinateVector m) (holDeriv p (c 0) (curveDz c)) ζ := by
      conv_lhs => rw [← sum_coord_smul (X ζ)]
      exact dDir_sum_dir _ _ _ _ _
    have hdR : fderiv ℝ (fun s => p (c 0 s)) ζ (R ζ) =
        2 * (∑ m, R ζ m * dDir (coordinateVector m) (fun s => ((p (c 0 s) : ℝ) : ℂ)) ζ).re := by
      have h1 : dDir (R ζ) (fun s => ((p (c 0 s) : ℝ) : ℂ)) ζ =
          ∑ m, R ζ m * dDir (coordinateVector m) (fun s => ((p (c 0 s) : ℝ) : ℂ)) ζ := by
        conv_lhs => rw [← sum_coord_smul (R ζ)]
        exact dDir_sum_dir _ _ _ _ _
      rw [← h1, dDir_ofReal_eq ((hg2.differentiable (by norm_num)) ζ),
        re_ofReal_sub_I_mul_div_two]
      ring
    rw [h, hdX, hdR, termA, termB, termC, re_sum_ofReal_mul, re_sum_ofReal_mul]
    ring
  · have hζ' : 1 ≤ ‖ζ‖ := by
      rw [mem_ball, dist_zero_right, not_lt] at hζ; linarith
    simp [termA, termB, termC, chi_normSq_eq_zero hζ']


/-! ### Integrability -/

theorem continuous_chi_mul_coord (hρ : 1 < ρ) {V : ComplexModel n → ComplexModel n}
    (hV : DifferentiableOn ℂ V (ball 0 ρ)) (m : Fin n) :
    Continuous (fun ζ : ComplexModel n => (chi n (‖ζ‖ ^ 2) : ℂ) * V ζ m) :=
  (contDiff_mul_of_tsupport_subset (k := 0) isOpen_ball
    ((contDiff_ofReal_comp (contDiff_chi_normSq (n := n))).of_le (by norm_cast))
    ((contDiffOn_real_of_differentiableOn_complex (differentiableOn_coord hV m)
      isOpen_ball).of_le (by norm_cast))
    (tsupport_chi_normSq_subset.trans (closedBall_subset_ball hρ))).continuous

theorem contDiff_holDeriv_curve (hp : ContDiff ℝ 2 p)
    (hc : ContDiff ℝ 2 (fun q : ℂ × ComplexModel n => c q.1 q.2)) :
    ContDiff ℝ 1 (holDeriv p (c 0) (curveDz c)) :=
  contDiff_holDeriv hp ((hc.comp (contDiff_const.prodMk contDiff_id)).of_le (by norm_num))
    (contDiff_curveDz hc)

theorem contDiff_ofReal_comp_curve (hp : ContDiff ℝ 2 p)
    (hc : ContDiff ℝ 2 (fun q : ℂ × ComplexModel n => c q.1 q.2)) :
    ContDiff ℝ 2 (fun s => ((p (c 0 s) : ℝ) : ℂ)) :=
  contDiff_ofReal_comp (hp.comp (hc.comp (contDiff_const.prodMk contDiff_id)))

theorem integrable_termB_summand (hρ : 1 < ρ) (hp : ContDiff ℝ 2 p)
    (hc : ContDiff ℝ 2 (fun q : ℂ × ComplexModel n => c q.1 q.2))
    (hXh : DifferentiableOn ℂ X (ball 0 ρ)) (m : Fin n) :
    Integrable (fun ζ => ((chi n (‖ζ‖ ^ 2) : ℂ) * X ζ m) *
      dDir (coordinateVector m) (holDeriv p (c 0) (curveDz c)) ζ) := by
  have hdℓ := (contDiff_dDir (v := coordinateVector m) (k := 0)
    (by simpa using contDiff_holDeriv_curve hp hc)).continuous
  exact ((continuous_chi_mul_coord hρ hXh m).mul hdℓ).integrable_of_hasCompactSupport
    (hasCompactSupport_of_unitBall fun ζ hζ => by simp [chi_normSq_eq_zero hζ.le])

theorem integrable_termC_summand (hρ : 1 < ρ) (hp : ContDiff ℝ 2 p)
    (hc : ContDiff ℝ 2 (fun q : ℂ × ComplexModel n => c q.1 q.2))
    (hRh : DifferentiableOn ℂ R (ball 0 ρ)) (m : Fin n) :
    Integrable (fun ζ => ((chi n (‖ζ‖ ^ 2) : ℂ) * R ζ m) *
      dDir (coordinateVector m) (fun s => ((p (c 0 s) : ℝ) : ℂ)) ζ) := by
  have hdg := (contDiff_dDir (v := coordinateVector m) (k := 0)
    ((contDiff_ofReal_comp_curve hp hc).of_le (by norm_num))).continuous
  exact ((continuous_chi_mul_coord hρ hRh m).mul hdg).integrable_of_hasCompactSupport
    (hasCompactSupport_of_unitBall fun ζ hζ => by simp [chi_normSq_eq_zero hζ.le])

theorem integrable_termB2_summand (hρ : 1 < ρ) (hp : ContDiff ℝ 2 p)
    (hc : ContDiff ℝ 2 (fun q : ℂ × ComplexModel n => c q.1 q.2))
    (hXh : DifferentiableOn ℂ X (ball 0 ρ)) (m l : Fin n) :
    Integrable (fun ζ => dbarDir (coordinateVector l) (holDeriv p (c 0) (curveDz c)) ζ *
      dDir (coordinateVector m) (cutHad X m l) ζ) := by
  have h1 := (contDiff_dbarDir (v := coordinateVector l) (k := 0)
    (by simpa using contDiff_holDeriv_curve hp hc)).continuous
  have h2 := (contDiff_dDir (v := coordinateVector m) (k := 0)
    ((contDiff_cutHad hρ hXh m l).of_le (by norm_cast))).continuous
  exact (h1.mul h2).integrable_of_hasCompactSupport
    (hasCompactSupport_of_unitBall fun ζ hζ => by simp [dDir_cutHad_eq_zero hζ])

theorem integrable_termB1_summand (hρ : 1 < ρ) (hp : ContDiff ℝ 2 p)
    (hc : ContDiff ℝ 2 (fun q : ℂ × ComplexModel n => c q.1 q.2))
    (hXh : DifferentiableOn ℂ X (ball 0 ρ)) (m l : Fin n) :
    Integrable (fun ζ => dbarDir (coordinateVector l) (cutHad X m l) ζ *
      dDir (coordinateVector m) (holDeriv p (c 0) (curveDz c)) ζ) := by
  have h1 := (contDiff_dbarDir (v := coordinateVector l) (k := 0)
    ((contDiff_cutHad hρ hXh m l).of_le (by norm_cast))).continuous
  have h2 := (contDiff_dDir (v := coordinateVector m) (k := 0)
    (by simpa using contDiff_holDeriv_curve hp hc)).continuous
  exact (h1.mul h2).integrable_of_hasCompactSupport
    (hasCompactSupport_of_unitBall fun ζ hζ => by simp [dbarDir_cutHad_eq_zero hζ])

theorem integrable_termC2_summand (hρ : 1 < ρ) (hp : ContDiff ℝ 2 p)
    (hc : ContDiff ℝ 2 (fun q : ℂ × ComplexModel n => c q.1 q.2))
    (hRh : DifferentiableOn ℂ R (ball 0 ρ)) (m l : Fin n) :
    Integrable (fun ζ => dbarDir (coordinateVector l)
      (dDir (coordinateVector m) (fun s => ((p (c 0 s) : ℝ) : ℂ))) ζ * cutHad R m l ζ) := by
  have h1 := (contDiff_dbarDir (v := coordinateVector l) (k := 0)
    (contDiff_dDir (v := coordinateVector m) (k := 1) (contDiff_ofReal_comp_curve hp hc))).continuous
  have h2 := ((contDiff_cutHad hρ hRh m l).of_le (by norm_cast) : ContDiff ℝ 0 _).continuous
  exact (h1.mul h2).integrable_of_hasCompactSupport
    (hasCompactSupport_of_unitBall fun ζ hζ => by simp [cutHad_eq_zero hζ.le])

theorem integrable_termC1_summand (hρ : 1 < ρ) (hp : ContDiff ℝ 2 p)
    (hc : ContDiff ℝ 2 (fun q : ℂ × ComplexModel n => c q.1 q.2))
    (hRh : DifferentiableOn ℂ R (ball 0 ρ)) (m l : Fin n) :
    Integrable (fun ζ => dbarDir (coordinateVector l) (cutHad R m l) ζ *
      dDir (coordinateVector m) (fun s => ((p (c 0 s) : ℝ) : ℂ)) ζ) := by
  have h1 := (contDiff_dbarDir (v := coordinateVector l) (k := 0)
    ((contDiff_cutHad hρ hRh m l).of_le (by norm_cast))).continuous
  have h2 := (contDiff_dDir (v := coordinateVector m) (k := 0)
    ((contDiff_ofReal_comp_curve hp hc).of_le (by norm_num))).continuous
  exact (h1.mul h2).integrable_of_hasCompactSupport
    (hasCompactSupport_of_unitBall fun ζ hζ => by simp [dbarDir_cutHad_eq_zero hζ])

/-! ### Integration by parts of the two non-square terms -/

/-- `∫ ∑_m χ X_m ∂_m ℓ = ∫ ∑_{m,l} ∂̄_l ℓ · ∂_m(χ₁ σ_{ml})`. -/
theorem integral_termB_eq (hρ : 1 < ρ) (hp : ContDiff ℝ 2 p)
    (hc : ContDiff ℝ 2 (fun q : ℂ × ComplexModel n => c q.1 q.2))
    (hXh : DifferentiableOn ℂ X (ball 0 ρ)) (hX0 : X 0 = 0) :
    ∫ ζ, termB p c X ζ = ∫ ζ, termB2 p c X ζ := by
  simp only [termB, termB2]
  rw [integral_finset_sum _ fun m _ => integrable_termB_summand hρ hp hc hXh m,
    integral_finset_sum _ fun m _ => integrable_finsetSum _ fun l _ =>
      integrable_termB2_summand hρ hp hc hXh m l]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e : (fun ζ => ((chi n (‖ζ‖ ^ 2) : ℂ) * X ζ m) *
      dDir (coordinateVector m) (holDeriv p (c 0) (curveDz c)) ζ) =
      fun ζ => ∑ l, dbarDir (coordinateVector l) (cutHad X m l) ζ *
        dDir (coordinateVector m) (holDeriv p (c 0) (curveDz c)) ζ := by
    funext ζ
    rw [chi_mul_coord_eq_sum hρ hXh hX0 m ζ, Finset.sum_mul]
  rw [e, integral_finset_sum _ fun l _ => integrable_termB1_summand hρ hp hc hXh m l,
    integral_finset_sum _ fun l _ => integrable_termB2_summand hρ hp hc hXh m l]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact integral_dbarDir_mul_dDir_swap (contDiff_holDeriv_curve hp hc)
    ((contDiff_cutHad hρ hXh m l).of_le (by norm_cast)) (hasCompactSupport_cutHad m l) _ _

/-- `∫ ∑_m χ R_m ∂_m (p ∘ Φ) = -∫ ∑_{m,l} ∂̄_l ∂_m (p ∘ Φ) · χ₁ ϱ_{ml}`. -/
theorem integral_termC_eq (hρ : 1 < ρ) (hp : ContDiff ℝ 2 p)
    (hc : ContDiff ℝ 2 (fun q : ℂ × ComplexModel n => c q.1 q.2))
    (hRh : DifferentiableOn ℂ R (ball 0 ρ)) (hR0 : R 0 = 0) :
    ∫ ζ, termC p c R ζ = ∫ ζ, termC2 p c R ζ := by
  simp only [termC, termC2]
  rw [integral_neg, integral_finset_sum _ fun m _ => integrable_termC_summand hρ hp hc hRh m,
    integral_finset_sum _ fun m _ => integrable_finsetSum _ fun l _ =>
      integrable_termC2_summand hρ hp hc hRh m l, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e : (fun ζ => ((chi n (‖ζ‖ ^ 2) : ℂ) * R ζ m) *
      dDir (coordinateVector m) (fun s => ((p (c 0 s) : ℝ) : ℂ)) ζ) =
      fun ζ => ∑ l, dbarDir (coordinateVector l) (cutHad R m l) ζ *
        dDir (coordinateVector m) (fun s => ((p (c 0 s) : ℝ) : ℂ)) ζ := by
    funext ζ
    rw [chi_mul_coord_eq_sum hρ hRh hR0 m ζ, Finset.sum_mul]
  rw [e, integral_finset_sum _ fun l _ => integrable_termC1_summand hρ hp hc hRh m l,
    integral_finset_sum _ fun l _ => integrable_termC2_summand hρ hp hc hRh m l,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h := integral_mul_dbarDir_eq_neg (μ := volume)
    (contDiff_dDir (v := coordinateVector m) (k := 1) (contDiff_ofReal_comp_curve hp hc))
    ((contDiff_cutHad hρ hRh m l).of_le (by norm_cast))
    (Or.inr (hasCompactSupport_cutHad m l)) (coordinateVector l)
  rw [← h]
  congr 1
  funext ζ
  ring


/-! ### The pointwise lower bound -/

theorem norm_coordinateVector (m : Fin n) : ‖(coordinateVector m : ComplexModel n)‖ = 1 := by
  simp [coordinateVector]

/-- **The pointwise lower bound** of the integrand after the integrations by parts. -/
theorem termA_add_re_ge {a₁ a₂ b₁ : ℝ} (hρ : 1 < ρ) (hp : ContDiff ℝ 2 p)
    (hc : ContDiff ℝ 2 (fun q : ℂ × ComplexModel n => c q.1 q.2))
    (hΦ : DifferentiableOn ℂ (c 0) (ball 0 ρ)) (hY : DifferentiableOn ℂ (curveDz c) (ball 0 ρ))
    (hXh : DifferentiableOn ℂ X (ball 0 ρ))
    (hpsh : ∀ ζ ∈ closedBall (0 : ComplexModel n) 1, ∀ v, 0 ≤ leviForm p (c 0 ζ) v)
    (ha₁ : ∀ m, ∀ ζ ∈ closedBall (0 : ComplexModel n) 1, ‖fderiv ℂ (fun s => X s m) ζ‖ ≤ a₁)
    (ha₂ : ∀ m, ∀ ζ ∈ closedBall (0 : ComplexModel n) 1,
      ‖fderiv ℂ (fderiv ℂ (fun s => X s m)) ζ‖ ≤ a₂)
    (hb₁ : ∀ m, ∀ ζ ∈ closedBall (0 : ComplexModel n) 1, ‖fderiv ℂ (fun s => R s m) ζ‖ ≤ b₁)
    (ζ : ComplexModel n) :
    -(((n : ℝ) ^ 2 * (a₁ + a₂)) ^ 2 * (chi n (‖ζ‖ ^ 2) * levTr (fun s => p (c 0 s)) ζ)) -
        4 * (n : ℝ) ^ 2 * b₁ * (-chiOne n (‖ζ‖ ^ 2) * levTr (fun s => p (c 0 s)) ζ) ≤
      termA p c ζ + 2 * (termB2 p c X ζ).re + 2 * (termC2 p c R ζ).re := by
  by_cases hζ1 : ‖ζ‖ ≤ 1
  swap
  · push_neg at hζ1
    simp [termA, termB2, termC2, chi_normSq_eq_zero hζ1.le, chiOne_normSq_eq_zero hζ1.le,
      dDir_cutHad_eq_zero hζ1, cutHad_eq_zero hζ1.le]
  have hζ : ζ ∈ closedBall (0 : ComplexModel n) 1 := by
    rw [mem_closedBall, dist_zero_right]; exact hζ1
  have hζρ : ζ ∈ ball (0 : ComplexModel n) ρ := closedBall_subset_ball hρ hζ
  have hopen : IsOpen (ball (0 : ComplexModel n) ρ) := isOpen_ball
  have hΦζ : DifferentiableAt ℂ (c 0) ζ := hΦ.differentiableAt (hopen.mem_nhds hζρ)
  have hYζ : DifferentiableAt ℂ (curveDz c) ζ := hY.differentiableAt (hopen.mem_nhds hζρ)
  have hΦ2 : ContDiffAt ℂ 2 (c 0) ζ :=
    (contDiffAt_of_differentiableOn_complex hΦ hopen hζρ).of_le (by norm_cast)
  have hc0 : ContDiff ℝ 2 (c 0) := hc.comp (contDiff_const.prodMk contDiff_id)
  have hg2 : ContDiff ℝ 2 (fun s => p (c 0 s)) := hp.comp hc0
  have hgpsh : ∀ v, 0 ≤ leviForm (fun s => p (c 0 s)) ζ v := by
    intro v
    rw [leviForm_comp_holomorphic hΦ2 hp.contDiffAt]
    exact hpsh ζ hζ _
  set T := levTr (fun s => p (c 0 s)) ζ with hT
  have hT0 : 0 ≤ T := levTr_nonneg hgpsh
  have hχ0 : 0 ≤ chi n (‖ζ‖ ^ 2) := chi_nonneg n _
  have hχ₁0 : 0 ≤ -chiOne n (‖ζ‖ ^ 2) := neg_nonneg.mpr (chiOne_nonpos n _)
  -- the vector `k`
  set k : Fin n → Fin n → ℂ := fun m l => conj (ζ m) * hadMat X m l ζ -
    (((1 - ‖ζ‖ ^ 2) ^ 2 : ℝ) : ℂ) * fderiv ℂ (hadMat X m l) ζ (coordinateVector m) with hk
  set kv : ComplexModel n := ∑ l, conj (∑ m, k m l) • coordinateVector l with hkv
  have hkbound : ∀ m l, ‖k m l‖ ≤ a₁ + a₂ := by
    intro m l
    have hζm : ‖ζ m‖ ≤ 1 := (PiLp.norm_apply_le ζ m).trans hζ1
    have hσ : ‖hadMat X m l ζ‖ ≤ a₁ := norm_hadamardCoeff_le (ha₁ m) l hζ
    have hdσ : ‖fderiv ℂ (hadMat X m l) ζ (coordinateVector m)‖ ≤ a₂ := by
      refine ((fderiv ℂ (hadMat X m l) ζ).le_opNorm _).trans ?_
      rw [norm_coordinateVector, mul_one]
      exact norm_fderiv_hadamardCoeff_le hρ (differentiableOn_coord hXh m) (ha₂ m) l hζ
    have hw0 : 0 ≤ (1 - ‖ζ‖ ^ 2) ^ 2 := sq_nonneg _
    have hw1 : (1 - ‖ζ‖ ^ 2) ^ 2 ≤ 1 := by
      have h0 : 0 ≤ ‖ζ‖ ^ 2 := sq_nonneg _
      have h1 : ‖ζ‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg ζ]
      nlinarith
    calc ‖k m l‖ ≤ ‖conj (ζ m) * hadMat X m l ζ‖ +
          ‖(((1 - ‖ζ‖ ^ 2) ^ 2 : ℝ) : ℂ) * fderiv ℂ (hadMat X m l) ζ (coordinateVector m)‖ :=
          norm_sub_le _ _
      _ = ‖ζ m‖ * ‖hadMat X m l ζ‖ +
          (1 - ‖ζ‖ ^ 2) ^ 2 * ‖fderiv ℂ (hadMat X m l) ζ (coordinateVector m)‖ := by
          rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hw0]
      _ ≤ 1 * a₁ + 1 * a₂ := by
          gcongr
      _ = a₁ + a₂ := by ring
  have hkvbound : ‖kv‖ ≤ (n : ℝ) ^ 2 * (a₁ + a₂) := by
    calc ‖kv‖ ≤ ∑ l, ‖conj (∑ m, k m l) • (coordinateVector l : ComplexModel n)‖ :=
          norm_sum_le _ _
      _ = ∑ l, ‖∑ m, k m l‖ := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [norm_smul, norm_coordinateVector, mul_one, Complex.norm_conj]
      _ ≤ ∑ l : Fin n, ∑ m : Fin n, (a₁ + a₂) :=
          Finset.sum_le_sum fun l _ => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun m _ => hkbound m l)
      _ = (n : ℝ) ^ 2 * (a₁ + a₂) := by simp [Finset.sum_const]; ring
  -- the square term
  have hB2 : termB2 p c X ζ =
      (chi n (‖ζ‖ ^ 2) : ℂ) * dbarDir kv (holDeriv p (c 0) (curveDz c)) ζ := by
    have hd : dbarDir kv (holDeriv p (c 0) (curveDz c)) ζ =
        ∑ l, (∑ m, k m l) * dbarDir (coordinateVector l) (holDeriv p (c 0) (curveDz c)) ζ := by
      rw [hkv, dbarDir_sum_dir]
      simp only [Complex.conj_conj]
    rw [hd, termB2]
    have hcut : ∀ m l, dDir (coordinateVector m) (cutHad X m l) ζ =
        (chi n (‖ζ‖ ^ 2) : ℂ) * k m l := fun m l => by
      rw [dDir_cutHad hXh m l hζρ]
    simp_rw [hcut]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  have hre := (re_dDir_holDeriv (p := p) (Φ := c 0) (Y := curveDz c) hp.contDiffAt hΦζ hYζ
    kv kv).2
  have hsq := neg_leviForm_le_add_two_hermRe hp.contDiffAt (curveDz c ζ)
    (fderiv ℂ (c 0) ζ kv) (hpsh ζ hζ _)
  have hnat : leviForm (fun s => p (c 0 s)) ζ kv = leviForm p (c 0 ζ) (fderiv ℂ (c 0) ζ kv) :=
    leviForm_comp_holomorphic hΦ2 hp.contDiffAt kv
  have htr := leviForm_le_levTr_mul hg2.contDiffAt hgpsh kv
  have hLX := hpsh ζ hζ (curveDzbar c ζ)
  have hkv2 : ‖kv‖ ^ 2 ≤ ((n : ℝ) ^ 2 * (a₁ + a₂)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hkvbound 2
  have hpart1 : -(((n : ℝ) ^ 2 * (a₁ + a₂)) ^ 2 * (chi n (‖ζ‖ ^ 2) * T)) ≤
      termA p c ζ + 2 * (termB2 p c X ζ).re := by
    rw [hB2, Complex.re_ofReal_mul, hre, termA]
    have h1 : T * ‖kv‖ ^ 2 ≤ T * ((n : ℝ) ^ 2 * (a₁ + a₂)) ^ 2 :=
      mul_le_mul_of_nonneg_left hkv2 hT0
    have h2 : -(chi n (‖ζ‖ ^ 2) * (T * ((n : ℝ) ^ 2 * (a₁ + a₂)) ^ 2)) ≤
        -(chi n (‖ζ‖ ^ 2) * leviForm p (c 0 ζ) (fderiv ℂ (c 0) ζ kv)) := by
      rw [← hnat]
      exact neg_le_neg (mul_le_mul_of_nonneg_left (htr.trans h1) hχ0)
    have h3 : -(chi n (‖ζ‖ ^ 2) * leviForm p (c 0 ζ) (fderiv ℂ (c 0) ζ kv)) ≤
        chi n (‖ζ‖ ^ 2) * (leviForm p (c 0 ζ) (curveDz c ζ) +
          2 * hermRe p (c 0 ζ) (curveDz c ζ) (fderiv ℂ (c 0) ζ kv)) := by
      rw [← mul_neg]; exact mul_le_mul_of_nonneg_left hsq hχ0
    have h4 : 0 ≤ chi n (‖ζ‖ ^ 2) * leviForm p (c 0 ζ) (curveDzbar c ζ) := mul_nonneg hχ0 hLX
    nlinarith
  -- the second-order term
  have hC2 : ‖∑ m, ∑ l, dbarDir (coordinateVector l)
      (dDir (coordinateVector m) (fun s => ((p (c 0 s) : ℝ) : ℂ))) ζ * cutHad R m l ζ‖ ≤
      2 * (n : ℝ) ^ 2 * b₁ * (-chiOne n (‖ζ‖ ^ 2) * T) := by
    have hterm : ∀ m l, ‖dbarDir (coordinateVector l)
        (dDir (coordinateVector m) (fun s => ((p (c 0 s) : ℝ) : ℂ))) ζ * cutHad R m l ζ‖ ≤
        2 * T * (-chiOne n (‖ζ‖ ^ 2) * b₁) := by
      intro m l
      have h1 : ‖dbarDir (coordinateVector l)
          (dDir (coordinateVector m) (fun s => ((p (c 0 s) : ℝ) : ℂ))) ζ‖ ≤ 2 * T := by
        have := norm_dbarDir_dDir_ofReal_le hg2.contDiffAt hgpsh (coordinateVector m)
          (coordinateVector l)
        have hm := leviForm_coord_le_levTr hgpsh m
        have hl := leviForm_coord_le_levTr hgpsh l
        linarith
      have h2 : ‖cutHad R m l ζ‖ ≤ -chiOne n (‖ζ‖ ^ 2) * b₁ := by
        rw [cutHad, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonpos (chiOne_nonpos n _)]
        exact mul_le_mul_of_nonneg_left (norm_hadamardCoeff_le (hb₁ m) l hζ) hχ₁0
      rw [norm_mul]
      exact mul_le_mul h1 h2 (norm_nonneg _) (by linarith)
    calc _ ≤ ∑ m : Fin n, ∑ l : Fin n, ‖dbarDir (coordinateVector l)
          (dDir (coordinateVector m) (fun s => ((p (c 0 s) : ℝ) : ℂ))) ζ * cutHad R m l ζ‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => norm_sum_le _ _)
      _ ≤ ∑ m : Fin n, ∑ l : Fin n, 2 * T * (-chiOne n (‖ζ‖ ^ 2) * b₁) :=
          Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun l _ => hterm m l
      _ = 2 * (n : ℝ) ^ 2 * b₁ * (-chiOne n (‖ζ‖ ^ 2) * T) := by
          simp [Finset.sum_const]; ring
  have hpart2 : -(4 * (n : ℝ) ^ 2 * b₁ * (-chiOne n (‖ζ‖ ^ 2) * T)) ≤
      2 * (termC2 p c R ζ).re := by
    rw [termC2, Complex.neg_re]
    have := Complex.re_le_norm (∑ m, ∑ l, dbarDir (coordinateVector l)
      (dDir (coordinateVector m) (fun s => ((p (c 0 s) : ℝ) : ℂ))) ζ * cutHad R m l ζ)
    linarith
  linarith

/-! ### The core estimate -/

/-- **The core joint Levi estimate** (abstract form, see the module docstring):
`L φ(0) ≥ -(n²(a₁+a₂))² ∫ χ T - 4 n² b₁ ∫ (-χ₁) T`, `φ(τ) = ∫ p(c(τ, ζ)) χ(|ζ|²) dζ`,
`T = levTr (p ∘ c(0, ·))`. -/
theorem leviForm_integral_ge {a₁ a₂ b₁ : ℝ} (hρ : 1 < ρ) (hp : ContDiff ℝ 2 p)
    (hc : ContDiff ℝ 2 (fun q : ℂ × ComplexModel n => c q.1 q.2))
    (hΦ : DifferentiableOn ℂ (c 0) (ball 0 ρ)) (hY : DifferentiableOn ℂ (curveDz c) (ball 0 ρ))
    (hXh : DifferentiableOn ℂ X (ball 0 ρ)) (hRh : DifferentiableOn ℂ R (ball 0 ρ))
    (hX0 : X 0 = 0) (hR0 : R 0 = 0)
    (hX : ∀ ζ ∈ ball (0 : ComplexModel n) ρ, fderiv ℂ (c 0) ζ (X ζ) = curveDzbar c ζ)
    (hR : ∀ ζ ∈ ball (0 : ComplexModel n) ρ,
      fderiv ℂ (c 0) ζ (R ζ) = curveLevi c ζ - fderiv ℂ (curveDz c) ζ (X ζ))
    (hpsh : ∀ ζ ∈ closedBall (0 : ComplexModel n) 1, ∀ v, 0 ≤ leviForm p (c 0 ζ) v)
    (ha₁ : ∀ m, ∀ ζ ∈ closedBall (0 : ComplexModel n) 1, ‖fderiv ℂ (fun s => X s m) ζ‖ ≤ a₁)
    (ha₂ : ∀ m, ∀ ζ ∈ closedBall (0 : ComplexModel n) 1,
      ‖fderiv ℂ (fderiv ℂ (fun s => X s m)) ζ‖ ≤ a₂)
    (hb₁ : ∀ m, ∀ ζ ∈ closedBall (0 : ComplexModel n) 1, ‖fderiv ℂ (fun s => R s m) ζ‖ ≤ b₁) :
    -(((n : ℝ) ^ 2 * (a₁ + a₂)) ^ 2 *
        ∫ ζ, chi n (‖ζ‖ ^ 2) * levTr (fun s => p (c 0 s)) ζ) -
      4 * (n : ℝ) ^ 2 * b₁ * ∫ ζ, -chiOne n (‖ζ‖ ^ 2) * levTr (fun s => p (c 0 s)) ζ ≤
    leviForm (fun τ => ∫ ζ, p (c τ ζ) * chi n (‖ζ‖ ^ 2)) 0 1 := by
  have hc0 : ContDiff ℝ 2 (c 0) := hc.comp (contDiff_const.prodMk contDiff_id)
  have hg2 : ContDiff ℝ 2 (fun s => p (c 0 s)) := hp.comp hc0
  have hcτ : ∀ ζ : ComplexModel n, ContDiff ℝ 2 (fun τ => c τ ζ) := fun ζ =>
    hc.comp (contDiff_id.prodMk contDiff_const)
  -- step 1: differentiation under the integral sign
  have hF : ContDiffOn ℝ 2 (fun q : ℂ × ComplexModel n => p (c q.1 q.2) * chi n (‖q.2‖ ^ 2))
      (univ ×ˢ univ) :=
    ((hp.comp hc).mul (((contDiff_chi_normSq (n := n)).of_le (by norm_cast)).comp
      contDiff_snd)).contDiffOn
  have hsupp : ∀ τ ∈ (univ : Set ℂ), ∀ ζ : ComplexModel n, 1 < ‖ζ‖ →
      p (c τ ζ) * chi n (‖ζ‖ ^ 2) = 0 := fun τ _ ζ hζ => by
    rw [chi_normSq_eq_zero hζ.le, mul_zero]
  have step1 : leviForm (fun τ => ∫ ζ, p (c τ ζ) * chi n (‖ζ‖ ^ 2)) 0 1 =
      ∫ ζ, chi n (‖ζ‖ ^ 2) * leviForm (fun τ => p (c τ ζ)) 0 1 := by
    rw [leviForm_integral_of_contDiffOn (μ := volume)
      (F := fun τ ζ => p (c τ ζ) * chi n (‖ζ‖ ^ 2)) isOpen_univ hF hsupp (mem_univ (0 : ℂ)) 1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    have e : (fun τ => p (c τ ζ) * chi n (‖ζ‖ ^ 2)) =
        (chi n (‖ζ‖ ^ 2)) • (fun τ => p (c τ ζ)) := by
      funext τ; simp [mul_comm]
    simp only
    rw [e, leviForm_smul (show ContDiffAt ℝ 2 (fun τ => p (c τ ζ)) 0 from
      (hp.comp (hcτ ζ)).contDiffAt)]
  -- integrability
  have hF2 : ContDiffOn ℝ 2 (fun q : ℂ × ComplexModel n => p (c q.1 q.2)) (univ ×ˢ univ) :=
    (hp.comp hc).contDiffOn
  have hD : Continuous (fun ζ : ComplexModel n => fderiv ℝ (fderiv ℝ (fun τ => p (c τ ζ))) 0) := by
    have h1 := continuousOn_fderiv2_param (F := fun τ ζ => p (c τ ζ)) isOpen_univ hF2
    rw [univ_prod_univ, continuousOn_univ] at h1
    exact h1.comp (continuous_const.prodMk continuous_id)
  have hLc : Continuous (fun ζ : ComplexModel n => leviForm (fun τ => p (c τ ζ)) 0 1) := by
    simp only [leviForm, realHessian_eq_fderiv]
    exact (((hD.clm_apply continuous_const).clm_apply continuous_const).add
      ((hD.clm_apply continuous_const).clm_apply continuous_const)).div_const 4
  have hIL : Integrable (fun ζ : ComplexModel n =>
      chi n (‖ζ‖ ^ 2) * leviForm (fun τ => p (c τ ζ)) 0 1) :=
    (((contDiff_chi_normSq (n := n)).continuous).mul hLc).integrable_of_hasCompactSupport
      (hasCompactSupport_of_unitBall_real fun ζ hζ => by simp [chi_normSq_eq_zero hζ.le])
  have hIB : Integrable (termB p c X) :=
    integrable_finsetSum _ fun m _ => integrable_termB_summand hρ hp hc hXh m
  have hIC : Integrable (termC p c R) :=
    integrable_finsetSum _ fun m _ => integrable_termC_summand hρ hp hc hRh m
  have hIB2 : Integrable (termB2 p c X) :=
    integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun l _ =>
      integrable_termB2_summand hρ hp hc hXh m l
  have hIC2 : Integrable (termC2 p c R) :=
    (integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun l _ =>
      integrable_termC2_summand hρ hp hc hRh m l).neg
  have hpt := chi_mul_leviForm_eq (p := p) (R := R) hρ hp hc hΦ hY hX hR
  have hIA : Integrable (termA p c) := by
    have e : termA p c = fun ζ => chi n (‖ζ‖ ^ 2) * leviForm (fun τ => p (c τ ζ)) 0 1 -
        2 * (termB p c X ζ).re - 2 * (termC p c R ζ).re := by
      funext ζ; rw [hpt ζ]; ring
    rw [e]
    exact (hIL.sub (hIB.re.const_mul 2)).sub (hIC.re.const_mul 2)
  have hTc : Continuous (levTr (fun s => p (c 0 s))) := continuous_levTr hg2
  have hIχT : Integrable (fun ζ : ComplexModel n =>
      chi n (‖ζ‖ ^ 2) * levTr (fun s => p (c 0 s)) ζ) :=
    (((contDiff_chi_normSq (n := n)).continuous).mul hTc).integrable_of_hasCompactSupport
      (hasCompactSupport_of_unitBall_real fun ζ hζ => by simp [chi_normSq_eq_zero hζ.le])
  have hIχ₁T : Integrable (fun ζ : ComplexModel n =>
      -chiOne n (‖ζ‖ ^ 2) * levTr (fun s => p (c 0 s)) ζ) :=
    (((contDiff_chiOne_normSq (n := n)).continuous.neg).mul hTc).integrable_of_hasCompactSupport
      (hasCompactSupport_of_unitBall_real fun ζ hζ => by simp [chiOne_normSq_eq_zero hζ.le])
  -- assembly
  have hIB' : Integrable (fun ζ => 2 * (termB p c X ζ).re) := hIB.re.const_mul 2
  have hIC' : Integrable (fun ζ => 2 * (termC p c R ζ).re) := hIC.re.const_mul 2
  have hIB2' : Integrable (fun ζ => 2 * (termB2 p c X ζ).re) := hIB2.re.const_mul 2
  have hIC2' : Integrable (fun ζ => 2 * (termC2 p c R ζ).re) := hIC2.re.const_mul 2
  have hIAB : Integrable (fun ζ => termA p c ζ + 2 * (termB p c X ζ).re) := hIA.add hIB'
  have hIAB2 : Integrable (fun ζ => termA p c ζ + 2 * (termB2 p c X ζ).re) := hIA.add hIB2'
  have hreB : ∫ ζ, (termB p c X ζ).re = (∫ ζ, termB p c X ζ).re := integral_re hIB
  have hreC : ∫ ζ, (termC p c R ζ).re = (∫ ζ, termC p c R ζ).re := integral_re hIC
  have hreB2 : ∫ ζ, (termB2 p c X ζ).re = (∫ ζ, termB2 p c X ζ).re := integral_re hIB2
  have hreC2 : ∫ ζ, (termC2 p c R ζ).re = (∫ ζ, termC2 p c R ζ).re := integral_re hIC2
  have hsplit : ∫ ζ, chi n (‖ζ‖ ^ 2) * leviForm (fun τ => p (c τ ζ)) 0 1 =
      ∫ ζ, (termA p c ζ + 2 * (termB2 p c X ζ).re + 2 * (termC2 p c R ζ).re) := by
    have h1 : ∫ ζ, chi n (‖ζ‖ ^ 2) * leviForm (fun τ => p (c τ ζ)) 0 1 =
        (∫ ζ, termA p c ζ) + 2 * (∫ ζ, termB p c X ζ).re + 2 * (∫ ζ, termC p c R ζ).re := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hIAB hIC',
        integral_add hIA hIB', integral_const_mul, integral_const_mul, hreB, hreC]
    have h2 : ∫ ζ, (termA p c ζ + 2 * (termB2 p c X ζ).re + 2 * (termC2 p c R ζ).re) =
        (∫ ζ, termA p c ζ) + 2 * (∫ ζ, termB2 p c X ζ).re + 2 * (∫ ζ, termC2 p c R ζ).re := by
      rw [integral_add hIAB2 hIC2', integral_add hIA hIB2', integral_const_mul,
        integral_const_mul, hreB2, hreC2]
    rw [h1, h2, integral_termB_eq hρ hp hc hXh hX0, integral_termC_eq hρ hp hc hRh hR0]
  have hI1 : Integrable (fun ζ : ComplexModel n => -(((n : ℝ) ^ 2 * (a₁ + a₂)) ^ 2 *
      (chi n (‖ζ‖ ^ 2) * levTr (fun s => p (c 0 s)) ζ))) := (hIχT.const_mul _).neg
  have hI2 : Integrable (fun ζ : ComplexModel n => 4 * (n : ℝ) ^ 2 * b₁ *
      (-chiOne n (‖ζ‖ ^ 2) * levTr (fun s => p (c 0 s)) ζ)) := hIχ₁T.const_mul _
  have hlow : -(((n : ℝ) ^ 2 * (a₁ + a₂)) ^ 2 *
        ∫ ζ, chi n (‖ζ‖ ^ 2) * levTr (fun s => p (c 0 s)) ζ) -
      4 * (n : ℝ) ^ 2 * b₁ * ∫ ζ, -chiOne n (‖ζ‖ ^ 2) * levTr (fun s => p (c 0 s)) ζ =
      ∫ ζ, (-(((n : ℝ) ^ 2 * (a₁ + a₂)) ^ 2 *
        (chi n (‖ζ‖ ^ 2) * levTr (fun s => p (c 0 s)) ζ)) - 4 * (n : ℝ) ^ 2 * b₁ *
          (-chiOne n (‖ζ‖ ^ 2) * levTr (fun s => p (c 0 s)) ζ)) := by
    rw [integral_sub hI1 hI2, integral_neg, integral_const_mul, integral_const_mul]
  rw [step1, hsplit, hlow]
  exact integral_mono (hI1.sub hI2) (hIAB2.add hIC2') fun ζ =>
    termA_add_re_ge hρ hp hc hΦ hY hXh hpsh ha₁ ha₂ hb₁ ζ

end Core

end SGPT.NPP.DN4
