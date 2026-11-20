import SGPT.Okounkov.TranscendentalWNLegendreSmoothFamily
import SGPT.Foundations.Analysis.Pending.HolomorphicMixedDensity
import SGPT.Foundations.Analysis.Pending.MixedDensityRankOneSlot

/-!
# The Monge–Ampère density of `F(z, log |τ|²)` (package WN-LEG)

Blueprint `claude-tok-wn-leg`, node `tok-wn-leg:smooth-family` (4).  In the situation of
`IsSmoothLegendreData D F α β`, let `ũ(q) = F(z, log |τ|²)` for `(z, τ) = stripModelEquiv N q`
(`uTilde`).  Then, for `z ∈ D`, `τ ≠ 0`, `y = log |τ|²` and `λ = ∂F/∂y (z, y)`,

  `MAdensity(ũ)(z, τ) = (N + 1)/π · F_yy(z, y)/|τ|² · MAdensity(û_λ)(z)`

(`smoothDensity_uTilde`), where `û_λ = legendreValue F · λ` and `MAdensity` is TN's
`smoothDensity` (`n!/πⁿ det (∂²/∂z_j∂z̄_k)`).

## Route

* `U(z, ζ) = F(z, Re ζ)` is `F` composed with the real-linear map `reLastMap`; its complex Hessian
  has last diagonal entry `F_yy/4` and Schur complement `schurMatrix F (z, Re ζ)`
  (`lastSchur_complexHessian_reLast`), so `det = F_yy/4 · det schurMatrix`
  (`det_eq_mul_det_lastSchur`).
* `U = ũ ∘ expLast` with the holomorphic map `expLast (z, ζ) = (z, e^{ζ/2})`, whose Jacobian
  determinant is `e^{ζ/2}/2`; TN's `mixedDensity_comp_holomorphic` gives
  `MAdensity(U)(q) = |e^{ζ/2}/2|² MAdensity(ũ)(expLast q)`.
* `schurMatrix F (z, Y(z, λ))` is the complex Hessian of `û_λ`
  (`IsSmoothLegendreData.complexHessian_legendreValue`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
  SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality
  SGPT.Foundations.Analysis.Pending.MixedDensityRankOneSlot
  SGPT.Foundations.Analysis.Pending.HolomorphicMixedDensity

variable {N : ℕ}

/-! ### Coordinates of `ℂᴺ⁺¹ = ℂᴺ × ℂ` -/

theorem stripModelEquiv_snd_eq (q : ComplexModel (N + 1)) :
    (stripModelEquiv N q).2 = q (Fin.last N) := by
  have h := stripModelEquiv_symm_apply_last (stripModelEquiv N q).1 (stripModelEquiv N q).2
  rw [Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply] at h
  exact h.symm

theorem stripModelEquiv_symm_zero_one :
    (stripModelEquiv N).symm (0, 1) = coordinateVector (Fin.last N) := by
  ext i
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · rw [stripModelEquiv_symm_apply_last]
    simp [coordinateVector]
  · rw [stripModelEquiv_symm_apply_castSucc]
    simp [coordinateVector, Fin.castSucc_ne_last]

theorem stripModelEquiv_coordinateVector_castSucc (j : Fin N) :
    stripModelEquiv N (coordinateVector j.castSucc) = (coordinateVector j, 0) := by
  rw [← stripModelEquiv_symm_coordinateVector, ContinuousLinearEquiv.apply_symm_apply]

theorem stripModelEquiv_coordinateVector_last :
    stripModelEquiv N (coordinateVector (Fin.last N)) = (0, 1) := by
  rw [← stripModelEquiv_symm_zero_one, ContinuousLinearEquiv.apply_symm_apply]

/-! ### `U(z, ζ) = F(z, Re ζ)` -/

/-- `q ↦ (z, Re ζ)` for `(z, ζ) = stripModelEquiv N q`, a real-linear map `ℂᴺ⁺¹ → ℂᴺ × ℝ`. -/
def reLastMap (N : ℕ) : ComplexModel (N + 1) →L[ℝ] ComplexModel N × ℝ :=
  (((ContinuousLinearMap.fst ℂ (ComplexModel N) ℂ).comp
      (stripModelEquiv N : ComplexModel (N + 1) →L[ℂ] ComplexModel N × ℂ)).restrictScalars ℝ).prod
    (Complex.reCLM.comp (((ContinuousLinearMap.snd ℂ (ComplexModel N) ℂ).comp
      (stripModelEquiv N : ComplexModel (N + 1) →L[ℂ] ComplexModel N × ℂ)).restrictScalars ℝ))

@[simp] theorem reLastMap_apply (q : ComplexModel (N + 1)) :
    reLastMap N q = ((stripModelEquiv N q).1, (stripModelEquiv N q).2.re) := rfl

theorem reLastMap_castSucc (j : Fin N) :
    reLastMap N (coordinateVector j.castSucc) = (coordinateVector j, 0) := by
  simp [stripModelEquiv_coordinateVector_castSucc]

theorem reLastMap_I_castSucc (j : Fin N) :
    reLastMap N (Complex.I • coordinateVector j.castSucc) = (Complex.I • coordinateVector j, 0) := by
  simp [map_smul, stripModelEquiv_coordinateVector_castSucc]

theorem reLastMap_last : reLastMap N (coordinateVector (Fin.last N)) = (0, 1) := by
  simp [stripModelEquiv_coordinateVector_last]

theorem reLastMap_I_last : reLastMap N (Complex.I • coordinateVector (Fin.last N)) = 0 := by
  simp [map_smul, stripModelEquiv_coordinateVector_last]

section Hessian

variable {F : ComplexModel N × ℝ → ℝ} {q : ComplexModel (N + 1)}

theorem complexHessian_comp_reLastMap_apply (hF : ContDiffAt ℝ 2 F (reLastMap N q))
    (j k : Fin (N + 1)) :
    complexHessian (fun x => F (reLastMap N x)) q j k =
      ((realHessian F (reLastMap N q) (reLastMap N (coordinateVector j))
            (reLastMap N (coordinateVector k)) +
          realHessian F (reLastMap N q) (reLastMap N (Complex.I • coordinateVector j))
            (reLastMap N (Complex.I • coordinateVector k)) : ℝ) : ℂ) / 4 +
        Complex.I * ((realHessian F (reLastMap N q) (reLastMap N (coordinateVector j))
            (reLastMap N (Complex.I • coordinateVector k)) -
          realHessian F (reLastMap N q) (reLastMap N (Complex.I • coordinateVector j))
            (reLastMap N (coordinateVector k)) : ℝ) : ℂ) / 4 := by
  simp only [complexHessian, realHessian_comp_clm (reLastMap N) hF]

theorem complexHessian_reLast_last (hF : ContDiffAt ℝ 2 F (reLastMap N q)) :
    complexHessian (fun x => F (reLastMap N x)) q (Fin.last N) (Fin.last N) =
      ((partialYY F (reLastMap N q) / 4 : ℝ) : ℂ) := by
  rw [complexHessian_comp_reLastMap_apply hF, reLastMap_last, reLastMap_I_last]
  simp [partialYY]

/-- An algebraic identity behind the Schur complement of the last entry. -/
theorem schur_entry_identity (p₁ p₂ p₃ p₄ a b a' b' c : ℝ) (hc : c ≠ 0) :
    ((p₁ + p₂ : ℝ) : ℂ) / 4 + Complex.I * ((p₃ - p₄ : ℝ) : ℂ) / 4 -
        ((a : ℂ) / 4 - Complex.I * (b : ℂ) / 4) * ((a' : ℂ) / 4 + Complex.I * (b' : ℂ) / 4) /
          ((c / 4 : ℝ) : ℂ) =
      (((p₁ - a * a' / c) + (p₂ - b * b' / c) : ℝ) : ℂ) / 4 +
        Complex.I * (((p₃ - a * b' / c) - (p₄ - b * a' / c) : ℝ) : ℂ) / 4 := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  push_cast
  field_simp
  linear_combination ((b : ℂ) * b') * Complex.I_sq

theorem lastSchur_complexHessian_reLast (hF : ContDiffAt ℝ 2 F (reLastMap N q))
    (hc : partialYY F (reLastMap N q) ≠ 0) :
    lastSchur (complexHessian (fun x => F (reLastMap N x)) q) = schurMatrix F (reLastMap N q) := by
  ext j k
  rw [lastSchur, complexHessian_reLast_last hF, complexHessian_comp_reLastMap_apply hF,
    complexHessian_comp_reLastMap_apply hF, complexHessian_comp_reLastMap_apply hF]
  simp only [reLastMap_castSucc, reLastMap_I_castSucc, reLastMap_last, reLastMap_I_last,
    realHessian_zero_left, realHessian_zero_right, add_zero, zero_sub, sub_zero]
  have hs₁ := realHessian_symm hF (0, 1) (coordinateVector k, 0)
  have hs₂ := realHessian_symm hF (0, 1) (Complex.I • coordinateVector k, 0)
  rw [hs₁, hs₂, schurMatrix, schurForm, schurForm, schurForm, schurForm]
  have := schur_entry_identity
    (realHessian F (reLastMap N q) (coordinateVector j, 0) (coordinateVector k, 0))
    (realHessian F (reLastMap N q) (Complex.I • coordinateVector j, 0)
      (Complex.I • coordinateVector k, 0))
    (realHessian F (reLastMap N q) (coordinateVector j, 0) (Complex.I • coordinateVector k, 0))
    (realHessian F (reLastMap N q) (Complex.I • coordinateVector j, 0) (coordinateVector k, 0))
    (realHessian F (reLastMap N q) (coordinateVector j, 0) (0, 1))
    (realHessian F (reLastMap N q) (Complex.I • coordinateVector j, 0) (0, 1))
    (realHessian F (reLastMap N q) (coordinateVector k, 0) (0, 1))
    (realHessian F (reLastMap N q) (Complex.I • coordinateVector k, 0) (0, 1))
    (partialYY F (reLastMap N q)) hc
  push_cast at this ⊢
  linear_combination this

/-- **The determinant of the complex Hessian of `F(z, Re ζ)`** (`tok-wn-leg:schur`). -/
theorem det_complexHessian_reLast (hF : ContDiffAt ℝ 2 F (reLastMap N q))
    (hc : partialYY F (reLastMap N q) ≠ 0) :
    (complexHessian (fun x => F (reLastMap N x)) q).det =
      ((partialYY F (reLastMap N q) / 4 : ℝ) : ℂ) * (schurMatrix F (reLastMap N q)).det := by
  have hlast := complexHessian_reLast_last hF
  have hne : complexHessian (fun x => F (reLastMap N x)) q (Fin.last N) (Fin.last N) ≠ 0 := by
    rw [hlast]
    exact_mod_cast div_ne_zero hc (by norm_num)
  rw [det_eq_mul_det_lastSchur _ hne, hlast, lastSchur_complexHessian_reLast hF hc]

theorem smoothDensity_comp_reLastMap (hF : ContDiffAt ℝ 2 F (reLastMap N q))
    (hc : partialYY F (reLastMap N q) ≠ 0) :
    smoothDensity (fun x => F (reLastMap N x)) q =
      ((N + 1).factorial : ℝ) / Real.pi ^ (N + 1) * (partialYY F (reLastMap N q) / 4) *
        (schurMatrix F (reLastMap N q)).det.re := by
  rw [smoothDensity, det_complexHessian_reLast hF hc, Complex.re_ofReal_mul]
  ring

end Hessian

/-! ### The holomorphic map `(z, ζ) ↦ (z, e^{ζ/2})` -/

/-- `(z, ζ) ↦ (z, e^{ζ/2})` on `ℂᴺ⁺¹` (last coordinate `ζ`). -/
def expLast (N : ℕ) (q : ComplexModel (N + 1)) : ComplexModel (N + 1) :=
  q + (Complex.exp (q (Fin.last N) / 2) - q (Fin.last N)) • coordinateVector (Fin.last N)

theorem stripModelEquiv_expLast (q : ComplexModel (N + 1)) :
    stripModelEquiv N (expLast N q) =
      ((stripModelEquiv N q).1, Complex.exp (q (Fin.last N) / 2)) := by
  rw [expLast, map_add, map_smul, stripModelEquiv_coordinateVector_last]
  ext
  · simp
  · simp [stripModelEquiv_snd_eq]

/-- `log |e^{ζ/2}|² = Re ζ`. -/
theorem logNormSq_exp_half_complex (ζ : ℂ) : logNormSq (Complex.exp (ζ / 2)) = ζ.re := by
  rw [logNormSq, norm_exp_half, ← Real.exp_nat_mul]
  push_cast
  rw [show (2 : ℝ) * (ζ.re / 2) = ζ.re by ring, Real.log_exp]

/-- The function `ũ(q) = F(z, log |τ|²)`, `(z, τ) = stripModelEquiv N q`, on `ℂᴺ⁺¹`. -/
def uTilde (F : ComplexModel N × ℝ → ℝ) (q : ComplexModel (N + 1)) : ℝ :=
  F ((stripModelEquiv N q).1, logNormSq (stripModelEquiv N q).2)

theorem uTilde_expLast (F : ComplexModel N × ℝ → ℝ) (q : ComplexModel (N + 1)) :
    uTilde F (expLast N q) = F (reLastMap N q) := by
  rw [uTilde, stripModelEquiv_expLast, logNormSq_exp_half_complex, reLastMap_apply,
    stripModelEquiv_snd_eq]

/-- The last coordinate as a `ℂ`-linear map. -/
def lastProj (N : ℕ) : ComplexModel (N + 1) →L[ℂ] ℂ := EuclideanSpace.proj (Fin.last N)

@[simp] theorem lastProj_apply (q : ComplexModel (N + 1)) : lastProj N q = q (Fin.last N) := rfl

theorem expLast_eq : expLast N = fun q =>
    q + (Complex.exp (lastProj N q / 2) - lastProj N q) • coordinateVector (Fin.last N) := rfl

theorem contDiff_expLast : ContDiff ℂ ∞ (expLast N) := by
  rw [expLast_eq]
  have hp : ContDiff ℂ ∞ (lastProj N) := (lastProj N).contDiff
  exact contDiff_id.add
    (((Complex.contDiff_exp.comp (hp.div_const 2)).sub hp).smul contDiff_const)

theorem hasFDerivAt_expLast (q : ComplexModel (N + 1)) :
    HasFDerivAt (expLast N)
      (ContinuousLinearMap.id ℂ (ComplexModel (N + 1)) +
        ((Complex.exp (q (Fin.last N) / 2) / 2 - 1) • lastProj N).smulRight
          (coordinateVector (Fin.last N))) q := by
  rw [expLast_eq]
  have hg : HasDerivAt (fun ζ : ℂ => Complex.exp (ζ / 2) - ζ)
      (Complex.exp (q (Fin.last N) / 2) / 2 - 1) (q (Fin.last N)) := by
    have h1 : HasDerivAt (fun ζ : ℂ => ζ / 2) (1 / 2) (q (Fin.last N)) :=
      (hasDerivAt_id _).div_const 2
    have h2 := (Complex.hasDerivAt_exp _).comp (q (Fin.last N)) h1
    have h3 := h2.sub (hasDerivAt_id (q (Fin.last N)))
    exact h3.congr_deriv (by ring)
  have hcomp : HasFDerivAt (fun x : ComplexModel (N + 1) =>
      Complex.exp (lastProj N x / 2) - lastProj N x)
      ((Complex.exp (q (Fin.last N) / 2) / 2 - 1) • lastProj N) q := by
    have := hg.hasFDerivAt.comp q (lastProj N).hasFDerivAt
    refine this.congr_fderiv ?_
    ext v
    simp [mul_comm]
  exact (hasFDerivAt_id q).add (hcomp.smul_const _)

theorem jacobianMatrix_expLast (q : ComplexModel (N + 1)) :
    jacobianMatrix (expLast N) q =
      Matrix.diagonal fun a => if a = Fin.last N then Complex.exp (q (Fin.last N) / 2) / 2 else 1 := by
  have hd : DifferentiableAt ℂ (expLast N) q := (hasFDerivAt_expLast q).differentiableAt
  ext a j
  simp only [jacobianMatrix, Matrix.of_apply]
  rw [hd.fderiv_restrictScalars ℝ, ContinuousLinearMap.coe_restrictScalars',
    (hasFDerivAt_expLast q).fderiv]
  by_cases haj : a = j
  · subst haj
    by_cases ha : a = Fin.last N
    · subst ha
      simp [coordinateVector]
    · simp [coordinateVector, ha]
  · rw [Matrix.diagonal_apply_ne _ haj]
    by_cases hj : j = Fin.last N
    · subst hj
      simp [coordinateVector, haj]
    · simp [coordinateVector, haj, hj]

theorem det_jacobianMatrix_expLast (q : ComplexModel (N + 1)) :
    (jacobianMatrix (expLast N) q).det = Complex.exp (q (Fin.last N) / 2) / 2 := by
  rw [jacobianMatrix_expLast, Matrix.det_diagonal, Fin.prod_univ_castSucc]
  simp [Fin.castSucc_ne_last]

theorem normSq_det_jacobianMatrix_expLast (q : ComplexModel (N + 1)) :
    Complex.normSq (jacobianMatrix (expLast N) q).det = Real.exp (q (Fin.last N)).re / 4 := by
  rw [det_jacobianMatrix_expLast, Complex.normSq_div, Complex.normSq_eq_norm_sq,
    norm_exp_half, ← Real.exp_nat_mul]
  push_cast
  rw [show (2 : ℝ) * ((q (Fin.last N)).re / 2) = (q (Fin.last N)).re by ring]
  norm_num [Complex.normSq_apply]

/-! ### The density identity -/

section Density

variable {D : Set (ComplexModel N)} {F : ComplexModel N × ℝ → ℝ} {α β : ℝ}

/-- `Ω × ℂ` in the model `ℂᴺ⁺¹`. -/
def stripDomain (D : Set (ComplexModel N)) : Set (ComplexModel (N + 1)) :=
  {q | (stripModelEquiv N q).1 ∈ D}

/-- `Ω × ℂ*` in the model `ℂᴺ⁺¹`. -/
def puncturedDomain (D : Set (ComplexModel N)) : Set (ComplexModel (N + 1)) :=
  {q | (stripModelEquiv N q).1 ∈ D ∧ (stripModelEquiv N q).2 ≠ 0}

theorem isOpen_stripDomain (hD : IsOpen D) : IsOpen (stripDomain D) :=
  hD.preimage (continuous_fst.comp (stripModelEquiv N).continuous)

theorem isOpen_puncturedDomain (hD : IsOpen D) : IsOpen (puncturedDomain D) :=
  (hD.preimage (continuous_fst.comp (stripModelEquiv N).continuous)).inter
    (isOpen_ne.preimage (continuous_snd.comp (stripModelEquiv N).continuous))

theorem contDiffAt_logNormSq {τ : ℂ} (hτ : τ ≠ 0) : ContDiffAt ℝ ∞ logNormSq τ := by
  have hn : ‖τ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hτ)
  exact (Real.contDiffAt_log.mpr hn).comp τ (contDiff_norm_sq ℝ).contDiffAt

theorem contDiffOn_uTilde (hF : ContDiffOn ℝ ∞ F (D ×ˢ univ)) :
    ContDiffOn ℝ ∞ (uTilde F) (puncturedDomain D) := by
  have hfst : ContDiff ℝ ∞ fun q : ComplexModel (N + 1) => (stripModelEquiv N q).1 :=
    (((ContinuousLinearMap.fst ℂ (ComplexModel N) ℂ).comp
      (stripModelEquiv N : ComplexModel (N + 1) →L[ℂ] ComplexModel N × ℂ)).restrictScalars
        ℝ).contDiff
  have hsnd : ContDiff ℝ ∞ fun q : ComplexModel (N + 1) => (stripModelEquiv N q).2 :=
    (((ContinuousLinearMap.snd ℂ (ComplexModel N) ℂ).comp
      (stripModelEquiv N : ComplexModel (N + 1) →L[ℂ] ComplexModel N × ℂ)).restrictScalars
        ℝ).contDiff
  have hinner : ContDiffOn ℝ ∞ (fun q : ComplexModel (N + 1) =>
      ((stripModelEquiv N q).1, logNormSq (stripModelEquiv N q).2)) (puncturedDomain D) := by
    intro q hq
    refine (hfst.contDiffAt.prodMk ?_).contDiffWithinAt
    exact ContDiffAt.comp (g := logNormSq) (f := fun q => (stripModelEquiv N q).2) q
      (contDiffAt_logNormSq hq.2) hsnd.contDiffAt
  exact hF.comp hinner fun q hq => ⟨hq.1, mem_univ _⟩

namespace IsSmoothLegendreData

variable (h : IsSmoothLegendreData D F α β)
include h

/-- `MAdensity(U)(q) = |e^{ζ/2}/2|² MAdensity(ũ)(expLast q)` for `U = ũ ∘ expLast`. -/
theorem smoothDensity_reLast_eq {q : ComplexModel (N + 1)} (hq : q ∈ stripDomain D) :
    smoothDensity (fun x => F (reLastMap N x)) q =
      Real.exp (q (Fin.last N)).re / 4 * smoothDensity (uTilde F) (expLast N q) := by
  have hmaps : MapsTo (expLast N) (stripDomain D) (puncturedDomain D) := by
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [stripModelEquiv_expLast]
      exact hx
    · rw [stripModelEquiv_expLast]
      exact Complex.exp_ne_zero _
  have hm := mixedDensity_comp_holomorphic (f := fun _ : Fin (N + 1) => uTilde F)
    (isOpen_stripDomain h.isOpen) (isOpen_puncturedDomain h.isOpen)
    (contDiff_expLast.contDiffOn) (fun _ => contDiffOn_uTilde h.contDiffOn) hmaps hq
  simp only [mixedDensity_diagonal, uTilde_expLast] at hm
  rw [hm, normSq_det_jacobianMatrix_expLast]

/-- **The pointwise Monge–Ampère density identity** (`tok-wn-leg:smooth-family` (4)):
`MAdensity(ũ)(z, τ) = (N + 1)/π · F_yy(z, y)/|τ|² · MAdensity(û_λ)(z)`, `y = log |τ|²`,
`λ = ∂F/∂y (z, y)`. -/
theorem smoothDensity_uTilde {z : ComplexModel N} (hz : z ∈ D) {τ : ℂ} (hτ : τ ≠ 0) :
    smoothDensity (uTilde F) ((stripModelEquiv N).symm (z, τ)) =
      ((N + 1 : ℕ) : ℝ) / Real.pi * (partialYY F (z, logNormSq τ) / ‖τ‖ ^ 2) *
        smoothDensity (fun z' => legendreValue F z' (partialY F (z, logNormSq τ))) z := by
  set q : ComplexModel (N + 1) := (stripModelEquiv N).symm (z, 2 * Complex.log τ) with hq_def
  have hqe : stripModelEquiv N q = (z, 2 * Complex.log τ) := by
    rw [hq_def, ContinuousLinearEquiv.apply_symm_apply]
  have hqlast : q (Fin.last N) = 2 * Complex.log τ := by
    rw [← stripModelEquiv_snd_eq, hqe]
  have hexp : expLast N q = (stripModelEquiv N).symm (z, τ) := by
    apply (stripModelEquiv N).injective
    rw [stripModelEquiv_expLast, hqe, hqlast, ContinuousLinearEquiv.apply_symm_apply]
    simp only [Prod.mk.injEq, true_and]
    rw [show 2 * Complex.log τ / 2 = Complex.log τ by ring, Complex.exp_log hτ]
  have hy : (2 * Complex.log τ).re = logNormSq τ := by
    rw [logNormSq, Real.log_pow]
    simp [Complex.log_re]
  have hrl : reLastMap N q = (z, logNormSq τ) := by
    rw [reLastMap_apply, hqe, hy]
  have hqD : q ∈ stripDomain D := by
    show (stripModelEquiv N q).1 ∈ D
    rw [hqe]
    exact hz
  have hF2 : ContDiffAt ℝ 2 F (reLastMap N q) := by
    rw [hrl]
    exact h.contDiffAt_two hz _
  have hc : partialYY F (reLastMap N q) ≠ 0 := by
    rw [hrl]
    exact (h.partialYY_pos z hz _).ne'
  have h1 := h.smoothDensity_reLast_eq hqD
  rw [smoothDensity_comp_reLastMap hF2 hc, hexp, hqlast, hy, hrl] at h1
  have hτ2 : Real.exp (logNormSq τ) = ‖τ‖ ^ 2 := by
    rw [logNormSq, Real.exp_log (pow_pos (norm_pos_iff.mpr hτ) 2)]
  rw [hτ2] at h1
  set lam := partialY F (z, logNormSq τ) with hlam_def
  have hlam : lam ∈ Ioo α β := h.partialY_mem z hz _
  have hw : smoothDensity (fun z' => legendreValue F z' lam) z =
      (N.factorial : ℝ) / Real.pi ^ N * (schurMatrix F (z, logNormSq τ)).det.re := by
    rw [smoothDensity, h.complexHessian_legendreValue hz hlam, hlam_def,
      h.legendreArg_partialY hz]
  rw [hw]
  have hpos : 0 < ‖τ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hτ) 2
  have hpi : 0 < Real.pi := Real.pi_pos
  have hfact : ((N + 1).factorial : ℝ) = ((N + 1 : ℕ) : ℝ) * (N.factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hfact] at h1
  field_simp at h1 ⊢
  linear_combination (-1 : ℝ) * h1

end IsSmoothLegendreData

end Density

end SGPT.Okounkov.TranscendentalWN
