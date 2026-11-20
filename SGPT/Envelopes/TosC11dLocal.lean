import SGPT.Envelopes.TosC11dFrame
import SGPT.Envelopes.TosC11bAbsorption

/-!
# The real-Hessian bound at the maximum point (local form of FPT `lem:penalized-real-hessian`)

Lane TOS-C11d (`claude-tos-c11d`, node `tos-c11d:local`).  Source: Xia, *Foundations of
pluripotential theory*, `lem:penalized-real-hessian`, Steps 2–4, after Tosatti (2018) and
Chu–Tosatti–Weinkove, for SGPT `thm:Tos_C11` (Tosatti, Chu–Zhou).

`local_bound`: fix `n > 0` and bounds `Cg, R, S, CF, BF`.  There are `A > 0` and `Λ` such that the
following holds.  Let `ψ, a, F` be smooth on `ℂⁿ`, with `0` the centre of normal coordinates for the
metric `g = metricOf ψ` (`NormalAt ψ`, second and third derivatives of `g` at `0` bounded by `Cg`),
with the penalized equation `det H(ψ + a) = e^{β(a - F)} det H(ψ)` near `0` (`β ≥ 0`),
`H(ψ + a)(0) = diag(r)` positive with `rᵢ ≤ R`, `‖DF(0)‖ ≤ CF`, `D²F(0) ≤ BF`, `s(0) ≤ S`, and suppose
that `0` is a maximum point of `(∇²a(Y, Y)/g(Y, Y)) e^{w}` with
`w = -(τ/2) log(1 + S - s) - A a`, `τ = (1 + 2 CF²)⁻¹`.  Then `D²a(0)(Y, Y) ≤ Λ ‖Y‖²`.

The proof: the eigenbasis of `D²a(0)` and the perturbation `B₀` (`frame_ineq` along the `2n`
real directions `eᵢ, i eᵢ`); weighted sums give `D_G log λ₁`, `D_G s`, `D_G a` and their bounds via
the differentiated equation (`NormalAt.equation_line`); then `TosC11b.max_inequality_of_components`,
the splitting identity (`cz_split`), `TosC11b.third_order_absorption`,
`TosC11b.four_eps_mul_sum_le` and `TosC11b.eta_K_add_T_le` give `η' K + T ≤ A n`, which bounds
`D²a(0)` on the real frame and hence the largest eigenvalue.
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

variable {n : ℕ}

/-- A sum over the real frame `eᵢ, i eᵢ` with the weights `1/(4 rᵢ)`. -/
def frameSum (r : Fin n → ℝ) (Q : ComplexModel n → ℝ) : ℝ :=
  ∑ i, (Q (TosC11c.stdVec i) + Q (Complex.I • TosC11c.stdVec i)) / (4 * r i)

theorem frameSum_add (r : Fin n → ℝ) (Q Q' : ComplexModel n → ℝ) :
    frameSum r (fun v => Q v + Q' v) = frameSum r Q + frameSum r Q' := by
  simp only [frameSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem frameSum_sub (r : Fin n → ℝ) (Q Q' : ComplexModel n → ℝ) :
    frameSum r (fun v => Q v - Q' v) = frameSum r Q - frameSum r Q' := by
  simp only [frameSum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem frameSum_const_mul (r : Fin n → ℝ) (c : ℝ) (Q : ComplexModel n → ℝ) :
    frameSum r (fun v => c * Q v) = c * frameSum r Q := by
  simp only [frameSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem frameSum_nonpos {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) {Q : ComplexModel n → ℝ}
    (hQ : ∀ i, Q (TosC11c.stdVec i) ≤ 0 ∧ Q (Complex.I • TosC11c.stdVec i) ≤ 0) :
    frameSum r Q ≤ 0 :=
  Finset.sum_nonpos fun i _ => div_nonpos_of_nonpos_of_nonneg (by linarith [hQ i])
    (by linarith [hr i])

theorem frameSum_le {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) {Q : ComplexModel n → ℝ} {c : ℝ}
    (hQ : ∀ i, Q (TosC11c.stdVec i) ≤ c ∧ Q (Complex.I • TosC11c.stdVec i) ≤ c) :
    frameSum r Q ≤ c / 2 * ∑ i, (r i)⁻¹ := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hri := hr i
  rw [div_le_iff₀ (by positivity)]
  have := hQ i
  have e : c / 2 * (r i)⁻¹ * (4 * r i) = 2 * c := by field_simp; ring
  rw [e]; linarith

theorem le_frameSum {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) {Q : ComplexModel n → ℝ} {c : ℝ}
    (hQ : ∀ i, c ≤ Q (TosC11c.stdVec i) ∧ c ≤ Q (Complex.I • TosC11c.stdVec i)) :
    c / 2 * ∑ i, (r i)⁻¹ ≤ frameSum r Q := by
  have h := frameSum_le (r := r) (Q := fun v => -Q v) (c := -c) hr fun i =>
    ⟨by linarith [(hQ i).1], by linarith [(hQ i).2]⟩
  have e : frameSum r (fun v => -Q v) = -frameSum r Q := by
    simp only [frameSum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e] at h
  linarith

/-! ### Weighted frame sums of jets -/

section Identities

variable {a : ComplexModel n → ℝ}

theorem frameSum_d4 (ha : ContDiff ℝ ∞ a) (r : Fin n → ℝ) (b : ComplexModel n) :
    frameSum r (fun v => fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ a))) 0 v v b b) =
      ∑ i, (cHm (leviBil (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ a))) 0 b b)) i i).re / r i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  beta_reduce
  rw [cHm_re_diag, leviBil_apply, d4_pairs ha 0 (TosC11c.stdVec i),
    d4_pairs ha 0 (Complex.I • TosC11c.stdVec i), coordinateVector_eq_stdVec]
  field_simp

theorem frameSum_d3 (ha : ContDiff ℝ ∞ a) (r : Fin n → ℝ) (u : ComplexModel n) :
    frameSum r (fun v => fderiv ℝ (fderiv ℝ (fderiv ℝ a)) 0 v v u) =
      ∑ i, (cHm (leviBil (fderiv ℝ (fderiv ℝ (fderiv ℝ a)) 0 u)) i i).re / r i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  beta_reduce
  rw [cHm_re_diag, leviBil_apply, d3_symm₁₃ ha 0 (TosC11c.stdVec i),
    d3_symm₁₃ ha 0 (Complex.I • TosC11c.stdVec i), d3_symm₂₃ ha 0 u (TosC11c.stdVec i),
    d3_symm₂₃ ha 0 u (Complex.I • TosC11c.stdVec i), coordinateVector_eq_stdVec]
  field_simp

theorem frameSum_d2 (r : Fin n → ℝ) :
    frameSum r (fun v => fderiv ℝ (fderiv ℝ a) 0 v v) =
      ∑ i, (complexHessian a 0 i i).re / r i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  beta_reduce
  rw [complexHessian_diagonal_re, leviForm, realHessian_eq_fderiv, realHessian_eq_fderiv,
    coordinateVector_eq_stdVec]
  field_simp

/-- **The splitting identity** `eq:real-hessian-third-splitting` with its error term: for the
derivatives `m₁(v) = D³a(0) v - K₁(v)` of the covariant Hessian, `b₁` a unit vector of an orthonormal
basis `b` and `Z_{iq} = ∂_{b₁} G_{i q̄}`,
`∂ᵢ m₁(b₁, b₁) - √2 Σ_q ν̄_q Z_{iq} + i Σ_{α ≠ i₁} μ_α ∂ᵢ m₁(b₁, b_α) = -∂ᵢ K₁(b₁, b₁) - i ∂ᵢ K₁(b₁, i b₁)`
with `ν_q = √2 (b₁)_q`, `μ_α = ⟪i b₁, b_α⟫`. -/
theorem split_identity (ha : ContDiff ℝ ∞ a) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K₁ : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (b : OrthonormalBasis ι ℝ (ComplexModel n)) (i₁ : ι) (i : Fin n) :
    cz ((fderiv ℝ (fderiv ℝ (fderiv ℝ a)) 0 (TosC11c.stdVec i) - K₁ (TosC11c.stdVec i)) (b i₁) (b i₁))
        ((fderiv ℝ (fderiv ℝ (fderiv ℝ a)) 0 (Complex.I • TosC11c.stdVec i) -
          K₁ (Complex.I • TosC11c.stdVec i)) (b i₁) (b i₁)) -
      ((Real.sqrt 2 : ℂ) * ∑ q, conj ((Real.sqrt 2 : ℂ) * b i₁ q) *
          cHm (leviBil (fderiv ℝ (fderiv ℝ (fderiv ℝ a)) 0 (b i₁))) i q -
        Complex.I * ∑ α ∈ Finset.univ.erase i₁, ((⟪Complex.I • b i₁, b α⟫ : ℝ) : ℂ) *
          cz ((fderiv ℝ (fderiv ℝ (fderiv ℝ a)) 0 (TosC11c.stdVec i) - K₁ (TosC11c.stdVec i))
              (b i₁) (b α))
            ((fderiv ℝ (fderiv ℝ (fderiv ℝ a)) 0 (Complex.I • TosC11c.stdVec i) -
              K₁ (Complex.I • TosC11c.stdVec i)) (b i₁) (b α))) =
      -cz (K₁ (TosC11c.stdVec i) (b i₁) (b i₁)) (K₁ (Complex.I • TosC11c.stdVec i) (b i₁) (b i₁)) -
        Complex.I * cz (K₁ (TosC11c.stdVec i) (b i₁) (Complex.I • b i₁))
          (K₁ (Complex.I • TosC11c.stdVec i) (b i₁) (Complex.I • b i₁)) := by
  set T := fderiv ℝ (fderiv ℝ (fderiv ℝ a)) 0 with hT
  set e := TosC11c.stdVec i with he
  set f := Complex.I • TosC11c.stdVec i with hf
  set b₁ := b i₁ with hb₁
  -- the sum over the eigenbasis reproduces `i b₁`
  have hcJ0 : ⟪Complex.I • b₁, b₁⟫ = 0 := by rw [real_inner_comm]; exact inner_I_smul_self b₁
  have hsumv : ∑ α ∈ Finset.univ.erase i₁, ⟪Complex.I • b₁, b α⟫ • b α = Complex.I • b₁ := by
    have h := b.sum_repr' (Complex.I • b₁)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₁)] at h
    rw [← hb₁, real_inner_comm, hcJ0, zero_smul, zero_add] at h
    refine (Finset.sum_congr rfl fun α _ => ?_).trans h
    rw [real_inner_comm]
  have hlin : ∀ L : ComplexModel n →L[ℝ] ℝ, ∑ α ∈ Finset.univ.erase i₁,
      ⟪Complex.I • b₁, b α⟫ * L (b α) = L (Complex.I • b₁) := fun L => by
    conv_rhs => rw [← hsumv]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
  have hsumY : ∑ α ∈ Finset.univ.erase i₁, ((⟪Complex.I • b₁, b α⟫ : ℝ) : ℂ) *
      cz ((T e - K₁ e) b₁ (b α)) ((T f - K₁ f) b₁ (b α)) =
      cz ((T e - K₁ e) b₁ (Complex.I • b₁)) ((T f - K₁ f) b₁ (Complex.I • b₁)) := by
    simp only [← cz_smul]
    rw [← cz_sum, hlin ((T e - K₁ e) b₁), hlin ((T f - K₁ f) b₁)]
  -- the splitting of the third derivatives
  have hsplit := cz_split (T e b₁) (T f b₁) b₁
  have hZ : ∀ q, cz (T e b₁ (TosC11c.stdVec q)) (T f b₁ (TosC11c.stdVec q)) +
      Complex.I * cz (T e b₁ (Complex.I • TosC11c.stdVec q)) (T f b₁ (Complex.I • TosC11c.stdVec q)) =
      2 * cHm (leviBil (T b₁)) i q := by
    intro q
    simp only [cHm, leviBil_apply, coordinateVector_eq_stdVec, smul_smul, Complex.I_mul_I,
      neg_one_smul, map_neg]
    rw [hT, d3_symm₁₂ ha 0 e b₁, d3_symm₁₂ ha 0 f b₁, d3_symm₁₂ ha 0 e b₁,
      d3_symm₁₂ ha 0 f b₁]
    apply Complex.ext <;> simp [cz] <;> ring
  have hsq : ∀ q, (Real.sqrt 2 : ℂ) * (conj ((Real.sqrt 2 : ℂ) * b₁ q) *
      cHm (leviBil (T b₁)) i q) = conj (b₁ q) * (2 * cHm (leviBil (T b₁)) i q) := by
    intro q
    have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
    rw [map_mul, Complex.conj_ofReal]
    linear_combination (conj (b₁ q) * cHm (leviBil (T b₁)) i q) * h2
  rw [hsumY, Finset.mul_sum]
  simp only [hsq, ← hZ]
  simp only [sub_apply, cz_sub]
  rw [hsplit]
  ring

end Identities

end SGPT.Envelopes.TosC11d
