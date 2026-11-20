import SGPT.Trace.TwistedL2MForms

/-!
# The twisted a priori estimate on open sets of `ℂⁿ`

Blueprint `claude-tl2-main.tex` (`claude-tl2-main:global-bkn`, `claude-tl2-main:twisted-bkn`,
`claude-tl2-main:apriori`).  For a twisted datum `T` on `X = ℂⁿ` and a finite family of local test
pieces `h_i ⊗ e_i` (each compactly supported in the base set of its own frame `e_i` and in `U`),
with global field `W = ∑_i h_i ⊗ e_i`:

* `sum_mkh`: the globalized Bochner--Kodaira--Nakano identity for the twisted weight
  `φ - log a`, `∫ |ϑ' W|² a e^{-φ} = ∫ Levi(p')(W) a e^{-φ} + ∫ tr(A_W Ā_W) a e^{-φ}`, obtained by
  applying the flat identity to each piece in its own frame and regrouping (`sum_gauge`);
* `curv_le`: the pointwise twisted inequality
  `H(W) ≤ a Levi(p - log a)(W) + (a+b)|ϑW|² - a|ϑ'W|²` (logarithmic twist and Young);
* `apriori`: **the twisted a priori estimate**
  `|⟨τ, ∂̄G⟩|² ≤ (∫_U D e^{-φ} dμ) · (‖T* τ‖² + Q(τ))`, with
  `Q(τ) = -Re ∫ tr(A_W Ā_W) a e^{-φ}`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle
open scoped Topology ContDiff ComplexConjugate Manifold ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ}

/-! ### A Cauchy--Schwarz inequality -/

theorem sq_le_mul_of_forall_pos {X A B : ℝ} (hX : 0 ≤ X) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 < t → 2 * X ≤ t * A + B / t) : X ^ 2 ≤ A * B := by
  by_contra hc
  rw [not_le] at hc
  have hXpos : 0 < X := by
    rcases hX.lt_or_eq with h' | h'
    · exact h'
    · rw [← h'] at hc; nlinarith [mul_nonneg hA hB]
  rcases hA.lt_or_eq with hA' | hA'
  · have h1 := h (X / A) (div_pos hXpos hA')
    have h2 : X / A * A = X := by field_simp
    rw [h2] at h1
    have h3 : B / (X / A) = A * B / X := by field_simp
    rw [h3] at h1
    have h4 : X ≤ A * B / X := by linarith
    rw [le_div_iff₀ hXpos] at h4
    nlinarith
  · have h1 := h ((B + 1) / X) (div_pos (by linarith) hXpos)
    rw [← hA', mul_zero, zero_add] at h1
    have h3 : B / ((B + 1) / X) = B * X / (B + 1) := by field_simp
    rw [h3, le_div_iff₀ (by linarith)] at h1
    nlinarith

theorem sq_integral_le_of_sq_le_mul {f g k : ComplexModel n → ℝ} (hf : Integrable f)
    (hg : Integrable g) (hk : Integrable k) (hf0 : ∀ z, 0 ≤ f z) (hg0 : ∀ z, 0 ≤ g z)
    (hk0 : ∀ z, 0 ≤ k z) (hkfg : ∀ z, k z ^ 2 ≤ f z * g z) :
    (∫ z, k z) ^ 2 ≤ (∫ z, f z) * ∫ z, g z := by
  refine sq_le_mul_of_forall_pos (integral_nonneg hk0) (integral_nonneg hf0)
    (integral_nonneg hg0) fun t ht => ?_
  have hpt : ∀ z, 2 * k z ≤ t * f z + g z / t := by
    intro z
    have hM : 0 ≤ g z / t := div_nonneg (hg0 z) ht.le
    have hL : 0 ≤ t * f z := mul_nonneg ht.le (hf0 z)
    have hLM : t * f z * (g z / t) = f z * g z := by field_simp
    have h4 : 4 * k z ^ 2 ≤ (t * f z + g z / t) ^ 2 := by
      nlinarith [sq_nonneg (t * f z - g z / t), hkfg z]
    nlinarith [hk0 z, sq_nonneg (t * f z + g z / t - 2 * k z)]
  have hint : Integrable (fun z => t * f z + g z / t) := (hf.const_mul t).add (hg.div_const t)
  calc 2 * ∫ z, k z = ∫ z, 2 * k z := (integral_const_mul 2 _).symm
    _ ≤ ∫ z, (t * f z + g z / t) := integral_mono (hk.const_mul 2) hint hpt
    _ = t * (∫ z, f z) + (∫ z, g z) / t := by
      rw [integral_add (hf.const_mul t) (hg.div_const t), integral_const_mul, integral_div]

namespace TwistedDatum

variable {T : TwistedDatum n (ComplexModel n)} {ρ : ComplexModel n → ℝ}
  (hρ : IsChartDensity T.μ chart0 ρ)

/-! ### Diagonal values -/

section Diagonal

include hρ

omit hρ in
theorem frameAt_mem_dom {z : ComplexModel n} (hz : z ∈ T.U) :
    z ∈ T.dom (atlasFrameAt T.L z) :=
  (T.mem_dom).mpr ⟨mem_atlasFrameAt_baseSet T.L z, hz⟩

omit hρ in
theorem exp_neg_pT {e : AtlasFrame T.L} {z : ComplexModel n} (hz : z ∈ T.dom e) :
    Real.exp (-T.pT ρ e z) = T.a z * Real.exp (-T.pW ρ e z) := by
  have ha := T.a_pos ((T.mem_dom).mp hz).2
  simp only [pT]
  rw [show -(T.pW ρ e z - Real.log (T.a z)) = Real.log (T.a z) + -T.pW ρ e z by ring,
    Real.exp_add, Real.exp_log ha]

omit hρ in
theorem Fθ_diag_re (e : AtlasFrame T.L) (u : ComplexModel n → ComplexModel n)
    (z : ComplexModel n) :
    (T.Fθ ρ e u u z).re = ‖chartTheta (T.pT ρ e) u z‖ ^ 2 * Real.exp (-T.pT ρ e z) := by
  simp only [Fθ, cweight, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

omit hρ in
theorem FA_diag_re (e : AtlasFrame T.L) (u : ComplexModel n → ComplexModel n)
    (z : ComplexModel n) :
    (T.FA ρ e u u z).re =
      (T.a z + T.b z) * ‖chartTheta (T.pW ρ e) u z‖ ^ 2 * Real.exp (-T.pW ρ e z) := by
  simp only [FA, cweight, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

theorem FL_diag_re {e : AtlasFrame T.L} (u : ComplexModel n → ComplexModel n)
    {z : ComplexModel n} (hz : z ∈ T.dom e) :
    (T.FL ρ e u u z).re = leviForm (T.pT ρ e) z (u z) * Real.exp (-T.pT ρ e z) := by
  simp only [FL, cweight, leviS_self ((pT_contDiffAt hρ hz).of_le two_le_infty)]
  norm_cast

theorem Hs_diag {e : AtlasFrame T.L} {z : ComplexModel n} (hz : z ∈ T.dom e)
    (v : ComplexModel n) :
    T.Hs ρ e z v v = (twistedCurvature T.a T.b (T.pW ρ e) z v : ℂ) := by
  have hzU := ((T.mem_dom).mp hz).2
  have ha : ContDiffAt ℝ ∞ T.a z :=
    (T.contDiffOn_U T.a_smooth).contDiffAt (T.isOpen_U.mem_nhds hzU)
  have hdA : T.dA z v * conj (T.dA z v) = ((holDerivSq T.a z v : ℝ) : ℂ) := by
    have h := FunctionalTwistedAdjointYoungDraft.normSq_chartTwistDerivative T.a
      (fun _ => v) (ha.differentiableAt (by simp))
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← h]
    rfl
  simp only [Hs, leviS_self ((pW_contDiffAt hρ hz).of_le two_le_infty),
    leviS_self (ha.of_le two_le_infty), hdA, twistedCurvature]
  push_cast
  ring

theorem FH_diag_re {e : AtlasFrame T.L} (u : ComplexModel n → ComplexModel n)
    {z : ComplexModel n} (hz : z ∈ T.dom e) :
    (T.FH ρ e u u z).re = twistedCurvature T.a T.b (T.pW ρ e) z (u z) *
      Real.exp (-T.pW ρ e z) := by
  simp only [FH, Hs_diag hρ hz, cweight]
  norm_cast

theorem twistedCurvature_nonneg {e : AtlasFrame T.L} {z : ComplexModel n} (hz : z ∈ T.dom e)
    (v : ComplexModel n) : 0 ≤ twistedCurvature T.a T.b (T.pW ρ e) z v := by
  by_cases hv : v = 0
  · subst hv
    simp [twistedCurvature, holDerivSq]
  · exact (T.curvature_pos chart0 e ρ hρ z hz.1 hz.2 v hv).le

end Diagonal

/-! ### The globalized identity and the pointwise inequality -/

section Family

variable {ι : Type} {s : Finset ι} {e : ι → AtlasFrame T.L}
  {h : ι → ComplexModel n → ComplexModel n}
  (hh : ∀ i, IsLocalTestField T.L T.U chart0 (e i) (h i))

/-- The sum over the pieces of a frame-indexed form. -/
def Φ (F : AtlasFrame T.L → (ComplexModel n → ComplexModel n) →
    (ComplexModel n → ComplexModel n) → ComplexModel n → ℂ)
    (s : Finset ι) (e : ι → AtlasFrame T.L) (h : ι → ComplexModel n → ComplexModel n)
    (z : ComplexModel n) : ℂ :=
  ∑ i ∈ s, F (e i) (T.tot s e h (e i)) (h i) z

include hρ hh

/-- **The globalized twisted Bochner--Kodaira--Nakano identity.** -/
theorem sum_mkh :
    ∫ z, T.Φ (T.Fθ ρ) s e h z = (∫ z, T.Φ (T.FT ρ) s e h z) + ∫ z, T.Φ (T.FL ρ) s e h z := by
  unfold Φ
  rw [integral_finsetSum _ fun i _ => T.integrable_piece hh (isGaugeForm_theta hρ) i,
    integral_finsetSum _ fun i _ => T.integrable_piece hh (isGaugeForm_tr hρ) i,
    integral_finsetSum _ fun i _ => T.integrable_piece hh (isGaugeForm_levi hρ) i,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact integral_chartTheta_mul_conj_local (T.isOpen_dom (e i)) (T.contDiffOn_pT hρ (e i))
    ((T.contDiffOn_tot hh (e i)).mono fun z hz => ((T.mem_dom).mp hz).1) (hh i).1 (hh i).2.1
    (T.tsupport_subset_dom hh i)

omit hρ in
theorem Φ_eq_diag {F : AtlasFrame T.L → (ComplexModel n → ComplexModel n) →
      (ComplexModel n → ComplexModel n) → ComplexModel n → ℂ} (hF : T.IsGaugeForm F)
    {z : ComplexModel n} (hz : z ∈ T.U) :
    T.Φ F s e h z = F (atlasFrameAt T.L z) (T.tot s e h (atlasFrameAt T.L z))
      (T.tot s e h (atlasFrameAt T.L z)) z :=
  T.sum_gauge hh hF (frameAt_mem_dom hz)

omit hρ in
theorem Φ_eq_zero {F : AtlasFrame T.L → (ComplexModel n → ComplexModel n) →
      (ComplexModel n → ComplexModel n) → ComplexModel n → ℂ} (hF : T.IsGaugeForm F)
    {z : ComplexModel n} (hz : z ∉ T.U) : T.Φ F s e h z = 0 :=
  T.sum_pieces_eq_zero_of_notMem_U hh hF hz

/-- **The pointwise twisted inequality** (logarithmic twist and Young). -/
theorem curv_le (z : ComplexModel n) :
    (T.Φ (T.FH ρ) s e h z).re ≤ (T.Φ (T.FL ρ) s e h z).re + (T.Φ (T.FA ρ) s e h z).re -
      (T.Φ (T.Fθ ρ) s e h z).re := by
  by_cases hz : z ∈ T.U
  · set e₀ := atlasFrameAt T.L z
    have hz₀ : z ∈ T.dom e₀ := frameAt_mem_dom hz
    rw [Φ_eq_diag hh (isGaugeForm_curv hρ) hz, Φ_eq_diag hh (isGaugeForm_levi hρ) hz,
      Φ_eq_diag hh (isGaugeForm_tstar hρ) hz, Φ_eq_diag hh (isGaugeForm_theta hρ) hz,
      FH_diag_re hρ _ hz₀, FL_diag_re hρ _ hz₀, FA_diag_re, Fθ_diag_re,
      exp_neg_pT hz₀]
    have hY := FunctionalTwistedDatumLocalYoungDraft.TwistedDatum.datum_twistedCurvature_le_shiftedLevi_and_adjoint
      T chart0 e₀ hρ (T.tot s e h e₀) hz₀
    have hE := Real.exp_pos (-T.pW ρ e₀ z)
    have hY' : twistedCurvature T.a T.b (T.pW ρ e₀) z (T.tot s e h e₀ z) ≤
        T.a z * leviForm (T.pT ρ e₀) z (T.tot s e h e₀ z) +
          (T.a z + T.b z) * ‖chartTheta (T.pW ρ e₀) (T.tot s e h e₀) z‖ ^ 2 -
          T.a z * ‖chartTheta (T.pT ρ e₀) (T.tot s e h e₀) z‖ ^ 2 := hY
    nlinarith
  · simp [Φ_eq_zero hh (isGaugeForm_curv hρ) hz, Φ_eq_zero hh (isGaugeForm_levi hρ) hz,
      Φ_eq_zero hh (isGaugeForm_tstar hρ) hz, Φ_eq_zero hh (isGaugeForm_theta hρ) hz]

theorem curv_nonneg (z : ComplexModel n) : 0 ≤ (T.Φ (T.FH ρ) s e h z).re := by
  by_cases hz : z ∈ T.U
  · have hz₀ := frameAt_mem_dom hz
    rw [Φ_eq_diag hh (isGaugeForm_curv hρ) hz, FH_diag_re hρ _ hz₀]
    exact mul_nonneg (twistedCurvature_nonneg hρ hz₀ _) (Real.exp_pos _).le
  · simp [Φ_eq_zero hh (isGaugeForm_curv hρ) hz]

/-- **The integrated twisted inequality**: `∫ H(W) e^{-p} ≤ ‖T* τ‖² + Q(τ)`. -/
theorem integral_curv_le :
    ∫ z, (T.Φ (T.FH ρ) s e h z).re ≤
      (∫ z, (T.Φ (T.FA ρ) s e h z).re) - (∫ z, T.Φ (T.FT ρ) s e h z).re := by
  have iH : Integrable (fun z => (T.Φ (T.FH ρ) s e h z).re) :=
    (T.integrable_sum_pieces (s := s) hh (isGaugeForm_curv hρ)).re
  have iL : Integrable (fun z => (T.Φ (T.FL ρ) s e h z).re) :=
    (T.integrable_sum_pieces (s := s) hh (isGaugeForm_levi hρ)).re
  have iA : Integrable (fun z => (T.Φ (T.FA ρ) s e h z).re) :=
    (T.integrable_sum_pieces (s := s) hh (isGaugeForm_tstar hρ)).re
  have iθ : Integrable (fun z => (T.Φ (T.Fθ ρ) s e h z).re) :=
    (T.integrable_sum_pieces (s := s) hh (isGaugeForm_theta hρ)).re
  have iθ' : Integrable (fun z => T.Φ (T.Fθ ρ) s e h z) :=
    T.integrable_sum_pieces (s := s) hh (isGaugeForm_theta hρ)
  have iL' : Integrable (fun z => T.Φ (T.FL ρ) s e h z) :=
    T.integrable_sum_pieces (s := s) hh (isGaugeForm_levi hρ)
  have hmono : ∫ z, (T.Φ (T.FH ρ) s e h z).re ≤ ∫ z, ((T.Φ (T.FL ρ) s e h z).re +
      (T.Φ (T.FA ρ) s e h z).re - (T.Φ (T.Fθ ρ) s e h z).re) :=
    integral_mono iH ((iL.add iA).sub iθ) (curv_le hρ hh)
  rw [integral_sub (f := fun z => (T.Φ (T.FL ρ) s e h z).re + (T.Φ (T.FA ρ) s e h z).re)
    (iL.add iA) iθ, integral_add iL iA] at hmono
  have hmkh := congrArg Complex.re (sum_mkh hρ hh (s := s))
  rw [Complex.add_re] at hmkh
  have e1 : (∫ z, T.Φ (T.Fθ ρ) s e h z).re = ∫ z, (T.Φ (T.Fθ ρ) s e h z).re :=
    (integral_re iθ').symm
  have e2 : (∫ z, T.Φ (T.FL ρ) s e h z).re = ∫ z, (T.Φ (T.FL ρ) s e h z).re :=
    (integral_re iL').symm
  linarith

/-! ### The data pairing -/

theorem data_sq_le (z : ComplexModel n) :
    ‖T.Φ (T.FD ρ) s e h z‖ ^ 2 ≤
      (T.U.indicator (fun x => T.D x * Real.exp (-T.φ x)) z * ρ z) * (T.Φ (T.FH ρ) s e h z).re := by
  by_cases hz : z ∈ T.U
  · set e₀ := atlasFrameAt T.L z
    have hz₀ : z ∈ T.dom e₀ := frameAt_mem_dom hz
    rw [Φ_eq_diag hh (isGaugeForm_data hρ) hz, Φ_eq_diag hh (isGaugeForm_curv hρ) hz,
      FH_diag_re hρ _ hz₀, indicator_of_mem hz]
    simp only [FD, cweight]
    have hB := T.D_bound chart0 e₀ ρ hρ z hz₀.1 hz (T.tot s e h e₀ z)
    have hexp := T.exp_neg_localWeight e₀ hρ hz₀.1
    simp only [chart0_symm_apply] at hB hexp
    change ‖dbarPairing (chartCoeff T.L chart0 e₀ T.G) z (T.tot s e h e₀ z) *
        ((Real.exp (-T.pW ρ e₀ z) : ℝ) : ℂ)‖ ^ 2 ≤ _
    have hexp' : Real.exp (-T.pW ρ e₀ z) =
        frameNormSq T.L e₀ z * Real.exp (-T.φ z) * ρ z := hexp
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow, hexp']
    have hB' : ‖dbarPairing (chartCoeff T.L chart0 e₀ T.G) z (T.tot s e h e₀ z)‖ ^ 2 *
        frameNormSq T.L e₀ z ≤
        T.D z * twistedCurvature T.a T.b (T.pW ρ e₀) z (T.tot s e h e₀ z) := hB
    have hN := frameNormSq_pos e₀ hz₀.1.2
    have hφ := Real.exp_pos (-T.φ z)
    have hρz := pos_of_isChartDensity hρ z
    have hK : 0 ≤ frameNormSq T.L e₀ z * Real.exp (-T.φ z) ^ 2 * ρ z ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right hB' hK
    nlinarith [this]
  · simp [Φ_eq_zero hh (isGaugeForm_data hρ) hz, Φ_eq_zero hh (isGaugeForm_curv hρ) hz]

end Family

end TwistedDatum

end SGPT.Trace.TwistedL2
