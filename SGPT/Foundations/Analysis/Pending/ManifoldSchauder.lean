import SGPT.Foundations.Analysis.Pending.ManifoldHolderSpace
import SGPT.Foundations.Analysis.Pending.WholeSpaceSolvability

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Global Schauder estimates on a compact complex manifold

Let `A` be a Hölder atlas of a complex manifold `M` (`HolderAtlas`: charts `e_i` with a
chart-smooth partition of unity `χ_i`), `b` an orthonormal basis of the real inner product space
`ComplexModel n`, `0 < r < 1`.  A second-order operator `L` on `M` is given chartwise: in the chart
`e_i` it reads `L_i v = a_i : D²v + Dv(β_i) + c_i v` (`SchauderWholeSpace.ellipticOp`) on the compact
set `e_i(tsupport χ_i)`, with coefficients defined on the whole model space and lying in the Schauder
class (`a_i` symmetric, `λ`-elliptic, bounded and `r`-Hölder; `β_i`, `c_i` bounded and `r`-Hölder).

`exists_norm_le` (**the global Schauder estimate**, Székelyhidi §2.3, end; the case `k = 0` of
blueprint `bou:schauder-global`): there is `C`, depending only on `(A, b, λ, Λ, r)`, such that every
`u ∈ C^{2,r}(M)` with `|u| ≤ S` and `L u = g ∈ C^{0,r}(M)` satisfies
`‖u‖_{C^{2,r}(M)} ≤ C (‖g‖_{C^{0,r}(M)} + S)`.

Proof.  The local piece `f_i = (χ_i u) ∘ e_i⁻¹` equals `χ̃_i v_i` with `χ̃_i = χ_i ∘ e_i⁻¹` and
`v_i = σ_i · (u ∘ e_i⁻¹)` (`σ_i` a cut-off equal to `1` near `e_i(tsupport χ_i)`; `v_i ∈ C^{2,r}_b` with
`‖v_i‖ ≤ C ‖u‖`, `HolderAtlas.HolderMap.exists_smul_comp_symm`).  By the product rule
(`ellipticOp_mul`) `L_i f_i = χ̃_i (g ∘ e_i⁻¹) + R_i` where `R_i` only involves `v_i`, `Dv_i` and fixed
derivatives of `χ̃_i`, so `[R_i]_r ≤ K (sup|v_i| + sup|D²v_i|)` (`abs_remainder_sub_le`).  The whole-space
Schauder estimate (`SchauderWholeSpace.exists_schauder_estimate`) bounds `‖f_i‖_{C^{2,r}_b}` by
`[L_i f_i]_r + sup|f_i|`, the interpolation inequality
(`HolderInterpolation.norm_fderiv_fderiv_le_interpolation`) bounds `sup|D²v_i|` by
`32 sup|v_i| / ρ² + 2 ρ^r ‖v_i‖`, and summing over the atlas with `ρ` small absorbs `‖u‖`.

TN.4 B5 linear track L3.
-/

noncomputable section

open Set Filter Topology Metric Function
open scoped NNReal ContDiff RealInnerProductSpace Manifold

namespace SGPT.Foundations.Analysis.Pending.ManifoldSchauder

open EllipticMeanValue SchauderBlowup SchauderWholeSpace HolderInterpolation

/-! ### The product rule for `L` -/

section ProductRule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)

/-- The cross term `a : (Dχ ⊗ Dv + Dv ⊗ Dχ)` of the product rule for `a : D²`. -/
def crossTerm (A : E →L[ℝ] E) (p q : E →L[ℝ] ℝ) : ℝ :=
  ∑ i, (p (b i) * q (A (b i)) + q (b i) * p (A (b i)))

/-- The product rule for the second derivative, evaluated. -/
theorem fderiv_fderiv_mul_apply {χ v : E → ℝ} {x : E} (hχ : ContDiff ℝ 2 χ)
    (hv : ContDiff ℝ 2 v) (p q : E) :
    fderiv ℝ (fderiv ℝ (fun y => χ y * v y)) x p q =
      χ x * fderiv ℝ (fderiv ℝ v) x p q + fderiv ℝ χ x p * fderiv ℝ v x q +
        fderiv ℝ v x p * fderiv ℝ χ x q + v x * fderiv ℝ (fderiv ℝ χ) x p q := by
  have hχ1 : Differentiable ℝ χ := hχ.differentiable (by norm_num)
  have hv1 : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hDχ : Differentiable ℝ (fderiv ℝ χ) :=
    (hχ.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hDv : Differentiable ℝ (fderiv ℝ v) :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have h1 : fderiv ℝ (fun y => χ y * v y) = fun y => χ y • fderiv ℝ v y + v y • fderiv ℝ χ y :=
    funext fun y => fderiv_mul (hχ1 y) (hv1 y)
  have hsm : HasFDerivAt (fun y => χ y • fderiv ℝ v y + v y • fderiv ℝ χ y) _ x :=
    ((hχ1 x).hasFDerivAt.smul (hDv x).hasFDerivAt).add ((hv1 x).hasFDerivAt.smul (hDχ x).hasFDerivAt)
  rw [h1, hsm.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

/-- **The product rule for `L`**: `L(χ v) = χ L v + v (a : D²χ + Dχ(β)) + a : (Dχ ⊗ Dv + Dv ⊗ Dχ)`. -/
theorem ellipticOp_mul (a : E → E →L[ℝ] E) (β : E → E) (c : E → ℝ) {χ v : E → ℝ}
    (hχ : ContDiff ℝ 2 χ) (hv : ContDiff ℝ 2 v) (x : E) :
    ellipticOp b a β c (fun y => χ y * v y) x =
      χ x * ellipticOp b a β c v x +
        v x * (hessTrace b (a x) (fderiv ℝ (fderiv ℝ χ) x) + fderiv ℝ χ x (β x)) +
          crossTerm b (a x) (fderiv ℝ χ x) (fderiv ℝ v x) := by
  have h1 : fderiv ℝ (fun y => χ y * v y) x (β x) =
      χ x * fderiv ℝ v x (β x) + v x * fderiv ℝ χ x (β x) := by
    rw [show (fun y => χ y * v y) = χ * v from rfl,
      fderiv_mul (hχ.differentiable (by norm_num) x) (hv.differentiable (by norm_num) x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
  simp only [ellipticOp, hessTrace, crossTerm, fderiv_fderiv_mul_apply hχ hv, h1,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end ProductRule

/-! ### Hölder bounds for the remainder of the product rule -/

section Remainder

/-- `|f₁ g₁ - f₂ g₂| ≤ |f₁ - f₂| G₀ + F₀ |g₁ - g₂|`, with bounds. -/
theorem abs_mul_sub_mul_le {f₁ f₂ g₁ g₂ Df G₀ F₀ Dg : ℝ} (h1 : |f₁ - f₂| ≤ Df) (h2 : |g₁| ≤ G₀)
    (h3 : |f₂| ≤ F₀) (h4 : |g₁ - g₂| ≤ Dg) : |f₁ * g₁ - f₂ * g₂| ≤ Df * G₀ + F₀ * Dg := by
  rw [show f₁ * g₁ - f₂ * g₂ = (f₁ - f₂) * g₁ + f₂ * (g₁ - g₂) by ring]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
  · exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
  · exact mul_le_mul h3 h4 (abs_nonneg _) ((abs_nonneg _).trans h3)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)

/-- `|φ w - φ' w'| ≤ ‖φ - φ'‖ ‖w‖ + ‖φ'‖ ‖w - w'‖`. -/
theorem abs_apply_sub_apply_le (φ φ' : E →L[ℝ] ℝ) (w w' : E) :
    |φ w - φ' w'| ≤ ‖φ - φ'‖ * ‖w‖ + ‖φ'‖ * ‖w - w'‖ := by
  rw [show φ w - φ' w' = (φ - φ') w + φ' (w - w') by simp only [sub_apply, map_sub]; ring]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [← Real.norm_eq_abs] <;>
    exact ContinuousLinearMap.le_opNorm _ _

/-- `|a : Q - a' : Q'| ≤ d (‖a - a'‖ ‖Q‖ + ‖a'‖ ‖Q - Q'‖)`. -/
theorem abs_hessTrace_sub_le (A A' : E →L[ℝ] E) (Q Q' : E →L[ℝ] E →L[ℝ] ℝ) :
    |hessTrace b A Q - hessTrace b A' Q'| ≤
      Fintype.card ι * (‖A - A'‖ * ‖Q‖ + ‖A'‖ * ‖Q - Q'‖) := by
  rw [show hessTrace b A Q - hessTrace b A' Q' = hessTrace b (A - A') Q + hessTrace b A' (Q - Q') by
    rw [hessTrace_sub_left, hessTrace_sub_right]; ring]
  refine (abs_add_le _ _).trans ?_
  have h1 := abs_hessTrace_le b (A - A') Q
  have h2 := abs_hessTrace_le b A' (Q - Q')
  nlinarith

/-- One term of the cross term. -/
theorem abs_cross_sub_le (A A' : E →L[ℝ] E) (p p' q q' : E →L[ℝ] ℝ) (w : E) (hw : ‖w‖ = 1)
    {a₀ p₀ q₀ : ℝ} (hA : ‖A‖ ≤ a₀) (hp' : ‖p'‖ ≤ p₀) (hq : ‖q‖ ≤ q₀) (hq' : ‖q'‖ ≤ q₀) :
    |p w * q (A w) - p' w * q' (A' w)| ≤
      ‖p - p'‖ * (q₀ * a₀) + p₀ * (‖q - q'‖ * a₀ + q₀ * ‖A - A'‖) := by
  have ha₀ : 0 ≤ a₀ := (norm_nonneg _).trans hA
  have hq₀ : 0 ≤ q₀ := (norm_nonneg _).trans hq
  refine abs_mul_sub_mul_le ?_ ?_ ?_ ?_
  · rw [← sub_apply, ← Real.norm_eq_abs]
    exact ((p - p').le_opNorm w).trans (by rw [hw, mul_one])
  · rw [← Real.norm_eq_abs]
    refine (q.le_opNorm _).trans (mul_le_mul hq ((A.le_opNorm w).trans ?_) (norm_nonneg _) hq₀)
    rw [hw, mul_one]; exact hA
  · rw [← Real.norm_eq_abs]
    exact (p'.le_opNorm w).trans (by rw [hw, mul_one]; exact hp')
  · refine (abs_apply_sub_apply_le q q' (A w) (A' w)).trans (add_le_add ?_ ?_)
    · refine mul_le_mul_of_nonneg_left ((A.le_opNorm w).trans ?_) (norm_nonneg _)
      rw [hw, mul_one]; exact hA
    · rw [← sub_apply]
      refine mul_le_mul hq' (((A - A').le_opNorm w).trans (by rw [hw, mul_one])) (norm_nonneg _)
        hq₀

theorem abs_crossTerm_le (A : E →L[ℝ] E) (p q : E →L[ℝ] ℝ) :
    |crossTerm b A p q| ≤ 2 * Fintype.card ι * (‖A‖ * ‖p‖ * ‖q‖) := by
  rw [crossTerm]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h : ∀ i, |p (b i) * q (A (b i)) + q (b i) * p (A (b i))| ≤ 2 * (‖A‖ * ‖p‖ * ‖q‖) := by
    intro i
    have hb : ‖b i‖ = 1 := b.orthonormal.1 i
    have e1 : |p (b i)| ≤ ‖p‖ := by
      rw [← Real.norm_eq_abs]; exact (p.le_opNorm _).trans (by rw [hb, mul_one])
    have e2 : |q (b i)| ≤ ‖q‖ := by
      rw [← Real.norm_eq_abs]; exact (q.le_opNorm _).trans (by rw [hb, mul_one])
    have e3 : |q (A (b i))| ≤ ‖q‖ * ‖A‖ := by
      rw [← Real.norm_eq_abs]
      exact (q.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        ((A.le_opNorm _).trans (by rw [hb, mul_one])) (norm_nonneg _))
    have e4 : |p (A (b i))| ≤ ‖p‖ * ‖A‖ := by
      rw [← Real.norm_eq_abs]
      exact (p.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        ((A.le_opNorm _).trans (by rw [hb, mul_one])) (norm_nonneg _))
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have := mul_le_mul e1 e3 (abs_nonneg _) (norm_nonneg _)
    have := mul_le_mul e2 e4 (abs_nonneg _) (norm_nonneg _)
    nlinarith
  refine (Finset.sum_le_sum fun i _ => h i).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  nlinarith [norm_nonneg A, norm_nonneg p, norm_nonneg q,
    mul_nonneg (mul_nonneg (norm_nonneg A) (norm_nonneg p)) (norm_nonneg q)]

theorem abs_crossTerm_sub_le (A A' : E →L[ℝ] E) (p p' q q' : E →L[ℝ] ℝ) {a₀ p₀ q₀ : ℝ}
    (hA : ‖A‖ ≤ a₀) (hp : ‖p‖ ≤ p₀) (hp' : ‖p'‖ ≤ p₀) (hq : ‖q‖ ≤ q₀) (hq' : ‖q'‖ ≤ q₀) :
    |crossTerm b A p q - crossTerm b A' p' q'| ≤
      2 * Fintype.card ι * (‖p - p'‖ * q₀ * a₀ + p₀ * ‖q - q'‖ * a₀ + p₀ * q₀ * ‖A - A'‖) := by
  have ha₀ : 0 ≤ a₀ := (norm_nonneg _).trans hA
  have hp₀ : 0 ≤ p₀ := (norm_nonneg _).trans hp
  have hq₀ : 0 ≤ q₀ := (norm_nonneg _).trans hq
  rw [crossTerm, crossTerm, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h : ∀ i, |(p (b i) * q (A (b i)) + q (b i) * p (A (b i))) -
      (p' (b i) * q' (A' (b i)) + q' (b i) * p' (A' (b i)))| ≤
      2 * (‖p - p'‖ * q₀ * a₀ + p₀ * ‖q - q'‖ * a₀ + p₀ * q₀ * ‖A - A'‖) := by
    intro i
    have hb : ‖b i‖ = 1 := b.orthonormal.1 i
    have e1 := abs_cross_sub_le A A' p p' q q' (b i) hb hA hp' hq hq'
    have e2 := abs_cross_sub_le A A' q q' p p' (b i) hb hA hq' hp hp'
    rw [show p (b i) * q (A (b i)) + q (b i) * p (A (b i)) -
        (p' (b i) * q' (A' (b i)) + q' (b i) * p' (A' (b i))) =
        (p (b i) * q (A (b i)) - p' (b i) * q' (A' (b i))) +
          (q (b i) * p (A (b i)) - q' (b i) * p' (A' (b i))) by ring]
    refine (abs_add_le _ _).trans ?_
    have hn1 := norm_nonneg (p - p')
    have hn2 := norm_nonneg (q - q')
    have hn3 := norm_nonneg (A - A')
    nlinarith [mul_nonneg hn1 (mul_nonneg hq₀ ha₀), mul_nonneg hp₀ (mul_nonneg hn2 ha₀),
      mul_nonneg hp₀ (mul_nonneg hq₀ hn3), mul_nonneg hn2 (mul_nonneg hp₀ ha₀),
      mul_nonneg hq₀ (mul_nonneg hn1 ha₀), mul_nonneg hq₀ (mul_nonneg hp₀ hn3)]
  refine (Finset.sum_le_sum fun i _ => h i).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring_nf
  exact le_rfl

end Remainder

/-! ### The remainder of the product rule is Hölder -/

section RemainderEstimate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)

/-- The remainder `R = v (a : D²χ + Dχ(β)) + a : (Dχ ⊗ Dv + Dv ⊗ Dχ)` of the product rule
`L(χ v) = χ L v + R`. -/
def remainder (a : E → E →L[ℝ] E) (β : E → E) (χ v : E → ℝ) (x : E) : ℝ :=
  v x * (hessTrace b (a x) (fderiv ℝ (fderiv ℝ χ) x) + fderiv ℝ χ x (β x)) +
    crossTerm b (a x) (fderiv ℝ χ x) (fderiv ℝ v x)

theorem ellipticOp_mul_eq (a : E → E →L[ℝ] E) (β : E → E) (c : E → ℝ) {χ v : E → ℝ}
    (hχ : ContDiff ℝ 2 χ) (hv : ContDiff ℝ 2 v) (x : E) :
    ellipticOp b a β c (fun y => χ y * v y) x =
      χ x * ellipticOp b a β c v x + remainder b a β χ v x := by
  rw [ellipticOp_mul b a β c hχ hv x, remainder, add_assoc]

/-- The constant of `abs_remainder_sub_le`. -/
def remainderConst (d Λ K₁ K₂ K₃ : ℝ) : ℝ :=
  4 * (d * Λ * K₂ + K₁ * Λ) + (d * (Λ * K₂ + Λ * (K₃ + 2 * K₂)) + ((K₂ + 2 * K₁) * Λ + K₁ * Λ)) +
    2 * d * (2 * (K₂ + 2 * K₁) + 6 * K₁) * Λ

/-- **The remainder is Hölder**: `[R]_r ≤ K (sup|v| + sup|D²v|)`, with `K` depending only on the
dimension, the bounds `Λ` of `a, β` and bounds `K₁, K₂, K₃` for `Dχ, D²χ, D³χ`. -/
theorem abs_remainder_sub_le {r Λ K₁ K₂ K₃ S B : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hK₃ : 0 ≤ K₃)
    (a : E → E →L[ℝ] E) (β : E → E) {χ v : E → ℝ}
    (hab : ∀ x, ‖a x‖ ≤ Λ) (hah : ∀ x y, ‖a x - a y‖ ≤ Λ * ‖x - y‖ ^ r)
    (hβb : ∀ x, ‖β x‖ ≤ Λ) (hβh : ∀ x y, ‖β x - β y‖ ≤ Λ * ‖x - y‖ ^ r)
    (h1 : ∀ x, ‖fderiv ℝ χ x‖ ≤ K₁) (h2 : ∀ x, ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ K₂)
    (h1L : ∀ x y, ‖fderiv ℝ χ x - fderiv ℝ χ y‖ ≤ K₂ * ‖x - y‖)
    (h2L : ∀ x y, ‖fderiv ℝ (fderiv ℝ χ) x - fderiv ℝ (fderiv ℝ χ) y‖ ≤ K₃ * ‖x - y‖)
    (hv : ContDiff ℝ 2 v) (hS : ∀ x, |v x| ≤ S) (hB : ∀ x, ‖fderiv ℝ (fderiv ℝ v) x‖ ≤ B)
    (x y : E) :
    |remainder b a β χ v x - remainder b a β χ v y| ≤
      remainderConst (Fintype.card ι) Λ K₁ K₂ K₃ * (S + B) * ‖x - y‖ ^ r := by
  set d : ℝ := (Fintype.card ι : ℝ) with hd
  set p := ‖x - y‖ ^ r with hp
  have hp0 : 0 ≤ p := Real.rpow_nonneg (norm_nonneg _) _
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans (hab 0)
  have hK₁ : 0 ≤ K₁ := (norm_nonneg _).trans (h1 0)
  have hK₂ : 0 ≤ K₂ := (ContinuousLinearMap.opNorm_nonneg _).trans (h2 0)
  have hS0 : 0 ≤ S := (abs_nonneg _).trans (hS 0)
  have hB0 : 0 ≤ B := (ContinuousLinearMap.opNorm_nonneg _).trans (hB 0)
  set H₁ := K₂ + 2 * K₁ with hH₁
  set H₂ := K₃ + 2 * K₂ with hH₂
  have hH₁0 : 0 ≤ H₁ := by positivity
  have hH₂0 : 0 ≤ H₂ := by positivity
  have hDχh : ‖fderiv ℝ χ x - fderiv ℝ χ y‖ ≤ H₁ * p :=
    norm_sub_le_rpow_of_lipschitz_of_bound (Y := E →L[ℝ] ℝ) hK₂ hr0 hr1 h1L h1 x y
  have hD2χh : ‖fderiv ℝ (fderiv ℝ χ) x - fderiv ℝ (fderiv ℝ χ) y‖ ≤ H₂ * p :=
    norm_sub_le_rpow_of_lipschitz_of_bound (Y := E →L[ℝ] E →L[ℝ] ℝ) hK₃ hr0 hr1 h2L h2 x y
  have hvh : |v x - v y| ≤ (B + 4 * S) * p := abs_sub_le_rpow hv hr0 hr1 hS hB x y
  have hDv : ∀ z, ‖fderiv ℝ v z‖ ≤ 2 * S + B := norm_fderiv_le_two_mul_add hv hS hB
  have hDvh : ‖fderiv ℝ v x - fderiv ℝ v y‖ ≤ (3 * B + 4 * S) * p :=
    norm_fderiv_sub_le_rpow hv hr0 hr1 hS hB x y
  -- the zeroth-order coefficient `P = a : D²χ + Dχ(β)`
  set P₀ := d * Λ * K₂ + K₁ * Λ with hP₀
  set P₁ := d * (Λ * K₂ + Λ * H₂) + (H₁ * Λ + K₁ * Λ) with hP₁
  have hP₀0 : 0 ≤ P₀ := by positivity
  have hP₁0 : 0 ≤ P₁ := by positivity
  have hPb : ∀ y, |hessTrace b (a y) (fderiv ℝ (fderiv ℝ χ) y) + fderiv ℝ χ y (β y)| ≤ P₀ := by
    intro y
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (abs_hessTrace_le b _ _).trans ?_
      have := mul_le_mul (hab y) (h2 y) (ContinuousLinearMap.opNorm_nonneg _) hΛ
      rw [mul_assoc, hd]; rw [mul_assoc] at *
      exact mul_le_mul_of_nonneg_left this hd0
    · rw [← Real.norm_eq_abs]
      exact ((fderiv ℝ χ y).le_opNorm _).trans (mul_le_mul (h1 y) (hβb y) (norm_nonneg _) hK₁)
  have hPh : |(hessTrace b (a x) (fderiv ℝ (fderiv ℝ χ) x) + fderiv ℝ χ x (β x)) -
      (hessTrace b (a y) (fderiv ℝ (fderiv ℝ χ) y) + fderiv ℝ χ y (β y))| ≤ P₁ * p := by
    rw [show (hessTrace b (a x) (fderiv ℝ (fderiv ℝ χ) x) + fderiv ℝ χ x (β x)) -
        (hessTrace b (a y) (fderiv ℝ (fderiv ℝ χ) y) + fderiv ℝ χ y (β y)) =
        (hessTrace b (a x) (fderiv ℝ (fderiv ℝ χ) x) - hessTrace b (a y) (fderiv ℝ (fderiv ℝ χ) y)) +
          (fderiv ℝ χ x (β x) - fderiv ℝ χ y (β y)) by ring]
    refine (abs_add_le _ _).trans ?_
    have e1 := abs_hessTrace_sub_le b (a x) (a y) (fderiv ℝ (fderiv ℝ χ) x)
      (fderiv ℝ (fderiv ℝ χ) y)
    have e2 := abs_apply_sub_apply_le (fderiv ℝ χ x) (fderiv ℝ χ y) (β x) (β y)
    have f1 : ‖a x - a y‖ * ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ Λ * p * K₂ :=
      mul_le_mul (hah x y) (h2 x) (ContinuousLinearMap.opNorm_nonneg _) (by positivity)
    have f2 : ‖a y‖ * ‖fderiv ℝ (fderiv ℝ χ) x - fderiv ℝ (fderiv ℝ χ) y‖ ≤ Λ * (H₂ * p) :=
      mul_le_mul (hab y) hD2χh (ContinuousLinearMap.opNorm_nonneg _) hΛ
    have f3 : ‖fderiv ℝ χ x - fderiv ℝ χ y‖ * ‖β x‖ ≤ H₁ * p * Λ :=
      mul_le_mul hDχh (hβb x) (norm_nonneg _) (by positivity)
    have f4 : ‖fderiv ℝ χ y‖ * ‖β x - β y‖ ≤ K₁ * (Λ * p) :=
      mul_le_mul (h1 y) (hβh x y) (norm_nonneg _) hK₁
    have g1 : d * (‖a x - a y‖ * ‖fderiv ℝ (fderiv ℝ χ) x‖ +
        ‖a y‖ * ‖fderiv ℝ (fderiv ℝ χ) x - fderiv ℝ (fderiv ℝ χ) y‖) ≤
        d * (Λ * p * K₂ + Λ * (H₂ * p)) := mul_le_mul_of_nonneg_left (add_le_add f1 f2) hd0
    have : d * (Λ * p * K₂ + Λ * (H₂ * p)) + (H₁ * p * Λ + K₁ * (Λ * p)) = P₁ * p := by
      rw [hP₁]; ring
    linarith
  -- the two parts of the remainder
  have hvP := abs_mul_sub_mul_le hvh (hPb x) (hS y) hPh
  have hc := abs_crossTerm_sub_le b (a x) (a y) (fderiv ℝ χ x) (fderiv ℝ χ y) (fderiv ℝ v x)
    (fderiv ℝ v y) (hab x) (h1 x) (h1 y) (hDv x) (hDv y)
  have c1 : ‖fderiv ℝ χ x - fderiv ℝ χ y‖ * (2 * S + B) * Λ ≤ H₁ * p * (2 * S + B) * Λ := by
    gcongr
  have c2 : K₁ * ‖fderiv ℝ v x - fderiv ℝ v y‖ * Λ ≤ K₁ * ((3 * B + 4 * S) * p) * Λ := by
    gcongr
  have c3 : K₁ * (2 * S + B) * ‖a x - a y‖ ≤ K₁ * (2 * S + B) * (Λ * p) := by
    gcongr
    exact hah x y
  have hcross : |crossTerm b (a x) (fderiv ℝ χ x) (fderiv ℝ v x) -
      crossTerm b (a y) (fderiv ℝ χ y) (fderiv ℝ v y)| ≤
      2 * d * (H₁ * p * (2 * S + B) * Λ + K₁ * ((3 * B + 4 * S) * p) * Λ +
        K₁ * (2 * S + B) * (Λ * p)) := by
    refine hc.trans ?_
    gcongr
  rw [remainder, remainder,
    show ∀ A B C D : ℝ, A + B - (C + D) = (A - C) + (B - D) from fun _ _ _ _ => by ring]
  refine (abs_add_le _ _).trans ((add_le_add hvP hcross).trans ?_)
  have key : remainderConst d Λ K₁ K₂ K₃ * (S + B) * p -
      ((B + 4 * S) * p * P₀ + S * (P₁ * p) +
        2 * d * (H₁ * p * (2 * S + B) * Λ + K₁ * ((3 * B + 4 * S) * p) * Λ +
          K₁ * (2 * S + B) * (Λ * p))) =
      p * (3 * P₀ * B + P₁ * B + 2 * d * Λ * (H₁ * B + K₁ * B + K₁ * B)) := by
    rw [remainderConst, hP₀, hP₁, hH₁, hH₂]; ring
  have : 0 ≤ p * (3 * P₀ * B + P₁ * B + 2 * d * Λ * (H₁ * B + K₁ * B + K₁ * B)) := by
    positivity
  linarith

end RemainderEstimate

/-! ### Auxiliary facts on the whole space -/

section Aux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)

/-- `L` is local: functions that agree near `x` have the same `L` at `x`. -/
theorem ellipticOp_congr (a : E → E →L[ℝ] E) (β : E → E) (c : E → ℝ) {f₁ f₂ : E → ℝ} {x : E}
    (h : f₁ =ᶠ[𝓝 x] f₂) : ellipticOp b a β c f₁ x = ellipticOp b a β c f₂ x := by
  simp only [ellipticOp, h.fderiv_eq, h.fderiv.fderiv_eq, h.eq_of_nhds]

/-- A `C¹` map with compact support is bounded and Lipschitz. -/
theorem exists_lipschitz_of_hasCompactSupport {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : E → Y} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ∃ K : ℝ, 0 ≤ K ∧ (∀ x, ‖f x‖ ≤ K) ∧ ∀ x y, ‖f x - f y‖ ≤ K * ‖x - y‖ := by
  obtain ⟨K₀, hK₀⟩ := hf.continuous.bounded_above_of_compact_support hc
  obtain ⟨K₁, hK₁⟩ := (hf.continuous_fderiv one_ne_zero).bounded_above_of_compact_support (hc.fderiv (𝕜 := ℝ))
  have hK₀0 : 0 ≤ K₀ := (norm_nonneg _).trans (hK₀ 0)
  refine ⟨max K₀ K₁, hK₀0.trans (le_max_left _ _), fun x => (hK₀ x).trans (le_max_left _ _),
    fun x y => ?_⟩
  have h := (convex_univ : Convex ℝ (univ : Set E)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hf.differentiable one_ne_zero) z) (fun z _ => (hK₁ z).trans (le_max_right K₀ K₁))
    (mem_univ y) (mem_univ x)
  exact h

/-- Bounds for a smooth function with compact support and its first three derivatives. -/
theorem exists_bounds_of_hasCompactSupport {σ : E → ℝ} (hσ : ContDiff ℝ ∞ σ)
    (hc : HasCompactSupport σ) :
    ∃ K₀ K₁ K₂ K₃ : ℝ, 0 ≤ K₀ ∧ 0 ≤ K₃ ∧ (∀ x, |σ x| ≤ K₀) ∧ (∀ x, ‖fderiv ℝ σ x‖ ≤ K₁) ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ σ) x‖ ≤ K₂) ∧
      (∀ x y, ‖fderiv ℝ σ x - fderiv ℝ σ y‖ ≤ K₂ * ‖x - y‖) ∧
      (∀ x y, ‖fderiv ℝ (fderiv ℝ σ) x - fderiv ℝ (fderiv ℝ σ) y‖ ≤ K₃ * ‖x - y‖) := by
  have h4 : ContDiff ℝ (4 : ℕ) σ := contDiff_infty.1 hσ 4
  have hD : ContDiff ℝ 3 (fderiv ℝ σ) := h4.fderiv_right (m := 3) (by norm_num)
  have hDD : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ σ)) := hD.fderiv_right (m := 2) (by norm_num)
  obtain ⟨K₀, hK₀0, hK₀, -⟩ := exists_lipschitz_of_hasCompactSupport (Y := ℝ)
    (h4.of_le (by norm_num)) hc
  obtain ⟨K₁, -, hK₁, hL₁⟩ := exists_lipschitz_of_hasCompactSupport (Y := E →L[ℝ] ℝ)
    (hD.of_le (by norm_num)) (hc.fderiv (𝕜 := ℝ))
  obtain ⟨K₂, -, hK₂, hL₂⟩ := exists_lipschitz_of_hasCompactSupport (Y := E →L[ℝ] E →L[ℝ] ℝ)
    (hDD.of_le (by norm_num)) ((hc.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ))
  refine ⟨K₀, K₁, max K₁ K₂, max K₂ 0, hK₀0, le_max_right _ _,
    fun x => by rw [← Real.norm_eq_abs]; exact hK₀ x, hK₁,
    fun x => (hK₂ x).trans (le_max_right _ _),
    fun x y => (hL₁ x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)),
    fun x y => (hL₂ x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))⟩

/-- Elements of `C^{0,r}_b` are bounded by and `r`-Hölder with constant their norm. -/
theorem abs_sub_le_of_zero {r : ℝ≥0} (h : BoundedContDiffHolderMap 0 r E ℝ) (x y : E) :
    |h x - h y| ≤ ‖h‖ * ‖x - y‖ ^ (r : ℝ) := by
  have h1 := h.iteratedFDerivHolder.holderWith.dist_le x y
  rw [BoundedContDiffHolderMap.coe_iteratedFDerivHolder, dist_eq_norm, dist_eq_norm,
    iteratedFDeriv_zero_eq_comp, Function.comp_apply, Function.comp_apply, ← map_sub,
    LinearIsometryEquiv.norm_map, Real.norm_eq_abs] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right
    (h.iteratedFDerivHolder.nnHolderNorm_le_norm.trans h.norm_iteratedFDerivHolder_le)
    (Real.rpow_nonneg (norm_nonneg _) _))

end Aux

/-! ### The global estimate on the manifold -/

section Manifold

open FirstPass

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] (A : HolderAtlas n M) {ι : Type*} [Fintype ι]
  (b : OrthonormalBasis ι ℝ (ComplexModel n))

/-- **The estimate in one chart**: `‖(χ_i u) ∘ e_i⁻¹‖_{C^{2,r}_b} ≤ K_g ‖g‖ + K_s (1 + ρ⁻²) S + K_u ρ^r ‖u‖`
for every scale `ρ > 0`, uniformly over the operators of the class. -/
theorem exists_chart_estimate (i : Fin A.m) {lam Λ : ℝ} {r : ℝ≥0} (hlam : 0 < lam)
    (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ Kg Ks Ku : ℝ, 0 ≤ Kg ∧ 0 ≤ Ks ∧ 0 ≤ Ku ∧
      ∀ (a : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n)
        (β : ComplexModel n → ComplexModel n) (c : ComplexModel n → ℝ),
        IsEllipticCoeff a lam Λ r → IsLowerCoeff β c Λ r →
      ∀ (u : A.HolderMap 2 r ℝ) (g : A.HolderMap 0 r ℝ) (S : ℝ), 0 ≤ S → (∀ y, |u y| ≤ S) →
      (∀ z ∈ (A.chart i).val '' tsupport (A.χ i),
        g ((A.chart i).val.symm z) = ellipticOp b a β c (fun w => u ((A.chart i).val.symm w)) z) →
      ∀ ρ : ℝ, 0 < ρ →
        ‖u.rep i‖ ≤ Kg * ‖g‖ + Ks * (1 + 1 / ρ ^ 2) * S + Ku * ρ ^ (r : ℝ) * ‖u‖ := by
  classical
  set e := A.chart i with he
  set K := e.val '' tsupport (A.χ i) with hK
  have hKc : IsCompact K := A.isCompact_image_tsupport i
  have hKt : K ⊆ e.val.target := by
    rintro _ ⟨y, hy, rfl⟩; exact e.val.map_source (A.tsupport_subset i hy)
  set χt := e.val.target.indicator (A.χ i ∘ e.val.symm) with hχt_def
  obtain ⟨hχs, hχc, hχt⟩ := HolderAtlas.HolderMap.contDiff_indicator_comp_symm e
    (A.chartSmooth i) (A.isCompact_tsupport i) (A.tsupport_subset i)
  have hsupp : ∀ z, χt z ≠ 0 → z ∈ K := by
    intro z hz
    by_cases hzt : z ∈ e.val.target
    · rw [hχt_def, indicator_of_mem hzt, comp_apply] at hz
      exact ⟨e.val.symm z, subset_tsupport _ hz, e.val.right_inv hzt⟩
    · exact absurd (indicator_of_notMem hzt _) hz
  obtain ⟨K', hK'c, hKK', hK't⟩ := exists_compact_between hKc e.val.open_target hKt
  obtain ⟨σ, hσs, hσc, hσt, hσ1⟩ :=
    exists_contDiff_eq_one_of_isCompact hK'c e.val.open_target hK't
  obtain ⟨Cv, hCv⟩ := HolderAtlas.HolderMap.exists_smul_comp_symm (A := A) (k := 2) (r := r)
    (F := ℝ) hr1.le e (contDiff_infty.1 hσs 3) hσc hσt
  obtain ⟨Ch, hCh⟩ := HolderAtlas.HolderMap.exists_smul_comp_symm (A := A) (k := 0) (r := r)
    (F := ℝ) hr1.le e (contDiff_infty.1 hχs 1) hχc hχt
  obtain ⟨C₀, hC₀, hSch⟩ := exists_schauder_estimate (Λ := Λ) b hlam hr0 hr1
  obtain ⟨K₀, K₁, K₂, K₃, hK₀0, hK₃0, hχ0, hχ1, hχ2, hχ1L, hχ2L⟩ :=
    exists_bounds_of_hasCompactSupport hχs hχc
  obtain ⟨Kσ, -, -, -, hKσ0, -, hσ0, -⟩ := exists_bounds_of_hasCompactSupport hσs hσc
  set KR := remainderConst (Fintype.card ι) Λ K₁ K₂ K₃ with hKR
  refine ⟨3 * C₀ * |Ch|, K₀ + 3 * C₀ * K₀ + 3 * C₀ * |KR| * Kσ + 96 * C₀ * |KR| * Kσ,
    6 * C₀ * |KR| * |Cv|, by positivity, by positivity, by positivity,
    fun a β c ha hβc u g S hS0 hu hrep ρ hρ => ?_⟩
  have hΛ : 0 ≤ Λ := nonneg_of_isEllipticCoeff ha
  have hK₁0 : 0 ≤ K₁ := (norm_nonneg _).trans (hχ1 0)
  have hK₂0 : 0 ≤ K₂ := (ContinuousLinearMap.opNorm_nonneg _).trans (hχ2 0)
  have hKR0 : 0 ≤ KR := by rw [hKR, remainderConst]; positivity
  rw [abs_of_nonneg hKR0]
  obtain ⟨v, hv, hvn⟩ := hCv u
  obtain ⟨h, hh, hhn⟩ := hCh g
  have hh' : ∀ z, h z = χt z * g (e.val.symm z) := fun z => by rw [hh z]; rfl
  set f := u.rep i with hf_def
  -- `f = χ̃ · (u ∘ e⁻¹) = χ̃ · v`
  have hfu : ∀ z, f z = χt z * u (e.val.symm z) := by
    intro z
    rw [hf_def, HolderAtlas.HolderMap.coe_rep]
    by_cases hzt : z ∈ e.val.target
    · rw [HolderAtlas.localRep_of_mem _ hzt, hχt_def, indicator_of_mem hzt, comp_apply,
        smul_eq_mul]
    · rw [HolderAtlas.localRep_of_notMem _ hzt, hχt_def, indicator_of_notMem hzt, zero_mul]
  have hfv : ∀ z, f z = χt z * v z := by
    intro z
    rw [hfu z, hv z, smul_eq_mul]
    by_cases hz0 : χt z = 0
    · simp [hz0]
    · rw [hσ1 z (interior_subset (hKK' (hsupp z hz0))), one_mul]
  have hfeq : ⇑f = fun z => χt z * v z := funext hfv
  have hv2 : ContDiff ℝ 2 ⇑v := WholeSpaceSolvability.contDiff_two v
  have hχ2' : ContDiff ℝ 2 χt := contDiff_infty.1 hχs 2
  -- the equation for `f`
  have hL : ∀ z, ellipticOp b a β c f z = h z + remainder b a β χt v z := by
    intro z
    rw [hfeq, ellipticOp_mul_eq b a β c hχ2' hv2, hh' z]
    congr 1
    by_cases hz0 : χt z = 0
    · rw [hz0, zero_mul, zero_mul]
    · have hzK := hsupp z hz0
      rw [hrep z hzK]
      congr 1
      refine ellipticOp_congr b a β c ?_
      filter_upwards [isOpen_interior.mem_nhds (hKK' hzK)] with w hw
      rw [hv w, hσ1 w (interior_subset hw), one_smul]
  -- bounds for `v`
  have hvS : ∀ z, |v z| ≤ Kσ * S := fun z => by
    rw [hv z, smul_eq_mul, abs_mul]; exact mul_le_mul (hσ0 z) (hu _) (abs_nonneg _) hKσ0
  have hvH : HolderWith ‖v‖.toNNReal r (fderiv ℝ (fderiv ℝ ⇑v)) :=
    HolderWith.of_dist_le fun x y => by
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (norm_nonneg _)]
      exact WholeSpaceSolvability.norm_fderiv_fderiv_sub_le v x y
  set Bv := 32 * (Kσ * S) / ρ ^ 2 + 2 * ‖v‖ * ρ ^ (r : ℝ) with hBv
  have hvB : ∀ z, ‖fderiv ℝ (fderiv ℝ ⇑v) z‖ ≤ Bv := fun z => by
    have := norm_fderiv_fderiv_le_interpolation hv2 (A := Kσ * S)
      (fun y => by rw [Real.norm_eq_abs]; exact hvS y)
      ⟨‖v‖, WholeSpaceSolvability.norm_fderiv_fderiv_le v⟩ hvH hρ z
    rwa [Real.coe_toNNReal _ (norm_nonneg _)] at this
  have hBv0 : 0 ≤ Bv := by positivity
  -- the Hölder bound for `L f`
  set Mf := ‖h‖ + KR * (Kσ * S + Bv) with hMf
  have hMf0 : 0 ≤ Mf := by positivity
  have hLf : ∀ x y, |ellipticOp b a β c f x - ellipticOp b a β c f y| ≤
      Mf * ‖x - y‖ ^ (r : ℝ) := by
    intro x y
    rw [hL x, hL y,
      show ∀ A B C D : ℝ, A + B - (C + D) = (A - C) + (B - D) from fun _ _ _ _ => by ring]
    refine (abs_add_le _ _).trans ?_
    have e1 := abs_sub_le_of_zero h x y
    have e2 := abs_remainder_sub_le b (r := (r : ℝ)) r.coe_nonneg (by exact_mod_cast hr1.le)
      hK₃0 a β ha.bound ha.holder hβc.bound_β hβc.holder_β hχ1 hχ2 hχ1L hχ2L hv2 hvS hvB x y
    calc _ ≤ ‖h‖ * ‖x - y‖ ^ (r : ℝ) + KR * (Kσ * S + Bv) * ‖x - y‖ ^ (r : ℝ) :=
          add_le_add e1 e2
      _ = Mf * ‖x - y‖ ^ (r : ℝ) := by rw [hMf]; ring
  -- the whole-space Schauder estimate for `f`
  have hfA : ∀ z, |f z| ≤ K₀ * S := fun z => by
    rw [hfu z, abs_mul]; exact mul_le_mul (hχ0 z) (hu _) (abs_nonneg _) hK₀0
  obtain ⟨s1, s2, s3⟩ := hSch a β c ha hβc f (WholeSpaceSolvability.contDiff_two f)
    ⟨‖f‖, WholeSpaceSolvability.norm_fderiv_fderiv_sub_le f⟩
    ⟨‖f‖, WholeSpaceSolvability.norm_fderiv_fderiv_le f⟩ (K₀ * S) Mf hMf0 hfA hLf
  have hfn := WholeSpaceSolvability.norm_le_of_bounds f (by positivity) hfA s3 s2 s1
  -- assembling the constants
  have e_h : ‖h‖ ≤ |Ch| * ‖g‖ :=
    hhn.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
  have e_v : ‖v‖ ≤ |Cv| * ‖u‖ :=
    hvn.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
  have hρr : 0 ≤ ρ ^ (r : ℝ) := Real.rpow_nonneg hρ.le _
  set q := 1 / ρ ^ 2 with hq
  have hq0 : 0 ≤ q := by positivity
  have hBv' : Bv ≤ 32 * Kσ * S * q + 2 * (|Cv| * ‖u‖) * ρ ^ (r : ℝ) := by
    rw [hBv, hq, show 32 * (Kσ * S) / ρ ^ 2 = 32 * Kσ * S * (1 / ρ ^ 2) by ring]
    gcongr
  have hMf' : Mf ≤ |Ch| * ‖g‖ + KR * (Kσ * S + (32 * Kσ * S * q +
      2 * (|Cv| * ‖u‖) * ρ ^ (r : ℝ))) := by
    rw [hMf]; gcongr
  calc ‖f‖ ≤ K₀ * S + C₀ * (Mf + K₀ * S) + C₀ * (Mf + K₀ * S) + C₀ * (Mf + K₀ * S) := hfn
    _ = K₀ * S + 3 * C₀ * Mf + 3 * C₀ * K₀ * S := by ring
    _ ≤ K₀ * S + 3 * C₀ * (|Ch| * ‖g‖ + KR * (Kσ * S + (32 * Kσ * S * q +
          2 * (|Cv| * ‖u‖) * ρ ^ (r : ℝ)))) + 3 * C₀ * K₀ * S := by gcongr
    _ = 3 * C₀ * |Ch| * ‖g‖ + ((K₀ + 3 * C₀ * K₀ + 3 * C₀ * KR * Kσ) * S +
          96 * C₀ * KR * Kσ * S * q) + 6 * C₀ * KR * |Cv| * ρ ^ (r : ℝ) * ‖u‖ := by ring
    _ ≤ 3 * C₀ * |Ch| * ‖g‖ + (K₀ + 3 * C₀ * K₀ + 3 * C₀ * KR * Kσ + 96 * C₀ * KR * Kσ) *
          (1 + q) * S + 6 * C₀ * KR * |Cv| * ρ ^ (r : ℝ) * ‖u‖ := by
        have h1 : 0 ≤ (K₀ + 3 * C₀ * K₀ + 3 * C₀ * KR * Kσ) * S * q := by positivity
        have h2 : 0 ≤ 96 * C₀ * KR * Kσ * S := by positivity
        have key : (K₀ + 3 * C₀ * K₀ + 3 * C₀ * KR * Kσ + 96 * C₀ * KR * Kσ) * (1 + q) * S -
            ((K₀ + 3 * C₀ * K₀ + 3 * C₀ * KR * Kσ) * S + 96 * C₀ * KR * Kσ * S * q) =
            (K₀ + 3 * C₀ * K₀ + 3 * C₀ * KR * Kσ) * S * q + 96 * C₀ * KR * Kσ * S := by ring
        linarith

/-- **The global Schauder estimate** on a compact complex manifold, `k = 0` (Székelyhidi §2.3,
end; blueprint `bou:schauder-global`): for a Hölder atlas `A` and `0 < r < 1` there is `C` such that
for every operator given chartwise by coefficients `(a_i, β_i, c_i)` in the Schauder class
`(λ, Λ, r)` on `e_i(tsupport χ_i)`, every `u ∈ C^{2,r}(M)` with `|u| ≤ S` and every
`g = L u ∈ C^{0,r}(M)`: `‖u‖_{C^{2,r}(M)} ≤ C (‖g‖_{C^{0,r}(M)} + S)`. -/
theorem exists_norm_le {lam Λ : ℝ} {r : ℝ≥0} (hlam : 0 < lam) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : Fin A.m → ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n)
        (β : Fin A.m → ComplexModel n → ComplexModel n) (c : Fin A.m → ComplexModel n → ℝ),
        (∀ i, IsEllipticCoeff (a i) lam Λ r) → (∀ i, IsLowerCoeff (β i) (c i) Λ r) →
      ∀ (u : A.HolderMap 2 r ℝ) (g : A.HolderMap 0 r ℝ) (S : ℝ), 0 ≤ S → (∀ y, |u y| ≤ S) →
      (∀ i, ∀ z ∈ (A.chart i).val '' tsupport (A.χ i),
        g ((A.chart i).val.symm z) =
          ellipticOp b (a i) (β i) (c i) (fun w => u ((A.chart i).val.symm w)) z) →
      ‖u‖ ≤ C * (‖g‖ + S) := by
  choose Kg Ks Ku hKg hKs hKu hest using
    fun i => exists_chart_estimate A b i (Λ := Λ) hlam hr0 hr1
  set SKu := ∑ i, Ku i with hSKu
  have hSKu0 : 0 ≤ SKu := Finset.sum_nonneg fun i _ => hKu i
  have hr0' : (0 : ℝ) < r := hr0
  set ρ : ℝ := (1 / (2 * (SKu + 1))) ^ (1 / (r : ℝ)) with hρ_def
  have hρ : 0 < ρ := Real.rpow_pos_of_pos (by positivity) _
  have hρr : ρ ^ (r : ℝ) = 1 / (2 * (SKu + 1)) := by
    rw [hρ_def, ← Real.rpow_mul (by positivity), one_div_mul_cancel hr0'.ne', Real.rpow_one]
  have hsmall : SKu * ρ ^ (r : ℝ) ≤ 1 / 2 := by
    rw [hρr, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set SKg := ∑ i, Kg i with hSKg
  set SKs := ∑ i, Ks i * (1 + 1 / ρ ^ 2) with hSKs
  have hSKg0 : 0 ≤ SKg := Finset.sum_nonneg fun i _ => hKg i
  have hSKs0 : 0 ≤ SKs := Finset.sum_nonneg fun i _ => by have := hKs i; positivity
  refine ⟨2 * (SKg + SKs), by positivity, fun a β c ha hβc u g S hS0 hu hrep => ?_⟩
  have hsum : ‖u‖ ≤ SKg * ‖g‖ + SKs * S + SKu * ρ ^ (r : ℝ) * ‖u‖ := by
    calc ‖u‖ = ∑ i, ‖u.rep i‖ := HolderAtlas.HolderMap.norm_def u
      _ ≤ ∑ i, (Kg i * ‖g‖ + Ks i * (1 + 1 / ρ ^ 2) * S + Ku i * ρ ^ (r : ℝ) * ‖u‖) :=
          Finset.sum_le_sum fun i _ =>
            hest i (a i) (β i) (c i) (ha i) (hβc i) u g S hS0 hu (hrep i) ρ hρ
      _ = SKg * ‖g‖ + SKs * S + SKu * ρ ^ (r : ℝ) * ‖u‖ := by
          simp only [Finset.sum_add_distrib, ← Finset.sum_mul, hSKg, hSKs, hSKu]
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg u
  have : SKu * ρ ^ (r : ℝ) * ‖u‖ ≤ 1 / 2 * ‖u‖ := mul_le_mul_of_nonneg_right hsmall hu0
  have hg0 : 0 ≤ ‖g‖ := norm_nonneg g
  nlinarith [mul_nonneg hSKg0 hS0, mul_nonneg hSKs0 hg0]

end Manifold

end SGPT.Foundations.Analysis.Pending.ManifoldSchauder
