import SGPT.Foundations.Analysis.Pending.EllipticLiouville
import SGPT.Foundations.Analysis.Pending.HolderBlowupCompactness
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Simon's blow-up proof of the Schauder estimate on the whole space

Let `E` be a finite-dimensional real inner product space with an orthonormal basis `b`, and
`0 < α < 1`.  For a coefficient field `a : E → (E →L[ℝ] E)` in the class `IsEllipticCoeff a λ Λ α`
(symmetric, `⟪a(x) v, v⟫ ≥ λ ‖v‖²`, `‖a(x)‖ ≤ Λ`, `‖a(x) - a(y)‖ ≤ Λ ‖x - y‖^α`) write
`L_a u (x) = a(x) : D²u(x) = hessTrace b (a x) (D²u x)`.

**Simon's estimate** (`exists_holder_hessian_le`): there is a constant `C`, depending only on
`(b, λ, Λ, α)`, such that every `C²` function `u` whose second derivative is bounded by `B` and
`α`-Hölder (with some constant) satisfies
`‖D²u(x) - D²u(y)‖ ≤ C (M + B) ‖x - y‖^α` whenever `L_a u` is `(M, α)`-Hölder.
With the interpolation inequalities (`HolderInterpolation`) this gives the global `C^{2,α}` estimate.

The proof is the blow-up argument of Székelyhidi, Theorem 2.8 (`szekelyhidi-extremal:page-0044`--
`page-0047`; L. Simon, *Schauder estimates by scaling*, 1997), on the whole space: normalise the
Hölder seminorm of `D²u` to `1`, pick a pair of points `p, p + h` where it is almost attained,
rescale by `ρ = ‖h‖` around `p` and subtract the quadratic Taylor term
(`W(x) = ρ^{-2-α} u(p + ρ x) - ½ ρ^{-α} D²u(p)(x, x)`), pass to a limit along an ultrafilter
(`HolderBlowupCompactness`), observe that the limit solves a constant-coefficient equation `A : D²V = 0`
with `D²V` Hölder and `D²V(0) = 0`, `‖D²V(ξ)‖ ≥ 1/2` (`blowup_contradiction`), and conclude by the
rigidity theorem (`EllipticLiouville.fderiv_fderiv_eq_of_hessTrace_eq_zero`).

Part L2.7 of the linear track for Yau's theorem.
-/

noncomputable section

open Set Filter Topology Metric
open scoped NNReal RealInnerProductSpace ContDiff

namespace SGPT.Foundations.Analysis.Pending.SchauderBlowup

open EllipticMeanValue EllipticLiouville HolderBlowupCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)

/-! ### The trace pairing -/

theorem hessTrace_sub_left (A A' : E →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] ℝ) :
    hessTrace b (A - A') Q = hessTrace b A Q - hessTrace b A' Q := by
  simp only [hessTrace, sub_apply, map_sub, Finset.sum_sub_distrib]

theorem hessTrace_sub_right (A : E →L[ℝ] E) (Q Q' : E →L[ℝ] E →L[ℝ] ℝ) :
    hessTrace b A (Q - Q') = hessTrace b A Q - hessTrace b A Q' := by
  simp only [hessTrace, sub_apply, Finset.sum_sub_distrib]

theorem hessTrace_smul_right (A : E →L[ℝ] E) (c : ℝ) (Q : E →L[ℝ] E →L[ℝ] ℝ) :
    hessTrace b A (c • Q) = c * hessTrace b A Q := by
  simp only [hessTrace, smul_apply, smul_eq_mul, Finset.mul_sum]

theorem abs_hessTrace_le (A : E →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] ℝ) :
    |hessTrace b A Q| ≤ Fintype.card ι * ‖A‖ * ‖Q‖ := by
  rw [hessTrace]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h : ∀ i, |Q (b i) (A (b i))| ≤ ‖A‖ * ‖Q‖ := fun i => by
    rw [← Real.norm_eq_abs]
    calc ‖Q (b i) (A (b i))‖ ≤ ‖Q (b i)‖ * ‖A (b i)‖ := (Q (b i)).le_opNorm _
      _ ≤ (‖Q‖ * ‖b i‖) * (‖A‖ * ‖b i‖) :=
          mul_le_mul (Q.le_opNorm _) (A.le_opNorm _) (norm_nonneg _) (by positivity)
      _ = ‖A‖ * ‖Q‖ := by rw [b.orthonormal.1 i]; ring
  calc ∑ i, |Q (b i) (A (b i))| ≤ ∑ _i : ι, ‖A‖ * ‖Q‖ := Finset.sum_le_sum fun i _ => h i
    _ = Fintype.card ι * ‖A‖ * ‖Q‖ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]; ring

theorem continuous_hessTrace (A : E →L[ℝ] E) : Continuous (hessTrace b A) :=
  continuous_finsetSum _ fun _ _ =>
    (continuous_id.clm_apply continuous_const).clm_apply continuous_const

theorem continuous_hessTrace_left (Q : E →L[ℝ] E →L[ℝ] ℝ) :
    Continuous fun A : E →L[ℝ] E => hessTrace b A Q :=
  continuous_finsetSum _ fun i _ =>
    (Q (b i)).continuous.comp (continuous_id.clm_apply continuous_const)

/-! ### Rescaling and the quadratic term -/

theorem hasFDerivAt_rescale {f : E → ℝ} (hf : Differentiable ℝ f) (c ρ : ℝ) (p x : E) :
    HasFDerivAt (fun x => c * f (p + ρ • x)) ((c * ρ) • fderiv ℝ f (p + ρ • x)) x := by
  have h1 : HasFDerivAt (fun x : E => p + ρ • x) (ρ • ContinuousLinearMap.id ℝ E) x :=
    ((hasFDerivAt_id x).const_smul ρ).const_add p
  have h2 := ((hf (p + ρ • x)).hasFDerivAt.comp x h1).const_mul c
  refine h2.congr_fderiv ?_
  ext v
  simp only [smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_id', id_eq, map_smul, smul_eq_mul]
  ring

theorem hasFDerivAt_fderiv_rescale {f : E → ℝ} (hf : Differentiable ℝ (fderiv ℝ f)) (c ρ : ℝ)
    (p x : E) :
    HasFDerivAt (fun x => (c * ρ) • fderiv ℝ f (p + ρ • x))
      ((c * ρ ^ 2) • fderiv ℝ (fderiv ℝ f) (p + ρ • x)) x := by
  have h1 : HasFDerivAt (fun x : E => p + ρ • x) (ρ • ContinuousLinearMap.id ℝ E) x :=
    ((hasFDerivAt_id x).const_smul ρ).const_add p
  have h2 := ((hf (p + ρ • x)).hasFDerivAt.comp x h1).const_smul (c * ρ)
  refine h2.congr_fderiv ?_
  ext v w
  simp only [smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_id', id_eq, map_smul, smul_eq_mul]
  ring

/-- `D(½ Q(x, x)) = Q(x, ·)` for a symmetric bilinear form `Q`. -/
theorem hasFDerivAt_half_quad (Q : E →L[ℝ] E →L[ℝ] ℝ) (hQ : ∀ v w, Q v w = Q w v) (x : E) :
    HasFDerivAt (fun x => (1 / 2 : ℝ) * Q x x) (Q x) x := by
  have h := (Q.hasFDerivAt_of_bilinear (hasFDerivAt_id x) (hasFDerivAt_id x)).const_mul (1 / 2 : ℝ)
  refine h.congr_fderiv ?_
  ext v
  simp only [smul_apply, add_apply,
    ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.coe_id', smul_eq_mul, id, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_id]
  rw [hQ v x]
  ring

/-! ### Generic normed-space helpers

Applied with an explicit `Y := E →L[ℝ] E →L[ℝ] ℝ`: for this nested type the instances
`NormSMulClass`, `ContinuousSub` are not found by instance search in this Mathlib version, and the
strong topology is only unified with the norm topology at default transparency. -/

section Generic

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem norm_smul_real (c : ℝ) (y : Y) : ‖c • y‖ = |c| * ‖y‖ := by
  rw [norm_smul, Real.norm_eq_abs]

theorem tendsto_norm_aux {l : Filter ℕ} {f : ℕ → Y} {a : Y} (hf : Tendsto f l (𝓝 a)) :
    Tendsto (fun n => ‖f n‖) l (𝓝 ‖a‖) :=
  hf.norm

theorem tendsto_norm_sub_aux {l : Filter ℕ} {f g : ℕ → Y} {a b : Y} (hf : Tendsto f l (𝓝 a))
    (hg : Tendsto g l (𝓝 b)) : Tendsto (fun n => ‖f n - g n‖) l (𝓝 ‖a - b‖) :=
  (hf.sub hg).norm

theorem eq_of_tendsto_aux {l : Filter ℕ} [l.NeBot] {f : ℕ → Y} {a b : Y}
    (hf : Tendsto f l (𝓝 a)) (hb : ∀ n, f n = b) : a = b := by
  rw [show f = fun _ => b from funext hb] at hf
  exact tendsto_nhds_unique hf tendsto_const_nhds

theorem norm_le_of_sub_eq_zero {a b : Y} {c : ℝ} (hb : b = 0) (h : ‖a - b‖ ≤ c) : ‖a‖ ≤ c := by
  rwa [hb, sub_zero] at h

theorem norm_zero_aux : ‖(0 : Y)‖ = 0 := norm_zero

theorem norm_sub_self_aux (y : Y) : ‖y - y‖ = 0 := by simp

end Generic

/-! ### The operator class and the blow-up -/

/-- The coefficient class of Simon's estimate: symmetric, uniformly elliptic with constant `lam`,
bounded by `Λ`, and `(Λ, α)`-Hölder. -/
structure IsEllipticCoeff (a : E → E →L[ℝ] E) (lam Λ α : ℝ) : Prop where
  symm : ∀ x u v, ⟪a x u, v⟫ = ⟪u, a x v⟫
  elliptic : ∀ x v, lam * ‖v‖ ^ 2 ≤ ⟪a x v, v⟫
  bound : ∀ x, ‖a x‖ ≤ Λ
  holder : ∀ x y, ‖a x - a y‖ ≤ Λ * ‖x - y‖ ^ α

/-- **The blow-up contradiction.**  There is no sequence of operators in the class and of `C²`
functions `u_n` with `[D²u_n]_α ≤ 1`, a pair of points where `[D²u_n]_α ≥ 1/2` is attained, and
`|D²u_n|_0 + [L_n u_n]_α ≤ ε_n → 0`. -/
theorem blowup_contradiction {lam Λ α : ℝ} (hlam : 0 < lam) (hα0 : 0 < α) (hα1 : α < 1)
    (a : ℕ → E → E →L[ℝ] E) (ha : ∀ n, IsEllipticCoeff (a n) lam Λ α)
    (u : ℕ → E → ℝ) (hu : ∀ n, ContDiff ℝ 2 (u n))
    (hH : ∀ n x y, ‖fderiv ℝ (fderiv ℝ (u n)) x - fderiv ℝ (fderiv ℝ (u n)) y‖ ≤ ‖x - y‖ ^ α)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hB : ∀ n x, ‖fderiv ℝ (fderiv ℝ (u n)) x‖ ≤ ε n)
    (hM : ∀ n x y, |hessTrace b (a n x) (fderiv ℝ (fderiv ℝ (u n)) x) -
      hessTrace b (a n y) (fderiv ℝ (fderiv ℝ (u n)) y)| ≤ ε n * ‖x - y‖ ^ α)
    (p h : ℕ → E) (hh : ∀ n, h n ≠ 0)
    (hgap : ∀ n, ‖h n‖ ^ α <
      2 * ‖fderiv ℝ (fderiv ℝ (u n)) (p n + h n) - fderiv ℝ (fderiv ℝ (u n)) (p n)‖) :
    False := by
  set m : ℝ := (Fintype.card ι : ℝ) with hm
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  let U : Ultrafilter ℕ := hyperfilter ℕ
  have hUle : (U : Filter ℕ) ≤ atTop := hyperfilter_le_cofinite.trans Nat.cofinite_eq_atTop.le
  have hεU : Tendsto ε U (𝓝 0) := hε.mono_left hUle
  have hε0 : ∀ n, 0 ≤ ε n := fun n => (ContinuousLinearMap.opNorm_nonneg _).trans (hB n 0)
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans ((ha 0).bound 0)
  set ρ : ℕ → ℝ := fun n => ‖h n‖ with hρ
  have hρpos : ∀ n, 0 < ρ n := fun n => norm_pos_iff.2 (hh n)
  -- `ρ^α ≤ 4 ε`, so `ρ^α → 0`
  have hρα : ∀ n, ρ n ^ α ≤ 4 * ε n := fun n => by
    have h2 : ‖fderiv ℝ (fderiv ℝ (u n)) (p n + h n) - fderiv ℝ (fderiv ℝ (u n)) (p n)‖ ≤ 2 * ε n :=
      (norm_sub_le (E := E →L[ℝ] E →L[ℝ] ℝ) _ _).trans
        ((add_le_add (hB n (p n + h n)) (hB n (p n))).trans (by linarith))
    calc ρ n ^ α = ‖h n‖ ^ α := rfl
      _ ≤ 2 * ‖fderiv ℝ (fderiv ℝ (u n)) (p n + h n) - fderiv ℝ (fderiv ℝ (u n)) (p n)‖ :=
          (hgap n).le
      _ ≤ 2 * (2 * ε n) := mul_le_mul_of_nonneg_left h2 zero_le_two
      _ = 4 * ε n := by ring
  have hρU : Tendsto (fun n => ρ n ^ α) U (𝓝 0) :=
    squeeze_zero (fun n => Real.rpow_nonneg (hρpos n).le _) hρα (by simpa using hεU.const_mul 4)
  -- derivatives of `u n`
  have hu1 : ∀ n, Differentiable ℝ (u n) := fun n => (hu n).differentiable (by norm_num)
  have hDu : ∀ n, Differentiable ℝ (fderiv ℝ (u n)) := fun n =>
    ((hu n).fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hsym : ∀ n z v w, fderiv ℝ (fderiv ℝ (u n)) z v w = fderiv ℝ (fderiv ℝ (u n)) z w v := fun n z v w =>
    ((hu n).contDiffAt.isSymmSndFDerivAt (by simp)) v w
  -- the rescaled functions `W n x = ρ^{-2-α} u(p + ρ x) - ½ ρ^{-α} D²u(p)(x, x)`
  set c : ℕ → ℝ := fun n => ρ n ^ (-2 - α) with hc
  set Q := fun n => (ρ n ^ (-α)) • fderiv ℝ (fderiv ℝ (u n)) (p n) with hQ
  have hQs : ∀ n v w, Q n v w = Q n w v := fun n v w => by
    simp only [hQ, smul_apply, smul_eq_mul]
    rw [hsym]
  set W : ℕ → E → ℝ := fun n x => c n * u n (p n + ρ n • x) - (1 / 2 : ℝ) * Q n x x with hW
  have hcρ : ∀ n, c n * ρ n ^ 2 = ρ n ^ (-α) := fun n => by
    simp only [hc]
    rw [← Real.rpow_natCast, ← Real.rpow_add (hρpos n)]
    congr 1
    push_cast
    ring
  have hW1 : ∀ n x, HasFDerivAt (W n)
      ((c n * ρ n) • fderiv ℝ (u n) (p n + ρ n • x) - Q n x) x := fun n x =>
    (hasFDerivAt_rescale (hu1 n) (c n) (ρ n) (p n) x).sub (hasFDerivAt_half_quad (Q n) (hQs n) x)
  have hW2 : ∀ n x, HasFDerivAt (fun x => (c n * ρ n) • fderiv ℝ (u n) (p n + ρ n • x) - Q n x)
      ((c n * ρ n ^ 2) • fderiv ℝ (fderiv ℝ (u n)) (p n + ρ n • x) - Q n) x := fun n x =>
    (hasFDerivAt_fderiv_rescale (hDu n) (c n) (ρ n) (p n) x).sub (Q n).hasFDerivAt
  have hDW : ∀ n, fderiv ℝ (W n) =
      fun x => (c n * ρ n) • fderiv ℝ (u n) (p n + ρ n • x) - Q n x := fun n =>
    funext fun x => (hW1 n x).fderiv
  have hD2W : ∀ n x, fderiv ℝ (fderiv ℝ (W n)) x =
      (ρ n ^ (-α)) • (fderiv ℝ (fderiv ℝ (u n)) (p n + ρ n • x) - fderiv ℝ (fderiv ℝ (u n)) (p n)) := by
    intro n x
    rw [hDW n, (hW2 n x).fderiv, hcρ]
    ext v w
    simp only [hQ, sub_apply, smul_apply, smul_eq_mul]
    ring
  have hWc : ∀ n, ContDiff ℝ 2 (W n) := fun n =>
    (contDiff_const.mul ((hu n).comp (contDiff_const.add (contDiff_const.smul contDiff_id)))).sub
      (contDiff_const.mul (((Q n).contDiff.clm_apply contDiff_id)))
  -- Hölder bound and normalisation of `D²W`
  have hραinv : ∀ n, ρ n ^ (-α) * ρ n ^ α = 1 := fun n => by
    rw [← Real.rpow_add (hρpos n), neg_add_cancel, Real.rpow_zero]
  have hWH : ∀ n x y, ‖fderiv ℝ (fderiv ℝ (W n)) x - fderiv ℝ (fderiv ℝ (W n)) y‖ ≤
      1 * ‖x - y‖ ^ α := by
    intro n x y
    have heq : ρ n ^ (-α) • (fderiv ℝ (fderiv ℝ (u n)) (p n + ρ n • x) - fderiv ℝ (fderiv ℝ (u n)) (p n)) -
        ρ n ^ (-α) • (fderiv ℝ (fderiv ℝ (u n)) (p n + ρ n • y) - fderiv ℝ (fderiv ℝ (u n)) (p n)) =
        ρ n ^ (-α) • (fderiv ℝ (fderiv ℝ (u n)) (p n + ρ n • x) -
          fderiv ℝ (fderiv ℝ (u n)) (p n + ρ n • y)) := by
      ext v w
      simp only [sub_apply, smul_apply, smul_eq_mul]
      ring
    rw [hD2W, hD2W, heq, norm_smul_real (Y := E →L[ℝ] E →L[ℝ] ℝ),
      abs_of_pos (Real.rpow_pos_of_pos (hρpos n) _), one_mul]
    have := hH n (p n + ρ n • x) (p n + ρ n • y)
    rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (hρpos n),
      Real.mul_rpow (hρpos n).le (norm_nonneg _)] at this
    calc ρ n ^ (-α) * ‖fderiv ℝ (fderiv ℝ (u n)) (p n + ρ n • x) - fderiv ℝ (fderiv ℝ (u n)) (p n + ρ n • y)‖
        ≤ ρ n ^ (-α) * (ρ n ^ α * ‖x - y‖ ^ α) :=
          mul_le_mul_of_nonneg_left this (Real.rpow_nonneg (hρpos n).le _)
      _ = ‖x - y‖ ^ α := by rw [← mul_assoc, hραinv, one_mul]
  have hW0 : ∀ n, fderiv ℝ (fderiv ℝ (W n)) 0 = 0 := fun n => by
    rw [hD2W]
    ext v w
    simp
  -- the limit
  obtain ⟨V, hVc, hVlim⟩ := exists_contDiff_two_tendsto_fderiv_fderiv U W hWc zero_le_one hα0
    hWH hW0
  -- the unit vectors where the Hölder quotient is almost attained
  set ξ : ℕ → E := fun n => (ρ n)⁻¹ • h n with hξ
  have hξn : ∀ n, ‖ξ n‖ = 1 := fun n => by
    simp only [hξ, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hρpos n)]
    exact inv_mul_cancel₀ (hρpos n).ne'
  obtain ⟨ξ0, hξ0⟩ := exists_tendsto_of_norm_le U ξ (r := 1) fun n => (hξn n).le
  have hgapW : ∀ n, 1 / 2 < ‖fderiv ℝ (fderiv ℝ (W n)) (ξ n)‖ := by
    intro n
    have hρξ : ρ n • ξ n = h n := by
      simp only [hξ, smul_smul, mul_inv_cancel₀ (hρpos n).ne', one_smul]
    rw [hD2W, hρξ, norm_smul_real (Y := E →L[ℝ] E →L[ℝ] ℝ),
      abs_of_pos (Real.rpow_pos_of_pos (hρpos n) _)]
    have h1 := hgap n
    have h2 : 0 < ρ n ^ (-α) := Real.rpow_pos_of_pos (hρpos n) _
    have h3 : ρ n ^ (-α) * ρ n ^ α = 1 := hραinv n
    simp only [hρ] at h1 h2 h3 ⊢
    nlinarith
  have hVξ : 1 / 2 ≤ ‖fderiv ℝ (fderiv ℝ V) ξ0‖ := by
    have hlim : Tendsto (fun n => ‖fderiv ℝ (fderiv ℝ (W n)) ξ0‖ + ‖ξ n - ξ0‖ ^ α) U
        (𝓝 (‖fderiv ℝ (fderiv ℝ V) ξ0‖ + 0)) := by
      refine (tendsto_norm_aux (Y := E →L[ℝ] E →L[ℝ] ℝ) (hVlim ξ0)).add ?_
      have h1 : Tendsto (fun n => ‖ξ n - ξ0‖) U (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 hξ0
      have h2 := h1.rpow_const (p := α) (Or.inr hα0.le)
      rwa [Real.zero_rpow hα0.ne'] at h2
    rw [add_zero] at hlim
    refine ge_of_tendsto hlim (Eventually.of_forall fun n => ?_)
    have h1 := hgapW n
    have h2 := hWH n (ξ n) ξ0
    have h3 := norm_le_insert' (E := E →L[ℝ] E →L[ℝ] ℝ) (fderiv ℝ (fderiv ℝ (W n)) (ξ n))
      (fderiv ℝ (fderiv ℝ (W n)) ξ0)
    linarith
  -- the limit operator
  obtain ⟨A, hA⟩ := exists_tendsto_of_norm_le (Y := E →L[ℝ] E) U (fun n => a n (p n))
    fun n => (ha n).bound _
  have hAs : ∀ v w, ⟪A v, w⟫ = ⟪v, A w⟫ := by
    intro v w
    have h1 : Tendsto (fun n => ⟪a n (p n) v, w⟫) U (𝓝 ⟪A v, w⟫) :=
      ((continuous_id.clm_apply continuous_const).inner (𝕜 := ℝ) continuous_const).tendsto A |>.comp hA
    have h2 : Tendsto (fun n => ⟪a n (p n) v, w⟫) U (𝓝 ⟪v, A w⟫) := by
      have hc : Continuous fun T : E →L[ℝ] E => ⟪v, T w⟫ :=
        (innerSL ℝ v).continuous.comp (ContinuousLinearMap.apply ℝ E w).continuous
      have := (hc.tendsto A).comp hA
      refine this.congr fun n => ?_
      simp only [Function.comp_apply]
      exact ((ha n).symm _ v w).symm
    exact tendsto_nhds_unique h1 h2
  have hAe : ∀ v, lam * ‖v‖ ^ 2 ≤ ⟪A v, v⟫ := by
    intro v
    have h1 : Tendsto (fun n => ⟪a n (p n) v, v⟫) U (𝓝 ⟪A v, v⟫) :=
      ((continuous_id.clm_apply continuous_const).inner (𝕜 := ℝ) continuous_const).tendsto A |>.comp hA
    exact ge_of_tendsto h1 (Eventually.of_forall fun n => (ha n).elliptic _ v)
  -- the limit equation `A : D²V = 0`
  have hAeq : ∀ x, hessTrace b A (fderiv ℝ (fderiv ℝ V) x) = 0 := by
    intro x
    set β : ℕ → ℝ := fun n => m * (‖A - a n (p n)‖ + Λ * (ρ n ^ α * ‖x‖ ^ α)) * ‖x‖ ^ α +
      ε n * ‖x‖ ^ α * (1 + m * Λ) with hβ
    have hβlim : Tendsto β U (𝓝 0) := by
      have h1 : Tendsto (fun n => ‖A - a n (p n)‖) U (𝓝 0) := by
        have := tendsto_iff_norm_sub_tendsto_zero.1 hA
        refine this.congr fun n => ?_
        rw [norm_sub_rev]
      have := ((((h1.add ((hρU.mul_const (‖x‖ ^ α)).const_mul Λ)).const_mul m).mul_const
        (‖x‖ ^ α)).add ((hεU.mul_const (‖x‖ ^ α)).mul_const (1 + m * Λ)))
      simpa [hβ] using this
    have hT : ∀ n, |hessTrace b A (fderiv ℝ (fderiv ℝ (W n)) x)| ≤ β n := by
      intro n
      obtain ⟨z, hz⟩ : ∃ z, p n + ρ n • x = z := ⟨_, rfl⟩
      have hzp : ‖p n - z‖ ^ α = ρ n ^ α * ‖x‖ ^ α := by
        rw [← hz, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (hρpos n),
          Real.mul_rpow (hρpos n).le (norm_nonneg _)]
      have hzp' : ‖z - p n‖ ^ α = ρ n ^ α * ‖x‖ ^ α := by rw [norm_sub_rev, hzp]
      obtain ⟨Q0, hQ0⟩ : ∃ Q0 : E →L[ℝ] E →L[ℝ] ℝ, fderiv ℝ (fderiv ℝ (W n)) x = Q0 := ⟨_, rfl⟩
      obtain ⟨Dz, hDz⟩ : ∃ Dz : E →L[ℝ] E →L[ℝ] ℝ, fderiv ℝ (fderiv ℝ (u n)) z = Dz := ⟨_, rfl⟩
      obtain ⟨Dp, hDp⟩ : ∃ Dp : E →L[ℝ] E →L[ℝ] ℝ, fderiv ℝ (fderiv ℝ (u n)) (p n) = Dp :=
        ⟨_, rfl⟩
      have hQ0eq : Q0 = ρ n ^ (-α) • (Dz - Dp) := by rw [← hQ0, hD2W, hz, hDz, hDp]
      have hDWx : ‖Q0‖ ≤ ‖x‖ ^ α := by
        have h := hWH n x 0
        rw [hQ0, hW0, sub_zero, one_mul] at h
        exact norm_le_of_sub_eq_zero (Y := E →L[ℝ] E →L[ℝ] ℝ) rfl (by simpa using h)
      have hDp_le : ‖Dp‖ ≤ ε n := by rw [← hDp]; exact hB n (p n)
      have hM' : |hessTrace b (a n z) Dz - hessTrace b (a n (p n)) Dp| ≤
          ε n * (ρ n ^ α * ‖x‖ ^ α) := by
        have := hM n z (p n)
        rwa [hzp', hDz, hDp] at this
      have hAz : ‖a n (p n) - a n z‖ ≤ Λ * (ρ n ^ α * ‖x‖ ^ α) := by
        rw [← hzp]; exact (ha n).holder _ _
      rw [hQ0]
      have e1 := hessTrace_sub_left b A (a n z) Q0
      have e2 : hessTrace b (a n z) Q0 =
          ρ n ^ (-α) * (hessTrace b (a n z) Dz - hessTrace b (a n z) Dp) := by
        rw [hQ0eq, hessTrace_smul_right, hessTrace_sub_right]
      have e3 := hessTrace_sub_left b (a n (p n)) (a n z) Dp
      have hfirst : |hessTrace b (A - a n z) Q0| ≤
          m * (‖A - a n (p n)‖ + Λ * (ρ n ^ α * ‖x‖ ^ α)) * ‖x‖ ^ α := by
        refine (abs_hessTrace_le b _ _).trans ?_
        have h1 : ‖A - a n z‖ ≤ ‖A - a n (p n)‖ + Λ * (ρ n ^ α * ‖x‖ ^ α) :=
          (norm_sub_le_norm_sub_add_norm_sub A (a n (p n)) (a n z)).trans
            (add_le_add le_rfl hAz)
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hm0) hDWx (norm_nonneg Q0)
          (mul_nonneg hm0 (by positivity))
      have h2 : |hessTrace b (a n (p n) - a n z) Dp| ≤ m * (Λ * (ρ n ^ α * ‖x‖ ^ α)) * ε n :=
        (abs_hessTrace_le b _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left hAz hm0) hDp_le
          (norm_nonneg Dp) (mul_nonneg hm0 (by positivity)))
      have hsecond : |hessTrace b (a n z) Q0| ≤ ε n * ‖x‖ ^ α * (1 + m * Λ) := by
        have hsplit : hessTrace b (a n z) Dz - hessTrace b (a n z) Dp =
            (hessTrace b (a n z) Dz - hessTrace b (a n (p n)) Dp) +
              hessTrace b (a n (p n) - a n z) Dp := by
          rw [e3]; ring
        rw [e2, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (hρpos n) _), hsplit]
        calc ρ n ^ (-α) * |hessTrace b (a n z) Dz - hessTrace b (a n (p n)) Dp +
              hessTrace b (a n (p n) - a n z) Dp|
            ≤ ρ n ^ (-α) * (ε n * (ρ n ^ α * ‖x‖ ^ α) + m * (Λ * (ρ n ^ α * ‖x‖ ^ α)) * ε n) :=
              mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hM' h2))
                (Real.rpow_nonneg (hρpos n).le _)
          _ = (ρ n ^ (-α) * ρ n ^ α) * (ε n * ‖x‖ ^ α * (1 + m * Λ)) := by ring
          _ = ε n * ‖x‖ ^ α * (1 + m * Λ) := by rw [hραinv, one_mul]
      have hsum : hessTrace b A Q0 = hessTrace b (A - a n z) Q0 + hessTrace b (a n z) Q0 := by
        rw [e1]; ring
      rw [hsum]
      exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)
    obtain ⟨Q, hQ⟩ : ∃ Q : E →L[ℝ] E →L[ℝ] ℝ, fderiv ℝ (fderiv ℝ V) x = Q := ⟨_, rfl⟩
    have hQn : Tendsto (fun n => ‖fderiv ℝ (fderiv ℝ (W n)) x - Q‖) U (𝓝 0) := by
      have h := tendsto_norm_sub_aux (Y := E →L[ℝ] E →L[ℝ] ℝ) (hVlim x)
        (tendsto_const_nhds (x := fderiv ℝ (fderiv ℝ V) x))
      rw [sub_self, norm_zero_aux (Y := E →L[ℝ] E →L[ℝ] ℝ)] at h
      rwa [hQ] at h
    have hbound : ∀ n, |hessTrace b A Q| ≤
        β n + m * ‖A‖ * ‖fderiv ℝ (fderiv ℝ (W n)) x - Q‖ := by
      intro n
      obtain ⟨Qn, hQn'⟩ : ∃ Qn : E →L[ℝ] E →L[ℝ] ℝ, fderiv ℝ (fderiv ℝ (W n)) x = Qn :=
        ⟨_, rfl⟩
      have h1 := hT n
      rw [hQn'] at h1 ⊢
      have e := hessTrace_sub_right b A Q Qn
      have h2 := abs_hessTrace_le b A (Q - Qn)
      rw [norm_sub_rev (E := E →L[ℝ] E →L[ℝ] ℝ)] at h2
      calc |hessTrace b A Q| = |hessTrace b A Qn + hessTrace b A (Q - Qn)| := by rw [e]; ring_nf
        _ ≤ |hessTrace b A Qn| + |hessTrace b A (Q - Qn)| := abs_add_le _ _
        _ ≤ β n + m * ‖A‖ * ‖Qn - Q‖ := add_le_add h1 h2
    have hlim : Tendsto (fun n => β n + m * ‖A‖ * ‖fderiv ℝ (fderiv ℝ (W n)) x - Q‖) U (𝓝 0) := by
      simpa using hβlim.add (hQn.const_mul (m * ‖A‖))
    rw [hQ]
    exact abs_nonpos_iff.1 (ge_of_tendsto hlim (Eventually.of_forall hbound))
  -- `D²V` is Hölder, hence constant by rigidity
  have hVH : ∀ x y, ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ V) y‖ ≤ 1 * ‖x - y‖ ^ α :=
    fun x y => le_of_tendsto (tendsto_norm_sub_aux (Y := E →L[ℝ] E →L[ℝ] ℝ) (hVlim x) (hVlim y))
      (Eventually.of_forall fun n => hWH n x y)
  have hV0 : fderiv ℝ (fderiv ℝ V) 0 = 0 :=
    eq_of_tendsto_aux (Y := E →L[ℝ] E →L[ℝ] ℝ) (hVlim 0) hW0
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  have hconst := fderiv_fderiv_eq_of_hessTrace_eq_zero b hAs hlam hAe hVc hAeq zero_le_one
    hα0.le hα1 hVH ξ0
  rw [hconst, hV0, norm_zero_aux (Y := E →L[ℝ] E →L[ℝ] ℝ)] at hVξ
  norm_num at hVξ

/-- `D²(c f) = c D²f`. -/
theorem fderiv_fderiv_const_mul {f : E → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ) (z : E) :
    fderiv ℝ (fderiv ℝ (fun z => c * f z)) z = c • fderiv ℝ (fderiv ℝ f) z := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hDf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have h1 : fderiv ℝ (fun z => c * f z) = fun z => c • fderiv ℝ f z :=
    funext fun z => ((hf1 z).hasFDerivAt.const_mul c).fderiv
  rw [h1]
  exact ((hDf z).hasFDerivAt.const_smul c).fderiv

/-- **Simon's Schauder estimate on the whole space** (Székelyhidi Thm 2.8, first part, global form):
there is `C = C(b, λ, Λ, α)` such that for every coefficient field in `IsEllipticCoeff a λ Λ α` and
every `C²` function `u` with `α`-Hölder second derivative,
`[D²u]_α ≤ C ([L_a u]_α + |D²u|_0)`, where `L_a u = a : D²u`. -/
theorem exists_holder_hessian_le {lam Λ α : ℝ} (hlam : 0 < lam) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : E → E →L[ℝ] E, IsEllipticCoeff a lam Λ α →
      ∀ u : E → ℝ, ContDiff ℝ 2 u →
      (∃ H : ℝ, ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H * ‖x - y‖ ^ α) →
      ∀ B M : ℝ, (∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ B) →
      (∀ x y, |hessTrace b (a x) (fderiv ℝ (fderiv ℝ u) x) -
        hessTrace b (a y) (fderiv ℝ (fderiv ℝ u) y)| ≤ M * ‖x - y‖ ^ α) →
      ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ C * (M + B) * ‖x - y‖ ^ α := by
  by_contra hcon
  push Not at hcon
  choose a ha u hu hH B M hB hM x y hxy using fun n : ℕ => hcon n (Nat.cast_nonneg n)
  -- the Hölder quotients of `D²u n`
  set q : ℕ → E → E → ℝ := fun n z w =>
    ‖fderiv ℝ (fderiv ℝ (u n)) z - fderiv ℝ (fderiv ℝ (u n)) w‖ / ‖z - w‖ ^ α with hq
  set Qs : ℕ → Set ℝ := fun n => {t | ∃ z w, z ≠ w ∧ t = q n z w} with hQs
  have hpow : ∀ z w : E, z ≠ w → 0 < ‖z - w‖ ^ α := fun z w hzw =>
    Real.rpow_pos_of_pos (norm_pos_iff.2 (sub_ne_zero.2 hzw)) _
  have hxy' : ∀ n, x n ≠ y n := by
    intro n hxy0
    have := hxy n
    rw [hxy0, sub_self, norm_zero, Real.zero_rpow hα0.ne', mul_zero,
      norm_sub_self_aux (Y := E →L[ℝ] E →L[ℝ] ℝ)] at this
    exact lt_irrefl 0 this
  have hbdd : ∀ n, BddAbove (Qs n) := by
    intro n
    obtain ⟨H, hH'⟩ := hH n
    refine ⟨H, ?_⟩
    rintro t ⟨z, w, hzw, rfl⟩
    simp only [hq]
    rw [div_le_iff₀ (hpow z w hzw)]
    exact hH' z w
  have hmem : ∀ n, q n (x n) (y n) ∈ Qs n := fun n => ⟨x n, y n, hxy' n, rfl⟩
  have hB0 : ∀ n, 0 ≤ B n := fun n => (ContinuousLinearMap.opNorm_nonneg _).trans (hB n 0)
  have hM0 : ∀ n, 0 ≤ M n := by
    intro n
    have h1 := hM n (x n) (y n)
    have h2 := hpow _ _ (hxy' n)
    by_contra hneg
    push Not at hneg
    have : M n * ‖x n - y n‖ ^ α < 0 := mul_neg_of_neg_of_pos hneg h2
    linarith [abs_nonneg (hessTrace b (a n (x n)) (fderiv ℝ (fderiv ℝ (u n)) (x n)) -
      hessTrace b (a n (y n)) (fderiv ℝ (fderiv ℝ (u n)) (y n)))]
  set S : ℕ → ℝ := fun n => sSup (Qs n) with hS
  have hqS : ∀ n z w, z ≠ w → q n z w ≤ S n := fun n z w hzw =>
    le_csSup (hbdd n) ⟨z, w, hzw, rfl⟩
  have hSgt : ∀ n : ℕ, (n : ℝ) * (M n + B n) < S n := by
    intro n
    refine lt_of_lt_of_le ?_ (hqS n _ _ (hxy' n))
    simp only [hq]
    rw [lt_div_iff₀ (hpow _ _ (hxy' n))]
    exact hxy n
  have hSpos : ∀ n, 0 < S n := fun n =>
    lt_of_le_of_lt (mul_nonneg (Nat.cast_nonneg n) (add_nonneg (hM0 n) (hB0 n))) (hSgt n)
  -- a pair where the quotient exceeds `S / 2`
  have hpair : ∀ n, ∃ z w, z ≠ w ∧ S n / 2 < q n z w := by
    intro n
    obtain ⟨t, ⟨z, w, hzw, rfl⟩, ht⟩ :=
      exists_lt_of_lt_csSup ⟨_, hmem n⟩ (half_lt_self (hSpos n))
    exact ⟨z, w, hzw, ht⟩
  choose z w hzw hzwq using hpair
  -- normalise
  set v : ℕ → E → ℝ := fun n t => (S n)⁻¹ * u n t with hv
  have hvc : ∀ n, ContDiff ℝ 2 (v n) := fun n => contDiff_const.mul (hu n)
  have hD2v : ∀ n t, fderiv ℝ (fderiv ℝ (v n)) t = (S n)⁻¹ • fderiv ℝ (fderiv ℝ (u n)) t :=
    fun n t => fderiv_fderiv_const_mul (hu n) _ t
  have hSinv : ∀ n, 0 < (S n)⁻¹ := fun n => inv_pos.2 (hSpos n)
  have hnormsub : ∀ n t t', ‖fderiv ℝ (fderiv ℝ (v n)) t - fderiv ℝ (fderiv ℝ (v n)) t'‖ =
      (S n)⁻¹ * ‖fderiv ℝ (fderiv ℝ (u n)) t - fderiv ℝ (fderiv ℝ (u n)) t'‖ := by
    intro n t t'
    have heq : (S n)⁻¹ • fderiv ℝ (fderiv ℝ (u n)) t - (S n)⁻¹ • fderiv ℝ (fderiv ℝ (u n)) t' =
        (S n)⁻¹ • (fderiv ℝ (fderiv ℝ (u n)) t - fderiv ℝ (fderiv ℝ (u n)) t') := by
      ext e1 e2
      simp only [sub_apply, smul_apply, smul_eq_mul]
      ring
    rw [hD2v, hD2v, heq, norm_smul_real (Y := E →L[ℝ] E →L[ℝ] ℝ), abs_of_pos (hSinv n)]
  have hnorm : ∀ n t, ‖fderiv ℝ (fderiv ℝ (v n)) t‖ =
      (S n)⁻¹ * ‖fderiv ℝ (fderiv ℝ (u n)) t‖ := by
    intro n t
    rw [hD2v, norm_smul_real (Y := E →L[ℝ] E →L[ℝ] ℝ), abs_of_pos (hSinv n)]
  have htr : ∀ n t, hessTrace b (a n t) (fderiv ℝ (fderiv ℝ (v n)) t) =
      (S n)⁻¹ * hessTrace b (a n t) (fderiv ℝ (fderiv ℝ (u n)) t) := by
    intro n t
    rw [hD2v, hessTrace_smul_right]
  set ε : ℕ → ℝ := fun n => (M n + B n) / S n with hε
  have hε0 : ∀ n, 0 ≤ ε n := fun n => div_nonneg (add_nonneg (hM0 n) (hB0 n)) (hSpos n).le
  have hεle : ∀ n : ℕ, 1 ≤ n → ε n ≤ 1 / (n : ℝ) := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [hε, div_le_div_iff₀ (hSpos n) hn', one_mul, mul_comm]
    exact (hSgt n).le
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall hε0) ?_ tendsto_one_div_atTop_nhds_zero_nat
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact hεle n hn
  refine blowup_contradiction b hlam hα0 hα1 a ha v hvc ?_ ε hεlim ?_ ?_ z
    (fun n => w n - z n) (fun n => sub_ne_zero.2 (hzw n).symm) ?_
  · -- `[D²v]_α ≤ 1`
    intro n t t'
    rw [hnormsub]
    by_cases htt : t = t'
    · rw [htt, sub_self, norm_zero_aux (Y := E →L[ℝ] E →L[ℝ] ℝ), mul_zero]
      exact Real.rpow_nonneg (norm_nonneg _) _
    · have h1 := hqS n t t' htt
      rw [hq, div_le_iff₀ (hpow t t' htt)] at h1
      calc (S n)⁻¹ * ‖fderiv ℝ (fderiv ℝ (u n)) t - fderiv ℝ (fderiv ℝ (u n)) t'‖
          ≤ (S n)⁻¹ * (S n * ‖t - t'‖ ^ α) := mul_le_mul_of_nonneg_left h1 (hSinv n).le
        _ = ‖t - t'‖ ^ α := by rw [← mul_assoc, inv_mul_cancel₀ (hSpos n).ne', one_mul]
  · -- `|D²v|_0 ≤ ε`
    intro n t
    rw [hnorm]
    calc (S n)⁻¹ * ‖fderiv ℝ (fderiv ℝ (u n)) t‖ ≤ (S n)⁻¹ * B n :=
          mul_le_mul_of_nonneg_left (hB n t) (hSinv n).le
      _ ≤ ε n := by
          simp only [hε]
          rw [div_eq_inv_mul]
          exact mul_le_mul_of_nonneg_left (by linarith [hM0 n]) (hSinv n).le
  · -- `[L v]_α ≤ ε`
    intro n t t'
    rw [htr, htr, ← mul_sub, abs_mul, abs_of_pos (hSinv n)]
    calc (S n)⁻¹ * |hessTrace b (a n t) (fderiv ℝ (fderiv ℝ (u n)) t) -
          hessTrace b (a n t') (fderiv ℝ (fderiv ℝ (u n)) t')| ≤ (S n)⁻¹ * (M n * ‖t - t'‖ ^ α) :=
          mul_le_mul_of_nonneg_left (hM n t t') (hSinv n).le
      _ ≤ ε n * ‖t - t'‖ ^ α := by
          simp only [hε]
          rw [div_eq_inv_mul, mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (hSinv n).le
          exact mul_le_mul_of_nonneg_right (by linarith [hB0 n]) (Real.rpow_nonneg (norm_nonneg _) _)
  · -- the gap
    intro n
    rw [add_sub_cancel, hnormsub]
    have h1 := hzwq n
    simp only [hq] at h1
    rw [lt_div_iff₀ (hpow _ _ (hzw n)), norm_sub_rev (z n) (w n)] at h1
    have h2 : ‖fderiv ℝ (fderiv ℝ (u n)) (z n) - fderiv ℝ (fderiv ℝ (u n)) (w n)‖ =
        ‖fderiv ℝ (fderiv ℝ (u n)) (w n) - fderiv ℝ (fderiv ℝ (u n)) (z n)‖ :=
      norm_sub_rev (E := E →L[ℝ] E →L[ℝ] ℝ) _ _
    rw [h2] at h1
    have h3 : S n / 2 * ‖w n - z n‖ ^ α * (S n)⁻¹ = ‖w n - z n‖ ^ α / 2 := by
      have := (hSpos n).ne'
      field_simp
    have h4 := mul_lt_mul_of_pos_right h1 (hSinv n)
    rw [h3] at h4
    nlinarith [h4]

end SGPT.Foundations.Analysis.Pending.SchauderBlowup
