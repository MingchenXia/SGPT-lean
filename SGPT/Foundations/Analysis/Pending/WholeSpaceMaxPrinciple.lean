import SGPT.Foundations.Analysis.Pending.SchauderWholeSpace
import SGPT.Foundations.Analysis.Pending.HessianLocalExtremum
import Mathlib.Analysis.InnerProductSpace.Spectrum

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The maximum principle for `L - μ` on the whole space

Let `E` be a finite-dimensional real inner product space with an orthonormal basis `b`, and let
`L u = a : D²u + Du(β) + c u` (`SchauderWholeSpace.ellipticOp`) with `a(x)` symmetric and positive
semidefinite, `‖a(x)‖ ≤ Λ`, `‖β(x)‖ ≤ Λ` and `c ≤ 0`.  For `μ > 0` and every BOUNDED `C²` function
`u` (`abs_le_of_ellipticOp_sub`):

`μ |u|_0 ≤ |L u - μ u|_0`.

The supremum of `u` need not be attained on the whole space; it is approximated by the maxima of
`u - ε |x - x₀|²` (attained in the unit ball around an almost-maximising point `x₀`), where the
second-order condition `D²v ≤ 0` (`IsLocalMax.fderiv_fderiv_nonpos`, L5, TN-CLASSICAL's
`HessianLocalExtremum`) gives `a : D²u ≤ 2 ε tr a`.

Linear algebra: `a : Q = hessTrace b a Q` does not depend on the orthonormal basis
(`hessTrace_eq_of_orthonormalBasis`), and `a : Q ≤ 0` when `a` is symmetric positive semidefinite
and `Q(h, h) ≤ 0` for all `h` (`hessTrace_nonpos`, computed in an eigenbasis of `a`).

Part of L2.9 of the linear track for Yau's theorem
(the linear elliptic estimates; blueprint `bou:max-principle`): it gives
the `C⁰` bound of the parameter-dependent Schauder estimate and the injectivity of `L - μ`.
-/

noncomputable section

open Set Filter Topology Metric
open scoped RealInnerProductSpace

namespace SGPT.Foundations.Analysis.Pending.WholeSpaceMaxPrinciple

open EllipticMeanValue SchauderBlowup SchauderWholeSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)

/-! ### Linear algebra of `a : Q` -/

/-- The inner product as a continuous bilinear map `E →L[ℝ] E →L[ℝ] ℝ`. -/
def innerBilin : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ

@[simp]
theorem innerBilin_apply (v w : E) : innerBilin v w = ⟪v, w⟫ := rfl

/-- `a : Q = ∑ᵢ Q(bᵢ, a bᵢ)` does not depend on the orthonormal basis. -/
theorem hessTrace_eq_of_orthonormalBasis {κ : Type*} [Fintype κ] (e : OrthonormalBasis κ ℝ E)
    (A : E →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] ℝ) : hessTrace b A Q = hessTrace e A Q := by
  simp only [hessTrace]
  have h1 : ∀ i, Q (b i) (A (b i)) = ∑ k, ⟪e k, b i⟫ * Q (e k) (A (b i)) := by
    intro i
    have hQ : Q (b i) = ∑ k, ⟪e k, b i⟫ • Q (e k) := by
      conv_lhs => rw [← e.sum_repr' (b i)]
      simp only [map_sum, map_smul]
    rw [hQ]
    simp
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hA : A (e k) = ∑ i, ⟪b i, e k⟫ • A (b i) := by
    conv_lhs => rw [← b.sum_repr' (e k)]
    simp only [map_sum, map_smul]
  rw [hA, map_sum]
  simp only [map_smul, smul_eq_mul, real_inner_comm (e k)]

/-- **`a : Q ≤ 0`** for `a` symmetric positive semidefinite and `Q(h, h) ≤ 0` for all `h`. -/
theorem hessTrace_nonpos {A : E →L[ℝ] E} (hA : ∀ v w, ⟪A v, w⟫ = ⟪v, A w⟫)
    (hApos : ∀ v, 0 ≤ ⟪A v, v⟫) {Q : E →L[ℝ] E →L[ℝ] ℝ} (hQ : ∀ h, Q h h ≤ 0) :
    hessTrace b A Q ≤ 0 := by
  have hsym : (A : E →ₗ[ℝ] E).IsSymmetric := fun v w => hA v w
  set e := hsym.eigenvectorBasis rfl with he
  rw [hessTrace_eq_of_orthonormalBasis b e, hessTrace]
  refine Finset.sum_nonpos fun j _ => ?_
  have hev : A (e j) = (hsym.eigenvalues rfl j : ℝ) • e j :=
    hsym.apply_eigenvectorBasis rfl j
  have hev0 : 0 ≤ hsym.eigenvalues rfl j := by
    have h := hApos (e j)
    rw [hev, inner_smul_left, real_inner_self_eq_norm_sq, e.orthonormal.1 j] at h
    simpa using h
  rw [hev, map_smul, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos hev0 (hQ (e j))

/-- `a : ⟪·, ·⟫ = ∑ᵢ ⟪bᵢ, a bᵢ⟫ ≤ (dim) ‖a‖`. -/
theorem hessTrace_innerBilin_le (A : E →L[ℝ] E) :
    hessTrace b A innerBilin ≤ Fintype.card ι * ‖A‖ := by
  have h := abs_hessTrace_le b A innerBilin
  have hn : ‖(innerBilin : E →L[ℝ] E →L[ℝ] ℝ)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    rw [one_mul]
    exact (innerSL_apply_norm ℝ v).le
  calc hessTrace b A innerBilin ≤ |hessTrace b A innerBilin| := le_abs_self _
    _ ≤ Fintype.card ι * ‖A‖ * ‖(innerBilin : E →L[ℝ] E →L[ℝ] ℝ)‖ := h
    _ ≤ Fintype.card ι * ‖A‖ * 1 := by gcongr
    _ = Fintype.card ι * ‖A‖ := mul_one _

/-! ### The paraboloid `‖x - x₀‖²` -/

theorem hasFDerivAt_norm_sub_sq (x₀ y : E) :
    HasFDerivAt (fun y => ‖y - x₀‖ ^ 2) ((2 : ℝ) • innerBilin (y - x₀)) y := by
  have h := ((hasFDerivAt_id y).sub_const x₀).norm_sq
  refine h.congr_fderiv ?_
  ext v
  simp only [smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    innerSL_apply_apply, id_eq, nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul]
  rfl

theorem hasFDerivAt_two_smul_innerBilin_sub (x₀ y : E) :
    HasFDerivAt (fun y => (2 : ℝ) • innerBilin (y - x₀)) ((2 : ℝ) • (innerBilin : E →L[ℝ] E →L[ℝ] ℝ)) y := by
  have h := ((innerBilin : E →L[ℝ] E →L[ℝ] ℝ).hasFDerivAt.comp y
    ((hasFDerivAt_id y).sub_const x₀)).const_smul (2 : ℝ)
  refine HasFDerivAt.congr_fderiv (f := fun y => (2 : ℝ) • innerBilin (y - x₀)) h ?_
  rw [ContinuousLinearMap.comp_id]

/-! ### The maximum principle -/

section MaxPrinciple

variable {u : E → ℝ}

theorem ellipticOp_neg (a : E → E →L[ℝ] E) (β : E → E) (c : E → ℝ) (u : E → ℝ) (x : E) :
    ellipticOp b a β c (fun y => -u y) x = -ellipticOp b a β c u x := by
  have h1 : fderiv ℝ (fun y => -u y) = fun y => -fderiv ℝ u y := funext fun y => fderiv_neg
  have h2 : fderiv ℝ (fderiv ℝ fun y => -u y) x = -fderiv ℝ (fderiv ℝ u) x := by
    rw [h1]; exact fderiv_neg
  have h3 : hessTrace b (a x) (-fderiv ℝ (fderiv ℝ u) x) = -hessTrace b (a x) (fderiv ℝ (fderiv ℝ u) x) := by
    simp only [hessTrace, neg_apply, Finset.sum_neg_distrib]
  simp only [ellipticOp]
  rw [h2, h3, h1]
  simp only [neg_apply]
  ring

/-- **The maximum principle, one-sided**: if `a` is symmetric positive semidefinite and bounded by
`Λ`, `‖β‖ ≤ Λ`, `c ≤ 0`, `μ > 0`, `u` is `C²` and bounded above, and `L u - μ u ≥ -F` with `F ≥ 0`,
then `μ u ≤ F`. -/
theorem mul_le_of_ellipticOp_sub {a : E → E →L[ℝ] E} {β : E → E} {c : E → ℝ} {Λ μ F : ℝ}
    (hsymm : ∀ x v w, ⟪a x v, w⟫ = ⟪v, a x w⟫) (hpos : ∀ x v, 0 ≤ ⟪a x v, v⟫)
    (ha : ∀ x, ‖a x‖ ≤ Λ) (hβ : ∀ x, ‖β x‖ ≤ Λ) (hc : ∀ x, c x ≤ 0) (hμ : 0 < μ) (hF0 : 0 ≤ F)
    (hu : ContDiff ℝ 2 u) (hbdd : ∃ A, ∀ x, u x ≤ A)
    (hF : ∀ x, -F ≤ ellipticOp b a β c u x - μ * u x) (x : E) : μ * u x ≤ F := by
  obtain ⟨A, hA⟩ := hbdd
  have hbd : BddAbove (range u) := ⟨A, by rintro _ ⟨y, rfl⟩; exact hA y⟩
  set s : ℝ := ⨆ y, u y with hs_def
  have hus : ∀ y, u y ≤ s := fun y => le_ciSup hbd y
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans (hβ 0)
  set K : ℝ := μ + 2 * Λ * (Fintype.card ι + 1) with hK
  have hK0 : 0 ≤ K := by positivity
  suffices hsF : μ * s ≤ F from (mul_le_mul_of_nonneg_left (hus x) hμ.le).trans hsF
  rcases le_or_gt s 0 with hs0 | hs0
  · exact (mul_nonpos_of_nonneg_of_nonpos hμ.le hs0).trans hF0
  -- the core estimate at a fixed `ε ∈ (0, s)`
  have hcore : ∀ ε, 0 < ε → ε < s → μ * s ≤ F + ε * K := by
    intro ε hε hεs
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, s - ε < u x₀ := exists_lt_of_lt_ciSup (by linarith)
    set v : E → ℝ := fun y => u y - ε * ‖y - x₀‖ ^ 2 with hv_def
    have hq : ContDiff ℝ 2 fun y : E => ‖y - x₀‖ ^ 2 :=
      (contDiff_id.sub contDiff_const).norm_sq ℝ
    have hv : ContDiff ℝ 2 v := hu.sub (contDiff_const.mul hq)
    obtain ⟨p, hpK, hpmax⟩ := (isCompact_closedBall x₀ 1).exists_isMaxOn
      (nonempty_closedBall.2 zero_le_one) hv.continuous.continuousOn
    have hvx₀ : v x₀ = u x₀ := by simp [hv_def]
    have hvp : s - ε < v p := hx₀.trans_le (hvx₀ ▸ hpmax (mem_closedBall_self zero_le_one))
    have hglob : ∀ y, v y ≤ v p := by
      intro y
      by_cases hy : y ∈ closedBall x₀ 1
      · exact hpmax hy
      · have h1 : 1 < ‖y - x₀‖ := by rw [mem_closedBall, dist_eq_norm] at hy; linarith
        have h2 : 1 ≤ ‖y - x₀‖ ^ 2 := by nlinarith
        have : v y ≤ s - ε := by
          simp only [hv_def]; nlinarith [hus y]
        linarith
    have hloc : IsLocalMax v p := Filter.Eventually.of_forall hglob
    have hD2v := fun h => hloc.fderiv_fderiv_nonpos hv.contDiffAt h
    have hD1v : fderiv ℝ v p = 0 := hloc.fderiv_eq_zero
    have hu1 : Differentiable ℝ u := hu.differentiable (by norm_num)
    have hDu : Differentiable ℝ (fderiv ℝ u) :=
      (hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
    -- first and second derivatives of `v`
    have hfv : fderiv ℝ v = fun y => fderiv ℝ u y - ε • ((2 : ℝ) • innerBilin (y - x₀)) := by
      funext y
      exact ((hu1 y).hasFDerivAt.sub ((hasFDerivAt_norm_sub_sq x₀ y).const_mul ε)).fderiv
    have hD2 : fderiv ℝ (fderiv ℝ v) p =
        fderiv ℝ (fderiv ℝ u) p - ε • ((2 : ℝ) • (innerBilin : E →L[ℝ] E →L[ℝ] ℝ)) := by
      rw [hfv]
      exact ((hDu p).hasFDerivAt.sub
        ((hasFDerivAt_two_smul_innerBilin_sub x₀ p).const_smul ε)).fderiv
    have hD1 : fderiv ℝ u p = ε • ((2 : ℝ) • innerBilin (p - x₀)) := by
      have := hfv ▸ congrFun (congrArg DFunLike.coe hD1v) 0
      rw [hfv] at hD1v
      exact sub_eq_zero.mp hD1v
    -- the three terms of `L u (p)`
    have htr : hessTrace b (a p) (fderiv ℝ (fderiv ℝ u) p) ≤ 2 * ε * (Fintype.card ι * Λ) := by
      have hnp := hessTrace_nonpos b (hsymm p) (hpos p) (Q := fderiv ℝ (fderiv ℝ v) p) hD2v
      rw [hD2, hessTrace_sub_right, hessTrace_smul_right, hessTrace_smul_right] at hnp
      have hi := hessTrace_innerBilin_le b (a p)
      have : (Fintype.card ι : ℝ) * ‖a p‖ ≤ Fintype.card ι * Λ := by gcongr; exact ha p
      nlinarith
    have hpx : ‖p - x₀‖ ≤ 1 := by rw [mem_closedBall, dist_eq_norm] at hpK; exact hpK
    have hfirst : fderiv ℝ u p (β p) ≤ 2 * ε * Λ := by
      rw [hD1]
      simp only [smul_apply, innerBilin_apply, smul_eq_mul]
      have h1 : ⟪p - x₀, β p⟫ ≤ ‖p - x₀‖ * ‖β p‖ := real_inner_le_norm _ _
      have h2 : ‖p - x₀‖ * ‖β p‖ ≤ 1 * Λ :=
        mul_le_mul hpx (hβ p) (norm_nonneg _) zero_le_one
      nlinarith
    have hup : s - ε < u p := by
      have : v p ≤ u p := by simp only [hv_def]; nlinarith [sq_nonneg ‖p - x₀‖]
      linarith
    have hzero : c p * u p ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (hc p) (by linarith)
    have hLp := hF p
    simp only [ellipticOp] at hLp
    have hμu : μ * (s - ε) ≤ μ * u p := mul_le_mul_of_nonneg_left hup.le hμ.le
    rw [hK]
    nlinarith
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set ε : ℝ := min (s / 2) (δ / (K + 1)) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by positivity)
  have hεs : ε < s := (min_le_left _ _).trans_lt (by linarith)
  have hεK : ε * K ≤ δ := by
    have h1 : ε ≤ δ / (K + 1) := min_le_right _ _
    have h2 : ε * K ≤ δ / (K + 1) * K := mul_le_mul_of_nonneg_right h1 hK0
    have h3 : δ / (K + 1) * K ≤ δ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
    linarith
  linarith [hcore ε hε0 hεs]

/-- **The maximum principle for `L - μ` on the whole space**: `μ |u|_0 ≤ |L u - μ u|_0` for
bounded `C²` functions, when `a` is symmetric positive semidefinite, `‖a‖, ‖β‖ ≤ Λ` and `c ≤ 0`. -/
theorem mul_abs_le_of_ellipticOp_sub {a : E → E →L[ℝ] E} {β : E → E} {c : E → ℝ} {Λ μ F : ℝ}
    (hsymm : ∀ x v w, ⟪a x v, w⟫ = ⟪v, a x w⟫) (hpos : ∀ x v, 0 ≤ ⟪a x v, v⟫)
    (ha : ∀ x, ‖a x‖ ≤ Λ) (hβ : ∀ x, ‖β x‖ ≤ Λ) (hc : ∀ x, c x ≤ 0) (hμ : 0 < μ)
    (hu : ContDiff ℝ 2 u) (hbdd : ∃ A, ∀ x, |u x| ≤ A)
    (hF : ∀ x, |ellipticOp b a β c u x - μ * u x| ≤ F) (x : E) : μ * |u x| ≤ F := by
  obtain ⟨A, hA⟩ := hbdd
  have hF0 : 0 ≤ F := (abs_nonneg _).trans (hF 0)
  have h1 := mul_le_of_ellipticOp_sub b hsymm hpos ha hβ hc hμ hF0 hu
    ⟨A, fun y => (le_abs_self _).trans (hA y)⟩ (fun y => by
      have := neg_abs_le (ellipticOp b a β c u y - μ * u y)
      linarith [hF y]) x
  have h2 := mul_le_of_ellipticOp_sub b hsymm hpos ha hβ hc hμ hF0 (u := fun y => -u y) hu.neg
    ⟨A, fun y => (neg_le_abs _).trans (hA y)⟩ (fun y => by
      rw [ellipticOp_neg]
      have := le_abs_self (ellipticOp b a β c u y - μ * u y)
      linarith [hF y]) x
  rcases le_total 0 (u x) with h | h
  · rw [abs_of_nonneg h]; exact h1
  · rw [abs_of_nonpos h]; linarith

end MaxPrinciple

end SGPT.Foundations.Analysis.Pending.WholeSpaceMaxPrinciple
