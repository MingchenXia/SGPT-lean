import SGPT.Foundations.Analysis.Pending.HolderInterpolation
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Mollification of bounded Hölder maps

Let `E` be a finite-dimensional real normed space with an additive Haar measure `μ`, `F` a real
Banach space, `φ : E → ℝ` a nonnegative continuous integrable function with `∫ φ = 1` (a mollifier),
and `u : E → F` continuous.  For the convolution `φ ⋆ u (x) = ∫ φ(t) u(x - t) dt`
(`MeasureTheory.convolution` with `lsmul ℝ ℝ`):

* `norm_convolution_le`: `‖u‖ ≤ A` pointwise implies `‖φ ⋆ u‖ ≤ A` pointwise;
* `dist_convolution_le`: `u` `(H, r)`-Hölder implies `φ ⋆ u` `(H, r)`-Hölder (`holderWith_convolution`);
* `contDiff_convolution`: `φ ⋆ u` is `C^n` when `φ` is `C^n` with compact support;
* `hasFDerivAt_convolution_of_bounded`: if `u` is `C¹` with bounded derivative, then
  `D(φ ⋆ u) = φ ⋆ Du` (differentiation under the integral; mathlib's
  `HasCompactSupport.hasFDerivAt_convolution_right` differentiates the compactly supported factor).

* `iteratedFDeriv_convolution`: `D^j(φ ⋆ u) = φ ⋆ D^j u` for `j ≤ k` when `u` is `C^k` with bounded
  derivatives of order `≤ k`;
* `norm_convolution_sub_le`: `‖φ ⋆ u - u‖ ≤ H R^r` when `u` is `(H, r)`-Hölder and `φ` vanishes
  outside the ball of radius `R`;
* `BoundedContDiffHolderMap.mollify`: `φ ⋆ u ∈ C^{k,r}_b` for `u ∈ C^{k,r}_b` and a smooth compactly
  supported mollifier, with `‖φ ⋆ u‖ ≤ ‖u‖` (`norm_mollify_le`) and `‖D^i(φ ⋆ u) - D^i u‖ ≤ ‖u‖ R`
  (`i < k`), `‖D^k(φ ⋆ u) - D^k u‖ ≤ ‖u‖ R^r` (`norm_iteratedFDeriv_mollify_sub_le_of_lt`,
  `norm_iteratedFDeriv_mollify_sub_le`), so `φ_ε ⋆ u → u` in `C^k` with the rate `ε^r`.

So mollification does not increase the sup norm or the Hölder seminorm, and commutes with
derivatives; these are the inputs of the regularity steps of the Schauder theory (mollifying a
`C^{2,α}` solution of a constant-coefficient equation, Székelyhidi Thm 2.8,
`szekelyhidi-extremal:page-0046`, and Corollary 2.2, `page-0041`).

Part L2.2 of the linear track for Yau's theorem.
-/

noncomputable section

open Set Filter Topology Metric MeasureTheory
open scoped NNReal Convolution ContDiff

namespace SGPT.Foundations.Analysis.Pending.HolderMollification

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ E]
  {μ : Measure E}

/-- The integrand `t ↦ φ(t) u(x - t)` is integrable when `φ` is integrable and `u` bounded and
continuous. -/
theorem integrable_smul_comp_sub {φ : E → ℝ} (hφi : Integrable φ μ) (hφc : Continuous φ)
    {u : E → F} (hu : Continuous u) {A : ℝ} (hA : ∀ y, ‖u y‖ ≤ A) (x : E) :
    Integrable (fun t => φ t • u (x - t)) μ := by
  refine (hφi.norm.mul_const A).mono' ?_ (Eventually.of_forall fun t => ?_)
  · exact (hφc.smul (hu.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hA _) (norm_nonneg _)

/-- **Mollification does not increase the sup norm.** -/
theorem norm_convolution_le {φ : E → ℝ} (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ μ)
    (hφ1 : ∫ t, φ t ∂μ = 1) {u : E → F} {A : ℝ} (hA : ∀ y, ‖u y‖ ≤ A) (x : E) :
    ‖(φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) x‖ ≤ A := by
  rw [convolution_lsmul]
  calc ‖∫ t, φ t • u (x - t) ∂μ‖ ≤ ∫ t, φ t * A ∂μ := by
        refine norm_integral_le_of_norm_le (hφi.mul_const A) (Eventually.of_forall fun t => ?_)
        rw [norm_smul, Real.norm_of_nonneg (hφ0 t)]
        exact mul_le_mul_of_nonneg_left (hA _) (hφ0 t)
    _ = A := by rw [integral_mul_const, hφ1, one_mul]

/-- **Mollification does not increase the Hölder seminorm.** -/
theorem dist_convolution_le {φ : E → ℝ} (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ μ)
    (hφc : Continuous φ) (hφ1 : ∫ t, φ t ∂μ = 1) {u : E → F} (hu : Continuous u) {A : ℝ}
    (hA : ∀ y, ‖u y‖ ≤ A) {H r : ℝ≥0} (hH : HolderWith H r u) (x x' : E) :
    dist ((φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) x) ((φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) x')
      ≤ H * dist x x' ^ (r : ℝ) := by
  rw [convolution_lsmul, convolution_lsmul, dist_eq_norm,
    ← integral_sub (integrable_smul_comp_sub hφi hφc hu hA x)
      (integrable_smul_comp_sub hφi hφc hu hA x')]
  calc ‖∫ t, (φ t • u (x - t) - φ t • u (x' - t)) ∂μ‖
      ≤ ∫ t, φ t * (H * dist x x' ^ (r : ℝ)) ∂μ := by
        refine norm_integral_le_of_norm_le (hφi.mul_const _) (Eventually.of_forall fun t => ?_)
        rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hφ0 t), ← dist_eq_norm]
        refine mul_le_mul_of_nonneg_left ?_ (hφ0 t)
        have h := hH.dist_le (x - t) (x' - t)
        rwa [dist_sub_right] at h
    _ = H * dist x x' ^ (r : ℝ) := by rw [integral_mul_const, hφ1, one_mul]

/-- The Hölder statement of `dist_convolution_le`. -/
theorem holderWith_convolution {φ : E → ℝ} (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ μ)
    (hφc : Continuous φ) (hφ1 : ∫ t, φ t ∂μ = 1) {u : E → F} (hu : Continuous u) {A : ℝ}
    (hA : ∀ y, ‖u y‖ ≤ A) {H r : ℝ≥0} (hH : HolderWith H r u) :
    HolderWith H r (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) :=
  HolderWith.of_dist_le fun x x' => dist_convolution_le hφ0 hφi hφc hφ1 hu hA hH x x'

variable [μ.IsAddHaarMeasure]

/-- **Mollifications are smooth**: `φ ⋆ u` is `C^n` when `φ` is `C^n` with compact support and `u`
is locally integrable. -/
theorem contDiff_convolution {n : ℕ∞} {φ : E → ℝ} (hφc : HasCompactSupport φ)
    (hφ : ContDiff ℝ n φ) {u : E → F} (hu : LocallyIntegrable u μ) [μ.IsNegInvariant] :
    ContDiff ℝ n (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) :=
  hφc.contDiff_convolution_left _ hφ hu

omit [μ.IsAddHaarMeasure] in
/-- **Mollification commutes with differentiation**: if `u` is `C¹` with `‖Du‖ ≤ B`, then
`D(φ ⋆ u)(x) = (φ ⋆ Du)(x)`. -/
theorem hasFDerivAt_convolution_of_bounded {φ : E → ℝ} (hφi : Integrable φ μ)
    (hφc : Continuous φ) {u : E → F} (hu : ContDiff ℝ 1 u) {A : ℝ} (hA : ∀ y, ‖u y‖ ≤ A)
    {B : ℝ} (hB : ∀ y, ‖fderiv ℝ u y‖ ≤ B) (x₀ : E) :
    HasFDerivAt (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u)
      ((φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] fderiv ℝ u) x₀) x₀ := by
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hDc : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  have hfun : (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) = fun x => ∫ t, φ t • u (x - t) ∂μ := by
    funext x; rw [convolution_lsmul]
  rw [hfun, convolution_lsmul]
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ)
    (F' := fun x t => φ t • fderiv ℝ u (x - t)) (bound := fun t => ‖φ t‖ * B)
    univ_mem (Eventually.of_forall fun x => ?_) ?_ ?_ ?_ ?_ ?_
  · exact (hφc.smul (hu.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · exact integrable_smul_comp_sub hφi hφc hu.continuous hA x₀
  · exact (hφc.smul (hDc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · refine Eventually.of_forall fun t x _ => ?_
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
  · exact hφi.norm.mul_const B
  · refine Eventually.of_forall fun t x _ => ?_
    have h1 : HasFDerivAt (fun x => u (x - t)) (fderiv ℝ u (x - t)) x := by
      have := (hud (x - t)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const t)
      rwa [ContinuousLinearMap.comp_id] at this
    exact h1.const_smul (φ t)

omit [μ.IsAddHaarMeasure] in
/-- Convolution commutes with a linear isometric equivalence applied to the values. -/
theorem convolution_comp_linearIsometryEquiv {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F ≃ₗᵢ[ℝ] G) (φ : E → ℝ) (u : E → F) (x : E) :
    (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] fun y => L (u y)) x =
      L ((φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) x) := by
  rw [convolution_lsmul, convolution_lsmul]
  calc ∫ t, φ t • L (u (x - t)) ∂μ = ∫ t, L.toContinuousLinearEquiv (φ t • u (x - t)) ∂μ := by
        congr 1
        funext t
        exact (L.map_smul (φ t) (u (x - t))).symm
    _ = L (∫ t, φ t • u (x - t) ∂μ) := L.toContinuousLinearEquiv.integral_comp_comm _

omit [μ.IsAddHaarMeasure] in
/-- **Mollification commutes with all derivatives**: if `u` is `C^k` with bounded derivatives of
order `≤ k`, then `D^j(φ ⋆ u) = φ ⋆ D^j u` for every `j ≤ k`. -/
theorem iteratedFDeriv_convolution {φ : E → ℝ} (hφi : Integrable φ μ) (hφc : Continuous φ)
    {k : ℕ} {u : E → F} (hu : ContDiff ℝ k u)
    (hb : ∀ i ≤ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ i u x‖ ≤ C) :
    ∀ j ≤ k, iteratedFDeriv ℝ j (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) =
      φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] iteratedFDeriv ℝ j u := by
  intro j
  induction j with
  | zero =>
    intro _
    funext x
    rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply, iteratedFDeriv_zero_eq_comp]
    exact (convolution_comp_linearIsometryEquiv _ φ u x).symm
  | succ j ih =>
    intro hj
    have hjk : j ≤ k := by omega
    obtain ⟨A, hA⟩ := hb j hjk
    obtain ⟨B, hB⟩ := hb (j + 1) hj
    have hg : ContDiff ℝ 1 (iteratedFDeriv ℝ j u) :=
      hu.iteratedFDeriv_right (by exact_mod_cast (show 1 + j ≤ k by omega))
    funext x
    have h := hasFDerivAt_convolution_of_bounded (μ := μ) hφi hφc hg hA
      (fun y => by rw [norm_fderiv_iteratedFDeriv]; exact hB y) x
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih hjk, h.fderiv,
      iteratedFDeriv_succ_eq_comp_left]
    exact (convolution_comp_linearIsometryEquiv
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F).symm φ
      (fderiv ℝ (iteratedFDeriv ℝ j u)) x).symm

omit [μ.IsAddHaarMeasure] in
/-- **Mollification converges with a rate**: if `u` is `(H, r)`-Hölder and the mollifier `φ` is
supported in the closed ball of radius `R`, then `‖φ ⋆ u - u‖ ≤ H R^r`. -/
theorem norm_convolution_sub_le {φ : E → ℝ} (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ μ)
    (hφc : Continuous φ) (hφ1 : ∫ t, φ t ∂μ = 1) {R : ℝ}
    (hφR : ∀ t, R < ‖t‖ → φ t = 0) {u : E → F} (hu : Continuous u) {A : ℝ}
    (hA : ∀ y, ‖u y‖ ≤ A) {H r : ℝ≥0} (hH : HolderWith H r u) (x : E) :
    ‖(φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) x - u x‖ ≤ H * R ^ (r : ℝ) := by
  have hux : u x = ∫ t, φ t • u x ∂μ := by rw [integral_smul_const, hφ1, one_smul]
  rw [convolution_lsmul, hux, ← integral_sub (integrable_smul_comp_sub hφi hφc hu hA x)
    (hφi.smul_const _)]
  calc ‖∫ t, (φ t • u (x - t) - φ t • u x) ∂μ‖ ≤ ∫ t, φ t * (H * R ^ (r : ℝ)) ∂μ := by
        refine norm_integral_le_of_norm_le (hφi.mul_const _) (Eventually.of_forall fun t => ?_)
        rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hφ0 t)]
        by_cases ht : R < ‖t‖
        · rw [hφR t ht, zero_mul, zero_mul]
        · refine mul_le_mul_of_nonneg_left ?_ (hφ0 t)
          have h := hH.dist_le (x - t) x
          rw [dist_eq_norm, dist_eq_norm, sub_sub_cancel_left, norm_neg] at h
          refine h.trans (mul_le_mul_of_nonneg_left ?_ H.2)
          exact Real.rpow_le_rpow (norm_nonneg t) (not_lt.1 ht) r.2
    _ = H * R ^ (r : ℝ) := by rw [integral_mul_const, hφ1, one_mul]

/-! ### Mollification in `C^{k,r}_b` -/

namespace BoundedContDiffHolderMap

open SGPT.Foundations.Analysis.Pending.BoundedContDiffHolderMap

variable {k : ℕ} {r : ℝ≥0} [μ.IsNegInvariant] {φ : E → ℝ}

/-- The mollification `φ ⋆ u` of `u ∈ C^{k,r}_b(E, F)` by a nonnegative smooth compactly supported
`φ` with `∫ φ = 1`. -/
def mollify (hφ0 : ∀ t, 0 ≤ φ t) (hφc : HasCompactSupport φ) (hφs : ContDiff ℝ ∞ φ)
    (hφ1 : ∫ t, φ t ∂μ = 1) (u : BoundedContDiffHolderMap k r E F) :
    BoundedContDiffHolderMap k r E F where
  toFun := φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u
  contDiff' := (contDiff_convolution hφc hφs (u.contDiff.continuous.locallyIntegrable)).of_le
    (by exact_mod_cast le_top)
  bounded' i hi := by
    obtain ⟨C, hC⟩ := u.bounded hi
    refine ⟨C, fun x => ?_⟩
    rw [iteratedFDeriv_convolution (hφs.continuous.integrable_of_hasCompactSupport hφc)
      hφs.continuous u.contDiff (fun j hj => u.bounded hj) i hi]
    exact norm_convolution_le hφ0 (hφs.continuous.integrable_of_hasCompactSupport hφc) hφ1 hC x
  memHolder' := by
    obtain ⟨C, hC⟩ := u.bounded le_rfl
    rw [iteratedFDeriv_convolution (hφs.continuous.integrable_of_hasCompactSupport hφc)
      hφs.continuous u.contDiff (fun j hj => u.bounded hj) k le_rfl]
    exact (holderWith_convolution hφ0 (hφs.continuous.integrable_of_hasCompactSupport hφc)
      hφs.continuous hφ1 (u.continuous_iteratedFDeriv le_rfl) hC
      u.memHolder.holderWith).memHolder

variable (hφ0 : ∀ t, 0 ≤ φ t) (hφc : HasCompactSupport φ) (hφs : ContDiff ℝ ∞ φ)
  (hφ1 : ∫ t, φ t ∂μ = 1)

@[simp]
theorem coe_mollify (u : BoundedContDiffHolderMap k r E F) :
    ⇑(mollify hφ0 hφc hφs hφ1 u) = φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u :=
  rfl

/-- `D^i(φ ⋆ u) = φ ⋆ D^i u` for `u ∈ C^{k,r}_b` and `i ≤ k`. -/
theorem iteratedFDeriv_mollify (u : BoundedContDiffHolderMap k r E F) {i : ℕ} (hi : i ≤ k) :
    iteratedFDeriv ℝ i (mollify hφ0 hφc hφs hφ1 u) =
      φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] iteratedFDeriv ℝ i u :=
  iteratedFDeriv_convolution (hφs.continuous.integrable_of_hasCompactSupport hφc) hφs.continuous
    u.contDiff (fun _ hj => u.bounded hj) i hi

/-- **Mollification does not increase the `C^{k,r}_b` norm.** -/
theorem norm_mollify_le (u : BoundedContDiffHolderMap k r E F) :
    ‖mollify hφ0 hφc hφs hφ1 u‖ ≤ ‖u‖ := by
  have hφi : Integrable φ μ := hφs.continuous.integrable_of_hasCompactSupport hφc
  have hBCF : ∀ i ≤ k, ‖(mollify hφ0 hφc hφs hφ1 u).iteratedFDerivBCF i‖ ≤
      ‖u.iteratedFDerivBCF i‖ := by
    intro i hi
    refine (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun x => ?_
    rw [coe_iteratedFDerivBCF _ hi, iteratedFDeriv_mollify hφ0 hφc hφs hφ1 u hi]
    refine norm_convolution_le hφ0 hφi hφ1 (fun y => ?_) x
    rw [← u.coe_iteratedFDerivBCF hi]
    exact (u.iteratedFDerivBCF i).norm_coe_le_norm y
  rw [norm_def, norm_def]
  refine add_le_add (Finset.sum_le_sum fun i hi => hBCF i (Finset.mem_range.1 hi).le) ?_
  rw [BoundedHolderMap.norm_def, BoundedHolderMap.norm_def]
  refine add_le_add (hBCF k le_rfl) ?_
  have hH := u.iteratedFDerivHolder.holderWith
  rw [coe_iteratedFDerivHolder] at hH
  obtain ⟨C, hC⟩ := u.bounded le_rfl
  have h := holderWith_convolution hφ0 hφi hφs.continuous hφ1
    (u.continuous_iteratedFDeriv le_rfl) hC hH
  rw [← iteratedFDeriv_mollify hφ0 hφc hφs hφ1 u le_rfl,
    ← coe_iteratedFDerivHolder (mollify hφ0 hφc hφs hφ1 u)] at h
  rw [coe_iteratedFDerivHolder u]
  exact_mod_cast h.nnholderNorm_le

/-- **Convergence of the derivatives below the top order**: if `φ` vanishes outside the ball of
radius `R`, then `‖D^i(φ ⋆ u) - D^i u‖ ≤ ‖u‖ R` for `i < k` (`D^i u` is `‖u‖`-Lipschitz). -/
theorem norm_iteratedFDeriv_mollify_sub_le_of_lt {R : ℝ} (hφR : ∀ t, R < ‖t‖ → φ t = 0)
    (u : BoundedContDiffHolderMap k r E F) {i : ℕ} (hi : i < k) (x : E) :
    ‖iteratedFDeriv ℝ i (mollify hφ0 hφc hφs hφ1 u) x - iteratedFDeriv ℝ i u x‖ ≤ ‖u‖ * R := by
  have hφi : Integrable φ μ := hφs.continuous.integrable_of_hasCompactSupport hφc
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ i u) :=
    (u.contDiff.iteratedFDeriv_right (m := 1) (by exact_mod_cast (show 1 + i ≤ k by omega))).differentiable
      one_ne_zero
  have hL : LipschitzWith ‖u‖₊ (iteratedFDeriv ℝ i u) := by
    refine lipschitzWith_of_nnnorm_fderiv_le hdiff fun y => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, norm_fderiv_iteratedFDeriv]
    exact u.norm_iteratedFDeriv_apply_le hi y
  obtain ⟨C, hC⟩ := u.bounded hi.le
  rw [iteratedFDeriv_mollify hφ0 hφc hφs hφ1 u hi.le]
  have h := norm_convolution_sub_le hφ0 hφi hφs.continuous hφ1 hφR
    (u.continuous_iteratedFDeriv hi.le) hC hL.holderWith x
  simpa only [NNReal.coe_one, Real.rpow_one, coe_nnnorm] using h

/-- **Convergence of the top derivative**: `‖D^k(φ ⋆ u) - D^k u‖ ≤ ‖u‖ R^r` if `φ` vanishes
outside the ball of radius `R`. -/
theorem norm_iteratedFDeriv_mollify_sub_le {R : ℝ} (hR : 0 ≤ R) (hφR : ∀ t, R < ‖t‖ → φ t = 0)
    (u : BoundedContDiffHolderMap k r E F) (x : E) :
    ‖iteratedFDeriv ℝ k (mollify hφ0 hφc hφs hφ1 u) x - iteratedFDeriv ℝ k u x‖ ≤
      ‖u‖ * R ^ (r : ℝ) := by
  have hφi : Integrable φ μ := hφs.continuous.integrable_of_hasCompactSupport hφc
  have hH := u.iteratedFDerivHolder.holderWith
  rw [coe_iteratedFDerivHolder] at hH
  obtain ⟨C, hC⟩ := u.bounded le_rfl
  rw [iteratedFDeriv_mollify hφ0 hφc hφs hφ1 u le_rfl]
  refine (norm_convolution_sub_le hφ0 hφi hφs.continuous hφ1 hφR
    (u.continuous_iteratedFDeriv le_rfl) hC hH x).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hR _)
  have h := u.iteratedFDerivHolder.nnHolderNorm_le_norm.trans u.norm_iteratedFDerivHolder_le
  rwa [coe_iteratedFDerivHolder] at h

end BoundedContDiffHolderMap

end SGPT.Foundations.Analysis.Pending.HolderMollification
