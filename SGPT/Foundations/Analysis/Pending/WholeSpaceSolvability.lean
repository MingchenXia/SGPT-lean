import SGPT.Foundations.Analysis.Pending.HelmholtzHolder
import SGPT.Foundations.Analysis.Pending.MethodOfContinuity

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Solvability of `L u - μ u = f` on the whole space

Let `E` be a finite-dimensional real inner product space with an orthonormal basis `b`,
`0 < α < 1`, `μ > 0`, and `L u = a : D²u + Du(β) + c u` (`SchauderWholeSpace.ellipticOp`) with
`a ∈ IsEllipticCoeff a λ Λ α`, `(β, c) ∈ IsLowerCoeff β c Λ α` and `c ≤ 0`.  For every bounded
`α`-Hölder `f` there is a bounded `C²` function `u` with bounded `α`-Hölder second derivative such
that `L u - μ u = f` (`exists_ellipticOp_sub_eq`).

Proof: in the Banach space `X = C^{2,α}_b(E)` (`BoundedContDiffHolderMap 2 α E ℝ`) and the normed
space `Y = C^{0,α}_b(E)` (`BoundedHolderMap α E ℝ`) the operators `L_t u = ellipticOp` with the
coefficients `(1 - t) 1 + t a`, `t β`, `t c - μ` are bounded linear maps `X → Y` (`opY`), uniformly
estimated by `‖u‖_X ≤ C ‖L_t u‖_Y` for `t ∈ [0, 1]` (the Schauder estimate
`SchauderWholeSpace.exists_schauder_estimate` and the maximum principle
`WholeSpaceMaxPrinciple.mul_abs_le_of_ellipticOp_sub`, uniform over the class with constants
`(min 1 λ, Λ + 1 + μ, α)`); `L₀ = Δ - μ` is onto (`HelmholtzHolder.exists_laplacian_sub_eq_of_holder`),
so `L₁ = L - μ` is onto by the method of continuity (`MethodOfContinuity.surjective_of_continuity`).

TN.4 B5 linear track L2.10; the
whole-space step of the parametrix in blueprint `bou:kahler-laplacian-solvability`.
-/

noncomputable section

open Set Filter Topology Metric
open scoped NNReal RealInnerProductSpace

namespace SGPT.Foundations.Analysis.Pending.WholeSpaceSolvability

open EllipticMeanValue SchauderBlowup SchauderWholeSpace WholeSpaceMaxPrinciple HelmholtzHolder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Bridges between `C^{2,r}_b`, `C^{0,r}_b` and pointwise bounds -/

section Bridges

variable {r : ℝ≥0}

theorem contDiff_two (u : BoundedContDiffHolderMap 2 r E ℝ) : ContDiff ℝ 2 ⇑u := by
  exact_mod_cast u.contDiff

theorem abs_apply_le (u : BoundedContDiffHolderMap 2 r E ℝ) (x : E) : |u x| ≤ ‖u‖ := by
  rw [← Real.norm_eq_abs]; exact u.norm_apply_le x

theorem norm_fderiv_le (u : BoundedContDiffHolderMap 2 r E ℝ) (x : E) :
    ‖fderiv ℝ u x‖ ≤ ‖u‖ := by
  rw [← norm_iteratedFDeriv_one]; exact u.norm_iteratedFDeriv_apply_le (by norm_num) x

theorem norm_fderiv_fderiv_le (u : BoundedContDiffHolderMap 2 r E ℝ) (x : E) :
    ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ ‖u‖ := by
  rw [← HolderInterpolation.norm_iteratedFDeriv_two]; exact u.norm_iteratedFDeriv_apply_le le_rfl x

theorem norm_fderiv_fderiv_sub_le (u : BoundedContDiffHolderMap 2 r E ℝ) (x y : E) :
    ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ ‖u‖ * ‖x - y‖ ^ (r : ℝ) := by
  rw [← HolderInterpolation.norm_iteratedFDeriv_two_sub]
  have h := u.iteratedFDerivHolder.holderWith.dist_le x y
  rw [BoundedContDiffHolderMap.coe_iteratedFDerivHolder, dist_eq_norm, dist_eq_norm] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) _))
  exact u.iteratedFDerivHolder.nnHolderNorm_le_norm.trans u.norm_iteratedFDerivHolder_le

/-- An upper bound for the `C^{2,r}_b` norm from pointwise bounds. -/
theorem norm_le_of_bounds (u : BoundedContDiffHolderMap 2 r E ℝ) {A B₁ B₂ H : ℝ} (hH0 : 0 ≤ H)
    (h0 : ∀ x, |u x| ≤ A) (h1 : ∀ x, ‖fderiv ℝ u x‖ ≤ B₁)
    (h2 : ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ B₂)
    (hH : ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H * ‖x - y‖ ^ (r : ℝ)) :
    ‖u‖ ≤ A + B₁ + B₂ + H := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (h0 0)
  have hB₁ : 0 ≤ B₁ := (norm_nonneg _).trans (h1 0)
  have hB₂ : 0 ≤ B₂ := (ContinuousLinearMap.opNorm_nonneg _).trans (h2 0)
  have e0 : ‖u.iteratedFDerivBCF 0‖ ≤ A := by
    refine (BoundedContinuousFunction.norm_le hA0).2 fun x => ?_
    rw [u.coe_iteratedFDerivBCF (by norm_num), norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    exact h0 x
  have e1 : ‖u.iteratedFDerivBCF 1‖ ≤ B₁ := by
    refine (BoundedContinuousFunction.norm_le hB₁).2 fun x => ?_
    rw [u.coe_iteratedFDerivBCF (by norm_num), norm_iteratedFDeriv_one]
    exact h1 x
  have e2 : ‖u.iteratedFDerivHolder‖ ≤ B₂ + H := by
    have hHol : HolderWith H.toNNReal r (u.iteratedFDerivHolder) :=
      HolderWith.of_dist_le fun x y => by
        rw [BoundedContDiffHolderMap.coe_iteratedFDerivHolder, Real.coe_toNNReal _ hH0,
          dist_eq_norm, dist_eq_norm, HolderInterpolation.norm_iteratedFDeriv_two_sub]
        exact hH x y
    refine (u.iteratedFDerivHolder.norm_le_of_holderWith hHol).trans ?_
    rw [Real.coe_toNNReal _ hH0]
    gcongr
    refine (BoundedContinuousFunction.norm_le hB₂).2 fun x => ?_
    rw [BoundedContDiffHolderMap.iteratedFDerivHolder_toBoundedContinuousFunction,
      u.coe_iteratedFDerivBCF le_rfl, HolderInterpolation.norm_iteratedFDeriv_two]
    exact h2 x
  rw [BoundedContDiffHolderMap.norm_def, Finset.sum_range_succ, Finset.sum_range_one]
  linarith

/-- An element of `C^{2,r}_b` from a `C²` function with pointwise bounds. -/
def ofBounds (u : E → ℝ) (hu : ContDiff ℝ 2 u) {A B₁ B₂ H : ℝ}
    (h0 : ∀ x, |u x| ≤ A) (h1 : ∀ x, ‖fderiv ℝ u x‖ ≤ B₁)
    (h2 : ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ B₂)
    (hH : ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H * ‖x - y‖ ^ (r : ℝ)) :
    BoundedContDiffHolderMap 2 r E ℝ where
  toFun := u
  contDiff' := by exact_mod_cast hu
  bounded' i hi := by
    interval_cases i
    · exact ⟨A, fun x => by rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]; exact h0 x⟩
    · exact ⟨B₁, fun x => by rw [norm_iteratedFDeriv_one]; exact h1 x⟩
    · exact ⟨B₂, fun x => by rw [HolderInterpolation.norm_iteratedFDeriv_two]; exact h2 x⟩
  memHolder' := ⟨H.toNNReal, HolderWith.of_dist_le fun x y => by
    rw [dist_eq_norm, dist_eq_norm, HolderInterpolation.norm_iteratedFDeriv_two_sub]
    exact (hH x y).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal H)
      (Real.rpow_nonneg (norm_nonneg _) _))⟩

@[simp]
theorem coe_ofBounds (u : E → ℝ) (hu : ContDiff ℝ 2 u) {A B₁ B₂ H : ℝ} (h0 h1 h2 hH) :
    ⇑(ofBounds (r := r) u hu (A := A) (B₁ := B₁) (B₂ := B₂) (H := H) h0 h1 h2 hH) = u :=
  rfl

theorem abs_apply_le_holder (g : BoundedHolderMap r E ℝ) (x : E) : |g x| ≤ ‖g‖ := by
  rw [← Real.norm_eq_abs]; exact g.norm_apply_le x

theorem abs_sub_le_holder (g : BoundedHolderMap r E ℝ) (x y : E) :
    |g x - g y| ≤ ‖g‖ * ‖x - y‖ ^ (r : ℝ) := by
  have h := g.holderWith.dist_le x y
  rw [Real.dist_eq, dist_eq_norm] at h
  exact h.trans (mul_le_mul_of_nonneg_right g.nnHolderNorm_le_norm
    (Real.rpow_nonneg (norm_nonneg _) _))

/-- An element of `C^{0,r}_b` from a bounded `r`-Hölder function (`r > 0`). -/
def ofHolder (hr : 0 < r) (g : E → ℝ) {F M : ℝ} (hF : ∀ x, |g x| ≤ F) (hM0 : 0 ≤ M)
    (hM : ∀ x y, |g x - g y| ≤ M * ‖x - y‖ ^ (r : ℝ)) : BoundedHolderMap r E ℝ where
  toBoundedContinuousFunction := BoundedContinuousFunction.ofNormedAddCommGroup g
    (HolderWith.continuous (C := M.toNNReal) (HolderWith.of_dist_le fun x y => by
      rw [Real.coe_toNNReal _ hM0, Real.dist_eq, dist_eq_norm]; exact hM x y) hr)
    F fun x => by rw [Real.norm_eq_abs]; exact hF x
  memHolder' := ⟨M.toNNReal, HolderWith.of_dist_le fun x y => by
    change dist (g x) (g y) ≤ _
    rw [Real.coe_toNNReal _ hM0, Real.dist_eq, dist_eq_norm]; exact hM x y⟩

@[simp]
theorem coe_ofHolder (hr : 0 < r) (g : E → ℝ) {F M : ℝ} (hF hM0 hM) :
    ⇑(ofHolder hr g (F := F) (M := M) hF hM0 hM) = g :=
  rfl

theorem norm_ofHolder_le (hr : 0 < r) (g : E → ℝ) {F M : ℝ} (hF : ∀ x, |g x| ≤ F) (hM0 : 0 ≤ M)
    (hM : ∀ x y, |g x - g y| ≤ M * ‖x - y‖ ^ (r : ℝ)) :
    ‖ofHolder hr g hF hM0 hM‖ ≤ F + M := by
  have hF0 : 0 ≤ F := (abs_nonneg _).trans (hF 0)
  have hHol : HolderWith M.toNNReal r (ofHolder hr g hF hM0 hM) := HolderWith.of_dist_le
    fun x y => by rw [Real.coe_toNNReal _ hM0, Real.dist_eq, dist_eq_norm]; exact hM x y
  refine ((ofHolder hr g hF hM0 hM).norm_le_of_holderWith hHol).trans ?_
  rw [Real.coe_toNNReal _ hM0]
  gcongr
  refine (BoundedContinuousFunction.norm_le hF0).2 fun x => ?_
  rw [Real.norm_eq_abs]; exact hF x

end Bridges

/-! ### Linearity of `L` -/

section Linear

variable {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)

theorem hessTrace_add_right (A : E →L[ℝ] E) (Q Q' : E →L[ℝ] E →L[ℝ] ℝ) :
    hessTrace b A (Q + Q') = hessTrace b A Q + hessTrace b A Q' := by
  simp only [hessTrace, add_apply, Finset.sum_add_distrib]

theorem ellipticOp_add (a : E → E →L[ℝ] E) (β : E → E) (c : E → ℝ) {u v : E → ℝ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (x : E) :
    ellipticOp b a β c (u + v) x = ellipticOp b a β c u x + ellipticOp b a β c v x := by
  have hu1 : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hv1 : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hDu : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hDv : Differentiable ℝ (fderiv ℝ v) :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have h1 : fderiv ℝ (u + v) = fun y => fderiv ℝ u y + fderiv ℝ v y :=
    funext fun y => ((hu1 y).hasFDerivAt.add (hv1 y).hasFDerivAt).fderiv
  have h2 : fderiv ℝ (fderiv ℝ (u + v)) x = fderiv ℝ (fderiv ℝ u) x + fderiv ℝ (fderiv ℝ v) x := by
    rw [h1]; exact fderiv_add (hDu x) (hDv x)
  simp only [ellipticOp]
  rw [h2, h1]
  simp only [hessTrace_add_right, add_apply, Pi.add_apply]
  ring

theorem ellipticOp_smul (a : E → E →L[ℝ] E) (β : E → E) (c : E → ℝ) (k : ℝ) {u : E → ℝ}
    (hu : ContDiff ℝ 2 u) (x : E) :
    ellipticOp b a β c (k • u) x = k * ellipticOp b a β c u x := by
  have hu1 : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hDu : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have h1 : fderiv ℝ (k • u) = fun y => k • fderiv ℝ u y :=
    funext fun y => ((hu1 y).hasFDerivAt.const_smul k).fderiv
  have h2 : fderiv ℝ (fderiv ℝ (k • u)) x = k • fderiv ℝ (fderiv ℝ u) x := by
    rw [h1]; exact fderiv_const_smul (hDu x) k
  simp only [ellipticOp]
  rw [h2, h1]
  simp only [hessTrace_smul_right, smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

end Linear

/-! ### `L` as a bounded linear map `C^{2,r}_b → C^{0,r}_b` -/

section Operator

variable {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {r : ℝ≥0}

theorem abs_ellipticOp_le (a : E → E →L[ℝ] E) (β : E → E) (c : E → ℝ) {Λ : ℝ}
    (hab : ∀ x, ‖a x‖ ≤ Λ) (hβc : IsLowerCoeff β c Λ r) (u : BoundedContDiffHolderMap 2 r E ℝ)
    (x : E) : |ellipticOp b a β c u x| ≤ (Fintype.card ι + 2) * Λ * ‖u‖ := by
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans (hab 0)
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg u
  have h1 := abs_hessTrace_le b (a x) (fderiv ℝ (fderiv ℝ u) x)
  have h2 : |fderiv ℝ u x (β x)| ≤ ‖u‖ * Λ := by
    rw [← Real.norm_eq_abs]
    exact ((fderiv ℝ u x).le_opNorm _).trans
      (mul_le_mul (norm_fderiv_le u x) (hβc.bound_β x) (norm_nonneg _) hu0)
  have h3 : |c x * u x| ≤ Λ * ‖u‖ := by
    rw [abs_mul]; exact mul_le_mul (hβc.bound_c x) (abs_apply_le u x) (abs_nonneg _) hΛ
  have h4 : (Fintype.card ι : ℝ) * ‖a x‖ * ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ Fintype.card ι * Λ * ‖u‖ := by
    gcongr
    · exact hab x
    · exact norm_fderiv_fderiv_le u x
  calc |ellipticOp b a β c u x| ≤ |hessTrace b (a x) (fderiv ℝ (fderiv ℝ u) x)| +
        |fderiv ℝ u x (β x)| + |c x * u x| := abs_add_three _ _ _
    _ ≤ (Fintype.card ι + 2) * Λ * ‖u‖ := by nlinarith

theorem abs_ellipticOp_sub_le (hr1 : r ≤ 1) (a : E → E →L[ℝ] E) (β : E → E) (c : E → ℝ) {Λ : ℝ}
    (hab : ∀ x, ‖a x‖ ≤ Λ) (hah : ∀ x y, ‖a x - a y‖ ≤ Λ * ‖x - y‖ ^ (r : ℝ))
    (hβc : IsLowerCoeff β c Λ r) (u : BoundedContDiffHolderMap 2 r E ℝ) (x y : E) :
    |ellipticOp b a β c u x - ellipticOp b a β c u y| ≤
      (2 * Fintype.card ι + 16) * Λ * ‖u‖ * ‖x - y‖ ^ (r : ℝ) := by
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans (hab 0)
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg u
  have hp : 0 ≤ ‖x - y‖ ^ (r : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  set Qx := fderiv ℝ (fderiv ℝ u) x
  set Qy := fderiv ℝ (fderiv ℝ u) y
  have htop : |hessTrace b (a x) Qx - hessTrace b (a y) Qy| ≤
      2 * Fintype.card ι * Λ * ‖u‖ * ‖x - y‖ ^ (r : ℝ) := by
    have e : hessTrace b (a x) Qx - hessTrace b (a y) Qy =
        hessTrace b (a x - a y) Qx + hessTrace b (a y) (Qx - Qy) := by
      rw [hessTrace_sub_left, hessTrace_sub_right]; ring
    rw [e]
    have h1 := abs_hessTrace_le b (a x - a y) Qx
    have h2 := abs_hessTrace_le b (a y) (Qx - Qy)
    have h3 : (Fintype.card ι : ℝ) * ‖a x - a y‖ * ‖Qx‖ ≤
        Fintype.card ι * (Λ * ‖x - y‖ ^ (r : ℝ)) * ‖u‖ := by
      gcongr
      · exact hah x y
      · exact norm_fderiv_fderiv_le u x
    have h4 : (Fintype.card ι : ℝ) * ‖a y‖ * ‖Qx - Qy‖ ≤
        Fintype.card ι * Λ * (‖u‖ * ‖x - y‖ ^ (r : ℝ)) := by
      gcongr
      · exact hab y
      · exact norm_fderiv_fderiv_sub_le u x y
    calc _ ≤ |hessTrace b (a x - a y) Qx| + |hessTrace b (a y) (Qx - Qy)| := abs_add_le _ _
      _ ≤ _ := by nlinarith
  have hlow := abs_lowerOrder_sub_le (contDiff_two u) (by positivity) (by exact_mod_cast hr1)
    hβc (abs_apply_le u) (norm_fderiv_fderiv_le u) x y
  have e : ellipticOp b a β c u x - ellipticOp b a β c u y =
      (hessTrace b (a x) Qx - hessTrace b (a y) Qy) +
        ((fderiv ℝ u x (β x) + c x * u x) - (fderiv ℝ u y (β y) + c y * u y)) := by
    simp only [ellipticOp, Qx, Qy]; ring
  rw [e]
  calc _ ≤ |hessTrace b (a x) Qx - hessTrace b (a y) Qy| +
        |(fderiv ℝ u x (β x) + c x * u x) - (fderiv ℝ u y (β y) + c y * u y)| := abs_add_le _ _
    _ ≤ 2 * Fintype.card ι * Λ * ‖u‖ * ‖x - y‖ ^ (r : ℝ) +
        Λ * (11 * ‖u‖ + 5 * ‖u‖) * ‖x - y‖ ^ (r : ℝ) := add_le_add htop hlow
    _ = (2 * Fintype.card ι + 16) * Λ * ‖u‖ * ‖x - y‖ ^ (r : ℝ) := by ring

/-- The operator `L` as a linear map `C^{2,r}_b(E) → C^{0,r}_b(E)`. -/
def opY (hr : 0 < r) (hr1 : r ≤ 1) (a : E → E →L[ℝ] E) (β : E → E) (c : E → ℝ) {Λ : ℝ}
    (hab : ∀ x, ‖a x‖ ≤ Λ) (hah : ∀ x y, ‖a x - a y‖ ≤ Λ * ‖x - y‖ ^ (r : ℝ))
    (hβc : IsLowerCoeff β c Λ r) :
    BoundedContDiffHolderMap 2 r E ℝ →ₗ[ℝ] BoundedHolderMap r E ℝ where
  toFun u := ofHolder hr (ellipticOp b a β c u) (abs_ellipticOp_le b a β c hab hβc u)
    (mul_nonneg (mul_nonneg (by positivity) ((norm_nonneg _).trans (hab 0))) (norm_nonneg u))
    (abs_ellipticOp_sub_le b hr1 a β c hab hah hβc u)
  map_add' u v := BoundedHolderMap.ext fun x => by
    simp only [coe_ofHolder, BoundedHolderMap.coe_add, Pi.add_apply,
      BoundedContDiffHolderMap.coe_add]
    exact ellipticOp_add b a β c (contDiff_two u) (contDiff_two v) x
  map_smul' k u := BoundedHolderMap.ext fun x => by
    simp only [coe_ofHolder, BoundedHolderMap.coe_smul, Pi.smul_apply, smul_eq_mul,
      BoundedContDiffHolderMap.coe_smul, RingHom.id_apply]
    exact ellipticOp_smul b a β c k (contDiff_two u) x

theorem coe_opY (hr : 0 < r) (hr1 : r ≤ 1) (a : E → E →L[ℝ] E) (β : E → E) (c : E → ℝ) {Λ : ℝ}
    (hab hah) (hβc : IsLowerCoeff β c Λ r) (u : BoundedContDiffHolderMap 2 r E ℝ) :
    ⇑(opY b hr hr1 a β c hab hah hβc u) = ellipticOp b a β c u :=
  rfl

theorem norm_opY_le (hr : 0 < r) (hr1 : r ≤ 1) (a : E → E →L[ℝ] E) (β : E → E) (c : E → ℝ)
    {Λ : ℝ} (hab hah) (hβc : IsLowerCoeff β c Λ r) (u : BoundedContDiffHolderMap 2 r E ℝ) :
    ‖opY b hr hr1 a β c hab hah hβc u‖ ≤ (3 * Fintype.card ι + 18) * Λ * ‖u‖ := by
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans (hab 0)
  have h := norm_ofHolder_le hr (ellipticOp b a β c u) (abs_ellipticOp_le b a β c hab hβc u)
    (mul_nonneg (mul_nonneg (by positivity) hΛ) (norm_nonneg u))
    (abs_ellipticOp_sub_le b hr1 a β c hab hah hβc u)
  refine h.trans (le_of_eq ?_)
  ring

end Operator

/-! ### Solvability -/

section Solvability

variable {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)

theorem hessTrace_combo (t : ℝ) (A : E →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] ℝ) :
    hessTrace b ((1 - t) • ContinuousLinearMap.id ℝ E + t • A) Q =
      (1 - t) * hessTrace b (ContinuousLinearMap.id ℝ E) Q + t * hessTrace b A Q := by
  simp only [hessTrace, add_apply, smul_apply, ContinuousLinearMap.id_apply, map_add, map_smul,
    smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum]

/-- **`L u - μ u = f` is solvable on the whole space** (`μ > 0`, `c ≤ 0`): for every bounded
`α`-Hölder `f` there is a bounded `C²` function `u` with bounded `α`-Hölder second derivative and
`a : D²u + Du(β) + c u - μ u = f`. -/
theorem exists_ellipticOp_sub_eq [MeasurableSpace E] [BorelSpace E] {lam Λ α : ℝ} (hlam : 0 < lam)
    (hα0 : 0 < α) (hα1 : α < 1) {a : E → E →L[ℝ] E} {β : E → E} {c : E → ℝ}
    (ha : IsEllipticCoeff a lam Λ α) (hβc : IsLowerCoeff β c Λ α) (hc : ∀ x, c x ≤ 0) {μ : ℝ}
    (hμ : 0 < μ) {f : E → ℝ} {F M : ℝ} (hM0 : 0 ≤ M) (hF : ∀ x, |f x| ≤ F)
    (hM : ∀ x y, |f x - f y| ≤ M * ‖x - y‖ ^ α) :
    ∃ u : E → ℝ, ContDiff ℝ 2 u ∧
      (∃ H : ℝ, ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H * ‖x - y‖ ^ α) ∧
      (∃ B : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ B) ∧ (∃ A : ℝ, ∀ x, |u x| ≤ A) ∧
      ∀ x, ellipticOp b a β c u x - μ * u x = f x := by
  set r : ℝ≥0 := ⟨α, hα0.le⟩ with hr_def
  have hr : 0 < r := hα0
  have hr1 : r ≤ 1 := by rw [← NNReal.coe_le_coe]; exact hα1.le
  have hrα : (r : ℝ) = α := rfl
  have hΛ : 0 ≤ Λ := nonneg_of_isEllipticCoeff ha
  set Λ₁ : ℝ := Λ + 1 + μ with hΛ₁
  have hΛ₁0 : 0 ≤ Λ₁ := by positivity
  have hpα : ∀ x y : E, 0 ≤ ‖x - y‖ ^ α := fun x y => Real.rpow_nonneg (norm_nonneg _) _
  -- the two end operators
  have hb0 : ∀ x : E, ‖(ContinuousLinearMap.id ℝ E : E →L[ℝ] E)‖ ≤ Λ₁ := fun _ =>
    ContinuousLinearMap.norm_id_le.trans (by linarith)
  have hh0 : ∀ x y : E, ‖(ContinuousLinearMap.id ℝ E : E →L[ℝ] E) -
      ContinuousLinearMap.id ℝ E‖ ≤ Λ₁ * ‖x - y‖ ^ (r : ℝ) := fun x y => by
    rw [sub_self, norm_zero]; exact mul_nonneg hΛ₁0 (hpα x y)
  have hl0 : IsLowerCoeff (fun _ : E => (0 : E)) (fun _ => -μ) Λ₁ (r : ℝ) := by
    refine ⟨fun _ => ?_, fun x y => ?_, fun _ => ?_, fun x y => ?_⟩
    · simp; linarith
    · simp only [sub_self, norm_zero]; exact mul_nonneg hΛ₁0 (hpα x y)
    · rw [abs_neg, abs_of_pos hμ]; linarith
    · simp only [sub_self, abs_zero]; exact mul_nonneg hΛ₁0 (hpα x y)
  have hb1 : ∀ x, ‖a x‖ ≤ Λ₁ := fun x => (ha.bound x).trans (by linarith)
  have hh1 : ∀ x y, ‖a x - a y‖ ≤ Λ₁ * ‖x - y‖ ^ (r : ℝ) := fun x y =>
    (ha.holder x y).trans (mul_le_mul_of_nonneg_right (by linarith) (hpα x y))
  have hl1 : IsLowerCoeff β (fun x => c x - μ) Λ₁ (r : ℝ) := by
    refine ⟨fun x => (hβc.bound_β x).trans (by linarith), fun x y => ?_, fun x => ?_,
      fun x y => ?_⟩
    · exact (hβc.holder_β x y).trans (mul_le_mul_of_nonneg_right (by linarith) (hpα x y))
    · calc |c x - μ| ≤ |c x| + |μ| := abs_sub _ _
        _ ≤ Λ₁ := by rw [abs_of_pos hμ]; linarith [hβc.bound_c x]
    · rw [show c x - μ - (c y - μ) = c x - c y by ring]
      exact (hβc.holder_c x y).trans (mul_le_mul_of_nonneg_right (by linarith) (hpα x y))
  set T₀ := opY b hr hr1 (fun _ => ContinuousLinearMap.id ℝ E) (fun _ => 0) (fun _ => -μ)
    hb0 hh0 hl0 with hT₀
  set T₁ := opY b hr hr1 a β (fun x => c x - μ) hb1 hh1 hl1 with hT₁
  -- the interpolated operators
  have hTt : ∀ t : ℝ, ∀ u : BoundedContDiffHolderMap 2 r E ℝ, ∀ x,
      (T₀ u + t • (T₁ u - T₀ u)) x =
        ellipticOp b (fun x => (1 - t) • ContinuousLinearMap.id ℝ E + t • a x)
          (fun x => t • β x) (fun x => t * c x) u x - μ * u x := by
    intro t u x
    simp only [BoundedHolderMap.coe_add, BoundedHolderMap.coe_smul, BoundedHolderMap.coe_sub,
      Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hT₀, hT₁, coe_opY, ellipticOp,
      hessTrace_combo]
    simp only [map_smul, smul_eq_mul, map_zero]
    ring
  -- the uniform estimate
  set lam₁ : ℝ := min 1 lam with hlam₁
  have hlam₁0 : 0 < lam₁ := lt_min one_pos hlam
  obtain ⟨C₀, hC₀, hS⟩ := exists_schauder_estimate (Λ := Λ₁) b hlam₁0 hα0 hα1
  have hclass : ∀ t ∈ Icc (0 : ℝ) 1,
      IsEllipticCoeff (fun x => (1 - t) • ContinuousLinearMap.id ℝ E + t • a x) lam₁ Λ₁ α ∧
      IsLowerCoeff (fun x => t • β x) (fun x => t * c x - μ) Λ₁ α := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    refine ⟨⟨fun x u v => ?_, fun x v => ?_, fun x => ?_, fun x y => ?_⟩,
      ⟨fun x => ?_, fun x y => ?_, fun x => ?_, fun x y => ?_⟩⟩
    · simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply, inner_add_left,
        inner_add_right, inner_smul_left, inner_smul_right, ha.symm x u v]
      simp
    · simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply, inner_add_left,
        inner_smul_left, real_inner_self_eq_norm_sq]
      have h1 := ha.elliptic x v
      have h2 : lam₁ ≤ 1 := min_le_left _ _
      have h3 : lam₁ ≤ lam := min_le_right _ _
      simp only [RCLike.conj_to_real]
      have e1 : (1 - t) * (lam₁ * ‖v‖ ^ 2) ≤ (1 - t) * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg ‖v‖]) (by linarith)
      have e2 : t * (lam₁ * ‖v‖ ^ 2) ≤ t * ⟪a x v, v⟫ :=
        mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_right h3 (sq_nonneg _)) h1) ht0
      nlinarith
    · calc ‖(1 - t) • ContinuousLinearMap.id ℝ E + t • a x‖
          ≤ ‖(1 - t) • ContinuousLinearMap.id ℝ E‖ + ‖t • a x‖ := norm_add_le _ _
        _ ≤ (1 - t) * 1 + t * Λ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg ht0]
            gcongr
            · exact ContinuousLinearMap.norm_id_le
            · exact ha.bound x
        _ ≤ Λ₁ := by nlinarith
    · rw [show (1 - t) • ContinuousLinearMap.id ℝ E + t • a x -
          ((1 - t) • ContinuousLinearMap.id ℝ E + t • a y) = t • (a x - a y) by
          rw [smul_sub]; abel, norm_smul, Real.norm_of_nonneg ht0]
      calc t * ‖a x - a y‖ ≤ 1 * (Λ * ‖x - y‖ ^ α) :=
            mul_le_mul ht1 (ha.holder x y) (norm_nonneg _) zero_le_one
        _ ≤ Λ₁ * ‖x - y‖ ^ α := by
            rw [one_mul]; exact mul_le_mul_of_nonneg_right (by linarith) (hpα x y)
    · rw [norm_smul, Real.norm_of_nonneg ht0]
      calc t * ‖β x‖ ≤ 1 * Λ := mul_le_mul ht1 (hβc.bound_β x) (norm_nonneg _) zero_le_one
        _ ≤ Λ₁ := by linarith
    · rw [← smul_sub, norm_smul, Real.norm_of_nonneg ht0]
      calc t * ‖β x - β y‖ ≤ 1 * (Λ * ‖x - y‖ ^ α) :=
            mul_le_mul ht1 (hβc.holder_β x y) (norm_nonneg _) zero_le_one
        _ ≤ Λ₁ * ‖x - y‖ ^ α := by
            rw [one_mul]; exact mul_le_mul_of_nonneg_right (by linarith) (hpα x y)
    · calc |t * c x - μ| ≤ |t * c x| + |μ| := abs_sub _ _
        _ ≤ 1 * Λ + μ := by
            rw [abs_mul, abs_of_nonneg ht0, abs_of_pos hμ]
            gcongr
            exact hβc.bound_c x
        _ ≤ Λ₁ := by linarith
    · rw [show t * c x - μ - (t * c y - μ) = t * (c x - c y) by ring, abs_mul,
        abs_of_nonneg ht0]
      calc t * |c x - c y| ≤ 1 * (Λ * ‖x - y‖ ^ α) :=
            mul_le_mul ht1 (hβc.holder_c x y) (abs_nonneg _) zero_le_one
        _ ≤ Λ₁ * ‖x - y‖ ^ α := by
            rw [one_mul]; exact mul_le_mul_of_nonneg_right (by linarith) (hpα x y)
  set C : ℝ := 1 / μ + 3 * C₀ * (1 + 1 / μ) with hC
  have hC0 : 0 ≤ C := by positivity
  have hest : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u, ‖u‖ ≤ C * ‖T₀ u + t • (T₁ u - T₀ u)‖ := by
    intro t ht u
    obtain ⟨hat, hlt⟩ := hclass t ht
    set g := T₀ u + t • (T₁ u - T₀ u) with hg
    set G := ‖g‖ with hG
    have hG0 : 0 ≤ G := norm_nonneg _
    have hgx : ∀ x, ellipticOp b (fun x => (1 - t) • ContinuousLinearMap.id ℝ E + t • a x)
        (fun x => t • β x) (fun x => t * c x - μ) u x = g x := fun x => by
      rw [hTt]; simp only [ellipticOp]; ring
    -- the maximum principle
    have hmax : ∀ x, μ * |u x| ≤ G := by
      intro x
      refine mul_abs_le_of_ellipticOp_sub b hat.symm (fun x v => le_trans
          (mul_nonneg hlam₁0.le (sq_nonneg ‖v‖)) (hat.elliptic x v)) hat.bound hlt.bound_β
        (fun x => mul_nonpos_of_nonneg_of_nonpos ht.1 (hc x)) hμ (contDiff_two u)
        ⟨‖u‖, abs_apply_le u⟩ (fun y => ?_) x
      rw [← hTt]; exact abs_apply_le_holder g y
    have hA : ∀ x, |u x| ≤ G / μ := fun x => by
      rw [le_div_iff₀ hμ, mul_comm]; exact hmax x
    obtain ⟨h1, h2, h3⟩ := hS _ _ _ hat hlt u (contDiff_two u)
      ⟨‖u‖, norm_fderiv_fderiv_sub_le u⟩ ⟨‖u‖, norm_fderiv_fderiv_le u⟩ (G / μ) G hG0 hA
      (fun x y => by rw [hgx, hgx]; exact abs_sub_le_holder g x y)
    have hb := norm_le_of_bounds u (by positivity) hA h3 h2 h1
    calc ‖u‖ ≤ G / μ + C₀ * (G + G / μ) + C₀ * (G + G / μ) + C₀ * (G + G / μ) := hb
      _ = C * G := by rw [hC]; ring
  -- `T₀ = Δ - μ` is onto
  have hsurj0 : Function.Surjective T₀ := by
    intro g
    obtain ⟨u, hu2, ⟨H, hH⟩, ⟨B, hB⟩, hμu, hueq⟩ :=
      exists_laplacian_sub_eq_of_holder b hα0 hα1 hμ (f := g) (norm_nonneg g)
        (abs_apply_le_holder g) (abs_sub_le_holder g)
    have hA : ∀ x, |u x| ≤ ‖g‖ / μ := fun x => by
      rw [le_div_iff₀ hμ, mul_comm]; exact hμu x
    have hH0 : ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤
        |H| * ‖x - y‖ ^ (r : ℝ) := fun x y =>
      (hH x y).trans (mul_le_mul_of_nonneg_right (le_abs_self H) (hpα x y))
    refine ⟨ofBounds u hu2 hA (norm_fderiv_le_two_mul_add hu2 hA hB) hB hH0, ?_⟩
    ext x
    rw [hT₀, coe_opY, coe_ofBounds, ellipticOp_id_const, ← hueq x]
    ring
  have hK : ∀ u, ‖T₁ u - T₀ u‖ ≤ (2 * ((3 * Fintype.card ι + 18) * Λ₁)) * ‖u‖ := fun u => by
    have e1 := norm_opY_le b hr hr1 a β (fun x => c x - μ) hb1 hh1 hl1 u
    have e0 := norm_opY_le b hr hr1 (fun _ => ContinuousLinearMap.id ℝ E) (fun _ => 0)
      (fun _ => -μ) hb0 hh0 hl0 u
    calc ‖T₁ u - T₀ u‖ ≤ ‖T₁ u‖ + ‖T₀ u‖ := norm_sub_le _ _
      _ ≤ _ := by rw [hT₀, hT₁]; linarith
  have hsurj1 := MethodOfContinuity.surjective_of_continuity T₀ T₁ hC0 (by positivity) hK hest
    hsurj0
  -- solve with the data `f`
  obtain ⟨u, hu⟩ := hsurj1 (ofHolder hr f hF hM0 hM)
  refine ⟨u, contDiff_two u, ⟨‖u‖, norm_fderiv_fderiv_sub_le u⟩, ⟨‖u‖, norm_fderiv_fderiv_le u⟩,
    ⟨‖u‖, abs_apply_le u⟩, fun x => ?_⟩
  have h : (T₁ u) x = (ofHolder hr f hF hM0 hM) x := by rw [hu]
  change ellipticOp b a β (fun x => c x - μ) u x = f x at h
  simp only [ellipticOp] at h ⊢
  linarith

end Solvability

end SGPT.Foundations.Analysis.Pending.WholeSpaceSolvability
