import SGPT.Foundations.Analysis.Pending.HolderGerm
import SGPT.Foundations.Analysis.Pending.ManifoldSchauder

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Regularity by difference quotients: one derivative more from uniform Schauder bounds

Let `E` be a finite-dimensional real inner product space with an orthonormal basis `b`, `0 < r < 1`,
`w ∈ C^{2,r}_b(E)` and `θ` a smooth compactly supported cut-off.  For a direction `ζ` and `h > 0` let
`D_h w (x) = (w (x + h ζ) - w x) / h` (`diffQuot`).

**Main result** `exists_mul_fderiv_mem` (the difference-quotient argument, Gilbarg--Trudinger §6.4,
Székelyhidi §2.2 for the Schauder input): suppose that for all small `h > 0` the difference quotient
solves an elliptic equation `a_h : D²(D_h w) = g_h` on `tsupport θ`, with `a_h` in the Schauder class
`IsEllipticCoeff (a h) λ Λ r` and `|g_h| ≤ M`, `[g_h]_r ≤ M`, **uniformly in `h`**.  Then
`θ · ∂_ζ w ∈ C^{2,r}_b(E)`; in particular `∂_ζ w` is `C^{2,r}` where `θ = 1`.

Proof.  `V_h = θ · D_h w` lies in `C^{2,r}_b`.  By the product rule (`ManifoldSchauder.ellipticOp_mul_eq`)
`a_h : D²V_h = θ g_h + R_h`, where the remainder `R_h` only involves `D_h w` and `D(D_h w) = D_h(Dw)`,
which are bounded and `r`-Hölder uniformly in `h` because `w ∈ C^{2,r}_b` (mean value theorem,
`norm_diffQuot_le`, `norm_diffQuot_sub_le`).  The whole-space Schauder estimate
(`SchauderWholeSpace.exists_schauder_estimate`) bounds `‖V_h‖_{C^{2,r}_b}` uniformly; along `h_j → 0`
a subsequence converges in `C^{2,s}_b` (`s < r`, all `V_h` vanish off the compact `tsupport θ`,
`BoundedContDiffHolderMap.exists_subseq_tendsto_ofLE`), the limit is `θ ∂_ζ w` (pointwise limit of the
difference quotients), and the uniform `r`-Hölder bound of `D²V_h` passes to the limit.

Consumers: the linear regularity step and the first (nonlinear) step of the regularity bootstrap for
the Monge–Ampère equation `ma A ψ = tF + εψ` (TN.4 B5, plan
the proof of Yau's theorem, P2).
-/

noncomputable section

open Set Filter Topology Metric Function
open scoped NNReal ContDiff RealInnerProductSpace

namespace SGPT.Foundations.Analysis.Pending.DifferenceQuotient

open EllipticMeanValue SchauderBlowup SchauderWholeSpace ManifoldSchauder WholeSpaceSolvability

/-! ### Difference quotients -/

section Generic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The difference quotient `D_h^ζ w (x) = (w (x + h ζ) - w x) / h`. -/
def diffQuot (w : E → F) (ζ : E) (h : ℝ) (x : E) : F :=
  h⁻¹ • (w (x + h • ζ) - w x)

/-- `|D_h w| ≤ sup ‖Dw‖ ‖ζ‖` (mean value theorem). -/
theorem norm_diffQuot_le {w : E → F} (hw : Differentiable ℝ w) {B : ℝ}
    (hB : ∀ x, ‖fderiv ℝ w x‖ ≤ B) (ζ : E) {h : ℝ} (hh : h ≠ 0) (x : E) :
    ‖diffQuot w ζ h x‖ ≤ B * ‖ζ‖ := by
  have hm := (convex_univ : Convex ℝ (univ : Set E)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hw z) (fun z _ => hB z) (mem_univ x) (mem_univ (x + h • ζ))
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at hm
  have hpos : 0 < |h| := abs_pos.mpr hh
  rw [diffQuot, norm_smul, norm_inv, Real.norm_eq_abs, inv_mul_le_iff₀ hpos]
  calc ‖w (x + h • ζ) - w x‖ ≤ B * (|h| * ‖ζ‖) := hm
    _ = |h| * (B * ‖ζ‖) := by ring

/-- `[D_h w]_r ≤ [Dw]_r ‖ζ‖` (mean value theorem for `t ↦ w (x + t) - w (y + t)`). -/
theorem norm_diffQuot_sub_le {w : E → F} (hw : Differentiable ℝ w) {H r : ℝ}
    (hH : ∀ x y, ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ H * ‖x - y‖ ^ r) (ζ : E) {h : ℝ} (hh : h ≠ 0)
    (x y : E) : ‖diffQuot w ζ h x - diffQuot w ζ h y‖ ≤ H * ‖x - y‖ ^ r * ‖ζ‖ := by
  set g : E → F := fun t => w (x + t) - w (y + t) with hg
  have hgd : ∀ t ∈ (univ : Set E),
      HasFDerivWithinAt g (fderiv ℝ w (x + t) - fderiv ℝ w (y + t)) univ t := by
    intro t _
    have h1 : HasFDerivAt (fun t => w (x + t)) (fderiv ℝ w (x + t)) t :=
      (hasFDerivAt_comp_add_left x).mpr (hw (x + t)).hasFDerivAt
    have h2 : HasFDerivAt (fun t => w (y + t)) (fderiv ℝ w (y + t)) t :=
      (hasFDerivAt_comp_add_left y).mpr (hw (y + t)).hasFDerivAt
    exact (h1.sub h2).hasFDerivWithinAt
  have hb : ∀ t ∈ (univ : Set E), ‖fderiv ℝ w (x + t) - fderiv ℝ w (y + t)‖ ≤ H * ‖x - y‖ ^ r :=
    fun t _ => by simpa using hH (x + t) (y + t)
  have hm := (convex_univ : Convex ℝ (univ : Set E)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hgd hb (mem_univ 0) (mem_univ (h • ζ))
  rw [sub_zero, norm_smul, Real.norm_eq_abs] at hm
  have hpos : 0 < |h| := abs_pos.mpr hh
  have heq : diffQuot w ζ h x - diffQuot w ζ h y = h⁻¹ • (g (h • ζ) - g 0) := by
    simp only [diffQuot, hg, add_zero, smul_sub]
    rw [add_comm x, add_comm y]
    abel
  rw [heq, norm_smul, norm_inv, Real.norm_eq_abs, inv_mul_le_iff₀ hpos]
  calc ‖g (h • ζ) - g 0‖ ≤ H * ‖x - y‖ ^ r * (|h| * ‖ζ‖) := hm
    _ = |h| * (H * ‖x - y‖ ^ r * ‖ζ‖) := by ring

/-- The difference quotients converge to the directional derivative. -/
theorem tendsto_diffQuot {w : E → F} {x : E} (hw : DifferentiableAt ℝ w x) (ζ : E) :
    Tendsto (fun h => diffQuot w ζ h x) (𝓝[≠] 0) (𝓝 (fderiv ℝ w x ζ)) := by
  have hl : HasDerivAt (fun t : ℝ => x + t • ζ) ζ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ζ).const_add x
  have hd := hw.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have := hd.tendsto_slope_zero
  simpa [diffQuot, comp_apply] using this

/-- `D (D_h w) = D_h (D w)`. -/
theorem fderiv_diffQuot {w : E → F} (hw : Differentiable ℝ w) (ζ : E) (h : ℝ) :
    fderiv ℝ (diffQuot w ζ h) = diffQuot (fderiv ℝ w) ζ h := by
  funext x
  have h1 : HasFDerivAt (fun y => w (y + h • ζ)) (fderiv ℝ w (x + h • ζ)) x :=
    (hasFDerivAt_comp_add_right (h • ζ)).mpr (hw _).hasFDerivAt
  exact ((h1.sub (hw x).hasFDerivAt).const_smul h⁻¹).fderiv

theorem differentiable_diffQuot {w : E → F} (hw : Differentiable ℝ w) (ζ : E) (h : ℝ) :
    Differentiable ℝ (diffQuot w ζ h) := fun x =>
  (((hasFDerivAt_comp_add_right (h • ζ)).mpr (hw _).hasFDerivAt).sub
    (hw x).hasFDerivAt).const_smul h⁻¹ |>.differentiableAt

end Generic

/-! ### Translates and difference quotients in `C^{k,r}_b` -/

section HolderSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {k : ℕ} {r : ℝ≥0}

/-- The translate `x ↦ w (x + c)` of `w ∈ C^{k,r}_b`. -/
def translate (w : BoundedContDiffHolderMap k r E F) (c : E) : BoundedContDiffHolderMap k r E F where
  toFun x := w (x + c)
  contDiff' := w.contDiff.comp (contDiff_id.add contDiff_const)
  bounded' i hi := by
    obtain ⟨C, hC⟩ := w.bounded hi
    exact ⟨C, fun x => by rw [iteratedFDeriv_comp_add_right]; exact hC _⟩
  memHolder' := by
    refine ⟨nnHolderNorm r (iteratedFDeriv ℝ k w), fun x y => ?_⟩
    rw [iteratedFDeriv_comp_add_right']
    have := w.memHolder.holderWith (x + c) (y + c)
    simpa only [edist_add_right] using this

@[simp]
theorem coe_translate (w : BoundedContDiffHolderMap k r E F) (c : E) :
    ⇑(translate w c) = fun x => w (x + c) :=
  rfl

/-- The difference quotient of `w ∈ C^{k,r}_b`, as an element of `C^{k,r}_b`. -/
def diffQuotMap (w : BoundedContDiffHolderMap k r E F) (ζ : E) (h : ℝ) :
    BoundedContDiffHolderMap k r E F :=
  h⁻¹ • (translate w (h • ζ) - w)

@[simp]
theorem coe_diffQuotMap (w : BoundedContDiffHolderMap k r E F) (ζ : E) (h : ℝ) :
    ⇑(diffQuotMap w ζ h) = diffQuot (⇑w) ζ h := by
  funext x
  simp [diffQuotMap, diffQuot]

end HolderSpace

/-! ### The remainder of the product rule, with Hölder bounds on `v` and `Dv` -/

section Remainder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)

/-- `[R]_r ≤ 17 d Λ K S` for the remainder `R = v (a : D²χ) + a : (Dχ ⊗ Dv + Dv ⊗ Dχ)` when `v` and
`Dv` are bounded by `S` and `(3S, r)`-, resp. `(S, r)`-Hölder, `a` is bounded by `Λ` and
`(Λ, r)`-Hölder, and `χ` has `Dχ`, `D²χ` bounded by `K` and `K`-Lipschitz. -/
theorem abs_remainder_sub_le' {r Λ K S : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (a : E → E →L[ℝ] E)
    {χ v : E → ℝ} (hab : ∀ x, ‖a x‖ ≤ Λ) (hah : ∀ x y, ‖a x - a y‖ ≤ Λ * ‖x - y‖ ^ r)
    (h1 : ∀ x, ‖fderiv ℝ χ x‖ ≤ K) (h2 : ∀ x, ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ K)
    (h1L : ∀ x y, ‖fderiv ℝ χ x - fderiv ℝ χ y‖ ≤ K * ‖x - y‖)
    (h2L : ∀ x y, ‖fderiv ℝ (fderiv ℝ χ) x - fderiv ℝ (fderiv ℝ χ) y‖ ≤ K * ‖x - y‖)
    (hvb : ∀ x, |v x| ≤ S) (hvh : ∀ x y, |v x - v y| ≤ 3 * S * ‖x - y‖ ^ r)
    (hDvb : ∀ x, ‖fderiv ℝ v x‖ ≤ S) (hDvh : ∀ x y, ‖fderiv ℝ v x - fderiv ℝ v y‖ ≤ S * ‖x - y‖ ^ r)
    (x y : E) :
    |remainder b a (fun _ => 0) χ v x - remainder b a (fun _ => 0) χ v y| ≤
      17 * Fintype.card ι * Λ * K * S * ‖x - y‖ ^ r := by
  set d : ℝ := (Fintype.card ι : ℝ) with hd
  set p := ‖x - y‖ ^ r with hp
  have hp0 : 0 ≤ p := Real.rpow_nonneg (norm_nonneg _) _
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans (hab 0)
  have hK : 0 ≤ K := (norm_nonneg _).trans (h1 0)
  have hS : 0 ≤ S := (abs_nonneg _).trans (hvb 0)
  have hDχh : ‖fderiv ℝ χ x - fderiv ℝ χ y‖ ≤ 3 * K * p := by
    have := norm_sub_le_rpow_of_lipschitz_of_bound (Y := E →L[ℝ] ℝ) hK hr0 hr1 h1L h1 x y
    linarith
  have hD2χh : ‖fderiv ℝ (fderiv ℝ χ) x - fderiv ℝ (fderiv ℝ χ) y‖ ≤ 3 * K * p := by
    have := norm_sub_le_rpow_of_lipschitz_of_bound (Y := E →L[ℝ] E →L[ℝ] ℝ) hK hr0 hr1 h2L h2 x y
    linarith
  -- the zeroth-order coefficient `P = a : D²χ`
  have hPb : ∀ z, |hessTrace b (a z) (fderiv ℝ (fderiv ℝ χ) z) + fderiv ℝ χ z 0| ≤ d * Λ * K := by
    intro z
    rw [map_zero, add_zero]
    refine (abs_hessTrace_le b _ _).trans ?_
    have := mul_le_mul (hab z) (h2 z) (ContinuousLinearMap.opNorm_nonneg _) hΛ
    rw [← hd, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left this hd0
  have hPh : |(hessTrace b (a x) (fderiv ℝ (fderiv ℝ χ) x) + fderiv ℝ χ x 0) -
      (hessTrace b (a y) (fderiv ℝ (fderiv ℝ χ) y) + fderiv ℝ χ y 0)| ≤ 4 * d * Λ * K * p := by
    simp only [map_zero, add_zero]
    refine (abs_hessTrace_sub_le b _ _ _ _).trans ?_
    have f1 : ‖a x - a y‖ * ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ Λ * p * K :=
      mul_le_mul (hah x y) (h2 x) (ContinuousLinearMap.opNorm_nonneg _) (by positivity)
    have f2 : ‖a y‖ * ‖fderiv ℝ (fderiv ℝ χ) x - fderiv ℝ (fderiv ℝ χ) y‖ ≤ Λ * (3 * K * p) :=
      mul_le_mul (hab y) hD2χh (ContinuousLinearMap.opNorm_nonneg _) hΛ
    have : d * (Λ * p * K + Λ * (3 * K * p)) = 4 * d * Λ * K * p := by ring
    rw [← hd]
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add f1 f2) hd0]
  have hvP := abs_mul_sub_mul_le (hvh x y) (hPb x) (hvb y) hPh
  have hc := abs_crossTerm_sub_le b (a x) (a y) (fderiv ℝ χ x) (fderiv ℝ χ y) (fderiv ℝ v x)
    (fderiv ℝ v y) (hab x) (h1 x) (h1 y) (hDvb x) (hDvb y)
  have c1 : ‖fderiv ℝ χ x - fderiv ℝ χ y‖ * S * Λ ≤ 3 * K * p * S * Λ := by gcongr
  have c2 : K * ‖fderiv ℝ v x - fderiv ℝ v y‖ * Λ ≤ K * (S * p) * Λ := by gcongr; exact hDvh x y
  have c3 : K * S * ‖a x - a y‖ ≤ K * S * (Λ * p) := by gcongr; exact hah x y
  rw [remainder, remainder,
    show ∀ A B C D : ℝ, A + B - (C + D) = (A - C) + (B - D) from fun _ _ _ _ => by ring]
  refine (abs_add_le _ _).trans ((add_le_add hvP hc).trans ?_)
  rw [← hd]
  have e : 3 * S * p * (d * Λ * K) + S * (4 * d * Λ * K * p) +
      2 * d * (3 * K * p * S * Λ + K * (S * p) * Λ + K * S * (Λ * p)) =
      17 * d * Λ * K * S * p := by ring
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add (add_le_add c1 c2) c3)
    (by positivity : (0 : ℝ) ≤ 2 * d)]

end Remainder

/-! ### The difference-quotient argument -/

section Main

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)

theorem fderiv_fderiv_sub_map {s : ℝ≥0} (f f' : BoundedContDiffHolderMap 2 s E ℝ) (z : E) :
    fderiv ℝ (fderiv ℝ ⇑(f - f')) z = fderiv ℝ (fderiv ℝ f) z - fderiv ℝ (fderiv ℝ f') z := by
  have hf := contDiff_two f
  have hf' := contDiff_two f'
  have h1 : fderiv ℝ ⇑(f - f') = fun x => fderiv ℝ f x - fderiv ℝ f' x := by
    funext x
    rw [BoundedContDiffHolderMap.coe_sub]
    exact fderiv_sub ((hf.differentiable (by simp)) x) ((hf'.differentiable (by simp)) x)
  rw [h1]
  exact fderiv_sub (((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) z)
    (((hf'.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) z)

/-- **The difference-quotient argument.**  If for all `0 < h ≤ h₀` the difference quotient `D_h w` of
`w ∈ C^{2,r}_b` solves `a_h : D²(D_h w) = g_h` on `tsupport θ`, with `a_h` in the Schauder class and
`g_h` bounded and `r`-Hölder uniformly in `h`, then `θ · ∂_ζ w ∈ C^{2,r}_b`. -/
theorem exists_mul_fderiv_mem {lam Λ M : ℝ} {r : ℝ≥0} (hlam : 0 < lam) (hr0 : 0 < r)
    (hr1 : r < 1) (w : BoundedContDiffHolderMap 2 r E ℝ) {θ : E → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hθc : HasCompactSupport θ) (ζ : E) {h₀ : ℝ} (hh₀ : 0 < h₀) (a : ℝ → E → E →L[ℝ] E)
    (g : ℝ → E → ℝ) (ha : ∀ h, 0 < h → h ≤ h₀ → IsEllipticCoeff (a h) lam Λ r)
    (hgb : ∀ h, 0 < h → h ≤ h₀ → ∀ x, |g h x| ≤ M)
    (hgh : ∀ h, 0 < h → h ≤ h₀ → ∀ x y, |g h x - g h y| ≤ M * ‖x - y‖ ^ (r : ℝ))
    (heq : ∀ h, 0 < h → h ≤ h₀ → ∀ x ∈ tsupport θ,
      hessTrace b (a h x) (fderiv ℝ (fderiv ℝ (diffQuot (⇑w) ζ h)) x) = g h x) :
    ∃ W : BoundedContDiffHolderMap 2 r E ℝ, ∀ x, W x = θ x * fderiv ℝ w x ζ := by
  have hr1' : r ≤ 1 := hr1.le
  have hrr0 : (0 : ℝ) ≤ r := r.coe_nonneg
  have hrr1 : (r : ℝ) ≤ 1 := by exact_mod_cast hr1'
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans ((ha h₀ hh₀ le_rfl).bound 0)
  have hM : 0 ≤ M := (abs_nonneg _).trans (hgb h₀ hh₀ le_rfl 0)
  -- bounds for the cut-off
  have h4 : ContDiff ℝ (4 : ℕ) θ := contDiff_infty.1 hθ 4
  obtain ⟨K₀, hK₀0, hK₀b, hK₀l⟩ :=
    HolderGerm.exists_lipschitz_of_hasCompactSupport (h4.of_le (by norm_num)) hθc
  obtain ⟨-, K₁, K₂, K₃, -, hK₃0, -, hK₁b, hK₂b, hK₁l, hK₂l⟩ :=
    exists_bounds_of_hasCompactSupport hθ hθc
  have hK₁0 : 0 ≤ K₁ := (norm_nonneg _).trans (hK₁b 0)
  have hK₂0 : 0 ≤ K₂ := (ContinuousLinearMap.opNorm_nonneg _).trans (hK₂b 0)
  set K : ℝ := K₀ + K₁ + K₂ + K₃ with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hθb : ∀ x, |θ x| ≤ K := fun x => by
    rw [← Real.norm_eq_abs]; exact (hK₀b x).trans (by linarith)
  have hθh : ∀ x y, |θ x - θ y| ≤ 3 * K * ‖x - y‖ ^ (r : ℝ) := by
    intro x y
    have := norm_sub_le_rpow_of_lipschitz_of_bound (Y := ℝ) hK₀0 hrr0 hrr1 hK₀l hK₀b x y
    rw [Real.norm_eq_abs] at this
    exact this.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _))
  have h1θ : ∀ x, ‖fderiv ℝ θ x‖ ≤ K := fun x => (hK₁b x).trans (by linarith)
  have h2θ : ∀ x, ‖fderiv ℝ (fderiv ℝ θ) x‖ ≤ K := fun x => (hK₂b x).trans (by linarith)
  have h1θL : ∀ x y, ‖fderiv ℝ θ x - fderiv ℝ θ y‖ ≤ K * ‖x - y‖ := fun x y =>
    (hK₁l x y).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  have h2θL : ∀ x y, ‖fderiv ℝ (fderiv ℝ θ) x - fderiv ℝ (fderiv ℝ θ) y‖ ≤ K * ‖x - y‖ :=
    fun x y => (hK₂l x y).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  -- bounds for `w` and its difference quotients
  have hw2 : ContDiff ℝ 2 ⇑w := contDiff_two w
  have hwd : Differentiable ℝ ⇑w := hw2.differentiable (by simp)
  have hDwd : Differentiable ℝ (fderiv ℝ ⇑w) :=
    (hw2.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  set S : ℝ := ‖w‖ * ‖ζ‖ with hSdef
  have hS0 : 0 ≤ S := by positivity
  have hv : ∀ h, h ≠ 0 → (∀ x, |diffQuot (⇑w) ζ h x| ≤ S) ∧
      (∀ x y, |diffQuot (⇑w) ζ h x - diffQuot (⇑w) ζ h y| ≤ 3 * S * ‖x - y‖ ^ (r : ℝ)) ∧
      (∀ x, ‖fderiv ℝ (diffQuot (⇑w) ζ h) x‖ ≤ S) ∧
      (∀ x y, ‖fderiv ℝ (diffQuot (⇑w) ζ h) x - fderiv ℝ (diffQuot (⇑w) ζ h) y‖ ≤
        S * ‖x - y‖ ^ (r : ℝ)) := by
    intro h hh
    have hb0 : ∀ x, |diffQuot (⇑w) ζ h x| ≤ S := fun x => by
      rw [← Real.norm_eq_abs]; exact norm_diffQuot_le hwd (norm_fderiv_le w) ζ hh x
    have hb1 : ∀ x, ‖fderiv ℝ (diffQuot (⇑w) ζ h) x‖ ≤ S := fun x => by
      rw [fderiv_diffQuot hwd]; exact norm_diffQuot_le hDwd (norm_fderiv_fderiv_le w) ζ hh x
    refine ⟨hb0, fun x y => ?_, hb1, fun x y => ?_⟩
    · have hL : ∀ x y, ‖diffQuot (⇑w) ζ h x - diffQuot (⇑w) ζ h y‖ ≤ S * ‖x - y‖ := fun x y =>
        (convex_univ : Convex ℝ (univ : Set E)).norm_image_sub_le_of_norm_fderiv_le
          (fun z _ => differentiable_diffQuot hwd ζ h z) (fun z _ => hb1 z) (mem_univ y)
          (mem_univ x)
      have := norm_sub_le_rpow_of_lipschitz_of_bound (Y := ℝ) hS0 hrr0 hrr1 hL
        (fun x => by rw [Real.norm_eq_abs]; exact hb0 x) x y
      rw [Real.norm_eq_abs] at this
      linarith
    · rw [fderiv_diffQuot hwd]
      have := norm_diffQuot_sub_le hDwd (norm_fderiv_fderiv_sub_le w) ζ hh x y
      calc _ ≤ ‖w‖ * ‖x - y‖ ^ (r : ℝ) * ‖ζ‖ := this
        _ = S * ‖x - y‖ ^ (r : ℝ) := by rw [hSdef]; ring
  -- the functions `V_h = θ D_h w` in `C^{2,r}_b`
  set θ₂ : BoundedContDiffHolderMap 2 r E ℝ :=
    BoundedContDiffHolderMap.ofHasCompactSupport hr1' θ (h4.of_le (by norm_num)) hθc
  set V : ℝ → BoundedContDiffHolderMap 2 r E ℝ := fun h =>
    BoundedContDiffHolderMap.bilinear hr1' (ContinuousLinearMap.mul ℝ ℝ) θ₂ (diffQuotMap w ζ h)
    with hVdef
  have hVcoe : ∀ h, ⇑(V h) = fun x => θ x * diffQuot (⇑w) ζ h x := by
    intro h; funext x; simp [hVdef, θ₂]
  -- the uniform Hölder bound of `a_h : D²V_h`
  set d : ℝ := (Fintype.card ι : ℝ) with hd
  set M' : ℝ := 4 * K * M + 17 * d * Λ * K * S with hM'def
  have hM'0 : 0 ≤ M' := by positivity
  have hLV : ∀ h, 0 < h → h ≤ h₀ → ∀ x y,
      |ellipticOp b (a h) (fun _ => 0) (fun _ => 0) (V h) x -
        ellipticOp b (a h) (fun _ => 0) (fun _ => 0) (V h) y| ≤ M' * ‖x - y‖ ^ (r : ℝ) := by
    intro h hh hhh x y
    obtain ⟨hvb, hvh, hDvb, hDvh⟩ := hv h hh.ne'
    have hdq2 : ContDiff ℝ 2 (diffQuot (⇑w) ζ h) := by
      rw [← coe_diffQuotMap]; exact contDiff_two _
    have hθ2 : ContDiff ℝ 2 θ := h4.of_le (by norm_num)
    have hsplit : ∀ z, ellipticOp b (a h) (fun _ => 0) (fun _ => 0) (V h) z =
        θ z * g h z + remainder b (a h) (fun _ => 0) θ (diffQuot (⇑w) ζ h) z := by
      intro z
      rw [hVcoe, ellipticOp_mul_eq b _ _ _ hθ2 hdq2, ellipticOp_zero]
      congr 1
      by_cases hz : z ∈ tsupport θ
      · rw [heq h hh hhh z hz]
      · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul, zero_mul]
    rw [hsplit, hsplit,
      show ∀ A B C D : ℝ, A + B - (C + D) = (A - C) + (B - D) from fun _ _ _ _ => by ring]
    refine (abs_add_le _ _).trans ?_
    have e1 : |θ x * g h x - θ y * g h y| ≤ 3 * K * ‖x - y‖ ^ (r : ℝ) * M +
        K * (M * ‖x - y‖ ^ (r : ℝ)) :=
      abs_mul_sub_mul_le (hθh x y) (hgb h hh hhh x) (hθb y) (hgh h hh hhh x y)
    have e2 := abs_remainder_sub_le' b hrr0 hrr1 (a h) (ha h hh hhh).bound (ha h hh hhh).holder
      h1θ h2θ h1θL h2θL hvb hvh hDvb hDvh x y
    rw [← hd] at e2
    have : 3 * K * ‖x - y‖ ^ (r : ℝ) * M + K * (M * ‖x - y‖ ^ (r : ℝ)) +
        17 * d * Λ * K * S * ‖x - y‖ ^ (r : ℝ) = M' * ‖x - y‖ ^ (r : ℝ) := by
      rw [hM'def]; ring
    have hp0 : 0 ≤ ‖x - y‖ ^ (r : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
    nlinarith [mul_nonneg (mul_nonneg hK0 hM) hp0]
  -- the Schauder estimate gives a uniform `C^{2,r}_b` bound
  obtain ⟨C, hC0, hSch⟩ := exists_schauder_estimate (Λ := Λ) b hlam (by exact_mod_cast hr0)
    (by exact_mod_cast hr1)
  set A : ℝ := K * S with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hVb : ∀ h, 0 < h → ∀ x, |V h x| ≤ A := by
    intro h hh x
    rw [hVcoe, abs_mul]
    exact mul_le_mul (hθb x) ((hv h hh.ne').1 x) (abs_nonneg _) hK0
  set R : ℝ := A + 3 * (C * (M' + A)) with hRdef
  have hVn : ∀ h, 0 < h → h ≤ h₀ →
      (∀ x y, ‖fderiv ℝ (fderiv ℝ (V h)) x - fderiv ℝ (fderiv ℝ (V h)) y‖ ≤
        C * (M' + A) * ‖x - y‖ ^ (r : ℝ)) ∧ ‖V h‖ ≤ R := by
    intro h hh hhh
    obtain ⟨e1, e2, e3⟩ := hSch (a h) (fun _ => 0) (fun _ => 0) (ha h hh hhh)
      (isLowerCoeff_zero hΛ) (V h) (contDiff_two _)
      ⟨‖V h‖, norm_fderiv_fderiv_sub_le (V h)⟩ ⟨‖V h‖, norm_fderiv_fderiv_le (V h)⟩ A M' hM'0
      (hVb h hh) (hLV h hh hhh)
    refine ⟨e1, ?_⟩
    have hCMA : 0 ≤ C * (M' + A) := by positivity
    have := norm_le_of_bounds (V h) hCMA (hVb h hh) e3 e2 e1
    rw [hRdef]; linarith
  -- a sequence `h_j → 0⁺` and a convergent subsequence in `C^{2,s}_b`, `s = r/2`
  set hs : ℕ → ℝ := fun j => h₀ / (j + 2) with hsdef
  have hs0 : ∀ j, 0 < hs j := fun j => div_pos hh₀ (by positivity)
  have hsle : ∀ j, hs j ≤ h₀ := fun j => by
    rw [hsdef]; exact div_le_self hh₀.le (by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith)
  have hstend : Tendsto hs atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (Eventually.of_forall fun j => (hs0 j).ne')
    have h1 : Tendsto (fun j : ℕ => ((j : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    simpa [hsdef] using h1.const_div_atTop h₀
  set s : ℝ≥0 := r / 2 with hsr
  have hsr' : s < r := by rw [hsr]; exact NNReal.half_lt_self hr0.ne'
  have hsupp : ∀ j, ∀ x ∉ tsupport θ, V (hs j) x = 0 := by
    intro j x hx
    rw [hVcoe]
    simp [image_eq_zero_of_notMem_tsupport hx]
  obtain ⟨W', φ, hφ, hW'⟩ := BoundedContDiffHolderMap.exists_subseq_tendsto_ofLE hr1' hsr'
    hθc.isCompact (fun j => V (hs j)) hsupp (fun j => (hVn (hs j) (hs0 j) (hsle j)).2)
  -- pointwise convergence of values and second derivatives
  have hconv : ∀ x, Tendsto (fun j => V (hs (φ j)) x) atTop (𝓝 (W' x)) := by
    intro x
    have h1 := tendsto_iff_norm_sub_tendsto_zero.mp hW'
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_) h1
    have := (BoundedContDiffHolderMap.ofLE hsr'.le (V (hs (φ j))) - W').norm_apply_le x
    simpa using this
  have hconv2 : ∀ x, Tendsto (fun j => ‖fderiv ℝ (fderiv ℝ (V (hs (φ j)))) x -
      fderiv ℝ (fderiv ℝ W') x‖) atTop (𝓝 0) := by
    intro x
    have h1 := tendsto_iff_norm_sub_tendsto_zero.mp hW'
    refine squeeze_zero (fun _ => ContinuousLinearMap.opNorm_nonneg _) (fun j => ?_) h1
    have := norm_fderiv_fderiv_le (BoundedContDiffHolderMap.ofLE hsr'.le (V (hs (φ j))) - W') x
    rw [fderiv_fderiv_sub_map, BoundedContDiffHolderMap.coe_ofLE] at this
    exact this
  -- the limit is `θ ∂_ζ w`
  have hlim : ∀ x, W' x = θ x * fderiv ℝ w x ζ := by
    intro x
    have h2 : Tendsto (fun j => V (hs (φ j)) x) atTop (𝓝 (θ x * fderiv ℝ w x ζ)) := by
      have h3 := ((tendsto_diffQuot (hwd x) ζ).comp (hstend.comp hφ.tendsto_atTop)).const_mul
        (θ x)
      refine h3.congr fun j => ?_
      rw [hVcoe]
      rfl
    exact tendsto_nhds_unique (hconv x) h2
  -- the uniform `r`-Hölder bound of `D²V_h` passes to the limit
  have hH : ∀ x y, ‖fderiv ℝ (fderiv ℝ W') x - fderiv ℝ (fderiv ℝ W') y‖ ≤
      C * (M' + A) * ‖x - y‖ ^ (r : ℝ) := by
    intro x y
    set p : ℝ := C * (M' + A) * ‖x - y‖ ^ (r : ℝ) with hp
    have hT : Tendsto (fun j => p + (‖fderiv ℝ (fderiv ℝ (V (hs (φ j)))) x -
        fderiv ℝ (fderiv ℝ W') x‖ + ‖fderiv ℝ (fderiv ℝ (V (hs (φ j)))) y -
        fderiv ℝ (fderiv ℝ W') y‖)) atTop (𝓝 (p + (0 + 0))) :=
      tendsto_const_nhds.add ((hconv2 x).add (hconv2 y))
    rw [add_zero, add_zero] at hT
    refine ge_of_tendsto hT (Eventually.of_forall fun j => ?_)
    have hj := (hVn (hs (φ j)) (hs0 _) (hsle _)).1 x y
    set P := fderiv ℝ (fderiv ℝ (V (hs (φ j)))) x
    set Q := fderiv ℝ (fderiv ℝ (V (hs (φ j)))) y
    set P' := fderiv ℝ (fderiv ℝ W') x
    set Q' := fderiv ℝ (fderiv ℝ W') y
    have e : P' - Q' = (P - Q) - (P - P') + (Q - Q') := by abel
    calc ‖P' - Q'‖ = ‖(P - Q) - (P - P') + (Q - Q')‖ := by rw [e]
      _ ≤ ‖P - Q‖ + ‖P - P'‖ + ‖Q - Q'‖ := by
          have h1 := norm_add_le (P - Q - (P - P')) (Q - Q')
          have h2 := norm_sub_le (P - Q) (P - P')
          linarith
      _ ≤ p + (‖P - P'‖ + ‖Q - Q'‖) := by rw [hp]; linarith
  refine ⟨ofBounds (r := r) (⇑W') (contDiff_two W') (abs_apply_le W') (norm_fderiv_le W')
    (norm_fderiv_fderiv_le W') hH, fun x => ?_⟩
  rw [coe_ofBounds, hlim]

end Main

end SGPT.Foundations.Analysis.Pending.DifferenceQuotient
