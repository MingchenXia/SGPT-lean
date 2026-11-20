import SGPT.Foundations.Analysis.Pending.ManifoldMaxPrinciple
import SGPT.Foundations.Analysis.Pending.SchauderWeighted

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The large-parameter parametrix: `L - μ` is onto `C^{0,r}(M)` for `μ` large

Let `A` be a Hölder atlas of a compact complex manifold `M`, `b` an orthonormal basis of the real
inner product space `E = ComplexModel n`, `0 < r < 1`, and `L` an operator given chartwise: in the
chart `e_i` it reads `L_i v = a_i : D²v + Dv(β_i) + c_i v` (`SchauderWholeSpace.ellipticOp`) on an
open set `U_i` with `e_i(tsupport χ_i) ⊆ U_i ⊆ target(e_i)`, the coefficients lying on the whole space in
the Schauder class `(λ, Λ, r)` with `c_i ≤ 0`; and `L` is *realizable*: every `u ∈ C^{2,r}(M)` has a
function `g` on `M` with `g ∘ e_i⁻¹ = L_i (u ∘ e_i⁻¹)` on every `U_i` (this is the compatibility of the
chart data; for the Kähler Laplacian it is its chart independence).

`exists_ellipticOp_sub_eq_of_large` (blueprint `bou:kahler-laplacian-solvability`, first step of
(2)): there is `μ₀ ≥ 1` such that for every `μ ≥ μ₀` and `f ∈ C^{0,r}(M)` there is `u ∈ C^{2,r}(M)`
with `L u - μ u = f`.

Proof (a parametrix, no Sobolev spaces).  For `h ∈ C^{0,r}(M)` let `w_a = (L_a - μ)⁻¹ h_a`, `h_a = (χ_a h) ∘ e_a⁻¹`,
the whole-space solution (`WholeSpaceSolvability.exists_ellipticOp_sub_eq`, unique by the maximum
principle), `ψ_a` a cut-off equal to `1` near `e_a(tsupport χ_a)` with compact support in `U_a`, and
`P h = ∑_a push_a(ψ_a w_a)` (`HolderAtlas.HolderMap.exists_pushforward`).  By realizability and
locality, `L(push_a(ψ_a w_a)) = push_a(L_a(ψ_a w_a))`, and the product rule gives
`L_a(ψ_a w_a) = h_a + μ ψ_a w_a + R_a` with the first-order remainder `R_a`
(`ManifoldSchauder.remainder`); so `(L - μ) P h = h + R h`, `R h = ∑_a push_a R_a`.  The weighted
estimate (`SchauderWeighted.exists_weighted_estimate`) at `μ = t²` bounds `sup|w_a|`, `[w_a]_r`,
`sup|Dw_a|`, `[Dw_a]_r` by `C t^{r-1} ‖h‖`, hence `‖R h‖ ≤ C' t^{r-1} ‖h‖ ≤ ‖h‖ / 2` for `t` large; `R` is
additive, so `h ↦ f - R h` is a contraction of the Banach space `C^{0,r}(M)`, and its fixed point `h`
gives `u = P h`.

TN.4 B5 linear track L4(a') (the linear elliptic estimates §4,
the elliptic estimates).
-/

noncomputable section

open Set Filter Topology Metric Function
open scoped NNReal ContDiff RealInnerProductSpace Manifold

namespace SGPT.Foundations.Analysis.Pending.ManifoldParametrix

open FirstPass EllipticMeanValue SchauderBlowup SchauderWholeSpace WholeSpaceMaxPrinciple
  ManifoldSchauder

/-! ### On the whole space -/

section WholeSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {r : ℝ≥0}

/-- An element of `C^{0,r}_b` from a bounded `r`-Hölder function (`0 < r`). -/
def ofHolderZero (hr : 0 < r) (g : E → ℝ) {F M : ℝ} (hF : ∀ x, |g x| ≤ F) (hM0 : 0 ≤ M)
    (hM : ∀ x y, |g x - g y| ≤ M * ‖x - y‖ ^ (r : ℝ)) : BoundedContDiffHolderMap 0 r E ℝ where
  toFun := g
  contDiff' := contDiff_zero.2 (HolderWith.continuous (C := M.toNNReal) (HolderWith.of_dist_le
    fun x y => by rw [Real.coe_toNNReal _ hM0, Real.dist_eq, dist_eq_norm]; exact hM x y) hr)
  bounded' i hi := ⟨F, fun x => by
    obtain rfl : i = 0 := Nat.le_zero.1 hi
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]; exact hF x⟩
  memHolder' := ⟨M.toNNReal, HolderWith.of_dist_le fun x y => by
    rw [dist_eq_norm, dist_eq_norm, iteratedFDeriv_zero_eq_comp, comp_apply, comp_apply,
      ← map_sub, LinearIsometryEquiv.norm_map, Real.norm_eq_abs, Real.coe_toNNReal _ hM0]
    exact hM x y⟩

@[simp]
theorem coe_ofHolderZero (hr : 0 < r) (g : E → ℝ) {F M : ℝ} (hF hM0 hM) :
    ⇑(ofHolderZero hr g (F := F) (M := M) hF hM0 hM) = g :=
  rfl

theorem norm_ofHolderZero_le (hr : 0 < r) (g : E → ℝ) {F M : ℝ} (hF : ∀ x, |g x| ≤ F)
    (hM0 : 0 ≤ M) (hM : ∀ x y, |g x - g y| ≤ M * ‖x - y‖ ^ (r : ℝ)) :
    ‖ofHolderZero hr g hF hM0 hM‖ ≤ F + M := by
  have hF0 : 0 ≤ F := (abs_nonneg _).trans (hF 0)
  set w := ofHolderZero hr g hF hM0 hM with hw
  have hHol : HolderWith M.toNNReal r w.iteratedFDerivHolder := HolderWith.of_dist_le
    fun x y => by
      rw [BoundedContDiffHolderMap.coe_iteratedFDerivHolder, dist_eq_norm, dist_eq_norm,
        iteratedFDeriv_zero_eq_comp, comp_apply, comp_apply, ← map_sub,
        LinearIsometryEquiv.norm_map, Real.norm_eq_abs, Real.coe_toNNReal _ hM0]
      exact hM x y
  rw [BoundedContDiffHolderMap.norm_def, Finset.range_zero, Finset.sum_empty, zero_add]
  refine (w.iteratedFDerivHolder.norm_le_of_holderWith hHol).trans ?_
  rw [Real.coe_toNNReal _ hM0]
  gcongr
  refine (BoundedContinuousFunction.norm_le hF0).2 fun x => ?_
  rw [BoundedContDiffHolderMap.iteratedFDerivHolder_toBoundedContinuousFunction,
    w.coe_iteratedFDerivBCF le_rfl, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
  exact hF x

/-- `L (w - w') = L w - L w'` for `C²` functions. -/
theorem ellipticOp_sub (a : E → E →L[ℝ] E) (β : E → E) (c : E → ℝ) {w w' : E → ℝ}
    (hw : ContDiff ℝ 2 w) (hw' : ContDiff ℝ 2 w') (x : E) :
    ellipticOp b a β c (fun y => w y - w' y) x =
      ellipticOp b a β c w x - ellipticOp b a β c w' x := by
  have h := WholeSpaceSolvability.ellipticOp_add b a β c hw hw'.neg x
  rw [ellipticOp_neg] at h
  rw [show (fun y => w y - w' y) = w + fun y => -w' y from funext fun y => by
    simp [sub_eq_add_neg], h, sub_eq_add_neg]

/-- **Uniqueness on the whole space**: bounded `C²` solutions of `L w - μ w = h` coincide
(`a` elliptic, `c ≤ 0`, `μ > 0`). -/
theorem eq_of_ellipticOp_sub_eq {lam Λ α : ℝ} {a : E → E →L[ℝ] E} {β : E → E} {c : E → ℝ}
    (ha : IsEllipticCoeff a lam Λ α) (hlam : 0 ≤ lam) (hβc : IsLowerCoeff β c Λ α)
    (hc : ∀ x, c x ≤ 0) {μ : ℝ} (hμ : 0 < μ) {w w' : E → ℝ} (hw : ContDiff ℝ 2 w)
    (hw' : ContDiff ℝ 2 w') (hb : ∃ A, ∀ x, |w x| ≤ A) (hb' : ∃ A, ∀ x, |w' x| ≤ A)
    (h : ∀ x, ellipticOp b a β c w x - μ * w x = ellipticOp b a β c w' x - μ * w' x) :
    w = w' := by
  obtain ⟨A, hA⟩ := hb
  obtain ⟨A', hA'⟩ := hb'
  funext x
  have hd : ContDiff ℝ 2 (fun y => w y - w' y) := hw.sub hw'
  have key := mul_abs_le_of_ellipticOp_sub b ha.symm
    (fun x v => le_trans (mul_nonneg hlam (sq_nonneg ‖v‖)) (ha.elliptic x v)) ha.bound
    hβc.bound_β hc hμ hd ⟨A + A', fun y => (abs_sub _ _).trans (add_le_add (hA y) (hA' y))⟩
    (F := 0) (fun y => by
      rw [ellipticOp_sub b a β c hw hw' y, show ellipticOp b a β c w y - ellipticOp b a β c w' y -
        μ * (w y - w' y) = (ellipticOp b a β c w y - μ * w y) -
          (ellipticOp b a β c w' y - μ * w' y) by ring, h y, sub_self, abs_zero]) x
  have : |w x - w' x| = 0 := le_antisymm (by
    by_contra hpos; rw [not_le] at hpos; nlinarith [mul_pos hμ hpos]) (abs_nonneg _)
  exact sub_eq_zero.1 (abs_eq_zero.1 this)

/-- **Existence on the whole space** in `C^{2,r}_b`: `L w - μ w = h` for `h ∈ C^{0,r}_b`. -/
theorem exists_solve [MeasurableSpace E] [BorelSpace E] {lam Λ : ℝ} (hlam : 0 < lam)
    (hr0 : 0 < r) (hr1 : r < 1) {a : E → E →L[ℝ] E} {β : E → E} {c : E → ℝ}
    (ha : IsEllipticCoeff a lam Λ r) (hβc : IsLowerCoeff β c Λ r) (hc : ∀ x, c x ≤ 0) {μ : ℝ}
    (hμ : 0 < μ) (h : BoundedContDiffHolderMap 0 r E ℝ) :
    ∃ w : BoundedContDiffHolderMap 2 r E ℝ, ∀ x, ellipticOp b a β c w x - μ * w x = h x := by
  obtain ⟨u, hu, ⟨H, hH⟩, ⟨B, hB⟩, ⟨A, hA⟩, hueq⟩ :=
    WholeSpaceSolvability.exists_ellipticOp_sub_eq b hlam hr0 hr1 ha hβc hc hμ (f := h)
      (F := ‖h‖) (M := ‖h‖) (norm_nonneg _) (fun x => by
        rw [← Real.norm_eq_abs]; exact h.norm_apply_le x) (abs_sub_le_of_zero h)
  have hH0 : ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤
      |H| * ‖x - y‖ ^ (r : ℝ) := fun x y =>
    (hH x y).trans (mul_le_mul_of_nonneg_right (le_abs_self H)
      (Real.rpow_nonneg (norm_nonneg _) _))
  exact ⟨WholeSpaceSolvability.ofBounds u hu hA (norm_fderiv_le_two_mul_add hu hA hB) hB hH0,
    hueq⟩

/-- `‖g x - g y‖ ≤ (L t^{r-1} + 2 K t^r) ‖x - y‖^r` for an `L`-Lipschitz `g` bounded by `K`, any
scale `t > 0` (split at `‖x - y‖ = 1/t`). -/
theorem norm_sub_le_scale {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {g : X → Y} {L K t s : ℝ} (ht : 0 < t) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hL0 : 0 ≤ L)
    (hL : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (hK : ∀ x, ‖g x‖ ≤ K) (x y : X) :
    ‖g x - g y‖ ≤ (L * t ^ (s - 1) + 2 * K * t ^ s) * ‖x - y‖ ^ s := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK x)
  set d := ‖x - y‖ with hd
  have hd0 : 0 ≤ d := norm_nonneg _
  have hds : 0 ≤ d ^ s := Real.rpow_nonneg hd0 _
  have ht1 : 0 ≤ t ^ (s - 1) := Real.rpow_nonneg ht.le _
  have hts : 0 ≤ t ^ s := Real.rpow_nonneg ht.le _
  rcases le_total (d * t) 1 with hdt | hdt
  · -- small distances: the Lipschitz bound
    have hdt' : d ≤ t⁻¹ := by rw [← one_div, le_div_iff₀ ht]; exact hdt
    have hsplit : d = d ^ (1 - s) * d ^ s := by
      rw [← Real.rpow_add' hd0 (by norm_num), sub_add_cancel, Real.rpow_one]
    have hpow : d ^ (1 - s) ≤ t ^ (s - 1) := by
      calc d ^ (1 - s) ≤ t⁻¹ ^ (1 - s) := Real.rpow_le_rpow hd0 hdt' (by linarith)
        _ = t ^ (s - 1) := by
          rw [Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, neg_sub]
    calc ‖g x - g y‖ ≤ L * d := hL x y
      _ = L * d ^ (1 - s) * d ^ s := by rw [mul_assoc, ← hsplit]
      _ ≤ L * t ^ (s - 1) * d ^ s := by gcongr
      _ ≤ (L * t ^ (s - 1) + 2 * K * t ^ s) * d ^ s := by
          gcongr; nlinarith [mul_nonneg hK0 hts]
  · -- large distances: the sup bound
    have h1 : 1 ≤ (d * t) ^ s := Real.one_le_rpow hdt hs0
    rw [Real.mul_rpow hd0 ht.le] at h1
    calc ‖g x - g y‖ ≤ ‖g x‖ + ‖g y‖ := norm_sub_le _ _
      _ ≤ 2 * K := by linarith [hK x, hK y]
      _ ≤ 2 * K * (d ^ s * t ^ s) := le_mul_of_one_le_right (by positivity) h1
      _ ≤ (L * t ^ (s - 1) + 2 * K * t ^ s) * d ^ s := by
          nlinarith [mul_nonneg (mul_nonneg hL0 ht1) hds]

/-- **The whole-space solution is small for a large parameter** (`μ = t²`, `t ≥ 1`):
`sup|w|`, `[w]_r`, `sup|Dw|`, `[Dw]_r ≤ C t^{r-1} ‖h‖` for `L w - μ w = h`, uniformly over the class. -/
theorem exists_solve_small {lam Λ : ℝ} (hlam : 0 < lam) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ (a : E → E →L[ℝ] E) (β : E → E) (c : E → ℝ),
      IsEllipticCoeff a lam Λ r → IsLowerCoeff β c Λ r → (∀ x, c x ≤ 0) →
      ∀ t : ℝ, 1 ≤ t → ∀ (w : BoundedContDiffHolderMap 2 r E ℝ)
        (h : BoundedContDiffHolderMap 0 r E ℝ),
      (∀ x, ellipticOp b a β c w x - t ^ 2 * w x = h x) →
      (∀ x, |w x| ≤ Cs * (t ^ (r : ℝ) / t) * ‖h‖) ∧
      (∀ x y, |w x - w y| ≤ Cs * (t ^ (r : ℝ) / t) * ‖h‖ * ‖x - y‖ ^ (r : ℝ)) ∧
      (∀ x, ‖fderiv ℝ w x‖ ≤ Cs * (t ^ (r : ℝ) / t) * ‖h‖) ∧
      (∀ x y, ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤
        Cs * (t ^ (r : ℝ) / t) * ‖h‖ * ‖x - y‖ ^ (r : ℝ)) := by
  obtain ⟨Cw, hCw0, hW⟩ := SchauderWeighted.exists_weighted_estimate (Λ := Λ) (α := (r : ℝ)) b hlam
    (NNReal.coe_pos.2 hr0) (by exact_mod_cast hr1)
  refine ⟨6 * Cw + 2, by positivity, fun a β c ha hβc hc t ht w h hwh => ?_⟩
  have ht0 : 0 < t := one_pos.trans_le ht
  set N := ‖h‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  set T := t ^ (r : ℝ) with hT
  have hT1 : 1 ≤ T := Real.one_le_rpow ht r.coe_nonneg
  have hμ1 : 1 ≤ t ^ 2 := one_le_pow₀ ht
  have hμr : (t ^ 2) ^ ((r : ℝ) / 2) = T := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; congr 1; push_cast; ring
  have hμr1 : (t ^ 2) ^ ((1 + (r : ℝ)) / 2) = t * T := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le,
      show ((2 : ℕ) : ℝ) * ((1 + (r : ℝ)) / 2) = 1 + r by push_cast; ring,
      Real.rpow_add ht0, Real.rpow_one]
  have hw2 := WholeSpaceSolvability.contDiff_two w
  obtain ⟨-, w2, w3, w4⟩ := hW a β c ha hβc hc (t ^ 2) hμ1 w hw2
    ⟨‖w‖, WholeSpaceSolvability.norm_fderiv_fderiv_sub_le w⟩
    ⟨‖w‖, WholeSpaceSolvability.norm_fderiv_fderiv_le w⟩ ⟨‖w‖, WholeSpaceSolvability.abs_apply_le w⟩
    N N hN0 (fun x => by rw [hwh x, ← Real.norm_eq_abs]; exact h.norm_apply_le x)
    (fun x y => by rw [hwh x, hwh y]; exact abs_sub_le_of_zero h x y)
  rw [hμr] at w2 w3
  rw [hμr1] at w3
  have hK : N + T * N ≤ 2 * T * N := by nlinarith
  have hCwK : Cw * (N + T * N) ≤ Cw * (2 * T * N) := mul_le_mul_of_nonneg_left hK hCw0
  -- the three sup bounds
  have hB : ∀ x, ‖fderiv ℝ (fderiv ℝ w) x‖ ≤ 2 * Cw * N := fun x => by
    have := (w2 x).trans hCwK
    have hT0 : 0 < T := one_pos.trans_le hT1
    by_contra hcon; rw [not_le] at hcon
    nlinarith [mul_lt_mul_of_pos_left hcon hT0]
  have hD : ∀ x, ‖fderiv ℝ w x‖ ≤ 2 * Cw * N / t := fun x => by
    have := (w3 x).trans hCwK
    have hT0 : 0 < T := one_pos.trans_le hT1
    rw [le_div_iff₀ ht0]
    by_contra hcon; rw [not_le] at hcon
    nlinarith [mul_lt_mul_of_pos_left hcon hT0]
  have hS : ∀ x, |w x| ≤ N / t ^ 2 := fun x => by
    rw [le_div_iff₀ (by positivity), mul_comm]; exact w4 x
  -- comparison of the scales
  set ε := T / t with hε
  have hinv : 1 / t ≤ ε := by
    rw [hε]; exact div_le_div_of_nonneg_right hT1 ht0.le
  have hinv2 : 1 / t ^ 2 ≤ 1 / t := by
    rw [div_le_div_iff₀ (by positivity) ht0]; nlinarith
  have hrm1 : t ^ ((r : ℝ) - 1) = ε := by rw [Real.rpow_sub_one ht0.ne']
  have hNε : N / t ≤ N * ε := by rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hinv hN0
  have hNε2 : N / t ^ 2 ≤ N * ε := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left (hinv2.trans hinv) hN0
  have hε0 : 0 ≤ ε := by positivity
  refine ⟨fun x => ?_, fun x y => ?_, fun x => ?_, fun x y => ?_⟩
  · calc |w x| ≤ N / t ^ 2 := hS x
      _ ≤ N * ε := hNε2
      _ ≤ (6 * Cw + 2) * ε * N := by nlinarith [mul_nonneg hN0 hε0, mul_nonneg hCw0 (mul_nonneg hN0 hε0)]
  · have hlip : ∀ x y, ‖w x - w y‖ ≤ (2 * Cw * N / t) * ‖x - y‖ := fun x y => by
      rw [Real.norm_eq_abs]; exact abs_sub_le_of_fderiv hw2 hD x y
    have h1 := norm_sub_le_scale (g := ⇑w) ht0 r.coe_nonneg (by exact_mod_cast hr1.le)
      (by positivity) hlip (fun x => by rw [Real.norm_eq_abs]; exact hS x) x y
    rw [Real.norm_eq_abs, hrm1] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) _))
    have e1 : 2 * Cw * N / t * ε ≤ 2 * Cw * (N * ε) := by
      rw [show 2 * Cw * N / t * ε = 2 * Cw * (N / t) * ε by ring]
      have : N / t * ε ≤ N * ε := mul_le_mul_of_nonneg_right
        (div_le_self hN0 ht) hε0
      nlinarith
    have e2 : 2 * (N / t ^ 2) * T ≤ 2 * (N * ε) := by
      rw [show 2 * (N / t ^ 2) * T = 2 * (N / t * ε) by rw [hε]; field_simp]
      have : N / t * ε ≤ N * ε := mul_le_mul_of_nonneg_right (div_le_self hN0 ht) hε0
      linarith
    nlinarith [mul_nonneg hN0 hε0, mul_nonneg hCw0 (mul_nonneg hN0 hε0)]
  · calc ‖fderiv ℝ w x‖ ≤ 2 * Cw * N / t := hD x
      _ = 2 * Cw * (N / t) := by ring
      _ ≤ 2 * Cw * (N * ε) := by gcongr
      _ ≤ (6 * Cw + 2) * ε * N := by nlinarith [mul_nonneg hN0 hε0, mul_nonneg hCw0 (mul_nonneg hN0 hε0)]
  · have h1 := norm_sub_le_scale (g := fderiv ℝ ⇑w) ht0 r.coe_nonneg
      (by exact_mod_cast hr1.le) (by positivity) (norm_fderiv_sub_le hw2 hB) hD x y
    rw [hrm1] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) _))
    have e2 : 2 * (2 * Cw * N / t) * T = 4 * Cw * (N * ε) := by rw [hε]; field_simp; ring
    nlinarith [mul_nonneg hN0 hε0, mul_nonneg hCw0 (mul_nonneg hN0 hε0)]

/-- The constant `P₀` bounding `a : D²χ + Dχ(β)`. -/
def coeffZero (d Λ K₁ K₂ : ℝ) : ℝ := d * Λ * K₂ + K₁ * Λ

/-- The Hölder constant `P₁` of `a : D²χ + Dχ(β)`. -/
def coeffOne (d Λ K₁ K₂ K₃ : ℝ) : ℝ :=
  d * (Λ * K₂ + Λ * (K₃ + 2 * K₂)) + ((K₂ + 2 * K₁) * Λ + K₁ * Λ)

/-- The sup bound for the remainder `R = v (a : D²χ + Dχ(β)) + a : (Dχ ⊗ Dv + Dv ⊗ Dχ)`. -/
theorem abs_remainder_le {Λ K₁ K₂ S₀ D₀ : ℝ} (a : E → E →L[ℝ] E) (β : E → E) {χ v : E → ℝ}
    (hab : ∀ x, ‖a x‖ ≤ Λ) (hβb : ∀ x, ‖β x‖ ≤ Λ)
    (h1 : ∀ x, ‖fderiv ℝ χ x‖ ≤ K₁) (h2 : ∀ x, ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ K₂)
    (hS : ∀ x, |v x| ≤ S₀) (hD : ∀ x, ‖fderiv ℝ v x‖ ≤ D₀) (x : E) :
    |remainder b a β χ v x| ≤
      S₀ * coeffZero (Fintype.card ι) Λ K₁ K₂ + 2 * Fintype.card ι * (Λ * K₁ * D₀) := by
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans (hab 0)
  have hK₁ : 0 ≤ K₁ := (norm_nonneg _).trans (h1 0)
  have hS0 : 0 ≤ S₀ := (abs_nonneg _).trans (hS 0)
  have hd0 : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hP : |hessTrace b (a x) (fderiv ℝ (fderiv ℝ χ) x) + fderiv ℝ χ x (β x)| ≤
      coeffZero (Fintype.card ι) Λ K₁ K₂ := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (abs_hessTrace_le b _ _).trans ?_
      have := mul_le_mul (hab x) (h2 x) (ContinuousLinearMap.opNorm_nonneg _) hΛ
      rw [mul_assoc]; rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left this hd0
    · rw [← Real.norm_eq_abs]
      exact ((fderiv ℝ χ x).le_opNorm _).trans (mul_le_mul (h1 x) (hβb x) (norm_nonneg _) hK₁)
  have hc := abs_crossTerm_le b (a x) (fderiv ℝ χ x) (fderiv ℝ v x)
  have hc' : 2 * Fintype.card ι * (‖a x‖ * ‖fderiv ℝ χ x‖ * ‖fderiv ℝ v x‖) ≤
      2 * Fintype.card ι * (Λ * K₁ * D₀) := by
    gcongr
    · exact hab x
    · exact h1 x
    · exact hD x
  rw [remainder]
  refine (abs_add_le _ _).trans (add_le_add ?_ (hc.trans hc'))
  rw [abs_mul]
  exact mul_le_mul (hS x) hP (abs_nonneg _) hS0

/-- The Hölder bound for the remainder in terms of `sup|v|`, `[v]_r`, `sup|Dv|`, `[Dv]_r`. -/
theorem abs_remainder_sub_le' {s Λ K₁ K₂ K₃ S₀ S₁ D₀ D₁ : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hK₃ : 0 ≤ K₃) (a : E → E →L[ℝ] E) (β : E → E) {χ v : E → ℝ}
    (hab : ∀ x, ‖a x‖ ≤ Λ) (hah : ∀ x y, ‖a x - a y‖ ≤ Λ * ‖x - y‖ ^ s)
    (hβb : ∀ x, ‖β x‖ ≤ Λ) (hβh : ∀ x y, ‖β x - β y‖ ≤ Λ * ‖x - y‖ ^ s)
    (h1 : ∀ x, ‖fderiv ℝ χ x‖ ≤ K₁) (h2 : ∀ x, ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ K₂)
    (h1L : ∀ x y, ‖fderiv ℝ χ x - fderiv ℝ χ y‖ ≤ K₂ * ‖x - y‖)
    (h2L : ∀ x y, ‖fderiv ℝ (fderiv ℝ χ) x - fderiv ℝ (fderiv ℝ χ) y‖ ≤ K₃ * ‖x - y‖)
    (hS : ∀ x, |v x| ≤ S₀) (hS1 : ∀ x y, |v x - v y| ≤ S₁ * ‖x - y‖ ^ s)
    (hD : ∀ x, ‖fderiv ℝ v x‖ ≤ D₀)
    (hD1 : ∀ x y, ‖fderiv ℝ v x - fderiv ℝ v y‖ ≤ D₁ * ‖x - y‖ ^ s) (x y : E) :
    |remainder b a β χ v x - remainder b a β χ v y| ≤
      (S₁ * coeffZero (Fintype.card ι) Λ K₁ K₂ + S₀ * coeffOne (Fintype.card ι) Λ K₁ K₂ K₃ +
        2 * Fintype.card ι * ((K₂ + 2 * K₁) * D₀ * Λ + K₁ * D₁ * Λ + K₁ * D₀ * Λ)) *
        ‖x - y‖ ^ s := by
  set d : ℝ := (Fintype.card ι : ℝ) with hd
  set p := ‖x - y‖ ^ s with hp
  have hp0 : 0 ≤ p := Real.rpow_nonneg (norm_nonneg _) _
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans (hab 0)
  have hK₁ : 0 ≤ K₁ := (norm_nonneg _).trans (h1 0)
  have hK₂ : 0 ≤ K₂ := (ContinuousLinearMap.opNorm_nonneg _).trans (h2 0)
  have hS0 : 0 ≤ S₀ := (abs_nonneg _).trans (hS 0)
  have hD0 : 0 ≤ D₀ := (norm_nonneg _).trans (hD 0)
  set H₁ := K₂ + 2 * K₁ with hH₁
  set H₂ := K₃ + 2 * K₂ with hH₂
  have hDχh : ‖fderiv ℝ χ x - fderiv ℝ χ y‖ ≤ H₁ * p :=
    norm_sub_le_rpow_of_lipschitz_of_bound (Y := E →L[ℝ] ℝ) hK₂ hs0 hs1 h1L h1 x y
  have hD2χh : ‖fderiv ℝ (fderiv ℝ χ) x - fderiv ℝ (fderiv ℝ χ) y‖ ≤ H₂ * p :=
    norm_sub_le_rpow_of_lipschitz_of_bound (Y := E →L[ℝ] E →L[ℝ] ℝ) hK₃ hs0 hs1 h2L h2 x y
  set P₀ := coeffZero d Λ K₁ K₂ with hP₀
  set P₁ := coeffOne d Λ K₁ K₂ K₃ with hP₁
  have hPb : |hessTrace b (a x) (fderiv ℝ (fderiv ℝ χ) x) + fderiv ℝ χ x (β x)| ≤ P₀ := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (abs_hessTrace_le b _ _).trans ?_
      have := mul_le_mul (hab x) (h2 x) (ContinuousLinearMap.opNorm_nonneg _) hΛ
      rw [mul_assoc, hd]; rw [mul_assoc] at *
      exact mul_le_mul_of_nonneg_left this hd0
    · rw [← Real.norm_eq_abs]
      exact ((fderiv ℝ χ x).le_opNorm _).trans (mul_le_mul (h1 x) (hβb x) (norm_nonneg _) hK₁)
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
      rw [hP₁, coeffOne]; ring
    linarith
  have hvP := abs_mul_sub_mul_le (hS1 x y) hPb (hS y) hPh
  have hc := abs_crossTerm_sub_le b (a x) (a y) (fderiv ℝ χ x) (fderiv ℝ χ y) (fderiv ℝ v x)
    (fderiv ℝ v y) (hab x) (h1 x) (h1 y) (hD x) (hD y)
  have hcross : |crossTerm b (a x) (fderiv ℝ χ x) (fderiv ℝ v x) -
      crossTerm b (a y) (fderiv ℝ χ y) (fderiv ℝ v y)| ≤
      2 * d * (H₁ * p * D₀ * Λ + K₁ * (D₁ * p) * Λ + K₁ * D₀ * (Λ * p)) := by
    refine hc.trans ?_
    gcongr
    · exact hD1 x y
    · exact hah x y
  rw [remainder, remainder,
    show ∀ A B C D : ℝ, A + B - (C + D) = (A - C) + (B - D) from fun _ _ _ _ => by ring]
  refine (abs_add_le _ _).trans ((add_le_add hvP hcross).trans (le_of_eq ?_))
  ring

/-! ### Algebra of `L` and of the remainder -/

theorem ellipticOp_const_zero (a : E → E →L[ℝ] E) (β : E → E) (c : E → ℝ) (x : E) :
    ellipticOp b a β c (fun _ => (0 : ℝ)) x = 0 := by
  simp [ellipticOp, hessTrace]

/-- `L` is additive on functions that are `C²` near the point. -/
theorem ellipticOp_add_of_contDiffAt (a : E → E →L[ℝ] E) (β : E → E) (c : E → ℝ)
    {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    ellipticOp b a β c (fun y => f y + g y) x =
      ellipticOp b a β c f x + ellipticOp b a β c g x := by
  have hf1 : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
    (hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have hg1 : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y :=
    (hg.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have hDf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hDg : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hev : fderiv ℝ (fun y => f y + g y) =ᶠ[𝓝 x] fun y => fderiv ℝ f y + fderiv ℝ g y := by
    filter_upwards [hf1, hg1] with y hfy hgy
    exact fderiv_add hfy hgy
  have h2 : fderiv ℝ (fderiv ℝ (fun y => f y + g y)) x =
      fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ g) x := by
    rw [hev.fderiv_eq]; exact fderiv_add hDf hDg
  simp only [ellipticOp]
  rw [h2, hev.eq_of_nhds, WholeSpaceSolvability.hessTrace_add_right]
  simp only [add_apply]
  ring

/-- `L` commutes with finite sums of functions that are `C²` near the point. -/
theorem ellipticOp_finset_sum {κ : Type*} (a : E → E →L[ℝ] E) (β : E → E) (c : E → ℝ)
    (s : Finset κ) (f : κ → E → ℝ) {x : E} (hf : ∀ k ∈ s, ContDiffAt ℝ 2 (f k) x) :
    ellipticOp b a β c (fun y => ∑ k ∈ s, f k y) x = ∑ k ∈ s, ellipticOp b a β c (f k) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ellipticOp_const_zero b a β c x
  | insert k s hk ih =>
    have hs : ContDiffAt ℝ 2 (fun y => ∑ j ∈ s, f j y) x := by
      have := ContDiffAt.sum (s := s) (f := fun j y => f j y) (x := x)
        (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      simpa using this
    simp only [Finset.sum_insert hk]
    rw [ellipticOp_add_of_contDiffAt b a β c (hf k (Finset.mem_insert_self k s)) hs,
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

theorem crossTerm_zero_left (A : E →L[ℝ] E) (q : E →L[ℝ] ℝ) : crossTerm b A 0 q = 0 := by
  simp [crossTerm]

theorem crossTerm_sub_right (A : E →L[ℝ] E) (p q q' : E →L[ℝ] ℝ) :
    crossTerm b A p (q - q') = crossTerm b A p q - crossTerm b A p q' := by
  simp only [crossTerm, sub_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The remainder vanishes off `tsupport χ`. -/
theorem remainder_eq_zero_of_notMem (a : E → E →L[ℝ] E) (β : E → E) {χ : E → ℝ} (v : E → ℝ)
    {z : E} (hz : z ∉ tsupport χ) : remainder b a β χ v z = 0 := by
  have h1 : fderiv ℝ χ z = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => hz (tsupport_fderiv_subset ℝ h)
  have h2 : fderiv ℝ (fderiv ℝ χ) z = 0 :=
    image_eq_zero_of_notMem_tsupport fun h =>
      hz (tsupport_fderiv_subset ℝ (tsupport_fderiv_subset ℝ h))
  simp [remainder, h1, h2, hessTrace, crossTerm_zero_left]

theorem tsupport_remainder_subset (a : E → E →L[ℝ] E) (β : E → E) (χ v : E → ℝ) :
    tsupport (remainder b a β χ v) ⊆ tsupport χ :=
  closure_minimal (fun z hz => by
    by_contra h; exact hz (remainder_eq_zero_of_notMem b a β v h)) (isClosed_tsupport χ)

/-- The remainder is linear in `v`. -/
theorem remainder_sub (a : E → E →L[ℝ] E) (β : E → E) (χ : E → ℝ) {v v' : E → ℝ}
    (hv : Differentiable ℝ v) (hv' : Differentiable ℝ v') (x : E) :
    remainder b a β χ (fun y => v y - v' y) x =
      remainder b a β χ v x - remainder b a β χ v' x := by
  have h1 : fderiv ℝ (fun y => v y - v' y) x = fderiv ℝ v x - fderiv ℝ v' x :=
    fderiv_sub (hv x) (hv' x)
  simp only [remainder, h1, crossTerm_sub_right]
  ring

end WholeSpace

/-- Multiplication by a smooth function with compact support on `C^{2,r}_b` (`r ≤ 1`). -/
theorem exists_mul_cutoff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {r : ℝ≥0} (hr : r ≤ 1) {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) :
    ∀ w : BoundedContDiffHolderMap 2 r E ℝ, ∃ v : BoundedContDiffHolderMap 2 r E ℝ,
      ⇑v = fun z => ψ z * w z := by
  obtain ⟨C, hC⟩ := BoundedContDiffHolderMap.exists_smul_comp_of_contDiffOn (F := ℝ) (k := 2)
    hr isOpen_univ (contDiffOn_id (s := univ)) (contDiff_infty.1 hψ 3) hψc (subset_univ _)
  intro w
  obtain ⟨v, hv, -⟩ := hC w
  exact ⟨v, funext fun z => by rw [hv z, smul_eq_mul, id]⟩

/-! ### On the manifold -/

section Manifold

open HolderAtlas.HolderMap

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {A : HolderAtlas n M} {ι : Type*} [Fintype ι]
  (b : OrthonormalBasis ι ℝ (ComplexModel n)) {r : ℝ≥0}

theorem pushforward_sub (e : ComplexChart n M) (F G : ComplexModel n → ℝ) (y : M) :
    pushforward e (fun z => F z - G z) y = pushforward e F y - pushforward e G y := by
  by_cases hy : y ∈ e.val.source
  · simp only [pushforward_of_mem _ hy]
  · simp only [pushforward_of_notMem _ hy, sub_zero]

/-- **`L` of a push-forward**, computed in its own chart: if `L_i w - μ w = (χ_i h) ∘ e_i⁻¹`, `ψ = 1` on
`e_i(tsupport χ_i)` with support in the compact `K₂ ⊆ U_i`, `W = push_i(ψ w)` and `g = L W` (in all charts),
then `g = χ_i h + μ W + push_i(R)` with the remainder `R` of the product rule. -/
theorem eq_push_identity
    {a : Fin A.m → ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n}
    {β : Fin A.m → ComplexModel n → ComplexModel n} {c : Fin A.m → ComplexModel n → ℝ}
    {U : Fin A.m → Set (ComplexModel n)}
    (hKU : ∀ i, (A.chart i).val '' tsupport (A.χ i) ⊆ U i)
    (hUt : ∀ i, U i ⊆ (A.chart i).val.target)
    (i : Fin A.m) {ψ w : ComplexModel n → ℝ} (hψ : ContDiff ℝ 2 ψ) (hw : ContDiff ℝ 2 w)
    {K₂ : Set (ComplexModel n)} (hK₂c : IsCompact K₂) (hψK : tsupport ψ ⊆ K₂) (hK₂U : K₂ ⊆ U i)
    (hψ1 : ∀ z ∈ (A.chart i).val '' tsupport (A.χ i), ψ z = 1)
    (h : M → ℝ) {μ : ℝ}
    (hwh : ∀ z, ellipticOp b (a i) (β i) (c i) w z - μ * w z = A.localRep i h z)
    (W : M → ℝ) (hW : W = pushforward (A.chart i) (fun z => ψ z * w z))
    (g : M → ℝ)
    (hg : ∀ j, ∀ z ∈ U j, g ((A.chart j).val.symm z) =
      ellipticOp b (a j) (β j) (c j) (fun x => W ((A.chart j).val.symm x)) z)
    (y : M) :
    g y = A.χ i y * h y + μ * W y +
      pushforward (A.chart i) (remainder b (a i) (β i) ψ w) y := by
  set e := A.chart i with he
  have hsupp : tsupport (fun z => ψ z * w z) ⊆ K₂ := tsupport_mul_subset_left.trans hψK
  by_cases hy : y ∈ e.val.source ∧ e.val y ∈ U i
  · obtain ⟨hys, hyU⟩ := hy
    set z := e.val y with hz
    have hzt : z ∈ e.val.target := hUt i hyU
    have hsy : e.val.symm z = y := e.val.left_inv hys
    have h1 := hg i z hyU
    rw [hsy] at h1
    have hloc : (fun x => W (e.val.symm x)) =ᶠ[𝓝 z] fun x => ψ x * w x := by
      filter_upwards [e.val.open_target.mem_nhds hzt] with x hx
      rw [hW, pushforward_symm _ hx]
    rw [h1, ellipticOp_congr b _ _ _ hloc, ellipticOp_mul_eq b _ _ _ hψ hw]
    have hL : ellipticOp b (a i) (β i) (c i) w z = A.localRep i h z + μ * w z := by
      linarith [hwh z]
    have hrep : A.localRep i h z = A.χ i y * h y := by
      rw [HolderAtlas.localRep_chart _ hys, smul_eq_mul]
    have hψrep : ψ z * A.localRep i h z = A.localRep i h z := by
      by_cases h0 : A.localRep i h z = 0
      · rw [h0, mul_zero]
      · have hzK : z ∈ e.val '' tsupport (A.χ i) := by
          by_contra hzK
          exact h0 (HolderAtlas.localRep_eq_zero_of_notMem _ hzK)
        rw [hψ1 z hzK, one_mul]
    have hWy : W y = ψ z * w z := by rw [hW, pushforward_of_mem _ hys]
    rw [hL, pushforward_of_mem _ hys, hWy, ← hrep, mul_add, hψrep]
    ring
  · have hyK : y ∉ e.val.symm '' K₂ := by
      rintro ⟨k, hk, rfl⟩
      have hkt := hUt i (hK₂U hk)
      exact hy ⟨e.val.map_target hkt, by rw [e.val.right_inv hkt]; exact hK₂U hk⟩
    have hχy : A.χ i y = 0 := by
      by_contra hne
      have hyt : y ∈ tsupport (A.χ i) := subset_tsupport _ hne
      exact hy ⟨A.tsupport_subset i hyt, hKU i ⟨y, hyt, rfl⟩⟩
    have hWy : W y = 0 := by rw [hW]; exact pushforward_eq_zero_of_notMem hsupp hyK
    have hRy : pushforward e (remainder b (a i) (β i) ψ w) y = 0 :=
      pushforward_eq_zero_of_notMem ((tsupport_remainder_subset b _ _ ψ w).trans hψK) hyK
    rw [hχy, hWy, hRy, zero_mul, mul_zero, add_zero, add_zero]
    obtain ⟨j, -, hj⟩ : ∃ j ∈ Finset.univ, A.χ j y ≠ 0 :=
      Finset.exists_ne_zero_of_sum_ne_zero (by rw [A.sum_eq_one]; exact one_ne_zero)
    set ej := A.chart j with hej
    have hyj : y ∈ ej.val.source := A.tsupport_subset j (subset_tsupport _ hj)
    have hzj : ej.val y ∈ U j := hKU j ⟨y, subset_tsupport _ hj, rfl⟩
    have h1 := hg j (ej.val y) hzj
    rw [ej.val.left_inv hyj] at h1
    rw [h1]
    have hclosed : IsClosed (e.val.symm '' K₂) :=
      (hK₂c.image_of_continuousOn (e.val.continuousOn_symm.mono
        (hK₂U.trans (hUt i)))).isClosed
    have hnhds : (e.val.symm '' K₂)ᶜ ∈ 𝓝 (ej.val.symm (ej.val y)) := by
      rw [ej.val.left_inv hyj]; exact hclosed.isOpen_compl.mem_nhds hyK
    have hcont : ContinuousAt ej.val.symm (ej.val y) :=
      ej.val.continuousAt_symm (ej.val.map_source hyj)
    have hloc : (fun x => W (ej.val.symm x)) =ᶠ[𝓝 (ej.val y)] fun _ => (0 : ℝ) := by
      filter_upwards [hcont.preimage_mem_nhds hnhds] with x hx
      rw [hW]; exact pushforward_eq_zero_of_notMem hsupp hx
    rw [ellipticOp_congr b _ _ _ hloc, ellipticOp_const_zero]

/-- **`L - μ` is onto `C^{0,r}(M)` for `μ` large** (the parametrix; blueprint
`bou:kahler-laplacian-solvability`).  The operator is given chartwise by whole-space coefficients in
the Schauder class `(λ, Λ, r)` with `c_i ≤ 0` on open sets `U_i ⊇ e_i(tsupport χ_i)` of the chart
targets, and it is realizable (`hreal`: the chart data are compatible). -/
theorem exists_ellipticOp_sub_eq_of_large {lam Λ : ℝ} (hlam : 0 < lam) (hr0 : 0 < r)
    (hr1 : r < 1)
    (a : Fin A.m → ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n)
    (β : Fin A.m → ComplexModel n → ComplexModel n) (c : Fin A.m → ComplexModel n → ℝ)
    (ha : ∀ i, IsEllipticCoeff (a i) lam Λ r) (hβc : ∀ i, IsLowerCoeff (β i) (c i) Λ r)
    (hc : ∀ i x, c i x ≤ 0) (U : Fin A.m → Set (ComplexModel n)) (hU : ∀ i, IsOpen (U i))
    (hKU : ∀ i, (A.chart i).val '' tsupport (A.χ i) ⊆ U i)
    (hUt : ∀ i, U i ⊆ (A.chart i).val.target)
    (hreal : ∀ u : A.HolderMap 2 r ℝ, ∃ g : M → ℝ, ∀ i, ∀ z ∈ U i,
      g ((A.chart i).val.symm z) =
        ellipticOp b (a i) (β i) (c i) (fun w => u ((A.chart i).val.symm w)) z) :
    ∃ μ₀ : ℝ, 1 ≤ μ₀ ∧ ∀ μ : ℝ, μ₀ ≤ μ → ∀ f : A.HolderMap 0 r ℝ, ∃ u : A.HolderMap 2 r ℝ,
      ∀ i, ∀ z ∈ U i,
        ellipticOp b (a i) (β i) (c i) (fun w => u ((A.chart i).val.symm w)) z -
          μ * u ((A.chart i).val.symm z) = f ((A.chart i).val.symm z) := by
  classical
  have hr1' : r ≤ 1 := hr1.le
  set d : ℝ := (Fintype.card ι : ℝ) with hd
  -- cut-offs `ψ_i = 1` on `e_i(tsupport χ_i)`, supported in `U_i`
  have hcut : ∀ i : Fin A.m, ∃ ψ : ComplexModel n → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ U i ∧ ∀ z ∈ (A.chart i).val '' tsupport (A.χ i), ψ z = 1 := fun i =>
    exists_contDiff_eq_one_of_isCompact (A.isCompact_image_tsupport i) (hU i) (hKU i)
  choose ψ hψs hψc hψU hψ1 using hcut
  have hK₂t : ∀ i, tsupport (ψ i) ⊆ (A.chart i).val.target := fun i => (hψU i).trans (hUt i)
  -- push-forward constants
  have hP2 := fun i => exists_pushforward (A := A) (k := 2) (F := ℝ) hr1' (A.chart i) (hψc i)
    (hK₂t i)
  choose Cp2 hCp2 using hP2
  have hP0 := fun i => exists_pushforward (A := A) (k := 0) (F := ℝ) hr1' (A.chart i) (hψc i)
    (hK₂t i)
  choose Cp0 hCp0 using hP0
  -- bounds for the cut-offs
  have hbd := fun i => exists_bounds_of_hasCompactSupport (hψs i) (hψc i)
  choose K₀ K₁ K₂ K₃ hK₀0 hK₃0 hb0 hb1 hb2 hb1L hb2L using hbd
  -- the smallness constant on the whole space
  obtain ⟨Cs, hCs0, hsmall⟩ := exists_solve_small (Λ := Λ) b hlam hr0 hr1
  set Q : Fin A.m → ℝ := fun i => |2 * coeffZero d Λ (K₁ i) (K₂ i) +
    coeffOne d Λ (K₁ i) (K₂ i) (K₃ i) + 2 * d * (Λ * K₁ i) +
    2 * d * ((K₂ i + 2 * K₁ i) * Λ + K₁ i * Λ + K₁ i * Λ)| with hQ
  set Θ : ℝ := ∑ i, |Cp0 i| * Cs * Q i with hΘ
  have hΘ0 : 0 ≤ Θ := Finset.sum_nonneg fun i _ => by positivity
  have hr1R : (r : ℝ) < 1 := by exact_mod_cast hr1
  set t₀ : ℝ := (2 * Θ + 1) ^ (1 / (1 - (r : ℝ))) with ht₀
  have h1r : 0 < 1 - (r : ℝ) := by linarith
  have ht₀1 : 1 ≤ t₀ := Real.one_le_rpow (by linarith) (one_div_nonneg.2 h1r.le)
  have ht₀r : t₀ ^ (1 - (r : ℝ)) = 2 * Θ + 1 := by
    rw [ht₀, ← Real.rpow_mul (by positivity), one_div_mul_cancel h1r.ne', Real.rpow_one]
  refine ⟨t₀ ^ 2, one_le_pow₀ ht₀1, fun μ hμ f => ?_⟩
  -- the scale `t = √μ`
  set t := Real.sqrt μ with ht
  have hμ0 : 0 ≤ μ := (zero_le_one.trans (one_le_pow₀ ht₀1)).trans hμ
  have htt : t ^ 2 = μ := Real.sq_sqrt hμ0
  have htt₀ : t₀ ≤ t := by
    rw [ht]; exact Real.le_sqrt_of_sq_le hμ
  have ht1 : 1 ≤ t := ht₀1.trans htt₀
  have ht0 : 0 < t := one_pos.trans_le ht1
  set ε := t ^ (r : ℝ) / t with hε
  have hε0 : 0 ≤ ε := by positivity
  have hΘε : Θ * ε ≤ 1 / 2 := by
    have h1 : 2 * Θ + 1 ≤ t ^ (1 - (r : ℝ)) := by
      rw [← ht₀r]; exact Real.rpow_le_rpow (by linarith) htt₀ (by linarith)
    have h2 : t = t ^ (1 - (r : ℝ)) * t ^ (r : ℝ) := by
      rw [← Real.rpow_add ht0, sub_add_cancel, Real.rpow_one]
    have htr : 0 < t ^ (r : ℝ) := Real.rpow_pos_of_pos ht0 _
    rw [hε, mul_div_assoc', div_le_iff₀ ht0]
    nlinarith [mul_le_mul_of_nonneg_right h1 htr.le]
  -- whole-space solution operators `w_i(g)` of `L_i w - μ w = g`
  have hsol : ∀ i (g : BoundedContDiffHolderMap 0 r (ComplexModel n) ℝ),
      ∃ w : BoundedContDiffHolderMap 2 r (ComplexModel n) ℝ,
        ∀ x, ellipticOp b (a i) (β i) (c i) w x - t ^ 2 * w x = g x := fun i g =>
    exists_solve b hlam hr0 hr1 (ha i) (hβc i) (hc i) (by positivity) g
  choose wsol hwsol using hsol
  have hwsub : ∀ i (g g' : BoundedContDiffHolderMap 0 r (ComplexModel n) ℝ),
      ⇑(wsol i (g - g')) = fun x => wsol i g x - wsol i g' x := by
    intro i g g'
    have h2 := WholeSpaceSolvability.contDiff_two (wsol i g)
    have h2' := WholeSpaceSolvability.contDiff_two (wsol i g')
    refine eq_of_ellipticOp_sub_eq b (ha i) hlam.le (hβc i) (hc i) (by positivity : 0 < t ^ 2)
      (WholeSpaceSolvability.contDiff_two _) (h2.sub h2')
      ⟨_, WholeSpaceSolvability.abs_apply_le (wsol i (g - g'))⟩
      ⟨‖wsol i g‖ + ‖wsol i g'‖, fun x => (abs_sub _ _).trans
        (add_le_add (WholeSpaceSolvability.abs_apply_le _ x)
          (WholeSpaceSolvability.abs_apply_le _ x))⟩ fun x => ?_
    rw [hwsol, ellipticOp_sub b _ _ _ h2 h2', BoundedContDiffHolderMap.coe_sub, Pi.sub_apply]
    have e1 := hwsol i g x
    have e2 := hwsol i g' x
    linarith
  -- the remainder operator
  set Rf : A.HolderMap 0 r ℝ → M → ℝ := fun h y =>
    ∑ i, pushforward (A.chart i) (remainder b (a i) (β i) (ψ i) (wsol i (h.rep i))) y with hRf
  have hRel : ∀ h : A.HolderMap 0 r ℝ, ∃ Rh : A.HolderMap 0 r ℝ,
      ⇑Rh = Rf h ∧ ‖Rh‖ ≤ 1 / 2 * ‖h‖ := by
    intro h
    have hone : ∀ i, ∃ W : A.HolderMap 0 r ℝ,
        ⇑W = pushforward (A.chart i) (remainder b (a i) (β i) (ψ i) (wsol i (h.rep i))) ∧
          ‖W‖ ≤ |Cp0 i| * Cs * Q i * ε * ‖h‖ := by
      intro i
      have hΛ : 0 ≤ Λ := nonneg_of_isEllipticCoeff (ha i)
      have hK₁ : 0 ≤ K₁ i := (norm_nonneg _).trans (hb1 i 0)
      have hK₂ : 0 ≤ K₂ i := (ContinuousLinearMap.opNorm_nonneg _).trans (hb2 i 0)
      set w := wsol i (h.rep i) with hw
      set N := ‖h.rep i‖ with hN
      have hN0 : 0 ≤ N := norm_nonneg _
      obtain ⟨s0, s1, d0, d1⟩ := hsmall (a i) (β i) (c i) (ha i) (hβc i) (hc i) t ht1 w
        (h.rep i) (hwsol i (h.rep i))
      set X := Cs * ε * N with hX
      have hX0 : 0 ≤ X := by positivity
      have hsup := abs_remainder_le b (a i) (β i) (ha i).bound (hβc i).bound_β (hb1 i) (hb2 i)
        s0 d0
      have hhol := abs_remainder_sub_le' b r.coe_nonneg hr1' (hK₃0 i) (a i) (β i) (ha i).bound
        (ha i).holder (hβc i).bound_β (hβc i).holder_β (hb1 i) (hb2 i) (hb1L i) (hb2L i) s0 s1
        d0 d1
      set FR := X * coeffZero d Λ (K₁ i) (K₂ i) + 2 * d * (Λ * K₁ i * X) with hFR
      set MR := X * coeffZero d Λ (K₁ i) (K₂ i) + X * coeffOne d Λ (K₁ i) (K₂ i) (K₃ i) +
        2 * d * ((K₂ i + 2 * K₁ i) * X * Λ + K₁ i * X * Λ + K₁ i * X * Λ) with hMR
      have hd0 : 0 ≤ d := Nat.cast_nonneg _
      have hP0 : 0 ≤ coeffZero d Λ (K₁ i) (K₂ i) := by
        rw [coeffZero]
        exact add_nonneg (mul_nonneg (mul_nonneg hd0 hΛ) hK₂) (mul_nonneg hK₁ hΛ)
      have hP1 : 0 ≤ coeffOne d Λ (K₁ i) (K₂ i) (K₃ i) := by
        rw [coeffOne]
        have := hK₃0 i
        refine add_nonneg (mul_nonneg hd0 (add_nonneg (mul_nonneg hΛ hK₂)
          (mul_nonneg hΛ (by linarith)))) (add_nonneg (mul_nonneg (by linarith) hΛ)
          (mul_nonneg hK₁ hΛ))
      have hMR0 : 0 ≤ MR := by
        rw [hMR]
        refine add_nonneg (add_nonneg (mul_nonneg hX0 hP0) (mul_nonneg hX0 hP1))
          (mul_nonneg (mul_nonneg (by norm_num) hd0) ?_)
        refine add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by linarith) hX0) hΛ)
          (mul_nonneg (mul_nonneg hK₁ hX0) hΛ)) (mul_nonneg (mul_nonneg hK₁ hX0) hΛ)
      set Rz := ofHolderZero hr0 (remainder b (a i) (β i) (ψ i) w) hsup hMR0 hhol with hRz
      have hRzt : tsupport ⇑Rz ⊆ tsupport (ψ i) := tsupport_remainder_subset b _ _ _ _
      obtain ⟨W, hW, hWn⟩ := hCp0 i Rz hRzt
      refine ⟨W, hW, ?_⟩
      have hRzn := norm_ofHolderZero_le hr0 (remainder b (a i) (β i) (ψ i) w) hsup hMR0 hhol
      have hFM : FR + MR ≤ X * Q i := by
        rw [hFR, hMR, hQ]
        refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left (le_abs_self _) hX0)
        ring
      have hNh : N ≤ ‖h‖ := norm_rep_le h i
      calc ‖W‖ ≤ Cp0 i * ‖Rz‖ := hWn
        _ ≤ |Cp0 i| * ‖Rz‖ := mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
        _ ≤ |Cp0 i| * (X * Q i) := mul_le_mul_of_nonneg_left (hRzn.trans hFM) (abs_nonneg _)
        _ = |Cp0 i| * Cs * Q i * ε * N := by rw [hX]; ring
        _ ≤ |Cp0 i| * Cs * Q i * ε * ‖h‖ := by
            apply mul_le_mul_of_nonneg_left hNh; positivity
    choose W hW hWn using hone
    refine ⟨∑ i, W i, ?_, ?_⟩
    · funext y
      have hc' : ⇑(∑ i, W i) = ∑ i, ⇑(W i) :=
        map_sum (HolderAtlas.HolderMap.coeAddHom (A := A) (k := 0) (r := r) (F := ℝ)) W
          Finset.univ
      rw [hc', Finset.sum_apply, hRf]
      simp only [hW]
    · refine (norm_sum_le _ _).trans ?_
      calc ∑ i, ‖W i‖ ≤ ∑ i, |Cp0 i| * Cs * Q i * ε * ‖h‖ := Finset.sum_le_sum fun i _ => hWn i
        _ = Θ * ε * ‖h‖ := by rw [hΘ, Finset.sum_mul, Finset.sum_mul]
        _ ≤ 1 / 2 * ‖h‖ := mul_le_mul_of_nonneg_right hΘε (norm_nonneg _)
  choose Rel hRelf hReln using hRel
  -- additivity of the remainder operator
  have hRelsub : ∀ h h' : A.HolderMap 0 r ℝ, Rel (h - h') = Rel h - Rel h' := by
    intro h h'
    ext y
    rw [HolderAtlas.HolderMap.coe_sub, Pi.sub_apply, hRelf, hRelf, hRelf, hRf]
    simp only
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← pushforward_sub]
    congr 1
    funext z
    rw [rep_sub, hwsub i]
    exact remainder_sub b _ _ _
      ((WholeSpaceSolvability.contDiff_two _).differentiable (by norm_num))
      ((WholeSpaceSolvability.contDiff_two _).differentiable (by norm_num)) z
  -- the fixed point of `h ↦ f - R h`
  set Φ : A.HolderMap 0 r ℝ → A.HolderMap 0 r ℝ := fun h => f - Rel h with hΦ
  have hΦc : ContractingWith (1 / 2 : ℝ≥0) Φ := by
    refine ⟨by rw [← NNReal.coe_lt_coe]; norm_num, LipschitzWith.of_dist_le_mul fun h h' => ?_⟩
    rw [dist_eq_norm, dist_eq_norm]
    have e : Φ h - Φ h' = Rel (h' - h) := by
      rw [hΦ, hRelsub]; exact sub_sub_sub_cancel_left _ _ _
    rw [e]
    calc ‖Rel (h' - h)‖ ≤ 1 / 2 * ‖h' - h‖ := hReln _
      _ = ((1 / 2 : ℝ≥0) : ℝ) * ‖h - h'‖ := by rw [norm_sub_rev]; norm_num
  set hs := ContractingWith.fixedPoint Φ hΦc with hhs
  have hfix : f - Rel hs = hs := ContractingWith.fixedPoint_isFixedPt hΦc
  -- the solution `u = ∑_i push_i(ψ_i w_i)`
  have hU2 : ∀ i, ∃ W : A.HolderMap 2 r ℝ,
      ⇑W = pushforward (A.chart i) (fun z => ψ i z * wsol i (hs.rep i) z) := by
    intro i
    obtain ⟨v, hv⟩ := exists_mul_cutoff hr1' (hψs i) (hψc i) (wsol i (hs.rep i))
    have hvt : tsupport ⇑v ⊆ tsupport (ψ i) := by rw [hv]; exact tsupport_mul_subset_left
    obtain ⟨W, hW, -⟩ := hCp2 i v hvt
    exact ⟨W, by rw [hW, hv]⟩
  choose Wu hWu using hU2
  refine ⟨∑ i, Wu i, fun j z hz => ?_⟩
  have hcu : ⇑(∑ i, Wu i) = ∑ i, ⇑(Wu i) :=
    map_sum (HolderAtlas.HolderMap.coeAddHom (A := A) (k := 2) (r := r) (F := ℝ)) Wu Finset.univ
  -- `L` of each piece, by realizability
  choose g hg using fun i => hreal (Wu i)
  have hpiece : ∀ i y, g i y = A.χ i y * hs y + μ * Wu i y +
      pushforward (A.chart i) (remainder b (a i) (β i) (ψ i) (wsol i (hs.rep i))) y := by
    intro i y
    refine eq_push_identity b hKU hUt i (contDiff_infty.1 (hψs i) 2)
      (WholeSpaceSolvability.contDiff_two _) (hψc i) le_rfl (hψU i) (hψ1 i) hs (μ := μ)
      (fun x => ?_) (Wu i) (hWu i) (g i) (hg i) y
    rw [← htt, hwsol i (hs.rep i) x, coe_rep]
  -- sum over the pieces
  set ej := A.chart j with hej
  have hzt : z ∈ ej.val.target := hUt j hz
  have hsum : ellipticOp b (a j) (β j) (c j) (fun w => (∑ i, Wu i) (ej.val.symm w)) z =
      ∑ i, g i (ej.val.symm z) := by
    have hfun : (fun w => (∑ i, Wu i) (ej.val.symm w)) =
        fun w => ∑ i, Wu i (ej.val.symm w) := by
      funext w; rw [hcu, Finset.sum_apply]
    rw [hfun, ellipticOp_finset_sum b _ _ _ Finset.univ (fun i w => Wu i (ej.val.symm w))
      fun i _ => ?_]
    · exact Finset.sum_congr rfl fun i _ => (hg i j z hz).symm
    · obtain ⟨v, hv⟩ := ManifoldMaxPrinciple.exists_local_rep hr1' (Wu i) ej hzt
      exact (WholeSpaceSolvability.contDiff_two v).contDiffAt.congr_of_eventuallyEq hv.symm
  rw [hsum]
  simp only [hpiece]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, A.sum_eq_one, one_mul,
    ← Finset.mul_sum]
  have hRs : ∑ i, pushforward (A.chart i) (remainder b (a i) (β i) (ψ i) (wsol i (hs.rep i)))
      (ej.val.symm z) = Rel hs (ej.val.symm z) := by
    rw [hRelf, hRf]
  have hfs : f (ej.val.symm z) = hs (ej.val.symm z) + Rel hs (ej.val.symm z) := by
    have := congrArg (fun F : A.HolderMap 0 r ℝ => F (ej.val.symm z)) hfix
    simp only [HolderAtlas.HolderMap.coe_sub, Pi.sub_apply] at this
    linarith
  rw [hRs, hfs, hcu, Finset.sum_apply]
  ring

end Manifold

end SGPT.Foundations.Analysis.Pending.ManifoldParametrix
