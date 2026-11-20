import SGPT.Foundations.Analysis.Pending.BoundedContDiffHolderMapBilinear
import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false

/-!
# Composition with smooth maps in `C^{k,r}_b`

Let `0 ≤ r ≤ 1`.  For a map `τ : E' → E` of class `C^{k+1}` whose derivatives `Dⁱ τ`,
`1 ≤ i ≤ k + 1`, are bounded (no bound on `τ` itself), composition `g ↦ g ∘ τ` is a bounded
linear operator `C^{k,r}_b(E, F) → C^{k,r}_b(E', F)` (`BoundedContDiffHolderMap.compCLM`).
The localized form (`exists_smul_comp_of_contDiffOn`): if `τ` is only `C^{k+1}` on an open set
`U ⊆ E'` and `σ` is a `C^{k+1}` cut-off with compact support in `U` (`E'` finite-dimensional),
then `x ↦ σ x • g (τ x)` lies in `C^{k,r}_b(E', F)` with norm `≤ C ‖g‖`.  This is the form used
for the chart transitions of a compact manifold.

The proof avoids the Faà di Bruno formula.  It is an induction on `k` through the derivative:
`f ∈ C^{k+1,r}_b` iff `f` is bounded and `D f ∈ C^{k,r}_b(E, E →L F)`
(`BoundedContDiffHolderMap.fderivMap`, `BoundedContDiffHolderMap.ofFDeriv`), and
`D (g ∘ τ) = B ((D g) ∘ τ, D τ)` for the composition `B = compL`, so the induction hypothesis
(applied to `D g`) and the product estimate `norm_bilinear_le` give the step.  The base case
`k = 0` is `[g ∘ τ]_r ≤ [g]_r Lip(τ) ^ r`.

## Main definitions and results

* `BoundedContDiffHolderMap.ofContDiff`: a `C^{k+1}` map with bounded derivatives up to order
  `k + 1` lies in `C^{k,r}_b` (`r ≤ 1`), with norm `≤ (k + 3) M`; `ofHasCompactSupport`.
* `BoundedContDiffHolderMap.fderivMap`: `D : C^{k+1,r}_b(E, F) → C^{k,r}_b(E, E →L[ℝ] F)`,
  `‖D f‖ ≤ ‖f‖`; `ofFDeriv`: the converse construction, `‖f‖ ≤ ‖f‖_∞ + ‖D f‖`.
* `BoundedContDiffHolderMap.exists_comp`: the composition estimate; `comp`, `compCLM`.
* `BoundedContDiffHolderMap.exists_smul_comp_of_contDiffOn`: the localized composition.

## Implementation notes

The induction changes the target space `F` into `E →L[ℝ] F`, so the composition results are
stated for `E` and `F` in one universe.

Part of the linear track `L1` of the plan for Yau's theorem.
-/

noncomputable section

open Set Filter Topology Metric Function
open scoped NNReal ContDiff Manifold

universe u

namespace HolderWith

variable {X Y Z : Type*}

/-- A map with `dist (f x) (f y) ≤ A` and `dist (f x) (f y) ≤ A * dist x y` is `(A, r)`-Hölder
for `r ≤ 1`. -/
theorem of_dist_le_of_le_mul [PseudoMetricSpace X] [PseudoMetricSpace Y] {f : X → Y}
    {r : ℝ≥0} (hr : r ≤ 1) {A : ℝ≥0} (h1 : ∀ x y, dist (f x) (f y) ≤ A)
    (h2 : ∀ x y, dist (f x) (f y) ≤ A * dist x y) : HolderWith A r f := by
  refine HolderWith.of_dist_le fun x y => ?_
  have hd := dist_nonneg (x := x) (y := y)
  rcases le_total (dist x y) 1 with hd1 | hd1
  · exact (h2 x y).trans (mul_le_mul_of_nonneg_left
      (Real.self_le_rpow_of_le_one hd hd1 (by exact_mod_cast hr)) A.coe_nonneg)
  · exact (h1 x y).trans (le_mul_of_one_le_right A.coe_nonneg (Real.one_le_rpow hd1 r.coe_nonneg))

/-- Post-composition with an isometry preserves Hölder constants. -/
theorem comp_isometry [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]
    {C r : ℝ≥0} {g : X → Y} {e : Y → Z} (he : Isometry e) (h : HolderWith C r g) :
    HolderWith C r (e ∘ g) := fun x y => by
  simpa only [comp_apply, he.edist_eq] using h x y

end HolderWith

namespace SGPT.Foundations.Analysis.Pending.BoundedContDiffHolderMap

/-- Finitely many bounds give one bound. -/
private theorem exists_forall_le_of_forall_exists {N : ℕ} {P : ℕ → ℝ → Prop}
    (hP : ∀ i C C', C ≤ C' → P i C → P i C') (h : ∀ i ≤ N, ∃ C, P i C) :
    ∃ M, ∀ i ≤ N, P i M := by
  induction N with
  | zero =>
    obtain ⟨C, hC⟩ := h 0 le_rfl
    exact ⟨C, fun i hi => by rw [Nat.le_zero.1 hi]; exact hC⟩
  | succ N ih =>
    obtain ⟨M, hM⟩ := ih fun i hi => h i (hi.trans (Nat.le_succ N))
    obtain ⟨C, hC⟩ := h (N + 1) le_rfl
    refine ⟨max M C, fun i hi => ?_⟩
    rcases Nat.lt_or_eq_of_le hi with hi | rfl
    · exact hP i M _ (le_max_left _ _) (hM i (Nat.lt_succ_iff.1 hi))
    · exact hP _ C _ (le_max_right _ _) hC

/-- A map whose derivatives up to order `N` are continuous with compact support has a common
bound for them. -/
theorem exists_bound_iteratedFDeriv_of_hasCompactSupport {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {N : ℕ}
    (hf : ContDiff ℝ N f) (hc : HasCompactSupport f) :
    ∃ M, ∀ i ≤ N, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ M :=
  exists_forall_le_of_forall_exists (P := fun i C => ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ C)
    (fun _ _ _ hCC' hC x => (hC x).trans hCC') fun i hi =>
      (hc.iteratedFDeriv i).exists_bound_of_continuous
        (hf.continuous_iteratedFDeriv (by exact_mod_cast hi))

variable {k : ℕ} {r : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A copy of `f` with a new underlying map equal to the old one (to control definitional
equalities). -/
def copy (f : BoundedContDiffHolderMap k r E F) (g : E → F) (h : g = ⇑f) :
    BoundedContDiffHolderMap k r E F where
  toFun := g
  contDiff' := h ▸ f.contDiff
  bounded' := h ▸ fun _ hi => f.bounded hi
  memHolder' := h ▸ f.memHolder

@[simp]
theorem coe_copy (f : BoundedContDiffHolderMap k r E F) (g : E → F) (h : g = ⇑f) :
    ⇑(f.copy g h) = g :=
  rfl

theorem copy_eq (f : BoundedContDiffHolderMap k r E F) (g : E → F) (h : g = ⇑f) :
    f.copy g h = f :=
  ext fun x => congrFun h x

/-! ### Smooth maps with bounded derivatives -/

/-- For `r ≤ 1`, the `k`-th derivative of a `C^{k+1}` map with `‖Dⁱ f‖ ≤ M` (`i ≤ k + 1`) is
`(2M, r)`-Hölder. -/
theorem holderWith_iteratedFDeriv_of_bound (hr : r ≤ 1) {f : E → F}
    (hf : ContDiff ℝ (k + 1 : ℕ) f) {M : ℝ}
    (hM : ∀ i ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ M) :
    HolderWith (Real.toNNReal (2 * M)) r (iteratedFDeriv ℝ k f) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Nat.zero_le _) 0)
  have hA : ((Real.toNNReal (2 * M) : ℝ≥0) : ℝ) = 2 * M := Real.coe_toNNReal _ (by positivity)
  refine HolderWith.of_dist_le_of_le_mul hr (fun x y => ?_) (fun x y => ?_)
  · rw [hA, dist_eq_norm]
    refine (norm_sub_le _ _).trans ?_
    linarith [hM k (Nat.le_succ k) x, hM k (Nat.le_succ k) y]
  · rw [hA, dist_eq_norm, dist_eq_norm, ← norm_neg, neg_sub, ← norm_neg (x - y), neg_sub]
    refine (Convex.norm_image_sub_le_of_norm_fderiv_le (s := univ) (C := M)
      (fun z _ => hf.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self k) z)
      (fun z _ => ?_) convex_univ (mem_univ _) (mem_univ _)).trans ?_
    · rw [norm_fderiv_iteratedFDeriv]
      exact hM (k + 1) le_rfl z
    · exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

/-- A `C^{k+1}` map with `‖Dⁱ f‖ ≤ M` for `i ≤ k + 1` lies in `C^{k,r}_b` (`r ≤ 1`). -/
def ofContDiff (hr : r ≤ 1) (f : E → F) (hf : ContDiff ℝ (k + 1 : ℕ) f) {M : ℝ}
    (hM : ∀ i ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ M) : BoundedContDiffHolderMap k r E F where
  toFun := f
  contDiff' := hf.of_le (by exact_mod_cast Nat.le_succ k)
  bounded' i hi := ⟨M, hM i (hi.trans (Nat.le_succ k))⟩
  memHolder' := (holderWith_iteratedFDeriv_of_bound hr hf hM).memHolder

@[simp]
theorem coe_ofContDiff (hr : r ≤ 1) (f : E → F) (hf : ContDiff ℝ (k + 1 : ℕ) f) {M : ℝ}
    (hM : ∀ i ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ M) : ⇑(ofContDiff hr f hf hM) = f :=
  rfl

/-- `‖f‖_{k,r} ≤ (k + 3) M` for a `C^{k+1}` map with `‖Dⁱ f‖ ≤ M`, `i ≤ k + 1`. -/
theorem norm_ofContDiff_le (hr : r ≤ 1) (f : E → F) (hf : ContDiff ℝ (k + 1 : ℕ) f) {M : ℝ}
    (hM : ∀ i ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ M) :
    ‖ofContDiff hr f hf hM‖ ≤ (k + 3) * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Nat.zero_le _) 0)
  set g := ofContDiff hr f hf hM with hg
  have hD : ∀ i ≤ k, ‖g.iteratedFDerivBCF i‖ ≤ M := fun i hi =>
    (BoundedContinuousFunction.norm_le hM0).2 fun x => by
      rw [coe_iteratedFDerivBCF _ hi]
      exact hM i (hi.trans (Nat.le_succ k)) x
  have hH : ‖g.iteratedFDerivHolder‖ ≤ M + 2 * M := by
    have h := g.iteratedFDerivHolder.norm_le_of_holderWith
      (C := Real.toNNReal (2 * M)) (by
        rw [coe_iteratedFDerivHolder]
        exact holderWith_iteratedFDeriv_of_bound hr hf hM)
    rw [iteratedFDerivHolder_toBoundedContinuousFunction,
      Real.coe_toNNReal _ (by positivity)] at h
    linarith [hD k le_rfl]
  have hS : ∑ i ∈ Finset.range k, ‖g.iteratedFDerivBCF i‖ ≤ k * M := by
    refine (Finset.sum_le_sum fun i hi => hD i (Finset.mem_range.1 hi).le).trans_eq ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [norm_def]
  linarith

/-- A `C^{k+1}` map with compact support lies in `C^{k,r}_b` (`r ≤ 1`). -/
def ofHasCompactSupport (hr : r ≤ 1) (f : E → F) (hf : ContDiff ℝ (k + 1 : ℕ) f)
    (hc : HasCompactSupport f) : BoundedContDiffHolderMap k r E F :=
  ofContDiff hr f hf (exists_bound_iteratedFDeriv_of_hasCompactSupport hf hc).choose_spec

@[simp]
theorem coe_ofHasCompactSupport (hr : r ≤ 1) (f : E → F) (hf : ContDiff ℝ (k + 1 : ℕ) f)
    (hc : HasCompactSupport f) : ⇑(ofHasCompactSupport hr f hf hc) = f :=
  rfl

/-! ### The derivative -/

theorem contDiff_fderiv (f : BoundedContDiffHolderMap (k + 1) r E F) :
    ContDiff ℝ k (fderiv ℝ f) :=
  f.contDiff.fderiv_right (by push_cast; exact le_rfl)

/-- `Dᵏ (D f) = (curry) ∘ Dᵏ⁺¹ f`. -/
theorem iteratedFDeriv_fderiv_eq (f : E → F) (k : ℕ) :
    iteratedFDeriv ℝ k (fderiv ℝ f) =
      (continuousMultilinearCurryRightEquiv' ℝ k E F) ∘ iteratedFDeriv ℝ (k + 1) f := by
  funext x
  rw [comp_apply, iteratedFDeriv_succ_eq_comp_right, comp_apply,
    LinearIsometryEquiv.apply_symm_apply]

/-- The derivative `D f ∈ C^{k,r}_b(E, E →L[ℝ] F)` of `f ∈ C^{k+1,r}_b(E, F)`. -/
def fderivMap (f : BoundedContDiffHolderMap (k + 1) r E F) :
    BoundedContDiffHolderMap k r E (E →L[ℝ] F) where
  toFun := fderiv ℝ f
  contDiff' := f.contDiff_fderiv
  bounded' i hi := by
    obtain ⟨C, hC⟩ := f.bounded (Nat.succ_le_succ hi)
    exact ⟨C, fun x => by rw [norm_iteratedFDeriv_fderiv]; exact hC x⟩
  memHolder' := by
    rw [iteratedFDeriv_fderiv_eq]
    exact (f.memHolder.holderWith.comp_isometry (LinearIsometryEquiv.isometry _)).memHolder

@[simp]
theorem coe_fderivMap (f : BoundedContDiffHolderMap (k + 1) r E F) :
    ⇑f.fderivMap = fderiv ℝ f :=
  rfl

/-- `‖D f‖_{k,r} ≤ ‖f‖_{k+1,r}`. -/
theorem norm_fderivMap_le (f : BoundedContDiffHolderMap (k + 1) r E F) :
    ‖f.fderivMap‖ ≤ ‖f‖ := by
  have hD : ∀ i ≤ k, ‖f.fderivMap.iteratedFDerivBCF i‖ ≤ ‖f.iteratedFDerivBCF (i + 1)‖ :=
    fun i hi => (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun x => by
      rw [coe_iteratedFDerivBCF _ hi, coe_fderivMap, norm_iteratedFDeriv_fderiv,
        ← coe_iteratedFDerivBCF f (Nat.succ_le_succ hi)]
      exact BoundedContinuousFunction.norm_coe_le_norm _ x
  have hH : ‖f.fderivMap.iteratedFDerivHolder‖ ≤ ‖f.iteratedFDerivHolder‖ := by
    have h := f.iteratedFDerivHolder.holderWith
    rw [coe_iteratedFDerivHolder] at h
    have h1 := f.fderivMap.iteratedFDerivHolder.norm_le_of_holderWith
      (C := nnHolderNorm r (iteratedFDeriv ℝ (k + 1) f)) (by
        rw [coe_iteratedFDerivHolder, coe_fderivMap, iteratedFDeriv_fderiv_eq]
        exact h.comp_isometry (LinearIsometryEquiv.isometry _))
    rw [iteratedFDerivHolder_toBoundedContinuousFunction] at h1
    rw [BoundedHolderMap.norm_def f.iteratedFDerivHolder,
      iteratedFDerivHolder_toBoundedContinuousFunction, coe_iteratedFDerivHolder]
    linarith [hD k le_rfl]
  rw [norm_def, norm_def, Finset.sum_range_succ']
  have := Finset.sum_le_sum fun i (hi : i ∈ Finset.range k) => hD i (Finset.mem_range.1 hi).le
  linarith [norm_nonneg (f.iteratedFDerivBCF 0)]

/-- A bounded differentiable map whose derivative lies in `C^{k,r}_b(E, E →L[ℝ] F)` lies in
`C^{k+1,r}_b(E, F)`. -/
def ofFDeriv (f : E → F) (hf : Differentiable ℝ f)
    (G : BoundedContDiffHolderMap k r E (E →L[ℝ] F)) (hG : fderiv ℝ f = ⇑G) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) : BoundedContDiffHolderMap (k + 1) r E F where
  toFun := f
  contDiff' := by
    have h : ContDiff ℝ ((k : WithTop ℕ∞) + 1) f :=
      contDiff_succ_iff_fderiv.2 ⟨hf, by simp, hG ▸ G.contDiff⟩
    exact_mod_cast h
  bounded' i hi := by
    cases i with
    | zero => exact ⟨C, fun x => by rw [norm_iteratedFDeriv_zero]; exact hC x⟩
    | succ j =>
      exact ⟨‖G‖, fun x => by
        rw [← norm_iteratedFDeriv_fderiv, hG]
        exact G.norm_iteratedFDeriv_apply_le (Nat.succ_le_succ_iff.1 hi) x⟩
  memHolder' := by
    have h : iteratedFDeriv ℝ (k + 1) f =
        (continuousMultilinearCurryRightEquiv' ℝ k E F).symm ∘ iteratedFDeriv ℝ k G := by
      rw [← hG, iteratedFDeriv_fderiv_eq]
      funext x
      simp
    rw [h]
    exact (G.memHolder.holderWith.comp_isometry (LinearIsometryEquiv.isometry _)).memHolder

@[simp]
theorem coe_ofFDeriv (f : E → F) (hf : Differentiable ℝ f)
    (G : BoundedContDiffHolderMap k r E (E →L[ℝ] F)) (hG : fderiv ℝ f = ⇑G) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) : ⇑(ofFDeriv f hf G hG hC) = f :=
  rfl

/-- `‖f‖_{k+1,r} ≤ C + ‖D f‖_{k,r}` when `‖f‖_∞ ≤ C`. -/
theorem norm_ofFDeriv_le (f : E → F) (hf : Differentiable ℝ f)
    (G : BoundedContDiffHolderMap k r E (E →L[ℝ] F)) (hG : fderiv ℝ f = ⇑G) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) : ‖ofFDeriv f hf G hG hC‖ ≤ C + ‖G‖ := by
  set g := ofFDeriv f hf G hG hC with hg
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have h0 : ‖g.iteratedFDerivBCF 0‖ ≤ C :=
    (BoundedContinuousFunction.norm_le hC0).2 fun x => by
      rw [coe_iteratedFDerivBCF _ (Nat.zero_le _), norm_iteratedFDeriv_zero]
      exact hC x
  have hD : ∀ i ≤ k, ‖g.iteratedFDerivBCF (i + 1)‖ ≤ ‖G.iteratedFDerivBCF i‖ :=
    fun i hi => (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun x => by
      rw [coe_iteratedFDerivBCF _ (Nat.succ_le_succ hi), hg, coe_ofFDeriv,
        ← norm_iteratedFDeriv_fderiv, hG, ← coe_iteratedFDerivBCF G hi]
      exact BoundedContinuousFunction.norm_coe_le_norm _ x
  have hH : ‖g.iteratedFDerivHolder‖ ≤ ‖G.iteratedFDerivHolder‖ := by
    have h := G.iteratedFDerivHolder.holderWith
    rw [coe_iteratedFDerivHolder] at h
    have he : iteratedFDeriv ℝ (k + 1) f =
        (continuousMultilinearCurryRightEquiv' ℝ k E F).symm ∘ iteratedFDeriv ℝ k G := by
      rw [← hG, iteratedFDeriv_fderiv_eq]
      funext x
      simp
    have h1 := g.iteratedFDerivHolder.norm_le_of_holderWith
      (C := nnHolderNorm r (iteratedFDeriv ℝ k G)) (by
        rw [coe_iteratedFDerivHolder, hg, coe_ofFDeriv, he]
        exact h.comp_isometry (LinearIsometryEquiv.isometry _))
    rw [iteratedFDerivHolder_toBoundedContinuousFunction] at h1
    rw [BoundedHolderMap.norm_def G.iteratedFDerivHolder,
      iteratedFDerivHolder_toBoundedContinuousFunction, coe_iteratedFDerivHolder]
    linarith [hD k le_rfl]
  rw [norm_def, norm_def, Finset.sum_range_succ']
  have := Finset.sum_le_sum fun i (hi : i ∈ Finset.range k) => hD i (Finset.mem_range.1 hi).le
  linarith

/-! ### Composition -/

section Comp

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- **Composition estimate.** For `r ≤ 1` and `τ : E' → E` of class `C^{k+1}` with bounded
derivatives `Dⁱ τ`, `1 ≤ i ≤ k + 1`, there is `C` with `g ∘ τ ∈ C^{k,r}_b(E', F)` and
`‖g ∘ τ‖ ≤ C ‖g‖` for every `g ∈ C^{k,r}_b(E, F)`. -/
theorem exists_comp (hr : r ≤ 1) {τ : E' → E} (hτ : ContDiff ℝ (k + 1 : ℕ) τ)
    (hτb : ∀ i, 1 ≤ i → i ≤ k + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ i τ x‖ ≤ C) :
    ∃ C, ∀ g : BoundedContDiffHolderMap k r E F,
      ∃ h : BoundedContDiffHolderMap k r E' F, ⇑h = g ∘ τ ∧ ‖h‖ ≤ C * ‖g‖ := by
  induction k generalizing F with
  | zero =>
    obtain ⟨L, hL⟩ := hτb 1 le_rfl le_rfl
    have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
    have hlip : LipschitzWith (Real.toNNReal L) τ :=
      lipschitzWith_of_nnnorm_fderiv_le (hτ.differentiable (by simp)) fun x => by
        rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hL0, ← norm_iteratedFDeriv_one]
        exact hL x
    refine ⟨1 + (Real.toNNReal L : ℝ) ^ (r : ℝ), fun g => ?_⟩
    -- the Hölder constant of `g ∘ τ`
    have hg0 : HolderWith (nnHolderNorm r (iteratedFDeriv ℝ 0 g)) r g := by
      have h := g.iteratedFDerivHolder.holderWith
      rw [coe_iteratedFDerivHolder] at h
      have h' := h.comp_isometry (continuousMultilinearCurryFin0 ℝ E F).isometry
      have he : (continuousMultilinearCurryFin0 ℝ E F) ∘ iteratedFDeriv ℝ 0 g = ⇑g := by
        funext x; simp
      rwa [he] at h'
    have hgτ := (hg0.comp (holderWith_one.2 hlip))
    rw [mul_one] at hgτ
    have hgτ' : HolderWith (nnHolderNorm r (iteratedFDeriv ℝ 0 g) * Real.toNNReal L ^ (r : ℝ)) r
        (iteratedFDeriv ℝ 0 (g ∘ τ)) := by
      have h' := hgτ.comp_isometry (continuousMultilinearCurryFin0 ℝ E' F).symm.isometry
      have he : (continuousMultilinearCurryFin0 ℝ E' F).symm ∘ (g ∘ τ) =
          iteratedFDeriv ℝ 0 (g ∘ τ) := by
        funext x; simp [iteratedFDeriv_zero_eq_comp]
      rwa [he] at h'
    let h : BoundedContDiffHolderMap 0 r E' F :=
      { toFun := g ∘ τ
        contDiff' := g.contDiff.comp (hτ.of_le (by simp))
        bounded' := fun i hi => ⟨‖g‖, fun x => by
          rw [Nat.le_zero.1 hi, norm_iteratedFDeriv_zero]
          exact g.norm_apply_le (τ x)⟩
        memHolder' := hgτ'.memHolder }
    refine ⟨h, rfl, ?_⟩
    have hB : ‖h.iteratedFDerivBCF 0‖ ≤ ‖g.iteratedFDerivBCF 0‖ :=
      (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun x => by
        rw [coe_iteratedFDerivBCF _ le_rfl, norm_iteratedFDeriv_zero]
        have := (g.iteratedFDerivBCF 0).norm_coe_le_norm (τ x)
        rwa [coe_iteratedFDerivBCF _ le_rfl, norm_iteratedFDeriv_zero] at this
    have hH : (nnHolderNorm r ⇑h.iteratedFDerivHolder : ℝ) ≤
        nnHolderNorm r (iteratedFDeriv ℝ 0 g) * (Real.toNNReal L : ℝ) ^ (r : ℝ) := by
      rw [coe_iteratedFDerivHolder]
      have := hgτ'.nnholderNorm_le
      exact_mod_cast this
    rw [norm_def, norm_def, Finset.range_zero, Finset.sum_empty, Finset.sum_empty, zero_add,
      zero_add, BoundedHolderMap.norm_def, BoundedHolderMap.norm_def,
      iteratedFDerivHolder_toBoundedContinuousFunction,
      iteratedFDerivHolder_toBoundedContinuousFunction, coe_iteratedFDerivHolder g]
    have hp : 0 ≤ (Real.toNNReal L : ℝ) ^ (r : ℝ) := Real.rpow_nonneg (NNReal.coe_nonneg _) _
    have hn : (0 : ℝ) ≤ nnHolderNorm r (iteratedFDeriv ℝ 0 g) := NNReal.coe_nonneg _
    have hb := norm_nonneg (g.iteratedFDerivBCF 0)
    nlinarith
  | succ k ih =>
    -- bounds for `D τ`
    obtain ⟨M, hM⟩ := exists_forall_le_of_forall_exists (N := k + 1)
      (P := fun i C => ∀ x, ‖iteratedFDeriv ℝ i (fderiv ℝ τ) x‖ ≤ C)
      (fun _ _ _ hCC' hC x => (hC x).trans hCC') fun i hi => by
        obtain ⟨C, hC⟩ := hτb (i + 1) (Nat.le_add_left 1 i) (Nat.succ_le_succ hi)
        exact ⟨C, fun x => by rw [norm_iteratedFDeriv_fderiv]; exact hC x⟩
    have hτ' : ContDiff ℝ (k + 1 : ℕ) (fderiv ℝ τ) :=
      hτ.fderiv_right (by push_cast; exact le_rfl)
    set Dτ : BoundedContDiffHolderMap k r E' (E' →L[ℝ] E) := ofContDiff hr (fderiv ℝ τ) hτ' hM
      with hDτ
    -- induction hypothesis for `D g`
    obtain ⟨C₁, hC₁⟩ := ih (F := E →L[ℝ] F) (hτ.of_le (by exact_mod_cast Nat.le_succ (k + 1)))
      fun i hi1 hi => hτb i hi1 (hi.trans (Nat.le_succ _))
    refine ⟨1 + 2 ^ (k + 3) * |C₁| * ‖Dτ‖, fun g => ?_⟩
    obtain ⟨h₁, hh₁, hh₁n⟩ := hC₁ g.fderivMap
    set B := ContinuousLinearMap.compL ℝ E' E F with hB
    set G := bilinear hr B h₁ Dτ with hG
    have hgd : Differentiable ℝ g := g.contDiff.differentiable (by simp)
    have hτd : Differentiable ℝ τ := hτ.differentiable (by simp)
    have hfd : fderiv ℝ (⇑g ∘ τ) = ⇑G := by
      funext x
      rw [fderiv_comp x (hgd (τ x)) (hτd x), hG, coe_bilinear, hh₁]
      rfl
    refine ⟨ofFDeriv (⇑g ∘ τ) (hgd.comp hτd) G hfd (C := ‖g‖) (fun x => g.norm_apply_le (τ x)),
      rfl, ?_⟩
    refine (norm_ofFDeriv_le _ _ _ _ _).trans ?_
    have hG' := norm_bilinear_le hr B h₁ Dτ
    have hBn := ContinuousLinearMap.norm_compL_le ℝ E' E F
    have hh₁' : ‖h₁‖ ≤ |C₁| * ‖g‖ :=
      hh₁n.trans (mul_le_mul (le_abs_self C₁) g.norm_fderivMap_le (norm_nonneg _)
        (abs_nonneg _))
    have h2 : (0 : ℝ) ≤ 2 ^ (k + 3) := by positivity
    have hD0 := norm_nonneg Dτ
    have hh0 := norm_nonneg h₁
    calc ‖g‖ + ‖G‖ ≤ ‖g‖ + 2 ^ (k + 3) * 1 * (|C₁| * ‖g‖) * ‖Dτ‖ := by
          gcongr
          exact hG'.trans (by gcongr)
      _ = (1 + 2 ^ (k + 3) * |C₁| * ‖Dτ‖) * ‖g‖ := by ring

/-- The composition `g ∘ τ` as an element of `C^{k,r}_b(E', F)` (see `exists_comp`). -/
def comp (hr : r ≤ 1) {τ : E' → E} (hτ : ContDiff ℝ (k + 1 : ℕ) τ)
    (hτb : ∀ i, 1 ≤ i → i ≤ k + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ i τ x‖ ≤ C)
    (g : BoundedContDiffHolderMap k r E F) : BoundedContDiffHolderMap k r E' F :=
  (((exists_comp (F := F) hr hτ hτb).choose_spec g).choose).copy (⇑g ∘ τ)
    (((exists_comp (F := F) hr hτ hτb).choose_spec g).choose_spec.1).symm

@[simp]
theorem coe_comp (hr : r ≤ 1) {τ : E' → E} (hτ : ContDiff ℝ (k + 1 : ℕ) τ)
    (hτb : ∀ i, 1 ≤ i → i ≤ k + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ i τ x‖ ≤ C)
    (g : BoundedContDiffHolderMap k r E F) : ⇑(comp hr hτ hτb g) = ⇑g ∘ τ :=
  rfl

/-- Composition with `τ` as a bounded linear operator `C^{k,r}_b(E, F) →L[ℝ] C^{k,r}_b(E', F)`.
-/
def compCLM (hr : r ≤ 1) {τ : E' → E} (hτ : ContDiff ℝ (k + 1 : ℕ) τ)
    (hτb : ∀ i, 1 ≤ i → i ≤ k + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ i τ x‖ ≤ C) :
    BoundedContDiffHolderMap k r E F →L[ℝ] BoundedContDiffHolderMap k r E' F :=
  LinearMap.mkContinuous
    { toFun := comp hr hτ hτb
      map_add' _ _ := ext fun _ => rfl
      map_smul' _ _ := ext fun _ => rfl }
    (exists_comp (F := F) hr hτ hτb).choose fun g => by
      change ‖comp hr hτ hτb g‖ ≤ _
      rw [comp, copy_eq]
      exact ((exists_comp (F := F) hr hτ hτb).choose_spec g).choose_spec.2

@[simp]
theorem compCLM_apply (hr : r ≤ 1) {τ : E' → E} (hτ : ContDiff ℝ (k + 1 : ℕ) τ)
    (hτb : ∀ i, 1 ≤ i → i ≤ k + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ i τ x‖ ≤ C)
    (g : BoundedContDiffHolderMap k r E F) : compCLM hr hτ hτb g = comp hr hτ hτb g :=
  rfl

/-- **Localized composition.** Let `E'` be finite-dimensional, `U ⊆ E'` open, `τ : E' → E` of
class `C^{k+1}` on `U` and `σ : E' → ℝ` of class `C^{k+1}` with compact support inside `U`.
Then there is `C` such that `x ↦ σ x • g (τ x)` lies in `C^{k,r}_b(E', F)` with norm `≤ C ‖g‖`
for every `g ∈ C^{k,r}_b(E, F)` (`r ≤ 1`).  (Outside `U` the values of `τ` do not matter.) -/
theorem exists_smul_comp_of_contDiffOn [FiniteDimensional ℝ E'] (hr : r ≤ 1) {U : Set E'}
    (hU : IsOpen U) {τ : E' → E} (hτ : ContDiffOn ℝ (k + 1 : ℕ) τ U) {σ : E' → ℝ}
    (hσ : ContDiff ℝ (k + 1 : ℕ) σ) (hσc : HasCompactSupport σ) (hσU : tsupport σ ⊆ U) :
    ∃ C, ∀ g : BoundedContDiffHolderMap k r E F,
      ∃ h : BoundedContDiffHolderMap k r E' F, (∀ x, h x = σ x • g (τ x)) ∧ ‖h‖ ≤ C * ‖g‖ := by
  -- a cut-off `ρ = 1` on `tsupport σ` with compact support in `U`
  obtain ⟨V, hVo, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hσc hU hσU
  obtain ⟨ρ, hρ1, hρV, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior (n := (⊤ : ℕ∞))
    𝓘(ℝ, E') (isClosed_tsupport σ) (by rwa [hVo.interior_eq])
  have hρs : ContDiff ℝ ∞ (ρ : E' → ℝ) := ρ.contMDiff.contDiff
  have hρsupp : support (ρ : E' → ℝ) ⊆ V := fun x hx => by
    by_contra hxV
    exact hx (hρV x hxV)
  have hρc : HasCompactSupport (ρ : E' → ℝ) :=
    HasCompactSupport.of_support_subset_isCompact hVc (hρsupp.trans subset_closure)
  have hρU : tsupport (ρ : E' → ℝ) ⊆ U := (closure_mono hρsupp).trans hVU
  have hρK : ∀ x ∈ tsupport σ, ρ x = 1 := fun x hx => (hρ1.self_of_nhdsSet) x hx
  -- the global map `τ̃ = ρ • τ`
  set τ' : E' → E := fun x => ρ x • τ x with hτ'
  have hτ'c : HasCompactSupport τ' := hρc.smul_right
  have hτ's : ContDiff ℝ (k + 1 : ℕ) τ' := by
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x ∈ U
    · exact (hρs.of_le (by exact_mod_cast le_top)).contDiffAt.smul
        (hτ.contDiffAt (hU.mem_nhds hx))
    · have hx' : x ∉ tsupport (ρ : E' → ℝ) := fun h => hx (hρU h)
      have h0 : τ' =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
        simp only [hτ', hy, Pi.zero_apply, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq h0
  obtain ⟨M, hM⟩ := exists_bound_iteratedFDeriv_of_hasCompactSupport hτ's hτ'c
  obtain ⟨C₁, hC₁⟩ := exists_comp (F := F) hr hτ's fun i _ hi => ⟨M, hM i hi⟩
  -- `σ` in `C^{k,r}_b(E', ℝ)`
  set σ' : BoundedContDiffHolderMap k r E' ℝ := ofHasCompactSupport hr σ hσ hσc with hσ'
  refine ⟨2 ^ (k + 3) * ‖σ'‖ * |C₁|, fun g => ?_⟩
  obtain ⟨h₁, hh₁, hh₁n⟩ := hC₁ g
  set B : ℝ →L[ℝ] F →L[ℝ] F := ContinuousLinearMap.lsmul ℝ ℝ with hB
  refine ⟨bilinear hr B σ' h₁, fun x => ?_, ?_⟩
  · rw [coe_bilinear, hh₁, hσ', coe_ofHasCompactSupport]
    change σ x • g (τ' x) = σ x • g (τ x)
    by_cases hx : σ x = 0
    · rw [hx, zero_smul, zero_smul]
    · rw [hτ']
      change σ x • g (ρ x • τ x) = σ x • g (τ x)
      rw [hρK x (subset_tsupport _ hx), one_smul]
  · refine (norm_bilinear_le hr B σ' h₁).trans ?_
    have hBn : ‖B‖ ≤ 1 := ContinuousLinearMap.opNorm_lsmul_le
    have hh₁' : ‖h₁‖ ≤ |C₁| * ‖g‖ :=
      hh₁n.trans (mul_le_mul_of_nonneg_right (le_abs_self C₁) (norm_nonneg _))
    have hσ0 := norm_nonneg σ'
    have hh0 := norm_nonneg h₁
    calc 2 ^ (k + 3) * ‖B‖ * ‖σ'‖ * ‖h₁‖ ≤ 2 ^ (k + 3) * 1 * ‖σ'‖ * (|C₁| * ‖g‖) := by
          gcongr
      _ = 2 ^ (k + 3) * ‖σ'‖ * |C₁| * ‖g‖ := by ring

end Comp

end SGPT.Foundations.Analysis.Pending.BoundedContDiffHolderMap
