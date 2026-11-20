import SGPT.NAPotential.BJModelGauss
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# `𝔾_m`-invariant valuations are Gauss extensions

Source: [BJ22] (`references/bj22-trivval`), §1.3–§1.4 and §2.2: a valuation `w` of
`ℂ(X)(t)` which is invariant under the `𝔾_m`-action `t ↦ λ t` is *monomial in `t`*,
`w(∑ fᵢ tⁱ) = minᵢ (w(fᵢ) + i w(t))`; hence, normalized by `w(t)`, it is the Gauss extension
`σ(v)` (the book's `eq:Gext`) of its restriction `v` to `ℂ(X)`. This is how the divisorial
valuations `ord_E` of the components `E` of the central fibre of a (normal) test configuration
are identified with Gauss extensions `b_E σ(v_E)` ([BJ22, §2.2, the definition of `v_E`]), the
input for the Monge–Ampère formula and for the charging of divisorial points (steps R5, R8 of
`claude-bj-model:plan`). Towards `thm:BJappseq` of `chapter_NApotential.tex`. Blueprint:
`claude-bj-model3.tex`, node `claude-bj-model3:invariant-gauss`.

The proof is linear algebra: for `f = ∑_{i ≤ N} fᵢ tⁱ` and `N + 1` distinct `λ_j ∈ ℂ^×`, the
Vandermonde matrix `(λ_jⁱ)` is invertible, so each `fᵢ tⁱ` is a `ℂ`-linear combination of the
`f(λ_j t)`; the ultrametric inequality and `w(f(λ t)) = w(f)` give `w(fᵢ tⁱ) ≥ w(f)`.

## Main results

* `coeff_mul_X_pow_eq_sum_comp`: the Vandermonde decomposition `fᵢ tⁱ = ∑_j u_j f(λ_j t)`;
* `le_val_iff_of_scaleInvariant`: for a `𝔾_m`-invariant `w`,
  `r ≤ w(f) ↔ ∀ i, r ≤ w(fᵢ) + i • w(t)` (monomiality);
* `restrictValuation`: the restriction of a valuation of `K(t)` to `K`;
* `SourceRealValuation.rescale`: positive multiples of a valuation;
* `eq_gaussExtension_of_scaleInvariant`: a `𝔾_m`-invariant valuation with `w(t) = 1` is the
  Gauss extension of its restriction;
* `rescale_eq_gaussExtension_of_scaleInvariant`: for `0 < w(t) = b < ∞`,
  `b⁻¹ w = σ(b⁻¹ w|_K)`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.BJModel3

open Polynomial SGPT.NAPotential.BJModel

variable {K : Type*} [Field K] [Algebra ℂ K]

/-! ### The Vandermonde decomposition -/

/-- The nodes `λ_j = j + 1 ∈ ℂ^×`. -/
def node (n : ℕ) (j : Fin n) : ℂ := (j : ℂ) + 1

theorem node_injective (n : ℕ) : Function.Injective (node n) := by
  intro i j h
  simp only [node, add_left_inj, Nat.cast_inj] at h
  exact Fin.ext h

theorem node_ne_zero (n : ℕ) (j : Fin n) : node n j ≠ 0 := by
  unfold node
  exact_mod_cast Nat.succ_ne_zero j

/-- **The Vandermonde decomposition.** For `f ∈ K[t]` of degree `≤ N` and `i ≤ N` there are
`u_j ∈ ℂ`, `j ≤ N`, with `fᵢ tⁱ = ∑_j u_j f(λ_j t)`, `λ_j = j + 1`. -/
theorem coeff_mul_X_pow_eq_sum_comp (f : K[X]) {N : ℕ} (hN : f.natDegree ≤ N) (i : Fin (N + 1)) :
    ∃ u : Fin (N + 1) → ℂ, C (f.coeff i) * X ^ (i : ℕ) =
      ∑ j, C (algebraMap ℂ K (u j)) * f.comp (C (algebraMap ℂ K (node (N + 1) j)) * X) := by
  classical
  let V : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ := Matrix.vandermonde (node (N + 1))
  have hdet : IsUnit V.det :=
    isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr (node_injective _))
  have hUV : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V hdet
  refine ⟨fun j => V⁻¹ i j, ?_⟩
  ext k
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, comp_C_mul_X_coeff]
  have hsum : ∑ j : Fin (N + 1), algebraMap ℂ K (V⁻¹ i j) *
      (f.coeff k * algebraMap ℂ K (node (N + 1) j) ^ k) =
      f.coeff k * algebraMap ℂ K (∑ j : Fin (N + 1), V⁻¹ i j * node (N + 1) j ^ k) := by
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow]
    ring
  rw [hsum]
  by_cases hk : k ≤ N
  · have hentry : ∑ j : Fin (N + 1), V⁻¹ i j * node (N + 1) j ^ k =
        (V⁻¹ * V) i ⟨k, Nat.lt_succ_of_le hk⟩ := by
      rw [Matrix.mul_apply]
      rfl
    rw [hentry, hUV, Matrix.one_apply]
    by_cases hik : (i : ℕ) = k
    · subst hik
      simp
    · have hne : i ≠ ⟨k, Nat.lt_succ_of_le hk⟩ := fun h => hik (by rw [h])
      simp [hne, Ne.symm hik]
  · have hk' : f.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hN (not_le.mp hk))
    have hik : k ≠ (i : ℕ) := by
      intro h
      exact hk (h ▸ Nat.lt_succ_iff.mp i.2)
    simp [hk', hik]

/-! ### Monomiality of `𝔾_m`-invariant valuations -/

variable (w : SourceRealValuation (FractionRing K[X]))

/-- The map `K[t] → K(t)`. -/
abbrev ι : K[X] →+* FractionRing K[X] := algebraMap K[X] (FractionRing K[X])

/-- **`𝔾_m`-invariance**: `w(f(λ t)) = w(f(t))` for all `λ ∈ ℂ^×` and `f ∈ K[t]`. -/
def IsScaleInvariant : Prop :=
  ∀ c : ℂ, c ≠ 0 → ∀ f : K[X], w (ι (f.comp (C (algebraMap ℂ K c) * X))) = w (ι f)

theorem algebraMap_complex_eq (a : ℂ) :
    algebraMap ℂ (FractionRing K[X]) a = ι (C (algebraMap ℂ K a)) := by
  rw [IsScalarTower.algebraMap_apply ℂ K[X] (FractionRing K[X]), ← Polynomial.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply]

/-- Multiplication by a complex constant does not decrease `w`. -/
theorem val_le_val_C_mul (a : ℂ) (g : K[X]) : w (ι g) ≤ w (ι (C (algebraMap ℂ K a) * g)) := by
  by_cases ha : a = 0
  · rw [ha, map_zero, C_0, zero_mul, map_zero, w.map_zero]
    exact le_top
  · rw [map_mul, w.map_mul', ← algebraMap_complex_eq, w.map_complex' a ha, zero_add]

/-- The ultrametric inequality for finite sums. -/
theorem le_val_sum {ι' : Type*} (s : Finset ι') (g : ι' → FractionRing K[X]) (r : WithTop ℝ)
    (h : ∀ j ∈ s, r ≤ w (g j)) : r ≤ w (∑ j ∈ s, g j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, w.map_zero]
    exact le_top
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (le_min (h a (Finset.mem_insert_self a s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))).trans (w.min_le_map_add' _ _)

/-- **A `𝔾_m`-invariant valuation dominates its monomial terms**: `w(f) ≤ w(fᵢ tⁱ)`. -/
theorem val_le_val_monomial (hw : IsScaleInvariant w) (f : K[X]) (i : ℕ) :
    w (ι f) ≤ w (ι (C (f.coeff i) * X ^ i)) := by
  by_cases hi : f.natDegree < i
  · rw [coeff_eq_zero_of_natDegree_lt hi, C_0, zero_mul, map_zero, w.map_zero]
    exact le_top
  · have hi' : i < f.natDegree + 1 := Nat.lt_succ_of_le (not_lt.mp hi)
    obtain ⟨u, hu⟩ := coeff_mul_X_pow_eq_sum_comp f le_rfl ⟨i, hi'⟩
    change w (ι f) ≤ w (ι (C (f.coeff (⟨i, hi'⟩ : Fin (f.natDegree + 1))) *
      X ^ ((⟨i, hi'⟩ : Fin (f.natDegree + 1)) : ℕ)))
    rw [hu, map_sum]
    refine le_val_sum w _ _ _ fun j _ => ?_
    refine le_of_eq_of_le ?_ (val_le_val_C_mul w (u j) _)
    exact (hw _ (node_ne_zero _ j) f).symm

/-- `w(a tⁱ) = w(a) + i • w(t)`. -/
theorem val_C_mul_X_pow (a : K) (i : ℕ) :
    w (ι (C a * X ^ i)) = w (ι (C a)) + i • w (ι X) := by
  rw [map_mul, w.map_mul', map_pow]
  congr 1
  induction i with
  | zero => rw [pow_zero, zero_smul, w.map_one]
  | succ i ih => rw [pow_succ, w.map_mul', ih, succ_nsmul]

/-- **Monomiality of `𝔾_m`-invariant valuations** ([BJ22, §1.3–§2.2]):
`r ≤ w(∑ fᵢ tⁱ) ↔ ∀ i, r ≤ w(fᵢ) + i • w(t)`, i.e.
`w(∑ fᵢ tⁱ) = minᵢ (w(fᵢ) + i w(t))`. -/
theorem le_val_iff_of_scaleInvariant (hw : IsScaleInvariant w) (f : K[X]) (r : WithTop ℝ) :
    r ≤ w (ι f) ↔ ∀ i : ℕ, r ≤ w (ι (C (f.coeff i))) + i • w (ι X) := by
  constructor
  · intro h i
    rw [← val_C_mul_X_pow]
    exact h.trans (val_le_val_monomial w hw f i)
  · intro h
    conv_rhs => rw [as_sum_support_C_mul_X_pow f, map_sum]
    exact le_val_sum w _ _ _ fun i _ => (val_C_mul_X_pow w _ i).symm ▸ h i

/-! ### Restriction and rescaling -/

omit w in
/-- **The restriction `w|_K`** of a valuation of `K(t)` to `K`. -/
def restrictValuation (w : SourceRealValuation (FractionRing K[X])) : SourceRealValuation K where
  toFun a := w (algebraMap K (FractionRing K[X]) a)
  eq_top_iff' a := by
    rw [w.eq_top_iff', map_eq_zero_iff _ (algebraMap K (FractionRing K[X])).injective]
  map_mul' a b := by rw [map_mul, w.map_mul']
  min_le_map_add' a b := by rw [map_add]; exact w.min_le_map_add' _ _
  map_complex' c hc := by
    rw [← IsScalarTower.algebraMap_apply]
    exact w.map_complex' c hc

theorem restrictValuation_apply (a : K) :
    restrictValuation w a = w (ι (C a)) := by
  change w (algebraMap K (FractionRing K[X]) a) = _
  rw [IsScalarTower.algebraMap_apply K K[X] (FractionRing K[X]), Polynomial.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply]

/-- The map `x ↦ c x` on `(-∞, ∞]` for `c > 0`. -/
def scaleTop (c : ℝ) : WithTop ℝ → WithTop ℝ := WithTop.map (c * ·)

@[simp] theorem scaleTop_top (c : ℝ) : scaleTop c ⊤ = ⊤ := rfl

@[simp] theorem scaleTop_coe (c r : ℝ) : scaleTop c (r : WithTop ℝ) = ((c * r : ℝ) : WithTop ℝ) :=
  rfl

theorem scaleTop_add (c : ℝ) (a b : WithTop ℝ) :
    scaleTop c (a + b) = scaleTop c a + scaleTop c b := by
  cases a with
  | top => simp only [WithTop.top_add, scaleTop_top]
  | coe a =>
    cases b with
    | top => simp only [WithTop.add_top, scaleTop_top]
    | coe b =>
      rw [← WithTop.coe_add, scaleTop_coe, scaleTop_coe, scaleTop_coe, mul_add, WithTop.coe_add]

theorem scaleTop_mono {c : ℝ} (hc : 0 ≤ c) : Monotone (scaleTop c) := by
  intro a b hab
  cases b with
  | top => simp
  | coe b =>
    cases a with
    | top => simp at hab
    | coe a =>
      simp only [scaleTop_coe, WithTop.coe_le_coe]
      exact mul_le_mul_of_nonneg_left (WithTop.coe_le_coe.mp hab) hc

theorem scaleTop_eq_top_iff {c : ℝ} (a : WithTop ℝ) : scaleTop c a = ⊤ ↔ a = ⊤ := by
  cases a with
  | top => simp
  | coe a =>
    rw [scaleTop_coe]
    exact ⟨fun h => absurd h WithTop.coe_ne_top, fun h => absurd h WithTop.coe_ne_top⟩

theorem scaleTop_nsmul (c : ℝ) (i : ℕ) (a : WithTop ℝ) : scaleTop c (i • a) = i • scaleTop c a := by
  induction i with
  | zero => simp [scaleTop]
  | succ i ih => rw [succ_nsmul, scaleTop_add, ih, succ_nsmul]

omit w in
/-- **The positive multiple `c w`** of a valuation (`c > 0`). -/
def _root_.SGPT.NAPotential.SourceRealValuation.rescale {L : Type*} [Field L] [Algebra ℂ L] (v : SourceRealValuation L)
    {c : ℝ} (hc : 0 < c) : SourceRealValuation L where
  toFun x := scaleTop c (v x)
  eq_top_iff' x := by rw [scaleTop_eq_top_iff, v.eq_top_iff']
  map_mul' x y := by rw [v.map_mul', scaleTop_add]
  min_le_map_add' x y := by
    rw [← (scaleTop_mono hc.le).map_min]
    exact scaleTop_mono hc.le (v.min_le_map_add' x y)
  map_complex' z hz := by rw [v.map_complex' z hz]; simp [scaleTop]

theorem _root_.SGPT.NAPotential.SourceRealValuation.rescale_apply {L : Type*} [Field L] [Algebra ℂ L]
    (v : SourceRealValuation L) {c : ℝ} (hc : 0 < c) (x : L) :
    v.rescale hc x = scaleTop c (v x) := rfl

/-! ### Identification with the Gauss extension -/

/-- **A `𝔾_m`-invariant valuation of `K(t)` with `w(t) = 1` is the Gauss extension of its
restriction to `K`** (`eq:Gext`, [BJ22, §1.3]). -/
theorem eq_gaussExtension_of_scaleInvariant (hw : IsScaleInvariant w) (h1 : w (ι X) = 1) :
    w = gaussExtension (restrictValuation w) := by
  apply gaussExtension_unique
  intro f
  have key : ∀ r : WithTop ℝ, r ≤ w (ι f) ↔ r ≤ gaussVal (restrictValuation w) f := by
    intro r
    rw [le_val_iff_of_scaleInvariant w hw, le_gaussVal_iff]
    refine forall_congr' fun i => ?_
    rw [restrictValuation_apply, h1]
    have : i • (1 : WithTop ℝ) = ((i : ℝ) : WithTop ℝ) := by
      induction i with
      | zero => simp
      | succ i ih => rw [succ_nsmul, ih]; push_cast; rfl
    rw [this]
  exact le_antisymm ((key _).mp le_rfl) ((key _).mpr le_rfl)

/-- Rescaling preserves `𝔾_m`-invariance. -/
theorem IsScaleInvariant.rescale (hw : IsScaleInvariant w) {c : ℝ} (hc : 0 < c) :
    IsScaleInvariant (w.rescale hc) := fun z hz f => by
  simp only [SourceRealValuation.rescale_apply, hw z hz f]

/-- **Normalized `𝔾_m`-invariant valuations are Gauss extensions**: if `w(t) = b` with
`0 < b < ∞`, then `b⁻¹ w = σ(b⁻¹ w|_K)`; i.e. `w = b σ(v)` for `v = b⁻¹ w|_K` ([BJ22, §2.2]:
`ord_E = b_E σ(v_E)` on a test configuration). -/
theorem rescale_eq_gaussExtension_of_scaleInvariant (hw : IsScaleInvariant w) {b : ℝ}
    (hb : 0 < b) (hX : w (ι X) = (b : WithTop ℝ)) :
    w.rescale (inv_pos.mpr hb) = gaussExtension (restrictValuation (w.rescale (inv_pos.mpr hb))) := by
  apply eq_gaussExtension_of_scaleInvariant _ (IsScaleInvariant.rescale w hw (inv_pos.mpr hb))
  rw [SourceRealValuation.rescale_apply, hX, scaleTop_coe, inv_mul_cancel₀ hb.ne']
  rfl

end SGPT.NAPotential.BJModel3
