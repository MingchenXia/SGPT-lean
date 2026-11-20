import SGPT.Foundations.Analysis.Pending.BoundedContDiffHolderMap
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

/-!
# Interpolation inequalities on the whole space

For a map `f : E → F` between real normed spaces (no boundedness of the domain, no dimension
hypothesis) whose second derivative is bounded and `α`-Hölder with constant `H`:

* `norm_sub_sub_fderiv_le_of_holderWith`: first-order Taylor with a Hölder derivative,
  `‖f (x + h) - f x - Df(x) h‖ ≤ H ‖h‖^{1 + r}` when `Df` is `r`-Hölder with constant `H`;
* `norm_fderiv_le_of_holderWith`: `‖Df(x)‖ ≤ 2 A / ρ + H ρ^r` for every `ρ > 0`, if `‖f‖ ≤ A`;
* `norm_fderiv_fderiv_le_interpolation`, `norm_fderiv_le_interpolation`: the interpolation
  inequalities of Gilbarg--Trudinger (6.89) / Lemma 6.32 on the whole space,
  `|D²f|_0 ≤ 32 A / ρ² + 2 H ρ^α` and `|Df|_0 ≤ 34 A / ρ + 2 H ρ^{1 + α}`, i.e.
  `|D^j f|_0 ≤ ε [D²f]_α + C(ε) |f|_0` (`j = 1, 2`);
* `BoundedContDiffHolderMap.norm_iteratedFDeriv_two_le_interpolation` and
  `...norm_iteratedFDeriv_one_le_interpolation`: the same for `u ∈ C^{2,α}_b(E, F)` in terms of
  `‖u‖_∞` and the Hölder seminorm `[D²u]_α` of `iteratedFDeriv ℝ 2 u`.

These are used by Simon's blow-up proof of the Schauder estimates (Székelyhidi, *An Introduction to
Extremal Kähler Metrics*, Theorem 2.8, `szekelyhidi-extremal:page-0044`, and its proof sketch on
`page-0045`--`page-0047`; L. Simon, *Schauder estimates by scaling*, 1997) to pass from a bound on
`[D²u]_α` to the full `C^{2,α}` norm, and by the localisation of the Schauder estimate on a compact
manifold.

Part L2.1 of the linear track for Yau's theorem (the linear elliptic estimates;
TN.4 B5, the TEMPORARY named input `YauTheorem.exists_kahler_mongeAmpere_eq_exp`, I-0797 / I-0902).
-/

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace SGPT.Foundations.Analysis.Pending.HolderInterpolation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **First-order Taylor formula with a Hölder derivative**: if `Df` is `r`-Hölder with constant
`H`, then `‖f (x + h) - f x - Df(x) h‖ ≤ H ‖h‖^{1 + r}`. -/
theorem norm_sub_sub_fderiv_le_of_holderWith {f : E → F} (hf : Differentiable ℝ f) {H r : ℝ≥0}
    (hD : HolderWith H r (fderiv ℝ f)) (x h : E) :
    ‖f (x + h) - f x - fderiv ℝ f x h‖ ≤ H * ‖h‖ ^ (1 + (r : ℝ)) := by
  set g : E → F := fun y => f y - fderiv ℝ f x (y - x) with hg
  have hgd : ∀ y, HasFDerivAt g (fderiv ℝ f y - fderiv ℝ f x) y := fun y => by
    have h1 := (hf y).hasFDerivAt
    have h2 := (fderiv ℝ f x).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const x)
    rw [ContinuousLinearMap.comp_id] at h2
    exact h1.sub h2
  have hbound : ∀ y ∈ segment ℝ x (x + h), ‖fderiv ℝ g y‖ ≤ H * ‖h‖ ^ (r : ℝ) := by
    intro y hy
    rw [(hgd y).fderiv, ← dist_eq_norm]
    have hyx : dist y x ≤ ‖h‖ := by
      rw [dist_eq_norm]
      have := norm_sub_le_of_mem_segment hy
      simpa using this
    calc dist (fderiv ℝ f y) (fderiv ℝ f x) ≤ H * dist y x ^ (r : ℝ) := hD.dist_le y x
      _ ≤ H * ‖h‖ ^ (r : ℝ) := by
        gcongr
  have hmv := (convex_segment x (x + h)).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => (hgd y).differentiableAt) hbound (left_mem_segment ℝ x (x + h))
    (right_mem_segment ℝ x (x + h))
  have hgx : g (x + h) - g x = f (x + h) - f x - fderiv ℝ f x h := by
    simp only [hg, add_sub_cancel_left, sub_self, map_zero, sub_zero]
    abel
  rw [hgx, add_sub_cancel_left] at hmv
  calc ‖f (x + h) - f x - fderiv ℝ f x h‖ ≤ H * ‖h‖ ^ (r : ℝ) * ‖h‖ := hmv
    _ = H * ‖h‖ ^ (1 + (r : ℝ)) := by
      rcases (norm_nonneg h).eq_or_lt with h0 | h0
      · rw [← h0]
        simp [Real.zero_rpow (by positivity : (1 + (r : ℝ)) ≠ 0)]
      · rw [Real.rpow_add h0, Real.rpow_one]
        ring

/-- **Interpolation for the first derivative**: if `‖f‖ ≤ A` and `Df` is `r`-Hölder with constant
`H`, then `‖Df(x)‖ ≤ 2A/ρ + H ρ^r` for every `ρ > 0`. -/
theorem norm_fderiv_le_of_holderWith {f : E → F} (hf : Differentiable ℝ f) {A : ℝ}
    (hA : ∀ y, ‖f y‖ ≤ A) {H r : ℝ≥0} (hD : HolderWith H r (fderiv ℝ f)) {ρ : ℝ} (hρ : 0 < ρ)
    (x : E) : ‖fderiv ℝ f x‖ ≤ 2 * A / ρ + H * ρ ^ (r : ℝ) := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA x)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  rcases (norm_nonneg h).eq_or_lt with h0 | h0
  · rw [← h0, mul_zero, norm_le_zero_iff.mp h0.symm.le, map_zero, norm_zero]
  set t : ℝ := ρ / ‖h‖ with ht
  have htpos : 0 < t := div_pos hρ h0
  have hth : ‖t • h‖ = ρ := by
    rw [norm_smul, Real.norm_of_nonneg htpos.le, ht, div_mul_cancel₀ _ h0.ne']
  have hT := norm_sub_sub_fderiv_le_of_holderWith hf hD x (t • h)
  rw [hth] at hT
  have hkey : ‖fderiv ℝ f x (t • h)‖ ≤ 2 * A + H * ρ ^ (1 + (r : ℝ)) := by
    have hsplit : fderiv ℝ f x (t • h) =
        (f (x + t • h) - f x) - (f (x + t • h) - f x - fderiv ℝ f x (t • h)) := by abel
    rw [hsplit]
    calc ‖(f (x + t • h) - f x) - (f (x + t • h) - f x - fderiv ℝ f x (t • h))‖
        ≤ ‖f (x + t • h) - f x‖ + ‖f (x + t • h) - f x - fderiv ℝ f x (t • h)‖ :=
          norm_sub_le _ _
      _ ≤ (A + A) + H * ρ ^ (1 + (r : ℝ)) := by
          gcongr
          exact (norm_sub_le _ _).trans (add_le_add (hA _) (hA _))
      _ = 2 * A + H * ρ ^ (1 + (r : ℝ)) := by ring
  rw [map_smul, norm_smul, Real.norm_of_nonneg htpos.le] at hkey
  have hρr : ρ ^ (1 + (r : ℝ)) = ρ * ρ ^ (r : ℝ) := by
    rw [Real.rpow_add hρ, Real.rpow_one]
  rw [hρr] at hkey
  have : ‖fderiv ℝ f x h‖ ≤ (2 * A + H * (ρ * ρ ^ (r : ℝ))) / t :=
    (le_div_iff₀ htpos).mpr (by linarith [mul_comm t ‖fderiv ℝ f x h‖])
  calc ‖fderiv ℝ f x h‖ ≤ (2 * A + H * (ρ * ρ ^ (r : ℝ))) / t := this
    _ = (2 * A / ρ + H * ρ ^ (r : ℝ)) * ‖h‖ := by
      rw [ht]
      field_simp

/-- A map with derivative bounded by `M` has an `M`-Lipschitz derivative's antiderivative: if
`‖D(Df)‖ ≤ M` then `Df` is `1`-Hölder with constant `M`. -/
theorem holderWith_one_fderiv_of_bound {f : E → F} (hf : ContDiff ℝ 2 f) {M : ℝ≥0}
    (hM : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ M) : HolderWith M 1 (fderiv ℝ f) := by
  rw [holderWith_one]
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  exact lipschitzWith_of_nnnorm_fderiv_le hd fun y => by
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact hM y

/-- **The interpolation inequality for `D²f`** (Gilbarg--Trudinger (6.89), whole space): if
`‖f‖ ≤ A`, `D²f` is bounded and `α`-Hölder with constant `H`, then
`‖D²f(x)‖ ≤ 32 A / ρ² + 2 H ρ^α` for every `ρ > 0`. -/
theorem norm_fderiv_fderiv_le_interpolation {f : E → F} (hf : ContDiff ℝ 2 f) {A : ℝ}
    (hA : ∀ y, ‖f y‖ ≤ A) (hB : ∃ M, ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ M) {H α : ℝ≥0}
    (hH : HolderWith H α (fderiv ℝ (fderiv ℝ f))) {ρ : ℝ} (hρ : 0 < ρ) (x : E) :
    ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ 32 * A / ρ ^ 2 + 2 * H * ρ ^ (α : ℝ) := by
  obtain ⟨M₀, hM₀⟩ := hB
  have hbdd : BddAbove (range fun y => ‖fderiv ℝ (fderiv ℝ f) y‖) := ⟨M₀, by
    rintro _ ⟨y, rfl⟩; exact hM₀ y⟩
  set S : ℝ := ⨆ y, ‖fderiv ℝ (fderiv ℝ f) y‖ with hS
  have hSy : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ S := fun y => le_ciSup hbdd y
  have hS0 : 0 ≤ S := (hSy x).trans' (by positivity)
  have hd1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hlip : HolderWith (Real.toNNReal S) 1 (fderiv ℝ f) :=
    holderWith_one_fderiv_of_bound hf fun y => by
      rw [Real.coe_toNNReal _ hS0]; exact hSy y
  -- `|Df| ≤ 2A/σ + S σ` with `σ = ρ/4`
  have hσ : 0 < ρ / 4 := by positivity
  have hDf : ∀ y, ‖fderiv ℝ f y‖ ≤ 2 * A / (ρ / 4) + S * (ρ / 4) := fun y => by
    have := norm_fderiv_le_of_holderWith hd1 hA hlip hσ y
    rwa [Real.coe_toNNReal _ hS0, NNReal.coe_one, Real.rpow_one] at this
  -- `|D²f| ≤ 2 |Df|_0 / ρ + H ρ^α`
  have hD2 : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤
      2 * (2 * A / (ρ / 4) + S * (ρ / 4)) / ρ + H * ρ ^ (α : ℝ) := fun y =>
    norm_fderiv_le_of_holderWith hd2 hDf hH hρ y
  have hSle : S ≤ 2 * (2 * A / (ρ / 4) + S * (ρ / 4)) / ρ + H * ρ ^ (α : ℝ) :=
    ciSup_le hD2
  have hexp : 2 * (2 * A / (ρ / 4) + S * (ρ / 4)) / ρ = 16 * A / ρ ^ 2 + S / 2 := by
    field_simp
    ring
  rw [hexp] at hSle
  calc ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ S := hSy x
    _ ≤ 2 * (16 * A / ρ ^ 2 + H * ρ ^ (α : ℝ)) := by linarith
    _ = 32 * A / ρ ^ 2 + 2 * H * ρ ^ (α : ℝ) := by ring

/-- **The interpolation inequality for `Df`** (whole space): under the hypotheses of
`norm_fderiv_fderiv_le_interpolation`, `‖Df(x)‖ ≤ 34 A / ρ + 2 H ρ^{1 + α}`. -/
theorem norm_fderiv_le_interpolation {f : E → F} (hf : ContDiff ℝ 2 f) {A : ℝ}
    (hA : ∀ y, ‖f y‖ ≤ A) (hB : ∃ M, ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ M) {H α : ℝ≥0}
    (hH : HolderWith H α (fderiv ℝ (fderiv ℝ f))) {ρ : ℝ} (hρ : 0 < ρ) (x : E) :
    ‖fderiv ℝ f x‖ ≤ 34 * A / ρ + 2 * H * ρ ^ (1 + (α : ℝ)) := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA x)
  set S : ℝ := 32 * A / ρ ^ 2 + 2 * H * ρ ^ (α : ℝ) with hS
  have hS0 : 0 ≤ S := by positivity
  have hD2 : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ S := fun y =>
    norm_fderiv_fderiv_le_interpolation hf hA hB hH hρ y
  have hlip : HolderWith (Real.toNNReal S) 1 (fderiv ℝ f) :=
    holderWith_one_fderiv_of_bound hf fun y => by
      rw [Real.coe_toNNReal _ hS0]; exact hD2 y
  have h := norm_fderiv_le_of_holderWith (hf.differentiable (by norm_num)) hA hlip hρ x
  rw [Real.coe_toNNReal _ hS0, NNReal.coe_one, Real.rpow_one] at h
  calc ‖fderiv ℝ f x‖ ≤ 2 * A / ρ + S * ρ := h
    _ = 34 * A / ρ + 2 * H * ρ ^ (1 + (α : ℝ)) := by
      rw [hS, Real.rpow_add hρ, Real.rpow_one]
      field_simp
      ring

/-! ### `iteratedFDeriv ℝ 2` versus `fderiv ℝ (fderiv ℝ ·)` -/

theorem iteratedFDeriv_two_apply_eq (f : E → F) (z : E) (m : Fin 2 → E) :
    iteratedFDeriv ℝ 2 f z m = fderiv ℝ (fderiv ℝ f) z (m 0) (m 1) := by
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_one_apply]
  rfl

/-- `iteratedFDeriv ℝ 2 f` is `fderiv ℝ (fderiv ℝ f)` followed by a linear isometry. -/
theorem exists_iteratedFDeriv_two_eq (f : E → F) :
    ∃ Ψ : (E →L[ℝ] E →L[ℝ] F) ≃ₗᵢ[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) F,
      ∀ z, iteratedFDeriv ℝ 2 f z = Ψ (fderiv ℝ (fderiv ℝ f) z) := by
  refine ⟨(continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] F)).symm.trans
    (continuousMultilinearCurryRightEquiv' ℝ 1 E F).symm, fun z => ?_⟩
  ext m
  rw [iteratedFDeriv_two_apply_eq]
  simp only [LinearIsometryEquiv.trans_apply]
  simp
  rfl

theorem norm_iteratedFDeriv_two (f : E → F) (x : E) :
    ‖iteratedFDeriv ℝ 2 f x‖ = ‖fderiv ℝ (fderiv ℝ f) x‖ := by
  obtain ⟨Ψ, hΨ⟩ := exists_iteratedFDeriv_two_eq f
  rw [hΨ, LinearIsometryEquiv.norm_map]

theorem norm_iteratedFDeriv_two_sub (f : E → F) (x y : E) :
    ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ =
      ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ := by
  obtain ⟨Ψ, hΨ⟩ := exists_iteratedFDeriv_two_eq f
  rw [hΨ, hΨ, ← Ψ.map_sub, Ψ.norm_map]

/-- Hölder continuity of `D²f` transfers from `iteratedFDeriv ℝ 2 f` to `fderiv (fderiv f)`. -/
theorem holderWith_fderiv_fderiv_of_iteratedFDeriv {f : E → F} {C r : ℝ≥0}
    (h : HolderWith C r (iteratedFDeriv ℝ 2 f)) : HolderWith C r (fderiv ℝ (fderiv ℝ f)) :=
  HolderWith.of_dist_le fun x y => by
    rw [dist_eq_norm, ← norm_iteratedFDeriv_two_sub, ← dist_eq_norm]
    exact h.dist_le x y

/-! ### Interpolation in `C^{2,α}_b(E, F)` -/

/-- **Interpolation in `C^{2,α}_b`, second derivatives**: for `u ∈ C^{2,α}_b(E, F)` with
`‖u‖ ≤ A` pointwise, `‖D²u(x)‖ ≤ 32 A / ρ² + 2 [D²u]_α ρ^α` for every `ρ > 0`. -/
theorem norm_iteratedFDeriv_two_le_interpolation {α : ℝ≥0}
    (u : BoundedContDiffHolderMap 2 α E F) {A : ℝ} (hA : ∀ y, ‖u y‖ ≤ A) {ρ : ℝ} (hρ : 0 < ρ)
    (x : E) :
    ‖iteratedFDeriv ℝ 2 u x‖ ≤
      32 * A / ρ ^ 2 + 2 * nnHolderNorm α (iteratedFDeriv ℝ 2 ⇑u) * ρ ^ (α : ℝ) := by
  have hc : ContDiff ℝ 2 ⇑u := by exact_mod_cast u.contDiff
  obtain ⟨M, hM⟩ := u.bounded (i := 2) le_rfl
  rw [norm_iteratedFDeriv_two]
  exact norm_fderiv_fderiv_le_interpolation hc hA
    ⟨M, fun y => (norm_iteratedFDeriv_two (⇑u) y).symm.trans_le (hM y)⟩
    (holderWith_fderiv_fderiv_of_iteratedFDeriv u.memHolder.holderWith) hρ x

/-- **Interpolation in `C^{2,α}_b`, first derivatives**: for `u ∈ C^{2,α}_b(E, F)` with
`‖u‖ ≤ A` pointwise, `‖Du(x)‖ ≤ 34 A / ρ + 2 [D²u]_α ρ^{1 + α}` for every `ρ > 0`. -/
theorem norm_iteratedFDeriv_one_le_interpolation {α : ℝ≥0}
    (u : BoundedContDiffHolderMap 2 α E F) {A : ℝ} (hA : ∀ y, ‖u y‖ ≤ A) {ρ : ℝ} (hρ : 0 < ρ)
    (x : E) :
    ‖iteratedFDeriv ℝ 1 u x‖ ≤
      34 * A / ρ + 2 * nnHolderNorm α (iteratedFDeriv ℝ 2 ⇑u) * ρ ^ (1 + (α : ℝ)) := by
  have hc : ContDiff ℝ 2 ⇑u := by exact_mod_cast u.contDiff
  obtain ⟨M, hM⟩ := u.bounded (i := 2) le_rfl
  rw [norm_iteratedFDeriv_one]
  exact norm_fderiv_le_interpolation hc hA
    ⟨M, fun y => (norm_iteratedFDeriv_two (⇑u) y).symm.trans_le (hM y)⟩
    (holderWith_fderiv_fderiv_of_iteratedFDeriv u.memHolder.holderWith) hρ x

end SGPT.Foundations.Analysis.Pending.HolderInterpolation
