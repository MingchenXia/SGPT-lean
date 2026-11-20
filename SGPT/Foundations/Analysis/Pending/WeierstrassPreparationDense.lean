import SGPT.Foundations.Analysis.Pending.RegularDirectionDense
import SGPT.Foundations.Analysis.Pending.GermCoordinateTower

set_option autoImplicit false

/-!
# Weierstrass preparation in a PRESCRIBED, and shared, direction

`Pending.GermCoordinateTower.exists_mul_comapEquiv_eq_prodWeierstrassGerm` puts a nonzero
germ of `E × ℂ` in Weierstrass form after SOME linear change of coordinates: the direction
comes out of `Pending.RegularDirection.exists_regular_continuousLinearEquiv` and nothing is
known about it.  The Noether normalization behind Demailly's local parametrization theorem
needs two things that version does not give.

* One direction must serve a FINITE FAMILY of germs at once, because the germ of a
  subvariety at a point is reducible and one projection has to be finite on every component.
* The direction must be close to a PRESCRIBED one, because
  `Pending.AdaptedProjectionGerm.exists_adaptedProjection` prescribes `B₀` and only
  approximates it.

Both come from `Pending.RegularDirectionDense`: the good directions are open and dense, so
a finite intersection of them is again dense.  What this module adds is the passage from a
good direction to a change of coordinates one can compute with, namely the SHEAR

  `shear a : (x, t) ↦ (x + t • a, t)`,

whose inverse is `shear (-a)` and which moves only the last coordinate's direction,
`shear a (0, t) = t • (a, 1)`.  Keeping the change of coordinates a shear is what will let
the Noether induction read off the transported projection: `(shear a)⁻¹` changes the first
`E`-block by `- t • a` and leaves `t` alone.

`exists_shear_prodWeierstrassGerm` is the resulting statement: one shear, with `a` as close
as we like to a prescribed `a₀`, putting every member of a finite family of nonzero germs
in Weierstrass form in the last variable.

Degenerate cases.  The empty family is allowed and returns any `a` in the ball.  `a₀ = 0`
is allowed; the conclusion never asserts `a ≠ 0`, and indeed `a = 0` is admissible exactly
when every `g i` is already regular in the last variable.  `E = 0` is allowed, and there
`a = a₀ = 0`: a nonzero germ of `ℂ` is regular in its only variable.
-/

open Filter Metric Set
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending

open HolomorphicGermWeierstrassPreparation RegularDirectionDense

noncomputable section

namespace HolGerm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The **shear** `(x, t) ↦ (x + t • a, t)` of `E × ℂ`.  It fixes the last coordinate and
moves the direction of the last coordinate axis to `(a, 1)`. -/
def shear (a : E) : (E × ℂ) ≃L[ℂ] (E × ℂ) :=
  ContinuousLinearEquiv.equivOfInverse
    (((ContinuousLinearMap.fst ℂ E ℂ) + (ContinuousLinearMap.snd ℂ E ℂ).smulRight a).prod
      (ContinuousLinearMap.snd ℂ E ℂ))
    (((ContinuousLinearMap.fst ℂ E ℂ) - (ContinuousLinearMap.snd ℂ E ℂ).smulRight a).prod
      (ContinuousLinearMap.snd ℂ E ℂ))
    (fun x => by ext <;> simp) (fun x => by ext <;> simp)

@[simp] theorem shear_apply (a : E) (x : E × ℂ) : shear a x = (x.1 + x.2 • a, x.2) := rfl

@[simp] theorem shear_symm_apply (a : E) (x : E × ℂ) :
    (shear a).symm x = (x.1 - x.2 • a, x.2) := rfl

theorem shear_apply_zero (a : E) (t : ℂ) : shear a (0, t) = t • (a, (1 : ℂ)) := by
  simp [Prod.smul_mk]

/-- The scaled direction `(a, 1)` with `a = c⁻¹ • w₁` is the complex line through
`w = (w₁, c)`, so regularity along `w` is regularity along a shear direction. -/
theorem prod_inv_smul_eq {c : ℂ} (hc : c ≠ 0) (w : E × ℂ) (hw : w.2 = c) :
    ((c⁻¹ • w.1, (1 : ℂ)) : E × ℂ) = c⁻¹ • w := by
  refine Prod.ext rfl ?_
  simp [hw, inv_mul_cancel₀ hc]

/-- **Weierstrass preparation along a shear, for a FINITE FAMILY, in a direction as close as
we like to a prescribed one.**

Every member of a finite family of nonzero germs of `E × ℂ` becomes, after multiplication by
a unit and ONE shear `shear a` with `‖a - a₀‖ < δ`, a Weierstrass polynomial in the last
variable.  This is
`Pending.GermCoordinateTower.HolGerm.exists_mul_comapEquiv_eq_prodWeierstrassGerm` with the
two strengthenings Demailly's local parametrization theorem needs: the change of coordinates
is a shear (so the transported projection can be computed), it is shared by the whole
family, and its direction is prescribed up to `δ`.

The direction comes from `Pending.RegularDirectionDense.exists_forall_regularAlong'`, which
produces a `w` close to `(a₀, 1)` regular for every `g i` at once.  Its last coordinate `c`
is close to `1`, hence nonzero, and regularity only sees the complex line `ℂ w`, so `w` may
be rescaled to `(c⁻¹ • w₁, 1)` — a genuine shear direction — at the cost of a controlled
extra error.  That rescaling is why the hypothesis is `δ > 0` and not `a = a₀`: the good
directions are dense, not everywhere.

Degenerate cases.  `ι` empty: the conclusion is `‖a - a₀‖ < δ` alone, satisfied by
`a = a₀`.  `E = 0`: `a = a₀ = 0` and the statement is one-variable Weierstrass preparation.
`g i` a unit: then `s = 0` and `prodWeierstrassGerm 0 A = 1`. -/
theorem exists_shear_prodWeierstrassGerm {ι : Type*} [Fintype ι] {g : ι → HolGerm (E × ℂ)}
    (hg : ∀ i, g i ≠ 0) (a₀ : E) {δ : ℝ} (hδ : 0 < δ) :
    ∃ a : E, ‖a - a₀‖ < δ ∧ ∀ i, ∃ (q : HolGerm (E × ℂ)) (s : ℕ) (A : ℕ → HolGerm E),
      IsUnit q ∧ (∀ j < s, eval (A j) = 0) ∧
        q * comapEquiv (shear a) (g i) = prodWeierstrassGerm s A := by
  classical
  choose G hG hGeq using fun i => exists_eq_mk (g i)
  have hne : ∀ i, ¬ ∀ᶠ z in 𝓝 (0 : E × ℂ), G i z = 0 := by
    intro i hev
    exact hg i (by rw [hGeq i, ← mk_zero, mk_eq_mk_iff]; exact hev)
  -- the tolerance on the good direction, before the rescaling that turns it into a shear
  set ε : ℝ := min (1 / 2) (δ / (2 * ‖a₀‖ + 4)) with hεdef
  have hden : (0 : ℝ) < 2 * ‖a₀‖ + 4 := by positivity
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hεhalf : ε ≤ 1 / 2 := min_le_left _ _
  have hεδ : ε * (2 * ‖a₀‖ + 4) ≤ δ := by
    have := min_le_right (1 / 2 : ℝ) (δ / (2 * ‖a₀‖ + 4))
    rw [← hεdef] at this
    calc ε * (2 * ‖a₀‖ + 4) ≤ (δ / (2 * ‖a₀‖ + 4)) * (2 * ‖a₀‖ + 4) :=
          mul_le_mul_of_nonneg_right this hden.le
      _ = δ := by field_simp
  obtain ⟨w, hw, hreg⟩ :=
    exists_forall_regularAlong' (g := G) hG hne ((a₀, (1 : ℂ)) : E × ℂ) hε
  have hsplit : ‖w - ((a₀, (1 : ℂ)) : E × ℂ)‖ = max ‖w.1 - a₀‖ ‖w.2 - 1‖ := by
    rw [Prod.norm_def]; rfl
  rw [hsplit] at hw
  have h1 : ‖w.1 - a₀‖ < ε := (le_max_left _ _).trans_lt hw
  have h2 : ‖w.2 - 1‖ < ε := (le_max_right _ _).trans_lt hw
  -- the last coordinate is close to `1`, hence invertible
  have hlow : 1 / 2 < ‖w.2‖ := by
    have := norm_sub_norm_le (1 : ℂ) w.2
    rw [norm_sub_rev] at this
    have h1c : ‖(1 : ℂ)‖ = 1 := norm_one
    rw [h1c] at this
    linarith
  have hc : w.2 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlow
    linarith
  refine ⟨w.2⁻¹ • w.1, ?_, fun i => ?_⟩
  · -- `‖c⁻¹ w₁ - a₀‖ ≤ ‖c⁻¹ - 1‖ ‖w₁‖ + ‖w₁ - a₀‖ < 2ε(‖a₀‖ + 1) + ε ≤ δ`
    have hdecomp : w.2⁻¹ • w.1 - a₀ = (w.2⁻¹ - 1) • w.1 + (w.1 - a₀) := by
      rw [sub_smul, one_smul]; abel
    have hinv : ‖w.2⁻¹ - 1‖ < 2 * ε := by
      have hfac : w.2⁻¹ - 1 = (1 - w.2) * w.2⁻¹ := by
        field_simp
      rw [hfac, norm_mul, norm_inv, norm_sub_rev]
      have hpos : (0 : ℝ) < ‖w.2‖ := by linarith
      calc ‖w.2 - 1‖ * ‖w.2‖⁻¹ < ε * ‖w.2‖⁻¹ := by
            exact mul_lt_mul_of_pos_right h2 (by positivity)
        _ ≤ ε * 2 := by
            refine mul_le_mul_of_nonneg_left ?_ hε.le
            rw [inv_le_comm₀ hpos (by norm_num)]
            linarith
        _ = 2 * ε := by ring
    have hw1 : ‖w.1‖ < ‖a₀‖ + ε := by
      have := norm_sub_norm_le w.1 a₀
      linarith
    have hkey : ‖w.2⁻¹ • w.1 - a₀‖ < 2 * ε * (‖a₀‖ + ε) + ε := by
      rw [hdecomp]
      refine (norm_add_le _ _).trans_lt ?_
      rw [norm_smul]
      have hb : ‖w.2⁻¹ - 1‖ * ‖w.1‖ < 2 * ε * (‖a₀‖ + ε) := by
        rcases eq_or_lt_of_le (norm_nonneg w.1) with hz | hz
        · rw [← hz, mul_zero]; positivity
        · exact mul_lt_mul'' hinv hw1 (norm_nonneg _) (norm_nonneg _)
      linarith
    have hfin : 2 * ε * (‖a₀‖ + ε) + ε ≤ δ := by
      nlinarith [hε.le, norm_nonneg a₀]
    linarith
  · -- the shear direction is regular for `G i`, so Weierstrass preparation applies
    have hregA : RegularAlong (G i) ((w.2⁻¹ • w.1, (1 : ℂ)) : E × ℂ) := by
      rw [prod_inv_smul_eq hc w rfl]
      exact (regularAlong_smul (inv_ne_zero hc) w).2 (hreg i)
    set a : E := w.2⁻¹ • w.1 with hadef
    set F : (E × ℂ) → ℂ := G i ∘ (shear a) with hFdef
    have hF : ∀ᶠ z in 𝓝 (0 : E × ℂ), DifferentiableAt ℂ F z :=
      eventually_differentiableAt_comp_clm ((shear a : (E × ℂ) →L[ℂ] E × ℂ)) (hG i)
    have hline : ∀ t : ℂ, F ((0 : E), t) = G i (t • ((a, (1 : ℂ)) : E × ℂ)) := by
      intro t
      rw [hFdef, Function.comp_apply, shear_apply_zero]
    have hφ : AnalyticAt ℂ (fun t : ℂ => F ((0 : E), t)) 0 := by
      rw [Complex.analyticAt_iff_eventually_differentiableAt]
      have := eventually_differentiableAt_comp_clm (ContinuousLinearMap.inr ℂ E ℂ) hF
      simpa [Function.comp_def] using this
    have hnotzero : ¬ ∀ᶠ t in 𝓝 (0 : ℂ), F ((0 : E), t) = 0 := by
      intro hev
      exact hregA (by filter_upwards [hev] with t ht; rwa [hline t] at ht)
    obtain ⟨d, u, hu, hu0, hpow⟩ :=
      hφ.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnotzero
    have hpow' : ∀ᶠ t in 𝓝 (0 : ℂ), F ((0 : E), t) = t ^ d * u t := by
      filter_upwards [hpow] with t ht
      simpa [smul_eq_mul] using ht
    obtain ⟨q, hq, hq0, b, hb, hb0, heq⟩ := exists_weierstrass_preparation hF hu hu0 hpow'
    refine ⟨mk q hq, d, fun j => mk (b j) (hb j), (isUnit_iff_eval_ne_zero _).2 hq0,
      fun j hj => hb0 j hj, ?_⟩
    rw [hGeq i, comapEquiv_mk, prodWeierstrassGerm_eq_mk]
    exact (mk_eq_mk_iff (hf := eventually_differentiableAt_mul hq hF)).2 heq

end HolGerm

end

end SGPT.Foundations.Analysis.Pending
