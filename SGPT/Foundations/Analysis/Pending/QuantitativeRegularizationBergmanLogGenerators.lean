import SGPT.Foundations.Analysis.Pending.BergmanSupWeight

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The Bergman weight is dominated by any uniformly dominating generator family

Source: Copy-4, `lem:regularization`, Step 1 (`transcendental-nakamaye-copy4-20260911`);
blueprint `ana:regularization`.

`BergmanGenerators.exists_uniform_generators` produces, by Baire category, finitely many
members `g` of the weighted Bergman unit ball that dominate **every** member of that ball
on a smaller ball:  `‖f y‖² ≤ K ∑ₗ ‖gₗ y‖²`.  The Bergman kernel on the diagonal is the
supremum of `‖f y‖²` over exactly that ball, so the same inequality holds for it; in
logarithmic form,

> `bergmanLog(ball z 2R, w) ≤ generatorLog g + log K'`  on `ball z r`.

This is the direction *opposite* to `BergmanSupWeight.bergmanSup_extremal`, and it is the
bridge the regularization chain needs: the germ estimates of
`QuantitativeRegularizationMultiplierGermFamily` bound an arbitrary family of germs of
`𝓘(mΨ)` by `bergmanLog`, whereas the gluing modules run on the `generatorLog` of a patch's
own finite generator family.  Composing the two dominates an arbitrary germ family by the
patch generators **without** assuming that those generators generate the multiplier ideal,
which is the obligation `QuantitativeRegularizationLocalBergman`'s docstring flags.

The constant is taken as `K' = max K 0 + 1`: the hypothesis alone does not force `K ≥ 0`
(it is vacuous where all the `gₗ` vanish), and `K' > 0` is what makes `log K'` a real
number rather than `⊥`.
-/

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology BigOperators

namespace SGPT.Foundations.Analysis.Pending.QuantitativeRegularizationBergmanLogGenerators

noncomputable section

open FirstPass BergmanSupWeight

variable {d : ℕ}

/-- The weighted Bergman unit ball of `BergmanGenerators` is the Bergman ball of
`BergmanSupWeight` on `ball z (2R)`. -/
theorem bergmanUnitBall_eq (z : ComplexModel d) (R : ℝ) (w : ComplexModel d → ℝ≥0∞) :
    BergmanGenerators.bergmanUnitBall z R w = bergmanBall (ball z (2 * R)) w := rfl

/-- **The Bergman kernel inherits a uniform generator domination.**

If a finite family dominates every member of the weighted unit ball on `ball z r`, then it
dominates the kernel on the diagonal there. -/
theorem bergmanSup_le_mul_generatorNormSq
    {z : ComplexModel d} {R : ℝ} {w : ComplexModel d → ℝ≥0∞}
    {N : ℕ} {g : Fin N → ComplexModel d → ℂ} {K r : ℝ}
    (hdom : ∀ f ∈ BergmanGenerators.bergmanUnitBall z R w, ∀ y ∈ ball z r,
      ‖f y‖ ^ 2 ≤ K * ∑ l, ‖g l y‖ ^ 2)
    {y : ComplexModel d} (hy : y ∈ ball z r) :
    bergmanSup (ball z (2 * R)) w y
      ≤ ENNReal.ofReal (max K 0 + 1) * ENNReal.ofReal (generatorNormSq g y) := by
  have hsum : 0 ≤ generatorNormSq g y := generatorNormSq_nonneg g y
  refine iSup₂_le fun f hf => ?_
  have hfle : ‖f y‖ ^ 2 ≤ (max K 0 + 1) * generatorNormSq g y := by
    refine (hdom f hf y hy).trans ?_
    have : K * generatorNormSq g y ≤ (max K 0 + 1) * generatorNormSq g y := by
      have hK : K ≤ max K 0 + 1 := by
        have := le_max_left K 0
        linarith
      exact mul_le_mul_of_nonneg_right hK hsum
    simpa [generatorNormSq] using this
  calc ENNReal.ofReal (‖f y‖ ^ 2)
      ≤ ENNReal.ofReal ((max K 0 + 1) * generatorNormSq g y) := ENNReal.ofReal_le_ofReal hfle
    _ = ENNReal.ofReal (max K 0 + 1) * ENNReal.ofReal (generatorNormSq g y) :=
        ENNReal.ofReal_mul (by positivity)

/-- The logarithmic form: `bergmanLog ≤ generatorLog + log K'`. -/
theorem bergmanLog_le_generatorLog_add
    {z : ComplexModel d} {R : ℝ} {w : ComplexModel d → ℝ≥0∞}
    {N : ℕ} {g : Fin N → ComplexModel d → ℂ} {K r : ℝ}
    (hdom : ∀ f ∈ BergmanGenerators.bergmanUnitBall z R w, ∀ y ∈ ball z r,
      ‖f y‖ ^ 2 ≤ K * ∑ l, ‖g l y‖ ^ 2)
    {y : ComplexModel d} (hy : y ∈ ball z r) :
    bergmanLog (ball z (2 * R)) w y
      ≤ generatorLog g y + ((Real.log (max K 0 + 1) : ℝ) : EReal) := by
  have hK : (0 : ℝ) < max K 0 + 1 := by have := le_max_right K 0; linarith
  rw [bergmanLog, generatorLog_eq_log_sum]
  calc ENNReal.log (bergmanSup (ball z (2 * R)) w y)
      ≤ ENNReal.log (ENNReal.ofReal (max K 0 + 1) *
          ENNReal.ofReal (generatorNormSq g y)) :=
        ENNReal.log_monotone (bergmanSup_le_mul_generatorNormSq hdom hy)
    _ = ENNReal.log (ENNReal.ofReal (∑ j, ‖g j y‖ ^ 2)) +
          ((Real.log (max K 0 + 1) : ℝ) : EReal) := by
        rw [ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos hK, add_comm]
        rfl

/-- **The bridge, in existence form.**  For a weight bounded below on `ball z (2R)` there
are finitely many members of the weighted unit ball and one constant with

> `bergmanLog(ball z 2R, w) ≤ log ∑ₗ |gₗ|² + C`  on a smaller ball `ball z r`.

The family is the Baire-category family of `BergmanGenerators.exists_uniform_generators`;
nothing is assumed about which ideal it generates. -/
theorem exists_bergmanLog_le_generatorLog_add
    {z : ComplexModel d} {R : ℝ} {w : ComplexModel d → ℝ≥0∞}
    (hR : 0 < R) (hw : AEMeasurable w (volume.restrict (ball z (2 * R))))
    {δ : ℝ} (hδ : 0 < δ) (hlow : ∀ y ∈ ball z (2 * R), ENNReal.ofReal δ ≤ w y) :
    ∃ (N : ℕ) (g : Fin N → ComplexModel d → ℂ) (r C : ℝ), 0 < r ∧
      (∀ l, g l ∈ BergmanGenerators.bergmanUnitBall z R w) ∧
      ∀ y ∈ ball z r,
        bergmanLog (ball z (2 * R)) w y ≤ generatorLog g y + (C : EReal) := by
  obtain ⟨N, g, r, K, hr, hg, hdom⟩ :=
    BergmanGenerators.exists_uniform_generators hR hw hδ hlow
  exact ⟨N, g, r, Real.log (max K 0 + 1), hr, hg,
    fun y hy => bergmanLog_le_generatorLog_add hdom hy⟩

end

end SGPT.Foundations.Analysis.Pending.QuantitativeRegularizationBergmanLogGenerators
