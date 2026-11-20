import SGPT.Foundations.Analysis.FirstPass.TopPowerDensityPositivity
import SGPT.Foundations.Analysis.Pending.RestrictedMassEnvelopeMonotone

set_option autoImplicit false

/-!
# Upper bounds for the genuine top-power density

`FirstPass.TopPowerDensityPositivity` proves the LOWER bound
`pow_mul_le_actualTopPowerDensity`: a `(1,1)`-form bounded below by `c‖v‖²` on
complex lines has top-power density at least `cᵏ` times that of the standard
form.  The local finite-volume statement for an analytic subvariety needs the
opposite comparison: a smooth Kähler form on a compact piece of a chart is
bounded ABOVE by a multiple of the flat form, so its parameter density along any
regular parametrization is bounded by a multiple of the FLAT parameter density.

* `actualTopPowerDensity_smul` — the density is homogeneous of degree `k` in the
  form, because the pairing-sum formula is a sum of products of `k` values.
* `actualTopPowerDensity_le_pow_mul` — the mirror of
  `pow_mul_le_actualTopPowerDensity`: if `A ≤ c·B` on complex lines, with `A`
  semipositive and `A`, `B` of type `(1,1)`, then the density of `A` is at most
  `cᵏ` times that of `B`.  The proof is the same one: `c·B - A` is semipositive,
  so monotonicity under adding a semipositive `(1,1)`-form applies.
* `actualTopPowerDensity_comp_le_pow_mul` — the same comparison after pullback by
  a complex linear map, which is the form the parameter densities take: the
  density of `L^*A` is at most `cᵏ` times the density of `L^*ω`.
* `apply_I_smul_self_le_norm_mul` — the comparison constant always exists
  pointwise: `A(v, iv) ≤ ‖A‖·‖v‖²` for every real two-form.

The two facts that a pullback by a complex linear map preserves being `(1,1)`
and being semipositive are `Pending.RestrictedMassEnvelopeMonotone`'s, reused
rather than restated.

Nothing here is about manifolds or subvarieties; these are statements about one
alternating form on `ℂⁿ`.
-/

open scoped InnerProductSpace

namespace SGPT.Foundations.Analysis.Pending.TopPowerDensityUpperBound

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses

noncomputable section

variable {n : ℕ}

/-- The pairing sum is homogeneous of degree `k` in the form. -/
theorem coordinatePairingSum_smul {iota : Type*} [Fintype iota] [DecidableEq iota] {k : ℕ}
    (c : ℝ) (A : CoordinateRealTwoForm n) (q : Fin k × Fin 2 → iota)
    (v : iota → ComplexModel n) :
    coordinatePairingSum (c • A) q v = c ^ k * coordinatePairingSum A q v := by
  unfold coordinatePairingSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun sigma _ => ?_
  have hprod : (∏ i : Fin k, (c • A) ![v (sigma (q (i, 0))), v (sigma (q (i, 1)))]) =
      c ^ k * ∏ i : Fin k, A ![v (sigma (q (i, 0))), v (sigma (q (i, 1)))] := by
    simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hprod]
  ring

/-- The genuine top-power density is homogeneous of degree `k` in the form. -/
theorem actualTopPowerDensity_smul {k : ℕ} (c : ℝ) (A : CoordinateRealTwoForm k) :
    actualTopPowerDensity (c • A) = c ^ k * actualTopPowerDensity A := by
  unfold actualTopPowerDensity
  rw [coordinateWedgePower_apply_eq_pairingSum, coordinateWedgePower_apply_eq_pairingSum,
    coordinatePairingSum_smul]
  ring

/-- **The upper comparison.**  If the semipositive `(1,1)`-form `A` is dominated
on complex lines by `c` times the `(1,1)`-form `B`, then its top-power density is
dominated by `cᵏ` times that of `B`. -/
theorem actualTopPowerDensity_le_pow_mul {k : ℕ} {A B : CoordinateRealTwoForm k}
    (hA : IsOneOne A) (hApos : CoefficientSemipositive A) (hB : IsOneOne B)
    {c : ℝ} (hle : ∀ v, A ![v, Complex.I • v] ≤ c * B ![v, Complex.I • v]) :
    actualTopPowerDensity A ≤ c ^ k * actualTopPowerDensity B := by
  have hD : IsOneOne (c • B - A) := fun u v => by
    simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, hA u v, hB u v]
  have hDpos : CoefficientSemipositive (c • B - A) := fun v => by
    simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, sub_nonneg]
    exact hle v
  have hmono := actualTopPowerDensity_le_add hA hApos hD hDpos
  rw [add_sub_cancel] at hmono
  rw [← actualTopPowerDensity_smul]
  exact hmono

/-- Every real two-form is dominated on complex lines by its operator norm. -/
theorem apply_I_smul_self_le_norm_mul (A : CoordinateRealTwoForm n) (v : ComplexModel n) :
    A ![v, Complex.I • v] ≤ ‖A‖ * ‖v‖ ^ 2 := by
  refine (le_abs_self _).trans ?_
  refine (A.le_opNorm ![v, Complex.I • v]).trans (le_of_eq ?_)
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, norm_smul,
    Complex.norm_I, one_mul]
  ring

/-- **The upper comparison after pullback.**  If the semipositive `(1,1)`-form
`A` on `ℂⁿ` satisfies `A(z, iz) ≤ c‖z‖²`, then for every complex linear
`L : ℂᵏ → ℂⁿ` the density of `L^*A` is at most `cᵏ` times the density of the
pulled-back standard form `L^*ω`.

This is the shape the parameter densities of a regular parametrization take:
`L` is the derivative of the parametrization read in a chart, `A` the
coefficient of the K\"ahler form at the corresponding point, and `L^*ω` the flat
parameter density of that chart. -/
theorem actualTopPowerDensity_comp_le_pow_mul {k : ℕ} {A : CoordinateRealTwoForm n}
    (hA : IsOneOne A) (hApos : CoefficientSemipositive A)
    (L : ComplexModel k →L[ℝ] ComplexModel n)
    (hL : ∀ v, L (Complex.I • v) = Complex.I • L v)
    {c : ℝ} (hle : ∀ z : ComplexModel n, A ![z, Complex.I • z] ≤ c * ‖z‖ ^ 2) :
    actualTopPowerDensity (A.compContinuousLinearMap L) ≤
      c ^ k * actualTopPowerDensity
        ((standardHermitianTwoForm n).compContinuousLinearMap L) := by
  refine actualTopPowerDensity_le_pow_mul
    (RestrictedMassEnvelopeMonotone.isOneOne_compContinuousLinearMap hA L hL)
    (RestrictedMassEnvelopeMonotone.coefficientSemipositive_compContinuousLinearMap hApos L hL)
    (RestrictedMassEnvelopeMonotone.isOneOne_compContinuousLinearMap
      (standardHermitianTwoForm_isOneOne n) L hL) fun v => ?_
  have hLv : (A.compContinuousLinearMap L) ![v, Complex.I • v] = A ![L v, Complex.I • L v] := by
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    congr 1
    ext i
    fin_cases i <;> simp [hL]
  have hstd : ((standardHermitianTwoForm n).compContinuousLinearMap L) ![v, Complex.I • v] =
      ‖L v‖ ^ 2 := by
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    have : (fun i => L (![v, Complex.I • v] i)) = ![L v, Complex.I • L v] := by
      ext i
      fin_cases i <;> simp [hL]
    rw [show (L ∘ ![v, Complex.I • v] : Fin 2 → ComplexModel n) = ![L v, Complex.I • L v] from
      this]
    exact standardHermitianTwoForm_apply_I_smul_self (L v)
  rw [hLv, hstd]
  exact hle (L v)

end

end SGPT.Foundations.Analysis.Pending.TopPowerDensityUpperBound
