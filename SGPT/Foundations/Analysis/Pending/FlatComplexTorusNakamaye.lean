import SGPT.Foundations.Analysis.Pending.FlatComplexTorus
import SGPT.Foundations.Analysis.Pending.NakamayeMainTheorem

set_option autoImplicit false

/-!
# The main theorem applied to the flat compact complex torus

`FlatComplexTorus` builds the flat torus `X = ℂⁿ / Λ` with its complex-manifold
structure, compactness, connectedness and the flat Kähler background `ω`, sorry-free.
Here the headline `NakamayeMainTheorem.nonKahlerLocus_eq_nullLocus` is instantiated
on it: for every `n ≥ 1` and every pseudoeffective class `α` of `X`,
`E_nK(α) = Null(α)`, in particular for `α = 0` and `α = {ω}`.

This is evidence that the main theorem's hypotheses are not vacuous (every instance
argument and hypothesis is supplied by a concrete object).  It adds no hypothesis or
obligation to those of the main theorem, which is sorry-free.

Content check (sorry-free): `nonKahlerLocus_kahler_eq_empty` -- on any complex manifold
of positive dimension, the class of a Kähler background has empty non-Kähler locus
(`ω` with potential `0` is a Kähler current, and a positive Lelong number forces a
pole). On the torus the main theorem therefore gives `Null({ω}) = ∅`
(`nullLocus_kahler_torus_eq_empty`): the instantiated conclusion is not the
degenerate `E_nK = Null = X` for every class.
-/

namespace SGPT.Foundations.Analysis.Pending.FlatComplexTorusNakamaye

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.NumericalRestrictedVolume FlatComplexTorus

variable {n : ℕ}

/-- The transcendental Nakamaye theorem on the flat torus `ℂⁿ / Λ`. -/
theorem nonKahlerLocus_eq_nullLocus_torus (hn : 0 < n) (alpha : RealBottChern n (Torus n))
    (hpsef : ClassPseudoeffectiveViaPotentials alpha) :
    nonKahlerLocus alpha = nullLocus (flatKahlerBackground n) alpha :=
  NakamayeMainTheorem.nonKahlerLocus_eq_nullLocus hn (flatKahlerBackground n) alpha hpsef

/-- The main theorem on the torus for the zero class. -/
theorem nonKahlerLocus_zero_eq_nullLocus_torus (hn : 0 < n) :
    nonKahlerLocus (0 : RealBottChern n (Torus n)) =
      nullLocus (flatKahlerBackground n) (0 : RealBottChern n (Torus n)) :=
  nonKahlerLocus_eq_nullLocus_torus hn 0 (classPseudoeffectiveViaPotentials_zero n)

/-- The main theorem on the torus for the Kähler class `{ω}`. -/
theorem nonKahlerLocus_kahler_eq_nullLocus_torus (hn : 0 < n) :
    nonKahlerLocus (RealBottChern.ofRepresentative (flatKahlerBackground n).form) =
      nullLocus (flatKahlerBackground n)
        (RealBottChern.ofRepresentative (flatKahlerBackground n).form) :=
  nonKahlerLocus_eq_nullLocus_torus hn _ (classPseudoeffectiveViaPotentials_kahler n)

section KahlerClass

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The class of a Kähler background has empty non-Kähler locus (positive dimension):
`ω` itself, with potential `0`, is a Kähler current (`ω ≥ ω/2`) and has no pole. -/
theorem nonKahlerLocus_kahler_eq_empty (hn : 0 < n) (omega : KahlerBackground n M) :
    nonKahlerLocus (RealBottChern.ofRepresentative omega.form) = ∅ := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have heq : omega.form - (KahlerBackground.smul hhalf omega).form =
      (KahlerBackground.smul hhalf omega).form := by
    rw [KahlerBackground.smul_form]
    module
  let T : KahlerCurrent (RealBottChern.ofRepresentative omega.form) :=
    { representative := omega.form
      represents := rfl
      potential := fun _ => 0
      lowerBound := KahlerBackground.smul hhalf omega
      strictlyPsh := by
        rw [heq]
        exact (LocalPotentials.isThetaPshPotential_zero_iff _).mpr
          (KahlerBackground.smul hhalf omega).isSemipositive }
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  have h : (0 : EReal) = ⊥ := eq_bot_of_lelongNumber_pos hn T.strictlyPsh.1 (hx T)
  exact EReal.zero_ne_bot h

end KahlerClass

/-- On the torus, the main theorem gives `Null({ω}) = ∅`. -/
theorem nullLocus_kahler_torus_eq_empty (hn : 0 < n) :
    nullLocus (flatKahlerBackground n)
      (RealBottChern.ofRepresentative (flatKahlerBackground n).form) = ∅ := by
  rw [← nonKahlerLocus_kahler_eq_nullLocus_torus hn]
  exact nonKahlerLocus_kahler_eq_empty hn _

end SGPT.Foundations.Analysis.Pending.FlatComplexTorusNakamaye
