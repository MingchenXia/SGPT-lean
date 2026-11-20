import SGPT.Foundations.Analysis.Pending.ComponentVanishing
import SGPT.Foundations.Analysis.Pending.NoIsolatedPoints

set_option autoImplicit false

/-!
# The transcendental Nakamaye theorem: `E_nK(α) = Null(α)`

Source: Copy-4, `thm:main` (second assertion) and `sec:gluing`
(`transcendental-nakamaye-copy4-20260911`); blueprint `ana:locus-equality`;
Collins--Tosatti, Conjecture 1.1 of CT22.

Let `X` be a nonempty connected compact Kähler manifold of positive complex
dimension and `α` a pseudoeffective real `(1,1)`-class.  Then
`E_nK(α) = Null(α)`.

* `E_nK(α)` is `NonKahlerLocus.nonKahlerLocus`: the common positive-Lelong-number
  set of all Kähler currents in `α` (all of `X` when there is none).
* `Null(α)` is `NumericalRestrictedVolume.nullLocus`: the union of the
  positive-dimensional closed irreducible analytic subvarieties `V` with
  `⟨α^{dim V}⟩_{X|V} = 0`, the numerical restricted volume being the CT22 right
  limit of absolutely continuous restricted top masses, computed with the Kähler
  form `omega`.
* Pseudoeffectivity is `ClassPseudoeffectiveViaPotentials`.

The hypothesis `0 < n` is essential in this encoding: in dimension zero every
punctured neighbourhood filter is trivial, Lelong numbers take the value `⊤`, and
`E_nK` would be the whole (point) manifold while `Null` is empty.

The proof is the manuscript's deduction, with no local `sorry`.  It rests on the
imported statements `ComponentVanishing`, `NoIsolatedPoints`, `LocusProperties` and
`AnalyticIrreducibleComponents`, which are all proved, so the theorem depends on no
`sorry` (its axioms are `propext`, `Classical.choice` and `Quot.sound`).  If `α` is
not big, `E_nK(α) = X` and `X` itself has zero restricted volume.  If `α` is big,
`E_nK(α)` is analytic without isolated points, so each of its points lies on a
positive-dimensional component, which has zero restricted volume; conversely a
positive-dimensional subvariety not inside `E_nK(α)` has positive restricted volume.
-/

open Set Filter

namespace SGPT.Foundations.Analysis.Pending.NakamayeMainTheorem

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.NumericalRestrictedVolume
  ComponentVanishing NoIsolatedPoints LocusProperties AnalyticIrreducibleComponents

noncomputable section

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **The transcendental Nakamaye theorem** (Copy-4, `thm:main`):
`E_nK(α) = Null(α)` for every pseudoeffective class on a nonempty connected compact
Kähler manifold of positive dimension. -/
theorem nonKahlerLocus_eq_nullLocus
    [Nonempty X] [CompactSpace X] [ConnectedSpace X] (hn : 0 < n)
    (omega : KahlerBackground n X) (alpha : RealBottChern n X)
    (hpsef : ClassPseudoeffectiveViaPotentials alpha) :
    nonKahlerLocus alpha = nullLocus omega alpha := by
  ext x
  constructor
  · intro hx
    by_cases hbig : IsBigClass alpha
    · have hK : Nonempty (KahlerBackground n X) := ⟨omega⟩
      obtain ⟨V, hVcomp, hVdim, hxV⟩ := exists_isIrreducibleComponent_pos_dim_of_accPt
        (isComplexAnalyticSubset_nonKahlerLocus hn hK alpha hbig) hx
        (accPt_nonKahlerLocus hn hK alpha hbig x hx)
      exact mem_nullLocus.mpr ⟨V, hVdim,
        numericalRestrictedVolume_eq_zero_of_isIrreducibleComponent hn omega alpha hpsef V
          hVdim hVcomp, hxV⟩
    · obtain ⟨Z, hZ, hZdim⟩ := exists_subvariety_univ (n := n) (M := X)
      exact mem_nullLocus.mpr ⟨Z, hZdim.symm ▸ hn,
        (numericalRestrictedVolume_eq_zero_iff_not_isBigClass hn omega alpha hpsef Z hZ).mpr
          hbig, hZ ▸ mem_univ x⟩
  · intro hx
    obtain ⟨V, hVdim, hRV, hxV⟩ := mem_nullLocus.mp hx
    by_contra hxE
    exact (numericalRestrictedVolume_pos_of_not_subset_nonKahlerLocus omega alpha hpsef V
      hVdim fun h => hxE (h hxV)).ne' hRV

end

end SGPT.Foundations.Analysis.Pending.NakamayeMainTheorem
