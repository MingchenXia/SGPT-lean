import SGPT.Foundations.Analysis.Pending.FlatPatchDensityComparison
import SGPT.Foundations.Analysis.Pending.FlatDensityGramDeterminant
import SGPT.Foundations.Analysis.Pending.FlatVolumeFibreBound
import SGPT.Foundations.Analysis.Pending.ProjectedPatchJacobian
import SGPT.Foundations.Analysis.Pending.DecomposableBasisSheetBound
import SGPT.Foundations.Analysis.Pending.FamilyFibreCount

set_option autoImplicit false

/-!
# The local flat volume bound in one chart (named classical input)

Demailly, *Complex analytic and differential geometry*, III.2.6: an analytic
subset of an open subset of `ℂⁿ` has locally finite `2k`-dimensional volume,
where `k` is its dimension.  In the parametrization language of this project
that is exactly the statement below: near any point of `V` there is a
neighbourhood on which the sum, over the finitely many disjoint pieces of any
regular-piece family, of the FLAT parameter densities of one fixed chart is
bounded.

This is the whole of the classical input behind the local finite-volume bound
`Pending.SubvarietyBackgroundMass.exists_localBackgroundBound`.  Nothing else is
left in it: no Kähler background, no class, no presentation, no potential and no
pole set — one chart, one analytic subvariety and the flat metric of that chart.
The passage from this statement to the bound for the background Kähler form is
proved in `Pending.SubvarietyBackgroundMass` from
`Pending.FlatPatchDensityComparison`: the coefficient of a Kähler form is bounded
on a compact part of the chart target, so its parameter density is at most a
constant times the flat one.

The proof below is Demailly's own.  By Wirtinger the flat density of the
parametrization is the Gram determinant `k!·Re det (LᴴL)`; a family of
decomposable `(k,k)`-forms that is still a BASIS bounds that determinant by a
constant times the sum of the squared moduli of the corresponding `k × k`
determinants (`Pending.PluckerSpanningBound`); each of those is the real Jacobian
of the linear projection attached to the basis form
(`Pending.LinearProjectionJacobian`); and a family of maps into `Δ` with at most
`N` preimages over almost every point integrates its Jacobian to at most `N`
times `vol Δ` (`Pending.MultiplicityAreaBound`).  The assembly is
`Pending.DecomposableBasisFlatVolume.exists_flatVolumeConst`.

`exists_localFlatVolumeBound_gram` below records the same statement with the flat
density replaced by the Gram determinant `k! · Re det (LᴴL)` of
`Pending.FlatDensityGramDeterminant`, which is the form the expansion consumes.

Everything above is proved; the one remaining input is
`Pending.DecomposableBasisSheetBound.exists_decomposableBasisSheetBound`, the
perturbed decomposable basis: a finite family of `ℂ`-linear maps `ℂⁿ → ℂ^k`
whose Plücker functionals still separate points, each of which is a ramified
covering of `V` near `x` with one sheet number.  That is the sentence of CADG
III.2.6 itself.

What left this statement and cannot come back is the FIXED chart.  The `binom n k`
coordinate projections of one chart do span
(`Pending.DecomposableBasisSheetBound.spansPlucker_subsetProjection`), so the
earlier route was the special case in which nothing is perturbed — and that is
the one case Demailly avoids, because bounding the local degree of a fixed
projection is not a classical theorem, while bounding it in coordinates ADAPTED
to the germ is (CADG II.3.8/II.3.19, and in this project
`Pending.GermParametrizationData.SetsData.ncard_fibre` with its
almost-everywhere form `Pending.ParametrizationFibreBound.exists_fibreBound`).
Perturbing each basis form separately costs nothing because spanning is open;
adaptedness is dense.  So `ana:generic-local-degree` is no longer on this path.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.LocalFlatVolumeBound

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolume
  FirstPass.RegularPatchNeighborhood
open FlatPatchDensityComparison
open SGPT.Foundations.Analysis.Pending.CauchyBinet
  SGPT.Foundations.Analysis.Pending.SubsetProjection
  SGPT.Foundations.Analysis.Pending.ProjectedPatchJacobian
  SGPT.Foundations.Analysis.Pending.FlatVolumeFibreBound
  SGPT.Foundations.Analysis.Pending.LinearProjectionJacobian
  SGPT.Foundations.Analysis.Pending.DecomposableBasisFlatVolume
  SGPT.Foundations.Analysis.Pending.DecomposableBasisSheetBound
  SGPT.Foundations.Analysis.Pending.FamilyFibreCount

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **NAMED CLASSICAL INPUT (Demailly CADG III.2.6, local finite volume).**
Every point of `V` has a neighbourhood inside the source of its preferred chart
on which the total FLAT parameter mass of every finite family of disjoint
regular pieces is bounded by one constant.

The flat parameter density `flatPatchDensity e P` is the Jacobian of
`e ∘ P.toManifold` measured against the flat metric of the chart `e`, so the sum
below is the `2·dim V`-dimensional flat volume, counted with multiplicity, of the
part of `V_reg` that the family covers. -/
theorem exists_localFlatVolumeBound (V : ClosedIrreducibleAnalyticSubvariety n M)
    {x : M} (hx : x ∈ V.carrier) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ U ⊆ (complexChartAt (n := n) x).val.source ∧
      ∃ N : ℝ≥0∞, N ≠ ⊤ ∧
        ∀ F : RegularPieceFamily V (∅ : Set M),
          (∀ i, (F.patch i).toManifold '' F.piece i ⊆ U) →
          ∑ i, ∫⁻ w in F.piece i,
              ENNReal.ofReal
                (flatPatchDensity (complexChartAt (n := n) x) (F.patch i) w) ≤ N := by
  classical
  obtain ⟨m, B, U, Δ, N₀, hspan, hUopen, hxU, hUsub, hΔm, hΔtop, hmapsV, hfibV⟩ :=
    exists_decomposableBasisSheetBound V hx
  obtain ⟨C, hCtop, hC⟩ := exists_flatVolumeConst B hspan
  refine ⟨U, hUopen, hxU, hUsub, C * (N₀ : ℝ≥0∞) * volume Δ, ?_, ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hCtop (by simp)) hΔtop
  · intro F hF
    have hmem : ∀ (i : Fin F.size), ∀ w ∈ F.piece i,
        (F.patch i).toManifold w ∈ U ∩ V.carrier := by
      intro i w hw
      refine ⟨hF i ⟨w, hw, rfl⟩, ?_⟩
      exact regularLocus_subset (n := n) V.carrier V.dim
        (F.image_subset_regularLocus i ⟨w, hw, rfl⟩)
    have hchart : ∀ i, F.piece i ⊆ chartDomain (complexChartAt (n := n) x) (F.patch i) :=
      fun i w hw => ⟨F.piece_subset i hw, hUsub (hmem i w hw).1⟩
    have hmaps : ∀ (s : Fin m) (i : Fin F.size),
        Set.MapsTo
          (linearProjectedParametrization (B s) (complexChartAt (n := n) x) (F.patch i))
          (F.piece i) Δ :=
      fun s i w hw => hmapsV s _ (hmem i w hw)
    have hfib : ∀ s : Fin m, ∀ᵐ y : ComplexModel V.dim,
        y ∈ Δ →
          ∑ i, (F.piece i ∩
              linearProjectedParametrization (B s) (complexChartAt (n := n) x)
                (F.patch i) ⁻¹' {y}).encard ≤ (N₀ : ℕ∞) := by
      intro s
      filter_upwards [hfibV s] with y hy _
      refine le_trans ?_ hy
      exact sum_encard_preimage_le F (U := U ∩ V.carrier)
        (fun i => fun _ hz => by
          obtain ⟨w, hw, rfl⟩ := hz
          exact hmem i w hw)
        (fun z => B s ((complexChartAt (n := n) x).val z)) y
    exact hC (complexChartAt (n := n) x) F hchart hΔm hmaps hfib

/-- The same bound with the flat density written as a Gram determinant.  This is
the shape the Cauchy--Binet expansion consumes: `L = D(e ∘ γ)_w` and the density
is `k!` times the real part of `det (LᴴL)`. -/
theorem exists_localFlatVolumeBound_gram (V : ClosedIrreducibleAnalyticSubvariety n M)
    {x : M} (hx : x ∈ V.carrier) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ U ⊆ (complexChartAt (n := n) x).val.source ∧
      ∃ N : ℝ≥0∞, N ≠ ⊤ ∧
        ∀ F : RegularPieceFamily V (∅ : Set M),
          (∀ i, (F.patch i).toManifold '' F.piece i ⊆ U) →
          ∑ i, ∫⁻ w in F.piece i,
              ENNReal.ofReal ((V.dim.factorial : ℝ) *
                ((FlatDensityGramDeterminant.rectGram
                  (chartPullbackDerivative (complexChartAt (n := n) x)
                    (F.patch i) w)).det).re) ≤ N := by
  obtain ⟨U, hUopen, hxU, hUsub, N, hNtop, hN⟩ := exists_localFlatVolumeBound V hx
  refine ⟨U, hUopen, hxU, hUsub, N, hNtop, fun F hF => ?_⟩
  refine le_trans (le_of_eq ?_) (hN F hF)
  refine Finset.sum_congr rfl fun i _ => MeasureTheory.setLIntegral_congr_fun
    (F.measurableSet_piece i) fun w hw => ?_
  have hchart : w ∈ chartDomain (complexChartAt (n := n) x) (F.patch i) :=
    ⟨F.piece_subset i hw, hUsub (hF i ⟨w, hw, rfl⟩)⟩
  exact congrArg ENNReal.ofReal
    (FlatDensityGramDeterminant.flatPatchDensity_eq_gram _ _ hchart).symm

end

end SGPT.Foundations.Analysis.Pending.LocalFlatVolumeBound
