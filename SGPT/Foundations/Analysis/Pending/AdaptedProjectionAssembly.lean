import SGPT.Foundations.Analysis.Pending.IrreducibleGermSheetBound
import SGPT.Foundations.Analysis.Pending.GermComponentDimension

set_option autoImplicit false

/-!
# Demailly's perturbation step at a point of a subvariety, assembled

`Pending.AdaptedProjectionGerm.exists_adaptedProjection` asks, at a point `x` of a
closed irreducible analytic subvariety `V` of dimension `k`, for a direction `B`
within `δ` of a prescribed `B₀` which is a ramified covering of `V` near `x`, in
the almost-everywhere form.  This module assembles it from the pieces:

* the germ of `V` at `x`, read in the preferred chart and translated to the
  origin, is an analytic germ
  (`Pending.AnalyticDescendingChain.isAnalyticGerm_chartGerm`) and is therefore,
  near `0`, an irredundant finite union of irreducible germs
  (`Pending.AnalyticGermDecomposition.exists_irreducible_decomposition_euclidean`);
* `Pending.IrreducibleGermSheetBound.exists_germSheetBound_near` gives ONE
  direction within `δ` of `B₀` that is a ramified covering of every member of
  that family, hence of their union;
* `Pending.ChartGermSheetBound.GermSheetBound.congr` moves the bound from the
  union back to the chart germ, and
  `Pending.ChartGermSheetBound.exists_adaptedProjection_of_chartGermSheetBound`
  moves it from the chart germ to `V` itself, keeping the direction.

The DIMENSION of the components — they must all be of dimension `V.dim`, which is
the pure-dimensionality of an irreducible analytic set — is
`exists_pureDimensionParametrizationData`, and it is now PROVED in
`Pending.GermComponentDimension`.  The only remaining classical input of the
Lelong local bound at singular points is therefore the genericity of the
normalizing direction,
`Pending.IrreducibleGermSheetBound.exists_parametrizationData_near`.

The irredundancy of the decomposition is not decoration: without it the family may
contain, say, the germ `{0}`, which is irreducible of dimension `0` and changes
neither the union nor its sheet bound, and then no common dimension exists.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.AdaptedProjectionAssembly

open FirstPass
open SGPT.Foundations.Analysis.Pending.AnalyticDescendingChain
open SGPT.Foundations.Analysis.Pending.AnalyticGermDecomposition
open SGPT.Foundations.Analysis.Pending.GermParametrizationData
open SGPT.Foundations.Analysis.Pending.ChartGermSheetBound
open SGPT.Foundations.Analysis.Pending.IrreducibleGermSheetBound

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

set_option linter.unusedVariables false in
/-- **Pure dimension of an irreducible analytic subvariety, PROVED.**  Let `V` be a
closed irreducible analytic subvariety of dimension `V.dim`, let `x ∈ V`, and let
`A₁, …, A_r` be an irredundant family of irreducible analytic germs whose union
is, near `0`, the chart germ of `V` at `x`.  Then every `A i` is put in Noether
position over `𝒪_{V.dim}` by some linear change of coordinates, with
parametrization data of dimension exactly `V.dim`.

The content is that the local irreducible components of `V` at ANY of its points
all have the dimension certified once and for all by `V.regularLocus_nonempty`: an
irreducible analytic set is of pure dimension.  It is now
`Pending.GermComponentDimension.dim_eq_of_parametrizationData`, which relates
`V.dim` — a field certified by one regular point — to the Noether dimension of a
germ: the parametrization data of a germ exhibits regular points of its own
dimension arbitrarily near `0`, thinness of the pairwise intersections lets such a
point be chosen in an open set meeting no other component, and there the chart
germ of `V` coincides with that component, so the point is a regular point of `V`
and `Pending.PureDimension.eq_dim_of_regularAtDim` applies.

Checked against the degenerate cases.  For `r = 0` the conclusion is empty and the
statement says nothing; this happens only when the chart germ is empty near `0`,
which for `x ∈ V.carrier` it is not.  For `V.dim = 0` the point `x` is isolated in
`V`, each component is the germ `{0}` and its parametrization data has dimension
`0`.  For `n = 0` the only subvariety is a point.  The irredundancy hypothesis is
necessary: adding the germ `{0}` to a decomposition changes neither the union nor
any sheet bound, and `{0}` has Noether dimension `0`.

`hx` is not used by the proof and is deliberately kept: for `r = 0` the conclusion
holds vacuously, and for `r ≥ 1` the nonemptiness of each germ near `0` comes from
`IsIrreducibleGerm` rather than from `x ∈ V.carrier`.  Removing it would change the
statement of an existing declaration, which is why the linter is silenced here
instead. -/
theorem exists_pureDimensionParametrizationData
    (V : ClosedIrreducibleAnalyticSubvariety n M) {x : M} (hx : x ∈ V.carrier)
    {r : ℕ} {A : Fin r → Set (ComplexModel n)}
    (hA : ∀ i, IsIrreducibleGerm (A i))
    (hcover : chartGerm (n := n) V.carrier x =ᶠ[𝓝 0] (⋃ i, A i))
    (hpw : Pairwise fun i j => ¬ (A i ≤ᶠ[𝓝 0] A j)) :
    ∃ (L₀ : Fin r → ComplexModel n ≃L[ℂ] ComplexModel n)
      (P₀ : ∀ i, ParametrizationData (L₀ i ⁻¹' A i)), ∀ i, (P₀ i).dim = V.dim := by
  have h : ∀ i, ∃ (L : ComplexModel n ≃L[ℂ] ComplexModel n)
      (P : ParametrizationData (L ⁻¹' A i)), P.dim = V.dim := by
    intro i
    obtain ⟨L, ⟨P⟩⟩ := exists_noetherParametrizationData (hA i)
    obtain ⟨S⟩ := nonempty_setsData P
    exact ⟨L, P, GermComponentDimension.dim_eq_of_parametrizationData V hA hcover hpw i P S⟩
  choose L₀ P₀ hdim using h
  exact ⟨L₀, P₀, hdim⟩

/-- **Demailly's perturbation step at a point of a subvariety**, from the
genericity of the normalizing direction and the pure dimension of the germ.  The
statement is that of
`Pending.AdaptedProjectionGerm.exists_adaptedProjection`; every geometric and
measure-theoretic step between the local parametrization theorem and it — the
chart germ, its decomposition, the common direction, the finite union, the
injection of a fibre upstairs into a fibre of the germ, and the translation of the
base point — is discharged. -/
theorem exists_adaptedProjection (V : ClosedIrreducibleAnalyticSubvariety n M)
    {x : M} (hx : x ∈ V.carrier)
    (B₀ : ComplexModel n →L[ℂ] ComplexModel V.dim) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (B : ComplexModel n →L[ℂ] ComplexModel V.dim) (U : Set M)
      (Δ : Set (ComplexModel V.dim)) (N : ℕ),
      ‖B - B₀‖ < δ ∧
        IsOpen U ∧ x ∈ U ∧ U ⊆ (complexChartAt (n := n) x).val.source ∧
        MeasurableSet Δ ∧ volume Δ ≠ ⊤ ∧
        (∀ z ∈ U ∩ V.carrier, B ((complexChartAt (n := n) x).val z) ∈ Δ) ∧
        (∀ᵐ y : ComplexModel V.dim,
          {z | z ∈ U ∩ V.carrier ∧ B ((complexChartAt (n := n) x).val z) = y}.encard
            ≤ (N : ℕ∞)) := by
  obtain ⟨r, A, hAirr, -, hcover, hpw⟩ :=
    exists_irreducible_decomposition_euclidean
      (isAnalyticGerm_chartGerm (n := n) V.analytic x)
  obtain ⟨L₀, P₀, hdim⟩ := exists_pureDimensionParametrizationData V hx hAirr hcover hpw
  obtain ⟨B, hnorm, hbound⟩ := exists_germSheetBound_near hAirr P₀ hdim V.dim_le B₀ hδ
  obtain ⟨U, Δ, N, hU, hxU, hUsub, hΔ, hΔt, hmaps, hfib⟩ :=
    exists_adaptedProjection_of_chartGermSheetBound V x (ChartGermSheetBound.GermSheetBound.congr hbound hcover)
  exact ⟨B, U, Δ, N, hnorm, hU, hxU, hUsub, hΔ, hΔt, hmaps, hfib⟩

end SGPT.Foundations.Analysis.Pending.AdaptedProjectionAssembly
