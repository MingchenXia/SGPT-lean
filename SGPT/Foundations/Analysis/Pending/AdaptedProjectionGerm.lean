import SGPT.Foundations.Analysis.Pending.PluckerSpanningOpen
import SGPT.Foundations.Analysis.Pending.DecomposableBasisFlatVolume
import SGPT.Foundations.Analysis.Pending.AdaptedProjectionAssembly

set_option autoImplicit false

/-!
# One germ, one direction: the dense half of Demailly's perturbation step

`Pending.PluckerSpanningOpen` proved the OPEN clause of

> After a slight perturbation of the `β_{s,j}`, we may assume that each
> projection `π_s` defines a ramified covering of `A ∩ (Δ'×Δ'')`, and that
> `(β_s)` remains a basis of `Λ^{p,p}T^⋆Ω`
> (`\source{demailly-cadg:III.2.6}`, `agbook.tex:8704`),

namely that spanning survives every small move of the family.  This module names
the remaining, DENSE clause — and nothing else.

`exists_adaptedProjection` fixes ONE point `x` of ONE irreducible analytic
subvariety `V` and ONE prescribed direction `B₀`, and asks for a direction `B`
arbitrarily close to `B₀` that is a ramified covering of the germ of `V` at `x`,
in the almost-everywhere form `Pending.MultiplicityAreaBound` consumes.  There is
no family in it, no spanning, no basis of `Λ^{k,k}`, and no simultaneously
generic linear change of `ℂⁿ`: those were exactly the ingredients that the
openness lemma now supplies for free, `s` by `s`.

This is the classical local parametrization of an analytic germ together with
the genericity of the projection direction (Demailly CADG II.3.8/II.3.19): the
directions that fail form a proper analytic subset of the space of surjections
`ℂⁿ → ℂ^k`, hence a set with dense complement, which is why `B₀` may be
prescribed and only approximated.  The project already has the exact-fibre form
of the conclusion for a germ presented by parametrization data,
`Pending.GermParametrizationData.SetsData.ncard_fibre`, and its
almost-everywhere consequence
`Pending.ParametrizationFibreBound.exists_fibreBound`; what is not built is the
producer of that data at an arbitrary point of a
`ClosedIrreducibleAnalyticSubvariety`, in coordinates adapted to it.

Checked against the degenerate cases.  For `V.dim = 0` the target is the zero
space, `B = B₀ = 0` is admissible, `Δ = univ` has volume `1`, and the fibre
clause says that a small enough `U` meets `V` in finitely many points, which
holds because a `0`-dimensional analytic set is discrete.  For `n = 0` this is
the same statement.  The almost-everywhere quantifier is not cosmetic: the fibre
over a branch point of the covering is smaller, but the fibre over a point of
the image of a positive-dimensional fibre of a BAD direction is infinite, and no
pointwise bound survives perturbation.  Since the fibre clause quantifies over
all of `ℂ^k` and the part of `U ∩ V` mapping outside `Δ` is empty by the
preceding clause, nothing is asserted off `Δ` beyond `∅.encard = 0 ≤ N`.
-/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.AdaptedProjectionGerm

open FirstPass
open SGPT.Foundations.Analysis.Pending.CauchyBinet
  SGPT.Foundations.Analysis.Pending.PluckerSpanningBound
  SGPT.Foundations.Analysis.Pending.LinearProjectionJacobian

/-- Reindexing a spanning family along a surjection keeps it spanning: the
condition only quantifies over the members. -/
theorem spansPlucker_comp {k n : ℕ} {σ τ : Type*} {B : σ → Matrix (Fin k) (Fin n) ℂ}
    (hB : SpansPlucker B) {f : τ → σ} (hf : Function.Surjective f) :
    SpansPlucker fun t => B (f t) := by
  intro ξ h
  refine hB ξ fun s => ?_
  obtain ⟨t, rfl⟩ := hf s
  exact h t

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Demailly CADG III.2.6, the DENSE clause of the perturbation.**  Let `x` be a point of an
irreducible analytic subvariety `V` of dimension `k`, let `B₀ : ℂⁿ → ℂ^k` be any
`ℂ`-linear map and let `δ > 0`.  Then there is `B` with `‖B - B₀‖ < δ`, a
neighbourhood `U` of `x` inside the source of the preferred chart at `x`, a
measurable `Δ ⊆ ℂ^k` of finite volume and an integer `N`, such that `B` maps the
part of `V` in `U` into `Δ` with at most `N` points over almost every value.

Together with `Pending.PluckerSpanningOpen.exists_dist_lt_spansPlucker` this is
the whole of Demailly's perturbation sentence, and hence — through
`Pending.DecomposableBasisSheetBound.exists_decomposableBasisSheetBound` and
`Pending.LocalFlatVolumeBound` — the last step of the Lelong local bound at
singular points.  See the module docstring for why the `B₀` and `δ` are part of
the statement rather than a weakening of it: the openness lemma consumes exactly
the freedom to prescribe the direction being perturbed.

It is no longer a bare `sorry`.  `Pending.AdaptedProjectionAssembly` proves it
from the local parametrization theorem of this project — Noether normalization,
the algebraic parametrization, the parametrizing sets and their exact fibre count
— together with the decomposition of the germ of `V` at `x` into irreducible
components, the finite union of sheet bounds and the passage from the chart germ
to `V`.  Exactly two classical statements are left there: the genericity of the
normalizing direction, and the pure dimension of an irreducible analytic set. -/
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
            ≤ (N : ℕ∞)) :=
  AdaptedProjectionAssembly.exists_adaptedProjection V hx B₀ hδ

end SGPT.Foundations.Analysis.Pending.AdaptedProjectionGerm
