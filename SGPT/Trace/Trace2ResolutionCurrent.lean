import SGPT.Trace.Trace2Resolution
import SGPT.Trace.TraceCurrent

/-!
# Traces of currents along an arbitrary irreducible subvariety, read on a resolution

Source: `chapter_trace.tex`, `rmk:tracecurrent`: for `T ∈ 𝒵₊(X, α)` with `ν(T, Y) = 0` and
`β ∈ H^{1,1}(Ỹ, ℝ)`, `Tr^β_Y(T)` is any closed positive `(1,1)`-current in `β` representing
`Tr_Y(T)`. Blueprint: `claude-trace2.tex`.

The trace-current API (`SGPT.Trace.TraceCurrent`) is stated for an arbitrary compact connected
target `V` of dimension `k + 1` with a holomorphic map `ι : V → X`. Here `V` is a resolution of an
arbitrary irreducible analytic subset `Y` of positive dimension (`Trace2Resolution`):

* `exists_resolution_of_dim`: a resolution of `Y` with charts in `ℂ^d` for every `d = dim Y`;
* `currentGenericLelongNumber_eq_of_resolution`: `ν(T, Y)` along the resolution is the book's
  generic Lelong number of a potential of `T` along `Y`;
* `exists_isTraceCurrent_of_resolution`: if `ν(T, Y) = 0`, some closed positive current on the
  resolution (in a Kähler class) represents `Tr_Y(T)`;
* `sourcePEquivalent_of_isTraceCurrent_of_resolution`: two currents representing `Tr_Y(T)` have
  `P`-equivalent potentials.

As in `Trace2Resolution`, the identification of the resolution with the normalization `Ỹ`
(`cor:PSH`), and of classes on `Ỹ` with classes on the resolution, is not formalized.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

universe u

namespace SGPT.Trace.Trace2Resolution

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.Pending
  SourceTraceRepresentativeDefinition SingularGlobalPOrder
  SGPT.PSH.BookCurrent SGPT.Trace.TraceCurrent

section Dim

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **`thm:res` for `Y`, with the dimension as a parameter.** For every `d = dim Y` there are a
compact connected complex manifold `V` of dimension `d` with a Kähler form and a holomorphic
resolution `ι : V → X` of `Y`. -/
theorem exists_resolution_of_dim [CompactSpace X] (omega : KahlerBackground n X)
    (Y : ClosedIrreducibleAnalyticSubvariety n X) (d : ℕ) (hd : Y.dim = d) :
    ∃ (V : Type u) (_ : TopologicalSpace V) (_ : ChartedSpace (ComplexModel d) V)
      (_ : IsComplexManifold d V) (_ : CompactSpace V) (_ : ConnectedSpace V) (ι : V → X)
      (_ : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel n) ∞ ι),
      IsResolutionOf Y ι ∧ Nonempty (KahlerBackground d V) := by
  subst hd
  obtain ⟨R⟩ := exists_resolutionTarget omega Y
  exact ⟨R.V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, R.ι,
    R.contMDiff, R.isResolutionOf, ⟨R.kahler⟩⟩

end Dim

section Current

variable {m k : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X] [CompactSpace X]
  {Y : ClosedIrreducibleAnalyticSubvariety (m + 1) X}
  {V : Type u} [TopologicalSpace V] [ChartedSpace (ComplexModel (k + 1)) V]
  [IsComplexManifold (k + 1) V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V]
  [ConnectedSpace V] {ι : V → X}
  (hι : ContMDiff 𝓘(ℂ, ComplexModel (k + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ ι)

omit [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V] in
/-- **`ν(T, Y)` along a resolution** (`rmk:tracecurrent`): the generic Lelong number of `T` along
a resolution `ι` of `Y` is the book's generic Lelong number `ν(φ, Y) = min_Y ν(φ, ·)` of a
potential `φ` of `T` (`def:pshfunctions:L1101`). -/
theorem currentGenericLelongNumber_eq_of_resolution (hres : IsResolutionOf Y ι)
    (T : ClosedPositiveCurrent m X) :
    currentGenericLelongNumber T ι =
      (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) X).sourceGenericLelong
        (presentationPotential T) Y.carrier :=
  sourceGenericLelongNumber_eq_sourceGenericLelong hres.range_eq _

/-- **Source `rmk:tracecurrent` for an arbitrary irreducible `Y` of positive dimension, read on
a resolution: existence.** If `ν(T, Y) = 0`, some closed positive `(1,1)`-current on the
resolution, in a Kähler class `β`, represents `Tr_Y(T)` (it is a `Tr^β_Y(T)`). -/
theorem exists_isTraceCurrent_of_resolution (hres : IsResolutionOf Y ι)
    (hk : k + 1 ≤ m + 1) (omega : KahlerBackground (m + 1) X)
    (omegaV : KahlerBackground (k + 1) V) (T : ClosedPositiveCurrent m X)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) X).sourceGenericLelong
        (presentationPotential T) Y.carrier = 0) :
    ∃ (β : KahlerBackground (k + 1) V) (S : ClosedPositiveCurrentIn k V
      (RealBottChern.ofRepresentative β.form)), IsTraceCurrentIn hι omega omegaV T S :=
  exists_isTraceCurrent hι hk omega omegaV T
    ((currentGenericLelongNumber_eq_of_resolution hres T).trans hν)

/-- **Source `rmk:tracecurrent` for an arbitrary irreducible `Y`, read on a resolution:
well-definedness.** Two currents representing `Tr_Y(T)` (arbitrary auxiliary choices) have
`P`-equivalent potentials, and every current representing `Tr_Y(T)` forces `ν(T, Y) = 0`. -/
theorem isTraceCurrent_of_resolution (hres : IsResolutionOf Y ι) (hk : k + 1 ≤ m + 1)
    {omega omega' : KahlerBackground (m + 1) X} {omegaV omegaV' : KahlerBackground (k + 1) V}
    {T : ClosedPositiveCurrent m X} {S S' : ClosedPositiveCurrent k V}
    (hS : IsTraceCurrent hι omega omegaV T S) (hS' : IsTraceCurrent hι omega' omegaV' T S')
    {η η' : ClosedRealOneOneForm (k + 1) V} {τ τ' : V → EReal}
    (hpS : IsPresentation S η τ) (hpS' : IsPresentation S' η' τ') :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) X).sourceGenericLelong
        (presentationPotential T) Y.carrier = 0 ∧
      SourcePEquivalent (n := k + 1) τ τ' :=
  ⟨(currentGenericLelongNumber_eq_of_resolution hres T).symm.trans
      (hS.currentGenericLelongNumber_eq_zero hι),
    hS.sourcePEquivalent hι hk hS' hpS hpS'⟩

end Current

end SGPT.Trace.Trace2Resolution
