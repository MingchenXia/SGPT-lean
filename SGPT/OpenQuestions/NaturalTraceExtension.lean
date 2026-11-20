import SGPT.OpenQuestions.SubmanifoldComponents
import SGPT.PSH.SourceIEnvelope
import SGPT.Foundations.Analysis.Pending.NaturalSubmanifoldSourceTraceDefinition

/-!
# The trace-extension conjecture on an arbitrary closed submanifold

Source `conj:exttracegeneral` (chapter `chapter_history`), stated for an arbitrary
closed complex submanifold `Y` of a connected compact Kähler manifold `X`
(possibly disconnected, components possibly of different dimensions), with the
complex structure and Kähler class that the connected components of `Y` inherit
from `X`, and the trace computed with the natural trace predicate
`IsNaturalSourceTraceRepresentative`. `ClosedSubmanifoldComponent n Y` indexes
exactly the connected components of `Y` (`exists_closedSubmanifoldComponent`,
`ClosedSubmanifoldComponent.ext_of_set`). This is a proposition, not a proof of
the conjecture.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.OpenQuestions

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Foundations.Analysis.Pending.NaturalSubmanifoldSourceTraceDefinition
open SGPT.PSH.VariableComplexAtlas
open scoped Topology Manifold ContDiff

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

section NaturalTraceExtension

/-- The Kähler currents in the restricted class `α|_W` on a closed connected
submanifold `W`, with the complex structure induced from `X`, where `α` is the
class of the Kähler form of `omega`. -/
def NaturalComponentKahlerCurrent (omega : KahlerBackground n M) {W : Set M} {k : ℕ}
    (hW : IsClosedConnectedSubmanifold n W k) : Type u :=
  letI := SubmanifoldChartedSpace.chartedSpace
    (SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW) hW.2.2
  haveI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
    (SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW) hW.2.2
  KahlerCurrent (RealBottChern.ofRepresentative
    (ClosedRealOneOneForm.pullback (SubmanifoldChartedSpace.contMDiff_val
      (SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW) hW.2.2) omega.form))

/-- The potential of a Kähler current on a natural component. -/
def NaturalComponentKahlerCurrent.potential {omega : KahlerBackground n M} {W : Set M}
    {k : ℕ} {hW : IsClosedConnectedSubmanifold n W k}
    (S : NaturalComponentKahlerCurrent omega hW) : W → EReal :=
  letI := SubmanifoldChartedSpace.chartedSpace
    (SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW) hW.2.2
  haveI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
    (SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW) hW.2.2
  KahlerCurrent.potential S

/-- `𝓘`-equivalence of two functions on a natural component (all positive real
exponents, all holomorphic germs, in the induced complex structure). -/
def NaturalComponentIEquivalent {W : Set M} {k : ℕ}
    (hW : IsClosedConnectedSubmanifold n W k) (u v : W → EReal) : Prop :=
  letI := SubmanifoldChartedSpace.chartedSpace
    (SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW) hW.2.2
  haveI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
    (SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW) hW.2.2
  sourceIEquivalent (ofFixedModel k W) u v

/-- Source `conj:exttracegeneral` for the connected compact Kähler manifold `X`,
the closed complex submanifold `Y` and the Kähler class `α = {ω}`: for every
Kähler current `S ∈ α|_Y` (that is, a Kähler current `S_c ∈ α|_{Y_c}` on each
connected component `Y_c` of `Y`) there is a Kähler current `T ∈ α` whose trace
`Tr_{Y_c}(T)` is defined (generic Lelong number zero along `Y_c`) and
`𝓘`-equivalent to `S_c` for every component. A proposition only. -/
def naturalKahlerTraceExtensionStatement [CompactSpace M] [ConnectedSpace M]
    (omega : KahlerBackground n M) (Y : Set M) (_hY : IsClosedSubmanifold n Y) : Prop :=
  ∀ S : ∀ c : ClosedSubmanifoldComponent n Y, NaturalComponentKahlerCurrent omega c.2.2,
    ∃ T : KahlerCurrent (RealBottChern.ofRepresentative omega.form),
      ∀ c : ClosedSubmanifoldComponent n Y, ∃ τ : c.1.1 → EReal,
        IsNaturalSourceTraceRepresentative omega c.2.2 T.potential τ ∧
          NaturalComponentIEquivalent c.2.2 τ (S c).potential

end NaturalTraceExtension

end SGPT.OpenQuestions
