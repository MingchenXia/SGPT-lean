import SGPT.Foundations.Analysis.Pending.ClosedCurrentMassFinitenessReduction

set_option autoImplicit false

/-!
# The finite pairing-remainder datum of the closed-current argument

`ClosedCurrentFinitePairingRemainderData`: for a sequence of regular-piece families of a
positive-dimensional irreducible analytic subvariety `V` whose pieces carry local telescope
potentials, finite local weighted-patch pairing remainders whose real bound tends to zero.

The named input that asserted this datum along every such sequence
(`closedCurrentFinitePairingRemainderData_of_closed_integrationCurrent`) and the four
declarations that only consumed it were RETIRED by human decision I-0902 (on I-0826): the input
had no consumer outside this module, and without exhaustion hypotheses it was false (inbox I-0839).
The live, proved form is
`CertifiedClosedCurrentStokes.certifiedFinitePairingRemainderData_of_closed_integrationCurrent`
(along an exhaustion with plurisubharmonic local potentials); the structure below stays because
`CertifiedClosedCurrentStokes.closedCurrentFinitePairingRemainderData_of_certified` produces it.

Source: Lelong, *Intégration sur un ensemble analytique complexe* (1957), and
Demailly, *Complex Analytic and Differential Geometry*, III, Theorem 2.7
(`demailly-cadg:III.2.7`).
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.PositiveDimensionalClosedCurrentStokes

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume
open ClosedCurrentMassLimitReduction
open SingularCollarMassErrorReduction
open PartitionPairingCollarErrorReduction
open PartitionPairingCollarErrorReduction.ExhaustionPartitionPairingRemainderData
open FormPieceMassCurrentPairingBridge.FormPieceTelescopeData
open ClosedCurrentMassFinitenessReduction

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The precise finite-cutoff datum supplied by the external closed-current
argument. For each good finite regular-piece family, it supplies local
weighted-pushforward measures and identifies the finite density telescope with
their scalar pairings. The absolute value of their finite sum is bounded by a
real remainder which tends to zero along the supplied exhaustion.

The good local telescope data, both density positivity statements, the
current-side finite mass (by compact K\"ahler domination), and the background
finite mass are already derived internally. This interface therefore retains
only the local weighted pairing construction and its vanishing collar bound. It
does not state finite mass equality, a common limit, or a global Stokes law. -/
structure ClosedCurrentFinitePairingRemainderData
    [CompactSpace M] (beta : KahlerBackground n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    (hq : q.representative = 0) {v : M → ℝ} (hvs : ChartSmooth (n := n) v)
    (hpot : q.potential = fun x => ((v x : ℝ) : EReal))
    (H : ℕ → RegularPieceFamily V (∅ : Set M))
    (hgood : ∀ m i, RegularPieceGoodExhaustion.HasLocalTelescopePotential q hvs
      ((H m).patch i) ((H m).piece i))
    (hV : V.dim ≠ 0) where
  pairingRemainder : ∀ m,
    FiniteTelescopePairingRemainderData
      (of_localTelescopePotential (hgood m))
  tendsto_remainder : Tendsto
    (fun m => (pairingRemainder m).remainder) atTop (𝓝 0)

end

end SGPT.Foundations.Analysis.Pending.PositiveDimensionalClosedCurrentStokes
