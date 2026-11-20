import SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
import SGPT.PSH.GlobalPComparison
import SGPT.PSH.SourceIEnvelope

/-! Faithful assertions associated with the original open trace questions.

These declarations define propositions. They do not prove the conjecture or
assert that the requested extension/refinement exists. The finite-component
extension assertion is kept separate from the original whole-current
component decomposition and assembly problem.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.OpenQuestions

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.PSH.VariableComplexAtlas
open scoped Topology Manifold ContDiff

universe u v

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M]

/-- Component formulation of original `conj:exttracegeneral`: a SINGLE
ambient current must extend the prescribed currents on all disjoint
components. A proposition statement only, not a proof of the conjecture. -/
def finiteComponentKahlerTraceExtensionStatement [CompactSpace M] [ConnectedSpace M]
    {J : Type v} [Finite J] (Y : J → Set M) (k : J → ℕ)
    [∀ j, ChartedSpace (ComplexModel (k j)) (Y j)]
    [∀ j, IsComplexManifold (k j) (Y j)]
    [∀ j, CompactSpace (Y j)] [∀ j, ConnectedSpace (Y j)]
    (_hY : ∀ j, IsClosedConnectedSubmanifold n (Y j) (k j))
    (_hdisj : Pairwise (fun i j ↦ Disjoint (Y i) (Y j)))
    (hι : ∀ j, ContMDiff 𝓘(ℂ, ComplexModel (k j)) 𝓘(ℂ, ComplexModel n) ∞
      (Subtype.val : Y j → M))
    (omega : KahlerBackground n M)
    (omegaY : ∀ j, KahlerBackground (k j) (Y j)) : Prop :=
  ∀ S : ∀ j, KahlerCurrent (RealBottChern.ofRepresentative
      (ClosedRealOneOneForm.pullback (hι j) omega.form)),
    ∃ T : KahlerCurrent (RealBottChern.ofRepresentative omega.form),
      ∀ j, ∃ τ : Y j → EReal,
        IsSourceTraceRepresentativeAlong omega (omegaY j) (hι j) T.potential τ ∧
        sourceIEquivalent (ofFixedModel (k j) (Y j)) τ (S j).potential

/-- Original `prob:history:L221`, expressed as representative invariance
of the genuine source trace relation for the original P quotients.
The ambient manifold need not be connected. This is a proposition statement,
not a proof that the proposed quotient operator is available. -/
def sourceTracePRefinementStatement [CompactSpace M]
    (Y : Set M) (k : ℕ) [ChartedSpace (ComplexModel k) Y] [IsComplexManifold k Y]
    [CompactSpace Y] [ConnectedSpace Y]
    (_hY : IsClosedConnectedSubmanifold n Y k)
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞
      (Subtype.val : Y → M)) : Prop :=
  ∀ (omega₀ omega₁ : KahlerBackground n M)
    (omegaY₀ omegaY₁ : KahlerBackground k Y)
    (u v : M → EReal) (τu τv : Y → EReal),
    IsSourceTraceRepresentativeAlong omega₀ omegaY₀ hι u τu →
    IsSourceTraceRepresentativeAlong omega₁ omegaY₁ hι v τv →
    SGPT.PSH.GlobalPComparison.sourcePEquivalent (n := n) u v →
    SGPT.PSH.GlobalPComparison.sourcePEquivalent (n := k) τu τv

end SGPT.OpenQuestions
