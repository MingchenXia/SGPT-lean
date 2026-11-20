import SGPT.OpenQuestions.TraceStatements
import SGPT.Okounkov.SourceTraceIdealOrder
import SGPT.Foundations.Analysis.Pending.RooftopDimZero
import SGPT.Foundations.Analysis.Pending.GlobalPMultiplierOrder

/-!
# The proposed formalization of `prob:history:L221` is a theorem

`SGPT.OpenQuestions.sourceTracePRefinementStatement` (traces of `P`-equivalent
potentials are `P`-equivalent, for arbitrary auxiliary backgrounds) was proposed
as a formalization of the open problem `prob:history:L221`. It is provable: it
follows from `P`-equivalence implying `𝓘`-equivalence and from the monotonicity
of the trace operator in the multiplier order (`prop:tracelinear` (1)). Hence it
is not a faithful formalization of the problem, whose informal "refinement"
requirement (an operator on `P`-classes that is finer than the existing one) has
no precise content in the source.
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
open SGPT.PSH.VariableComplexAtlas
open scoped Topology Manifold ContDiff

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

section PRefinement

variable [MeasurableSpace M] [BorelSpace M]

omit [MeasurableSpace M] [BorelSpace M] in
private theorem sourceTrace_background {k : ℕ} {V : Type*} [TopologicalSpace V]
    [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
    [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]
    {omega : KahlerBackground n M} {omegaV : KahlerBackground k V} {ι : V → M}
    {hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι}
    {u : M → EReal} {τ : V → EReal}
    (htrace : IsSourceTraceRepresentativeAlong omega omegaV hι u τ) :
    ∃ β : KahlerBackground k V, IsThetaPshPotential β.form.val τ := by
  obtain ⟨_hzero, _θ, _ε, _uSeq, _hqea, β, _hβ, hτ, _hterms, _hlim⟩ := htrace
  exact ⟨β, hτ⟩

private theorem moreSingularOn_of_zero_dim {V : Type*} [TopologicalSpace V]
    [ChartedSpace (ComplexModel 0) V] [IsComplexManifold 0 V] [ConnectedSpace V]
    {θ σ : SmoothRealForm 0 V 2} {u v : V → EReal}
    (hu : IsThetaPshPotential θ u) (hv : IsThetaPshPotential σ v) :
    MoreSingularOn u v univ := by
  let : DiscreteTopology V := discreteTopology_iff_isOpen_singleton.mpr
    (RooftopDimZero.isOpen_singleton_of_dim_zero rfl)
  let : Subsingleton V := subsingleton_of_preconnected_totallyDisconnected
  let x : V := Classical.arbitrary V
  have huco : ((u x).toReal : EReal) = u x := EReal.coe_toReal
    (hu.1.quasiPlurisubharmonic.ne_top x)
    (RooftopDimZero.ne_bot_of_locallyNondegenerate_of_dim_zero rfl hu.2 x)
  have hvco : ((v x).toReal : EReal) = v x := EReal.coe_toReal
    (hv.1.quasiPlurisubharmonic.ne_top x)
    (RooftopDimZero.ne_bot_of_locallyNondegenerate_of_dim_zero rfl hv.2 x)
  refine ⟨(u x).toReal - (v x).toReal, ?_⟩
  intro y _hy
  rw [Subsingleton.elim y x, ← huco, ← hvco, ← EReal.coe_add]
  exact_mod_cast (by linarith : (u x).toReal ≤ (v x).toReal + ((u x).toReal - (v x).toReal))

/-- The proposition `sourceTracePRefinementStatement` is a theorem: traces of
`P`-equivalent potentials are `P`-equivalent, for arbitrary auxiliary
backgrounds. (`P`-equivalence implies `𝓘`-equivalence, and the trace is monotone
for the multiplier order.) Hence it is not a formalization of the open problem
`prob:history:L221`. -/
theorem sourceTracePRefinementStatement_holds [CompactSpace M]
    (Y : Set M) (k : ℕ) [ChartedSpace (ComplexModel k) Y] [IsComplexManifold k Y]
    [CompactSpace Y] [ConnectedSpace Y]
    (hY : IsClosedConnectedSubmanifold n Y k)
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞
      (Subtype.val : Y → M)) :
    sourceTracePRefinementStatement Y k hY hι := by
  intro omega₀ omega₁ omegaY₀ omegaY₁ u v τu τv hu hv huv
  have hk : k ≤ n := SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hY
  by_cases hn : n = 0
  · subst n
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    obtain ⟨β₀, hτ₀⟩ := sourceTrace_background hu
    obtain ⟨β₁, hτ₁⟩ := sourceTrace_background hv
    exact ⟨SingularGlobalPOrder.sourcePOrder_of_moreSingularOn omegaY₀ β₀.form β₁.form hτ₀ hτ₁
        (moreSingularOn_of_zero_dim hτ₀ hτ₁),
      SingularGlobalPOrder.sourcePOrder_of_moreSingularOn omegaY₀ β₁.form β₀.form hτ₁ hτ₀
        (moreSingularOn_of_zero_dim hτ₁ hτ₀)⟩
  · have : Nonempty M := ⟨(Classical.arbitrary Y).1⟩
    have hI := GlobalPMultiplierOrder.iEquivalentOnManifold_of_sourcePEquivalent huv
    exact ⟨SGPT.Okounkov.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives hn
        omegaY₀ omegaY₁ hι hu hv hI.1,
      SGPT.Okounkov.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives hn
        omegaY₁ omegaY₀ hι hv hu hI.2⟩

end PRefinement

end SGPT.OpenQuestions
