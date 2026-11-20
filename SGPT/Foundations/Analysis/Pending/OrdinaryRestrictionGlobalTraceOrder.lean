import SGPT.Foundations.Analysis.Pending.TraceRepresentativeConstruction
import SGPT.Foundations.Analysis.Pending.SingularNativeGlobalPOrderClosed
import SGPT.Foundations.Analysis.Pending.SingularNativeCommonBackground
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple

set_option autoImplicit false

/-! # A genuine non-pole ordinary restriction lies globally below its trace -/

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.OrdinaryRestrictionGlobalTraceOrder

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground
  TraceRepresentativeConstruction SingularGlobalPOrder ThetaPshL1Topology
  SingularCanonicalSingularityDistance PluripolarCapacityDichotomy

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- Actual corrected pullback and a natural non-pole point produce strong
ordinary restriction, then native order closure compares it with the trace. -/
theorem sourcePOrder_ordinaryRestriction_of_isTraceRepresentativeAlong
    {omega : KahlerBackground n M} (omegaV : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u : M → EReal} {τ : V → EReal}
    (htrace : IsTraceRepresentativeAlong omega omegaV hι u τ)
    (hne : ∃ y : V, u (ι y) ≠ ⊥) :
    SourcePOrder (n := k) (fun y => u (ι y)) τ := by
  obtain ⟨_, θ, ε, uSeq, happ, β, _, hτ, hv, hlim⟩ := htrace
  let ρ : ClosedRealOneOneForm k V := ClosedRealOneOneForm.pullback hι θ
  have hRraw : ThetaPlurisubharmonic ρ.val (fun y => u (ι y)) :=
    GlobalPotentialPullback.thetaPlurisubharmonic_comp hι happ.target.1
  have hR : IsThetaPshPotential ρ.val (fun y => u (ι y)) :=
    ThetaPshIdentityPrinciple.isThetaPshPotential_of_exists_ne_bot hRraw hne
  let B : Bool → ClosedRealOneOneForm k V := fun b => if b then ρ else β.form
  obtain ⟨C, hC, hsemi⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul
    omegaV (fun b : Bool => -(B b))
  let γ : KahlerBackground k V := KahlerBackground.smul hC omegaV
  have hγof (b : Bool) {p : V → EReal} (hp : IsThetaPshPotential (B b).val p) :
      IsThetaPshPotential γ.form.val p := by
    have hform : B b + (-B b + C • omegaV.form) = γ.form := by
      dsimp only [γ, KahlerBackground.smul_form]
      module
    simpa only [hform] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hp (hsemi b)
  have hRγ : IsThetaPshPotential γ.form.val (fun y => u (ι y)) := hγof true hR
  have hτγ : IsThetaPshPotential γ.form.val τ := hγof false hτ
  have hvγ (j : ℕ) : IsThetaPshPotential γ.form.val (fun y => uSeq j (ι y)) :=
    hγof false (hv j)
  have hlimγ := (SingularNativeCommonBackground.tendsto_native_iff_kahler_targets
    omegaV β γ atTop hv hτ hvγ hτγ).mp hlim
  let R : ThetaPshL1 γ.form.val := ⟨fun y => u (ι y), hRγ⟩
  let T : ThetaPshL1 γ.form.val := ⟨τ, hτγ⟩
  let A : ℕ → ThetaPshL1 γ.form.val := fun j => ⟨fun y => uSeq j (ι y), hvγ j⟩
  have horder : ∀ᶠ j in atTop, SourcePOrder (n := k) R.val (A j).val := by
    apply Filter.Eventually.of_forall
    intro j
    have hpoint (y : V) : u (ι y) ≤ uSeq j (ι y) :=
      (happ.term_antitone (ι y)).le_of_tendsto (happ.term_tendsto (ι y)) j
    exact sourcePOrder_of_moreSingularOn omegaV γ.form γ.form hRγ (hvγ j)
      (MoreSingularOn.of_le fun y _ => hpoint y)
  let := singularityPseudoMetricSpace omegaV γ.form (isBigClass_kahler γ)
  let : TopologicalSpace (ThetaPshL1 γ.form.val) :=
    (singularityPseudoMetricSpace omegaV γ.form
      (isBigClass_kahler γ)).toUniformSpace.toTopologicalSpace
  exact SingularNativeGlobalPOrderClosed.sourcePOrder_of_native_limits
    omegaV γ.form (isBigClass_kahler γ) atTop (fun _ => R) A R T
      tendsto_const_nhds hlimγ horder

end

end SGPT.Foundations.Analysis.Pending.OrdinaryRestrictionGlobalTraceOrder
