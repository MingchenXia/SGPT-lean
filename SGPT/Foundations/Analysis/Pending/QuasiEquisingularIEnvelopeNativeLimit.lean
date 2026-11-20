import SGPT.Foundations.Analysis.Pending.AnalyticAntitoneBigIGoodLimit
import SGPT.Foundations.Analysis.Pending.DominationTailOrder
import SGPT.Foundations.Analysis.Pending.GlobalPMultiplierOrder

set_option autoImplicit false

/-! # Full original-background QEA limits are the actual I-envelope -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.QuasiEquisingularIEnvelopeNativeLimit

open FirstPass FirstPass.PositiveClasses FirstPass.IEnvelope
  FirstPass.QuasiEquisingularApproximation FirstPass.NonKahlerLocus
  DiagonalMass RelativeEnergy ThetaPshL1Topology SingularGlobalPOrder
  SingularCanonicalSingularityDistance

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- The original positive mass and every field of the actual QEA produce
the true I-envelope identification, I-goodness and native convergence. -/
theorem iInf_envelopes_eq_iEnvelope_and_native_limit
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u : M → EReal} {ε : ℕ → ℝ} {U : ℕ → M → EReal}
    (happ : IsQuasiEquisingularApproximation omega θ u ε U)
    (hU : ∀ j, IsThetaPshPotential θ.val (U j))
    (hpos : HasPositivePotentialMass θ u happ.target) :
    (⨅ j, singularityEnvelope θ.val (U j)) = iSingularityEnvelope θ.val u ∧
    ∃ hI : IsThetaPshPotential θ.val (iSingularityEnvelope θ.val u),
      IGoodWith θ (iSingularityEnvelope θ.val u) hI ∧
      Tendsto (fun j => (⟨U j, hU j⟩ : ThetaPshL1 θ.val))
        atTop (@nhds (ThetaPshL1 θ.val)
          (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
          ⟨iSingularityEnvelope θ.val u, hI⟩) := by
  have hle (j : ℕ) (x : M) : u x ≤ U j x :=
    (happ.term_antitone x).le_of_tendsto (happ.term_tendsto x) j
  have hmass (j : ℕ) : diagonalPotentialMass θ u happ.target ≤
      diagonalPotentialMass θ (U j) (hU j) :=
    diagonalPotentialMass_mono_of_kahler omega happ.target (hU j)
      (MoreSingularOn.of_le fun x _ => hle j x)
  have hfinite : diagonalPotentialMass θ u happ.target < ⊤ :=
    MixedMass.globalMixedMass_lt_top omega (fun _ : Fin n => happ.target.1)
  let δ : ℝ := (diagonalPotentialMass θ u happ.target).toReal
  have hδ : 0 < δ := ENNReal.toReal_pos (ne_of_gt hpos) hfinite.ne
  have hbound (j : ℕ) : ENNReal.ofReal δ ≤
      diagonalPotentialMass θ (U j) (hU j) := by
    rw [ENNReal.ofReal_toReal hfinite.ne]
    exact hmass j
  have hanti : Antitone U := fun i j hij x => happ.term_antitone x hij
  obtain ⟨hT, hTI, hlim⟩ :=
    AnalyticAntitoneBigIGoodLimit.exists_iGood_native_model_limit_of_analytic_antitone_uniform_mass
      omega θ hbig hU happ.term_hasAnalyticSingularityType hanti hδ hbound
  let T : M → EReal := ⨅ j, singularityEnvelope θ.val (U j)
  have hP : IsThetaPshPotential θ.val (singularityEnvelope θ.val u) :=
    singularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      happ.target.1.hasSmoothLocalPotentials u happ.target
  have hPT : singularityEnvelope θ.val u ≤ T := by
    apply le_iInf
    intro j
    exact singularityEnvelope_mono (MoreSingularOn.of_le fun x _ => hle j x)
  have huT : SourcePOrder (n := n) u T :=
    (SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope
      omega θ happ.target).1.trans omega
      (sourcePOrder_of_moreSingularOn omega θ θ hP hT.plurisubharmonic
        (MoreSingularOn.of_le fun x _ => hPT x))
  have hIuT : IOrderOnManifold (n := n) u T :=
    GlobalPMultiplierOrder.iOrderOnManifold_of_sourcePOrder huT
  have hITstage (j : ℕ) : IOrderOnManifold (n := n) T (U j) := by
    have hPj := singularityEnvelope_isThetaPshPotential θ.val θ.property.1
      θ.property.2 (hU j).1.hasSmoothLocalPotentials (U j) (hU j)
    have hTPj : SourcePOrder (n := n) T (singularityEnvelope θ.val (U j)) :=
      sourcePOrder_of_moreSingularOn omega θ θ hT.plurisubharmonic hPj
        (MoreSingularOn.of_le fun x _ => (iInf_le (fun i =>
          singularityEnvelope θ.val (U i)) j) x)
    exact GlobalPMultiplierOrder.iOrderOnManifold_of_sourcePOrder
      (hTPj.trans omega (SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope
        omega θ (hU j)).2)
  have hITu : IOrderOnManifold (n := n) T u :=
    DominationTailOrder.iOrderOnManifold_of_forall_iOrderOnManifold_of_eventually
      hT.plurisubharmonic.1.quasiPlurisubharmonic hITstage
      (fun _ _ hc hcd => happ.eventually_multiplierIdealIncluded hc hcd)
  have heq : T = iSingularityEnvelope θ.val u :=
    (hT.envelope_eq.trans hTI.envelope_eq).trans
      (iSingularityEnvelope_eq_of_iEquivalent ⟨hIuT, hITu⟩).symm
  change (⨅ j, singularityEnvelope θ.val (U j)) = iSingularityEnvelope θ.val u at heq
  refine ⟨heq, ?_⟩
  have hI : IsThetaPshPotential θ.val (iSingularityEnvelope θ.val u) :=
    heq ▸ hT.plurisubharmonic
  refine ⟨hI, ?_, ?_⟩
  · simpa only [heq] using hTI
  · simpa only [heq] using hlim

end

end SGPT.Foundations.Analysis.Pending.QuasiEquisingularIEnvelopeNativeLimit
