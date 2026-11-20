import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityOrderedMassCriterion
import SGPT.Foundations.Analysis.Pending.SingularGlobalPMaximum
import SGPT.Foundations.Analysis.Pending.SingularGlobalPMixedMassEquality

set_option autoImplicit false

/-! # Actual source P-ordered mass and singularity convergence

SGPT PDF0216--0217 mass monotonicity and PDF0226--0227 Corollary 6.2.6
convergence equivalences. Actual maximum source equivalence and independent
mixed mass preservation give original mass monotonicity, even at zero mass.
Positive target mass then internally supplies right positivity and the
fixed-background comparison. Genuine envelope mass preservation transports
the one scalar limit to actual pointwise-ordered endpoint limits, without
idempotence. Native topology is explicitly the actual distance-generated
topology. The infimum identity, varying backgrounds, and completeness are
separate, and no incoming monotonicity is required.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularGlobalPOrderedConvergence

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.POrder
  DiagonalMass MixedMass RelativeEnergy SingularGlobalPOrder SingularGlobalPMaximum
  SingularGlobalPMixedMassEquality SingularPEnvelopeMixedMassPreservation
  SingularCanonicalSingularityOrderedMassCriterion SingularMinimalCanonicalRay
  SingularCanonicalSingularityDistance SingularCanonicalSingularityMassComparison
  ThetaPshL1Topology

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Actual source maximum equivalence internally gives original top-mass
monotonicity, including zero original masses. -/
theorem diagonalPotentialMass_mono_of_sourcePOrder
    (omega : KahlerBackground n M) {θ : ClosedRealOneOneForm n M}
    {u v : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (huv : SourcePOrder (n := n) u v) :
    diagonalPotentialMass θ u hu ≤ diagonalPotentialMass θ v hv := by
  have hw := IsThetaPshPotential.max hu hv
  have hpeq := (sourcePOrder_iff_sourcePEquivalent_max omega hu hv).mp huv
  have hmass : diagonalPotentialMass θ (fun x => max (u x) (v x)) hw =
      diagonalPotentialMass θ v hv :=
    globalMixedMass_eq_of_sourcePEquivalent omega (fun _ : Fin n => hw)
      (fun _ : Fin n => hv) (fun _ => hpeq)
  exact (diagonalPotentialMass_mono_of_kahler omega hu hw
    (MoreSingularOn.of_le fun x _ => le_max_left _ _)).trans_eq hmass

/-- Positive left mass internally produces positive right mass before
transporting the source comparison to the actual original background. -/
theorem pOrderWith_of_sourcePOrder_of_positive_left_mass
    (omega : KahlerBackground n M) {θ : ClosedRealOneOneForm n M}
    {u v : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (hupos : 0 < diagonalPotentialMass θ u hu)
    (huv : SourcePOrder (n := n) u v) : POrderWith θ u v := by
  have hvpos : HasPositivePotentialMass θ v hv := hupos.trans_le
    (diagonalPotentialMass_mono_of_sourcePOrder omega hu hv huv)
  exact (sourcePOrder_iff_pOrderWith omega θ hu hv hupos hvpos).mp huv

private theorem endpointMixedMass_eq_of_sourcePEquivalent
    (omega : KahlerBackground n M) {θ : ClosedRealOneOneForm n M}
    {u v p : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (hp : IsThetaPshPotential θ.val p)
    (huv : SourcePEquivalent (n := n) u v) (j : Fin (n + 1)) :
    endpointMixedMass θ p u hp hu j = endpointMixedMass θ p v hp hv j := by
  have hup : ∀ i, IsThetaPshPotential θ.val (endpointMixedPotential j u p i) := by
    intro i
    dsimp only [endpointMixedPotential]
    split_ifs <;> first | exact hu | exact hp
  have hvp : ∀ i, IsThetaPshPotential θ.val (endpointMixedPotential j v p i) := by
    intro i
    dsimp only [endpointMixedPotential]
    split_ifs <;> first | exact hv | exact hp
  have href := sourcePOrder_refl_of_isThetaPshPotential omega hp
  have hrel : ∀ i, SourcePEquivalent (n := n)
      (endpointMixedPotential j u p i) (endpointMixedPotential j v p i) := by
    intro i
    dsimp only [endpointMixedPotential]
    split_ifs <;> first | exact huv | exact ⟨href, href⟩
  exact globalMixedMass_eq_of_sourcePEquivalent omega hup hvp hrel

private theorem endpointMixedMass_envelopes_eq
    (omega : KahlerBackground n M) {θ : ClosedRealOneOneForm n M}
    {u p : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hp : IsThetaPshPotential θ.val p)
    (hPu : IsThetaPshPotential θ.val (singularityEnvelope θ.val u))
    (hPp : IsThetaPshPotential θ.val (singularityEnvelope θ.val p)) (j : Fin (n + 1)) :
    endpointMixedMass θ (singularityEnvelope θ.val p) (singularityEnvelope θ.val u)
      hPp hPu j = endpointMixedMass θ p u hp hu j := by
  have ht : ∀ i, IsThetaPshPotential θ.val (endpointMixedPotential j u p i) := by
    intro i
    dsimp only [endpointMixedPotential]
    split_ifs <;> first | exact hu | exact hp
  have hPt : ∀ i, IsThetaPshPotential θ.val
      (singularityEnvelope θ.val (endpointMixedPotential j u p i)) := fun i =>
    singularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      (ht i).1.hasSmoothLocalPotentials _ (ht i)
  have heq : (fun i => singularityEnvelope θ.val (endpointMixedPotential j u p i)) =
      endpointMixedPotential j (singularityEnvelope θ.val u) (singularityEnvelope θ.val p) := by
    funext i
    dsimp only [endpointMixedPotential]
    split_ifs <;> rfl
  have hmeasure := UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple heq
    (fun i => (hPt i).1)
    (endpointMixedPotential_thetaPlurisubharmonic θ j
      (singularityEnvelope θ.val u) (singularityEnvelope θ.val p) hPu hPp)
  exact (congrArg (fun μ : Measure M => μ univ) hmeasure).symm.trans
    (globalMixedMass_singularityEnvelope_eq omega ht)

/-- The positive source target produces actual fixed-envelope order and
genuine preserved scalar masses, hence every original endpoint mass limit. -/
theorem tendsto_endpointMixedMass_of_sourcePOrder_of_positive_target_of_diagonal_tendsto
    (omega : KahlerBackground n M) {θ : ClosedRealOneOneForm n M}
    {I : Type*} (F : Filter I) {u : I → M → EReal} {v p : M → EReal}
    (hu : ∀ i, IsThetaPshPotential θ.val (u i)) (hv : IsThetaPshPotential θ.val v)
    (hp : IsThetaPshPotential θ.val p) (horder : ∀ i, SourcePOrder (n := n) v (u i))
    (hvpos : 0 < diagonalPotentialMass θ v hv) (hppos : 0 < diagonalPotentialMass θ p hp)
    (hdiag : Tendsto (fun i => diagonalPotentialMass θ (u i) (hu i)) F
      (𝓝 (diagonalPotentialMass θ v hv))) (j : Fin (n + 1)) :
    Tendsto (fun i => endpointMixedMass θ p (u i) hp (hu i) j) F
      (𝓝 (endpointMixedMass θ p v hp hv j)) := by
  let Pu : I → M → EReal := fun i => singularityEnvelope θ.val (u i)
  let Pv := singularityEnvelope θ.val v
  let Pp := singularityEnvelope θ.val p
  have hPu : ∀ i, IsThetaPshPotential θ.val (Pu i) := fun i =>
    singularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      (hu i).1.hasSmoothLocalPotentials _ (hu i)
  have hPv : IsThetaPshPotential θ.val Pv :=
    singularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      hv.1.hasSmoothLocalPotentials _ hv
  have hPp : IsThetaPshPotential θ.val Pp :=
    singularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      hp.1.hasSmoothLocalPotentials _ hp
  have hle : ∀ i, Pv ≤ Pu i := fun i =>
    pOrderWith_of_sourcePOrder_of_positive_left_mass omega hv (hu i) hvpos (horder i)
  have hmu (i : I) : diagonalPotentialMass θ (Pu i) (hPu i) =
      diagonalPotentialMass θ (u i) (hu i) :=
    singularityEnvelopeMassPreserving omega θ (u i) (hu i) (hPu i)
  have hmv : diagonalPotentialMass θ Pv hPv = diagonalPotentialMass θ v hv :=
    singularityEnvelopeMassPreserving omega θ v hv hPv
  have hmp : diagonalPotentialMass θ Pp hPp = diagonalPotentialMass θ p hp :=
    singularityEnvelopeMassPreserving omega θ p hp hPp
  have hPdiag : Tendsto (fun i => diagonalPotentialMass θ (Pu i) (hPu i)) F
      (𝓝 (diagonalPotentialMass θ Pv hPv)) := by
    simpa only [hmu, hmv] using hdiag
  have hm := tendsto_endpointMixedMass_of_le_of_diagonal_tendsto omega F hPu hPv hPp
    hle (hmv ▸ hvpos) (hmp ▸ hppos) hPdiag j
  have hEu (i : I) : endpointMixedMass θ Pp (Pu i) hPp (hPu i) j =
      endpointMixedMass θ p (u i) hp (hu i) j :=
    endpointMixedMass_envelopes_eq omega (hu i) hp (hPu i) hPp j
  have hEv : endpointMixedMass θ Pp Pv hPp hPv j = endpointMixedMass θ p v hp hv j :=
    endpointMixedMass_envelopes_eq omega hv hp hPv hPp j
  simpa only [hEu, hEv] using hm

/-- Genuine source order identifies maximum masses with the original
stage masses, giving the native endpoint criterion even at zero target mass. -/
theorem tendsto_native_iff_endpointMixedMass_of_sourcePOrder
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} (F : Filter I) (w : I → ThetaPshL1 θ.val) (v : ThetaPshL1 θ.val)
    (horder : ∀ i, SourcePOrder (n := n) v.val (w i).val) :
    letI := singularityPseudoMetricSpace omega θ hbig
    letI : TopologicalSpace (ThetaPshL1 θ.val) :=
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
    Tendsto w F (𝓝 v) ↔ ∀ j : Fin (n + 1),
      Tendsto (fun i => endpointMixedMass θ (thetaPshSupremum θ.val) (w i).val
        (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic (w i).property j)
        F (𝓝 (endpointMixedMass θ (thetaPshSupremum θ.val) v.val
          (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic v.property j)) := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  have hmass (i : I) (j : Fin (n + 1)) : endpointMixedMass θ (thetaPshSupremum θ.val)
      (fun x => max ((w i).val x) (v.val x))
      (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
      (IsThetaPshPotential.max (w i).property v.property) j =
      endpointMixedMass θ (thetaPshSupremum θ.val) (w i).val
        (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic (w i).property j := by
    have hpeq : SourcePEquivalent (n := n)
        (fun x => max ((w i).val x) (v.val x)) (w i).val := by
      simpa only [max_comm] using
        (sourcePOrder_iff_sourcePEquivalent_max omega v.property (w i).property).mp (horder i)
    exact endpointMixedMass_eq_of_sourcePEquivalent omega
      (IsThetaPshPotential.max (w i).property v.property) (w i).property
      (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic hpeq j
  rw [tendsto_native_iff_endpointMixedMass omega θ hbig F w v]
  simp only [hmass, and_self]

/-- The actual source order and positive target produce all fixed-envelope
scalar-to-endpoint data internally; one top-mass limit characterizes native convergence. -/
theorem tendsto_native_iff_diagonalPotentialMass_of_sourcePOrder_of_positive_target
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} (F : Filter I) (w : I → ThetaPshL1 θ.val) (v : ThetaPshL1 θ.val)
    (horder : ∀ i, SourcePOrder (n := n) v.val (w i).val)
    (hvpos : 0 < diagonalPotentialMass θ v.val v.property) :
    letI := singularityPseudoMetricSpace omega θ hbig
    letI : TopologicalSpace (ThetaPshL1 θ.val) :=
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
    Tendsto w F (𝓝 v) ↔ Tendsto (fun i => diagonalPotentialMass θ (w i).val (w i).property)
      F (𝓝 (diagonalPotentialMass θ v.val v.property)) := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  constructor
  · intro h
    have htop := ((tendsto_native_iff_endpointMixedMass omega θ hbig F w v).mp h
      (Fin.last n)).1
    have htup {a : M → EReal} : endpointMixedPotential (Fin.last n) a
        (thetaPshSupremum θ.val) = (fun _ : Fin n => a) := by
      funext i
      simp only [endpointMixedPotential, Fin.val_last, if_pos i.isLt]
    have heq {a : M → EReal} (ha : IsThetaPshPotential θ.val a) :
        endpointMixedMass θ (thetaPshSupremum θ.val) a
          (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic ha (Fin.last n) =
          diagonalPotentialMass θ a ha :=
      congrArg (fun μ : Measure M => μ univ)
        (UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple htup
          (endpointMixedPotential_thetaPlurisubharmonic θ (Fin.last n) a
            (thetaPshSupremum θ.val) ha
            (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic)
          (fun _ : Fin n => ha.1))
    simpa only [heq] using htop
  · intro hdiag
    apply (tendsto_native_iff_endpointMixedMass_of_sourcePOrder omega θ hbig F w v horder).mpr
    intro j
    exact tendsto_endpointMixedMass_of_sourcePOrder_of_positive_target_of_diagonal_tendsto
      omega F (fun i => (w i).property) v.property
      (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic horder hvpos
      (isModelPotential_thetaPshSupremum omega θ hbig).positive_mass hdiag j

end

end SGPT.Foundations.Analysis.Pending.SingularGlobalPOrderedConvergence
