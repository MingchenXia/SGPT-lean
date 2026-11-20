import SGPT.Foundations.Analysis.Pending.QuasiEquisingularIEnvelopeNativeLimit
import SGPT.Foundations.Analysis.Pending.IGoodGlobalPStability

set_option autoImplicit false

/-! # The actual full-QEA native criterion for original-background I-goodness -/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.FullQEANativeIGoodCriterion

open FirstPass FirstPass.PositiveClasses FirstPass.IEnvelope
  FirstPass.QuasiEquisingularApproximation FirstPass.NonKahlerLocus
  DiagonalMass ThetaPshL1Topology SingularCanonicalSingularityDistance

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Every actual full QEA in its original background has the original
potential as native limit exactly when that potential is I-good there. -/
theorem native_qea_tendsto_target_iff_iGoodWith
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u : M → EReal} {ε : ℕ → ℝ} {U : ℕ → M → EReal}
    (happ : IsQuasiEquisingularApproximation omega θ u ε U)
    (hU : ∀ j, IsThetaPshPotential θ.val (U j))
    (hpos : HasPositivePotentialMass θ u happ.target) :
    Tendsto (fun j => (⟨U j, hU j⟩ : ThetaPshL1 θ.val)) atTop
      (@nhds (ThetaPshL1 θ.val)
        (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
        ⟨u, happ.target⟩) ↔ IGoodWith θ u happ.target := by
  obtain ⟨_, hI, hIG, hlim⟩ :=
    QuasiEquisingularIEnvelopeNativeLimit.iInf_envelopes_eq_iEnvelope_and_native_limit
      omega θ hbig happ hU hpos
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  let x : ℕ → ThetaPshL1 θ.val := fun j => ⟨U j, hU j⟩
  let a : ThetaPshL1 θ.val := ⟨u, happ.target⟩
  let b : ThetaPshL1 θ.val := ⟨iSingularityEnvelope θ.val u, hI⟩
  have hb : Tendsto x atTop (𝓝 b) := hlim
  change Tendsto x atTop (𝓝 a) ↔ IGoodWith θ u happ.target
  constructor
  · intro ha
    exact IGoodGlobalPStability.iGoodWith_of_native_dist_eq_zero omega θ hbig b a hIG
      (tendsto_nhds_unique_dist hb ha)
  · intro hgood
    have hPEq : SingularGlobalPOrder.SourcePEquivalent (n := n) u
        (iSingularityEnvelope θ.val u) := by
      rw [← hgood.envelope_eq]
      exact SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope
        omega θ happ.target
    have hzero : dist a b = 0 := by
      rw [dist_eq_singularityDistance_toReal]
      have hd :=
        (SingularCanonicalDistanceZeroPEquivalence.singularityDistance_eq_zero_iff_sourcePEquivalent
          omega θ hbig happ.target hI).mpr hPEq
      change (singularityDistance omega θ hbig u (iSingularityEnvelope θ.val u)).toReal = 0
      rw [hd, EReal.toReal_zero]
    have hdist (j : ℕ) : dist (x j) a = dist (x j) b := by
      apply le_antisymm
      · have hh := dist_triangle (x j) b a
        rw [dist_comm b a, hzero, add_zero] at hh
        exact hh
      · simpa only [hzero, add_zero] using dist_triangle (x j) a b
    rw [tendsto_iff_dist_tendsto_zero] at hb ⊢
    simpa only [hdist] using hb

end

end SGPT.Foundations.Analysis.Pending.FullQEANativeIGoodCriterion
