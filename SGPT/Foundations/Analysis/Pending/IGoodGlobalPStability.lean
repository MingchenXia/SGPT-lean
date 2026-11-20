import SGPT.Foundations.Analysis.Pending.IGoodBasic
import SGPT.Foundations.Analysis.Pending.SingularGlobalPMixedMassEquality
import SGPT.Foundations.Analysis.Pending.GlobalPMultiplierOrder
import SGPT.Foundations.Analysis.Pending.SingularCanonicalDistanceZeroPEquivalence

set_option autoImplicit false

/-! # I-goodness is stable under actual global P-equivalence and native zero distance -/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.IGoodGlobalPStability

open FirstPass FirstPass.PositiveClasses FirstPass.POrder FirstPass.IEnvelope
  FirstPass.NonKahlerLocus
  DiagonalMass SingularGlobalPOrder SingularGlobalPMixedMassEquality
  SingularCanonicalSingularityDistance ThetaPshL1Topology

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- The other reader's original-background positive mass, ordinary-envelope
equality and I-envelope equality are produced from the actual source relation. -/
theorem iGoodWith_of_sourcePEquivalent (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {φ ψ : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hψ : IsThetaPshPotential θ.val ψ)
    (hI : IGoodWith θ φ hφ) (hPEq : SourcePEquivalent (n := n) φ ψ) :
    IGoodWith θ ψ hψ := by
  have hmass : diagonalPotentialMass θ φ hφ = diagonalPotentialMass θ ψ hψ :=
    globalMixedMass_eq_of_sourcePEquivalent omega (fun _ : Fin n => hφ)
      (fun _ : Fin n => hψ) (fun _ : Fin n => hPEq)
  have hpos : HasPositivePotentialMass θ ψ hψ := hI.positiveMass.trans_eq hmass
  have hfixed := (sourcePEquivalent_iff_pEquivalentWith omega θ hφ hψ
    hI.positiveMass hpos).mp hPEq
  have hP := pEquivalentWith_iff_envelope_eq.mp hfixed
  have hIE : iSingularityEnvelope θ.val φ = iSingularityEnvelope θ.val ψ :=
    iSingularityEnvelope_eq_of_iEquivalent
      (GlobalPMultiplierOrder.iEquivalentOnManifold_of_sourcePEquivalent hPEq)
  exact ⟨hpos, hP.symm.trans (hI.envelope_eq.trans hIE)⟩

/-- The actual finite radial value and native-agreement theorem turn a
genuine native zero distance into source equivalence before transporting I-goodness. -/
theorem iGoodWith_of_native_dist_eq_zero (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (u v : ThetaPshL1 θ.val) (hI : IGoodWith θ u.val u.property) :
    letI := singularityPseudoMetricSpace omega θ hbig
    dist u v = 0 → IGoodWith θ v.val v.property := by
  let := singularityPseudoMetricSpace omega θ hbig
  intro hd
  rw [dist_eq_singularityDistance_toReal] at hd
  obtain ⟨m, _, _, _, hD⟩ := exists_tendsto_singularityDistance omega θ hbig
    u.property v.property
  have hm : m = 0 := by simpa only [hD, EReal.toReal_coe] using hd
  have hzero : singularityDistance omega θ hbig u.val v.val = 0 := by
    simpa only [hm, EReal.coe_zero] using hD
  exact iGoodWith_of_sourcePEquivalent omega u.property v.property hI
    ((SingularCanonicalDistanceZeroPEquivalence.singularityDistance_eq_zero_iff_sourcePEquivalent
      omega θ hbig u.property v.property).mp hzero)

end

end SGPT.Foundations.Analysis.Pending.IGoodGlobalPStability
