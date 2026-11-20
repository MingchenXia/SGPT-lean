import SGPT.Foundations.Analysis.Pending.IEnvelopeIncreasingRegularizedSupremum

set_option autoImplicit false
noncomputable section

namespace SGPT.Foundations.Analysis.Pending.DirectedIncreasingIEnvelope

open Set Filter MeasureTheory
open scoped Topology ENNReal
open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.IEnvelope
open IncreasingMixedDirectedNets IEnvelopeIncreasingRegularizedSupremum
open ActualIEnvelopeOrderInfimum

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- The actual sequence identity extends to every directed increasing net
by genuine Choquet selection and two literal regularized-supremum bounds. -/
theorem iSingularityEnvelope_directed_regularized_iSup_eq
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {v : I → M → EReal} {u : M → EReal}
    (hv : ∀ i, IsThetaPshPotential θ.val (v i)) (hmono : Monotone v)
    (hu : IsThetaPshPotential θ.val u) (hreg : uscRegularization (⨆ i, v i) = u)
    (hpos : DiagonalMass.HasPositivePotentialMass θ u hu) :
    uscRegularization (⨆ i, iSingularityEnvelope θ.val (v i)) =
      iSingularityEnvelope θ.val u := by
  classical
  obtain ⟨j, hj, _, hsup⟩ :=
    exists_monotone_sequence_uscRegularization_iSup_eq
      (K := Unit) (u := fun i _ => v i) (Classical.arbitrary I) (fun _ => hmono)
  have hseqreg : uscRegularization (⨆ k, v (j k)) = u := (hsup ()).trans hreg
  have hseq := iSingularityEnvelope_regularized_iSup_eq omega θ hbig
    (fun k => hv (j k)) (fun _ _ hkl => hmono (hj hkl)) hu hseqreg hpos
  have hvu (i : I) : v i ≤ u := by
    rw [← hreg]
    exact (le_iSup v i).trans (le_uscRegularization _)
  have hbound (i : I) : iSingularityEnvelope θ.val (v i) ≤
      iSingularityEnvelope θ.val u :=
    iSingularityEnvelope_le_of_iOrderOnManifold θ hu
      (iOrderOnManifold_of_le hu.1.quasiPlurisubharmonic (hvu i))
  have hupper : uscRegularization (⨆ i, iSingularityEnvelope θ.val (v i)) ≤
      iSingularityEnvelope θ.val u :=
    uscRegularization_le
      (iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
        hu.1.hasSmoothLocalPotentials u hu).1.quasiPlurisubharmonic.upperSemicontinuous
      (iSup_le hbound)
  apply le_antisymm hupper
  rw [← hseq]
  exact uscRegularization_mono (iSup_le fun k =>
    le_iSup (fun i => iSingularityEnvelope θ.val (v i)) (j k))

end SGPT.Foundations.Analysis.Pending.DirectedIncreasingIEnvelope
