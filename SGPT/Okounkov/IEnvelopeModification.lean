import SGPT.Foundations.Analysis.Pending.AnalyticModificationPotentialDescent
import SGPT.Foundations.Analysis.Pending.GenuineModificationIdealOrderInvariance
import SGPT.Foundations.Analysis.Pending.IEnvelopeAnalytic

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov

open Set
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.IEnvelope SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy AnalyticModificationStrongPullback

variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [Nonempty X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

omit [CompactSpace X] [Nonempty X] in
private theorem iEquivalent_comp_iff_of_thetaPsh
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
    {θ σ : SmoothRealForm n X 2} {u v : X → EReal}
    (hu : IsThetaPshPotential θ u) (hv : IsThetaPshPotential σ v) :
    IEquivalentOnManifold (n := n) u v ↔
      IEquivalentOnManifold (n := n) (u ∘ π) (v ∘ π) := by
  exact and_congr
    (GenuineModificationIdealOrderInvariance.iOrder_iff_comp
      hπ hu.1.quasiPlurisubharmonic hv.quasiPshPotential)
    (GenuineModificationIdealOrderInvariance.iOrder_iff_comp
      hπ hv.1.quasiPlurisubharmonic hu.quasiPshPotential)

/-- The literal original I-envelope commutes with an actual general
modification, using genuine whole-fiber potential descent. -/
theorem iSingularityEnvelope_modification_pullback
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
    (θ : ClosedRealOneOneForm n X) {u : X → EReal}
    (hu : IsThetaPshPotential θ.val u) :
    iSingularityEnvelope (ClosedRealOneOneForm.pullback hπ.1 θ).val (u ∘ π) =
      (iSingularityEnvelope θ.val u) ∘ π := by
  classical
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  let : Nonempty Y := by
    obtain ⟨x⟩ := ‹Nonempty X›
    obtain ⟨y, _⟩ := surjective_of_isAnalyticModification hπ x
    exact ⟨y⟩
  let β := ClosedRealOneOneForm.pullback hπ.1 θ
  let E := iSingularityEnvelope θ.val u
  let Eπ := iSingularityEnvelope β.val (u ∘ π)
  have hup := isThetaPshPotential_comp_of_isAnalyticModification hπ θ hu
  have hE : IsThetaPshPotential θ.val E :=
    iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      hu.1.hasSmoothLocalPotentials u hu
  have hEp : IsThetaPshPotential β.val Eπ :=
    iSingularityEnvelope_isThetaPshPotential β.val β.property.1 β.property.2
      hup.1.hasSmoothLocalPotentials (u ∘ π) hup
  have hEI : IEquivalentOnManifold (n := n) E u :=
    (iEquivalent_iSingularityEnvelope θ.val θ.property.1 θ.property.2
      hu.1.hasSmoothLocalPotentials u hu).symm
  have hEpI : IEquivalentOnManifold (n := n) Eπ (u ∘ π) :=
    (iEquivalent_iSingularityEnvelope β.val β.property.1 β.property.2
      hup.1.hasSmoothLocalPotentials (u ∘ π) hup).symm
  have hlow : E ∘ π ≤ Eπ := le_iSingularityEnvelope
    (isThetaPshPotential_comp_of_isAnalyticModification hπ θ hE)
    (fun y => iSingularityEnvelope_le_zero θ.val u (π y))
    ((iEquivalent_comp_iff_of_thetaPsh hπ hE hu).mp hEI)
  obtain ⟨v, hv, hread⟩ :=
    AnalyticModificationPotentialDescent.exists_descent_of_isAnalyticModification hπ θ hEp
  have hv0 : v ≤ 0 := by
    intro x
    obtain ⟨y, hxy⟩ := surjective_of_isAnalyticModification hπ x
    rw [← hxy, hread]
    exact iSingularityEnvelope_le_zero β.val (u ∘ π) y
  have hvI : IEquivalentOnManifold (n := n) v u := by
    apply (iEquivalent_comp_iff_of_thetaPsh hπ hv hu).mpr
    have heq : v ∘ π = Eπ := funext hread
    simpa only [heq] using hEpI
  have hupper : v ≤ E := le_iSingularityEnvelope hv hv0 hvI
  apply funext
  intro y
  exact le_antisymm ((hread y).symm.trans_le (hupper (π y))) (hlow y)

end SGPT.Okounkov
