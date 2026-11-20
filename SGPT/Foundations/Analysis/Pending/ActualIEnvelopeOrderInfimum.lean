import SGPT.Foundations.Analysis.Pending.IEnvelopeAnalytic
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshMaximumOrders

set_option autoImplicit false

/-! # Actual ideal order and genuine pointwise I-model infima -/

open Set

namespace SGPT.Foundations.Analysis.Pending.ActualIEnvelopeOrderInfimum

open FirstPass FirstPass.IEnvelope FirstPass.PositiveClasses GlobalQuasiPshMaximumOrders

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M]

/-- The actual one-way maximum theorem turns ideal order into the
literal envelope inequality, without assuming the first weight PSH. -/
theorem iSingularityEnvelope_le_of_iOrderOnManifold
    (θ : ClosedRealOneOneForm n M) {φ ψ : M → EReal}
    (hψ : IsThetaPshPotential θ.val ψ) (hI : IOrderOnManifold (n := n) φ ψ) :
    iSingularityEnvelope θ.val φ ≤ iSingularityEnvelope θ.val ψ := by
  let B := iSingularityEnvelope θ.val ψ
  have hB : IsThetaPshPotential θ.val B :=
    iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      hψ.1.hasSmoothLocalPotentials ψ hψ
  have hψB : IEquivalentOnManifold (n := n) ψ B :=
    iEquivalent_iSingularityEnvelope θ.val θ.property.1 θ.property.2
      hψ.1.hasSmoothLocalPotentials ψ hψ
  apply (iSingularityEnvelope_le_iff (upperSemicontinuous_iSingularityEnvelope θ.val ψ)).mpr
  intro a ha ha0 haI
  have haB : IOrderOnManifold (n := n) a B := haI.1.trans (hI.trans hψB.1)
  have hmI : IEquivalentOnManifold (n := n) (fun x => max (a x) (B x)) B :=
    (iOrderOnManifold_iff_iEquivalent_max ha hB).mp haB
  have hm : (fun x => max (a x) (B x)) ≤ iSingularityEnvelope θ.val B :=
    le_iSingularityEnvelope (IsThetaPshPotential.max ha hB)
      (fun x => max_le (ha0 x) (iSingularityEnvelope_le_zero θ.val ψ x)) hmI
  have hfix : iSingularityEnvelope θ.val B = B :=
    iSingularityEnvelope_idempotent θ.val θ.property.1 θ.property.2
      hψ.1.hasSmoothLocalPotentials ψ hψ
  exact (show a ≤ (fun x => max (a x) (B x)) from fun x => le_max_left _ _).trans
    (hm.trans_eq hfix)

/-- Ordinary infima remain actual I-models as soon as the genuine PSH
condition is provided by an independent infimum-regularity producer. -/
theorem isIModelPotential_iInf_of_isThetaPshPotential
    (θ : ClosedRealOneOneForm n M) {I : Type*} [Nonempty I]
    {v : I → M → EReal} (hv : ∀ i, IsIModelPotential θ.val (v i))
    (hτ : IsThetaPshPotential θ.val (⨅ i, v i)) :
    IsIModelPotential θ.val (⨅ i, v i) := by
  obtain ⟨i₀⟩ := ‹Nonempty I›
  have hv0 (i : I) : v i ≤ 0 := by
    rw [(hv i).envelope_eq]
    exact iSingularityEnvelope_le_zero θ.val (v i)
  have hτ0 : (⨅ i, v i) ≤ 0 := (iInf_le v i₀).trans (hv0 i₀)
  have hdown : iSingularityEnvelope θ.val (⨅ i, v i) ≤ ⨅ i, v i := by
    apply le_iInf
    intro i
    have hI : IOrderOnManifold (n := n) (⨅ j, v j) (v i) :=
      iOrderOnManifold_of_le (hv i).plurisubharmonic.1.quasiPlurisubharmonic (iInf_le v i)
    exact (iSingularityEnvelope_le_of_iOrderOnManifold θ (hv i).plurisubharmonic hI).trans_eq
      (hv i).envelope_eq.symm
  exact ⟨hτ, le_antisymm
    (le_iSingularityEnvelope hτ hτ0 (IEquivalentOnManifold.refl (⨅ i, v i))) hdown⟩

end

end SGPT.Foundations.Analysis.Pending.ActualIEnvelopeOrderInfimum
