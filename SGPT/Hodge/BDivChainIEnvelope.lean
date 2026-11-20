import SGPT.BDivisor.BlowupModel2Linear
import SGPT.Foundations.Analysis.Pending.IEnvelopeAnalytic

/-! # A potential and its I-envelope give the same b-divisor

This source-facing producer manufactures the I-envelope and its regularity
from the given actual theta-PSH potential. It is used in the proof of
`thm:bigandnefreal` and does not assume equality of b-divisors. -/

set_option autoImplicit false
noncomputable section
universe u

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Hodge.BDivChain

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.IEnvelope
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [CompactSpace X] [ConnectedSpace X]

/-- A current defined by a theta-PSH potential and the current defined by its
I-envelope have the same b-divisor on every actual model system. -/
theorem currentBDivisorOn_iEnvelope (S : ModelSystem (m + 1) X)
    (θ : ClosedRealOneOneForm (m + 1) X) (φ : X → EReal)
    (hφ : IsThetaPshPotential θ.val φ) :
    let hI := iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      hφ.1.hasSmoothLocalPotentials φ hφ
    currentBDivisorOn S (thetaPotentialCurrent θ.val (iSingularityEnvelope θ.val φ) hI)
      (SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hI) =
    currentBDivisorOn S (thetaPotentialCurrent θ.val φ hφ)
      (SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hφ) := by
  dsimp only
  let hI := iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
    hφ.1.hasSmoothLocalPotentials φ hφ
  have hTI := SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hI
  have hT := SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hφ
  have hequiv := iEquivalent_iSingularityEnvelope θ.val θ.property.1 θ.property.2
    hφ.1.hasSmoothLocalPotentials φ hφ
  have hclass : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
      ⟨thetaPotentialCurrent θ.val (iSingularityEnvelope θ.val φ) hI, hTI.1, hTI.2.1⟩ =
      bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
      ⟨thetaPotentialCurrent θ.val φ hφ, hT.1, hT.2.1⟩ := by
    exact (ThetaPotentialCurrentBottChernClass.bottChernClass_thetaClosedCurrent θ _ hI).trans
      (ThetaPotentialCurrentBottChernClass.bottChernClass_thetaClosedCurrent θ _ hφ).symm
  exact currentBDivisorOn_eq_of_iEquivalent S hTI hT hclass
    ⟨θ, θ, _, φ, hI, hφ, rfl, rfl, hequiv.2⟩
    ⟨θ, θ, φ, _, hφ, hI, rfl, rfl, hequiv.1⟩

end SGPT.Hodge.BDivChain

#print axioms SGPT.Hodge.BDivChain.currentBDivisorOn_iEnvelope
