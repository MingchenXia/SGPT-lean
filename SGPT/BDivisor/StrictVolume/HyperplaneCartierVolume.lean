import SGPT.Hodge.SourceSemipositivePullbackVolume
import SGPT.BDivisor.VolumeBDivisor
import SGPT.BDivisor.PseudoeffectivePushforward
import SGPT.Projective.FubiniStudyNormalization
import SGPT.Hodge.SourceNefClassVolume

/-! The literal original hyperplane endpoint of ex:volbdivnetstrict:
an actual Cartier b-divisor on original CP2 with actual ALL-model volume one. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.BDivisor.BaseHyperplaneNext
open Set
open SGPT.Projective SGPT.Projective.FsNormalizationNext
open SGPT.PSH.VariableComplexAtlas
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.NefMixedMass
open scoped Topology Manifold ContDiff ENNReal

/-- The literal original CP2 FS class volume, with no incoming mass or
normalization certificate. The normalization is the actual triangle proof. -/
theorem originalCP2_fs_sourceClassVolume_eq_one :
    sourceClassVolume (RealBottChern.ofRepresentative
      (ComplexProjectiveSpace.fsClosedForm (N := 2))) = 1 := by
  apply (ENNReal.toReal_eq_one_iff _).mp
  rw [sourceClassVolume_semipositive_eq_slotIntegral
    (ComplexProjectiveSpace.fsBackground (N := 2))
    (ComplexProjectiveSpace.fsClosedForm (N := 2))
    (ComplexProjectiveSpace.fsBackground (N := 2)).isSemipositive]
  have h := originalCP2_fs_classSlotIntegral_eq_one
  rw [classSlotIntegral_ofRepresentative] at h
  exact h

/-- The genuine Cartier b-divisor realized on the ACTUAL original CP2 root
by the ACTUAL original Fubini--Study hyperplane class. -/
def originalHyperplaneCartierBDivisor :
    WeilBDivisor 2 (ComplexProjectiveSpace 2) (by decide) :=
  WeilBDivisor.cartierOf (by decide) Modification.root
    (RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := 2)))

theorem originalHyperplaneCartierBDivisor_isRealization :
    originalHyperplaneCartierBDivisor.IsRealization Modification.root
      (RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := 2))) :=
  WeilBDivisor.isRealization_cartierOf Modification.root _

theorem originalHyperplaneCartierBDivisor_isNefCartier :
    originalHyperplaneCartierBDivisor.IsNefCartier :=
  WeilBDivisor.isNefCartier_cartierOf_kahler (ComplexProjectiveSpace.fsBackground (N := 2))

theorem originalHyperplaneCartierBDivisor_isPseudoeffective :
    originalHyperplaneCartierBDivisor.IsPseudoeffective := by
  apply (WeilBDivisor.isPseudoeffective_cartierOf_iff Modification.root _).mpr
  exact ⟨fun _ => (0 : EReal), (LocalPotentials.isThetaPshPotential_zero_iff _).mpr
    (ComplexProjectiveSpace.fsBackground (N := 2)).isSemipositive⟩

/-- Exact original class readback on EVERY analytic model. -/
theorem originalHyperplaneCartierBDivisor_onModel
    (ρ : Modification 2 (ComplexProjectiveSpace 2)) :
    originalHyperplaneCartierBDivisor.onModel ρ = classPullback ρ.contMDiff_map
      (RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := 2))) := by
  rw [originalHyperplaneCartierBDivisor_isRealization ρ (Modification.root_le ρ),
    Modification.classPullbackOfLE_root]

/-- Every original-model trace has actual volume one; no Kähler-background
hypothesis on the arbitrary model is supplied or manufactured falsely. -/
theorem originalHyperplaneCartierBDivisor_classVolume_eq_one
    (ρ : Modification 2 (ComplexProjectiveSpace 2)) :
    Modification.classVolume ρ (originalHyperplaneCartierBDivisor.onModel ρ) = 1 := by
  let : MeasurableSpace ρ.carrier := borel ρ.carrier
  have : BorelSpace ρ.carrier := ⟨rfl⟩
  rw [originalHyperplaneCartierBDivisor_onModel]
  change sourceClassVolume (classPullback ρ.contMDiff_map
    (RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := 2)))) = 1
  calc
    _ = sourceClassVolume (RealBottChern.ofRepresentative
        (ComplexProjectiveSpace.fsClosedForm (N := 2))) :=
      sourceClassVolume_semipositive_pullback_all_models
        (ComplexProjectiveSpace.fsBackground (N := 2))
        (ComplexProjectiveSpace.fsClosedForm (N := 2))
        (ComplexProjectiveSpace.fsBackground (N := 2)).isSemipositive ρ.isAnalyticModification
    _ = 1 := originalCP2_fs_sourceClassVolume_eq_one

/-- The ACTUAL canonical b-divisor volume is one. The infimum is over ALL
analytic modifications, rather than a restriction to blowup models. -/
theorem originalHyperplaneCartierBDivisor_volume_eq_one :
    originalHyperplaneCartierBDivisor.vol = 1 := by
  rw [WeilBDivisor.vol_of_isPseudoeffective originalHyperplaneCartierBDivisor_isPseudoeffective]
  apply le_antisymm
  · exact (iInf_le _ Modification.root).trans_eq
      (originalHyperplaneCartierBDivisor_classVolume_eq_one Modification.root)
  · exact le_iInf fun ρ => (originalHyperplaneCartierBDivisor_classVolume_eq_one ρ).ge

/-- Full hyperplane endpoint of the original strict-volume example, with
original geometry and every positivity/volume output produced internally. -/
theorem originalHyperplaneCartierBDivisor_endpoint :
    originalHyperplaneCartierBDivisor.IsRealization Modification.root
      (RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := 2))) ∧
      originalHyperplaneCartierBDivisor.IsNefCartier ∧
      originalHyperplaneCartierBDivisor.IsPseudoeffective ∧
      originalHyperplaneCartierBDivisor.vol = 1 :=
  ⟨originalHyperplaneCartierBDivisor_isRealization,
    originalHyperplaneCartierBDivisor_isNefCartier,
    originalHyperplaneCartierBDivisor_isPseudoeffective,
    originalHyperplaneCartierBDivisor_volume_eq_one⟩

end SGPT.BDivisor.BaseHyperplaneNext
