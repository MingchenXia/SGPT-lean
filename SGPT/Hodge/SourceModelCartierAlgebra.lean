import SGPT.Hodge.SourceModelCartierUpper
import SGPT.Hodge.SourceNefCartierOrder
import SGPT.Hodge.SourceCartierSequence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
  SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft SGPT.Hodge.BDivChain.SourceIntersection

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X] [CompactSpace X]
local notation "Sys" => ModelSystem.blowup (m+1) X

/-- The actual model-Cartier construction is a real linear map. -/
def modelCartierLinear (π : (ModelSystem.blowup (m+1) X).Model) : RealBottChern (m+1) π.1.carrier →ₗ[ℝ] WeilFamilyAny Sys where
  toFun := modelCartier π
  map_add' α β := by
    unfold modelCartier
    rw [WeilBDivisorOn.cartierOf_add]
    apply Subtype.ext
    rfl
  map_smul' c α := by
    unfold modelCartier
    rw [WeilBDivisorOn.cartierOf_smul]
    apply Subtype.ext
    rfl

theorem modelCartier_self (π : (ModelSystem.blowup (m+1) X).Model) (α : RealBottChern (m+1) π.1.carrier) :
    (modelCartier π α).val π=α := by
  change (WeilBDivisorOn.cartierOf (Nat.succ_pos m) π α).onModel π=α
  rw [WeilBDivisorOn.isRealization_cartierOf π α π (le_refl π)]
  exact Modification.classPullbackOfLE_refl π.1 α

theorem modelCartier_eq_of_realization {D : WeilFamilyAny Sys} {π : (ModelSystem.blowup (m+1) X).Model}
    {α : RealBottChern (m+1) π.1.carrier} (hr : IsRealizationAny D π α) :
    D=modelCartier π α := by
  apply family_eq_of_toExisting_eq (Nat.succ_pos m)
  change toExisting Sys (Nat.succ_pos m) D=toExisting Sys (Nat.succ_pos m)
    (fromExisting Sys (Nat.succ_pos m) (WeilBDivisorOn.cartierOf (Nat.succ_pos m) π α))
  rw [toExisting_fromExisting]
  exact ((isRealizationAny_iff_existing (Nat.succ_pos m) D π α).mp hr).eq_cartierOf

/-- A genuine positive model-class difference gives the original order on
EVERY book model; actual pullback and pushforward produce its witnesses. -/
theorem modelCartier_mono {π : (ModelSystem.blowup (m+1) X).Model} {α β : RealBottChern (m+1) π.1.carrier}
    (h : ClassPseudoeffectiveViaPotentials (β-α)) :
    LEAny (modelCartier π α) (modelCartier π β) := by
  intro δ
  obtain ⟨ρ,hπ,hδ⟩ := ModelSystem.Model.exists_le_le π δ
  have hp := classPseudoeffective_classPullback
    (Modification.Dominates.isAnalyticModification (show π.1≤ρ.1 from hπ)) h
  have hq := classPseudoeffective_classPushforward
    (Modification.contMDiff_homOfLE (show δ.1≤ρ.1 from hδ)) (Nat.succ_pos m) hp
  change ClassPseudoeffectiveViaPotentials
    (Modification.classPushforwardOfLE (Nat.succ_pos m) (show δ.1≤ρ.1 from hδ)
      (Modification.classPullbackOfLE (show π.1≤ρ.1 from hπ) (β-α))) at hq
  change ClassPseudoeffectiveViaPotentials
    ((WeilBDivisorOn.cartierOf (Nat.succ_pos m) π β).onModel δ-
      (WeilBDivisorOn.cartierOf (Nat.succ_pos m) π α).onModel δ)
  rw [WeilBDivisorOn.cartierOf_onModel β hπ hδ,
    WeilBDivisorOn.cartierOf_onModel α hπ hδ]
  simpa only [map_sub] using hq

theorem modelCartier_isNefCartier (π : (ModelSystem.blowup (m+1) X).Model)
    (κ : KahlerBackground (m+1) π.1.carrier) {α : RealBottChern (m+1) π.1.carrier}
    (hα : ClassNefWithRespectTo κ α) : IsNefCartierAny (modelCartier π α) := by
  refine ⟨π,α,?_,κ,hα⟩
  exact WeilBDivisorOn.isRealization_cartierOf π α

/-- The literal model-Cartier map preserves the original topology, without
choosing a cofinal tower or a finite set of target models. -/
theorem modelCartier_converges {I : Type*} {l : Filter I} (π : (ModelSystem.blowup (m+1) X).Model)
    {a : I → RealBottChern (m+1) π.1.carrier} {α : RealBottChern (m+1) π.1.carrier}
    (h : Tendsto a l (@nhds _ (euclideanTopology _) α)) :
    ConvergesAny l (fun i => modelCartier π (a i)) (modelCartier π α) := by
  intro δ
  rw [tendsto_euclideanTopology_iff]
  intro f
  let F : RealBottChern (m+1) π.1.carrier →ₗ[ℝ] ℝ :=
    f.comp ((LinearMap.proj δ).comp ((weilFamiliesAny Sys).subtype.comp (modelCartierLinear π)))
  exact (tendsto_euclideanTopology_iff.mp h) F

variable [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- The actual dimension-uniform current family lies below the actual
Cartier closure of each of its SAME original traces. -/
theorem currentFamily_le_modelCartier (π : (ModelSystem.blowup (m+1) X).Model)
    (T : ClosedPositive (n := m+1) (X := X)) :
    LEAny (currentBDivisorAnyOn Sys T)
      (modelCartier π ((currentBDivisorAnyOn Sys T).val π)) := by
  have htrace : (currentBDivisorAnyOn Sys T).val π=
      π.1.regPullClass (toBookCurrent T).current
        (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent T)) :=
    regPullClassAny_eq_existing π.1 T
  rw [htrace]
  apply (leAny_iff_existing (Nat.succ_pos m) _ _).mpr
  rw [currentBDivisorAnyOn_eq_existing]
  simpa only [modelCartier,toExisting_fromExisting] using
    currentBDivisor_le_modelCartier π (toBookCurrent T)

/-- Actual big-nef realizations INTERNALLY supply the current needed by the
model-Cartier upper bound. No current or upper-bound certificate is an input. -/
theorem bigNefFamily_le_modelCartier (ω : KahlerBackground (m+1) X)
    (D : BigNefFamily (n := m+1) (X := X)) (π : (ModelSystem.blowup (m+1) X).Model) :
    LEAny D.val (modelCartier π (D.val.val π)) := by
  have h := currentFamily_le_modelCartier π (realizingCurrent ω D).val
  simpa only [realizingCurrent_family] using h

end SGPT.Hodge.BDivChain.SourceMixedOrderDraft
