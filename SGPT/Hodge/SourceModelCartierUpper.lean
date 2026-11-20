import SGPT.Hodge.SourceRegFamily
import SGPT.BDivisor.PseudoeffectivePushforward
import SGPT.Hodge.SourceNefIntersection

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
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft SGPT.Hodge.BDivChain.SourceIntersection

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X]
  [CompactSpace X]
local notation "Sys" => ModelSystem.blowup (m+1) X
local notation "Cur" => GlobalCurrent (m+1) X (degreeTwo (Nat.succ_pos m))

/-- The class of an ACTUAL positive current is genuinely pseudo-effective. -/
theorem classPseudoeffective_of_closedPositive {T : Cur}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) :
    ClassPseudoeffectiveViaPotentials (bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m)
      ⟨T,hT.1,hT.2.1⟩) := by
  exact (PseudoeffectiveOriginalCurrentEquivalence.classPseudoeffectiveViaPotentials_iff_exists_original_current
    _).mpr ⟨⟨T,hT.1,hT.2.1⟩,hT.2.2,rfl⟩

/-- Actual relative Siu divisorial positivity, retaining the SAME original
current and arbitrary original model domination. -/
theorem classPseudoeffective_pullback_regPullClass_sub
    {π τ : Modification (m+1) X} (h : π≤τ) (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X) :
    ClassPseudoeffectiveViaPotentials (Modification.classPullbackOfLE h
      (π.regPullClass T.current (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T))-
      τ.regPullClass T.current (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T)) := by
  let hT := SGPT.Siu.isClosedPositiveCurrent_bookCurrent T
  let hg := Modification.Dominates.isAnalyticModification h
  let ρ : Modification (m+1) π.carrier :=
    { carrier := τ.carrier
      map := Modification.homOfLE h
      isAnalyticModification := hg }
  let P := Modification4.pull π.isAnalyticModification T.current hT
  let hP := Modification4.isClosedPositiveCurrent_pull π.isAnalyticModification hT
  let B := SGPT.Siu.toBookCurrent P hP
  let R := SGPT.Siu.bookSiuRegularPart B
  let hR := SGPT.Siu.isClosedPositiveCurrent_bookCurrent R
  have hpull : Modification4.pull hg P hP=Modification4.pull τ.isAnalyticModification T.current hT := by
    symm
    rw [PrimePushforward.pull_congr (Modification.map_comp_homOfLE h).symm τ.isAnalyticModification
      (AnalyticModificationComposition.isAnalyticModification_comp π.isAnalyticModification hg)]
    exact PrimePushforward.pull_comp π.isAnalyticModification hg hT
  have hreg : ρ.regPull R.current hR=τ.regPull T.current hT := by
    calc ρ.regPull R.current hR=ρ.regPull B.current (SGPT.Siu.isClosedPositiveCurrent_bookCurrent B) :=
          SGPT.Hodge.BDivChain.SourceReg.regPull_regular_eq ρ B
      _ = τ.regPull T.current hT := by
        change SGPT.Siu.siuRegularPart (Modification4.pull hg P hP) _ =
          SGPT.Siu.siuRegularPart (Modification4.pull τ.isAnalyticModification T.current hT) _
        exact PrimePushforward.siuRegularPart_congr hpull _ _
  have hregClass : ρ.regPullClass R.current hR=τ.regPullClass T.current hT := by
    unfold Modification.regPullClass
    apply SGPT.Hodge.BDivChain.bottChernClass_congr
    exact hreg
  have he : Modification.classPullbackOfLE h (π.regPullClass T.current hT)-τ.regPullClass T.current hT=
      ρ.divPullClass R.current hR := by
    rw [←hregClass,ρ.regPullClass_eq hR]
    have hRclass : bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m)
        ⟨R.current,hR.1,hR.2.1⟩ = π.regPullClass T.current hT := rfl
    change Modification.classPullbackOfLE h (π.regPullClass T.current hT)-
      (Modification.classPullbackOfLE h
        (bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) ⟨R.current,hR.1,hR.2.1⟩)-
        ρ.divPullClass R.current hR)=_
    rw [hRclass]
    abel
  rw [he]
  exact classPseudoeffective_of_closedPositive
    (SGPT.Siu.isClosedPositiveCurrent_siuDivisorialPart
      (Modification4.isClosedPositiveCurrent_pull ρ.isAnalyticModification hR))

/-- The actual Cartier family determined by one ORIGINAL model trace. -/
def modelCartier (π : (ModelSystem.blowup (m+1) X).Model)
    (α : RealBottChern (m+1) π.1.carrier) : WeilFamilyAny Sys :=
  fromExisting Sys (Nat.succ_pos m) (WeilBDivisorOn.cartierOf (Nat.succ_pos m) π α)

/-- EVERY actual current family lies below the actual Cartier closure of
ANY of its original model traces. The common model and positive class are
internally produced; no output upper-bound certificate is an input. -/
theorem currentBDivisor_le_modelCartier
    (π : (ModelSystem.blowup (m+1) X).Model)
    (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X) :
    (currentBDivisorOn Sys T.current (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T)).LE
      (WeilBDivisorOn.cartierOf (Nat.succ_pos m) π
        (π.1.regPullClass T.current (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T))) := by
  intro δ
  obtain ⟨ρ,hπ,hδ⟩ := ModelSystem.Model.exists_le_le π δ
  have hp := classPseudoeffective_pullback_regPullClass_sub
    (show π.1≤ρ.1 from hπ) T
  have hpush := classPseudoeffective_classPushforward
    (Modification.contMDiff_homOfLE (show δ.1≤ρ.1 from hδ)) (Nat.succ_pos m) hp
  change ClassPseudoeffectiveViaPotentials
    (Modification.classPushforwardOfLE (Nat.succ_pos m) (show δ.1≤ρ.1 from hδ)
      (Modification.classPullbackOfLE (show π.1≤ρ.1 from hπ)
        (π.1.regPullClass T.current (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T))-
        ρ.1.regPullClass T.current (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T))) at hpush
  rw [map_sub,Modification.classPushforwardOfLE_regPullClass] at hpush
  change ClassPseudoeffectiveViaPotentials
    (ModelSystem.Model.cartierClass (Nat.succ_pos m) π _ δ-δ.1.regPullClass T.current _)
  rw [ModelSystem.Model.cartierClass_eq (Nat.succ_pos m) hπ hδ]
  exact hpush

end SGPT.Hodge.BDivChain.SourceMixedOrderDraft
