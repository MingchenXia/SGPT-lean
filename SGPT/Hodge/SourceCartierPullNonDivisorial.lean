import SGPT.Hodge.SourceRegFamily
import SGPT.Hodge.SourceCurrentCorrespondence
import SGPT.Hodge.SourceCurrentNonDivisorial

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceNefCartierEquivalenceDraft
open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor SGPT.BDivisor.PrimePushforward
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft
variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X] [CompactSpace X]
local notation "Sys" => ModelSystem.blowup (m+1) X
local notation "Cur" => GlobalCurrent (m+1) X (degreeTwo (Nat.succ_pos m))

/-- A Cartier trace on an ARBITRARY original realization model is the class
of the actual regular pullback current on that same model. -/
theorem class_regPull_of_actual_cartier_realization
    (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X) (π : (ModelSystem.blowup (m+1) X).Model)
    (α : RealBottChern (m+1) π.1.carrier)
    (hr : (currentBDivisor T).IsRealization π α) :
    π.1.regPullClass T.current (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T)=α := by
  have h := hr π (le_refl π)
  rw [Modification.classPullbackOfLE_refl] at h
  exact h

variable [ConnectedSpace X]

/-- Exact higher-model Cartier readback forces the actual pullback of the
actual regular current to be nondivisorial. No zero-Lelong or zero-current
certificate is supplied: zero-class positivity produces it internally. -/
theorem isNonDivisorial_pull_regPull_of_actual_cartier_realization
    (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X) (π ρ : (ModelSystem.blowup (m+1) X).Model)
    (α : RealBottChern (m+1) π.1.carrier)
    (hr : (currentBDivisor T).IsRealization π α)
    (f : ρ.1.carrier → π.1.carrier)
    (hf : IsAnalyticModification (n := m+1) f)
    (hsquare : π.1.map ∘ f=ρ.1.map) :
    SGPT.Siu.IsNonDivisorial
      (Modification4.pull hf (π.1.regPull T.current (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T))
        (π.1.isClosedPositiveCurrent_regPull (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T)))
      (Modification4.isClosedPositiveCurrent_pull hf
        (π.1.isClosedPositiveCurrent_regPull (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T))) := by
  let : ConnectedSpace ρ.1.carrier := Modification.IsBlowupModel.connectedSpace ρ.property
  let hT := SGPT.Siu.isClosedPositiveCurrent_bookCurrent T
  let P := Modification4.pull π.1.isAnalyticModification T.current hT
  let hP := Modification4.isClosedPositiveCurrent_pull π.1.isAnalyticModification hT
  let R := π.1.regPull T.current hT
  let hR := π.1.isClosedPositiveCurrent_regPull hT
  let q : Modification (m+1) π.1.carrier :=
    { carrier := ρ.1.carrier, map := f, isAnalyticModification := hf }
  have hdom : π≤ρ := ⟨f,hf.1,hsquare⟩
  have hcomp : Modification4.pull ρ.1.isAnalyticModification T.current hT=
      Modification4.pull hf P hP := by
    rw [pull_congr hsquare.symm ρ.1.isAnalyticModification
      (AnalyticModificationComposition.isAnalyticModification_comp π.1.isAnalyticModification hf)]
    exact pull_comp π.1.isAnalyticModification hf hT
  have hreg : q.regPull R hR=ρ.1.regPull T.current hT := by
    have h := SourceReg.regPull_regular_eq q (SGPT.Siu.toBookCurrent P hP)
    change q.regPull R hR=q.regPull P hP at h
    exact h.trans (siuRegularPart_congr hcomp.symm _ _)
  have hRegClass : q.regPullClass R hR=classPullback hf.1 α := by
    have h := hr ρ hdom
    change ρ.1.regPullClass T.current hT=Modification.classPullbackOfLE
      (show π.1≤ρ.1 from hdom) α at h
    rw [Modification.classPullbackOfLE_eq (show π.1≤ρ.1 from hdom) hf.1 hsquare] at h
    exact (SGPT.Hodge.BDivChain.bottChernClass_congr hreg).trans h
  have hRClass : bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) ⟨R,hR.1,hR.2.1⟩=α :=
    class_regPull_of_actual_cartier_realization T π α hr
  let Q := Modification4.pull hf R hR
  let hQ := Modification4.isClosedPositiveCurrent_pull hf hR
  have hQClass : bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) ⟨Q,hQ.1,hQ.2.1⟩=
      classPullback hf.1 α := by
    rw [bottChernClass_pull hf hR,hRClass]
  have hroot : (currentBDivisor (SGPT.Siu.toBookCurrent Q hQ)).root=
      SGPT.PSH.BookCurrent.currentClass (SGPT.Siu.toBookCurrent Q hQ) := by
    have h := currentBDivisorOn_root (ModelSystem.blowup (m+1) ρ.1.carrier) hQ
    exact h.trans (hRegClass.trans hQClass.symm)
  exact isNonDivisorial_of_root_eq_currentClass (SGPT.Siu.toBookCurrent Q hQ) hroot

end SGPT.Hodge.BDivChain.SourceNefCartierEquivalenceDraft
