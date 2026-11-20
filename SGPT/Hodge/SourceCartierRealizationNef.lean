import SGPT.Hodge.SourceCartierPointLelong
import SGPT.Hodge.SourcePolarizedNefIntersection
import SGPT.Hodge.SourceNefFamilyAlgebra

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
  SGPT.Foundations.Analysis.Pending.ThetaPotentialCurrentBottChernClass
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor
  SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft
  SGPT.Hodge.BDivChain.SourceNefProjectiveDraft
  SGPT.Hodge.BDivChain.SourceNefIntersectionDraft
  SGPT.Hodge.BDivChain.SourceMixedOrderDraft
  SGPT.Hodge.BDivChain.SourceIntersection

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X]
  [CompactSpace X] [ConnectedSpace X]

/-- Every actual Cartier realization of a current b-divisor has nef class.
Actual point pullbacks and Demailly regularization generate the conclusion. -/
theorem classNef_of_current_cartier_realization
    (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X)
    (π : (ModelSystem.blowup (m+1) X).Model)
    (α : RealBottChern (m+1) π.1.carrier)
    (hr : (currentBDivisor T).IsRealization π α)
    (κ : KahlerBackground (m+1) π.1.carrier) : ClassNefWithRespectTo κ α := by
  let : ConnectedSpace π.1.carrier := Modification.IsBlowupModel.connectedSpace π.property
  let R := π.1.regPull T.current (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T)
  let hR := π.1.isClosedPositiveCurrent_regPull (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T)
  obtain ⟨θ,u,hu,heq⟩ := hR.exists_thetaPotential
  have hclass : RealBottChern.ofRepresentative θ=α := by
    have h := SGPT.Hodge.BDivChain.bottChernClass_congr
      (S := ⟨R,hR.1,hR.2.1⟩) (S' := thetaClosedCurrent θ u hu) heq
    change π.1.regPullClass T.current (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T)=
      bottChernClass _ _ (thetaClosedCurrent θ u hu) at h
    rw [bottChernClass_thetaClosedCurrent] at h
    exact h.symm.trans (class_regPull_of_actual_cartier_realization T π α hr)
  rw [←hclass]
  exact classNef_of_positive_potential_zero_lelong κ θ u hu
    (potential_lelong_zero_of_actual_cartier_realization T π α hr θ u hu heq)

omit [ConnectedSpace X] in
/-- A root Cartier family is realized on every original model by the actual
pullback of its root class; all higher traces retain literal pullback functoriality. -/
theorem rootCartierAny_realized_on_every_model (β : RealBottChern (m+1) X)
    (π : (ModelSystem.blowup (m+1) X).Model) :
    IsRealizationAny (rootCartierAny β) π
      (Modification.classPullbackOfLE (show Modification.root≤π.1
        from ModelSystem.Model.root_le π) β) := by
  intro ρ h
  rw [rootCartierAny_onModel]
  exact Modification.classPullbackOfLE_trans
    (show Modification.root≤π.1 from ModelSystem.Model.root_le π)
    (show π.1≤ρ.1 from h) β

/-- Every original nef Cartier family has nef class on EACH of its original
realizations, with no bigness, current, point-Lelong or regularization premise.
The current correspondence is applied internally after root Kähler shifts. -/
theorem classNef_of_nef_cartier_realization (ω : KahlerBackground (m+1) X)
    (D : WeilFamilyAny (ModelSystem.blowup (m+1) X)) (hD : IsNefAny D)
    (π : (ModelSystem.blowup (m+1) X).Model)
    (α : RealBottChern (m+1) π.1.carrier) (hr : IsRealizationAny D π α)
    (κ : KahlerBackground (m+1) π.1.carrier) : ClassNefWithRespectTo κ α := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let β := Modification.classPullbackOfLE (show Modification.root≤π.1
    from ModelSystem.Model.root_le π) (RealBottChern.ofRepresentative ω.form)
  have hperturb (ε : ℝ) (hε : 0<ε) : ClassNefWithRespectTo κ (α+ε • β) := by
    let B := kahlerPerturbedBigNef ω ω D hD ε hε
    let T := (realizingCurrent ω B).val
    have hfamily : toExisting _ (Nat.succ_pos m) B.val=currentBDivisor (toBookCurrent T) := by
      exact (congrArg (toExisting _ (Nat.succ_pos m)) (realizingCurrent_family ω B)).symm.trans
        (currentBDivisorAnyOn_eq_existing (ModelSystem.blowup (m+1) X) T)
    have hreal : IsRealizationAny B.val π (α+ε • β) :=
      isRealizationAny_add hr (isRealizationAny_smul
        (rootCartierAny_realized_on_every_model (RealBottChern.ofRepresentative ω.form) π) ε)
    have hrex := (isRealizationAny_iff_existing (Nat.succ_pos m) B.val π (α+ε • β)).mp hreal
    rw [hfamily] at hrex
    exact classNef_of_current_cartier_realization (toBookCurrent T) π (α+ε • β) hrex κ
  let c : ℕ → ℝ := fun k => 1/((k : ℝ)+1)
  have hc (k) : 0<c k := by dsimp [c]; positivity
  have hc0 : Tendsto c atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let : TopologicalSpace (RealBottChern (m+1) π.1.carrier) := SGPT.BDivisor.euclideanTopology _
  have hlim : Tendsto (fun k => α+c k • β) atTop (𝓝 α) := by
    rw [SGPT.BDivisor.tendsto_euclideanTopology_iff]
    intro ℓ
    simpa only [map_add,map_smul,smul_eq_mul,zero_mul,add_zero] using
      tendsto_const_nhds.add (hc0.mul_const (ℓ β))
  exact (SGPT.Hodge.isClosed_setOf_classNef κ).mem_of_tendsto hlim
    (Eventually.of_forall fun k => hperturb (c k) (hc k))

end SGPT.Hodge.BDivChain.SourceNefCartierEquivalenceDraft
