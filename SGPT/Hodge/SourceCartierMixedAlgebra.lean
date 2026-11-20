import SGPT.Hodge.SourceNefFamilyAlgebra

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
  SGPT.Foundations.Analysis.Pending.NefMixedMass
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
  SGPT.Hodge.BDivChain.SourceNefIntersectionDraft

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
local notation "Sys" => ModelSystem.blowup (m+1) X

theorem nefIntersectionReal_of_common_nef_realization (ω : KahlerBackground (m+1) X)
    (D : Fin (m+1) → WeilFamilyAny Sys)
    (π : (ModelSystem.blowup (m+1) X).Model) (κ : KahlerBackground (m+1) π.1.carrier)
    (θ : Fin (m+1) → ClosedRealOneOneForm (m+1) π.1.carrier)
    (hr : ∀ i,IsRealizationAny (D i) π (RealBottChern.ofRepresentative (θ i)))
    (hθ : ∀ i,NefWithRespectTo κ (θ i)) :
    nefIntersectionReal D=modelSlotIntegral π κ θ := by
  have hD i : IsNefAny (D i) := isNefAny_of_nef_realization (D i) π κ (θ i) (hr i) (hθ i)
  have h := nefIntersection_of_common_nef_realization ω D π κ θ hr hθ
  simpa only [nefIntersection,ENNReal.toReal_ofReal (nefIntersectionReal_nonneg ω D hD)] using h

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem isRealizationAny_update (D : Fin (m+1) → WeilFamilyAny Sys)
    (π : (ModelSystem.blowup (m+1) X).Model)
    (θ : Fin (m+1) → ClosedRealOneOneForm (m+1) π.1.carrier)
    (hr : ∀ i,IsRealizationAny (D i) π (RealBottChern.ofRepresentative (θ i)))
    (j : Fin (m+1)) (U : WeilFamilyAny Sys) (η : ClosedRealOneOneForm (m+1) π.1.carrier)
    (hU : IsRealizationAny U π (RealBottChern.ofRepresentative η)) :
    ∀ i,IsRealizationAny (Function.update D j U i) π
      (RealBottChern.ofRepresentative (Function.update θ j η i)) := by
  classical
  intro i
  by_cases hij : i=j
  · subst i
    simpa only [Function.update_self] using hU
  · simpa only [Function.update_of_ne hij] using hr i

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem nef_update (π : (ModelSystem.blowup (m+1) X).Model)
    (κ : KahlerBackground (m+1) π.1.carrier)
    (θ : Fin (m+1) → ClosedRealOneOneForm (m+1) π.1.carrier)
    (hθ : ∀ i,NefWithRespectTo κ (θ i)) (j : Fin (m+1))
    (η : ClosedRealOneOneForm (m+1) π.1.carrier) (hη : NefWithRespectTo κ η) :
    ∀ i,NefWithRespectTo κ (Function.update θ j η i) := by
  classical
  intro i
  by_cases hij : i=j
  · subst i
    simpa only [Function.update_self] using hη
  · simpa only [Function.update_of_ne hij] using hθ i

/-- Slot additivity on genuine original nef Cartier inputs, through ONE
internally produced common model and the actual smooth multilinear reader. -/
theorem nefIntersectionReal_update_add_cartier (ω : KahlerBackground (m+1) X)
    (D : Fin (m+1) → WeilFamilyAny Sys) (hD : ∀ i,IsNefCartierAny (D i))
    (j : Fin (m+1)) (U V : WeilFamilyAny Sys)
    (hU : IsNefCartierAny U) (hV : IsNefCartierAny V) :
    nefIntersectionReal (Function.update D j (U+V))=
      nefIntersectionReal (Function.update D j U)+nefIntersectionReal (Function.update D j V) := by
  classical
  let F : Fin (m+1) ⊕ Bool → WeilFamilyAny Sys := Sum.elim D (fun b => if b then U else V)
  have hF : ∀ i,IsNefCartierAny (F i) := by
    intro i
    cases i with
    | inl i => exact hD i
    | inr b => cases b with | false => exact hV | true => exact hU
  obtain ⟨π,κ,θ,hr,hn⟩ := exists_common_nef_realization ω F hF
  let θ₀ i := θ (Sum.inl i)
  let A := θ (Sum.inr true)
  let B := θ (Sum.inr false)
  have hbase i : IsRealizationAny (D i) π (RealBottChern.ofRepresentative (θ₀ i)) := hr (Sum.inl i)
  have hUA : IsRealizationAny U π (RealBottChern.ofRepresentative A) := hr (Sum.inr true)
  have hVB : IsRealizationAny V π (RealBottChern.ofRepresentative B) := hr (Sum.inr false)
  have hsum : IsRealizationAny (U+V) π (RealBottChern.ofRepresentative (A+B)) := by
    have he : RealBottChern.ofRepresentative (A+B)=
        RealBottChern.ofRepresentative A+RealBottChern.ofRepresentative B :=
      map_add RealBottChern.ofRepresentativeLinearMap _ _
    rw [he]
    exact isRealizationAny_add hUA hVB
  rw [nefIntersectionReal_of_common_nef_realization ω _ π κ _
      (isRealizationAny_update D π θ₀ hbase j (U+V) (A+B) hsum)
      (nef_update π κ θ₀ (fun i => hn (Sum.inl i)) j (A+B)
        (nefWithRespectTo_add κ (hn (Sum.inr true)) (hn (Sum.inr false)))),
    nefIntersectionReal_of_common_nef_realization ω _ π κ _
      (isRealizationAny_update D π θ₀ hbase j U A hUA)
      (nef_update π κ θ₀ (fun i => hn (Sum.inl i)) j A (hn (Sum.inr true))),
    nefIntersectionReal_of_common_nef_realization ω _ π κ _
      (isRealizationAny_update D π θ₀ hbase j V B hVB)
      (nef_update π κ θ₀ (fun i => hn (Sum.inl i)) j B (hn (Sum.inr false)))]
  let : MeasurableSpace π.1.carrier := borel π.1.carrier
  let : BorelSpace π.1.carrier := ⟨rfl⟩
  exact slotIntegral_update_add κ θ₀ j A B

theorem nefIntersectionReal_update_smul_cartier (ω : KahlerBackground (m+1) X)
    (D : Fin (m+1) → WeilFamilyAny Sys) (hD : ∀ i,IsNefCartierAny (D i))
    (j : Fin (m+1)) (U : WeilFamilyAny Sys) (hU : IsNefCartierAny U)
    (c : ℝ) (hc : 0≤c) :
    nefIntersectionReal (Function.update D j (c • U))=
      c * nefIntersectionReal (Function.update D j U) := by
  classical
  let F : Fin (m+1) ⊕ Unit → WeilFamilyAny Sys := Sum.elim D (fun _ => U)
  have hF : ∀ i,IsNefCartierAny (F i) := by
    intro i
    cases i with | inl i => exact hD i | inr _ => exact hU
  obtain ⟨π,κ,θ,hr,hn⟩ := exists_common_nef_realization ω F hF
  let θ₀ i := θ (Sum.inl i)
  let A := θ (Sum.inr ())
  have hbase i : IsRealizationAny (D i) π (RealBottChern.ofRepresentative (θ₀ i)) := hr (Sum.inl i)
  have hUA : IsRealizationAny U π (RealBottChern.ofRepresentative A) := hr (Sum.inr ())
  have hscale : IsRealizationAny (c • U) π (RealBottChern.ofRepresentative (c • A)) := by
    rw [RealBottChern.ofRepresentative_smul]
    exact isRealizationAny_smul hUA c
  rw [nefIntersectionReal_of_common_nef_realization ω _ π κ _
      (isRealizationAny_update D π θ₀ hbase j (c • U) (c • A) hscale)
      (nef_update π κ θ₀ (fun i => hn (Sum.inl i)) j (c • A)
        (nefWithRespectTo_smul κ hc (hn (Sum.inr ())))),
    nefIntersectionReal_of_common_nef_realization ω _ π κ _
      (isRealizationAny_update D π θ₀ hbase j U A hUA)
      (nef_update π κ θ₀ (fun i => hn (Sum.inl i)) j A (hn (Sum.inr ())))]
  let : MeasurableSpace π.1.carrier := borel π.1.carrier
  let : BorelSpace π.1.carrier := ⟨rfl⟩
  exact slotIntegral_update_smul κ θ₀ j c A

theorem nefIntersectionReal_perm_cartier (ω : KahlerBackground (m+1) X)
    (D : Fin (m+1) → WeilFamilyAny Sys) (hD : ∀ i,IsNefCartierAny (D i))
    (σ : Equiv.Perm (Fin (m+1))) :
    nefIntersectionReal (fun i => D (σ i))=nefIntersectionReal D := by
  obtain ⟨π,κ,θ,hr,hn⟩ := exists_common_nef_realization ω D hD
  rw [nefIntersectionReal_of_common_nef_realization ω _ π κ (fun i => θ (σ i))
      (fun i => hr (σ i)) (fun i => hn (σ i)),
    nefIntersectionReal_of_common_nef_realization ω _ π κ θ hr hn]
  let : MeasurableSpace π.1.carrier := borel π.1.carrier
  let : BorelSpace π.1.carrier := ⟨rfl⟩
  exact slotIntegral_perm κ θ σ

end SGPT.Hodge.BDivChain.SourceMixedOrderDraft
