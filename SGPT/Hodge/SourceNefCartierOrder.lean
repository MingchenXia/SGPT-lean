import SGPT.Hodge.SourceNefCartierCohomology
import SGPT.Foundations.Analysis.Pending.DominationNefIntersectionOrder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
  SGPT.Hodge.BDivChain.SourceNefIntersectionDraft

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
local notation "Sys" => ModelSystem.blowup (m+1) X

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- A finite list has an ACTUAL common original blowup model. This uses
the existing book common-model theorem, never a supplied common-model certificate. -/
theorem exists_common_book_model {I : Type*} [Fintype I]
    (π : I → (ModelSystem.blowup (m+1) X).Model) :
    ∃ ρ : (ModelSystem.blowup (m+1) X).Model,∀ i,π i≤ρ := by
  classical
  have key (S : Finset I) : ∃ ρ : (ModelSystem.blowup (m+1) X).Model,∀ i ∈ S,π i≤ρ := by
    induction S using Finset.induction_on with
    | empty => exact ⟨ModelSystem.Model.root,fun i hi => False.elim (Finset.notMem_empty i hi)⟩
    | @insert a S ha ih =>
      obtain ⟨ρ,hρ⟩ := ih
      obtain ⟨σ,h1,h2⟩ := ModelSystem.Model.exists_le_le (π a) ρ
      refine ⟨σ,?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl|hi
      · exact h1
      · exact (hρ i hi).trans h2
  obtain ⟨ρ,hρ⟩ := key Finset.univ
  exact ⟨ρ,fun i => hρ i (Finset.mem_univ i)⟩

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- EVERY actual finite nef Cartier tuple has an internally produced genuine
common realization by actual nef smooth classes, with no target reader certificate. -/
theorem exists_common_nef_realization (ω : KahlerBackground (m+1) X)
    {I : Type*} [Fintype I] (D : I → WeilFamilyAny Sys) (hD : ∀ i,IsNefCartierAny (D i)) :
    ∃ (ρ : (ModelSystem.blowup (m+1) X).Model) (κ : KahlerBackground (m+1) ρ.1.carrier)
      (θ : I → ClosedRealOneOneForm (m+1) ρ.1.carrier),
      (∀ i,IsRealizationAny (D i) ρ (RealBottChern.ofRepresentative (θ i))) ∧
        ∀ i,NefWithRespectTo κ (θ i) := by
  classical
  choose π α hr κ₀ hnef using hD
  obtain ⟨ρ,hρ⟩ := exists_common_book_model π
  obtain ⟨κ⟩ := ModelSystem.blowup_nonempty_kahlerBackground ⟨ω⟩ ρ
  let hf i := Modification.contMDiff_homOfLE (show (π i).1≤ρ.1 from hρ i)
  let θ i := ClosedRealOneOneForm.pullback (hf i) (Quotient.out (α i))
  have hrep i : RealBottChern.ofRepresentative (Quotient.out (α i))=α i := Quotient.out_eq (α i)
  have hform i : NefWithRespectTo (κ₀ i) (Quotient.out (α i)) := by
    change ClassNefWithRespectTo (κ₀ i) (RealBottChern.ofRepresentative (Quotient.out (α i)))
    rw [hrep i]
    exact hnef i
  refine ⟨ρ,κ,θ,?_,?_⟩
  · intro i
    have hreal : IsRealizationAny (D i) (π i) (RealBottChern.ofRepresentative (Quotient.out (α i))) := by
      rw [hrep i]
      exact hr i
    have hp := ((isRealizationAny_iff_existing (Nat.succ_pos m) (D i) (π i) _).mp hreal).pullback (hρ i)
    apply (isRealizationAny_iff_existing (Nat.succ_pos m) (D i) ρ _).mpr
    simpa only [θ,hf,Modification.classPullbackOfLE,classPullback_ofRepresentative] using hp
  · intro i
    exact nefWithRespectTo_pullback (hf i) (κ₀ i) κ (hform i)

/-- Genuine ORIGINAL order monotonicity for arbitrary nef Cartier tuples:
the common realization and the actual cohomological reader are produced internally. -/
theorem nefIntersection_mono_of_nefCartier (ω : KahlerBackground (m+1) X)
    (D E : Fin (m+1) → WeilFamilyAny Sys)
    (hD : ∀ i,IsNefCartierAny (D i)) (hE : ∀ i,IsNefCartierAny (E i))
    (hDE : ∀ i,LEAny (D i) (E i)) : (nefIntersection D).toReal≤(nefIntersection E).toReal := by
  classical
  let F : Fin (m+1) ⊕ Fin (m+1) → WeilFamilyAny Sys := Sum.elim D E
  have hF : ∀ i,IsNefCartierAny (F i) := by intro i; cases i with | inl i => exact hD i | inr i => exact hE i
  obtain ⟨π,κ,θ,hr,hnef⟩ := exists_common_nef_realization ω F hF
  let A : Fin (m+1) → ClosedRealOneOneForm (m+1) π.1.carrier := fun i => θ (Sum.inl i)
  let B : Fin (m+1) → ClosedRealOneOneForm (m+1) π.1.carrier := fun i => θ (Sum.inr i)
  have hDA i : IsRealizationAny (D i) π (RealBottChern.ofRepresentative (A i)) := hr (Sum.inl i)
  have hEB i : IsRealizationAny (E i) π (RealBottChern.ofRepresentative (B i)) := hr (Sum.inr i)
  rw [nefIntersection_of_common_nef_realization ω D π κ A hDA (fun i => hnef (Sum.inl i)),
    nefIntersection_of_common_nef_realization ω E π κ B hEB (fun i => hnef (Sum.inr i))]
  let : MeasurableSpace π.1.carrier := borel π.1.carrier
  let : BorelSpace π.1.carrier := ⟨rfl⟩
  apply DominationNefIntersectionOrder.slotIntegral_le_of_nef_pseudoeffective_differences κ A B
    (fun i => hnef (Sum.inl i)) (fun i => hnef (Sum.inr i))
  intro i _
  have hp := hDE i π
  have hA : (D i).val π=RealBottChern.ofRepresentative (A i) :=
    ((isRealizationAny_iff_existing (Nat.succ_pos m) (D i) π _).mp (hDA i)).onModel_eq
  have hB : (E i).val π=RealBottChern.ofRepresentative (B i) :=
    ((isRealizationAny_iff_existing (Nat.succ_pos m) (E i) π _).mp (hEB i)).onModel_eq
  rw [hA,hB] at hp
  have he : RealBottChern.ofRepresentative (B i-A i)=
      RealBottChern.ofRepresentative (B i)-RealBottChern.ofRepresentative (A i) :=
    map_sub RealBottChern.ofRepresentativeLinearMap _ _
  rw [←he] at hp
  exact (classPseudoeffectiveViaPotentials_ofRepresentative (B i-A i)).mp hp

end SGPT.Hodge.BDivChain.SourceMixedOrderDraft
