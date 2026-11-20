import SGPT.Hodge.SourceModelCartierAlgebra

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
  SGPT.Hodge.BDivChain.SourceNefIntersectionDraft SGPT.Hodge.BDivChain.SourceCartierSequenceDraft

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X] [CompactSpace X]
local notation "Sys" => ModelSystem.blowup (m+1) X

theorem isRealizationAny_add {D E : WeilFamilyAny Sys}
    {π : (ModelSystem.blowup (m+1) X).Model} {α β : RealBottChern (m+1) π.1.carrier}
    (hD : IsRealizationAny D π α) (hE : IsRealizationAny E π β) :
    IsRealizationAny (D+E) π (α+β) := by
  intro ρ h
  change D.val ρ+E.val ρ=Modification.classPullbackOfLE (show π.1≤ρ.1 from h) (α+β)
  rw [hD ρ h,hE ρ h,map_add]

theorem isRealizationAny_smul {D : WeilFamilyAny Sys}
    {π : (ModelSystem.blowup (m+1) X).Model} {α : RealBottChern (m+1) π.1.carrier}
    (hD : IsRealizationAny D π α) (c : ℝ) : IsRealizationAny (c • D) π (c • α) := by
  intro ρ h
  change c • D.val ρ=Modification.classPullbackOfLE (show π.1≤ρ.1 from h) (c • α)
  rw [hD ρ h,map_smul]

theorem isNefCartierAny_add (ω : KahlerBackground (m+1) X)
    {D E : WeilFamilyAny Sys} (hD : IsNefCartierAny D) (hE : IsNefCartierAny E) :
    IsNefCartierAny (D+E) := by
  classical
  let F : Bool → WeilFamilyAny Sys := fun b => if b then D else E
  have hF : ∀ b,IsNefCartierAny (F b) := by
    intro b
    cases b with
    | false => exact hE
    | true => exact hD
  obtain ⟨π,κ,θ,hr,hn⟩ := exists_common_nef_realization ω F hF
  have hreal := isRealizationAny_add (hr true) (hr false)
  have he : RealBottChern.ofRepresentative (θ true+θ false)=
      RealBottChern.ofRepresentative (θ true)+RealBottChern.ofRepresentative (θ false) :=
    map_add RealBottChern.ofRepresentativeLinearMap _ _
  refine ⟨π,RealBottChern.ofRepresentative (θ true+θ false),?_,κ,?_⟩
  · rw [he]
    exact hreal
  · exact nefWithRespectTo_add κ (hn true) (hn false)

theorem isNefCartierAny_smul {D : WeilFamilyAny Sys} (hD : IsNefCartierAny D)
    {c : ℝ} (hc : 0≤c) : IsNefCartierAny (c • D) := by
  obtain ⟨π,α,hr,κ,hα⟩ := hD
  exact ⟨π,c • α,isRealizationAny_smul hr c,κ,classNefWithRespectTo_smul κ hc hα⟩

theorem convergesAny_add {I : Type*} {l : Filter I}
    {A B : I → WeilFamilyAny Sys} {D E : WeilFamilyAny Sys}
    (ha : ConvergesAny l A D) (hb : ConvergesAny l B E) :
    ConvergesAny l (fun i => A i+B i) (D+E) := by
  intro π
  rw [tendsto_euclideanTopology_iff]
  intro f
  change Tendsto (fun i => f ((A i).val π+(B i).val π)) l (𝓝 (f (D.val π+E.val π)))
  simpa only [map_add] using
    ((tendsto_euclideanTopology_iff.mp (ha π)) f).add
      ((tendsto_euclideanTopology_iff.mp (hb π)) f)

theorem convergesAny_smul {I : Type*} {l : Filter I}
    {A : I → WeilFamilyAny Sys} {D : WeilFamilyAny Sys}
    (ha : ConvergesAny l A D) (c : ℝ) : ConvergesAny l (fun i => c • A i) (c • D) := by
  intro π
  rw [tendsto_euclideanTopology_iff]
  intro f
  change Tendsto (fun i => f (c • (A i).val π)) l (𝓝 (f (c • D.val π)))
  simpa only [map_smul,smul_eq_mul] using
    ((tendsto_euclideanTopology_iff.mp (ha π)) f).const_mul c

theorem leAny_add {D E F G : WeilFamilyAny Sys} (hDE : LEAny D E) (hFG : LEAny F G) :
    LEAny (D+F) (E+G) := by
  intro π
  have hp := SGPT.Okounkov.TranscendentalVolumeConcavity.classPseudoeffective_add (hDE π) (hFG π)
  change ClassPseudoeffectiveViaPotentials ((E.val π+G.val π)-(D.val π+F.val π))
  convert hp using 1; abel

theorem leAny_smul {D E : WeilFamilyAny Sys} (hDE : LEAny D E) {c : ℝ} (hc : 0≤c) :
    LEAny (c • D) (c • E) := by
  intro π
  have hp := SGPT.Okounkov.TranscendentalVolumeConcavity.classPseudoeffective_smul (hDE π) hc
  change ClassPseudoeffectiveViaPotentials (c • E.val π-c • D.val π)
  simpa only [smul_sub] using hp

/-- A source tuple update retains its genuine Cartier witnesses. -/
theorem isNefCartierAny_update (D : Fin (m+1) → WeilFamilyAny Sys)
    (hD : ∀ i,IsNefCartierAny (D i)) (j : Fin (m+1)) (U : WeilFamilyAny Sys)
    (hU : IsNefCartierAny U) : ∀ i,IsNefCartierAny (Function.update D j U i) := by
  classical
  intro i
  by_cases hij : i=j
  · subst i
    simpa only [Function.update_self] using hU
  · simpa only [Function.update_of_ne hij] using hD i

theorem leAny_update (D E : Fin (m+1) → WeilFamilyAny Sys)
    (hDE : ∀ i,LEAny (D i) (E i)) (j : Fin (m+1)) (U V : WeilFamilyAny Sys)
    (hUV : LEAny U V) : ∀ i,LEAny (Function.update D j U i) (Function.update E j V i) := by
  classical
  intro i
  by_cases hij : i=j
  · subst i
    simpa only [Function.update_self] using hUV
  · simpa only [Function.update_of_ne hij] using hDE i

theorem convergesAny_update {I : Type*} {l : Filter I}
    (A : Fin (m+1) → I → WeilFamilyAny Sys) (D : Fin (m+1) → WeilFamilyAny Sys)
    (hA : ∀ i,ConvergesAny l (A i) (D i)) (j : Fin (m+1))
    (U : I → WeilFamilyAny Sys) (V : WeilFamilyAny Sys) (hU : ConvergesAny l U V) :
    ∀ i,ConvergesAny l (fun k => Function.update (fun i => A i k) j (U k) i)
      (Function.update D j V i) := by
  classical
  intro i
  by_cases hij : i=j
  · subst i
    simpa only [Function.update_self] using hU
  · simpa only [Function.update_of_ne hij] using hA i

end SGPT.Hodge.BDivChain.SourceMixedOrderDraft
