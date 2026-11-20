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
  SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft SGPT.Hodge.BDivChain.SourceIntersection
  SGPT.Hodge.BDivChain.SourceNefIntersectionDraft

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X] [CompactSpace X]
local notation "Sys" => ModelSystem.blowup (m+1) X

theorem leAny_trans {D E F : WeilFamilyAny Sys} (hDE : LEAny D E) (hEF : LEAny E F) :
    LEAny D F := by
  intro π
  have hp := SGPT.Okounkov.TranscendentalVolumeConcavity.classPseudoeffective_add
    (hDE π) (hEF π)
  change ClassPseudoeffectiveViaPotentials (F.val π-D.val π)
  convert hp using 1; abel

theorem modelKahler_pseudoeffective (π : (ModelSystem.blowup (m+1) X).Model)
    (κ : KahlerBackground (m+1) π.1.carrier) :
    ClassPseudoeffectiveViaPotentials (RealBottChern.ofRepresentative κ.form) := by
  exact ⟨fun _ => 0,(LocalPotentials.isThetaPshPotential_zero_iff _).mpr κ.isSemipositive⟩

theorem modelCartier_shift_isNefCartier (π : (ModelSystem.blowup (m+1) X).Model)
    (κ : KahlerBackground (m+1) π.1.carrier) {α : RealBottChern (m+1) π.1.carrier}
    (hα : ClassNefWithRespectTo κ α) {ε : ℝ} (hε : 0≤ε) :
    IsNefCartierAny (modelCartier π (α+ε • RealBottChern.ofRepresentative κ.form)) :=
  modelCartier_isNefCartier π κ (classNefWithRespectTo_add κ hα
    (classNefWithRespectTo_smul κ hε (classNefWithRespectTo_of_semipositive κ κ.isSemipositive)))

theorem modelCartier_shift_antitone (π : (ModelSystem.blowup (m+1) X).Model)
    (κ : KahlerBackground (m+1) π.1.carrier) (α : RealBottChern (m+1) π.1.carrier)
    {a b : ℝ} (hab : a≤b) :
    LEAny (modelCartier π (α+a • RealBottChern.ofRepresentative κ.form))
      (modelCartier π (α+b • RealBottChern.ofRepresentative κ.form)) := by
  apply modelCartier_mono
  have hp := SGPT.Okounkov.TranscendentalVolumeConcavity.classPseudoeffective_smul
    (modelKahler_pseudoeffective π κ) (sub_nonneg.mpr hab)
  convert hp using 1; module

theorem modelCartier_shift_converges (π : (ModelSystem.blowup (m+1) X).Model)
    (κ : KahlerBackground (m+1) π.1.carrier) (α : RealBottChern (m+1) π.1.carrier)
    {I : Type*} {l : Filter I} {ε : I → ℝ} (hε : Tendsto ε l (𝓝 0)) :
    ConvergesAny l (fun i => modelCartier π (α+ε i • RealBottChern.ofRepresentative κ.form))
      (modelCartier π α) := by
  apply modelCartier_converges
  rw [tendsto_euclideanTopology_iff]
  intro f
  simpa only [map_add,map_smul,smul_eq_mul,zero_mul,add_zero] using
    tendsto_const_nhds.add (hε.mul_const (f (RealBottChern.ofRepresentative κ.form)))

/-- A decreasing actual family stays above its original modelwise limit.
Closedness of the genuine positive cone supplies the conclusion model by model. -/
theorem leAny_of_antitone_converges [ConnectedSpace X] (ω : KahlerBackground (m+1) X)
    {I : Type*} [Preorder I] [IsDirected I (·≤·)] [Nonempty I]
    (A : I → WeilFamilyAny Sys) (D : WeilFamilyAny Sys)
    (ha : ∀ i j,i≤j → LEAny (A j) (A i)) (hc : ConvergesAny atTop A D) (i : I) :
    LEAny D (A i) := by
  intro π
  obtain ⟨κ⟩ := ModelSystem.blowup_nonempty_kahlerBackground ⟨ω⟩ π
  let : ConnectedSpace π.1.carrier :=
    SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification π.1.isAnalyticModification
  let : TopologicalSpace (RealBottChern (m+1) π.1.carrier) := euclideanTopology _
  have hconv : Tendsto (fun j => (A i).val π-(A j).val π) atTop
      (@nhds _ (euclideanTopology _) ((A i).val π-D.val π)) := by
    rw [tendsto_euclideanTopology_iff]
    intro f
    simpa only [map_sub] using
      tendsto_const_nhds.sub ((tendsto_euclideanTopology_iff.mp (hc π)) f)
  exact (SGPT.Hodge.isClosed_setOf_classPseudoeffective κ).mem_of_tendsto hconv
    (eventually_atTop.mpr ⟨i,fun j hij => ha i j hij π⟩)

variable [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The original modelwise convergence and actual Siu-produced Cartier
upper give an EVENTUAL GLOBAL family bound. No global-domination output
certificate, finite-model hypothesis or chosen cofinal tower is an input. -/
theorem eventually_bigNef_le_modelCartier (ω : KahlerBackground (m+1) X)
    {I : Type*} {l : Filter I} (A : I → BigNefFamily (n := m+1) (X := X))
    (D : WeilFamilyAny Sys) (hc : ConvergesAny l (fun i => (A i).val) D)
    (π : (ModelSystem.blowup (m+1) X).Model) (κ : KahlerBackground (m+1) π.1.carrier)
    (α : RealBottChern (m+1) π.1.carrier)
    (hα : ClassPseudoeffectiveViaPotentials (α-D.val π)) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ i in l,LEAny (A i).val
      (modelCartier π (α+ε • RealBottChern.ofRepresentative κ.form)) := by
  filter_upwards [SGPT.Hodge.eventually_classPseudoeffective_add_smul_sub κ (hc π) hε] with i hi
  apply leAny_trans (bigNefFamily_le_modelCartier ω (A i) π)
  apply modelCartier_mono
  have hp := SGPT.Okounkov.TranscendentalVolumeConcavity.classPseudoeffective_add hi.1 hα
  convert hp using 1; module

end SGPT.Hodge.BDivChain.SourceMixedOrderDraft
