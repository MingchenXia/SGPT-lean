import SGPT.Hodge.SourceCartierQEAFamilyLimits
import SGPT.Hodge.SourceCartierFamilySequenceAlgebra

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.SourceCartierSequenceDraft

open Set Filter SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData SGPT.Foundations.Analysis.Pending
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
  SGPT.Hodge.BDivChain.SourceNefProjectiveDraft
open scoped Topology ENNReal

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The whole source positive-dimensional sequence: every geometric and
analytic producer is called on the original nef input, without any supplied
simultaneous-QEA/cofinal-model/decreasing-approximation certificate. -/
theorem exists_decreasing_big_nefCartier_sequence_pos (ω : KahlerBackground (m+1) X)
    (D : WeilFamilyAny (ModelSystem.blowup (m+1) X)) (hD : IsNefAny D) :
    ∃ F : ℕ → WeilFamilyAny (ModelSystem.blowup (m+1) X),
      (∀ i, IsNefCartierAny (F i) ∧ 0 < volumeAny (F i)) ∧
      (∀ i j : ℕ, i ≤ j → LEAny (F j) (F i)) ∧ ConvergesAny atTop F D := by
  obtain ⟨θ,u,hu,hK,hclass,hfamily⟩ := exists_kahler_realization_rows ω D hD
  have hI := realization_rows_IEquivalent ω D θ u hu hclass hfamily
  choose U threshold hQ hgentle hterm using fun i => exists_eventuallyKahler_exactDyadicQEA (hK i)
  let k := threshold 0
  let V (i j : ℕ) := U i (j+k)
  have hV₀ (j : ℕ) : IsThetaPshPotential (θ 0).val (V 0 j) ∧
      IsKahlerCurrentPotential (θ 0) (V 0 j) :=
    hterm 0 (j+k) (Nat.le_add_left _ _)
  have hV (i j : ℕ) (hj : threshold i ≤ j) : IsThetaPshPotential (θ i).val (V i j) ∧
      IsKahlerCurrentPotential (θ i) (V i j) :=
    hterm i (j+k) (hj.trans (Nat.le_add_right _ _))
  have hQ₀ : SGPT.PSH.SourceQuasiEquisingularApproximation (θ 0) (u 0) (V 0) :=
    SGPT.PSH.sourceQuasiEquisingularApproximation_tail (hQ 0) k
  let C := rootCartierAny (RealBottChern.ofRepresentative ω.form)
  let S (j : ℕ) := currentBDivisorAnyOn (ModelSystem.blowup (m+1) X)
    (representedCurrent (θ 0) (V 0 j) (hV₀ j).1)
  let B (j : ℕ) := S j-C
  have hSanti := representedFamily_antitone_of_qea (θ 0) (u 0) (V 0) hQ₀ (fun j => (hV₀ j).1)
  have hBanti (i j : ℕ) (hij : i ≤ j) : LEAny (B j) (B i) :=
    leAny_sub_const (hSanti i j hij) C
  have hSconv : ConvergesAny atTop S (D+C) := by
    have hc := representedFamily_converges_of_kahler_qea ω (θ 0) (u 0) (hu 0) (hK 0)
      (V 0) hQ₀ (fun j => (hV₀ j).1)
    rw [hfamily 0] at hc
    simpa only [reciprocalStep,Nat.cast_zero,zero_add,div_one,one_smul] using hc
  have hBconv : ConvergesAny atTop B D := by
    simpa only [add_sub_cancel_right] using convergesAny_sub_const hSconv C
  let j := fastIndex threshold
  have hj (i : ℕ) : threshold i ≤ j i := fastIndex_ge threshold i
  let F (i : ℕ) := currentBDivisorAnyOn (ModelSystem.blowup (m+1) X)
    (representedCurrent (θ i) (V i (j i)) (hV i (j i) (hj i)).1)
  have hF (i : ℕ) : IsNefCartierAny (F i) ∧ 0 < volumeAny (F i) :=
    representedFamily_big_nefCartier ω (θ i) (V i (j i))
      (hV i (j i) (hj i)).1 (hV i (j i) (hj i)).2 (hgentle i (j i+k)).2.2.1
  have hmatch (i : ℕ) : F i=B (j i)+reciprocalStep i • C := by
    have hs := sameDyadicType_of_IEquivalent (hI i) (hgentle i) (hgentle 0) (j i+k)
    exact matchedRow_family_minus_shift ω (sourceRootClass D) θ hclass i
      (V i (j i)) (V 0 (j i)) (hV i (j i) (hj i)).1 (hV₀ (j i)).1 hs
  refine ⟨F,hF,?_,?_⟩
  · intro a b hab
    rw [hmatch a,hmatch b]
    exact leAny_add_smul (hBanti (j a) (j b) ((fastIndex_strictMono threshold).monotone hab))
      (rootKahler_isPseudoeffectiveAny ω) (reciprocalStep_antitone hab)
  · have hc := convergesAny_add_smul_zero
      (convergesAny_comp hBconv (fastIndex_tendsto threshold)) C reciprocalStep_tendsto
    have heF : F=(fun i => B (j i)+reciprocalStep i • C) := funext hmatch
    rw [heF]
    exact hc

end SGPT.Hodge.BDivChain.SourceCartierSequenceDraft

namespace SGPT.Hodge.BDivChain.SourceCartierSequenceDraft

open Filter SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.BDivisor
  SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
open scoped Topology ENNReal

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

/-- WHOLE cor:nef_Cartierseq on every original nef family in ALL dimensions:
genuine big nef Cartier terms, original decreasing order and original topology
limit. No model countability, tower, chosen approximations or output certificate. -/
theorem source_nef_Cartierseq (ω : KahlerBackground n X)
    (D : WeilFamilyAny (ModelSystem.blowup n X)) (hD : IsNefAny D) :
    ∃ F : ℕ → WeilFamilyAny (ModelSystem.blowup n X),
      (∀ i, IsNefCartierAny (F i) ∧ 0 < volumeAny (F i)) ∧
      (∀ i j : ℕ, i ≤ j → LEAny (F j) (F i)) ∧ ConvergesAny atTop F D := by
  cases n with
  | zero =>
    refine ⟨fun _ => D,fun _ => ⟨isNefCartierAny_zero D,?_⟩,?_,?_⟩
    · rw [volumeAny_eq_one_of_dim_zero]
      exact zero_lt_one
    · intro _ _ _ π
      exact classPseudoeffective_of_dim_zero _
    · intro π
      let : TopologicalSpace (RealBottChern 0 π.1.carrier) := euclideanTopology _
      exact tendsto_const_nhds
  | succ m => exact exists_decreasing_big_nefCartier_sequence_pos ω D hD

end SGPT.Hodge.BDivChain.SourceCartierSequenceDraft
