import SGPT.Hodge.SourceMixedLinearity
import Mathlib.Order.LiminfLimsup

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceRemainingIntersectionDraft
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
  SGPT.Hodge.BDivChain.SourceIntersection SGPT.Hodge.BDivChain.SourceNefIntersectionDraft
  SGPT.Hodge.BDivChain.SourceMixedOrderDraft SGPT.Hodge.BDivChain.SourceCartierSequenceDraft
  SGPT.Hodge.BDivChain.SourceNefProjectiveDraft
variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
local notation "Sys" => ModelSystem.blowup (m+1) X

/-- Original converging big-nef nets have the genuine mixed-intersection
limsup bound against any actual nef Cartier upper of their limit. -/
theorem bigNef_limsup_le_cartier_upper (ω : KahlerBackground (m+1) X)
    {J : Type*} {l : Filter J} [l.NeBot]
    (A : Fin (m+1) → J → BigNefFamily (n := m+1) (X := X))
    (D E : Fin (m+1) → WeilFamilyAny Sys)
    (hc : ∀ i,ConvergesAny l (fun j => (A i j).val) (D i))
    (hE : ∀ i,IsNefCartierAny (E i)) (hDE : ∀ i,LEAny (D i) (E i)) :
    limsup (fun j => nefIntersection (fun i => (A i j).val)) l≤nefIntersection E := by
  classical
  obtain ⟨π,κ,θ,hr,hnef⟩ := exists_common_nef_realization ω E hE
  let α i := RealBottChern.ofRepresentative (θ i)
  have hα i : ClassNefWithRespectTo κ (α i) := hnef i
  have hEeq i : E i=modelCartier π (α i) := modelCartier_eq_of_realization (hr i)
  have htrace i : ClassPseudoeffectiveViaPotentials (α i-(D i).val π) := by
    have hp := hDE i π
    rw [hEeq i,modelCartier_self] at hp
    exact hp
  let U (ε : ℝ) (i : Fin (m+1)) := modelCartier π (α i+ε • RealBottChern.ofRepresentative κ.form)
  have hU (ε : ℝ) (hε : 0≤ε) (i) : IsNefCartierAny (U ε i) :=
    modelCartier_shift_isNefCartier π κ (hα i) hε
  have hbound (ε : ℝ) (hε : 0<ε) :
      limsup (fun j => nefIntersection (fun i => (A i j).val)) l≤nefIntersection (U ε) := by
    have hevent i := eventually_bigNef_le_modelCartier ω (A i) (D i) (hc i) π κ (α i) (htrace i) hε
    have hb : ∀ᶠ j in l,nefIntersection (fun i => (A i j).val)≤nefIntersection (U ε) := by
      filter_upwards [eventually_all.mpr hevent] with j hj
      exact source_nefIntersection_mono ω (fun i => (A i j).val) (U ε)
        (fun i => (A i j).property.2) (fun i => isNefAny_of_isNefCartierAny (hU ε hε.le i)) hj
    exact limsup_le_of_le (h := hb)
  let c : ℕ → ℝ := fun j => 1/((j : ℝ)+1)
  have hcpos j : 0<c j := by dsimp [c]; positivity
  have hcanti : Antitone c := by
    intro i j hij
    dsimp [c]
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hc0 : Tendsto c atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hconv i : ConvergesAny atTop (fun j => U (c j) i) (E i) := by
    rw [hEeq i]
    exact modelCartier_shift_converges π κ (α i) hc0
  have hlim := (source_DFdecnet ω (fun i j => U (c j) i) E
    (fun i j => isNefAny_of_isNefCartierAny (hU (c j) (hcpos j).le i))
    (fun i j k hjk => modelCartier_shift_antitone π κ (α i) (hcanti hjk)) hconv).2
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim (fun j => hbound (c j) (hcpos j))

/-- Big input nets need no nef Cartier limit or supplied approximation:
all original Cartier uppers are produced internally from the actual nef limit. -/
theorem bigNef_limsup_le_nef_limit (ω : KahlerBackground (m+1) X)
    {J : Type*} {l : Filter J} [l.NeBot]
    (A : Fin (m+1) → J → BigNefFamily (n := m+1) (X := X))
    (D : Fin (m+1) → WeilFamilyAny Sys) (hD : ∀ i,IsNefAny (D i))
    (hc : ∀ i,ConvergesAny l (fun j => (A i j).val) (D i)) :
    limsup (fun j => nefIntersection (fun i => (A i j).val)) l≤nefIntersection D := by
  classical
  choose E hE ha he using fun i => exists_decreasing_big_nefCartier_sequence_pos ω (D i) (hD i)
  have hbound k := bigNef_limsup_le_cartier_upper ω A D (fun i => E i k) hc
    (fun i => (hE i k).1)
    (fun i => leAny_of_antitone_converges ω (E i) (D i) (ha i) (he i) k)
  have hlim := (source_DFdecnet ω E D
    (fun i k => isNefAny_of_isNefCartierAny (hE i k).1) ha he).2
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hbound

/-- Genuine arbitrary-filter upper semicontinuity on the whole original nef cone,
with no positive-volume, fixed-root or supplied uniform-bound assumption. -/
theorem nefIntersection_limsup_le_pos (ω : KahlerBackground (m+1) X)
    {J : Type*} {l : Filter J} [l.NeBot]
    (D : Fin (m+1) → J → WeilFamilyAny Sys) (E : Fin (m+1) → WeilFamilyAny Sys)
    (hD : ∀ i j,IsNefAny (D i j)) (hE : ∀ i,IsNefAny (E i))
    (hc : ∀ i,ConvergesAny l (D i) (E i)) :
    limsup (fun j => nefIntersection (fun i => D i j)) l≤nefIntersection E := by
  let C := rootCartierAny (RealBottChern.ofRepresentative ω.form)
  have hC : IsPseudoeffectiveAny C := rootKahler_pseudoeffective ω
  have hbound (ε : Ioi (0 : ℝ)) :
      limsup (fun j => nefIntersection (fun i => D i j)) l≤
        bigNefIntersection ω (fun i => kahlerPerturbedBigNef ω ω (E i) (hE i) ε.val ε.property) := by
    let A : Fin (m+1) → J → BigNefFamily (n := m+1) (X := X) :=
      fun i j => kahlerPerturbedBigNef ω ω (D i j) (hD i j) ε.val ε.property
    let B : Fin (m+1) → BigNefFamily (n := m+1) (X := X) :=
      fun i => kahlerPerturbedBigNef ω ω (E i) (hE i) ε.val ε.property
    have hconst : ConvergesAny l (fun _ : J => ε.val • C) (ε.val • C) := by
      intro π
      let : TopologicalSpace (RealBottChern (m+1) π.1.carrier) := euclideanTopology _
      exact tendsto_const_nhds
    have hconv i : ConvergesAny l (fun j => (A i j).val) (B i).val :=
      convergesAny_add (hc i) hconst
    have horder (i) (j) : LEAny (D i j) (A i j).val := by
      intro π
      have hp := SGPT.Okounkov.TranscendentalVolumeConcavity.classPseudoeffective_smul
        (hC π) ε.property.le
      change ClassPseudoeffectiveViaPotentials
        (((D i j).val π+ε.val • C.val π)-(D i j).val π)
      convert hp using 1; module
    have hm : limsup (fun j => nefIntersection (fun i => D i j)) l≤
        limsup (fun j => nefIntersection (fun i => (A i j).val)) l := by
      exact limsup_le_limsup (Eventually.of_forall fun j => source_nefIntersection_mono ω _ _
        (fun i => hD i j) (fun i => (A i j).property.2) (fun i => horder i j))
    have hb := hm.trans (bigNef_limsup_le_nef_limit ω A (fun i => (B i).val)
      (fun i => (B i).property.2) hconv)
    rw [nefIntersection_eq_bigNefIntersection ω B] at hb
    exact hb
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds (source_DFext_limit ω ω E hE) hbound

end SGPT.Hodge.BDivChain.SourceRemainingIntersectionDraft
