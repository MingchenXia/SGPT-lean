import SGPT.Hodge.SourceEventualCartierUpper

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
  SGPT.Hodge.BDivChain.SourceNefIntersectionDraft SGPT.Hodge.BDivChain.SourceCartierSequenceDraft

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
local notation "Sys" => ModelSystem.blowup (m+1) X

theorem nefIntersection_le_of_nefCartier (ω : KahlerBackground (m+1) X)
    (D E : Fin (m+1) → WeilFamilyAny Sys)
    (hD : ∀ i,IsNefCartierAny (D i)) (hE : ∀ i,IsNefCartierAny (E i))
    (hDE : ∀ i,LEAny (D i) (E i)) : nefIntersection D≤nefIntersection E := by
  exact (ENNReal.toReal_le_toReal (nefIntersection_lt_top D).ne (nefIntersection_lt_top E).ne).mp
    (nefIntersection_mono_of_nefCartier ω D E hD hE hDE)

/-- Original modelwise order against arbitrary nef Cartier upper tuples.
The approximating currents, common realization, eventual GLOBAL upper and
both actual limits are internally produced from the original nef input. -/
theorem nefIntersection_le_of_cartier_upper (ω : KahlerBackground (m+1) X)
    (D E : Fin (m+1) → WeilFamilyAny Sys) (hD : ∀ i,IsNefAny (D i))
    (hE : ∀ i,IsNefCartierAny (E i)) (hDE : ∀ i,LEAny (D i) (E i)) :
    nefIntersection D≤nefIntersection E := by
  classical
  choose A hA ha hc using fun i => exists_decreasing_big_nefCartier_sequence_pos ω (D i) (hD i)
  let B (i : Fin (m+1)) (j : ℕ) : BigNefFamily (n := m+1) (X := X) :=
    ⟨A i j,(hA i j).2,isNefAny_of_isNefCartierAny (hA i j).1⟩
  obtain ⟨π,κ,θ,hr,hnef⟩ := exists_common_nef_realization ω E hE
  let α i := RealBottChern.ofRepresentative (θ i)
  have hα i : ClassNefWithRespectTo κ (α i) := hnef i
  have hEeq i : E i=modelCartier π (α i) := modelCartier_eq_of_realization (hr i)
  have htrace i : ClassPseudoeffectiveViaPotentials (α i-(D i).val π) := by
    have hp := hDE i π
    rw [hEeq i,modelCartier_self] at hp
    exact hp
  let U (ε : ℝ) (i : Fin (m+1)) :=
    modelCartier π (α i+ε • RealBottChern.ofRepresentative κ.form)
  have hU (ε : ℝ) (hε : 0≤ε) (i) : IsNefCartierAny (U ε i) :=
    modelCartier_shift_isNefCartier π κ (hα i) hε
  have hlimA := (source_DFdecnet ω A D
    (fun i j => isNefAny_of_isNefCartierAny (hA i j).1) ha hc).2
  have hεbound (ε : ℝ) (hε : 0<ε) : nefIntersection D≤nefIntersection (U ε) := by
    have hevent i := eventually_bigNef_le_modelCartier ω (B i) (D i) (hc i) π κ (α i)
      (htrace i) hε
    apply le_of_tendsto_of_tendsto hlimA tendsto_const_nhds
    filter_upwards [eventually_all.mpr hevent] with j hj
    exact nefIntersection_le_of_nefCartier ω (fun i => A i j) (U ε)
      (fun i => (hA i j).1) (hU ε hε.le) hj
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
  have hlimU := (source_DFdecnet ω (fun i j => U (c j) i) E
    (fun i j => isNefAny_of_isNefCartierAny (hU (c j) (hcpos j).le i))
    (fun i j k hjk => modelCartier_shift_antitone π κ (α i) (hcanti hjk)) hconv).2
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlimU (fun j => hεbound (c j) (hcpos j))

/-- Genuine different-root, all-slot monotonicity on the complete original
nef cone. Both Cartier sequences and every global comparison are produced
internally; the only order input is the literal original modelwise order. -/
theorem nefIntersection_mono_pos (ω : KahlerBackground (m+1) X)
    (D E : Fin (m+1) → WeilFamilyAny Sys)
    (hD : ∀ i,IsNefAny (D i)) (hE : ∀ i,IsNefAny (E i))
    (hDE : ∀ i,LEAny (D i) (E i)) : nefIntersection D≤nefIntersection E := by
  classical
  choose A hA ha hc using fun i => exists_decreasing_big_nefCartier_sequence_pos ω (E i) (hE i)
  have hbound j : nefIntersection D≤nefIntersection (fun i => A i j) := by
    apply nefIntersection_le_of_cartier_upper ω D (fun i => A i j) hD (fun i => (hA i j).1)
    intro i
    exact leAny_trans (hDE i) (leAny_of_antitone_converges ω (A i) (E i) (ha i) (hc i) j)
  have hlim := (source_DFdecnet ω A E
    (fun i j => isNefAny_of_isNefCartierAny (hA i j).1) ha hc).2
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hbound

end SGPT.Hodge.BDivChain.SourceMixedOrderDraft

namespace SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
  SGPT.Hodge.BDivChain.SourceNefIntersectionDraft
  SGPT.Hodge.BDivChain.SourceIntersection

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Original arbitrary-root mixed monotonicity on every genuine nef tuple,
including the actual empty intersection1 in dimension zero. -/
theorem source_nefIntersection_mono (ω : KahlerBackground n X)
    (D E : Fin n → WeilFamilyAny (ModelSystem.blowup n X))
    (hD : ∀ i,IsNefAny (D i)) (hE : ∀ i,IsNefAny (E i))
    (hDE : ∀ i,LEAny (D i) (E i)) : nefIntersection D≤nefIntersection E := by
  cases n with
  | zero =>
    rw [source_nefIntersection_dim_zero D,source_nefIntersection_dim_zero E]
  | succ m => exact nefIntersection_mono_pos ω D E hD hE hDE

/-- Exact original fourth clause of lma:DFlinear, all actual original big
nef families, arbitrary root classes, and original modelwise order only. -/
theorem source_DFlinear_mono (ω : KahlerBackground n X)
    (D E : Fin n → BigNefFamily (n := n) (X := X))
    (hDE : ∀ i,LEAny (D i).val (E i).val) :
    bigNefIntersection ω D≤bigNefIntersection ω E := by
  rw [←nefIntersection_eq_bigNefIntersection ω D,←nefIntersection_eq_bigNefIntersection ω E]
  exact source_nefIntersection_mono ω (fun i => (D i).val) (fun i => (E i).val)
    (fun i => (D i).property.2) (fun i => (E i).property.2) hDE

end SGPT.Hodge.BDivChain.SourceMixedOrderDraft
