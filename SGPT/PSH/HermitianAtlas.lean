import SGPT.PSH.VariableAtlas
import SGPT.PSH.HermitianPSH
import SGPT.Foundations.Analysis.FirstPass.HolomorphicContDiff

/-!
# FPT local quasi-PSH in the original variable-dimensional atlas

The local PSH-plus-smooth definition is independent of any global closed
background. Local nondegeneracy is retained explicitly, so a whole open
component cannot be identically negative infinity. The existing closed
background `IsQPSH` predicate keeps its original meaning in its own module.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {X : Type*} [TopologicalSpace X] (A : VariableComplexAtlas X)

/-- FPT quasi-PSH: genuine local PSH-plus-smooth germs and a dense finite
locus. No closedness or global potential is part of the definition. -/
def IsLocalQPSH (u : X → EReal) : Prop :=
  (∀ i, QuasiPlurisubharmonicOn (A.coordinate u i) (A.chart i).target) ∧
    LocallyNondegenerate u

/-- Local PSH-plus-smooth germs transport through the actual holomorphic
coordinate changes, including charts of different model dimensions. -/
theorem localQuasiPsh_germ_iff (u : X → EReal) (i j : A.Index) (x : X)
    (hi : x ∈ (A.chart i).source) (hj : x ∈ (A.chart j).source) :
    QuasiPlurisubharmonicAt (A.coordinate u i) (A.chart i x) ↔
      QuasiPlurisubharmonicAt (A.coordinate u j) (A.chart j x) := by
  have transport (a b : A.Index) (ha : x ∈ (A.chart a).source)
      (hb : x ∈ (A.chart b).source)
      (hu : QuasiPlurisubharmonicAt (A.coordinate u a) (A.chart a x)) :
      QuasiPlurisubharmonicAt (A.coordinate u b) (A.chart b x) := by
    let F := (A.chart b).symm.trans (A.chart a)
    have hx : A.chart b x ∈ F.source := by
      refine ⟨(A.chart b).map_source hb, ?_⟩
      change (A.chart b).symm (A.chart b x) ∈ (A.chart a).source
      simpa only [(A.chart b).left_inv hb] using ha
    have huF : QuasiPlurisubharmonicAt (A.coordinate u a) (F (A.chart b x)) := by
      simpa only [F, OpenPartialHomeomorph.trans_apply, (A.chart b).left_inv hb] using hu
    have hp := SGPT.Foundations.Analysis.Pending.HolomorphicPullback.quasiPlurisubharmonicAt_comp_holomorphic
      F.open_source (contDiffOn_of_differentiableOn_complex (A.holomorphic b a) F.open_source) hx huF
    apply hp.congr
    filter_upwards [F.open_source.mem_nhds hx] with y hy
    exact congrArg u ((A.chart a).left_inv hy.2)
  exact ⟨transport i j hi hj, transport j i hj hi⟩

/-- It suffices to exhibit a genuine local decomposition in one chart
about each point. Chart independence is proved, rather than an input. -/
theorem isLocalQPSH_iff_local_germs (u : X → EReal) :
    A.IsLocalQPSH u ↔
      (∀ x, ∃ i : A.Index, x ∈ (A.chart i).source ∧
        QuasiPlurisubharmonicAt (A.coordinate u i) (A.chart i x)) ∧
      LocallyNondegenerate u := by
  constructor
  · rintro ⟨hu, hnd⟩
    refine ⟨fun x => ?_, hnd⟩
    obtain ⟨i, hi⟩ := A.cover x
    exact ⟨i, hi, hu i (A.chart i x) ((A.chart i).map_source hi)⟩
  · rintro ⟨hu, hnd⟩
    refine ⟨fun j z hz => ?_, hnd⟩
    obtain ⟨i, hi, hui⟩ := hu ((A.chart j).symm z)
    have h := (A.localQuasiPsh_germ_iff u i j _ hi ((A.chart j).map_target hz)).mp hui
    simpa only [(A.chart j).right_inv hz] using h

/-- FPT local quasi-PSH never takes the excluded value positive infinity. -/
theorem IsLocalQPSH.ne_top {u : X → EReal} (hu : A.IsLocalQPSH u) (x : X) : u x ≠ ⊤ := by
  obtain ⟨i, hi⟩ := A.cover x
  have h := (hu.1 i _ ((A.chart i).map_source hi)).ne_top
  simpa only [coordinate, Function.comp_apply, (A.chart i).left_inv hi] using h

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The original fixed-model atlas reads back the actual native local
quasi-PSH predicate, including exactly its local nondegeneracy. -/
theorem ofFixedModel_isLocalQPSH_iff (u : M → EReal) :
    (ofFixedModel n M).IsLocalQPSH u ↔ IsGlobalQuasiPshPotential (n := n) u := Iff.rfl

/-- The genuine nonclosed current domain gives the corrected source/FPT
local quasi-PSH predicate on the original atlas. -/
theorem isLocalQPSH_of_isHermitianPSH {m : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (ComplexModel (m+1)) N] [IsComplexManifold (m+1) N]
    {omega : SGPT.PSH.Hermitian.Background (m+1) N} {u : N → EReal}
    (hu : SGPT.PSH.Hermitian.IsHermitianPSH omega u) :
    (ofFixedModel (m+1) N).IsLocalQPSH u := hu.quasiPshPotential

end SGPT.PSH.VariableComplexAtlas
