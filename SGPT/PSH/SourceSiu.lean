import SGPT.PSH.VariableLelong
import SGPT.PSH.GrauertRemmertBounded
import SGPT.Okounkov.LocalLelong
import SGPT.Foundations.Analysis.Pending.RawQuasiPshLelongSuperlevels
import SGPT.Foundations.Analysis.Pending.LelongNumberFiniteness
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SquaredLogLelongSourceNormalization
open scoped Topology ENNReal

variable {X : Type*} [TopologicalSpace X] (A : VariableComplexAtlas X)

private theorem locallyNondegenerate_coordinate_opens {u : X → EReal}
    (hu : A.IsPSH u) (i : A.Index) :
    let Ω : Opens (ComplexModel (A.dimension i)) :=
      ⟨(A.chart i).target, (A.chart i).open_target⟩
    LocallyNondegenerate (fun y : Ω => A.coordinate u i y) := by
  intro Ω x U hU hx
  have hO : IsOpen ((Subtype.val : Ω → ComplexModel (A.dimension i)) '' U) :=
    Ω.isOpen.isOpenMap_subtype_val U hU
  have hOt : ((Subtype.val : Ω → ComplexModel (A.dimension i)) '' U) ⊆
      (A.chart i).target := by rintro _ ⟨y, _, rfl⟩; exact y.2
  obtain ⟨y, hy, hfin⟩ := LocallyNondegenerate.exists_coordinate_ne_bot
    hu.locallyNondegenerate (A.chart i) hO hOt ⟨x, hx, rfl⟩
  obtain ⟨z, hz, rfl⟩ := hy
  exact ⟨z, hz, hfin⟩

/-- Original PSH and actual open charts produce finite source readers. -/
theorem sourceLelong_ne_top {u : X → EReal} (hu : A.IsPSH u) (x : X) :
    A.sourceLelong u x ≠ ⊤ := by
  obtain ⟨i, hi⟩ := A.cover x
  rw [A.sourceLelong_eq_chart u x i hi]
  by_cases hn : A.dimension i = 0
  · simp only [squaredLogLelongNumber, hn, ite_true]
    exact ENNReal.zero_ne_top
  let Ω : Opens (ComplexModel (A.dimension i)) :=
    ⟨(A.chart i).target, (A.chart i).open_target⟩
  let z : Ω := ⟨A.chart i x, (A.chart i).map_source hi⟩
  have hq := SGPT.Okounkov.manifoldQuasiPlurisubharmonic_opens_restrict
    (Ω := Ω) (fun y hy => (hu.chartPlurisubharmonic i y hy).quasiPlurisubharmonicAt)
  have hfinite := LelongNumberFiniteness.lelongNumber_ne_top_of_quasiPsh
    (Nat.pos_of_ne_zero hn) hq (locallyNondegenerate_coordinate_opens A hu i) z
  rw [SGPT.Okounkov.lelongNumber_opens_restrict] at hfinite
  intro htop
  exact hfinite (by rw [lelongNumber_eq_two_mul_squaredLog hn, htop]; simp)

/-- Literal finite holomorphic equations for every original source superlevel. -/
theorem sourceLelong_superlevel_hasAnalyticChartEquations {u : X → EReal}
    (hu : A.IsPSH u) (a : ℝ≥0∞) :
    A.HasAnalyticChartEquations {x : X | a ≤ A.sourceLelong u x} := by
  classical
  intro i z hz
  by_cases ha : a = ⊤
  · refine ⟨(A.chart i).target, (A.chart i).open_target, hz, subset_rfl,
      1, fun _ _ => 1, fun _ => differentiableOn_const 1, ?_⟩
    intro y _hy
    simp only [mem_ofPred_eq, ha, top_le_iff]
    constructor
    · intro h
      exact False.elim (A.sourceLelong_ne_top hu _ h)
    · intro h
      exact False.elim (one_ne_zero (h 0))
  by_cases hn : A.dimension i = 0
  · by_cases ha0 : a = 0
    · refine ⟨(A.chart i).target, (A.chart i).open_target, hz, subset_rfl,
        0, fun j => Fin.elim0 j, fun j => Fin.elim0 j, ?_⟩
      intro y _hy
      simp only [mem_ofPred_eq, ha0, zero_le, Fin.forall_fin_zero]
    · refine ⟨(A.chart i).target, (A.chart i).open_target, hz, subset_rfl,
        1, fun _ _ => 1, fun _ => differentiableOn_const 1, ?_⟩
      intro y hy
      have hzero : A.sourceLelong u ((A.chart i).symm y) = 0 := by
        rw [A.sourceLelong_eq_chart u _ i ((A.chart i).map_target hy)]
        simp only [squaredLogLelongNumber, hn, ite_true]
      simp only [mem_ofPred_eq, hzero, nonpos_iff_eq_zero]
      constructor
      · intro h
        exact False.elim (ha0 h)
      · intro h
        exact False.elim (one_ne_zero (h 0))
  let Ω : Opens (ComplexModel (A.dimension i)) :=
    ⟨(A.chart i).target, (A.chart i).open_target⟩
  let zz : Ω := ⟨z, hz⟩
  let v : Ω → EReal := fun y => A.coordinate u i y
  have hq : ManifoldQuasiPlurisubharmonic (n := A.dimension i) v :=
    SGPT.Okounkov.manifoldQuasiPlurisubharmonic_opens_restrict
      (fun y hy => (hu.chartPlurisubharmonic i y hy).quasiPlurisubharmonicAt)
  let P := (RawQuasiPshLelongSuperlevels.isComplexAnalyticSubset_superlevel
    hq (2 * a.toReal) zz).some
  let e := complexChartAt (n := A.dimension i) zz
  have hc (y : Ω) : e.val y = (y : ComplexModel (A.dimension i)) := rfl
  have hWt : P.coordinateNeighborhood ⊆ (A.chart i).target := by
    intro y hy
    have ht := P.coordinateNeighborhood_subset_target hy
    have hr : (e.val.symm y : ComplexModel (A.dimension i)) = y := by
      exact e.val.right_inv ht
    exact hr ▸ (e.val.symm y).2
  refine ⟨P.coordinateNeighborhood, P.isOpen_coordinateNeighborhood,
    P.center_mem_coordinateNeighborhood, hWt, P.generatorCount,
    P.generator, P.generator_holomorphic, ?_⟩
  intro y hy
  let yy : Ω := ⟨y, hWt hy⟩
  have hys : yy ∈ e.val.source := by
    change yy ∈ (chartAt (ComplexModel (A.dimension i)) zz).source
    apply AnalyticSubsetOpens.mem_chartAt_opens_source.mpr
    rw [chartAt_self_eq]
    trivial
  have he := P.zeroLocus hys hy
  change (ENNReal.ofReal (2 * a.toReal) ≤ lelongNumber (n := A.dimension i) v yy) ↔
    ∀ j, P.generator j y = 0 at he
  have hnative : lelongNumber (n := A.dimension i) v yy =
      2 * A.sourceLelong u ((A.chart i).symm y) := by
    rw [SGPT.Okounkov.lelongNumber_opens_restrict,
      lelongNumber_eq_two_mul_squaredLog hn,
      A.sourceLelong_eq_chart u _ i ((A.chart i).map_target (hWt hy)),
      (A.chart i).right_inv (hWt hy)]
  change (a ≤ A.sourceLelong u ((A.chart i).symm y)) ↔ _
  have htwice : ENNReal.ofReal (2 * a.toReal) = 2 * a := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_toReal ha]
    norm_num
  simpa only [hnative, htwice,
    mul_comm (2 : ℝ≥0∞),
    ENNReal.mul_le_mul_iff_left (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)] using he

/-- The usual analytic Zariski construction on the same original manifold. -/
@[instance_reducible]
def analyticZariskiTopology : TopologicalSpace X :=
  TopologicalSpace.generateFrom {U : Set X | A.HasAnalyticChartEquations Uᶜ}

/-- Each actual analytic set is closed in the analytic Zariski topology. -/
theorem HasAnalyticChartEquations.isClosed_analyticZariski {Z : Set X}
    (hZ : A.HasAnalyticChartEquations Z) :
    @IsClosed X A.analyticZariskiTopology Z := by
  apply (@isOpen_compl_iff X Z A.analyticZariskiTopology).mp
  exact TopologicalSpace.isOpen_generateFrom_of_mem
    (by simpa only [mem_ofPred_eq, compl_compl] using hZ)

/-- Whole original Siu semicontinuity, including varying dimension and poles. -/
theorem sourceLelong_upperSemicontinuous_analyticZariski {u : X → EReal}
    (hu : A.IsPSH u) :
    @UpperSemicontinuous X ℝ≥0∞ A.analyticZariskiTopology _ (A.sourceLelong u) := by
  apply (@upperSemicontinuous_iff_isClosed_preimage X A.analyticZariskiTopology
    ℝ≥0∞ _ (A.sourceLelong u)).mpr
  intro a
  exact (A.sourceLelong_superlevel_hasAnalyticChartEquations hu a).isClosed_analyticZariski A

end SGPT.PSH.VariableComplexAtlas
