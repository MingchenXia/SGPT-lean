import SGPT.PSH.NadelCoherence
import SGPT.Foundations.Analysis.Pending.MultiplierSubadditivityLocal
import SGPT.Foundations.Analysis.Pending.DemaillyApproximationAnalyticType

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending MultiplierIdealBergmanNadelIdeal

/-- Actual DEL subadditivity for two independent original PSH weights on
an original model domain, including dimension zero. -/
theorem multiplierIntegrableAt_sum_in_product_germ
    {n : ℕ} {W : Set (ComplexModel n)} (hW : IsOpen W)
    {u v : ComplexModel n → EReal} (hu : PSHOn u W) (hv : PSHOn v W)
    {z : ComplexModel n} (hz : z ∈ W) {f : ComplexModel n → ℂ}
    (hf : MultiplierIntegrableAt (fun y => u y + v y) 1 f z volume) :
    InGermSpan {g | ∃ a b, MultiplierIntegrableAt u 1 a z volume ∧
      MultiplierIntegrableAt v 1 b z volume ∧ g = fun y => a y * b y} z f := by
  cases n with
  | zero =>
    refine ⟨1, fun _ => f, fun _ _ => 1, ?_,
      fun _ => Eventually.of_forall fun _ => differentiableAt_const _,
      Eventually.of_forall fun _ => by simp⟩
    intro _
    refine ⟨f, fun _ => 1, multiplierIntegrableAt_zero_of_pshOn hu hz one_pos f,
      multiplierIntegrableAt_zero_of_pshOn hv hz one_pos _, ?_⟩
    funext y
    simp
  | succ m =>
    exact MultiplierSubadditivityLocal.inGermSpan_mul_of_multiplierIntegrableAt hW
      (hu.disc.plurisubharmonicOn hW) (hv.disc.plurisubharmonicOn hW) hz hf

/-- Whole original multiplier-ideal subadditivity for independent weights,
with actual finite holomorphic coefficients and the native ideal product. -/
theorem ManifoldPSH.multiplierIdeal_sum_le_mul
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {u v : M → EReal} (hu : ManifoldPSH (n := n) u) (hv : ManifoldPSH (n := n) v) :
    (multiplierIdeal (n := n) 1 (fun y => u y + v y)).Le
      ((multiplierIdeal (n := n) 1 u).mul (multiplierIdeal (n := n) 1 v)) := by
  intro x f hf
  cases n with
  | zero =>
    have hfU := (ZeroDimensionalQuasiPshMultiplierIdeals.mem_multiplierIdeal_iff_holomorphicAt
      hu.isThetaPshPotential_zero.quasiPshPotential one_pos x f).mpr hf.1
    have h1V := (ZeroDimensionalQuasiPshMultiplierIdeals.mem_multiplierIdeal_iff_holomorphicAt
      hv.isThetaPshPotential_zero.quasiPshPotential one_pos x (fun _ => 1)).mpr
        (holomorphicAt_const 1)
    refine ⟨hf.1, 1, fun _ => f, fun _ _ => 1, ?_,
      fun _ => holomorphicAt_const 1, Eventually.of_forall fun _ => by simp⟩
    intro _
    refine ⟨f, fun _ => 1, hfU, h1V, ?_⟩
    funext y
    simp
  | succ m =>
    let e : ComplexChart (m + 1) M := complexChartAt x
    have hx : x ∈ e.val.source := mem_complexChartAt_source x
    have hz := e.val.map_source hx
    have hsum : MultiplierIntegrableAt
        (fun z => chartFunction u e z + chartFunction v e z) 1
        (fun z => f (e.val.symm z)) (e.val x) volume := hf.2
    obtain ⟨N, s, a, hs, ha, heq⟩ :=
      MultiplierSubadditivityLocal.inGermSpan_mul_of_multiplierIntegrableAt e.val.open_target
        (hu.chartPlurisubharmonic e) (hv.chartPlurisubharmonic e) hz hsum
    choose p q hp hq hsp using hs
    have hp' (i : Fin N) : (multiplierIdeal (n := m + 1) 1 u).mem x
        (fun y => p i (e.val y)) :=
      DemaillyApproximationAnalyticType.mem_multiplierIdeal_of_chart
        hu.isThetaPshPotential_zero.1 one_pos e e.val.open_target
        (ρ := fun _ => 0) continuousOn_const hx hz (by simpa using hp i)
    have hq' (i : Fin N) : (multiplierIdeal (n := m + 1) 1 v).mem x
        (fun y => q i (e.val y)) :=
      DemaillyApproximationAnalyticType.mem_multiplierIdeal_of_chart
        hv.isThetaPshPotential_zero.1 one_pos e e.val.open_target
        (ρ := fun _ => 0) continuousOn_const hx hz (by simpa using hq i)
    refine ⟨hf.1, N, fun i y => p i (e.val y) * q i (e.val y),
      fun i y => a i (e.val y),
      fun i => ⟨_, _, hp' i, hq' i, rfl⟩,
      fun i => DemaillyApproximationAnalyticType.holomorphicAt_comp_atlas hx (ha i), ?_⟩
    filter_upwards [e.val.open_source.mem_nhds hx, (e.val.continuousAt hx).eventually heq]
      with y hy heqy
    rw [e.val.left_inv hy] at heqy
    rw [heqy]
    exact Finset.sum_congr rfl fun i _ => by rw [hsp i]

/-- Every actual chart of the source variable-dimensional manifold has
subadditivity for all its original holomorphic multiplier germs. -/
theorem VariableComplexAtlas.IsPSH.multiplierIntegrableAt_sum_in_product_germ
    {X : Type*} [TopologicalSpace X] {A : VariableComplexAtlas X}
    {u v : X → EReal} (hu : A.IsPSH u) (hv : A.IsPSH v) (i : A.Index)
    {x : X} (hx : x ∈ (A.chart i).source)
    {f : ComplexModel (A.dimension i) → ℂ}
    (hf : MultiplierIntegrableAt (fun y => A.coordinate u i y + A.coordinate v i y) 1
      f (A.chart i x) volume) :
    InGermSpan {g | ∃ a b,
      MultiplierIntegrableAt (A.coordinate u i) 1 a (A.chart i x) volume ∧
      MultiplierIntegrableAt (A.coordinate v i) 1 b (A.chart i x) volume ∧
      g = fun y => a y * b y} (A.chart i x) f := by
  have hz := (A.chart i).map_source hx
  have hpU : PSHOn (A.coordinate u i) (A.chart i).target :=
    ⟨(hu.chartPlurisubharmonic i).discPshOn,
      LocallyNondegenerate.exists_coordinate_ne_bot hu.locallyNondegenerate
        (A.chart i) (A.chart i).open_target subset_rfl hz⟩
  have hpV : PSHOn (A.coordinate v i) (A.chart i).target :=
    ⟨(hv.chartPlurisubharmonic i).discPshOn,
      LocallyNondegenerate.exists_coordinate_ne_bot hv.locallyNondegenerate
        (A.chart i) (A.chart i).open_target subset_rfl hz⟩
  exact SGPT.PSH.multiplierIntegrableAt_sum_in_product_germ (A.chart i).open_target
    hpU hpV hz hf

end SGPT.PSH
