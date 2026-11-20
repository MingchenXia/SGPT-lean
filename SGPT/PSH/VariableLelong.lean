import SGPT.PSH.ChartNullTransport
import SGPT.Foundations.Analysis.Pending.LocalHolomorphicLelongReaderCovariance
import SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization
import SGPT.Foundations.Analysis.Pending.ActualLelongPositiveScaling
import Mathlib.Topology.LocallyConstant.Basic

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SquaredLogLelongSourceNormalization
open scoped Topology ENNReal NNReal

/-- Source germ invariance reuses the genuine independently defined
squared-log normalization and actual native germ covariance. -/
theorem squaredLogLelongNumber_congr {n : ℕ} {u v : ComplexModel n → EReal}
    {x : ComplexModel n} (h : u =ᶠ[𝓝 x] v) :
    squaredLogLelongNumber (n := n) u x = squaredLogLelongNumber (n := n) v x := by
  by_cases hn : n = 0
  · simp [squaredLogLelongNumber, hn]
  apply (ENNReal.mul_right_inj (a := 2) (by norm_num) (by norm_num)).mp
  rw [← lelongNumber_eq_two_mul_squaredLog hn,
    ← lelongNumber_eq_two_mul_squaredLog hn]
  exact LelongNumberComparison.lelongNumber_congr h

/-- Whole actual local holomorphic-inverse covariance retains the
source's explicit zero-dimensional convention and squared norm. -/
theorem squaredLogLelongNumber_comp_inv_eq {n : ℕ} {p x : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) p) (hx : x ∈ Φ.source)
    (u : ComplexModel n → EReal) :
    squaredLogLelongNumber (n := n) (fun z => u (Φ.invFun z)) (Φ.toFun x) =
      squaredLogLelongNumber (n := n) u x := by
  by_cases hn : n = 0
  · simp [squaredLogLelongNumber, hn]
  apply (ENNReal.mul_right_inj (a := 2) (by norm_num) (by norm_num)).mp
  rw [← lelongNumber_eq_two_mul_squaredLog hn,
    ← lelongNumber_eq_two_mul_squaredLog hn]
  exact LocalHolomorphicLelongReaderCovariance.lelongNumber_comp_inv_eq Φ hx

/-- Actual chart transitions, with possibly distinct model dimensions,
produce equality of the original squared-log readers. -/
theorem squaredLogLelongNumber_chart_eq {X : Type*} [TopologicalSpace X]
    {d e : ℕ} (ei : OpenPartialHomeomorph X (ComplexModel d))
    (ej : OpenPartialHomeomorph X (ComplexModel e))
    (hF : DifferentiableOn ℂ (ei.symm.trans ej) (ei.symm.trans ej).source)
    (hG : DifferentiableOn ℂ (ej.symm.trans ei) (ej.symm.trans ei).source)
    (u : X → EReal) {x : X} (hi : x ∈ ei.source) (hj : x ∈ ej.source) :
    squaredLogLelongNumber (n := d) (u ∘ ei.symm) (ei x) =
      squaredLogLelongNumber (n := e) (u ∘ ej.symm) (ej x) := by
  have hx : ei x ∈ (ei.symm.trans ej).source := by
    refine ⟨ei.map_source hi, ?_⟩
    change ei.symm (ei x) ∈ ej.source
    simpa only [ei.left_inv hi] using hj
  have hG' : DifferentiableOn ℂ (ei.symm.trans ej).symm
      (ei.symm.trans ej).target := by
    change DifferentiableOn ℂ (ei.symm.trans ej).symm (ei.symm.trans ej).symm.source
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm] using hG
  have hdim := SGPT.PSH.model_dimension_eq_of_holomorphic_openPartial (ei.symm.trans ej) hF hG' ⟨_, hx⟩
  subst e
  let F := ei.symm.trans ej
  have hcenter : F (ei x) = ej x := by
    simp only [F, OpenPartialHomeomorph.trans_apply, ei.left_inv hi]
  let Φ : LocalHolomorphicEquivAt (n := d) (ei x) := {
    source := F.source
    target := F.target
    isOpen_source := F.open_source
    isOpen_target := F.open_target
    center_mem_source := hx
    toFun := F
    invFun := F.symm
    toFun_holomorphic := hF
    invFun_holomorphic := hG'
    mapsTo_toFun := fun _ hz => F.map_source hz
    mapsTo_invFun := fun _ hz => F.map_target hz
    left_inv := fun _ hz => F.left_inv hz
    right_inv := fun _ hz => F.right_inv hz }
  have hcov : squaredLogLelongNumber (n := d)
      (fun z => u (ei.symm (F.symm z))) (ej x) =
      squaredLogLelongNumber (n := d) (u ∘ ei.symm) (ei x) := by
    simpa only [Φ, hcenter, Function.comp_apply] using
      squaredLogLelongNumber_comp_inv_eq Φ hx (u ∘ ei.symm)
  have hy : ej x ∈ F.target := hcenter ▸ F.map_source hx
  have hgerm : (fun z => u (ei.symm (F.symm z))) =ᶠ[𝓝 (ej x)] u ∘ ej.symm := by
    filter_upwards [F.open_target.mem_nhds hy] with z hz
    change u (ei.symm (ei (ej.symm z))) = u (ej.symm z)
    exact congrArg u (ei.left_inv hz.2)
  exact hcov.symm.trans (squaredLogLelongNumber_congr hgerm)

/-- Every actual atlas chart gives the same original point reader. -/
theorem coordinate_squaredLogLelongNumber_eq {X : Type*} [TopologicalSpace X]
    (A : VariableComplexAtlas X) (u : X → EReal) (i j : A.Index) {x : X}
    (hi : x ∈ (A.chart i).source) (hj : x ∈ (A.chart j).source) :
    squaredLogLelongNumber (n := A.dimension i) (A.coordinate u i) (A.chart i x) =
      squaredLogLelongNumber (n := A.dimension j) (A.coordinate u j) (A.chart j x) :=
  squaredLogLelongNumber_chart_eq (A.chart i) (A.chart j)
    (A.holomorphic i j) (A.holomorphic j i) u hi hj

/-- The literal original point reader uses a chart actually supplied by the cover. -/
def sourceLelong {X : Type*} [TopologicalSpace X]
    (A : VariableComplexAtlas X) (u : X → EReal) (x : X) : ℝ≥0∞ :=
  let i := Classical.choose (A.cover x)
  squaredLogLelongNumber (n := A.dimension i) (A.coordinate u i) (A.chart i x)

/-- The cover choice agrees with every genuine chart, including all poles and zero dimensions. -/
theorem sourceLelong_eq_chart {X : Type*} [TopologicalSpace X]
    (A : VariableComplexAtlas X) (u : X → EReal) (x : X) (i : A.Index)
    (hi : x ∈ (A.chart i).source) :
    A.sourceLelong u x =
      squaredLogLelongNumber (n := A.dimension i) (A.coordinate u i) (A.chart i x) :=
  A.coordinate_squaredLogLelongNumber_eq u (Classical.choose (A.cover x)) i
    (Classical.choose_spec (A.cover x)) hi

/-- The positive-dimensional chart branch is exactly the printed squared-log growth supremum. -/
theorem sourceLelong_eq_growth_sup {X : Type*} [TopologicalSpace X]
    (A : VariableComplexAtlas X) (u : X → EReal) (x : X) (i : A.Index)
    (hi : x ∈ (A.chart i).source) (hn : A.dimension i ≠ 0) :
    A.sourceLelong u x =
      ⨆ (γ : ℝ≥0) (_ : ∃ C : ℝ, ∀ᶠ z in 𝓝[≠] (A.chart i x),
        u ((A.chart i).symm z) ≤
          (((γ : ℝ) * Real.log (‖z - A.chart i x‖ ^ 2) + C : ℝ) : EReal)),
        (γ : ℝ≥0∞) := by
  rw [A.sourceLelong_eq_chart u x i hi, squaredLogLelongNumber, if_neg hn]
  simp only [coordinate, Function.comp_apply, complexChartAt, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply, id_eq]

/-- Actual holomorphic compatibility makes the reader independent of the whole covering atlas. -/
theorem sourceLelong_eq_of_compatible_atlases {X : Type*} [TopologicalSpace X]
    (A B : VariableComplexAtlas X)
    (hAB : ∀ i j, DifferentiableOn ℂ ((A.chart i).symm.trans (B.chart j))
      ((A.chart i).symm.trans (B.chart j)).source)
    (hBA : ∀ j i, DifferentiableOn ℂ ((B.chart j).symm.trans (A.chart i))
      ((B.chart j).symm.trans (A.chart i)).source)
    (u : X → EReal) (x : X) : A.sourceLelong u x = B.sourceLelong u x :=
  squaredLogLelongNumber_chart_eq
    (A.chart (Classical.choose (A.cover x))) (B.chart (Classical.choose (B.cover x)))
    (hAB _ _) (hBA _ _) u (Classical.choose_spec (A.cover x))
    (Classical.choose_spec (B.cover x))

/-- The genuine fixed-model atlas agrees with the independently defined source manifold reader. -/
theorem sourceLelong_ofFixedModel_eq {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (u : M → EReal) (x : M) :
    (ofFixedModel n M).sourceLelong u x = squaredLogLelongNumber (n := n) u x := by
  let e := complexChartAt (n := n) x
  rw [(ofFixedModel n M).sourceLelong_eq_chart u x e (mem_complexChartAt_source x)]
  change squaredLogLelongNumber (n := n) (chartFunction u e) (e.val x) =
    squaredLogLelongNumber (n := n) u x
  by_cases hn : n = 0
  · simp only [squaredLogLelongNumber, hn, ite_true]
  apply (ENNReal.mul_right_inj (a := 2) (by norm_num) (by norm_num)).mp
  rw [← lelongNumber_eq_two_mul_squaredLog hn, ← lelongNumber_eq_two_mul_squaredLog hn]
  exact LelongChartReaderInvariance.lelongNumber_chartFunction_eq e
    (mem_complexChartAt_source x)

/-- Actual local complex dimension, using a chart from the covering property. -/
def pointDimension {X : Type*} [TopologicalSpace X]
    (A : VariableComplexAtlas X) (x : X) : ℕ :=
  A.dimension (Classical.choose (A.cover x))

theorem pointDimension_eq_chart {X : Type*} [TopologicalSpace X]
    (A : VariableComplexAtlas X) (x : X) (i : A.Index) (hi : x ∈ (A.chart i).source) :
    A.pointDimension x = A.dimension i :=
  A.dimension_eq_of_common_source (Classical.choose_spec (A.cover x)) hi

/-- Overlap derivatives manufacture local constancy of actual dimension. -/
theorem pointDimension_isLocallyConstant {X : Type*} [TopologicalSpace X]
    (A : VariableComplexAtlas X) : IsLocallyConstant A.pointDimension := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  obtain ⟨i, hi⟩ := A.cover x
  refine ⟨(A.chart i).source, (A.chart i).open_source, hi, fun y hy => ?_⟩
  exact (A.pointDimension_eq_chart y i hy).trans (A.pointDimension_eq_chart x i hi).symm

/-- Actual dimension is constant on the original connected component. -/
theorem pointDimension_eq_on_connectedComponent {X : Type*} [TopologicalSpace X]
    (A : VariableComplexAtlas X) (x : X) {y : X} (hy : y ∈ connectedComponent x) :
    A.pointDimension y = A.pointDimension x :=
  A.pointDimension_isLocallyConstant.apply_eq_of_isPreconnected
    isPreconnected_connectedComponent hy mem_connectedComponent

/-- Every point on an actual zero-dimensional connected component has original reader zero. -/
theorem sourceLelong_zero_on_component {X : Type*} [TopologicalSpace X]
    (A : VariableComplexAtlas X) (u : X → EReal) (x : X)
    (hd : A.pointDimension x = 0) {y : X} (hy : y ∈ connectedComponent x) :
    A.sourceLelong u y = 0 := by
  have hdy : A.pointDimension y = 0 :=
    (A.pointDimension_eq_on_connectedComponent x hy).trans hd
  unfold sourceLelong
  simp only [squaredLogLelongNumber,
    show A.dimension (Classical.choose (A.cover y)) = 0 from hdy, ite_true]

/-- The genuine radial logarithm has native coefficient one in positive dimension. -/
theorem lelongNumber_radial_log_eq_one {n : ℕ} (hn : n ≠ 0) :
    lelongNumber (n := n)
      (fun z : ComplexModel n => ENNReal.log (ENNReal.ofReal ‖z‖)) 0 = 1 := by
  let j : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  apply le_antisymm
  · have h := KahlerCurrentMax.lelongNumber_le_of_eventually_le
      (n := n) (x := (0 : ComplexModel n))
      (u := fun z => ENNReal.log (ENNReal.ofReal ‖z j‖))
      (v := fun z => ENNReal.log (ENNReal.ofReal ‖z‖))
      (Eventually.of_forall fun z => ENNReal.log_le_log
        (ENNReal.ofReal_le_ofReal (PiLp.norm_apply_le z j)))
    simpa only [CoordinateLogarithmLelongNormalization.lelongNumber_coordinate_log_eq_one] using h
  · have h : ENNReal.ofReal (1 : ℝ) ≤ lelongNumber (n := n)
        (fun z : ComplexModel n => ENNReal.log (ENNReal.ofReal ‖z‖)) 0 := by
      apply LelongNumberChartTransport.ofReal_le_lelongNumber (by norm_num : (0 : ℝ) ≤ 1)
        (C := 0)
      rw [eventually_nhdsWithin_iff]
      refine Eventually.of_forall fun z hz => ?_
      have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
      simp only [complexChartAt, chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
        id_eq, sub_zero, one_mul, add_zero, ENNReal.log_ofReal_of_pos hnorm]
      exact le_rfl
    simpa only [ENNReal.ofReal_one] using h

/-- Literal source normalization for the whole radial square, with its pole retained. -/
theorem squaredLogLelongNumber_radial_square_eq_one {n : ℕ} (hn : n ≠ 0) :
    squaredLogLelongNumber (n := n)
      (fun z : ComplexModel n => ENNReal.log (ENNReal.ofReal (‖z‖ ^ 2))) 0 = 1 := by
  have hfun : (fun z : ComplexModel n => ENNReal.log (ENNReal.ofReal (‖z‖ ^ 2))) =
      (fun z => (2 : EReal) * ENNReal.log (ENNReal.ofReal ‖z‖)) := by
    funext z
    rw [ENNReal.ofReal_pow (norm_nonneg z), ENNReal.log_pow]
    norm_num
  have hnative : lelongNumber (n := n)
      (fun z : ComplexModel n => ENNReal.log (ENNReal.ofReal (‖z‖ ^ 2))) 0 = 2 := by
    rw [hfun]
    have hs := ActualLelongPositiveScaling.lelongNumber_smul_eq
      (n := n) (u := fun z : ComplexModel n => ENNReal.log (ENNReal.ofReal ‖z‖))
      (x := 0) (by norm_num : 0 < (2 : ℝ))
    rw [lelongNumber_radial_log_eq_one hn] at hs
    have htwo : ((2 : ℝ) : EReal) = (2 : EReal) := EReal.coe_coe_eq_natCast 2
    rw [htwo] at hs
    simpa only [ENNReal.ofReal_ofNat, mul_one] using hs
  apply (ENNReal.mul_right_inj (a := 2) (by norm_num) (by norm_num)).mp
  rw [← lelongNumber_eq_two_mul_squaredLog hn, hnative, mul_one]

end SGPT.PSH.VariableComplexAtlas
