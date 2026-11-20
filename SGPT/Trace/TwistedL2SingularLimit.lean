import SGPT.Trace.TwistedL2SingularExhaustion
import SGPT.Foundations.Analysis.Pending.WeightedL2ExtensionLimit

/-!
# Limits of holomorphic sections with uniform weighted `L²` bounds

The limiting step of the proof of `claude-twisted-l2:weakly-pseudoconvex`
in `claude-twisted-l2.tex` (Demailly, *Analytic methods in algebraic geometry*,
proof of Theorem 5.1: solutions on the sublevel sets `X_t` have a weak limit).

## Main results

* `continuousOn_norm_sub_of_holomorphic`: `‖G - T‖` is continuous where `G` is smooth and `T`
  holomorphic.
* The actual singular weighted limit along an exhaustion is proved separately in
  `TwistedL2SingularLimitConstruction`, including its punctured-section variant.
  This file supplies continuity and measurability lemmas used in that construction.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle Metric
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

variable (L : HermitianHolomorphicLineBundle.{0, 0} n X)

/-- The coordinate of a difference is the difference of the coordinates. -/
theorem coord_sub (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ L.Fiber → X))
    [MemTrivializationAtlas e] {y : X} (hy : y ∈ e.baseSet) (v w : L.Fiber y) :
    (e ⟨y, v - w⟩).2 = (e ⟨y, v⟩).2 - (e ⟨y, w⟩).2 := by
  rw [← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e hy,
    ← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e hy,
    ← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e hy, map_sub]

/-- The coordinate of a smooth section in the frame at `x` is continuous at `x`. -/
theorem continuousAt_coord_of_isSmoothSectionOn {G : (x : X) → L.Fiber x}
    (hG : IsSmoothSectionOn L G univ) (x : X) :
    ContinuousAt (fun y => ((trivializationAt ℂ L.Fiber x) ⟨y, G y⟩).2) x := by
  set c := complexChartAt (n := n) x
  let e : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber x, inferInstance⟩
  have hx : x ∈ c.val.source := mem_complexChartAt_source x
  have hxe : x ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ L.Fiber x
  have hDo : IsOpen (chartFrameDomain L c e ∩ c.val.symm ⁻¹' univ) := by
    rw [preimage_univ, inter_univ]
    exact c.val.isOpen_inter_preimage_symm e.val.open_baseSet
  have hz : c.val x ∈ chartFrameDomain L c e ∩ c.val.symm ⁻¹' univ :=
    ⟨⟨c.val.map_source hx, by rw [mem_preimage, c.val.left_inv hx]; exact hxe⟩, trivial⟩
  have h1 : ContinuousAt (chartCoeff L c e G) (c.val x) :=
    (hG c e).continuousOn.continuousAt (hDo.mem_nhds hz)
  refine (h1.comp (c.val.continuousAt hx)).congr
    (eventually_of_mem (c.val.open_source.mem_nhds hx) fun y hy => ?_)
  have key : ∀ y', y' = y → (e.val ⟨y', G y'⟩).2 = (e.val ⟨y, G y⟩).2 := by
    rintro _ rfl; rfl
  simp only [Function.comp, chartCoeff, frameCoeff]
  exact key _ (c.val.left_inv hy)

/-- **`‖G - T‖` is continuous** on an open set where `T` is holomorphic and `G` smooth. -/
theorem continuousOn_norm_sub_of_holomorphic {G T : (x : X) → L.Fiber x}
    (hG : IsSmoothSectionOn L G univ) {V : Set X} (hV : IsOpen V)
    (hT : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber T V) :
    ContinuousOn (fun x => ‖G x - T x‖) V := by
  intro x hxV
  refine ContinuousAt.continuousWithinAt ?_
  set e := trivializationAt ℂ L.Fiber x with he
  have hxe : x ∈ e.baseSet := mem_baseSet_trivializationAt ℂ L.Fiber x
  have hT' : ContinuousAt (fun y => (e ⟨y, T y⟩).2) x :=
    ((Trivialization.mdifferentiableAt_section_iff (IB := 𝓘(ℂ, ComplexModel n)) e T hxe).mp
      ((hT x hxV).mdifferentiableAt (hV.mem_nhds hxV))).continuousAt
  have h2 : ContinuousAt (fun y => ‖(e ⟨y, G y⟩).2 - (e ⟨y, T y⟩).2‖ * ‖e.symm y 1‖) x :=
    ((continuousAt_coord_of_isSmoothSectionOn L hG x).sub hT').norm.mul
      ((SGPT.Bergman.CompactHolomorphicSectionsDraft.frameNorm_continuousOn L.Fiber
        e).continuousAt (e.open_baseSet.mem_nhds hxe))
  refine h2.congr (eventually_of_mem (e.open_baseSet.mem_nhds hxe) fun y hy => ?_)
  simp only
  rw [norm_eq_coord_mul L e hy (G y - T y), coord_sub L e hy]

/-- A holomorphic section has a continuous norm on its (open) domain. -/
theorem continuousOn_norm_of_holomorphic {T : (x : X) → L.Fiber x} {V : Set X}
    (hT : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber T V) :
    ContinuousOn (fun x => ‖T x‖) V :=
  SGPT.Bergman.CompactHolomorphicSectionsDraft.ContinuousFiberNorm.continuous.comp_continuousOn
    hT.continuousOn

/-- The indicator of an open set of a function continuous on it is measurable. -/
theorem measurable_indicator_of_continuousOn [MeasurableSpace X] [OpensMeasurableSpace X]
    {V : Set X} (hV : IsOpen V) {f : X → ℝ≥0∞} (hf : ContinuousOn f V) :
    Measurable (V.indicator f) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact ContinuousOn.measurable_piecewise hf continuousOn_const hV.measurableSet

end SGPT.Trace.TwistedL2
