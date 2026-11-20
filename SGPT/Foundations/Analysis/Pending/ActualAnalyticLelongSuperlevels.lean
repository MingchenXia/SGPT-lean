import SGPT.Foundations.Analysis.Pending.ActualAnalyticLelongJetLocus
import SGPT.Foundations.Analysis.Pending.StrictTransformLocus
import SGPT.Foundations.Analysis.Pending.LelongChartReaderInvariance
import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false

/-! # Actual weak analytic Lelong superlevels

Every real threshold is recovered from the internally produced integral jet
order. Genuine preferred-chart presentations yield manifold analytic subsets
and transport an open-piece lower bound to an entire irreducible subvariety.
The squared-logarithm factor two is retained literally.
-/

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualAnalyticLelongSuperlevels

open FirstPass FirstPass.NonKahlerLocus FirstPass.NumericalRestrictedVolumeScaffold

noncomputable section

private theorem translated_reader {n : ℕ} (u : ComplexModel n → EReal)
    (x : ComplexModel n) :
    lelongNumber (n := n) (fun z => u (z + x)) 0 = lelongNumber (n := n) u x := by
  let Φ : LocalHolomorphicEquivAt (n := n) x := {
    source := univ
    target := univ
    isOpen_source := isOpen_univ
    isOpen_target := isOpen_univ
    center_mem_source := mem_univ _
    toFun := fun z => z - x
    invFun := fun z => z + x
    toFun_holomorphic := (differentiable_id.sub_const x).differentiableOn
    invFun_holomorphic := (differentiable_id.add_const x).differentiableOn
    mapsTo_toFun := mapsTo_univ _ _
    mapsTo_invFun := mapsTo_univ _ _
    left_inv := fun z _ => sub_add_cancel z x
    right_inv := fun z _ => add_sub_cancel_right z x }
  simpa only [Φ, sub_self] using
    (LocalHolomorphicLelongReaderCovariance.lelongNumber_comp_inv_eq Φ (mem_univ x)
      (u := u))

private theorem center_threshold_iff {m N : ℕ}
    (f : Fin N → ComplexModel (m + 1) → ℂ)
    (hf : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ (f i) z)
    {c : ℝ} (hc : 0 < c) {b : ComplexModel (m + 1) → ℝ}
    (hb : BoundedRealGermAt b 0) (r : ℝ) :
    (ENNReal.ofReal r ≤ lelongNumber (n := m + 1)
      (fun z => (c : EReal) * generatorLog f z + (b z : EReal)) 0) ↔
    (ENNReal.ofReal (2 * c * (Nat.ceil (r / (2 * c)) : ℝ)) ≤
      lelongNumber (n := m + 1)
        (fun z => (c : EReal) * generatorLog f z + (b z : EReal)) 0) := by
  classical
  by_cases hne : ∃ i, ¬ ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), f i z = 0
  · obtain ⟨a, _, _, hν⟩ :=
      ActualFiniteGeneratorLelongNormalization.exists_finite_generator_lelong_normalization f hf hne
    rw [hν c hc b hb, ENNReal.ofReal_le_ofReal_iff (by positivity),
      ENNReal.ofReal_le_ofReal_iff (by positivity)]
    have hfactor : 0 < 2 * c := by positivity
    have hdiv : r ≤ 2 * c * (a : ℝ) ↔ r / (2 * c) ≤ (a : ℝ) := by
      simpa only [mul_comm] using (div_le_iff₀ hfactor).symm
    rw [hdiv]
    have hceil : (Nat.ceil (r / (2 * c)) : ℝ) ≤ (a : ℝ) ↔ r / (2 * c) ≤ (a : ℝ) := by
      exact (Nat.cast_le (α := ℝ)).trans Nat.ceil_le
    constructor
    · intro h
      exact mul_le_mul_of_nonneg_left (hceil.mpr h) hfactor.le
    · intro h
      apply hceil.mp
      nlinarith
  · have hzero : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), f i z = 0 := by
      simpa only [not_exists, not_not] using hne
    have hbot : ∀ᶠ z in 𝓝[≠] (0 : ComplexModel (m + 1)),
        (c : EReal) * generatorLog f z + (b z : EReal) = ⊥ := by
      have hall : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), ∀ i, f i z = 0 :=
        eventually_all.mpr hzero
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds hall] with z hz
      rw [(generatorLog_eq_bot_iff f z).mpr hz, EReal.coe_mul_bot_of_pos hc, EReal.bot_add]
    rw [LelongNumberChartTransport.lelongNumber_eq_top_of_eventually_bot hbot]
    exact iff_of_true le_top le_top

/-- Arbitrary real thresholds have genuine finite analytic zero germs;
integer rounding is produced from the original finite logarithmic family. -/
theorem isAnalyticGerm_real_lelong_superlevel {m N : ℕ}
    (f : Fin N → ComplexModel (m + 1) → ℂ)
    (hf : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ (f i) z)
    {c : ℝ} (hc : 0 < c) {b : ComplexModel (m + 1) → ℝ}
    (hb : BoundedRealGermAt b 0) (r : ℝ) :
    AnalyticGermDecomposition.IsAnalyticGerm
      {x : ComplexModel (m + 1) | ENNReal.ofReal r ≤
        lelongNumber (n := m + 1) (fun y => (c : EReal) * generatorLog f y + (b y : EReal)) x} := by
  classical
  obtain ⟨B, hB, hbound⟩ := hb
  obtain ⟨U, hprops, hU, h0⟩ :=
    eventually_nhds_iff.mp ((eventually_all.mpr hf).and hbound)
  have hU0 : ∀ᶠ x in 𝓝 (0 : ComplexModel (m + 1)), x ∈ U := hU.mem_nhds h0
  have hag := (ActualAnalyticLelongJetLocus.isAnalyticGerm_lelong_superlevel f hf hc
    (show BoundedRealGermAt b 0 from ⟨B, hB, hbound⟩) (Nat.ceil (r / (2 * c)))).1
  apply hag.congr
  filter_upwards [hU0] with x hx
  have hcont : Tendsto (fun z : ComplexModel (m + 1) => z + x) (𝓝 0) (𝓝 x) := by
    simpa only [zero_add] using
      (show ContinuousAt (fun z : ComplexModel (m + 1) => z + x) 0 from
        continuousAt_id.add continuousAt_const).tendsto
  have hfx : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      DifferentiableAt ℂ (fun z => f i (z + x)) z := by
    intro i
    filter_upwards [hcont.eventually (hU.mem_nhds hx)] with z hz
    exact ((hprops (z + x) hz).1 i).comp z (differentiableAt_id.add_const x)
  have hUx : ∀ᶠ y in 𝓝 x, y ∈ U := hU.mem_nhds hx
  have hbx : BoundedRealGermAt b ((0 : ComplexModel (m + 1)) + x) := by
    simpa only [zero_add] using
      (show BoundedRealGermAt b x from ⟨B, hB, hUx.mono fun y hy => (hprops y hy).2⟩)
  have hbt : BoundedRealGermAt (fun z => b (z + x)) 0 :=
    hbx.comp_continuousAt (F := fun z : ComplexModel (m + 1) => z + x) (y := 0)
      (continuousAt_id.add continuousAt_const)
  have h := center_threshold_iff (fun i z => f i (z + x)) hfx hc hbt r
  have heq : generatorLog (fun i z => f i (z + x)) = fun z => generatorLog f (z + x) := rfl
  rw [heq] at h
  have hreader := translated_reader (fun y => (c : EReal) * generatorLog f y + (b y : EReal)) x
  rw [hreader] at h
  exact propext h.symm

private theorem translated_reader_at {n : ℕ} (u : ComplexModel n → EReal)
    (p x : ComplexModel n) :
    lelongNumber (n := n) (fun z => u (z + p)) x = lelongNumber (n := n) u (x + p) := by
  let Φ : LocalHolomorphicEquivAt (n := n) (x + p) := {
    source := univ
    target := univ
    isOpen_source := isOpen_univ
    isOpen_target := isOpen_univ
    center_mem_source := mem_univ _
    toFun := fun z => z - p
    invFun := fun z => z + p
    toFun_holomorphic := (differentiable_id.sub_const p).differentiableOn
    invFun_holomorphic := (differentiable_id.add_const p).differentiableOn
    mapsTo_toFun := mapsTo_univ _ _
    mapsTo_invFun := mapsTo_univ _ _
    left_inv := fun z _ => sub_add_cancel z p
    right_inv := fun z _ => add_sub_cancel_right z p }
  simpa only [Φ, add_sub_cancel_right] using
    (LocalHolomorphicLelongReaderCovariance.lelongNumber_comp_inv_eq Φ (mem_univ (x + p))
      (u := u))

section Manifold

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- Literal weak analytic presentations produce actual finite holomorphic
superlevel equations in every preferred chart. -/
theorem isComplexAnalyticSubset_lelong_superlevel {u : M → EReal}
    (han : HasManifoldAnalyticSingularitiesSmoothOffPole (n := m + 1) u) (r : ℝ) :
    IsComplexAnalyticSubset (n := m + 1)
      {x : M | ENNReal.ofReal r ≤ lelongNumber (n := m + 1) u x} := by
  classical
  intro x
  let e := complexChartAt (n := m + 1) x
  let p := e.val x
  have hxsrc : x ∈ e.val.source := mem_complexChartAt_source x
  have hp : p ∈ e.val.target := e.val.map_source hxsrc
  obtain ⟨c, N, f, hc, ⟨U, hU, hpU, hf⟩, b, hb, _, heq⟩ := han e p hp
  have htend : Tendsto (fun z : ComplexModel (m + 1) => z + p) (𝓝 0) (𝓝 p) := by
    simpa only [zero_add] using
      (show ContinuousAt (fun z : ComplexModel (m + 1) => z + p) 0 from
        continuousAt_id.add continuousAt_const).tendsto
  have hft : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      DifferentiableAt ℂ (fun z => f i (z + p)) z := by
    intro i
    filter_upwards [htend.eventually (hU.mem_nhds hpU)] with z hz
    exact ((hf i).differentiableAt (hU.mem_nhds hz)).comp z
      (differentiableAt_id.add_const p)
  have hbp : BoundedRealGermAt b ((0 : ComplexModel (m + 1)) + p) := by
    simpa only [zero_add] using hb
  have hbt : BoundedRealGermAt (fun z => b (z + p)) 0 :=
    hbp.comp_continuousAt (F := fun z : ComplexModel (m + 1) => z + p) (y := 0)
      (continuousAt_id.add continuousAt_const)
  have hag := isAnalyticGerm_real_lelong_superlevel (fun i z => f i (z + p)) hft hc hbt r
  have heqT : (fun z : ComplexModel (m + 1) => chartFunction u e (z + p)) =ᶠ[𝓝 0]
      (fun z => (c : EReal) * generatorLog (fun i w => f i (w + p)) z +
        (b (z + p) : EReal)) := htend.eventually heq
  have hseteq :
      {z : ComplexModel (m + 1) | ENNReal.ofReal r ≤
        lelongNumber (n := m + 1) (fun w => (c : EReal) *
          generatorLog (fun i v => f i (v + p)) w + (b (w + p) : EReal)) z} =ᶠ[𝓝 0]
      {z : ComplexModel (m + 1) | ENNReal.ofReal r ≤
        lelongNumber (n := m + 1) (fun w => chartFunction u e (w + p)) z} := by
    filter_upwards [heqT.eventuallyEq_nhds] with z hz
    apply propext
    change (_ ≤ _) ↔ (_ ≤ _)
    rw [LelongNumberComparison.lelongNumber_congr hz]
  obtain ⟨q, g, hg, hzero⟩ := hag.congr hseteq
  have htarget : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), z + p ∈ e.val.target :=
    htend.eventually (e.val.open_target.mem_nhds hp)
  obtain ⟨W, hprops, hW, h0⟩ :=
    eventually_nhds_iff.mp (((eventually_all.mpr hg).and hzero).and htarget)
  refine ⟨{
    generatorCount := q
    generator := fun i w => g i (w - p)
    coordinateNeighborhood := (fun w => w - p) ⁻¹' W
    isOpen_coordinateNeighborhood := hW.preimage (continuous_id.sub continuous_const)
    center_mem_coordinateNeighborhood := by simpa only [p, e, mem_preimage, sub_self] using h0
    coordinateNeighborhood_subset_target := ?_
    generator_holomorphic := ?_
    zeroLocus := ?_ }⟩
  · intro w hw
    simpa only [sub_add_cancel] using (hprops (w - p) hw).2
  · intro i w hw
    exact (((hprops (w - p) hw).1.1 i).comp w
      (differentiableAt_id.sub_const p)).differentiableWithinAt
  · intro y hysrc hy
    change (ENNReal.ofReal r ≤ lelongNumber (n := m + 1) u y) ↔
      ∀ i, g i (e.val y - p) = 0
    rw [← LelongChartReaderInvariance.lelongNumber_chartFunction_eq e hysrc]
    have hread := translated_reader_at (chartFunction u e) p (e.val y - p)
    simp only [sub_add_cancel] at hread
    rw [← hread]
    exact (hprops (e.val y - p) hy).1.2

/-- Every nonempty ambient open piece of a genuine irreducible analytic
subvariety has its whole-subvariety logarithmic reader. -/
theorem iInf_lelongNumber_eq_open_piece {u : M → EReal}
    (han : HasManifoldAnalyticSingularitiesSmoothOffPole (n := m + 1) u)
    (V : ClosedIrreducibleAnalyticSubvariety (m + 1) M) {U : Set M}
    (hU : IsOpen U) (hVU : (V.carrier ∩ U).Nonempty) :
    (⨅ x ∈ V.carrier, lelongNumber (n := m + 1) u x) =
      ⨅ x ∈ V.carrier ∩ U, lelongNumber (n := m + 1) u x := by
  apply le_antisymm
  · refine le_iInf₂ fun x hx => ?_
    exact iInf₂_le_of_le x hx.1 le_rfl
  · refine le_iInf₂ fun x hx => ?_
    apply ENNReal.le_of_forall_nnreal_lt
    intro a ha
    have hA := isComplexAnalyticSubset_lelong_superlevel han (a : ℝ)
    have hsub : V.carrier ∩ U ⊆
        {y : M | ENNReal.ofReal (a : ℝ) ≤ lelongNumber (n := m + 1) u y} := by
      intro y hy
      simpa only [mem_ofPred_eq, ENNReal.ofReal_coe_nnreal] using
        (ha.le.trans (iInf₂_le_of_le y hy le_rfl))
    have hwhole := StrictTransformLocus.subset_of_inter_isOpen_subset V hA hU hVU hsub
    simpa only [mem_ofPred_eq, ENNReal.ofReal_coe_nnreal] using hwhole hx

end Manifold

end

end SGPT.Foundations.Analysis.Pending.ActualAnalyticLelongSuperlevels
