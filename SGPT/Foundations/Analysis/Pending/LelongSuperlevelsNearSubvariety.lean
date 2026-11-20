import SGPT.Foundations.Analysis.Pending.ActualAnalyticLelongSuperlevels

set_option autoImplicit false

/-! # Analytic Lelong superlevels only near a whole subvariety

The original weight is required to have actual analytic germs only at points
of the closed analytic carrier. Its superlevel intersection is nevertheless
an analytic subset of the whole ambient manifold. This supplies the literal
whole-prime/open-piece reader without extending a holomorphic germ globally.
-/

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.LelongSuperlevelsNearSubvariety

open FirstPass FirstPass.NonKahlerLocus

noncomputable section

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

private theorem superlevel_presentation_at {m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    {u : M → EReal} (x : M)
    (han : HasAnalyticSingularitiesSmoothOffPoleAt
      (chartFunction u (complexChartAt (n := m + 1) x))
      ((complexChartAt (n := m + 1) x).val x)) (r : ℝ) :
    Nonempty (ComplexAnalyticPresentationAt (n := m + 1)
      {y : M | ENNReal.ofReal r ≤ lelongNumber (n := m + 1) u y} x) := by
  classical
  let e := complexChartAt (n := m + 1) x
  let p := e.val x
  have hxsrc : x ∈ e.val.source := mem_complexChartAt_source x
  have hp : p ∈ e.val.target := e.val.map_source hxsrc
  obtain ⟨c, N, f, hc, ⟨U, hU, hpU, hf⟩, b, hb, _, heq⟩ := han
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
  have hag := ActualAnalyticLelongSuperlevels.isAnalyticGerm_real_lelong_superlevel (fun i z => f i (z + p)) hft hc hbt r
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

section Manifold

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- Analytic germs only along the original closed analytic carrier supply an
actual analytic intersection in the whole ambient manifold. -/
theorem isComplexAnalyticSubset_inter_lelong_superlevel {u : M → EReal} {A : Set M}
    (hA : IsComplexAnalyticSubset (n := m + 1) A) (hAcl : IsClosed A)
    (han : ∀ x ∈ A, HasAnalyticSingularitiesSmoothOffPoleAt
      (chartFunction u (complexChartAt (n := m + 1) x))
      ((complexChartAt (n := m + 1) x).val x)) (r : ℝ) :
    IsComplexAnalyticSubset (n := m + 1)
      (A ∩ {y : M | ENNReal.ofReal r ≤ lelongNumber (n := m + 1) u y}) := by
  classical
  intro x
  by_cases hx : x ∈ A
  · obtain ⟨pA⟩ := hA x
    obtain ⟨pν⟩ := superlevel_presentation_at x (han x hx) r
    exact ⟨pA.inter pν⟩
  · let e := complexChartAt (n := m + 1) x
    let O : Set M := e.val.source ∩ Aᶜ
    have hO : IsOpen O := e.val.open_source.inter hAcl.isOpen_compl
    have hxO : x ∈ O := ⟨mem_complexChartAt_source x, hx⟩
    have hOs : O ⊆ e.val.source := inter_subset_left
    refine ⟨{
      generatorCount := 1
      generator := fun _ _ => 1
      coordinateNeighborhood := e.val '' O
      isOpen_coordinateNeighborhood := e.val.isOpen_image_of_subset_source hO hOs
      center_mem_coordinateNeighborhood := ⟨x, hxO, rfl⟩
      coordinateNeighborhood_subset_target := ?_
      generator_holomorphic := fun _ => differentiableOn_const 1
      zeroLocus := ?_ }⟩
    · rintro z ⟨y, hy, rfl⟩
      exact e.val.map_source hy.1
    · intro y hysrc hy
      obtain ⟨z, hz, hzy⟩ := hy
      have hzy' : z = y := e.val.injOn hz.1 hysrc hzy
      have hyA : y ∉ A := hzy' ▸ hz.2
      constructor
      · intro hyint
        exact (hyA hyint.1).elim
      · intro h
        have hbad := h (0 : Fin 1)
        exact (one_ne_zero hbad).elim

/-- A whole irreducible carrier needs analytic germs only at its own points
for its logarithmic infimum to agree with every nonempty ambient open piece. -/
theorem iInf_lelongNumber_eq_open_piece {u : M → EReal}
    (V : ClosedIrreducibleAnalyticSubvariety (m + 1) M)
    (han : ∀ x ∈ V.carrier, HasAnalyticSingularitiesSmoothOffPoleAt
      (chartFunction u (complexChartAt (n := m + 1) x))
      ((complexChartAt (n := m + 1) x).val x)) {U : Set M}
    (hU : IsOpen U) (hVU : (V.carrier ∩ U).Nonempty) :
    (⨅ x ∈ V.carrier, lelongNumber (n := m + 1) u x) =
      ⨅ x ∈ V.carrier ∩ U, lelongNumber (n := m + 1) u x := by
  apply le_antisymm
  · refine le_iInf₂ fun x hx => ?_
    exact iInf₂_le_of_le x hx.1 le_rfl
  · refine le_iInf₂ fun x hx => ?_
    apply ENNReal.le_of_forall_nnreal_lt
    intro a ha
    have hA := isComplexAnalyticSubset_inter_lelong_superlevel
      V.irreducible_carrier.analytic V.isClosed_carrier han (a : ℝ)
    have hsub : V.carrier ∩ U ⊆
        V.carrier ∩ {y : M | ENNReal.ofReal (a : ℝ) ≤ lelongNumber (n := m + 1) u y} := by
      intro y hy
      refine ⟨hy.1, ?_⟩
      simpa only [mem_ofPred_eq, ENNReal.ofReal_coe_nnreal] using
        (ha.le.trans (iInf₂_le_of_le y hy le_rfl))
    have hwhole := StrictTransformLocus.subset_of_inter_isOpen_subset V hA hU hVU hsub
    simpa only [mem_ofPred_eq, ENNReal.ofReal_coe_nnreal] using (hwhole hx).2

end Manifold

end

end SGPT.Foundations.Analysis.Pending.LelongSuperlevelsNearSubvariety
