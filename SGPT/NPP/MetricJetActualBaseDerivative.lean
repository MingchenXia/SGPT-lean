import SGPT.NPP.MetricJetBaseDerivative

/-!
# Actual first base derivative of the literal metric polynomial overlap

The varying inverse metric, actual Koszul coefficient and actual coordinate
derivative are differentiated as part of the same explicit formula.
The complete blueprint is `dnt-big-metric-jet-base-derivative.tex`.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace SGPT.NPP.DNTBig

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Envelopes

variable {n : ℕ}

/-- Smoothness of the actual pullback metric, from the actual smooth metric
and actual smooth coordinate map. -/
theorem contDiffOn_actual_pullbackBilin
    {g : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    {φ : ComplexModel n → ComplexModel n} {U V : Set (ComplexModel n)}
    (hU : IsOpen U) (_hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V)
    (hφ : ContDiffOn ℝ ∞ φ U) (hmaps : MapsTo φ U V) :
    ContDiffOn ℝ ∞ (TosC11b.pullbackBilin g φ) U := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ φ) U := hφ.fderiv_of_isOpen hU (by simp)
  have hgc : ContDiffOn ℝ ∞ (fun z => g (φ z)) U := hg.comp hφ hmaps
  intro z hz
  have hc : ContDiffAt ℝ ∞ (fun z => g (φ z)) z := hgc.contDiffAt (hU.mem_nhds hz)
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ φ) z := hD.contDiffAt (hU.mem_nhds hz)
  let flipL := (ContinuousLinearMap.flipₗᵢ ℝ (ComplexModel n) (ComplexModel n) ℝ).toContinuousLinearEquiv
  have h1 := flipL.contDiff.contDiffAt.comp z (hc.clm_comp hd)
  have h2 := flipL.contDiff.contDiffAt.comp z (h1.clm_comp hd)
  exact h2.contDiffWithinAt

/-- Actual positive pullbacks from actual invertible coordinate derivatives. -/
theorem actual_pullbackBilin_positive
    {g : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    {φ : ComplexModel n → ComplexModel n} {z : ComplexModel n}
    (hpos : ∀ v, v ≠ 0 → 0 < g (φ z) v v)
    (L : ComplexModel n ≃L[ℝ] ComplexModel n)
    (hL : fderiv ℝ φ z = L.toContinuousLinearMap) :
    ∀ v, v ≠ 0 → 0 < TosC11b.pullbackBilin g φ z v v := by
  intro v hv
  change 0 < g (φ z) (fderiv ℝ φ z v) (fderiv ℝ φ z v)
  rw [hL]
  exact hpos _ (by simpa using L.injective.ne hv)

/-- The actual metric-overlap function is jointly smooth on a manufactured
product neighbourhood, derived from its literal two metric jets. -/
theorem exists_product_contDiffOn_metricJetOverlap
    {g : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    {φ : ComplexModel n → ComplexModel n} {U V : Set (ComplexModel n)}
    (hU : IsOpen U) (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V)
    (hφ : ContDiffOn ℝ ∞ φ U) (hmaps : MapsTo φ U V)
    (hpos : ∀ a ∈ V, ∀ v, v ≠ 0 → 0 < g a v v)
    (hlocalEquiv : ∀ a ∈ U, ∃ L : ComplexModel n ≃L[ℝ] ComplexModel n,
      fderiv ℝ φ a = L.toContinuousLinearMap)
    {z : ComplexModel n} (hz : z ∈ U) :
    ∃ A B : Set (ComplexModel n), IsOpen A ∧ z ∈ A ∧ A ⊆ U ∧
      IsOpen B ∧ (0 : ComplexModel n) ∈ B ∧
      ContDiffOn ℝ ∞ (fun q : ComplexModel n × ComplexModel n =>
        metricJetOverlap g φ q.1 q.2) (A ×ˢ B) := by
  have hpb := contDiffOn_actual_pullbackBilin hU hV hg hφ hmaps
  have hpbpos : ∀ a ∈ U, ∀ v, v ≠ 0 → 0 < TosC11b.pullbackBilin g φ a v v := by
    intro a ha
    obtain ⟨L, hL⟩ := hlocalEquiv a ha
    exact actual_pullbackBilin_positive (hpos _ (hmaps ha)) L hL
  have hJ := contDiffOn_metricQuadraticJet hU hpb hpbpos
  have hK := contDiffOn_metricQuadraticJet hV hg hpos
  have hJ0 : metricQuadraticJet (TosC11b.pullbackBilin g φ) z 0 = z := by
    rw [← bilinearQuadraticJet_metricConnection]
    simp [bilinearQuadraticJet]
  have hJat : ContDiffAt ℝ ∞
      (fun q : ComplexModel n × ComplexModel n =>
        metricQuadraticJet (TosC11b.pullbackBilin g φ) q.1 q.2) (z, 0) :=
    hJ.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hz, mem_univ _⟩)
  have hbase : {q : ComplexModel n × ComplexModel n | q.1 ∈ U} ∈ 𝓝 (z, 0) :=
    continuous_fst.continuousAt.preimage_mem_nhds (hU.mem_nhds hz)
  have htarget : {q : ComplexModel n × ComplexModel n |
      metricQuadraticJet (TosC11b.pullbackBilin g φ) q.1 q.2 ∈ U} ∈ 𝓝 (z, 0) :=
    hJat.continuousAt.preimage_mem_nhds (by simpa only [hJ0] using hU.mem_nhds hz)
  obtain ⟨A, B, hA, hzA, hB, h0B, hAB⟩ :=
    mem_nhds_prod_iff'.mp (inter_mem hbase htarget)
  have hAU : A ⊆ U := fun a ha =>
    (hAB (show (a, (0 : ComplexModel n)) ∈ A ×ˢ B from ⟨ha, h0B⟩)).1
  refine ⟨A, B, hA, hzA, hAU, hB, h0B, ?_⟩
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ φ) U := hφ.fderiv_of_isOpen hU (by simp)
  intro q hq
  have hqU : q.1 ∈ U := hAU hq.1
  have hqJ : metricQuadraticJet (TosC11b.pullbackBilin g φ) q.1 q.2 ∈ U := (hAB hq).2
  have hJq := hJ.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hqU, mem_univ _⟩)
  have hfirst := (hφ.contDiffAt (hU.mem_nhds hqJ)).comp q hJq
  have hφq : ContDiffAt ℝ ∞ (fun t : ComplexModel n × ComplexModel n => φ t.1) q :=
    (hφ.contDiffAt (hU.mem_nhds hqU)).comp q contDiffAt_fst
  have hDq : ContDiffAt ℝ ∞
      (fun t : ComplexModel n × ComplexModel n => fderiv ℝ φ t.1 t.2) q :=
    ((hD.contDiffAt (hU.mem_nhds hqU)).comp q contDiffAt_fst).clm_apply contDiffAt_snd
  have hKq : ContDiffAt ℝ ∞
      (fun t : ComplexModel n × ComplexModel n => metricQuadraticJet g t.1 t.2)
      (φ q.1, fderiv ℝ φ q.1 q.2) :=
    hK.contDiffAt ((hV.prod isOpen_univ).mem_nhds ⟨hmaps hqU, mem_univ _⟩)
  have hsecond := hKq.comp q (hφq.prodMk hDq)
  exact (hfirst.sub hsecond).contDiffWithinAt

/-- The first derivative in the ACTUAL BASE of the literal metric-jet
coordinate overlap has a manufactured cubic fibre bound. -/
theorem actual_metricJetOverlap_locally_cubic_base_derivative
    {g : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    {φ : ComplexModel n → ComplexModel n} {U V : Set (ComplexModel n)}
    (hU : IsOpen U) (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V)
    (hφ : ContDiffOn ℝ ∞ φ U) (hmaps : MapsTo φ U V)
    (hpos : ∀ a ∈ V, ∀ v, v ≠ 0 → 0 < g a v v)
    (hsym : ∀ a ∈ V, ∀ v t, g a v t = g a t v)
    (hlocalEquiv : ∀ a ∈ U, ∃ L : ComplexModel n ≃L[ℝ] ComplexModel n,
      fderiv ℝ φ a = L.toContinuousLinearMap)
    {z : ComplexModel n} (hz : z ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ v ∈ closedBall (0 : ComplexModel n) r,
        ‖fderiv ℝ (fun a => metricJetOverlap g φ a v) z‖ ≤ M * ‖v‖ ^ 3 := by
  obtain ⟨A, B, hA, hzA, hAU, hB, h0B, hR⟩ :=
    exists_product_contDiffOn_metricJetOverlap hU hV hg hφ hmaps hpos hlocalEquiv hz
  let F := fun q : ComplexModel n × ComplexModel n => metricJetOverlap g φ q.1 q.2
  have hzeros : ∀ a ∈ A, F (a, 0) = 0 ∧ fiberPartial F (a, 0) = 0 ∧
      fiberPartial (fiberPartial F) (a, 0) = 0 := by
    intro a ha
    have haU := hAU ha
    obtain ⟨L, hL⟩ := hlocalEquiv a haU
    have hgφ : DifferentiableAt ℝ g (φ a) :=
      ((hg.differentiableOn (by simp)).differentiableAt (hV.mem_nhds (hmaps haU)))
    obtain ⟨h0, h1, h2⟩ := metricJetOverlap_zero_two_jet hU
      (hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)) haU hgφ
      (hpos _ (hmaps haU)) (hsym _ (hmaps haU)) L hL
    have hFdiff : DifferentiableAt ℝ F (a, 0) :=
      ((hR.differentiableOn (by simp)).differentiableAt ((hA.prod hB).mem_nhds ⟨ha, h0B⟩))
    refine ⟨h0, ?_, ?_⟩
    · rw [← fderiv_fiber_slice hFdiff]
      exact h1
    · rw [← second_fderiv_fiber_slice hA hB hR ha h0B]
      exact h2
  obtain ⟨r, hr, hrB, M, hM, hbound⟩ :=
    exists_local_cubic_base_derivative_bound_of_zero_two_jet hA hB hR h0B
      (fun a ha => (hzeros a ha).1) (fun a ha => (hzeros a ha).2.1)
      (fun a ha => (hzeros a ha).2.2) hzA
  refine ⟨r, hr, M, hM, fun v hv => ?_⟩
  rw [fderiv_base_slice
    ((hR.differentiableOn (by simp)).differentiableAt ((hA.prod hB).mem_nhds ⟨hzA, hrB hv⟩))]
  exact hbound v hv

end SGPT.NPP.DNTBig
