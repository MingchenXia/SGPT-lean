import SGPT.PSH.CartierLogarithmicRemainder
import SGPT.PSH.NativeQPSHPullback
import SGPT.Foundations.Analysis.Pending.MemberPullback

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open InvertibleIdealQuotient RegularLocusComponent AnalyticGermDecomposition
open scoped Topology Manifold ContDiff

universe u
variable {m : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]

/-- Actual proper-modification geometry carries an ORIGINAL rational
Cartier logarithm and arbitrary locally bounded remainder to the SAME literal
total transform and internally produced geometric coefficients, jointly with
original global QPSH. No upstairs presentation or non-pole input is supplied. -/
theorem exists_native_modification_cartier_log_presentation
    (D : EffectiveDivisor (m + 1) X) {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (u : X → EReal) (hu : (VariableComplexAtlas.ofFixedModel (m + 1) X).IsQPSH u)
    (y : Y) (g : X → ℂ) (hg : HolomorphicAt (m + 1) g (π y))
    (hgen : ∀ a, D.ideal.mem (π y) a ↔ IsInSpanAt (n := m + 1) (· = g) (π y) a)
    (c : ℚ) (hc : 0 < c) (R : X → ℝ) (hR : BoundedRealGermAt R (π y))
    (hsource : u =ᶠ[𝓝 (π y)] fun z => ((c : ℝ) : EReal) * logNormSq (g z) + (R z : EReal)) :
    (VariableComplexAtlas.ofFixedModel (m + 1) Y).IsQPSH (u ∘ π) ∧
    let Δ := GermIdealTotalTransform.EffectiveDivisor.totalTransform hπ.1
      (interior_exceptionalLocus_eq_empty_of_native_analyticModification hπ) D
    Δ.support = π ⁻¹' D.support ∧
    ∃ S : Finset (GlobalComponents.globalComponents (n := m + 1) Δ.support),
      ∃ (r : GlobalComponents.globalComponents (n := m + 1) Δ.support →
          ComplexModel (m + 1) → ℂ)
        (hr : ∀ B, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (r B) z),
        (∀ B, HolGerm.mk (r B) (hr B) ≠ 0 ∧ Squarefree (HolGerm.mk (r B) (hr B)) ∧
          vanishingIdeal (AnalyticDescendingChain.chartGerm (n := m + 1)
            (cartierPrimeComponent Δ B).carrier y) = Ideal.span {HolGerm.mk (r B) (hr B)} ∧
          AnalyticDescendingChain.chartGerm (n := m + 1)
            (cartierPrimeComponent Δ B).carrier y =ᶠ[𝓝 0] {z | r B z = 0}) ∧
        (∀ B ∈ S, 0 < c * (regularComponentOrder Δ Δ.support B : ℚ)) ∧
        (∃ T ∈ 𝓝 y, ∀ z ∈ T, z ∈ π ⁻¹' D.support ↔
          ∃ B ∈ S, z ∈ (cartierPrimeComponent Δ B).carrier) ∧
        ∃ b : ComplexModel (m + 1) → ℝ, BoundedRealGermAt b 0 ∧
          (fun z => u (π ((complexChartAt (n := m + 1) y).val.symm
            (z + (complexChartAt (n := m + 1) y).val y)))) =ᶠ[𝓝 0]
            fun z => (∑ B : {B // B ∈ S},
              (((c * (regularComponentOrder Δ Δ.support B.val : ℚ) : ℚ) : ℝ) : EReal) *
                logNormSq (r B.val z)) + (b z : EReal) := by
  refine ⟨hu.comp_native_analyticModification hπ, ?_⟩
  let Δ := GermIdealTotalTransform.EffectiveDivisor.totalTransform hπ.1
    (interior_exceptionalLocus_eq_empty_of_native_analyticModification hπ) D
  have hsupport : Δ.support = π ⁻¹' D.support :=
    BlowupExceptionalDivisor.zeroLocus_pullback hπ.1
      (DivisorMetric.isCoherent_of_isInvertible D.isInvertible)
  have hgcomp : HolomorphicAt (m + 1) (g ∘ π) y :=
    hg.comp_contMDiff (Eventually.of_forall fun z => hπ.1.contMDiffAt)
  have hgencomp : ∀ a, Δ.ideal.mem y a ↔ IsInSpanAt (n := m + 1) (· = g ∘ π) y a :=
    fun a => MemberPullback.pullback_mem_iff_of_generator hπ.1 hg hgen a
  let e := (complexChartAt (n := m + 1) y).val
  have hyE : y ∈ e.source := mem_complexChartAt_source y
  have ht : Tendsto (fun z : ComplexModel (m + 1) => z + e y) (𝓝 0) (𝓝 (e y)) :=
    (continuous_add_const (e y)).tendsto' 0 (e y) (zero_add _)
  have hchart : Tendsto (fun z : ComplexModel (m + 1) => e.symm (z + e y)) (𝓝 0) (𝓝 y) := by
    simpa only [Function.comp_def, e.left_inv hyE] using
      (e.continuousAt_symm (e.map_source hyE)).tendsto.comp ht
  have hchartcont : ContinuousAt (fun z : ComplexModel (m + 1) => e.symm (z + e y)) 0 := by
    simpa only [ContinuousAt, zero_add, e.left_inv hyE] using hchart
  have hRcomp : BoundedRealGermAt (fun z => R (π z)) y :=
    hR.comp_continuousAt hπ.1.continuous.continuousAt
  have hRcoord : BoundedRealGermAt
      (fun z : ComplexModel (m + 1) => R (π (e.symm (z + e y)))) 0 := by
    have hR0 : BoundedRealGermAt (fun z => R (π z)) (e.symm (0 + e y)) := by
      simpa only [zero_add, e.left_inv hyE] using hRcomp
    exact hR0.comp_continuousAt
      (F := fun z : ComplexModel (m + 1) => e.symm (z + e y)) (y := 0) hchartcont
  have hmap : Tendsto (fun z : ComplexModel (m + 1) => π (e.symm (z + e y)))
      (𝓝 0) (𝓝 (π y)) := hπ.1.continuous.continuousAt.tendsto.comp hchart
  have hpotential : (fun z => u (π (e.symm (z + e y)))) =ᶠ[𝓝 0]
      fun z => ((c : ℝ) : EReal) * logNormSq ((g ∘ π) (e.symm (z + e y))) +
        (R (π (e.symm (z + e y))) : EReal) := hmap.eventually hsource
  obtain ⟨S, r, hr, hRdata, hpos, ⟨T, hyT, hcover⟩, b, hb, hrep⟩ :=
    exists_cartier_geometric_log_remainder Δ y (g ∘ π) hgcomp hgencomp c hc
      (fun z => u (π (e.symm (z + e y)))) (fun z => R (π (e.symm (z + e y)))) hRcoord hpotential
  exact ⟨hsupport, S, r, hr, hRdata, hpos,
    ⟨T, hyT, fun z hz => by simpa only [← hsupport] using hcover z hz⟩, b, hb, hrep⟩

end SGPT.PSH
