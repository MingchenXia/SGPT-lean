import SGPT.Foundations.Analysis.Pending.LelongSuperlevelsNearSubvariety
import SGPT.Foundations.Analysis.Pending.ManifoldFiniteSpanChartTransport
import SGPT.Foundations.Analysis.Pending.HolomorphicGermAlgebra

set_option autoImplicit false

/-! # Whole prime readers of original point-centered holomorphic germs

The actual holomorphic map pulls back original germs to every point of the
whole prime. No globally holomorphic representative or incoming analytic
weight is required. The single norm logarithm retains its coefficient one
half relative to the squared singleton generator logarithm.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.PointCenteredHolomorphicPrimeReaders

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus

noncomputable section

private theorem preferred_holomorphic {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {F : M → ℂ} {x : M} (hF : HolomorphicAt n F x) :
    ∀ᶠ z in 𝓝 ((complexChartAt (n := n) x).val x),
      DifferentiableAt ℂ (fun w => F ((complexChartAt (n := n) x).val.symm w)) z := by
  have hspan := (ManifoldFiniteSpanChartTransport.isInSpanAt_comp_chartSymm_iff
    (mem_chart_source (ComplexModel n) x) (fun _ : Fin 1 => F) F).mp
      (InvertibleIdealQuotient.isInSpanAt_self ⟨0, rfl⟩ hF)
  exact hspan.1.mono fun _ hz => hz.differentiableAt

private theorem generatorLog_analytic_preferred {n s : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (G : Fin s → M → ℂ) {x : M} (hG : ∀ i, HolomorphicAt n (G i) x)
    {c : ℝ} (hc : 0 < c) :
    HasAnalyticSingularitiesSmoothOffPoleAt
      (chartFunction (fun y => (c : EReal) * generatorLog G y)
        (complexChartAt (n := n) x)) ((complexChartAt (n := n) x).val x) := by
  let e := complexChartAt (n := n) x
  let g : Fin s → ComplexModel n → ℂ := fun i z => G i (e.val.symm z)
  have hgh : ∀ i, ∀ᶠ z in 𝓝 (e.val x), DifferentiableAt ℂ (g i) z :=
    fun i => preferred_holomorphic (hG i)
  obtain ⟨U, hprops, hU, hxU⟩ := eventually_nhds_iff.mp (eventually_all.mpr hgh)
  refine ⟨c, s, g, hc, ⟨U, hU, hxU, fun i z hz =>
    ((hprops z hz) i).differentiableWithinAt⟩, fun _ => 0, ?_, ?_, ?_⟩
  · exact ⟨0, le_rfl, Eventually.of_forall fun _ => by simp⟩
  · exact Eventually.of_forall fun _ _ => contDiffAt_const
  · exact Eventually.of_forall fun z => by
      simp only [chartFunction, EReal.coe_zero, add_zero]
      rfl

private theorem half_singleton_generatorLog {X : Type*} (F : X → ℂ) (x : X) :
    ((1 / 2 : ℝ) : EReal) * generatorLog (fun _ : Fin 1 => F) x =
      ENNReal.log (ENNReal.ofReal ‖F x‖) := by
  rw [generatorLog_eq_log_sum]
  simp only [Fin.sum_univ_one]
  rw [ENNReal.ofReal_pow (norm_nonneg (F x)), ENNReal.log_pow]
  rw [← mul_assoc]
  change (((1 / 2 : ℝ) : EReal) * ((2 : ℝ) : EReal)) * _ = _
  rw [← EReal.coe_mul]
  norm_num

section Manifold

variable {n m : ℕ} {X Y : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y]

/-- Every original holomorphic germ in the family internally supplies its
analytic pullback germs along the whole point-centered prime. -/
theorem iInf_generatorLog_comp_eq_open_piece {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel n) ∞ π)
    (x : X) {s : ℕ} (G : Fin s → X → ℂ) (hG : ∀ i, HolomorphicAt n (G i) x)
    (V : ClosedIrreducibleAnalyticSubvariety (m + 1) Y)
    (hcenter : ∀ y ∈ V.carrier, π y = x) {c : ℝ} (hc : 0 < c) {U : Set Y}
    (hU : IsOpen U) (hVU : (V.carrier ∩ U).Nonempty) :
    (⨅ y ∈ V.carrier, lelongNumber (n := m + 1)
      (fun z => (c : EReal) * generatorLog G (π z)) y) =
      ⨅ y ∈ V.carrier ∩ U, lelongNumber (n := m + 1)
        (fun z => (c : EReal) * generatorLog G (π z)) y := by
  apply LelongSuperlevelsNearSubvariety.iInf_lelongNumber_eq_open_piece V _ hU hVU
  intro y hy
  have hcomp : ∀ i, HolomorphicAt (m + 1) (fun z => G i (π z)) y := by
    intro i
    have hGi : HolomorphicAt n (G i) (π y) := hcenter y hy ▸ hG i
    exact hGi.comp_contMDiff (Eventually.of_forall fun z => hπ.contMDiffAt)
  exact generatorLog_analytic_preferred (fun i z => G i (π z)) hcomp hc

/-- The literal original norm logarithm uses one half of its squared
singleton generator logarithm, including all zeros and infinite readers. -/
theorem iInf_log_norm_comp_eq_open_piece {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel n) ∞ π)
    (x : X) {F : X → ℂ} (hF : HolomorphicAt n F x)
    (V : ClosedIrreducibleAnalyticSubvariety (m + 1) Y)
    (hcenter : ∀ y ∈ V.carrier, π y = x) {U : Set Y}
    (hU : IsOpen U) (hVU : (V.carrier ∩ U).Nonempty) :
    (⨅ y ∈ V.carrier, lelongNumber (n := m + 1)
      (fun z => ENNReal.log (ENNReal.ofReal ‖F (π z)‖)) y) =
      ⨅ y ∈ V.carrier ∩ U, lelongNumber (n := m + 1)
        (fun z => ENNReal.log (ENNReal.ofReal ‖F (π z)‖)) y := by
  have h := iInf_generatorLog_comp_eq_open_piece hπ x (fun _ : Fin 1 => F)
    (fun _ => hF) V hcenter (c := 1 / 2) (by norm_num) hU hVU
  simpa only [half_singleton_generatorLog] using h

end Manifold

end

end SGPT.Foundations.Analysis.Pending.PointCenteredHolomorphicPrimeReaders
