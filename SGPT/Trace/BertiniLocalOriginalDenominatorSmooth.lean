import SGPT.Trace.BertiniLocalOriginalChartNormal
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Actual original native smooth holomorphy of the original conormal
partial and reciprocal, with coordinate function produced from original p. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini

open Set Filter
open scoped Manifold ContDiff Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DerivativeIdeal
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace

variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (ζ : ComplexModel N) (j : Fin (N + 1))

theorem contDiffAt_nativeBertiniChartEquation (e : ComplexChart n X)
    {z : ComplexModel n} (hz : z ∈ chartLiftDomain p e j) :
    ContDiffAt ℂ ∞ (nativeBertiniChartEquation p i ζ j e) z := by
  have hG : DifferentiableOn ℂ (nativeBertiniChartEquation p i ζ j e) (chartLiftDomain p e j) := by
    intro w hw
    exact (hasFDerivAt_pairing_chartLift p p.contMDiff hw (affineLift i ζ)).differentiableAt.differentiableWithinAt
  exact contDiffAt_of_differentiableOn_complex hG (isOpen_chartLiftDomain p p.contMDiff e j) hz

theorem contMDiffAt_nativeBertiniChartPartial (e : ComplexChart n X) (m : Fin n) (x : X)
    (hex : x ∈ e.val.source) (hpx : p x ∈ (affineChart j).source) :
    ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞
      (chartDeriv e (EuclideanSpace.single m 1) (nativeBertiniLocalEquation p i ζ j)) x := by
  have hG := contDiffAt_nativeBertiniChartEquation p i ζ j e ((mem_chartLiftDomain_iff p hex).mpr hpx)
  have hD : ContDiffAt ℂ ∞ (fderiv ℂ (nativeBertiniChartEquation p i ζ j e)) (e.val x) :=
    hG.fderiv_right (by simp)
  have hpartial := hD.clm_apply (contDiffAt_const (c := EuclideanSpace.single m (1 : ℂ)))
  exact hpartial.contMDiffAt.comp x
    (contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas e.property) hex)

theorem contMDiffAt_nativeBertiniChartPartial_inv (e : ComplexChart n X) (m : Fin n) (x : X)
    (hex : x ∈ e.val.source) (hpx : p x ∈ (affineChart j).source)
    (hm : chartDeriv e (EuclideanSpace.single m 1) (nativeBertiniLocalEquation p i ζ j) x ≠ 0) :
    ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞
      (fun y => (chartDeriv e (EuclideanSpace.single m 1) (nativeBertiniLocalEquation p i ζ j) y)⁻¹) x :=
  (contMDiffAt_nativeBertiniChartPartial p i ζ j e m x hex hpx).inv₀ hm

end SGPT.Trace.Bertini
