import SGPT.Trace.BertiniFixedNativeChartDerivative
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! The LITERAL inverse of an actual holomorphic immersive homeomorphism
is holomorphic. Blueprint: complex-homeomorph-inverse.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Trace.Bertini

variable {n : ℕ} {X Y : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- The true inverse of the SAME actual homeomorphism is holomorphic,
from actual holomorphy and actual injective derivatives in equal dimensions. -/
theorem homeomorph_symm_contMDiff_of_mfderiv_injective (e : X ≃ₜ Y)
    (he : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e)
    (hD : ∀ x, Function.Injective
      (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) e x)) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm := by
  have hinv : ∀ x : X, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm (e x) := by
    intro x
    let c := complexChartAt (n := n) x
    let d := complexChartAt (n := n) (e x)
    have hc : x ∈ c.val.source := mem_complexChartAt_source x
    have hd : e x ∈ d.val.source := mem_complexChartAt_source (e x)
    let H : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) X Y ∞ := ⟨e, he⟩
    let F := coordinateMap e c d
    have hF : ContDiffAt ℂ ∞ F (c.val x) := coordinateMap_contDiffAt he c d (mem_coordinateDomain hc hd)
    let A := (mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, ComplexModel n)) c.property).mfderiv hc
    let B := (mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, ComplexModel n)) d.property).mfderiv hd
    have hread (v : ComplexModel n) : fderiv ℂ F (c.val x) v =
        B (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) e x (A.symm v)) :=
      coordinateMap_fderiv_fixed_native_charts_apply H c d x hc hd v
    have hi : Function.Injective (fderiv ℂ F (c.val x)) := by
      intro v w hvw
      apply A.symm.injective
      apply hD x
      apply B.injective
      exact (hread v).symm.trans (hvw.trans (hread w))
    have hb : Function.Bijective (fderiv ℂ F (c.val x)) :=
      ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩
    let T : ComplexModel n ≃L[ℂ] ComplexModel n :=
      ContinuousLinearEquiv.ofBijective (fderiv ℂ F (c.val x))
        (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hb.2)
    let Φ := c.val.symm.trans (e.toOpenPartialHomeomorph.trans d.val)
    have hsrc : c.val x ∈ Φ.source := by
      change c.val x ∈ c.val.target ∧
        (c.val.symm (c.val x) ∈ Set.univ ∧ e (c.val.symm (c.val x)) ∈ d.val.source)
      rw [c.val.left_inv hc]
      exact ⟨c.val.map_source hc, Set.mem_univ _, hd⟩
    have hval : Φ (c.val x) = d.val (e x) := coordinateMap_at hc
    have htgt : d.val (e x) ∈ Φ.target := hval ▸ Φ.map_source hsrc
    have hsymm : Φ.symm (d.val (e x)) = c.val x := by rw [← hval]; exact Φ.left_inv hsrc
    have hder : HasFDerivAt Φ (T : ComplexModel n →L[ℂ] ComplexModel n)
        (Φ.symm (d.val (e x))) := by
      rw [hsymm]
      exact (hF.differentiableAt (by simp)).hasFDerivAt
    have hFs : ContDiffAt ℂ ∞ Φ (Φ.symm (d.val (e x))) := hsymm.symm ▸ hF
    have hI : ContDiffAt ℂ ∞ Φ.symm (d.val (e x)) := Φ.contDiffAt_symm htgt hder hFs
    apply (contMDiffAt_iff_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas d.property)
      (IsManifold.subset_maximalAtlas c.property) hd (by simpa using hc)).mpr
    refine ⟨e.symm.continuous.continuousAt, ?_⟩
    simp only [mfld_simps, contDiffWithinAt_univ]
    exact hI
  intro y
  simpa only [e.apply_symm_apply] using hinv (e.symm y)

end SGPT.Projective.NumEq.CompleteIntersections
