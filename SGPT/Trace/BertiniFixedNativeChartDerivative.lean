import SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! Literal coordinate derivative in arbitrary fixed original source and
target charts, expressed using actual native manifold derivatives. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini

open Set Filter
open scoped Manifold ContDiff Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps

variable {n m : ℕ} {X Y : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]

theorem coordinateMap_fderiv_fixed_native_charts_apply
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) X Y ∞)
    (e : ComplexChart n X) (a : ComplexChart m Y) (x : X)
    (hex : x ∈ e.val.source) (hax : f x ∈ a.val.source) (v : ComplexModel n) :
    fderiv ℂ (coordinateMap f e a) (e.val x) v =
      (mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, ComplexModel m)) a.property).mfderiv hax
        (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) f x
          (((mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, ComplexModel n)) e.property).mfderiv hex).symm v)) := by
  let F := coordinateMap f e a
  let A := (mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, ComplexModel n)) e.property).mfderiv hex
  let B := (mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, ComplexModel m)) a.property).mfderiv hax
  have hz : e.val x ∈ coordinateDomain f e a := mem_coordinateDomain hex hax
  have hF : DifferentiableAt ℂ F (e.val x) :=
    (coordinateMap_contDiffAt f.contMDiff e a hz).differentiableAt (by simp)
  have he := mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel n)) e.property hex
  have ha := mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel m)) a.property hax
  have hf := (f.contMDiff x).mdifferentiableAt (by simp)
  have hleft := mfderiv_comp x hF.mdifferentiableAt he
  have hright := mfderiv_comp x ha hf
  have heq : (F ∘ e.val) =ᶠ[𝓝 x] (a.val ∘ f) := by
    filter_upwards [e.val.open_source.mem_nhds hex] with y hy
    exact coordinateMap_at hy
  have h := DFunLike.congr_fun hleft (A.symm v)
  rw [heq.mfderiv_eq, hright, mfderiv_eq_fderiv] at h
  change B (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) f x (A.symm v)) =
    fderiv ℂ F (e.val x) (A (A.symm v)) at h
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

end SGPT.Trace.Bertini
