import SGPT.Trace.BertiniNativeCanonicalFiberResidue
import SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! Exact native derivative readback in any original target chart.
This retains the original native map and native tangent structures.
-/

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
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]

/-- The coordinate derivative with original preferred source chart is
exactly the original native map differential followed by the original
target chart differential. No native/coordinate derivative certificate. -/
theorem coordinateMap_fderiv_preferred_source
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) X Y ∞)
    (x : X) (c : ComplexChart m Y) (hcx : f x ∈ c.val.source) :
    fderiv ℂ (coordinateMap f (complexChartAt (n := n) x) c)
      ((complexChartAt (n := n) x).val x) =
      (mfderiv 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) c.val (f x)).comp
        (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) f x) := by
  have hf := (f.contMDiff x).mdifferentiableAt (by simp)
  have hc := mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel m)) c.property hcx
  have hg := hc.comp x hf
  have hcoord : mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) (c.val ∘ f) x =
      fderiv ℂ (coordinateMap f (complexChartAt (n := n) x) c)
        ((complexChartAt (n := n) x).val x) := by
    simp only [mfderiv, writtenInExtChartAt, complexChartAt, mfld_simps,
      fderivWithin_univ, coordinateMap, Function.comp_def]
    rw [if_pos (show MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m)
      (fun y => c.val (f y)) x from hg)]
  exact hcoord.symm.trans (mfderiv_comp x hc hf)

theorem coordinateMap_fderiv_preferred_source_apply
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) X Y ∞)
    (x : X) (c : ComplexChart m Y) (hcx : f x ∈ c.val.source)
    (v : TangentSpace 𝓘(ℂ, ComplexModel n) x) :
    fderiv ℂ (coordinateMap f (complexChartAt (n := n) x) c)
        ((complexChartAt (n := n) x).val x) v =
      nativeOriginalChartTangentEquiv c (f x) hcx
        (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) f x v) := by
  rw [coordinateMap_fderiv_preferred_source f x c hcx]
  change (mfderiv 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) c.val (f x))
    ((mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) f x) v) = _
  exact (nativeOriginalChartTangentEquiv_apply c (f x) hcx _).symm

end SGPT.Trace.Bertini
