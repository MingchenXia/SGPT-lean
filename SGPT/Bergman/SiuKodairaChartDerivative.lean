import SGPT.Bergman.SiuKodairaNativeSection
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# The original manifold derivative in its actual preferred complex charts

In self-model complex manifolds the native manifold derivative is exactly
the genuine Fréchet derivative of its preferred-chart representative.
Blueprint: `siu-kodaira-embedding.tex`, node `siu-kodaira:section-map`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Bergman.SiuKodaira

open Set Filter Bundle
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {n m : ℕ} {X Y : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y]
  [IsComplexManifold m Y]

omit [IsComplexManifold n X] [IsComplexManifold m Y] in
/-- Exact original preferred-chart readback of the native complex differential. -/
theorem mfderiv_eq_fderiv_complexChartAt {f : X → Y} {p : X}
    (hf : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) f p) :
    mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) f p =
      fderiv ℂ (fun z => (complexChartAt (n := m) (f p)).val
        (f ((complexChartAt (n := n) p).val.symm z)))
        ((complexChartAt (n := n) p).val p) := by
  simp only [mfderiv, hf, if_pos, writtenInExtChartAt, complexChartAt, mfld_simps, fderivWithin_univ, Function.comp_def]

end SGPT.Bergman.SiuKodaira
