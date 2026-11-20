import SGPT.PSH.SigmaNativeFormGluing
import SGPT.PSH.AtlasNefPullback

/-! Actual native epsilon potentials GLUE into ONE genuine global smooth
potential, proving the literal original nef criterion on the true sigma manifold. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology Manifold ContDiff Classical
universe u
variable {I : Type u} {C : I → Type u} [∀ c,TopologicalSpace (C c)] {n : I → ℕ}
  [∀ c,ChartedSpace (ComplexModel (n c)) (C c)] [∀ c,IsComplexManifold (n c) (C c)]

/-- Native globally smooth real potentials are an ACTUAL globally smooth
real function on the entire varying-dimensional disjoint union. -/
theorem sigma_glued_real_chartSmooth
    (h : ∀ c,C c → ℝ) (hh : ∀ c,ChartSmooth (n := n c) (h c)) :
    (sigmaNativeAtlas (n := n) (C := C)).ChartSmoothOn (fun p => h p.1 p.2) univ := by
  rintro ⟨c,e⟩
  change ContDiffOn ℝ ∞ (fun z => h c (e.val.symm z)) (e.val.target ∩ univ)
  rw [Set.inter_univ]
  exact hh c e

/-- For the SAME epsilon, actual native nef approximating potentials glue
into ONE actual global smooth original potential and prove EVERY original
chart/tangent-line inequality. No global nef flag or output certificate is
assumed: all its scalar smoothness and positivity fields are manufactured. -/
theorem sigma_original_nef_of_native
    (omega theta : AtlasClosedRealOneOneForm (sigmaNativeAtlas (n := n) (C := C)))
    (homega : ∀ c,(sigmaRestrictedForm omega c).val.IsKahler)
    (hnef : ∀ c,NefWithRespectTo ⟨sigmaRestrictedForm omega c,homega c⟩ (sigmaRestrictedForm theta c)) :
    OriginalNefWithRespectTo omega theta := by
  intro epsilon hepsilon
  choose h hh hpos using (fun c => hnef c epsilon hepsilon)
  refine ⟨fun p => h p.1 p.2,sigma_glued_real_chartSmooth h hh,?_⟩
  rintro ⟨c,e⟩ z hz
  exact hpos c e z hz

end SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
