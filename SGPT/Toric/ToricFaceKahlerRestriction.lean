import SGPT.Toric.ToricSourceTraceNewtonFace
import SGPT.Okounkov.TranscendentalWNKeyGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology Manifold ContDiff Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The ACTUAL native inclusion of every genuine orbit closure pulls back
any original Kähler form to a Kähler form. Full actual original submanifold
geometry and both proved holomorphic inverse maps produce this fact;
no target Kähler or immersion/model certificate is an input. -/
theorem isKahler_pullback_toricFaceSourceInclusion
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (κ : KahlerBackground n (PolytopeToricVariety γ hs)) :
    (ClosedRealOneOneForm.pullback (contMDiff_toricFaceSourceInclusion (hs := hs) v J) κ.form).val.IsKahler := by
  obtain ⟨e,i,he⟩ := exists_toricFlagSelectedIndices J
  subst J
  let := originalPolytopeNativeChartedSpace
    (toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e i))
    (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e i))
  let := originalPolytopeNativeIsComplexManifold
    (toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e i))
    (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e i))
  let := toricFaceFlagCharts (hs := hs) v e i
  let := toricFaceFlag_isComplexManifold (hs := hs) v e i
  let f := toricFaceFlagHomeomorph (hs := hs) v e i
  have hf := contMDiff_toricFaceFlagHomeomorph (hs := hs) v e i
  have hg := contMDiff_toricFaceFlagHomeomorph_symm (hs := hs) v e i
  let hval := contMDiff_toricFaceFlag_val (hs := hs) v e i
  have hKval : (ClosedRealOneOneForm.pullback hval κ.form).val.IsKahler :=
    SubmanifoldKahlerRestriction.isKahler_pullback (toricFaceFlag_dimension_le e i)
      (toricFaceFlag_regular (hs := hs) v e i) κ.form κ.isKahler
  have hKf := SGPT.Okounkov.TranscendentalWN.isKahler_pullback_of_leftInverse hf hg
    f.symm_apply_apply (ClosedRealOneOneForm.pullback hval κ.form) hKval
  have hgeo := SGPT.Okounkov.TranscendentalVolId.pullback_comp_geometricallyEq' hval hf κ.form.val
  have hK := hgeo.isKahler_iff.mpr hKf
  exact hK

end SGPT.Toric
