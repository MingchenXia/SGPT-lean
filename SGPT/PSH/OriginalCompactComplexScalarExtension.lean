import SGPT.PSH.OriginalGlobalOneZeroAlgebra
import SGPT.PSH.OriginalCompactScalarExtension
import SGPT.Foundations.Analysis.Pending.ManifoldHolderSpace

/-! Genuine complex smooth chart scalars globalized on arbitrary compact K. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.ComplexCurrentBridge
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.ComplexCurrentDraft
open scoped Topology Distributions ContDiff
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] (A : VariableComplexAtlas X)

/-- Actual compact cutoffs and the frozen actual scalar zero-extension
producer manufacture a GENUINE global complex smooth scalar equal to any
prescribed chart-smooth scalar on K. No extension/output certificate. -/
theorem global_complex_smooth_scalar_on_compact (i : A.Index)
    (K : Compacts (ComplexModel (A.dimension i))) (hKU : (K : Set _)⊆(A.chart i).target)
    (a : ComplexModel (A.dimension i) → ℂ)
    (ha : ContDiffOn ℝ ∞ a (A.chart i).target) :
    ∃ f : X → ℂ,OriginalComplexSmooth A f ∧ ∀ z∈(K : Set _),f ((A.chart i).symm z)=a z := by
  let U : Opens (ComplexModel (A.dimension i)) := ⟨(A.chart i).target,(A.chart i).open_target⟩
  obtain ⟨chi,hchis,hchic,hchiU,hchi1⟩ :=
    SGPT.Foundations.Analysis.Pending.exists_contDiff_eq_one_of_isCompact K.isCompact U.isOpen hKU
  let chiTest : 𝓓(U,ℝ) := ⟨chi,hchis,hchic,hchiU⟩
  let gr : 𝓓(U,ℝ) := smoothMulTest U.isOpen (Complex.reCLM.contDiff.comp_contDiffOn ha)
    chiTest chiTest.tsupport_subset
  let gi : 𝓓(U,ℝ) := smoothMulTest U.isOpen (Complex.imCLM.contDiff.comp_contDiffOn ha)
    chiTest chiTest.tsupport_subset
  let fr := originalCompactScalarExtension A i gr
  let fi := originalCompactScalarExtension A i gi
  have hfr : OriginalRealSmooth A fr := originalCompactScalarExtension_smooth A i gr
  have hfi : OriginalRealSmooth A fi := originalCompactScalarExtension_smooth A i gi
  refine ⟨fun x => (fr x : ℂ)+Complex.I*(fi x : ℂ),complex_smooth_of_real_pair A fr fi hfr hfi,?_⟩
  intro z hzK
  change (originalCompactScalarExtension A i gr ((A.chart i).symm z) : ℂ)+
    Complex.I*(originalCompactScalarExtension A i gi ((A.chart i).symm z) : ℂ)=a z
  rw [originalCompactScalarExtension_coordinate A i gr (hKU hzK),
    originalCompactScalarExtension_coordinate A i gi (hKU hzK)]
  change ((chi z*(a z).re : ℝ) : ℂ)+Complex.I*((chi z*(a z).im : ℝ) : ℂ)=a z
  rw [hchi1 z hzK]
  apply Complex.ext <;> simp

end SGPT.PSH.ComplexCurrentBridge
