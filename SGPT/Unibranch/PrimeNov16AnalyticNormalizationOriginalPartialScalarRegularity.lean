import SGPT.Unibranch.NativeNov16PartialBaseScalarSections
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalWindowFunctionGerm
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSectionDensity

/-! Actual smaller-window germs manufacture WHOLE old-carrier scalar regularity and density.
Blueprint: prime-nov16-analytic-normalization-original-partial-scalar-regularity.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory Opposite
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalPartialScalarRegularity
open NativeNov16PartialBaseScalarSections
open PrimeNov16AnalyticNormalizationOriginalWindowFunctionGerm
open PrimeNov16AnalyticNormalizationOriginalSectionDensity
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceResidue

theorem actual_partial_scalar_nonzero_dense {n : ℕ} (B : Set (ComplexModel n))
    (P Ω : Opens (ComplexModel n)) (hΩP : Ω ≤ P)
    (hP : IsComplexAnalyticSubset (n := n) ((Subtype.val : P → ComplexModel n) ⁻¹' B))
    (hΩ : IsComplexAnalyticSubset (n := n) ((Subtype.val : Ω → ComplexModel n) ⁻¹' B))
    (W : Opens (TopCat.of ((Subtype.val : P → ComplexModel n) ⁻¹' B)))
    (V : Set Ω) (F : ComplexModel n → ℂ) (hF : DifferentiableOn ℂ F Ω)
    (hland : ∀ p : ((Subtype.val : P → ComplexModel n) ⁻¹' B),p ∈ W → p.val.val ∈ Ω)
    (hWindow : ∀ p : ((Subtype.val : P → ComplexModel n) ⁻¹' B),∀ hp : p ∈ W,
      (⟨p.val.val,hland p hp⟩ : Ω) ∈ V)
    (hn : ∀ p : ((Subtype.val : Ω → ComplexModel n) ⁻¹' B),p.val ∈ V →
      originalFunctionImage _ p (fun y : Ω => F y.val)
        (function_holomorphicAt Ω Ω F hF p.val p.val.property) ≠ 0) :
    (∀ p : ((Subtype.val : P → ComplexModel n) ⁻¹' B),∀ hp : p ∈ W,
      (actualSubspaceSheaf (n := n) ((Subtype.val : P → ComplexModel n) ⁻¹' B)).presheaf.germ W p hp
        (scalarSection P ((Subtype.val : P → ComplexModel n) ⁻¹' B) W Ω F hF hland) ≠ 0) ∧
    Dense {p : W | F p.val.val.val ≠ 0} := by
  have hNZ : ∀ p : ((Subtype.val : P → ComplexModel n) ⁻¹' B),∀ hp : p ∈ W,
      (actualSubspaceSheaf (n := n) ((Subtype.val : P → ComplexModel n) ⁻¹' B)).presheaf.germ W p hp
        (scalarSection P ((Subtype.val : P → ComplexModel n) ⁻¹' B) W Ω F hF hland) ≠ 0 := by
    intro p hp
    rw [scalarSection_germ P _ hP W Ω F hF hland p hp]
    let q : ((Subtype.val : Ω → ComplexModel n) ⁻¹' B) := ⟨⟨p.val.val,hland p hp⟩,p.property⟩
    exact original_function_image_nonzero_of_smaller_window B Ω P hΩP hΩ hP q F
      (function_holomorphicAt Ω Ω F hF q.val q.val.property)
      (function_holomorphicAt P Ω F hF p.val (hland p hp)) (hn q (hWindow p hp))
  refine ⟨hNZ,?_⟩
  have hd := original_section_nonzero_dense ((Subtype.val : P → ComplexModel n) ⁻¹' B) W
    (scalarSection P ((Subtype.val : P → ComplexModel n) ⁻¹' B) W Ω F hF hland) hNZ
  convert hd using 1
  ext p
  have hv := scalarSection_value P ((Subtype.val : P → ComplexModel n) ⁻¹' B) W Ω F hF hland p
  change F p.val.val.val ≠ 0 ↔ actualSubspaceStalkEval _ p.val
    ((actualSubspaceSheaf (n := n) ((Subtype.val : P → ComplexModel n) ⁻¹' B)).presheaf.germ W p.val p.property
      (scalarSection P ((Subtype.val : P → ComplexModel n) ⁻¹' B) W Ω F hF hland)) ≠ 0
  exact ⟨fun h he => h (hv.symm.trans he),fun h he => h (hv.trans he)⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalPartialScalarRegularity
