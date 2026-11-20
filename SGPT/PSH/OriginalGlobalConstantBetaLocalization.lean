import SGPT.PSH.OriginalCompactScalarExtension
import SGPT.Foundations.Analysis.Pending.ManifoldHolderSpace

/-! Genuine source GLOBAL smooth (1,0) covectors equal any prescribed
constant chart covector on an arbitrary compact scalar-test support. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.ComplexCurrentDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.BookCurrent
open scoped Topology Distributions ContDiff
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] (A : VariableComplexAtlas X)

/-- Actual compact chart cutoffs, scalar zero extension, genuine all-chart
smoothness, and df−i df∘J PRODUCE a true GLOBAL source (1,0) form with the
prescribed entire constant covector on K. No beta-extension certificate. -/
theorem original_global_one_zero_constant_on_compact (i : A.Index)
    (K : Compacts (ComplexModel (A.dimension i))) (hKU : (K : Set _) ⊆ (A.chart i).target)
    (b : ComplexModel (A.dimension i) →L[ℂ] ℂ) :
    ∃ B : OriginalGlobalOneZeroForm A,∀ z∈(K : Set _),B.coeff i z=b := by
  let U : Opens (ComplexModel (A.dimension i)) := ⟨(A.chart i).target,(A.chart i).open_target⟩
  obtain ⟨V,hVo,hKV,hVU,hVc⟩ :=
    exists_open_between_and_isCompact_closure K.isCompact U.isOpen hKU
  obtain ⟨chi,hchis,hchic,hchiU,hchi1⟩ :=
    SGPT.Foundations.Analysis.Pending.exists_contDiff_eq_one_of_isCompact hVc U.isOpen hVU
  let chiTest : 𝓓(U,ℝ) := ⟨chi,hchis,hchic,hchiU⟩
  let g : 𝓓(U,ℝ) := smoothMulTest U.isOpen (reForm b).contDiff.contDiffOn chiTest chiTest.tsupport_subset
  let f := originalCompactScalarExtension A i g
  let hf := originalCompactScalarExtension_smooth A i g
  refine ⟨originalOneZeroOfRealSmooth A f hf,?_⟩
  intro z hzK
  have hcoord : (f ∘ (A.chart i).symm)=ᶠ[𝓝 z] g :=
    originalCompactScalarExtension_coordinate_eventually A i g (hKU hzK)
  have hlinear : (g : ComplexModel (A.dimension i) → ℝ)=ᶠ[𝓝 z] reForm b := by
    filter_upwards [hVo.mem_nhds (hKV hzK)] with y hy
    change chi y * reForm b y=reForm b y
    rw [hchi1 y (subset_closure hy),one_mul]
  change realCovectorComplexLift (fderiv ℝ (f ∘ (A.chart i).symm) z)=b
  rw [hcoord.fderiv_eq,hlinear.fderiv_eq]
  simpa using realCovectorComplexLift_reForm b

/-- Whole finite source beta family is internally globalized on the ACTUAL
compact scalar-test support, with no dimension positivity or connectedness. -/
theorem original_global_beta_family_constant_on_compact (i : A.Index)
    (K : Compacts (ComplexModel (A.dimension i))) (hKU : (K : Set _) ⊆ (A.chart i).target)
    (p : ℕ) (beta : Fin p → ComplexModel (A.dimension i) →L[ℂ] ℂ) :
    ∃ B : Fin p → OriginalGlobalOneZeroForm A,∀ j z,z∈(K : Set _) → (B j).coeff i z=beta j := by
  classical
  choose B hB using (fun j : Fin p => original_global_one_zero_constant_on_compact A i K hKU (beta j))
  exact ⟨B,fun j z hz => hB j z hz⟩

end SGPT.PSH.ComplexCurrentDraft
