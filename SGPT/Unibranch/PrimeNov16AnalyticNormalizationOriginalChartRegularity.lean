import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalChartVanishing
import SGPT.Foundations.Analysis.Pending.CodimOnePartCanonical
import SGPT.Foundations.Analysis.Pending.RegularAtDimChart

/-! Actual centered chart-germ regular points read back to the literal original carrier.
Blueprint: prime-nov16-analytic-normalization-original-chart-regularity.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalChartRegularity

def modelTranslation {n : ℕ} (a : ComplexModel n) :
    ComplexModel n ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ ComplexModel n where
  toEquiv := Equiv.addRight a
  contMDiff_toFun := contMDiff_id.add contMDiff_const
  contMDiff_invFun := contMDiff_id.sub contMDiff_const

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem original_regular_of_chartGerm (C : Set M) (x y : M)
    (hy : y ∈ (complexChartAt (n := n) x).val.source) {d : ℕ}
    (hr : RegularAtDim (n := n) (AnalyticDescendingChain.chartGerm (n := n) C x)
      ((complexChartAt (n := n) x).val y-(complexChartAt (n := n) x).val x) d) :
    RegularAtDim (n := n) C y d := by
  let e := complexChartAt (n := n) x
  let B : Set (ComplexModel n) := e.val.target ∩ e.val.symm ⁻¹' C
  let T := modelTranslation (e.val x)
  have hs : T ⁻¹' B=AnalyticDescendingChain.chartGerm (n := n) C x := rfl
  have hrB := (CodimOnePartCanonical.regularAtDim_preimage_iff T).mp (hs.symm ▸ hr)
  have hp : T (e.val y-e.val x)=e.val y := sub_add_cancel _ _
  rw [hp] at hrB
  change RegularAtDim (n := n) (e.val.target ∩ e.val.symm ⁻¹' C) (e.val y) d at hrB
  rw [Set.inter_comm] at hrB
  have hrA := (RegularAtDimChart.regularAtDim_chart_iff e (e.val.symm ⁻¹' C) hy).mpr hrB
  apply RegularPointDimension.regularAtDim_of_inter_eq e.val.open_source hy ?_ hrA
  ext v
  change ((v ∈ e.val.source ∧ e.val.symm (e.val v) ∈ C) ∧ v ∈ e.val.source) ↔
    v ∈ C ∧ v ∈ e.val.source
  constructor
  · rintro ⟨⟨hv,hCv⟩,_hv⟩
    exact ⟨by simpa only [e.val.left_inv hv] using hCv,hv⟩
  · rintro ⟨hCv,hv⟩
    exact ⟨⟨hv,by simpa only [e.val.left_inv hv] using hCv⟩,hv⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalChartRegularity
