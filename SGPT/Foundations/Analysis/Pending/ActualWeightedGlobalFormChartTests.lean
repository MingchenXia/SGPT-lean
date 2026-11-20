import SGPT.Foundations.Analysis.Pending.SlotFormCompactIBP
import SGPT.Foundations.Analysis.FirstPass.LocalCurrents

set_option autoImplicit false

/-! # Actual weighted global differential forms as whole-chart tests

The entire mathematical statement and proof preceded this source.
-/

noncomputable section

open Set TopologicalSpace Filter
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.ActualWeightedGlobalFormChartTests

open FirstPass

variable {n q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A genuine weighted global form supplies its native whole-chart test internally. -/
theorem exists_testForm (e : ComplexChart n M) (γ : SmoothRealForm n M q)
    (χ : M → ℝ) (hχ : ChartSmooth (n := n) χ)
    (hcompact : IsCompact (tsupport χ)) (hsource : tsupport χ ⊆ e.val.source) :
    ∃ η : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm
        (⟨e.val.target, e.val.open_target⟩ : Opens (ComplexModel n)) q,
      (∀ z, η z = e.val.target.indicator (fun y => χ (e.val.symm y) • γ.coeff e y) z) ∧
      tsupport (η : ComplexModel n → (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) ⊆
        e.val '' tsupport χ := by
  classical
  let K : Set (ComplexModel n) := e.val '' tsupport χ
  have hKcompact : IsCompact K :=
    hcompact.image_of_continuousOn (e.val.continuousOn.mono hsource)
  have hKtarget : K ⊆ e.val.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.val.map_source (hsource hx)
  let F : ComplexModel n → (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ :=
    e.val.target.indicator (fun z => χ (e.val.symm z) • γ.coeff e z)
  have hFK : tsupport F ⊆ K := by
    refine closure_minimal (fun z hz => ?_) hKcompact.isClosed
    have hzV : z ∈ e.val.target := by
      by_contra hnot
      exact hz (indicator_of_notMem hnot _)
    have hχz : χ (e.val.symm z) ≠ 0 := by
      intro hzero
      exact hz (by simp only [F, indicator_of_mem hzV, hzero, zero_smul])
    exact ⟨e.val.symm z, subset_tsupport _ hχz, e.val.right_inv hzV⟩
  have hFV : tsupport F ⊆ e.val.target := hFK.trans hKtarget
  have hFsmoothOn : ContDiffOn ℝ ∞ F e.val.target :=
    ((hχ e).smul (γ.smooth e)).congr fun z hz => indicator_of_mem hz _
  have hFsmooth : ContDiff ℝ ∞ F := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ e.val.target
    · exact hFsmoothOn.contDiffAt (e.val.open_target.mem_nhds hz)
    · have hzsupport : z ∉ tsupport F := fun h => hz (hFV h)
      have hzero : F =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [(isClosed_tsupport F).isOpen_compl.mem_nhds hzsupport] with y hy
        exact image_eq_zero_of_notMem_tsupport hy
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  let η : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm
      (⟨e.val.target, e.val.open_target⟩ : Opens (ComplexModel n)) q :=
    ⟨F, hFsmooth, hKcompact.of_isClosed_subset (isClosed_tsupport F) hFK, hFV⟩
  exact ⟨η, fun _ => rfl, hFK⟩

end SGPT.Foundations.Analysis.Pending.ActualWeightedGlobalFormChartTests
