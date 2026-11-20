import SGPT.Foundations.Analysis.Pending.ChartPartition
import SGPT.Foundations.Analysis.Pending.SingularSmoothTestStokes
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorMass

set_option autoImplicit false

/-! # A genuine global bounded Kähler negative well on an actual chart compact

Independent compact smooth domination and zero extension construction.
The relative/global capacity comparison remains a separate consumer.
No cutoff, curvature or well witness is an input; all dimensions are retained.
-/

open Set Filter TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.ActualChartCapacityNegativeWell

open FirstPass FirstPass.PositiveClasses ChartPartition

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Genuine compact smooth domination produces the global bounded negative well
and its scaling parameter from the actual chart compact set alone. -/
theorem exists_chart_negative_well (omega : KahlerBackground n M)
    (e : ComplexChart n M) {D : Opens (ComplexModel n)}
    (hDt : (D : Set (ComplexModel n)) ⊆ e.val.target)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ δ : ℝ, 0 < δ ∧ 3 * δ ≤ 1 ∧ ∃ χ : M → ℝ,
      ChartSmooth (n := n) χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      tsupport χ ⊆ e.val.source ∩ e.val ⁻¹' (D : Set (ComplexModel n)) ∧
      (∀ z ∈ K, χ (e.val.symm z) = 1) ∧
      IsThetaPshPotential omega.form.val (fun x => ((-3 * δ * χ x : ℝ) : EReal)) ∧
      (∀ x, (-1 : EReal) ≤ ((-3 * δ * χ x : ℝ) : EReal) ∧
        ((-3 * δ * χ x : ℝ) : EReal) ≤ 0) := by
  obtain ⟨V, hVo, hKV, hVD, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK D.isOpen hKD
  obtain ⟨β, hβ, hβ1, hβsupp, hβ01⟩ := LocalBedfordTaylorMass.exists_cutoff_unit hK hVo hKV
  have hβc : HasCompactSupport β := hVc.of_isClosed_subset (isClosed_tsupport β)
    (hβsupp.trans subset_closure)
  have hβD : tsupport β ⊆ (D : Set (ComplexModel n)) := hβsupp.trans (subset_closure.trans hVD)
  let χ : M → ℝ := chartExtend e β
  have hχ : ChartSmooth (n := n) χ := chartSmooth_chartExtend e hβ hβc (hβD.trans hDt)
  have hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1 := fun x =>
    ⟨chartExtend_nonneg (fun z => (hβ01 z).1) x,
      chartExtend_le_one (fun z => (hβ01 z).2) x⟩
  have hχsupp : tsupport χ ⊆ e.val.source ∩ e.val ⁻¹' (D : Set (ComplexModel n)) := by
    have himg : IsCompact (e.val.symm '' tsupport β) :=
      hβc.image_of_continuousOn (e.val.symm.continuousOn.mono (hβD.trans hDt))
    have hs : tsupport χ ⊆ e.val.symm '' tsupport β :=
      (support_chartExtend_subset e).trans (by rw [himg.isClosed.closure_eq])
    rintro x hx
    obtain ⟨z, hz, rfl⟩ := hs hx
    exact ⟨e.val.map_target (hDt (hβD hz)), by
      rw [mem_preimage, e.val.right_inv (hDt (hβD hz))]
      exact hβD hz⟩
  have hχK : ∀ z ∈ K, χ (e.val.symm z) = 1 := by
    intro z hz
    change chartExtend e β (e.val.symm z) = 1
    rw [chartExtend_of_mem (e.val.map_target (hDt (hKD hz))),
      e.val.right_inv (hDt (hKD hz))]
    exact hβ1 z hz
  have hneg : ChartSmooth (n := n) (fun x => -χ x) := fun e' => (hχ e').neg
  obtain ⟨A, hA, hPSH, _hzero, _htype⟩ :=
    SingularSmoothTestStokes.exists_smooth_test_background omega (fun x => -χ x) hneg
  let δ : ℝ := 1 / (3 * (A + 1))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hprod : 3 * δ * (A + 1) = 1 := by
    dsimp only [δ]
    field_simp
  have h3δ : 3 * δ ≤ 1 := by nlinarith
  have hrem : 0 ≤ 1 - (3 * δ) * A := by nlinarith
  have hscaled := RestrictedApproximantComparison.isThetaPshPotential_smul hPSH
    (by positivity : 0 < 3 * δ)
  have hform : (3 * δ) • (A • omega.form) + (1 - (3 * δ) * A) • omega.form = omega.form := by
    rw [smul_smul, ← add_smul]
    have hh : (3 * δ) * A + (1 - (3 * δ) * A) = 1 := by ring
    rw [hh, one_smul]
  have hwell : IsThetaPshPotential omega.form.val (fun x => ((-3 * δ * χ x : ℝ) : EReal)) := by
    have hh : IsThetaPshPotential
        ((3 * δ) • (A • omega.form) + (1 - (3 * δ) * A) • omega.form).val
        (fun x => ((3 * δ : ℝ) : EReal) * ((-χ x : ℝ) : EReal)) :=
      ⟨LocalPotentials.thetaPlurisubharmonic_add_of_semipositive hscaled.1
        (KahlerDomination.isSemipositive_smul omega.isSemipositive hrem), hscaled.2⟩
    rw [hform] at hh
    have heq : (fun x => ((3 * δ : ℝ) : EReal) * ((-χ x : ℝ) : EReal)) =
        (fun x => ((-3 * δ * χ x : ℝ) : EReal)) := by
      funext x
      rw [← EReal.coe_mul]
      congr 1
      ring
    rwa [heq] at hh
  refine ⟨δ, hδ, h3δ, χ, hχ, hχ01, hχsupp, hχK, hwell, fun x => ?_⟩
  have hh := hχ01 x
  constructor
  · change ((-1 : ℝ) : EReal) ≤ _
    apply EReal.coe_le_coe_iff.mpr
    nlinarith
  · change _ ≤ ((0 : ℝ) : EReal)
    apply EReal.coe_le_coe_iff.mpr
    nlinarith

end
end SGPT.Foundations.Analysis.Pending.ActualChartCapacityNegativeWell
