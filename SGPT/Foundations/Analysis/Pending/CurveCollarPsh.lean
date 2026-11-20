import SGPT.Foundations.Analysis.Pending.CurveCollarBackground
import SGPT.Foundations.Analysis.Pending.LocalPotentials

set_option autoImplicit false

open Set

namespace SGPT.Foundations.Analysis.Pending.CurveCollarPsh

open FirstPass FirstPass.PositiveClasses ManifoldTubePositivity CurveCollarBackground

noncomputable section

/-- Actual normalized smooth curvature positivity gives a genuine strongly
nondegenerate finite potential, without any local-potential input. -/
theorem isThetaPshPotential_scaled_smooth_of_semipositive {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (a : ClosedRealOneOneForm n M) (ρ : M → ℝ) (hρ : ChartSmooth (n := n) ρ)
    (D : ℝ) (hpos : (a + D • ddcClosedForm ρ hρ).val.IsSemipositive) :
    IsThetaPshPotential a.val (fun x => ((D * ρ x : ℝ) : EReal)) := by
  have hsm : ChartSmooth (n := n) (fun x => D * ρ x) :=
    fun e => contDiffOn_const.mul (hρ e)
  refine ⟨(LocalPotentials.thetaPlurisubharmonic_smooth_iff a _ hsm).mpr ?_, ?_⟩
  · intro e z hz v
    change 0 ≤ a.val.coeff e z ![v, Complex.I • v] +
      smoothDDC (fun w => D • ρ (e.val.symm w)) z ![v, Complex.I • v]
    rw [smoothDDC_smul e.val.open_target (hρ e) D hz]
    simpa only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
      ddcClosedForm_coeff, ContinuousAlternatingMap.add_apply] using hpos e z hz v
  · intro x U _ hx
    exact ⟨x, hx, EReal.coe_ne_bot (D * ρ x)⟩

/-- The actual smooth correction is produced together with both compact curve
cutoffs and their genuine closed background. -/
theorem exists_curveCollarPsh {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel 1) M] [IsComplexManifold 1 M] [CompactSpace M]
    (ω : KahlerBackground 1 M) {K V₁ V₂ : Set M} (hK : IsCompact K)
    (hV₁ : IsOpen V₁) (hV₂ : IsOpen V₂) (hKV₁ : K ⊆ V₁)
    (hV₁V₂ : closure V₁ ⊆ V₂) (D : ℝ) (hD : 0 ≤ D) :
    ∃ (ρin ρout : M → ℝ) (hin : ChartSmooth (n := 1) ρin)
      (hout : ChartSmooth (n := 1) ρout) (C : ℝ),
      0 < C ∧ (∀ x, -1 ≤ ρin x) ∧ (∀ x, ρin x ≤ 0) ∧
      (∃ N : Set M, IsOpen N ∧ K ⊆ N ∧ ∀ x ∈ N, ρin x = 0) ∧
      (∀ x ∉ V₁, ρin x = -1) ∧
      (∀ x, -1 ≤ ρout x) ∧ (∀ x, ρout x ≤ 0) ∧
      (∃ N : Set M, IsOpen N ∧ closure V₁ ⊆ N ∧ ∀ x ∈ N, ρout x = 0) ∧
      (∀ x ∉ V₂, ρout x = -1) ∧
      (curveCollarBackground ω D C ρin hin).val.IsSemipositive ∧
      (curveCollarBackground ω D C ρin hin + D • ddcClosedForm ρout hout).val.IsSemipositive ∧
      IsThetaPshPotential (curveCollarBackground ω D C ρin hin).val
        (fun x => ((D * ρout x : ℝ) : EReal)) := by
  obtain ⟨ρin, ρout, hin, hout, C, hC, hinlow, hinup, hinN, hinoff,
    houtlow, houtup, houtN, houtoff, hκ, hpos⟩ :=
    exists_curveCollarBackground ω hK hV₁ hV₂ hKV₁ hV₁V₂ D hD
  exact ⟨ρin, ρout, hin, hout, C, hC, hinlow, hinup, hinN, hinoff,
    houtlow, houtup, houtN, houtoff, hκ, hpos,
    isThetaPshPotential_scaled_smooth_of_semipositive _ ρout hout D hpos⟩

end

end SGPT.Foundations.Analysis.Pending.CurveCollarPsh
