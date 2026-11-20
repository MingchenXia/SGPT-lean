import SGPT.Foundations.Analysis.FirstPass.TraceBackground
import SGPT.Foundations.Analysis.FirstPass.KahlerCurrentPerturbation
import SGPT.Foundations.Analysis.Pending.NefCoreKahlerCurrent

set_option autoImplicit false

/-! # An internally produced admissible target background with a uniform margin -/

open Set
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.AdmissibleTraceBackgroundMargin

open FirstPass FirstPass.PositiveClasses FirstPass.TraceBackground

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V] [CompactSpace V]

/-- Compact domination of the actual zeroth pulled-back background gives
one whole target Kähler form of margin for every antitone error term. -/
theorem exists_admissible_background_with_uniform_margin
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V)
    (θ : ClosedRealOneOneForm n M) {ε : ℕ → ℝ} (hε : Antitone ε) :
    ∃ C : ℝ, 0 < C ∧
      IsAdmissibleTraceBackground hι omega θ ε (C • omegaV.form) ∧
      ∀ j, (C • omegaV.form -
        ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form) - omegaV.form).val.IsSemipositive := by
  let γ : ℕ → ClosedRealOneOneForm k V :=
    fun j => ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form)
  obtain ⟨D, hD, hdom⟩ :=
    KahlerDomination.exists_pos_isSemipositive_add_smul omegaV (-γ 0)
  have hC : 0 < D + 1 := by linarith
  have hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsSemipositive :=
    ClosedRealOneOneForm.pullback_isSemipositive hι omega.isSemipositive
  have hmargin : ∀ j, ((D + 1) • omegaV.form - γ j - omegaV.form).val.IsSemipositive := by
    intro j
    have hsplit : (D + 1) • omegaV.form - γ j - omegaV.form =
        (-γ 0 + D • omegaV.form) +
          (ε 0 - ε j) • ClosedRealOneOneForm.pullback hι omega.form := by
      dsimp only [γ]
      rw [NefCoreKahlerCurrent.pullback_add_smul, NefCoreKahlerCurrent.pullback_add_smul]
      module
    rw [hsplit]
    have hscale := KahlerDomination.isSemipositive_smul hpull
      (sub_nonneg.mpr (hε (Nat.zero_le j)))
    intro e z hz v
    exact add_nonneg (hdom e z hz v) (hscale e z hz v)
  refine ⟨D + 1, hC, ⟨(KahlerBackground.smul hC omegaV).isKahler, ?_⟩, hmargin⟩
  intro j
  change ((D + 1) • omegaV.form - γ j).val.IsSemipositive
  have heq : (D + 1) • omegaV.form - γ j =
      ((D + 1) • omegaV.form - γ j - omegaV.form) + omegaV.form := by module
  rw [heq]
  intro e z hz v
  exact add_nonneg (hmargin j e z hz v) (omegaV.isSemipositive e z hz v)

end

end SGPT.Foundations.Analysis.Pending.AdmissibleTraceBackgroundMargin
