import SGPT.Okounkov.EffectiveDivisorResidual
import SGPT.Okounkov.OriginalFlagGeometry
import SGPT.Foundations.Analysis.Pending.SubmanifoldDivisorRestriction

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov

open Set Filter
open scoped Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending DivisorExponent IdealWeightPowers RestrictedIdealQuotient

/-- Independent actual divisor-side step: remove the maximal integer
component order and pull the effective residual ideal to the true tail. -/
def OriginalCartierFlagStep {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    (D : EffectiveDivisor (m + 1) F.carrier) (a : ℕ)
    (Dtail : EffectiveDivisor m F.tail.carrier) : Prop :=
  letI : ChartedSpace (ComplexModel m) (F.flag (1 : Fin (m + 2))) := F.tail.charts
  ∃ R : EffectiveDivisor (m + 1) F.carrier,
    (∀ x ∈ F.flag (1 : Fin (m + 2)), ∀ r : ℕ,
      IsDivNear (m + 1) D.ideal (F.flag (1 : Fin (m + 2))) r x ↔ r ≤ a) ∧
    D.ideal = (idealPow (vanishingIdeal (n := m + 1) (F.flag (1 : Fin (m + 2)))) a).mul R.ideal ∧
    ¬ F.flag (1 : Fin (m + 2)) ⊆ R.support ∧
    Dtail.ideal = GermIdeal.pullback (m := m)
      (Subtype.val : F.tail.carrier → F.carrier) R.ideal

/-- The original Cartier ideal and actual source flag internally produce
the genuine effective residual on its true inherited tail manifold. -/
theorem exists_originalCartierFlagStep {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    (D : EffectiveDivisor (m + 1) F.carrier) :
    ∃ (a : ℕ) (Dtail : EffectiveDivisor m F.tail.carrier), OriginalCartierFlagStep F D a Dtail := by
  let : ChartedSpace (ComplexModel m) (F.flag (1 : Fin (m + 2))) := F.tail.charts
  let : IsComplexManifold m (F.flag (1 : Fin (m + 2))) := F.tail.complex
  obtain ⟨a, R, ha, hDR, hnot⟩ := exists_effectiveDivisor_residual_smooth_component F.firstDivisor D
  have hval : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel (m + 1)) ∞
      (Subtype.val : F.tail.carrier → F.carrier) :=
    SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ m) F.firstDivisor.2.2
  have hIR : IsInvertibleAlong (m + 1) (F.flag (1 : Fin (m + 2))) R.ideal :=
    SubmanifoldDivisorRestriction.isInvertibleAlong_of_isClosedConnectedSubmanifold
      F.firstDivisor R.isInvertible hnot
  let Dtail : EffectiveDivisor m F.tail.carrier :=
    SubmanifoldIdealRestriction.restrictDivisor hval hIR
  exact ⟨a, Dtail, R, ha, hDR, hnot, rfl⟩

/-- Independent integer divisor recursion on the original flag, using
actual ideal division and restriction rather than any current valuation. -/
def OriginalCartierFlagValuation : (n : ℕ) → (F : OriginalFlagGeometry.{u} n) →
    EffectiveDivisor n F.carrier → (Fin n → ℕ) → Prop
  | 0, _, _, _ => True
  | m + 1, F, D, ν => ∃ Dtail : EffectiveDivisor m F.tail.carrier,
      OriginalCartierFlagStep F D (ν 0) Dtail ∧
      OriginalCartierFlagValuation m F.tail Dtail (fun i => ν i.succ)

/-- Genuine Cartier component division and restriction manufacture the
whole finite integer vector, including the actual empty-dimensional base. -/
theorem exists_originalCartierFlagValuation :
    ∀ (n : ℕ) (F : OriginalFlagGeometry.{u} n) (D : EffectiveDivisor n F.carrier),
      ∃ ν : Fin n → ℕ, OriginalCartierFlagValuation n F D ν := by
  intro n
  induction n with
  | zero =>
      intro F D
      exact ⟨Fin.elim0, trivial⟩
  | succ m ih =>
      intro F D
      obtain ⟨a, Dtail, hstep⟩ := exists_originalCartierFlagStep F D
      obtain ⟨ν, hν⟩ := ih F.tail Dtail
      exact ⟨Fin.cons a ν, Dtail,
        by simpa only [Fin.cons_zero] using hstep,
        by simpa only [Fin.cons_succ] using hν⟩

end SGPT.Okounkov
