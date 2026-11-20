import SGPT.Okounkov.OriginalFlagGeometry
import SGPT.Okounkov.SmoothDivisorTrace

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set Filter
open scoped Manifold ContDiff NNReal ENNReal
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending ThetaPshCodimTwoExtension
open SourceTraceRepresentativeDefinition NaturalSubmanifoldSourceTraceDefinition

/-- An actual original residual/plain-trace step, retaining every choice of
the genuine unit metric and source trace. No target value is supplied. -/
def OriginalFlagStep {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    (u : F.carrier → EReal) (τ : F.tail.carrier → EReal) : Prop :=
  ∃ θ : ClosedRealOneOneForm (m + 1) F.carrier, IsThetaPshPotential θ.val u ∧
    ∃ D : EffectiveDivisor (m + 1) F.carrier,
      D.ideal = vanishingIdeal (n := m + 1) (F.flag (1 : Fin (m + 2))) ∧
    ∃ E : MeteredEffectiveQDivisor (m + 1) F.carrier,
      E.support = F.flag (1 : Fin (m + 2)) ∧ DivisorMetric.IsDivisorMetric D E ∧
      IsNaturalSourceTraceRepresentative F.omega F.firstDivisor
        (extensionAcross (F.flag (1 : Fin (m + 2))) (smoothDivisorOffResidual E
          (sourceGenericLelongNumber (n := m + 1)
            (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) u).toNNReal u)) τ

/-- Literal original dimension recursion in the genuine computed tail flag.
The base is the unique vector on Fin 0; all actual plain-trace choices are
kept in the relation until the original independence theorem is proved. -/
def OriginalPotentialFlagValuation : (n : ℕ) → (F : OriginalFlagGeometry.{u} n) →
    (F.carrier → EReal) → (Fin n → ℝ≥0) → Prop
  | 0, _, _, _ => True
  | m + 1, F, u, ν =>
      ν 0 = (sourceGenericLelongNumber (n := m + 1)
        (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) u).toNNReal ∧
      ∃ τ : F.tail.carrier → EReal, OriginalFlagStep F u τ ∧
        OriginalPotentialFlagValuation m F.tail τ (fun i => ν i.succ)

/-- Original data produce a true residual/plain-trace step and a genuine
closed background for its target potential, internally and in every dimension. -/
theorem exists_originalFlagStep_and_target_potential {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {u : F.carrier → EReal}
    (hu : IsThetaPshPotential θ.val u) :
    ∃ τ : F.tail.carrier → EReal, OriginalFlagStep F u τ ∧
      ∃ β : ClosedRealOneOneForm m F.tail.carrier, IsThetaPshPotential β.val τ := by
  obtain ⟨D, hDI, E, hEW, hmetric, _hres, _hzero, τ, hτ⟩ :=
    exists_normalized_smooth_divisor_residual_sourceTrace F.omega hu F.firstDivisor
  have hstep : OriginalFlagStep F u τ := ⟨θ, hu, D, hDI, E, hEW, hmetric, hτ⟩
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) F.firstDivisor.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
    (Nat.le_succ m) F.firstDivisor.2.2
  unfold IsNaturalSourceTraceRepresentative at hτ
  obtain ⟨_hgen, _θ, _ε, _seq, _hqea, β, _hadm, hβτ, _hterms, _hlim⟩ := hτ
  exact ⟨τ, hstep, β.form, hβτ⟩

/-- Genuine original residual/trace existence at each step gives an actual
full finite vector. No recursive value or trace-existence certificate is an input. -/
theorem exists_originalPotentialFlagValuation :
    ∀ (n : ℕ) (F : OriginalFlagGeometry.{u} n)
      (θ : ClosedRealOneOneForm n F.carrier) (u : F.carrier → EReal),
      IsThetaPshPotential θ.val u →
        ∃ ν : Fin n → ℝ≥0, OriginalPotentialFlagValuation n F u ν := by
  intro n
  induction n with
  | zero =>
      intro F θ u hu
      exact ⟨Fin.elim0, trivial⟩
  | succ m ih =>
      intro F θ u hu
      obtain ⟨τ, hstep, β, hβτ⟩ := exists_originalFlagStep_and_target_potential F hu
      obtain ⟨ν, hν⟩ := ih F.tail β τ hβτ
      refine ⟨Fin.cons
        (sourceGenericLelongNumber (n := m + 1)
          (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) u).toNNReal ν, ?_⟩
      exact ⟨rfl, τ, hstep, by simpa only [Fin.cons_succ] using hν⟩

end SGPT.Okounkov
