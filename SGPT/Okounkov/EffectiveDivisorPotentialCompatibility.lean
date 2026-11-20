import SGPT.Okounkov.EffectiveDivisorTrace

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov

open Set Filter
open scoped Manifold ContDiff NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending IdealWeightPowers
open SourceTraceRepresentativeDefinition NaturalSubmanifoldSourceTraceDefinition

/-- Genuine finite-dimensional induction identifies the independently
constructed integer divisor recursion with the original potential vector. -/
theorem originalPotentialFlagValuation_of_originalCartierFlagValuation :
    ∀ (n : ℕ) (F : OriginalFlagGeometry.{u} n)
      (D : EffectiveDivisor n F.carrier) (ED : MeteredEffectiveQDivisor n F.carrier),
      DivisorMetric.IsDivisorMetric D ED →
      ∀ ν : Fin n → ℕ, OriginalCartierFlagValuation n F D ν →
        OriginalPotentialFlagValuation n F ED.weight (fun i => (ν i : ℝ≥0)) := by
  intro n
  induction n with
  | zero =>
      intro F D ED hED ν hν
      trivial
  | succ m ih =>
      intro F D ED hED ν hν
      obtain ⟨Dtail, hC, hνtail⟩ := hν
      obtain ⟨R, ha, hDR, hnot, hDtail⟩ := hC
      obtain ⟨L, hLI, EL, _hELsup, hEL, _hnormal⟩ :=
        exists_normalized_smooth_divisor_metric_normal_forms F.firstDivisor
      obtain ⟨ER, hERsup, hER⟩ := DivisorMetric.exists_divisorMetric R
      have hhead := sourceGeneric_effectiveDivisorMetric_eq_integer_order
        F.firstDivisor D L R hLI (ν 0) (by simpa only [hLI] using hDR)
          hnot ED EL ER hED hEL hER hERsup
      have hu := isThetaPshPotential_effectiveDivisorMetric D ED hED
      obtain ⟨τ, hstep, β, hβτ⟩ := exists_originalFlagStep_and_target_potential F hu
      obtain ⟨ET, _hETsup, hET⟩ := DivisorMetric.exists_divisorMetric Dtail
      have hclass := originalFlagStep_effectiveDivisorMetric_target_iEquivalent
        F D ED hED ⟨R, ha, hDR, hnot, hDtail⟩ hstep ET hET
      have htail := ih F.tail Dtail ET hET (fun i => ν i.succ) hνtail
      obtain ⟨μ, hμ⟩ := exists_originalPotentialFlagValuation m F.tail β τ hβτ
      have hμeq := originalPotentialFlagValuation_eq_of_iEquivalent
        m F.tail τ ET.weight μ (fun i => (ν i.succ : ℝ≥0)) hμ htail hclass
      rw [hμeq] at hμ
      exact ⟨by simp only [hhead, ENNReal.toNNReal_natCast], τ, hstep, hμ⟩

/-- The independent actual Cartier integer vector is unique, through the
checked original potential recursion and injective natural cast. -/
theorem originalCartierFlagValuation_unique {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (D : EffectiveDivisor n F.carrier) {ν μ : Fin n → ℕ}
    (hν : OriginalCartierFlagValuation n F D ν)
    (hμ : OriginalCartierFlagValuation n F D μ) : ν = μ := by
  obtain ⟨ED, _hEDsup, hED⟩ := DivisorMetric.exists_divisorMetric D
  have hνP := originalPotentialFlagValuation_of_originalCartierFlagValuation n F D ED hED ν hν
  have hμP := originalPotentialFlagValuation_of_originalCartierFlagValuation n F D ED hED μ hμ
  have hcast := originalPotentialFlagValuation_eq_of_iEquivalent n F ED.weight ED.weight
    (fun i => (ν i : ℝ≥0)) (fun i => (μ i : ℝ≥0)) hνP hμP
      (IEquivalentOnManifold.refl ED.weight)
  funext i
  exact_mod_cast congrFun hcast i

end SGPT.Okounkov
