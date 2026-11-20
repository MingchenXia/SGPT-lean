import SGPT.Okounkov.FlagCorrectionNonnegative
import SGPT.Okounkov.FlagTraceResidualSum
import SGPT.Okounkov.PotentialFlagValuationScaling

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending ThetaPshCodimTwoExtension
open SourceTraceRepresentativeDefinition NaturalSubmanifoldSourceTraceDefinition

/-- Genuine finite dimension induction identifies every actual potential
pullback vector with the same original geometric correction action. Actual
residuals, traces, divisor tails and all target memberships are manufactured. -/
theorem potentialFlagValuation_modification_eq_correctionNNReal :
    ∀ (n : ℕ) (F W : OriginalFlagGeometry.{u} n)
      (π : W.carrier → F.carrier) (hπ : IsFlagLifting F W π)
      (θ : ClosedRealOneOneForm n F.carrier) (u : F.carrier → EReal)
      (hu : IsThetaPshPotential θ.val u),
      potentialFlagValuation W
          (AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
            hπ.1 θ hu) =
        flagLiftingCorrectionNNReal n F W π hπ (potentialFlagValuation F hu) := by
  intro n
  induction n with
  | zero =>
      intro F W π hπ θ u hu
      funext i
      exact Fin.elim0 i
  | succ m ih =>
      intro F W π hπ θ u hu
      let hup := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
        hπ.1 θ hu
      obtain ⟨τ, hstep, β, hβ⟩ := exists_originalFlagStep_and_target_potential F hu
      obtain ⟨τup, hstepup, βup, hβup⟩ := exists_originalFlagStep_and_target_potential W hup
      have htailDown := potentialFlagValuation_tail_of_originalFlagStep F hu hstep hβ
      have htailUp := potentialFlagValuation_tail_of_originalFlagStep W hup hstepup hβup
      obtain ⟨_σ, _hrecorded, D, hDI, E, hEW, hE, hτ⟩ := hstep
      let c : ℝ≥0 := (sourceGenericLelongNumber (n := m + 1)
        (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) u).toNNReal
      let v := extensionAcross (F.flag (1 : Fin (m + 2))) (smoothDivisorOffResidual E c u)
      have hv := isThetaPshPotential_smooth_divisor_residual_of_unit_metric
        hu F.firstDivisor D hDI E hEW hE
      have hzero := sourceGeneric_smooth_divisor_residual_eq_zero
        hu F.firstDivisor D hDI E hEW hE hv
      change IsNaturalSourceTraceRepresentative F.omega F.firstDivisor v τ at hτ
      let : ChartedSpace (ComplexModel m) (W.flag (1 : Fin (m + 2))) := W.tail.charts
      obtain ⟨R, RT, η, hC, hη, hnot, hRI, ER, hERsup, hER,
          _hζ, _hζcur, ρ, hρ, hIup⟩ :=
        exists_recorded_unit_residual_trace_iEquivalent hπ hu D hDI E hEW hE hstepup
      obtain ⟨ET, _hETsup, hET⟩ := DivisorMetric.exists_divisorMetric RT
      have hIsum := iEquivalent_sourceTrace_lifted_residual_sum_tail
        hπ hv hzero hτ R RT hRI ER ET hERsup hER hET hnot c hρ
      have hI := hIup.trans hIsum
      have hτp := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
        hπ.tailMap_isFlagLifting.1 β hβ
      have hETp := isThetaPshPotential_effectiveDivisorMetric RT ET hET
      obtain ⟨hCET, hscale⟩ := exists_potentialFlagValuation_nonneg_smul W.tail hETp c
      have hsum := isThetaPshPotential_add_from_positive_sum hτp hCET
      have htarget := potentialFlagValuation_eq_of_iEquivalent W.tail hβup hsum hI
      have hETvalue : potentialFlagValuation W.tail hETp = fun i => (η i : ℝ≥0) :=
        originalPotentialFlagValuation_eq_of_iEquivalent m W.tail ET.weight ET.weight _ _
          (potentialFlagValuation_spec W.tail hETp)
          (originalPotentialFlagValuation_of_originalCartierFlagValuation m W.tail RT ET hET η hη)
          (IEquivalentOnManifold.refl ET.weight)
      have hrow : flagLiftingCorrectionRowNNReal hπ = fun i => (η i : ℝ≥0) :=
        flagLiftingCorrectionRowNNReal_eq_of_spec hπ ⟨D, hDI, RT, hC, η, hη, rfl⟩
      have hIH := ih F.tail W.tail hπ.tailMap hπ.tailMap_isFlagLifting β τ hβ
      rw [← htailDown] at hIH
      have hhead : potentialFlagValuation W hup 0 = potentialFlagValuation F hu 0 := by
        have huhead := (potentialFlagValuation_spec W hup).1
        have hdhead := (potentialFlagValuation_spec F hu).1
        exact huhead.trans ((congrArg ENNReal.toNNReal
          (hπ.sourceGeneric_first_comp_eq hu.quasiPshPotential)).trans hdhead.symm)
      have hFhead : potentialFlagValuation F hu 0 = c :=
        (potentialFlagValuation_spec F hu).1
      have htail : (fun i => potentialFlagValuation W hup i.succ) =
          fun i => flagLiftingCorrectionNNReal m F.tail W.tail hπ.tailMap
            hπ.tailMap_isFlagLifting (fun j => potentialFlagValuation F hu j.succ) i +
            potentialFlagValuation F hu 0 * flagLiftingCorrectionRowNNReal hπ i := by
        calc
          _ = potentialFlagValuation W.tail hβup := htailUp
          _ = potentialFlagValuation W.tail hsum := htarget
          _ = potentialFlagValuation W.tail hτp + potentialFlagValuation W.tail hCET :=
            potentialFlagValuation_add W.tail hτp hCET
          _ = _ := by
            rw [hIH, hscale, hETvalue, hrow, hFhead]
            rfl
      change potentialFlagValuation W hup = _
      rw [flagLiftingCorrectionNNReal_succ]
      funext i
      exact Fin.cases hhead (fun j => congrFun htail j) i

end SGPT.Okounkov
