import SGPT.Okounkov.FlagTraceScaling
import SGPT.Okounkov.PotentialFlagValuationAdd
import SGPT.Okounkov.PotentialFlagValuationZero

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov
open Set Filter
open scoped Manifold ContDiff NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending ThetaPshCodimTwoExtension
open SourceTraceRepresentativeDefinition NaturalSubmanifoldSourceTraceDefinition

private theorem actual_target_potential_of_originalFlagStep_scaling {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) {u : F.carrier → EReal}
    {τ : F.tail.carrier → EReal} (hstep : OriginalFlagStep F u τ) :
    ∃ β : ClosedRealOneOneForm m F.tail.carrier, IsThetaPshPotential β.val τ := by
  obtain ⟨_θ, _hu, _D, _hDI, _E, _hEW, _hmetric, hτ⟩ := hstep
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) F.firstDivisor.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
    (Nat.le_succ m) F.firstDivisor.2.2
  unfold IsNaturalSourceTraceRepresentative at hτ
  obtain ⟨_hzero, _θ, _ε, _seq, _hqea, β, _hadm, hβτ, _hterms, _hlim⟩ := hτ
  exact ⟨β.form, hβτ⟩

/-- Genuine positive scalar dimension induction on the original source
relation. Every scaled trace and multiplier comparison is produced. -/
theorem originalPotentialFlagValuation_pos_smul :
    ∀ (n : ℕ) (F : OriginalFlagGeometry.{u} n)
      (θ : ClosedRealOneOneForm n F.carrier) (u : F.carrier → EReal)
      (ν : Fin n → ℝ≥0) (c : ℝ≥0),
      0 < c → IsThetaPshPotential θ.val u →
      OriginalPotentialFlagValuation n F u ν →
      OriginalPotentialFlagValuation n F (fun x => ((c : ℝ) : EReal) * u x) (c • ν) := by
  intro n
  induction n with
  | zero => intro F θ u ν c hc hu hν; trivial
  | succ m ih =>
      intro F θ u ν c hc hu hν
      have hcR : 0 < (c : ℝ) := hc
      obtain ⟨hν₀, τ, hT, hνtail⟩ := hν
      have hcu := RestrictedApproximantComparison.isThetaPshPotential_smul hu hcR
      obtain ⟨τc, hTc, βc, hβc⟩ := exists_originalFlagStep_and_target_potential F hcu
      obtain ⟨β, hβ⟩ := actual_target_potential_of_originalFlagStep_scaling F hT
      have hctail := ih F.tail β τ (fun i => ν i.succ) c hc hβ hνtail
      obtain ⟨δ, hδ⟩ := exists_originalPotentialFlagValuation m F.tail βc τc hβc
      have hI := originalFlagStep_pos_smul_target_iEquivalent F hcR hT hTc
      have hδeq := originalPotentialFlagValuation_eq_of_iEquivalent m F.tail τc
        (fun y => ((c : ℝ) : EReal) * τ y) δ (c • (fun i => ν i.succ)) hδ hctail hI
      have hhead : (c • ν) 0 =
          (sourceGenericLelongNumber (n := m + 1)
            (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier)
            (fun x => ((c : ℝ) : EReal) * u x)).toNNReal := by
        rw [Pi.smul_apply, smul_eq_mul, hν₀]
        have hscale := flagGenericLelong_smul_eq F.flag u (1 : Fin (m + 2)) hcR
        change sourceGenericLelongNumber (n := m + 1)
          (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier)
          (fun x => ((c : ℝ) : EReal) * u x) =
          ENNReal.ofReal (c : ℝ) * sourceGenericLelongNumber (n := m + 1)
            (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) u at hscale
        rw [hscale, ENNReal.toNNReal_mul, ENNReal.ofReal_coe_nnreal, ENNReal.toNNReal_coe]
      refine ⟨hhead, τc, hTc, ?_⟩
      rw [hδeq] at hδ
      exact hδ

/-- The actual assignment is positively homogeneous with the original
extended-real scalar product. -/
theorem potentialFlagValuation_pos_smul {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    {θ : ClosedRealOneOneForm n F.carrier} {u : F.carrier → EReal}
    (hu : IsThetaPshPotential θ.val u) {c : ℝ≥0} (hc : 0 < c) :
    potentialFlagValuation F
      (RestrictedApproximantComparison.isThetaPshPotential_smul hu (show 0 < (c : ℝ) from hc)) =
      c • potentialFlagValuation F hu :=
  originalPotentialFlagValuation_eq_of_iEquivalent n F
    (fun x => ((c : ℝ) : EReal) * u x) (fun x => ((c : ℝ) : EReal) * u x) _ _
      (potentialFlagValuation_spec F _)
      (originalPotentialFlagValuation_pos_smul n F θ u _ c hc hu (potentialFlagValuation_spec F hu))
      (IEquivalentOnManifold.refl _)

/-- All original nonnegative scalars, including the genuine zero potential,
produce their actual scaled potential and the literal finite-vector formula. -/
theorem exists_potentialFlagValuation_nonneg_smul {n : ℕ}
    (F : OriginalFlagGeometry.{u} n)
    {θ : ClosedRealOneOneForm n F.carrier} {u : F.carrier → EReal}
    (hu : IsThetaPshPotential θ.val u) (c : ℝ≥0) :
    ∃ hcu : IsThetaPshPotential ((c : ℝ) • θ).val
        (fun x => ((c : ℝ) : EReal) * u x),
      potentialFlagValuation F hcu = c • potentialFlagValuation F hu := by
  by_cases hc : c = 0
  · obtain ⟨hzero, hνzero⟩ := exists_potentialFlagValuation_zero F
    subst c
    have hzform : (0 : ℝ) • θ = (0 : ClosedRealOneOneForm n F.carrier) := zero_smul _ _
    have hzfun : (fun x => ((0 : ℝ) : EReal) * u x) =
        (fun _ : F.carrier => (0 : EReal)) := by
      funext x
      simp only [EReal.coe_zero, zero_mul]
    have hcu : IsThetaPshPotential ((0 : ℝ) • θ).val
        (fun x => ((0 : ℝ) : EReal) * u x) := by
      rw [hzform, hzfun]
      exact hzero
    have hI : IEquivalentOnManifold (n := n)
        (fun x => ((0 : ℝ) : EReal) * u x) (fun _ : F.carrier => (0 : EReal)) := by
      rw [hzfun]
      exact IEquivalentOnManifold.refl _
    refine ⟨hcu, ?_⟩
    have hvalue := potentialFlagValuation_eq_of_iEquivalent F hcu hzero hI
    exact (hvalue.trans hνzero).trans (zero_smul (ℝ≥0) (potentialFlagValuation F hu)).symm
  · have hcpos : 0 < c := lt_of_le_of_ne (show 0 ≤ c from zero_le) (Ne.symm hc)
    let hcu := RestrictedApproximantComparison.isThetaPshPotential_smul hu
      (show 0 < (c : ℝ) from hcpos)
    exact ⟨hcu, potentialFlagValuation_pos_smul F hu hcpos⟩

end SGPT.Okounkov
