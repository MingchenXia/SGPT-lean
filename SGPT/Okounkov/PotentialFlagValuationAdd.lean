import SGPT.Okounkov.FlagTraceCombinations

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

private theorem actual_target_potential_of_originalFlagStep {m : ℕ}
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

/-- True original dimension induction gives actual vector addition.
The genuine original sum step is produced internally and its arbitrary
target trace is compared by the already-produced sum trace class. -/
theorem originalPotentialFlagValuation_add :
    ∀ (n : ℕ) (F : OriginalFlagGeometry.{u} n)
      (θ σ : ClosedRealOneOneForm n F.carrier) (u v : F.carrier → EReal)
      (ν μ : Fin n → ℝ≥0),
      IsThetaPshPotential θ.val u → IsThetaPshPotential σ.val v →
      OriginalPotentialFlagValuation n F u ν →
      OriginalPotentialFlagValuation n F v μ →
      OriginalPotentialFlagValuation n F (fun x => u x + v x) (ν + μ) := by
  intro n
  induction n with
  | zero => intro F θ σ u v ν μ hu hv hν hμ; trivial
  | succ m ih =>
      intro F θ σ u v ν μ hu hv hν hμ
      obtain ⟨hν₀, τu, hTu, hνtail⟩ := hν
      obtain ⟨hμ₀, τv, hTv, hμtail⟩ := hμ
      have hsum := isThetaPshPotential_add_from_positive_sum hu hv
      obtain ⟨τs, hTs, βs, hβs⟩ := exists_originalFlagStep_and_target_potential F hsum
      obtain ⟨βu, hβu⟩ := actual_target_potential_of_originalFlagStep F hTu
      obtain ⟨βv, hβv⟩ := actual_target_potential_of_originalFlagStep F hTv
      have hsumtail := ih F.tail βu βv τu τv (fun i => ν i.succ) (fun i => μ i.succ)
        hβu hβv hνtail hμtail
      obtain ⟨δ, hδ⟩ := exists_originalPotentialFlagValuation m F.tail βs τs hβs
      have hI := originalFlagStep_add_target_iEquivalent F hTu hTv hTs
      have hδeq := originalPotentialFlagValuation_eq_of_iEquivalent m F.tail τs
        (fun y => τu y + τv y) δ ((fun i => ν i.succ) + (fun i => μ i.succ))
          hδ hsumtail hI
      have hhead : (ν + μ) 0 =
          (sourceGenericLelongNumber (n := m + 1)
            (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier)
            (fun x => u x + v x)).toNNReal := by
        rw [Pi.add_apply, hν₀, hμ₀,
          sourceGeneric_subtype_add_eq F.firstDivisor hu.quasiPshPotential hv.quasiPshPotential,
          ENNReal.toNNReal_add (sourceGeneric_subtype_ne_top F.firstDivisor hu.quasiPshPotential)
            (sourceGeneric_subtype_ne_top F.firstDivisor hv.quasiPshPotential)]
      refine ⟨hhead, τs, hTs, ?_⟩
      rw [hδeq] at hδ
      exact hδ

/-- The actual choice-independent assignment is additive on all genuine
original inputs, with the actual sum background and original EReal sum. -/
theorem potentialFlagValuation_add {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    {θ σ : ClosedRealOneOneForm n F.carrier} {u v : F.carrier → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v) :
    potentialFlagValuation F (isThetaPshPotential_add_from_positive_sum hu hv) =
      potentialFlagValuation F hu + potentialFlagValuation F hv :=
  originalPotentialFlagValuation_eq_of_iEquivalent n F (fun x => u x + v x)
    (fun x => u x + v x) _ _
      (potentialFlagValuation_spec F (isThetaPshPotential_add_from_positive_sum hu hv))
      (originalPotentialFlagValuation_add n F θ σ u v _ _ hu hv
        (potentialFlagValuation_spec F hu) (potentialFlagValuation_spec F hv))
      (IEquivalentOnManifold.refl _)

end SGPT.Okounkov
