import SGPT.Okounkov.FlagDivisorCurrentCorrection
import SGPT.Okounkov.ThetaPotentialCurrentCombinations
import SGPT.Okounkov.CanonicalUnitResidualTrace
import SGPT.Foundations.Analysis.Pending.NefCoreKahlerCurrent

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Okounkov

open Set
open scoped Manifold ContDiff NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open GlobalCurrents CanonicalCurrentFrame NaturalThetaPshGeometricCurrent
open GlobalPositiveCurrentACRestriction
open SourceTraceRepresentativeDefinition NaturalSubmanifoldSourceTraceDefinition
open ThetaPshCodimTwoExtension

/-- Actual finite theta-current addition and unchanged closed-form pullback
linearity identify the entire pulled sum current, including exceptional terms. -/
theorem exists_thetaPotentialModificationCurrent_add {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π)
    {θ σ : ClosedRealOneOneForm (m + 1) F.carrier} {u v : F.carrier → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v) :
    ∃ huv : IsThetaPshPotential (θ + σ).val (fun x => u x + v x),
      thetaPotentialModificationCurrent hπ (θ + σ) (fun x => u x + v x) huv =
        thetaPotentialModificationCurrent hπ θ u hu +
          thetaPotentialModificationCurrent hπ σ v hv := by
  obtain ⟨huv, _hcur⟩ := exists_thetaPotentialCurrent_add hu hv
  have hup := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    hπ.1 θ hu
  have hvp := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    hπ.1 σ hv
  obtain ⟨_hsum, hsumcur⟩ := exists_thetaPotentialCurrent_add hup hvp
  have hform : ClosedRealOneOneForm.pullback hπ.1.1 (θ + σ) =
      ClosedRealOneOneForm.pullback hπ.1.1 θ + ClosedRealOneOneForm.pullback hπ.1.1 σ := by
    simpa only [one_smul] using NefCoreKahlerCurrent.pullback_add_smul hπ.1.1 θ σ 1
  refine ⟨huv, ?_⟩
  unfold thetaPotentialModificationCurrent
  simpa only [thetaPotentialCurrent, hform, Function.comp_def] using hsumcur

private theorem closedForm_pullback_smul_of_existing_algebra {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π) (c : ℝ) (θ : ClosedRealOneOneForm (m + 1) F.carrier) :
    ClosedRealOneOneForm.pullback hπ.1.1 (c • θ) =
      c • ClosedRealOneOneForm.pullback hπ.1.1 θ := by
  have halgebra {A : Type u} [AddCommGroup A] [Module ℝ A] (a : A) :
      a + (c - 1) • a = c • a := by
    calc
      a + (c - 1) • a = (1 : ℝ) • a + (c - 1) • a := by rw [one_smul]
      _ = (1 + (c - 1)) • a := (add_smul _ _ _).symm
      _ = c • a := by congr 1; ring
  have h := NefCoreKahlerCurrent.pullback_add_smul hπ.1.1 θ θ (c - 1)
  have hdown : θ + (c - 1) • θ = c • θ := halgebra θ
  have hup : ClosedRealOneOneForm.pullback hπ.1.1 θ +
      (c - 1) • ClosedRealOneOneForm.pullback hπ.1.1 θ =
      c • ClosedRealOneOneForm.pullback hπ.1.1 θ := halgebra _
  exact (congrArg (ClosedRealOneOneForm.pullback hπ.1.1) hdown.symm).trans (h.trans hup)

/-- Genuine nonnegative finite-current scaling, including zero, commutes
with the actual full theta-current modification constructor. -/
theorem exists_thetaPotentialModificationCurrent_nonneg_smul {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π)
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {u : F.carrier → EReal}
    (hu : IsThetaPshPotential θ.val u) {c : ℝ} (hc : 0 ≤ c) :
    ∃ hcu : IsThetaPshPotential (c • θ).val (fun x => (c : EReal) * u x),
      thetaPotentialModificationCurrent hπ (c • θ) (fun x => (c : EReal) * u x) hcu =
        c • thetaPotentialModificationCurrent hπ θ u hu := by
  obtain ⟨hcu, _hcur⟩ := exists_thetaPotentialCurrent_nonneg_smul hu hc
  have hup := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    hπ.1 θ hu
  obtain ⟨_hscaled, hscaledcur⟩ := exists_thetaPotentialCurrent_nonneg_smul hup hc
  refine ⟨hcu, ?_⟩
  unfold thetaPotentialModificationCurrent
  simpa only [thetaPotentialCurrent, closedForm_pullback_smul_of_existing_algebra hπ,
    Function.comp_def] using hscaledcur

/-- Actual pointwise residual recomposition and the whole unit-divisor
total transform produce a literal positive upstairs residual current. -/
theorem exists_thetaPotentialModificationCurrent_unit_residual_eq {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π)
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {u : F.carrier → EReal}
    (hu : IsThetaPshPotential θ.val u)
    (D : EffectiveDivisor (m + 1) F.carrier)
    (hDI : D.ideal = vanishingIdeal (n := m + 1) (F.flag (1 : Fin (m + 2))))
    (E : MeteredEffectiveQDivisor (m + 1) F.carrier)
    (hEW : E.support = F.flag (1 : Fin (m + 2)))
    (hE : DivisorMetric.IsDivisorMetric D E) (c : ℝ≥0)
    (hv : IsThetaPshPotential (θ - (c : ℝ) • E.curvature).val
      (extensionAcross (F.flag (1 : Fin (m + 2))) (smoothDivisorOffResidual E c u))) :
    letI : ChartedSpace (ComplexModel m) (W.flag (1 : Fin (m + 2))) := W.tail.charts
    ∃ (R : EffectiveDivisor (m + 1) W.carrier)
      (Dtail : EffectiveDivisor m W.tail.carrier) (ν : Fin m → ℕ),
      OriginalCartierFlagStep W
        (GermIdealTotalTransform.EffectiveDivisor.totalTransform
          hπ.1.1 hπ.interior_exceptional_eq_empty D) 1 Dtail ∧
      OriginalCartierFlagValuation m W.tail Dtail ν ∧
      ¬ W.flag (1 : Fin (m + 2)) ⊆ R.support ∧
      Dtail.ideal = GermIdeal.pullback (m := m)
        (Subtype.val : W.tail.carrier → W.carrier) R.ideal ∧
      thetaPotentialModificationCurrent hπ θ u hu -
          (c : ℝ) • smoothDivisorIntegrationCurrent W.firstDivisor =
        thetaPotentialModificationCurrent hπ (θ - (c : ℝ) • E.curvature)
          (extensionAcross (F.flag (1 : Fin (m + 2))) (smoothDivisorOffResidual E c u)) hv +
          (c : ℝ) • effectiveDivisorIntegrationCurrent W R ∧
      ∃ ER : MeteredEffectiveQDivisor (m + 1) W.carrier,
        ER.support = R.support ∧ DivisorMetric.IsDivisorMetric R ER ∧
        ∃ hζ : IsThetaPshPotential
            (ClosedRealOneOneForm.pullback hπ.1.1 (θ - (c : ℝ) • E.curvature) +
              (c : ℝ) • ER.curvature).val
            (fun z => extensionAcross (F.flag (1 : Fin (m + 2)))
              (smoothDivisorOffResidual E c u) (π z) + ((c : ℝ) : EReal) * ER.weight z),
          thetaPotentialModificationCurrent hπ θ u hu -
              (c : ℝ) • smoothDivisorIntegrationCurrent W.firstDivisor =
            thetaPotentialCurrent
              (ClosedRealOneOneForm.pullback hπ.1.1 (θ - (c : ℝ) • E.curvature) +
                (c : ℝ) • ER.curvature).val
              (fun z => extensionAcross (F.flag (1 : Fin (m + 2)))
                (smoothDivisorOffResidual E c u) (π z) + ((c : ℝ) : EReal) * ER.weight z) hζ := by
  let : ChartedSpace (ComplexModel m) (W.flag (1 : Fin (m + 2))) := W.tail.charts
  let v := extensionAcross (F.flag (1 : Fin (m + 2))) (smoothDivisorOffResidual E c u)
  let DA := GermIdealTotalTransform.EffectiveDivisor.totalTransform
    hπ.1.1 hπ.interior_exceptional_eq_empty D
  have hw := isThetaPshPotential_effectiveDivisorMetric D E hE
  obtain ⟨hcw, hcwcur⟩ := exists_thetaPotentialModificationCurrent_nonneg_smul hπ hw c.coe_nonneg
  obtain ⟨_hsum, hsumcur⟩ := exists_thetaPotentialModificationCurrent_add hπ hv hcw
  have hweightcur :=
    thetaPotentialModificationCurrent_effectiveDivisorMetric_eq_canonicalTotalTransform hπ D E hE
  have hrecompose := smooth_divisor_residual_recompose hu F.firstDivisor E hEW c hv
  have hsplit : thetaPotentialModificationCurrent hπ θ u hu =
      thetaPotentialModificationCurrent hπ (θ - (c : ℝ) • E.curvature) v hv +
        (c : ℝ) • effectiveDivisorIntegrationCurrent W DA := by
    simpa only [sub_add_cancel, hrecompose, hcwcur, hweightcur] using hsumcur
  obtain ⟨R, Dtail, ν, hstep, hν, hnot, htail, hdiv⟩ :=
    hπ.exists_totalTransform_unit_current_decomposition D hDI
  have hres : thetaPotentialModificationCurrent hπ θ u hu -
      (c : ℝ) • smoothDivisorIntegrationCurrent W.firstDivisor =
      thetaPotentialModificationCurrent hπ (θ - (c : ℝ) • E.curvature) v hv +
        (c : ℝ) • effectiveDivisorIntegrationCurrent W R := by
    calc
      _ = (thetaPotentialModificationCurrent hπ (θ - (c : ℝ) • E.curvature) v hv +
            (c : ℝ) • effectiveDivisorIntegrationCurrent W DA) -
          (c : ℝ) • smoothDivisorIntegrationCurrent W.firstDivisor := by rw [hsplit]
      _ = thetaPotentialModificationCurrent hπ (θ - (c : ℝ) • E.curvature) v hv +
          (c : ℝ) • (effectiveDivisorIntegrationCurrent W DA -
            smoothDivisorIntegrationCurrent W.firstDivisor) := by
        exact (add_sub_assoc _ _ _).trans
          (congrArg (fun A => thetaPotentialModificationCurrent hπ
            (θ - (c : ℝ) • E.curvature) v hv + A)
            (smul_sub (c : ℝ) (effectiveDivisorIntegrationCurrent W DA)
              (smoothDivisorIntegrationCurrent W.firstDivisor)).symm)
      _ = _ := by rw [hdiv]
  obtain ⟨ER, hERsup, hER⟩ := DivisorMetric.exists_divisorMetric R
  have hwr := isThetaPshPotential_effectiveDivisorMetric R ER hER
  obtain ⟨hcr, hcrcur⟩ := exists_thetaPotentialCurrent_nonneg_smul hwr c.coe_nonneg
  have hvp := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    hπ.1 (θ - (c : ℝ) • E.curvature) hv
  obtain ⟨hζ, hζcur⟩ := exists_thetaPotentialCurrent_add hvp hcr
  have hRcur : thetaPotentialCurrent ER.curvature.val ER.weight hwr =
      effectiveDivisorIntegrationCurrent W R :=
    (thetaPotentialCurrent_effectiveDivisorMetric_eq R ER hER).trans
      (effectiveDivisorIntegrationCurrent_eq_of_metric W R ER hER).symm
  rw [hcrcur, hRcur] at hζcur
  exact ⟨R, Dtail, ν, hstep, hν, hnot, htail, hres, ER, hERsup, hER,
    hζ, hres.trans hζcur.symm⟩

/-- Every original full-positive current internally supplies its canonical
coefficient, genuine residual/plain trace and entire upstairs handoff. -/
theorem exists_original_current_modification_residual_decomposition {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π)
    (T : GlobalCurrent (m + 1) F.carrier (degreeTwo (Nat.succ_pos m)))
    (hclosed : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    letI : ChartedSpace (ComplexModel m) (W.flag (1 : Fin (m + 2))) := W.tail.charts
    ∃ μ : F.carrier → ℝ≥0∞, IsOriginalCurrentSourceReader T μ ∧
      (⨅ p : F.flag (1 : Fin (m + 2)), μ p) ≠ ⊤ ∧
      (∃ p : F.flag (1 : Fin (m + 2)), μ p = ⨅ q : F.flag (1 : Fin (m + 2)), μ q) ∧
      ∃ (θ : ClosedRealOneOneForm (m + 1) F.carrier) (u : F.carrier → EReal)
        (hu : IsThetaPshPotential θ.val u),
        T = thetaPotentialCurrent θ.val u hu ∧
        μ = (fun p => SquaredLogLelongSourceNormalization.squaredLogLelongNumber
          (n := m + 1) u p) ∧
        let c : ℝ≥0 := (⨅ p : F.flag (1 : Fin (m + 2)), μ p).toNNReal
        ∃ D : EffectiveDivisor (m + 1) F.carrier,
          D.ideal = vanishingIdeal (n := m + 1) (F.flag (1 : Fin (m + 2))) ∧
          ∃ E : MeteredEffectiveQDivisor (m + 1) F.carrier,
            E.support = F.flag (1 : Fin (m + 2)) ∧ DivisorMetric.IsDivisorMetric D E ∧
            ∃ hv : IsThetaPshPotential (θ - (c : ℝ) • E.curvature).val
                (extensionAcross (F.flag (1 : Fin (m + 2))) (smoothDivisorOffResidual E c u)),
              thetaPotentialCurrent (θ - (c : ℝ) • E.curvature).val
                (extensionAcross (F.flag (1 : Fin (m + 2))) (smoothDivisorOffResidual E c u)) hv =
                  T - (c : ℝ) • smoothDivisorIntegrationCurrent F.firstDivisor ∧
              SourceTraceRepresentativeDefinition.sourceGenericLelongNumber (n := m + 1)
                (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier)
                (extensionAcross (F.flag (1 : Fin (m + 2))) (smoothDivisorOffResidual E c u)) = 0 ∧
              (∃ τ : F.flag (1 : Fin (m + 2)) → EReal,
                IsNaturalSourceTraceRepresentative F.omega F.firstDivisor
                  (extensionAcross (F.flag (1 : Fin (m + 2))) (smoothDivisorOffResidual E c u)) τ) ∧
              (∀ (σ : ClosedRealOneOneForm (m + 1) F.carrier) (w : F.carrier → EReal)
                (hw : IsThetaPshPotential σ.val w), T = thetaPotentialCurrent σ.val w hw →
                thetaPotentialModificationCurrent hπ θ u hu =
                  thetaPotentialModificationCurrent hπ σ w hw) ∧
              ∃ (R : EffectiveDivisor (m + 1) W.carrier)
                (Dtail : EffectiveDivisor m W.tail.carrier) (ν : Fin m → ℕ),
                OriginalCartierFlagStep W
                  (GermIdealTotalTransform.EffectiveDivisor.totalTransform
                    hπ.1.1 hπ.interior_exceptional_eq_empty D) 1 Dtail ∧
                OriginalCartierFlagValuation m W.tail Dtail ν ∧
                ¬ W.flag (1 : Fin (m + 2)) ⊆ R.support ∧
                Dtail.ideal = GermIdeal.pullback (m := m)
                  (Subtype.val : W.tail.carrier → W.carrier) R.ideal ∧
                thetaPotentialModificationCurrent hπ θ u hu -
                    (c : ℝ) • smoothDivisorIntegrationCurrent W.firstDivisor =
                  thetaPotentialModificationCurrent hπ (θ - (c : ℝ) • E.curvature)
                    (extensionAcross (F.flag (1 : Fin (m + 2))) (smoothDivisorOffResidual E c u)) hv +
                    (c : ℝ) • effectiveDivisorIntegrationCurrent W R ∧
                ∃ ER : MeteredEffectiveQDivisor (m + 1) W.carrier,
                  ER.support = R.support ∧ DivisorMetric.IsDivisorMetric R ER ∧
                  ∃ hζ : IsThetaPshPotential
                      (ClosedRealOneOneForm.pullback hπ.1.1 (θ - (c : ℝ) • E.curvature) +
                        (c : ℝ) • ER.curvature).val
                      (fun z => extensionAcross (F.flag (1 : Fin (m + 2)))
                        (smoothDivisorOffResidual E c u) (π z) + ((c : ℝ) : EReal) * ER.weight z),
                    thetaPotentialModificationCurrent hπ θ u hu -
                        (c : ℝ) • smoothDivisorIntegrationCurrent W.firstDivisor =
                      thetaPotentialCurrent
                        (ClosedRealOneOneForm.pullback hπ.1.1 (θ - (c : ℝ) • E.curvature) +
                          (c : ℝ) • ER.curvature).val
                        (fun z => extensionAcross (F.flag (1 : Fin (m + 2)))
                          (smoothDivisorOffResidual E c u) (π z) + ((c : ℝ) : EReal) * ER.weight z) hζ := by
  let : ChartedSpace (ComplexModel m) (W.flag (1 : Fin (m + 2))) := W.tail.charts
  obtain ⟨μ, hμ, hfinite, hattained, θ, u, hu, hread, hpoint,
    D, hDI, E, hEW, hE, hv, hdowncur, hzero, τ, htrace⟩ :=
    exists_canonical_original_current_unit_residual_sourceTrace F.omega T hclosed h11 hT F.firstDivisor
  refine ⟨μ, hμ, hfinite, hattained, θ, u, hu, hread, hpoint,
    D, hDI, E, hEW, hE, hv, hdowncur, hzero, ⟨τ, htrace⟩, ?_, ?_⟩
  · intro σ w hw hreadw
    exact thetaPotentialModificationCurrent_eq_of_thetaPotentialCurrent_eq hπ hu hw
      (hread.symm.trans hreadw)
  · exact exists_thetaPotentialModificationCurrent_unit_residual_eq hπ hu D hDI E hEW hE _ hv

end SGPT.Okounkov
