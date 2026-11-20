import SGPT.Okounkov.FlagCurrentResidualPullback
import SGPT.Okounkov.SourceTraceIdealOrder

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
open GlobalCurrents CanonicalCurrentFrame NaturalThetaPshGeometricCurrent

/-- Actual strict-transform covariance, effective support noncontainment
and nonnegative generic arithmetic manufacture the lifted residual zero. -/
theorem sourceGeneric_lifted_divisor_residual_sum_eq_zero {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π)
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {v : F.carrier → EReal}
    (hv : IsThetaPshPotential θ.val v)
    (hzero : sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) v = 0)
    (R : EffectiveDivisor (m + 1) W.carrier)
    (ER : MeteredEffectiveQDivisor (m + 1) W.carrier)
    (hERsup : ER.support = R.support) (hER : DivisorMetric.IsDivisorMetric R ER)
    (hnot : ¬ W.flag (1 : Fin (m + 2)) ⊆ R.support) (c : ℝ≥0) :
    sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : W.flag (1 : Fin (m + 2)) → W.carrier)
      (fun z => v (π z) + ((c : ℝ) : EReal) * ER.weight z) = 0 := by
  have hvp := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    hπ.1 θ hv
  have hwr := isThetaPshPotential_effectiveDivisorMetric R ER hER
  obtain ⟨hcr, _hcrcur⟩ := exists_thetaPotentialCurrent_nonneg_smul hwr c.coe_nonneg
  have hzeroV : sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : W.flag (1 : Fin (m + 2)) → W.carrier) (v ∘ π) = 0 :=
    (hπ.sourceGeneric_first_comp_eq hv.quasiPshPotential).trans hzero
  have hzeroR := sourceGeneric_effectiveDivisorMetric_eq_zero_of_not_contains
    R ER hERsup hnot
  have hscaled := W.smooth.flagGenericLelong_nonneg_smul_eq ER.weight
    (1 : Fin (m + 2)) c.coe_nonneg
  have hzeroCR : sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : W.flag (1 : Fin (m + 2)) → W.carrier)
      (fun z => ((c : ℝ) : EReal) * ER.weight z) = 0 := by
    simpa only [flagGenericLelong, hzeroR, mul_zero] using hscaled
  rw [sourceGeneric_subtype_add_eq W.firstDivisor hvp.quasiPshPotential hcr.quasiPshPotential]
  exact (congrArg₂ (fun a b : ℝ≥0∞ => a + b) hzeroV hzeroCR).trans (zero_add 0)

/-- Actual original data produce the lifted residual's full theta current,
generic zero and genuine plain source trace, including target dimension zero. -/
theorem exists_sourceTrace_lifted_divisor_residual_sum {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π)
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {v : F.carrier → EReal}
    (hv : IsThetaPshPotential θ.val v)
    (hzero : sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) v = 0)
    (R : EffectiveDivisor (m + 1) W.carrier)
    (ER : MeteredEffectiveQDivisor (m + 1) W.carrier)
    (hERsup : ER.support = R.support) (hER : DivisorMetric.IsDivisorMetric R ER)
    (hnot : ¬ W.flag (1 : Fin (m + 2)) ⊆ R.support) (c : ℝ≥0) :
    ∃ hζ : IsThetaPshPotential
        (ClosedRealOneOneForm.pullback hπ.1.1 θ + (c : ℝ) • ER.curvature).val
        (fun z => v (π z) + ((c : ℝ) : EReal) * ER.weight z),
      thetaPotentialCurrent
          (ClosedRealOneOneForm.pullback hπ.1.1 θ + (c : ℝ) • ER.curvature).val
          (fun z => v (π z) + ((c : ℝ) : EReal) * ER.weight z) hζ =
        thetaPotentialModificationCurrent hπ θ v hv +
          (c : ℝ) • effectiveDivisorIntegrationCurrent W R ∧
      sourceGenericLelongNumber (n := m + 1)
        (Subtype.val : W.flag (1 : Fin (m + 2)) → W.carrier)
        (fun z => v (π z) + ((c : ℝ) : EReal) * ER.weight z) = 0 ∧
      ∃ ρ : W.tail.carrier → EReal, IsNaturalSourceTraceRepresentative W.omega W.firstDivisor
        (fun z => v (π z) + ((c : ℝ) : EReal) * ER.weight z) ρ := by
  have hvp := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    hπ.1 θ hv
  have hwr := isThetaPshPotential_effectiveDivisorMetric R ER hER
  obtain ⟨hcr, hcrcur⟩ := exists_thetaPotentialCurrent_nonneg_smul hwr c.coe_nonneg
  obtain ⟨hζ, hζcur⟩ := exists_thetaPotentialCurrent_add hvp hcr
  have hRcur : thetaPotentialCurrent ER.curvature.val ER.weight hwr =
      effectiveDivisorIntegrationCurrent W R :=
    (thetaPotentialCurrent_effectiveDivisorMetric_eq R ER hER).trans
      (effectiveDivisorIntegrationCurrent_eq_of_metric W R ER hER).symm
  rw [hcrcur, hRcur] at hζcur
  have hzeroζ := sourceGeneric_lifted_divisor_residual_sum_eq_zero
    hπ hv hzero R ER hERsup hER hnot c
  obtain ⟨ρ, hρ⟩ :=
    NaturalSourceTraceExistenceAllDimensions.exists_naturalSourceTrace_of_isThetaPshPotential
      W.omega W.firstDivisor hζ hzeroζ
  exact ⟨hζ, hζcur, hzeroζ, ρ, hρ⟩

/-- Every original recorded upstairs residual trace has the ideal class of
the internally produced same whole-current effective-residual sum trace. -/
theorem exists_recorded_unit_residual_trace_iEquivalent {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π)
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {u : F.carrier → EReal}
    (hu : IsThetaPshPotential θ.val u)
    (D : EffectiveDivisor (m + 1) F.carrier)
    (hDI : D.ideal = vanishingIdeal (n := m + 1) (F.flag (1 : Fin (m + 2))))
    (E : MeteredEffectiveQDivisor (m + 1) F.carrier)
    (hEW : E.support = F.flag (1 : Fin (m + 2)))
    (hE : DivisorMetric.IsDivisorMetric D E)
    {τup : W.tail.carrier → EReal} (hstep : OriginalFlagStep W (u ∘ π) τup) :
    let c : ℝ≥0 := (sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) u).toNNReal
    let v := extensionAcross (F.flag (1 : Fin (m + 2))) (smoothDivisorOffResidual E c u)
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
      ∃ ER : MeteredEffectiveQDivisor (m + 1) W.carrier,
        ER.support = R.support ∧ DivisorMetric.IsDivisorMetric R ER ∧
        ∃ hζ : IsThetaPshPotential
            (ClosedRealOneOneForm.pullback hπ.1.1 (θ - (c : ℝ) • E.curvature) +
              (c : ℝ) • ER.curvature).val
            (fun z => v (π z) + ((c : ℝ) : EReal) * ER.weight z),
          thetaPotentialModificationCurrent hπ θ u hu -
              (c : ℝ) • smoothDivisorIntegrationCurrent W.firstDivisor =
            thetaPotentialCurrent
              (ClosedRealOneOneForm.pullback hπ.1.1 (θ - (c : ℝ) • E.curvature) +
                (c : ℝ) • ER.curvature).val
              (fun z => v (π z) + ((c : ℝ) : EReal) * ER.weight z) hζ ∧
          ∃ ρ : W.tail.carrier → EReal,
            IsNaturalSourceTraceRepresentative W.omega W.firstDivisor
              (fun z => v (π z) + ((c : ℝ) : EReal) * ER.weight z) ρ ∧
            IEquivalentOnManifold (n := m) τup ρ := by
  let c : ℝ≥0 := (sourceGenericLelongNumber (n := m + 1)
    (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) u).toNNReal
  let v := extensionAcross (F.flag (1 : Fin (m + 2))) (smoothDivisorOffResidual E c u)
  let : ChartedSpace (ComplexModel m) (W.flag (1 : Fin (m + 2))) := W.tail.charts
  have hv := isThetaPshPotential_smooth_divisor_residual_of_unit_metric
    hu F.firstDivisor D hDI E hEW hE
  have hzero := sourceGeneric_smooth_divisor_residual_eq_zero
    hu F.firstDivisor D hDI E hEW hE hv
  obtain ⟨R, Dtail, ν, hC, hν, hnot, htail, hres, ER, hERsup, hER, _hζ₀, _hζ₀cur⟩ :=
    exists_thetaPotentialModificationCurrent_unit_residual_eq hπ hu D hDI E hEW hE c hv
  obtain ⟨hζ, hζcur, _hzeroζ, ρ, hρ⟩ :=
    exists_sourceTrace_lifted_divisor_residual_sum hπ hv hzero R ER hERsup hER hnot c
  have hζfull := hres.trans hζcur.symm
  obtain ⟨_σ, _hrecorded, L, hLI, EL, hELsup, hEL, htraceUp⟩ := hstep
  have hup := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    hπ.1 θ hu
  have hcoef := hπ.sourceGeneric_first_comp_eq hu.quasiPshPotential
  have hcoefLambda : sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : W.flag (1 : Fin (m + 2)) → W.carrier) (fun y => u (π y)) =
      sourceGenericLelongNumber (n := m + 1)
        (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) u := by
    simpa only [Function.comp_def] using hcoef
  have hr := isThetaPshPotential_smooth_divisor_residual_of_unit_metric
    hup W.firstDivisor L hLI EL hELsup hEL
  have hrC : IsThetaPshPotential
      (ClosedRealOneOneForm.pullback hπ.1.1 θ - (c : ℝ) • EL.curvature).val
      (extensionAcross (W.flag (1 : Fin (m + 2))) (smoothDivisorOffResidual EL c (u ∘ π))) := by
    simpa only [Function.comp_def, hcoefLambda] using hr
  have hruCur := smooth_divisor_residual_current_eq_unit_current
    hup W.firstDivisor L hLI EL hELsup hEL
      (sourceGenericLelongNumber (n := m + 1)
        (Subtype.val : W.flag (1 : Fin (m + 2)) → W.carrier) (u ∘ π)).toNNReal hr
  have hruCurC : thetaPotentialCurrent
      (ClosedRealOneOneForm.pullback hπ.1.1 θ - (c : ℝ) • EL.curvature).val
      (extensionAcross (W.flag (1 : Fin (m + 2))) (smoothDivisorOffResidual EL c (u ∘ π))) hrC =
      thetaPotentialModificationCurrent hπ θ u hu -
        (c : ℝ) • smoothDivisorIntegrationCurrent W.firstDivisor := by
    simpa only [thetaPotentialModificationCurrent, Function.comp_def, hcoefLambda] using hruCur
  let : MeasurableSpace W.carrier := borel W.carrier
  let : BorelSpace W.carrier := ⟨rfl⟩
  have hIambient := iEquivalent_of_thetaPotentialCurrent_eq W.omega hrC hζ
    (hruCurC.trans hζfull)
  let Z := W.flag (1 : Fin (m + 2))
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) W.firstDivisor.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
    (Nat.le_succ m) W.firstDivisor.2.2
  let : CompactSpace Z := W.tail.compact
  let : ConnectedSpace Z := W.tail.connected
  let : MeasurableSpace Z := borel Z
  let : BorelSpace Z := ⟨rfl⟩
  let : MeasurableSpace W.tail.carrier := borel W.tail.carrier
  let : BorelSpace W.tail.carrier := ⟨rfl⟩
  let hι := SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ m) W.firstDivisor.2.2
  have htraceUpC : IsNaturalSourceTraceRepresentative W.omega W.firstDivisor
      (extensionAcross (W.flag (1 : Fin (m + 2))) (smoothDivisorOffResidual EL c (u ∘ π))) τup := by
    simpa only [hcoef] using htraceUp
  change IsSourceTraceRepresentativeAlong W.omega W.tail.omega hι _ τup at htraceUpC
  change IsSourceTraceRepresentativeAlong W.omega W.tail.omega hι _ ρ at hρ
  have hItarget := iEquivalent_of_iEquivalent_of_sourceTraceRepresentatives
    (Nat.succ_ne_zero m) W.tail.omega W.tail.omega hι htraceUpC hρ hIambient
  exact ⟨R, Dtail, ν, hC, hν, hnot, htail, ER, hERsup, hER, hζ, hζfull, ρ, hρ, hItarget⟩

end SGPT.Okounkov
