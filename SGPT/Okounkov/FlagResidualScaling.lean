import SGPT.Okounkov.ThetaPotentialCurrentCombinations

set_option autoImplicit false
noncomputable section
namespace SGPT.Okounkov
open Set Filter
open scoped Manifold ContDiff NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending ThetaPshCodimTwoExtension
open SourceTraceRepresentativeDefinition NaturalThetaPshGeometricCurrent

/-- Actual positive scalar residuals retain the true whole-current scaling
and hence multiplier equivalence, with both genuine unit metrics arbitrary. -/
theorem iEquivalent_smooth_divisor_residual_pos_smul {m : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
    [IsComplexManifold (m + 1) M] [CompactSpace M] [ConnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (omega : KahlerBackground (m + 1) M)
    {θ : ClosedRealOneOneForm (m + 1) M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) {c : ℝ} (hc : 0 < c)
    {W : Set M} (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    (D₀ D₁ : EffectiveDivisor (m + 1) M)
    (hDI₀ : D₀.ideal = vanishingIdeal (n := m + 1) W)
    (hDI₁ : D₁.ideal = vanishingIdeal (n := m + 1) W)
    (E₀ E₁ : MeteredEffectiveQDivisor (m + 1) M)
    (hEW₀ : E₀.support = W) (hEW₁ : E₁.support = W)
    (hmetric₀ : DivisorMetric.IsDivisorMetric D₀ E₀)
    (hmetric₁ : DivisorMetric.IsDivisorMetric D₁ E₁) :
    let a := (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal
    let ac := (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M)
      (fun x => (c : EReal) * u x)).toNNReal
    IEquivalentOnManifold (n := m + 1)
      (extensionAcross W (smoothDivisorOffResidual E₁ ac (fun x => (c : EReal) * u x)))
      (fun x => (c : EReal) * extensionAcross W (smoothDivisorOffResidual E₀ a u) x) := by
  dsimp only
  let a := (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal
  let ac := (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M)
      (fun x => (c : EReal) * u x)).toNNReal
  obtain ⟨hcu, hcuCurrent⟩ := exists_thetaPotentialCurrent_nonneg_smul hu hc.le
  have hr := isThetaPshPotential_smooth_divisor_residual_of_unit_metric hu hW D₀ hDI₀ E₀ hEW₀ hmetric₀
  have hrc := isThetaPshPotential_smooth_divisor_residual_of_unit_metric hcu hW D₁ hDI₁ E₁ hEW₁ hmetric₁
  obtain ⟨hcr, hcrCurrent⟩ := exists_thetaPotentialCurrent_nonneg_smul hr hc.le
  have hcoef : sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M)
      (fun x => (c : EReal) * u x) =
      ENNReal.ofReal c * sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u := by
    simpa only [flagGenericLelong] using
      flagGenericLelong_smul_eq (n := m + 1) (fun _ : Fin (m + 2) => W) u 0 hc
  have hac : (ac : ℝ) = c * (a : ℝ) := by
    change (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M)
      (fun x => (c : EReal) * u x)).toReal = _
    rw [hcoef, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le]
    rfl
  have hR := smooth_divisor_residual_current_eq_unit_current hu hW D₀ hDI₀ E₀ hEW₀ hmetric₀ a hr
  have hRc := smooth_divisor_residual_current_eq_unit_current hcu hW D₁ hDI₁ E₁ hEW₁ hmetric₁ ac hrc
  have hcur : thetaPotentialCurrent _ _ hrc = thetaPotentialCurrent _ _ hcr := by
    rw [hcrCurrent, hRc, hR, hcuCurrent, hac, mul_smul]
    exact (smul_sub c (thetaPotentialCurrent θ.val u hu)
      ((a : ℝ) • smoothDivisorIntegrationCurrent hW)).symm
  exact iEquivalent_of_thetaPotentialCurrent_eq omega hrc hcr hcur

end SGPT.Okounkov
