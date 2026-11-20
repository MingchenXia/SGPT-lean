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

/-- Actual sum residuals have the same whole current as the residual of
the actual sum, hence their original multiplier ideals agree. Original
data produce all three residuals and the actual sum potential internally. -/
theorem iEquivalent_smooth_divisor_residual_add_of_unit_metrics {m : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
    [IsComplexManifold (m + 1) M] [CompactSpace M] [ConnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (omega : KahlerBackground (m + 1) M)
    {θ σ : ClosedRealOneOneForm (m + 1) M} {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v)
    {W : Set M} (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    (D₀ D₁ Ds : EffectiveDivisor (m + 1) M)
    (hDI₀ : D₀.ideal = vanishingIdeal (n := m + 1) W)
    (hDI₁ : D₁.ideal = vanishingIdeal (n := m + 1) W)
    (hDIs : Ds.ideal = vanishingIdeal (n := m + 1) W)
    (E₀ E₁ Es : MeteredEffectiveQDivisor (m + 1) M)
    (hEW₀ : E₀.support = W) (hEW₁ : E₁.support = W) (hEWs : Es.support = W)
    (hmetric₀ : DivisorMetric.IsDivisorMetric D₀ E₀)
    (hmetric₁ : DivisorMetric.IsDivisorMetric D₁ E₁)
    (hmetrics : DivisorMetric.IsDivisorMetric Ds Es) :
    let c₀ := (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal
    let c₁ := (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) v).toNNReal
    let cs := (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M)
      (fun x => u x + v x)).toNNReal
    IEquivalentOnManifold (n := m + 1)
      (extensionAcross W (smoothDivisorOffResidual Es cs (fun x => u x + v x)))
      (fun x => extensionAcross W (smoothDivisorOffResidual E₀ c₀ u) x +
        extensionAcross W (smoothDivisorOffResidual E₁ c₁ v) x) := by
  dsimp only
  let c₀ := (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal
  let c₁ := (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) v).toNNReal
  let cs := (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M)
      (fun x => u x + v x)).toNNReal
  obtain ⟨hsum, hsumcur⟩ := exists_thetaPotentialCurrent_add hu hv
  have hr₀ := isThetaPshPotential_smooth_divisor_residual_of_unit_metric hu hW D₀ hDI₀ E₀ hEW₀ hmetric₀
  have hr₁ := isThetaPshPotential_smooth_divisor_residual_of_unit_metric hv hW D₁ hDI₁ E₁ hEW₁ hmetric₁
  have hrs := isThetaPshPotential_smooth_divisor_residual_of_unit_metric hsum hW Ds hDIs Es hEWs hmetrics
  obtain ⟨hradd, hraddcur⟩ := exists_thetaPotentialCurrent_add hr₀ hr₁
  have hcs : (cs : ℝ) = (c₀ : ℝ) + (c₁ : ℝ) := by
    change (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M)
      (fun x => u x + v x)).toReal = _
    rw [sourceGeneric_subtype_add_eq hW hu.quasiPshPotential hv.quasiPshPotential,
      ENNReal.toReal_add (sourceGeneric_subtype_ne_top hW hu.quasiPshPotential)
        (sourceGeneric_subtype_ne_top hW hv.quasiPshPotential)]
    rfl
  have h₀ := smooth_divisor_residual_current_eq_unit_current hu hW D₀ hDI₀ E₀ hEW₀ hmetric₀ c₀ hr₀
  have h₁ := smooth_divisor_residual_current_eq_unit_current hv hW D₁ hDI₁ E₁ hEW₁ hmetric₁ c₁ hr₁
  have hs := smooth_divisor_residual_current_eq_unit_current hsum hW Ds hDIs Es hEWs hmetrics cs hrs
  have hcur : thetaPotentialCurrent _ _ hrs = thetaPotentialCurrent _ _ hradd := by
    rw [hraddcur, hs, h₀, h₁, hsumcur, hcs, add_smul]
    abel
  exact iEquivalent_of_thetaPotentialCurrent_eq omega hrs hradd hcur

/-- The common-metric specialization retains the literal source residuals. -/
theorem iEquivalent_smooth_divisor_residual_add {m : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
    [IsComplexManifold (m + 1) M] [CompactSpace M] [ConnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (omega : KahlerBackground (m + 1) M)
    {θ σ : ClosedRealOneOneForm (m + 1) M} {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v)
    {W : Set M} (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    (D : EffectiveDivisor (m + 1) M) (hDI : D.ideal = vanishingIdeal (n := m + 1) W)
    (E : MeteredEffectiveQDivisor (m + 1) M) (hEW : E.support = W)
    (hmetric : DivisorMetric.IsDivisorMetric D E) :
    let c₀ := (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal
    let c₁ := (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) v).toNNReal
    let cs := (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M)
      (fun x => u x + v x)).toNNReal
    IEquivalentOnManifold (n := m + 1)
      (extensionAcross W (smoothDivisorOffResidual E cs (fun x => u x + v x)))
      (fun x => extensionAcross W (smoothDivisorOffResidual E c₀ u) x +
        extensionAcross W (smoothDivisorOffResidual E c₁ v) x) :=
  iEquivalent_smooth_divisor_residual_add_of_unit_metrics omega hu hv hW
    D D D hDI hDI hDI E E E hEW hEW hEW hmetric hmetric hmetric

end SGPT.Okounkov
