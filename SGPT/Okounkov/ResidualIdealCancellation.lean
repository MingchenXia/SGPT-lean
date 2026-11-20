import SGPT.Okounkov.MultiplierCancellation
import SGPT.Okounkov.DivisorResidualGenericZero

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov

open Set Filter
open scoped Manifold ContDiff NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending
open ThetaPshCodimTwoExtension SourceTraceRepresentativeDefinition

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [CompactSpace M]

/-- Actual upper residuals preserve original multiplier order when the
actual first generic coefficients agree. Their existence is produced
for the same original unit metric, rather than assumed. -/
theorem iOrder_smooth_divisor_residuals_of_iOrder_and_coefficient_eq
    {θ σ : ClosedRealOneOneForm (m + 1) M} {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v)
    (hI : IOrderOnManifold (n := m + 1) u v)
    {W : Set M} (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    (hcoef : sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u =
      sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) v)
    (D : EffectiveDivisor (m + 1) M)
    (hDI : D.ideal = vanishingIdeal (n := m + 1) W)
    (E : MeteredEffectiveQDivisor (m + 1) M) (hEW : E.support = W)
    (hmetric : DivisorMetric.IsDivisorMetric D E) :
    IOrderOnManifold (n := m + 1)
      (extensionAcross W (smoothDivisorOffResidual E
        (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal u))
      (extensionAcross W (smoothDivisorOffResidual E
        (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) v).toNNReal v)) := by
  let c : ℝ≥0 := (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal
  have hc : (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) v).toNNReal = c :=
    congrArg ENNReal.toNNReal hcoef.symm
  let ru := extensionAcross W (smoothDivisorOffResidual E c u)
  let rv := extensionAcross W (smoothDivisorOffResidual E c v)
  have hru : IsThetaPshPotential (θ - (c : ℝ) • E.curvature).val ru :=
    isThetaPshPotential_smooth_divisor_residual_of_unit_metric hu hW D hDI E hEW hmetric
  have hrv : IsThetaPshPotential (σ - (c : ℝ) • E.curvature).val rv := by
    simpa only [hc] using
      isThetaPshPotential_smooth_divisor_residual_of_unit_metric hv hW D hDI E hEW hmetric
  have hscaled : IsThetaPshPotential ((c : ℝ) • E.curvature).val
      (fun y => ((c : ℝ) : EReal) * E.weight y) := by
    by_cases hc0 : c = 0
    · simp only [hc0, NNReal.coe_zero, zero_smul, EReal.coe_zero, EReal.zero_mul]
      exact (LocalPotentials.isThetaPshPotential_zero_iff
        (0 : ClosedRealOneOneForm (m + 1) M)).mpr (by intro e z hz w; simp)
    · exact RestrictedApproximantComparison.isThetaPshPotential_smul
        (isThetaPshPotential_divisor_weight_of_smooth_support hW E hEW)
        (by exact_mod_cast (pos_iff_ne_zero.mpr hc0 : 0 < c))
  have hsum : IOrderOnManifold (n := m + 1)
      (fun y => ru y + ((c : ℝ) : EReal) * E.weight y)
      (fun y => rv y + ((c : ℝ) : EReal) * E.weight y) := by
    rw [smooth_divisor_residual_recompose hu hW E hEW c hru,
      smooth_divisor_residual_recompose hv hW E hEW c hrv]
    exact hI
  have hcancel := iOrder_of_iOrder_add_common_potential hru hrv hscaled hsum
  simpa only [hc] using hcancel

/-- The exact residual-equivalence step of the original valuation proof.
Both actual coefficient equality and both residual potentials are produced
from the original multiplier equivalence and same genuine unit metric. -/
theorem iEquivalent_smooth_divisor_residuals_of_iEquivalent
    {θ σ : ClosedRealOneOneForm (m + 1) M} {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v)
    (hI : IEquivalentOnManifold (n := m + 1) u v)
    {W : Set M} (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    (D : EffectiveDivisor (m + 1) M)
    (hDI : D.ideal = vanishingIdeal (n := m + 1) W)
    (E : MeteredEffectiveQDivisor (m + 1) M) (hEW : E.support = W)
    (hmetric : DivisorMetric.IsDivisorMetric D E) :
    IEquivalentOnManifold (n := m + 1)
      (extensionAcross W (smoothDivisorOffResidual E
        (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal u))
      (extensionAcross W (smoothDivisorOffResidual E
        (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) v).toNNReal v)) := by
  have hcoef := sourceGeneric_subtype_eq_of_iEquivalent hW
    hu.quasiPshPotential hv.quasiPshPotential hI
  exact ⟨iOrder_smooth_divisor_residuals_of_iOrder_and_coefficient_eq
      hu hv hI.1 hW hcoef D hDI E hEW hmetric,
    iOrder_smooth_divisor_residuals_of_iOrder_and_coefficient_eq
      hv hu hI.2 hW hcoef.symm D hDI E hEW hmetric⟩

end SGPT.Okounkov
