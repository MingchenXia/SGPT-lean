import SGPT.Okounkov.EffectiveDivisorCoefficient
import SGPT.Okounkov.ResidualIdealCancellation

set_option autoImplicit false
noncomputable section
namespace SGPT.Okounkov

open Set Filter
open scoped Manifold ContDiff NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending ThetaPshCodimTwoExtension
open SourceTraceRepresentativeDefinition SquaredLogLelongSourceNormalization IdealWeightPowers

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [CompactSpace M]

/-- The original upper residual of a genuine Cartier metric is in the
actual effective residual's multiplier class; all data are geometric,
and the pole-inclusive residual equivalence is produced. -/
theorem iEquivalent_effectiveDivisorMetric_residual_weight
    {W : Set M} (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    (D L R : EffectiveDivisor (m + 1) M)
    (hLI : L.ideal = vanishingIdeal (n := m + 1) W) (a : ℕ)
    (hDR : D.ideal = (idealPow L.ideal a).mul R.ideal) (hnot : ¬ W ⊆ R.support)
    (ED EL ER : MeteredEffectiveQDivisor (m + 1) M)
    (hED : DivisorMetric.IsDivisorMetric D ED)
    (hEL : DivisorMetric.IsDivisorMetric L EL) (hELsup : EL.support = W)
    (hER : DivisorMetric.IsDivisorMetric R ER) (hERsup : ER.support = R.support) :
    IEquivalentOnManifold (n := m + 1)
      (extensionAcross W (smoothDivisorOffResidual EL
        (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) ED.weight).toNNReal ED.weight))
      ER.weight := by
  have hu := isThetaPshPotential_effectiveDivisorMetric D ED hED
  have hv := isThetaPshPotential_effectiveDivisorMetric L EL hEL
  have hw := isThetaPshPotential_effectiveDivisorMetric R ER hER
  obtain ⟨hF, hI⟩ := iEquivalent_effectiveDivisorMetric_factorized_weights
    D L R a hDR ED EL ER hED hEL hER
  let f : M → EReal := fun x => a • EL.weight x + ER.weight x
  have hF' : IsThetaPshPotential ((a : ℝ) • EL.curvature + ER.curvature).val f := hF
  have haU := sourceGeneric_effectiveDivisorMetric_eq_integer_order hW D L R hLI a
    hDR hnot ED EL ER hED hEL hER hERsup
  have haF : sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) f =
      (a : ℝ≥0∞) :=
    (sourceGeneric_subtype_eq_of_iEquivalent hW hu.quasiPshPotential hF'.quasiPshPotential hI).symm.trans haU
  let c : ℝ≥0 := (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) f).toNNReal
  let r : M → EReal := extensionAcross W (smoothDivisorOffResidual EL c f)
  have hr : IsThetaPshPotential
      (((a : ℝ) • EL.curvature + ER.curvature) - (c : ℝ) • EL.curvature).val r :=
    isThetaPshPotential_smooth_divisor_residual_of_unit_metric hF' hW L hLI EL hELsup hEL
  have hscaled : IsThetaPshPotential ((a : ℝ) • EL.curvature).val
      (fun x => ((a : ℝ) : EReal) * EL.weight x) :=
    (exists_thetaPotentialCurrent_nonneg_smul hv (Nat.cast_nonneg a)).choose
  have hc : (c : ℝ) = (a : ℝ) := by
    simp only [c, haF, ENNReal.toNNReal_natCast, NNReal.coe_natCast]
  have hrecompose := smooth_divisor_residual_recompose hF' hW EL hELsup c hr
  have hsum : (fun x => r x + ((a : ℝ) : EReal) * EL.weight x) =
      (fun x => ER.weight x + ((a : ℝ) : EReal) * EL.weight x) := by
    calc
      _ = f := by simpa only [r, hc] using hrecompose
      _ = _ := by
        funext x
        simp only [f, EReal.nsmul_eq_mul, EReal.coe_coe_eq_natCast]
        exact add_comm _ _
  have hR : IEquivalentOnManifold (n := m + 1) r ER.weight :=
    iEquivalent_of_iEquivalent_add_common_potential hr hw hscaled
      (by rw [hsum]; exact IEquivalentOnManifold.refl _)
  exact (iEquivalent_smooth_divisor_residuals_of_iEquivalent
    hu hF' hI hW L hLI EL hELsup hEL).trans hR

end SGPT.Okounkov
