import SGPT.NAPotential.QwNAConcavity
import SGPT.Envelopes.SourceOrdinaryEnvelopeAlgebra

/-! Genuine positive REAL homogeneity of original potential analytification.
Blueprint: operation-correspondence-scaling.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.NAPotential.OperationComparison
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.Berkovich

private theorem half_mul_add {c : ℝ} (hc : 0 < c) (a : EReal) :
    ((c/2 : ℝ) : EReal) * a + ((c/2 : ℝ) : EReal) * a = (c : EReal) * a := by
  rw [← EReal.right_distrib_of_nonneg
    (EReal.coe_nonneg.mpr (by positivity : 0 ≤ c/2))
    (EReal.coe_nonneg.mpr (by positivity : 0 ≤ c/2)), ← EReal.coe_add]
  congr 2
  ring

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f) [IsProper f]
local instance opPotentialScalePointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance opPotentialScalePointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance opPotentialScalePointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

private theorem potentialAn_positiveScale_le
    {θ : ClosedRealOneOneForm n (SchemeComplexPoint f)}
    {φ : SchemeComplexPoint f → EReal} (hφ : IsThetaPshPotential θ.val φ)
    {c : ℝ} (hc : 0 < c) (v : BerkovichPoint f) :
    potentialAn n E (fun x => (c : EReal) * φ x) v ≤
      (c : EReal) * potentialAn n E φ v := by
  have he : (fun x => ((c/2 : ℝ) : EReal) * φ x + ((c/2 : ℝ) : EReal) * φ x) =
      (fun x => (c : EReal) * φ x) := funext fun x => half_mul_add hc (φ x)
  have hscaled := RestrictedApproximantComparison.isThetaPshPotential_smul hφ hc
  have hcombined : IsThetaPshPotential (c • θ).val
      (fun x => ((c/2 : ℝ) : EReal) * φ x + ((c/2 : ℝ) : EReal) * φ x) := by
    rw [he]
    exact hscaled
  have h := potentialAn_smul_add_le n E hφ hφ
    (by positivity : 0 < c/2) (by positivity : 0 < c/2) hcombined v
  rw [he, half_mul_add hc] at h
  exact h

/-- Actual original multiplier-ideal analytification is homogeneous under
EVERY positive REAL scalar, on ALL original Berkovich points and in all dimensions. -/
theorem potentialAn_positiveScale
    {θ : ClosedRealOneOneForm n (SchemeComplexPoint f)}
    {φ : SchemeComplexPoint f → EReal} (hφ : IsThetaPshPotential θ.val φ)
    {c : ℝ} (hc : 0 < c) (v : BerkovichPoint f) :
    potentialAn n E (fun x => (c : EReal) * φ x) v =
      (c : EReal) * potentialAn n E φ v := by
  apply le_antisymm (potentialAn_positiveScale_le n E hφ hc v)
  have hscaled := RestrictedApproximantComparison.isThetaPshPotential_smul hφ hc
  have h := potentialAn_positiveScale_le n E hscaled (inv_pos.mpr hc) v
  have he : (fun x => ((c⁻¹ : ℝ) : EReal) * ((c : EReal) * φ x)) = φ := by
    funext x
    rw [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hc.ne', EReal.coe_one, one_mul]
  rw [he] at h
  have hh := (sourcePositiveERealOrderIso c hc).monotone h
  change (c : EReal) * potentialAn n E φ v ≤
    (c : EReal) * (((c⁻¹ : ℝ) : EReal) *
      potentialAn n E (fun x => (c : EReal) * φ x) v) at hh
  simpa only [← mul_assoc,
    ← EReal.coe_mul, mul_inv_cancel₀ hc.ne', EReal.coe_one, one_mul] using hh

end SGPT.NAPotential.OperationComparison
