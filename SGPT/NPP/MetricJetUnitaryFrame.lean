import SGPT.NPP.SourceEnvelopeKernelCompatibility
import SGPT.Analysis.KahlerNormalCoordinates
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Actual metric-derived quadratic jets and unitary frame invariance

Complete blueprint: `blueprint/src/dnt-big-metric-jet-frame.tex`, written
first. The existing actual metric derivative / normalQuad construction is
reused unchanged. Its genuine covariance and Haar invariance prove that the
same explicit source-envelope jet integral is independent of unitary frames.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace

namespace SGPT.NPP.DNTBig

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.HolomorphicPullback
open SGPT.PSH.VariableComplexAtlas
open SGPT.Analysis.KahlerNormal

variable {n : ℕ}

/-- The actual explicit norm-radial kernel is invariant under every actual
complex linear isometry equivalence, not just scalar circle rotations. -/
theorem explicitRadialKernel_linearIsometry (Q : ComplexModel n ≃ₗᵢ[ℂ] ComplexModel n)
    (R : ℝ) (hR : 0 < R) (j : ℕ) (x : ComplexModel n) :
    explicitRadialKernel R hR j (Q x) = explicitRadialKernel R hR j x := by
  unfold explicitRadialKernel
  congr 1
  unfold explicitRadialRaw ContDiffBumpBase.ofInnerProductSpace
  simp only [norm_smul, Q.norm_map]

private theorem dHol_normalizedDeriv_unitary
    (α : ComplexModel n → CoordinateRealTwoForm n) (z : ComplexModel n)
    (A : ComplexModel n →L[ℂ] ComplexModel n)
    (Q : ComplexModel n ≃ₗᵢ[ℂ] ComplexModel n) (p u v : ComplexModel n) :
    dHol (normalizedDeriv α z (A.comp Q.toContinuousLinearEquiv.toContinuousLinearMap)) p u v =
      dHol (normalizedDeriv α z A) (Q p) (Q u) (Q v) := by
  simp only [dHol, hermitianEntry, normalizedDeriv_apply, ContinuousLinearMap.comp_apply,
    map_smul, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]

/-- Covariance is proved for the actual coefficient built from the actual
metric derivative by its actual inner-product characterization. -/
theorem normalQuad_normalizedDeriv_unitary
    {α : ComplexModel n → CoordinateRealTwoForm n} {z : ComplexModel n}
    (hα : DifferentiableAt ℝ α z) (h11 : ∀ᶠ x in 𝓝 z, IsOneOne (α x))
    (A : ComplexModel n →L[ℂ] ComplexModel n)
    (Q : ComplexModel n ≃ₗᵢ[ℂ] ComplexModel n) (p u : ComplexModel n) :
    Q (normalQuad
      (normalizedDeriv α z (A.comp Q.toContinuousLinearEquiv.toContinuousLinearMap))
      (normalizedDeriv_isOneOne hα h11 _) p u) =
      normalQuad (normalizedDeriv α z A) (normalizedDeriv_isOneOne hα h11 A) (Q p) (Q u) := by
  apply ext_inner_left ℂ
  intro v
  rw [show v = Q (Q.symm v) from (Q.apply_symm_apply v).symm,
    Q.inner_map_map]
  simp only [normalQuad_apply, inner_quadFun]
  rw [dHol_normalizedDeriv_unitary, Q.apply_symm_apply]

/-- The actual metric-derived quadratic holomorphic jet changes by the same
actual unitary reparametrization of its tangent variable. -/
theorem normalCoord_normalizedDeriv_unitary
    {α : ComplexModel n → CoordinateRealTwoForm n} {z : ComplexModel n}
    (hα : DifferentiableAt ℝ α z) (h11 : ∀ᶠ x in 𝓝 z, IsOneOne (α x))
    (A : ComplexModel n →L[ℂ] ComplexModel n)
    (Q : ComplexModel n ≃ₗᵢ[ℂ] ComplexModel n) (v : ComplexModel n) :
    normalCoord z (A.comp Q.toContinuousLinearEquiv.toContinuousLinearMap)
      (normalQuad (normalizedDeriv α z (A.comp Q.toContinuousLinearEquiv.toContinuousLinearMap))
        (normalizedDeriv_isOneOne hα h11 _)) v =
      normalCoord z A (normalQuad (normalizedDeriv α z A)
        (normalizedDeriv_isOneOne hα h11 A)) (Q v) := by
  simp only [normalCoord, ContinuousLinearMap.comp_apply, map_sub, map_smul,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    normalQuad_normalizedDeriv_unitary hα h11 A Q]

variable {Y : Type*} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

private theorem metric_coeff_differentiableAt (w : KahlerBackground n Y)
    (e : ComplexChart n Y) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    DifferentiableAt ℝ (w.form.val.coeff e) z :=
  ((w.form.val.smooth e).differentiableOn (by simp)).differentiableAt (e.val.open_target.mem_nhds hz)

private theorem metric_coeff_eventually_isOneOne (w : KahlerBackground n Y)
    (e : ComplexChart n Y) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    ∀ᶠ x in 𝓝 z, IsOneOne (w.form.val.coeff e x) := by
  filter_upwards [e.val.open_target.mem_nhds hz] with x hx
  exact (w.isKahler.1 e x hx).1

/-- The literal same source-envelope integral along the existing actual
metric-derived quadratic jet. No smoothing property is assigned by definition. -/
def sourceQuadraticMetricJetMean (w : KahlerBackground n Y)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n Y)) (g : Y → ℝ)
    (e : ComplexChart n Y) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (A : ComplexModel n →L[ℂ] ComplexModel n) (r : ℝ) : ℝ :=
  ∫ ζ : ComplexModel n,
    (sourceRelativeEnvelope θ (fun _ => ⊤) (fun x => (g x : EReal))
      (e.val.symm (normalCoord z A
        (normalQuad (normalizedDeriv (w.form.val.coeff e) z A)
          (normalizedDeriv_isOneOne (metric_coeff_differentiableAt w e hz)
            (metric_coeff_eventually_isOneOne w e hz) A)) (r • ζ)))).toReal *
      explicitRadialKernel 1 one_pos 0 ζ

/-- Genuine unitary frame independence of the actual metric-derived jet
integral of the same original source envelope, by actual Haar change of variables. -/
theorem sourceQuadraticMetricJetMean_unitary (w : KahlerBackground n Y)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n Y)) (g : Y → ℝ)
    (e : ComplexChart n Y) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (A : ComplexModel n →L[ℂ] ComplexModel n) (r : ℝ)
    (Q : ComplexModel n ≃ₗᵢ[ℂ] ComplexModel n) :
    sourceQuadraticMetricJetMean w θ g e z hz
      (A.comp Q.toContinuousLinearEquiv.toContinuousLinearMap) r =
        sourceQuadraticMetricJetMean w θ g e z hz A r := by
  let f : ComplexModel n → ℝ := fun ζ =>
    (sourceRelativeEnvelope θ (fun _ => ⊤) (fun x => (g x : EReal))
      (e.val.symm (normalCoord z A
        (normalQuad (normalizedDeriv (w.form.val.coeff e) z A)
          (normalizedDeriv_isOneOne (metric_coeff_differentiableAt w e hz)
            (metric_coeff_eventually_isOneOne w e hz) A)) (r • ζ)))).toReal *
      explicitRadialKernel 1 one_pos 0 ζ
  let Qr : ComplexModel n ≃ₗᵢ[ℝ] ComplexModel n :=
    { Q.toLinearEquiv.restrictScalars ℝ with norm_map' := Q.norm_map }
  have hhaar := Qr.measurePreserving.integral_comp
    Qr.toHomeomorph.measurableEmbedding f
  change (∫ ζ, f (Q ζ)) = ∫ ζ, f ζ at hhaar
  rw [sourceQuadraticMetricJetMean]
  simp_rw [normalCoord_normalizedDeriv_unitary (metric_coeff_differentiableAt w e hz)
    (metric_coeff_eventually_isOneOne w e hz) A Q,
    show ∀ ζ, Q (r • ζ) = r • Q ζ from fun ζ => (Q.restrictScalars ℝ).map_smul r ζ]
  convert hhaar using 1
  · apply integral_congr_ae
    exact Eventually.of_forall fun ζ => by
      dsimp only [f]
      rw [explicitRadialKernel_linearIsometry Q]
  · rfl

/-- Any two actual complex frames normalizing the same actual metric give
the same actual source jet mean. Existing normalization producers are reused;
no new normalization existence or frame-independence certificate is assumed. -/
theorem sourceQuadraticMetricJetMean_eq_of_normalizing (w : KahlerBackground n Y)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n Y)) (g : Y → ℝ)
    (e : ComplexChart n Y) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (A B : ComplexModel n ≃L[ℂ] ComplexModel n) (r : ℝ)
    (hA : ∀ u v, w.form.val.coeff e z ![A u, A v] = flatForm n ![u, v])
    (hB : ∀ u v, w.form.val.coeff e z ![B u, B v] = flatForm n ![u, v]) :
    sourceQuadraticMetricJetMean w θ g e z hz (A : ComplexModel n →L[ℂ] ComplexModel n) r =
      sourceQuadraticMetricJetMean w θ g e z hz (B : ComplexModel n →L[ℂ] ComplexModel n) r := by
  let Q₀ : ComplexModel n ≃L[ℂ] ComplexModel n := B.trans A.symm
  have hflat (u v : ComplexModel n) : flatForm n ![Q₀ u, Q₀ v] = flatForm n ![u, v] := by
    rw [← hA (Q₀ u) (Q₀ v)]
    simpa only [Q₀, ContinuousLinearEquiv.trans_apply, A.apply_symm_apply] using hB u v
  have hnorm (v : ComplexModel n) : ‖Q₀ v‖ = ‖v‖ := by
    have hh := hflat v (Complex.I • v)
    rw [map_smul, flatForm_apply_I_smul_self, flatForm_apply_I_smul_self] at hh
    have hpi : 0 < Real.pi⁻¹ := inv_pos.mpr Real.pi_pos
    have hsq := mul_left_cancel₀ hpi.ne' hh
    nlinarith [norm_nonneg (Q₀ v), norm_nonneg v]
  let Q : ComplexModel n ≃ₗᵢ[ℂ] ComplexModel n := { Q₀.toLinearEquiv with norm_map' := hnorm }
  have hAB : (A : ComplexModel n →L[ℂ] ComplexModel n).comp
      Q.toContinuousLinearEquiv.toContinuousLinearMap =
        (B : ComplexModel n →L[ℂ] ComplexModel n) := by
    apply ContinuousLinearMap.ext
    intro v
    change A (A.symm (B v)) = B v
    exact A.apply_symm_apply _
  have hh := sourceQuadraticMetricJetMean_unitary w θ g e z hz
    (A : ComplexModel n →L[ℂ] ComplexModel n) r Q
  rw [hAB] at hh
  exact hh.symm

end SGPT.NPP.DNTBig
