import SGPT.Trace.TwistedL2FunctionalTwistedCurvatureLogDraft
import SGPT.Trace.TwistedL2MainPiece

/-!
# Logarithmic twist on actual book datum

Pointwise support for the twisted L² argument. Specializes the independent local Young and
log-Levi identities to the actual chart/frame/density data, and relates the
untwisted adjoint coefficient to the book's actual H₁ norm pointwise. No
global Bochner--Kodaira or functional estimate is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.Trace.TwistedL2.FunctionalTwistedDatumLocalYoungDraft

open Set Filter MeasureTheory Bundle Complex
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open SGPT.Trace.TwistedL2.FunctionalTwistedAdjointYoungDraft
open SGPT.Trace.TwistedL2.FunctionalTwistedCurvatureLogDraft

variable {n : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

namespace TwistedDatum
variable (T : SGPT.Trace.TwistedL2.TwistedDatum n X)

/-- The logarithmically shifted actual chart adjoint satisfies the precise
pointwise Young estimate on every actual chart/frame piece. -/
theorem datum_chartTheta_sub_log_young (c : ComplexChart n X) (e : AtlasFrame T.L)
    {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity T.μ c ρ)
    (h : ComplexModel n → ComplexModel n) {z : ComplexModel n}
    (hz : z ∈ T.pieceDomain c e) :
    T.a (c.val.symm z) * ‖chartTheta
        (fun w => localWeight T.L c e ρ T.φ w - Real.log (T.a (c.val.symm w))) h z‖ ^ 2 ≤
      (T.a (c.val.symm z) + T.b (c.val.symm z)) *
        ‖chartTheta (localWeight T.L c e ρ T.φ) h z‖ ^ 2 +
      ((T.a (c.val.symm z))⁻¹ + (T.b (c.val.symm z))⁻¹) *
        holDerivSq (fun w => T.a (c.val.symm w)) z (h z) := by
  have hO := T.isOpen_pieceDomain c e
  have hp := ((T.contDiffOn_localWeight e hρ z hz).contDiffAt (hO.mem_nhds hz)).differentiableAt
    (by simp)
  have ha := (((T.a_smooth c).mono (T.pieceDomain_subset_chartSmooth c e) z hz).contDiffAt
    (hO.mem_nhds hz)).differentiableAt (by simp)
  obtain ⟨m, M, hm, hbounds⟩ := T.bounds
  have hb := hbounds (c.val.symm z) hz.2
  have ha0 : 0 < T.a (c.val.symm z) := hm.trans_le hb.1
  have hb0 : 0 < T.b (c.val.symm z) := hm.trans_le hb.2.2.1
  exact chartTheta_sub_log_young_curvature (localWeight T.L c e ρ T.φ)
    (fun w => T.a (c.val.symm w)) (fun w => T.b (c.val.symm w)) h hp ha ha0 hb0

/-- Actual chart-level comparison after cancellation of the log-Levi and
Young errors. This is purely pointwise and does not assume BKN. -/
theorem datum_twistedCurvature_le_shiftedLevi_and_adjoint
    (c : ComplexChart n X) (e : AtlasFrame T.L)
    {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity T.μ c ρ)
    (h : ComplexModel n → ComplexModel n) {z : ComplexModel n}
    (hz : z ∈ T.pieceDomain c e) :
    twistedCurvature (fun w => T.a (c.val.symm w)) (fun w => T.b (c.val.symm w))
        (localWeight T.L c e ρ T.φ) z (h z) ≤
      T.a (c.val.symm z) * leviForm
          (fun w => localWeight T.L c e ρ T.φ w - Real.log (T.a (c.val.symm w))) z (h z) +
        (T.a (c.val.symm z) + T.b (c.val.symm z)) *
          ‖chartTheta (localWeight T.L c e ρ T.φ) h z‖ ^ 2 -
        T.a (c.val.symm z) * ‖chartTheta
          (fun w => localWeight T.L c e ρ T.φ w - Real.log (T.a (c.val.symm w))) h z‖ ^ 2 := by
  have hO := T.isOpen_pieceDomain c e
  have hp : ContDiffAt ℝ 2 (localWeight T.L c e ρ T.φ) z :=
    ((T.contDiffOn_localWeight e hρ z hz).contDiffAt (hO.mem_nhds hz)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have ha : ContDiffAt ℝ 2 (fun w => T.a (c.val.symm w)) z :=
    (((T.a_smooth c).mono (T.pieceDomain_subset_chartSmooth c e) z hz).contDiffAt
      (hO.mem_nhds hz)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  obtain ⟨m, M, hm, hbounds⟩ := T.bounds
  have hb := hbounds (c.val.symm z) hz.2
  have ha0 : 0 < T.a (c.val.symm z) := hm.trans_le hb.1
  have hb0 : 0 < T.b (c.val.symm z) := hm.trans_le hb.2.2.1
  have hid := twistedCurvature_eq_log_shift_sub_young
    (localWeight T.L c e ρ T.φ) (fun w => T.a (c.val.symm w))
    (fun w => T.b (c.val.symm w)) hp ha ha0 hb0 (h z)
  have hy := datum_chartTheta_sub_log_young T c e hρ h hz
  linarith

/-- The original `T*` section, measured in the original H₁ weight, has
exactly the (a+b)-weighted local-adjoint squared norm. -/
theorem localTStar_H1weight_eq (c : ComplexChart n X) (e : AtlasFrame T.L)
    (ρ : ComplexModel n → ℝ) (h : ComplexModel n → ComplexModel n)
    {x : X} (hxU : x ∈ T.U) (hx : x ∈ c.val.source ∩ e.val.baseSet) :
    ‖T.localTStar c e ρ h x‖ ^ 2 * T.H1weight x =
      (T.a x + T.b x) * ‖chartTheta (localWeight T.L c e ρ T.φ) h (c.val x)‖ ^ 2 *
        frameNormSq T.L e x * Real.exp (-T.φ x) := by
  have hab : 0 < T.a x + T.b x := T.ab_pos hxU
  rw [T.localTStar_of_mem hx, norm_smul, mul_pow]
  simp only [SGPT.Trace.TwistedL2.TwistedDatum.pieceTheta, c.val.left_inv hx.1, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hab.le, mul_pow, frameNormSq, SGPT.Trace.TwistedL2.TwistedDatum.H1weight]
  field_simp [hab.ne']

/-- The same identity for the actual unit-frame coordinate used by the
already constructed Hilbert space H₁. -/
theorem H1coord_localTStar_sq_eq (c : ComplexChart n X) (e : AtlasFrame T.L)
    (ρ : ComplexModel n → ℝ) (h : ComplexModel n → ComplexModel n)
    {x : X} (hxU : x ∈ T.U) (hx : x ∈ c.val.source ∩ e.val.baseSet) :
    ‖T.H1coord (T.localTStar c e ρ h) x‖ ^ 2 =
      (T.a x + T.b x) * ‖chartTheta (localWeight T.L c e ρ T.φ) h (c.val x)‖ ^ 2 *
        frameNormSq T.L e x * Real.exp (-T.φ x) := by
  rw [T.norm_H1coord_sq _ hxU]
  exact localTStar_H1weight_eq T c e ρ h hxU hx

end TwistedDatum
end SGPT.Trace.TwistedL2.FunctionalTwistedDatumLocalYoungDraft
