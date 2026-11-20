import SGPT.Trace.TwistedL2MainLocalTests

/-!
# Pointwise pairing in a chart frame

The remaining step is to integrate this identity with the chart-density
pushforward and the compact support of a local test piece.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle Complex
open scoped Topology ENNReal ContDiff Manifold ComplexConjugate InnerProductSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

namespace TwistedDatum

variable (T : TwistedDatum n X)

/-- The inner-product integrand of the actual test section against the
actual L² correction, written in the same chart frame. -/
theorem H1coord_localTStar_pairing (u : Lp ℂ 2 (T.μ.restrict T.U))
    (c : ComplexChart n X) (e : AtlasFrame T.L) (ρ : ComplexModel n → ℝ)
    (h : ComplexModel n → ComplexModel n) {x : X} (hU : x ∈ T.U)
    (hx : x ∈ c.val.source ∩ e.val.baseSet) :
    conj (T.H1coord (T.localTStar c e ρ h) x) * (u : X → ℂ) x =
      conj (T.pieceTheta c e ρ h (c.val x)) * T.correctionFrameCoeff u e x *
        ((frameNormSq T.L e x * T.H1weight x : ℝ) : ℂ) := by
  have hw : (T.sqrtW x : ℂ) ≠ 0 := by
    exact_mod_cast (T.sqrtW_pos hU).ne'
  have hw2 : (T.sqrtW x : ℂ) ^ 2 = (T.H1weight x : ℂ) := by
    exact_mod_cast T.sqrtW_sq hU
  rw [T.H1coord_localTStar, Set.indicator_of_mem hx, Set.indicator_of_mem hx.2,
    correctionFrameCoeff, Set.indicator_of_mem hx.2, Complex.ofReal_mul, ← hw2]
  simp only [map_mul, Complex.conj_ofReal, conj_conj]
  field_simp [hw]

end TwistedDatum
end SGPT.Trace.TwistedL2
