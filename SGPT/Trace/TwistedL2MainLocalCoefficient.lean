import SGPT.Trace.TwistedL2MainCorrection

/-!
# Measurable local coefficients of the actual bundle correction

This file reads the actual correction in any holomorphic frame. The global
scalar representative is multiplied by the measurable unit-frame coefficient;
no differentiability or weak equation is asserted.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold ComplexConjugate InnerProductSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

namespace TwistedDatum

variable (T : TwistedDatum n X)

/-- The correction's coefficient in a frame, zero-extended off its base set. -/
def correctionFrameCoeff (u : Lp ℂ 2 (T.μ.restrict T.U)) (e : AtlasFrame T.L) (x : X) : ℂ :=
  ((T.sqrtW x : ℂ)⁻¹ * (u : X → ℂ) x) * e.val.baseSet.indicator (unitCoeff e) x

/-- The zero-extended frame coefficient is almost everywhere strongly
measurable for the actual restricted volume. -/
theorem aestronglyMeasurable_correctionFrameCoeff (u : Lp ℂ 2 (T.μ.restrict T.U))
    (e : AtlasFrame T.L) :
    AEStronglyMeasurable (T.correctionFrameCoeff u e) (T.μ.restrict T.U) := by
  have hw : Measurable (fun x : X => (T.sqrtW x : ℂ)⁻¹) :=
    (Complex.continuous_ofReal.measurable.comp T.measurable_sqrtW).inv
  exact (hw.aestronglyMeasurable.mul (Lp.memLp u).1).mul
    (measurable_indicator_unitCoeff e).aestronglyMeasurable

omit [BorelSpace X] in
/-- On the actual base set the measurable coefficient is the true frame
coefficient of the original bundle-valued correction. -/
theorem correctionFrameCoeff_of_mem (u : Lp ℂ 2 (T.μ.restrict T.U))
    (e : AtlasFrame T.L) {x : X} (hx : x ∈ e.val.baseSet) :
    T.correctionFrameCoeff u e x = (e.val ⟨x, T.correctionSection u x⟩).2 := by
  rw [correctionFrameCoeff, Set.indicator_of_mem hx, T.frameCoeff_correctionSection u e hx]

end TwistedDatum
end SGPT.Trace.TwistedL2
