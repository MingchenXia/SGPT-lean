import SGPT.Trace.TwistedL2MainGluing
import SGPT.Trace.TwistedL2MainFiniteReduction

/-!
# Conditional completion from the functional estimate

This draft derives the original raw-argument twisted L² statement from the
finite-test functional inequality. That inequality remains an unproved
analytic input and is not discharged by this file.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold ComplexConjugate InnerProductSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

namespace TwistedDatum

variable (T : TwistedDatum n X)

/-- For finite data energy, the functional estimate produces a holomorphic
section with the original twisted energy bound. -/
theorem correction_of_functional_finite
    (hfunctional : TwistedFunctionalBoundStatement n X)
    (hfinite : ∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ < ⊤) :
    ∃ S : (x : X) → T.L.Fiber x,
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) T.L.Fiber S T.U ∧
      (∫⁻ x in T.U, ENNReal.ofReal
        (‖T.G x - S x‖ ^ 2 * Real.exp (-T.φ x) / (T.a x + T.b x)) ∂T.μ) ≤
        ∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ := by
  obtain ⟨u, hbound, htest⟩ := T.exists_bundle_correction_of_functional hfunctional hfinite
  obtain ⟨S, hS, hSae⟩ := T.exists_holomorphic_section_ae_difference u htest
  refine ⟨S, hS, ?_⟩
  calc
    (∫⁻ x in T.U, ENNReal.ofReal
        (‖T.G x - S x‖ ^ 2 * Real.exp (-T.φ x) / (T.a x + T.b x)) ∂T.μ) =
      ∫⁻ x in T.U, ENNReal.ofReal
        (‖T.correctionSection u x‖ ^ 2 * T.H1weight x) ∂T.μ := by
          apply lintegral_congr_ae
          filter_upwards [hSae] with x hx
          have hdiff : T.G x - S x = T.correctionSection u x := by rw [hx]; abel
          rw [hdiff, H1weight]
          congr 1
          ring
    _ ≤ ∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ := hbound

end TwistedDatum

/-- The genuine finite-family analytic estimate implies the exact original
unbundled twisted L² correction statement. The analytic estimate remains an
explicit unproved hypothesis. -/
theorem twistedL2CorrectionStatement_of_functional
    (hfunctional : TwistedFunctionalBoundStatement n X) : TwistedL2CorrectionStatement n X := by
  intro omega U hU r hkahler hcomplete μ hμ L hmetric φ a b hφ ha hb hbounds hcurv
    G hG D Dσ hD hDσ hDσint
  let T : TwistedDatum n X :=
    ⟨omega, U, hU, r, hkahler, hcomplete, μ, hμ, L, hmetric, φ, a, b, hφ, ha, hb,
      hbounds, hcurv, G, hG, D, Dσ, hD, hDσ, hDσint⟩
  exact correction_of_finite_data
    (fun T hfinite => T.correction_of_functional_finite hfunctional hfinite) T

end SGPT.Trace.TwistedL2
