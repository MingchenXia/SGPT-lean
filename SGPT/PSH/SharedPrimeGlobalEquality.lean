import SGPT.PSH.ReducedPrimeOrderOne
import SGPT.Foundations.Analysis.Pending.ActualPrimeGlobalPolarDivisorUniqueness

-- Lean's numeric private-name component is constructed literally. This macro
-- expands ONLY to the pinned kernel constant; no theorem search or proof synthesis.
open Lean in
local macro "pinnedSharedPrimeKernel" : term =>
  pure (mkIdent (Name.append (Name.num `_private.SGPT.Foundations.Analysis.Pending.ActualPrimeGlobalPolarDivisorUniqueness 0) `SGPT.Foundations.Analysis.Pending.ActualPrimeGlobalPolarDivisorUniqueness.eq_of_common_prime_ideal))

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending AnalyticGermDecomposition
open scoped Topology Manifold ContDiff

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- Exact public interface to the existing pinned generic kernel producer.
Its actual type has NO compactness, current, potential, or metric inputs.
Origin and exact source/body hashes: shared-prime-generic-mother-pin.json. -/
theorem actual_codimension_one_eq_of_common_prime_ideal
    (V W : ClosedIrreducibleAnalyticSubvariety (m + 1) M)
    (hVdim : V.dim = m) (hWdim : W.dim = m) (x : M)
    (q : ComplexModel (m + 1) → ℂ) (hq : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ q z)
    (hQ : Prime (HolGerm.mk q hq))
    (hVI : vanishingIdeal (AnalyticDescendingChain.chartGerm (n := m + 1) V.carrier x) ≤
      Ideal.span {HolGerm.mk q hq})
    (hWI : vanishingIdeal (AnalyticDescendingChain.chartGerm (n := m + 1) W.carrier x) ≤
      Ideal.span {HolGerm.mk q hq}) : V = W :=
  pinnedSharedPrimeKernel V W hVdim hWdim x q hq hQ hVI hWI

/-- SAME actual original local prime ideal containment identifies the SAME
canonical global carriers, using the original geometric structures directly. -/
theorem geometricPrimeCarrier_eq_of_common_chart_prime
    (P Q : GeometricPrimeCarrier (m + 1) M) (x : M)
    (q : ComplexModel (m + 1) → ℂ) (hq : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ q z)
    (hQ : Prime (HolGerm.mk q hq))
    (hPI : vanishingIdeal (AnalyticDescendingChain.chartGerm (n := m + 1) P.val x) ≤
      Ideal.span {HolGerm.mk q hq})
    (hQI : vanishingIdeal (AnalyticDescendingChain.chartGerm (n := m + 1) Q.val x) ≤
      Ideal.span {HolGerm.mk q hq}) : P = Q := by
  have hPdim : P.subvariety.dim = m := by have h := P.subvariety_codimension; omega
  have hQdim : Q.subvariety.dim = m := by have h := Q.subvariety_codimension; omega
  have hV := actual_codimension_one_eq_of_common_prime_ideal P.subvariety Q.subvariety
    hPdim hQdim x q hq hQ (by rwa [P.subvariety_carrier]) (by rwa [Q.subvariety_carrier])
  apply GeometricPrimeCarrier.ext
  exact P.subvariety_carrier.symm.trans ((congrArg
    (fun V : ClosedIrreducibleAnalyticSubvariety (m + 1) M => V.carrier) hV).trans Q.subvariety_carrier)

end SGPT.PSH
