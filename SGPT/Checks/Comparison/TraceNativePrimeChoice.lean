import SGPT.Checks.Comparison.TraceNativeImagePoint
import SGPT.PSH.CompactPrimeOver

/-! Actual native prime charts and genuine ambient images, all dimensions.
Blueprint: trace-native-divisor-readers.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.NAPotential.TraceComparison.NativeImage
open Set AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.NAPotential.Berkovich SGPT.PSH.CompactPrimeOver
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open FixedGermNormalOrder DemaillyApproximantDivisorialLelong
open scoped Topology Manifold ContDiff

variable {m : ℕ} {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel (m+1)) V]
  [IsComplexManifold (m+1) V]

/-- SAME actual prime, point, divisor and original flattening. -/
structure PrimeChartData (p : PrimePresentation (m+1) V) where
  point : p.model
  mem : point ∈ p.divisor
  flattening : DivisorFlattening (m := m) p.divisor point

/-- Actual prime geometry supplies the chart internally. -/
def choosePrimeChartData (p : PrimePresentation (m+1) V) : PrimeChartData p := by
  classical
  have hdim : p.divisorDimension = m := by have h := p.codimension_one; omega
  have hE : IsClosedConnectedSubmanifold (m+1) p.divisor m := by simpa only [hdim] using p.smooth
  let z := Classical.choose hE.2.1.nonempty
  have hz : z ∈ p.divisor := Classical.choose_spec hE.2.1.nonempty
  exact ⟨z,hz,Classical.choice (DivisorFlattening.nonempty_of_regularAtDim (hE.2.2 z hz))⟩

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
local instance primeChoiceTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance primeChoiceCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance primeChoiceManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- The original ambient native image at an internally chosen actual
prime chart. No algebraization of the native target is assumed. -/
def primeImagePoint {k : ℕ} {W : Type} [TopologicalSpace W] [ChartedSpace (ComplexModel k) W]
    [IsComplexManifold k W] (ι : W → SchemeComplexPoint f)
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (p : PrimePresentation k W) (c : ℝ) (hc : 0 < c) : BerkovichPoint f := by
  cases k with
  | zero => exact False.elim (by have h := p.dimension_pos; omega)
  | succ j =>
    let d := choosePrimeChartData p
    exact nativeImagePoint f n (ι ∘ p.projection) (hι.comp p.modification.1) d.point d.flattening c hc

/-- Literal readback to the ORIGINAL shared image constructor. -/
theorem primeImagePoint_succ (ι : V → SchemeComplexPoint f)
    (hι : ContMDiff 𝓘(ℂ, ComplexModel (m+1)) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (p : PrimePresentation (m+1) V) (c : ℝ) (hc : 0 < c) :
    primeImagePoint f n ι hι p c hc =
      nativeImagePoint f n (ι ∘ p.projection) (hι.comp p.modification.1)
        (choosePrimeChartData p).point (choosePrimeChartData p).flattening c hc := rfl

end SGPT.NAPotential.TraceComparison.NativeImage
