module

public import SGPT.Foundations.Analysis.FirstPass.ExteriorDerivative

/-!
# Compatibility names for proved complex geometry

Both statements are now proved in `FirstPass.ExteriorDerivative`; these names
preserve the original interface without adding a `sorryAx` dependency. The first
compares actual real and complex derivatives of holomorphic chart transitions.
The second is the overlap equation for actual exterior derivatives of a form.

No Kähler existence theorem for a general manifold is postulated. The checked
definition of closedness tests the genuine exterior derivative in every chart;
the checked core now also bundles this derivative as a global smooth form.
-/

@[expose] public section

open scoped Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending

open FirstPass

/-- Compatibility wrapper: holomorphic changes of coordinates have
complex-linear real derivatives. -/
theorem chartTransitionDerivative_complex_smul
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] (e f : ComplexChart n M) (z : ComplexModel n)
    (hz : z ∈ (chartTransition e f).source) (c : ℂ) (v : ComplexModel n) :
    chartTransitionDerivative e f z (c • v) = c • chartTransitionDerivative e f z v :=
  FirstPass.chartTransitionDerivative_complex_smul e f z hz c v

/-- Compatibility wrapper: the local exterior derivatives obey the form
transformation law. The proof uses locality and actual pullback naturality. -/
theorem exteriorDerivative_compatible
    {n k : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] (form : SmoothRealForm n M k)
    (e f : ComplexChart n M) (z : ComplexModel n)
    (hz : z ∈ (chartTransition e f).source) (v : Fin (k + 1) → ComplexModel n) :
    extDeriv (form.coeff e) z v =
      extDeriv (form.coeff f) (chartTransition e f z)
        (fun i => chartTransitionDerivative e f z (v i)) :=
  FirstPass.exteriorDerivative_compatible form e f z hz v

end SGPT.Foundations.Analysis.Pending
