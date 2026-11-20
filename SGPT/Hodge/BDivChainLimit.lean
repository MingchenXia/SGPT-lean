import SGPT.BDivisor.BlowupModelNef
import SGPT.BDivisor.Modification3AugmentedNef

/-!
# Modelwise eventual agreement and limits of b-divisors

A source-facing producer for the realization argument in `thm:bigandnefreal`:
if modelwise-convergent b-divisors eventually agree with a fixed b-divisor at
each fixed model, then their limit is that fixed b-divisor. The filter may be
arbitrary and nontrivial. No finite-dimensionality assumption is needed.
-/

set_option autoImplicit false
noncomputable section
universe u

open Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses

namespace SGPT.BDivisor.WeilBDivisorOn

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
  {S : ModelSystem n X} {hn : 0 < n}

/-- Modelwise eventual equality and a modelwise limit determine the same
b-divisor; the Euclidean topology on every real Bott--Chern space is Hausdorff. -/
theorem eq_of_converges_of_eventually_eq {ι : Type*} {l : Filter ι} [l.NeBot]
    {D : ι → WeilBDivisorOn S hn} {E F : WeilBDivisorOn S hn}
    (hlim : Converges l D E)
    (hevent : ∀ π : S.Model, ∀ᶠ i in l, (D i).onModel π = F.onModel π) : E = F := by
  apply WeilBDivisorOn.ext
  intro π
  let : TopologicalSpace (RealBottChern n π.1.carrier) := euclideanTopology _
  let : T2Space (RealBottChern n π.1.carrier) := t2Space_euclideanTopology _
  have hconst : Tendsto (fun i => (D i).onModel π) l (𝓝 (F.onModel π)) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [hevent π] with i hi
      exact hi.symm)
  exact tendsto_nhds_unique (hlim π) hconst

end SGPT.BDivisor.WeilBDivisorOn

#print axioms SGPT.BDivisor.WeilBDivisorOn.eq_of_converges_of_eventually_eq
