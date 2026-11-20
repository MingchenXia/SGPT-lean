import SGPT.Foundations.Analysis.FirstPass.RegularPatchNeighborhood

set_option autoImplicit false

/-!
# Local Borel interface for complex manifolds

A complex manifold in the present development carries a topology but deliberately
has no globally chosen `MeasurableSpace`: formalization clients may choose a
measurable structure for a separate construction.  The integration current of an
analytic subvariety, however, needs the canonical Borel structure of the ambient
topology.  This module exposes that structure *explicitly* as `borel M`, rather
than registering a global instance for every complex manifold.

In particular, a regular patch parametrization is a.e.-measurable from Lebesgue
measure on each closed parameter ball into `borel M`.  Its pushforward is thus a
well-defined finite Borel measure on the ambient manifold.  This is only a local
branch interface: it deliberately does not claim that these branch measures
assemble to the global integration current `[V]`.
-/

open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.ManifoldBorelFoundation

open FirstPass FirstPass.NumericalRestrictedVolume FirstPass.RegularPatchNeighborhood
open MeasureTheory

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The canonical measurable structure used by measure-theoretic constructions
on an ambient complex manifold.  This is an abbreviation, not an instance, so it
cannot silently override a measurable structure chosen by a client. -/
abbrev manifoldBorel (M : Type*) [TopologicalSpace M] : MeasurableSpace M := borel M

/-- A continuous map into a complex manifold is measurable when its codomain is
endowed explicitly with the Borel structure of the manifold topology. -/
theorem continuous_measurable_manifoldBorel
    {X : Type*} [TopologicalSpace X] (f : X → M) (hf : Continuous f) :
    @Measurable X M (borel X) (manifoldBorel M) f := by
  let _ : MeasurableSpace X := borel X
  let _ : MeasurableSpace M := manifoldBorel M
  let _ : BorelSpace X := ⟨rfl⟩
  let _ : BorelSpace M := ⟨rfl⟩
  exact hf.measurable

/-- A map continuous on a Borel subset is a.e.-measurable for a measure restricted
to that subset, with the ambient manifold carrying its explicit Borel structure. -/
theorem ContinuousOn.aemeasurable_restrict_manifoldBorel
    {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : @MeasurableSet X (borel X) s) (f : X → M) (hf : ContinuousOn f s)
    (μ : @Measure X (borel X)) :
    @AEMeasurable X M (manifoldBorel M) (borel X) f (μ.restrict s) := by
  let _ : MeasurableSpace X := borel X
  let _ : MeasurableSpace M := manifoldBorel M
  let _ : BorelSpace X := ⟨rfl⟩
  let _ : BorelSpace M := ⟨rfl⟩
  exact hf.aemeasurable hs

/-- The Borel pushforward of Lebesgue measure along one closed regular branch.
The codomain measurable structure is explicitly `manifoldBorel M`; no global
measurable-space instance is installed for `M`. -/
def regularPatchClosedBallPushforwardBorel
    {V : ClosedIrreducibleAnalyticSubvariety n M} (P : RegularPatch V) (r : ℝ) :
    @Measure M (manifoldBorel M) := by
  let _ : MeasurableSpace M := manifoldBorel M
  exact Measure.map P.toManifold
    (volume.restrict (Metric.closedBall (0 : ComplexModel V.dim) r))

/-- The parametrization of a regular branch is a.e.-measurable into the canonical
Borel measurable space of the ambient complex manifold. -/
theorem regularPatchAEMeasurableToManifoldRestrictClosedBallBorel
    {V : ClosedIrreducibleAnalyticSubvariety n M} (P : RegularPatch V) {r : ℝ}
    (hr : Metric.closedBall (0 : ComplexModel V.dim) r ⊆ P.parameterDomain) :
    @AEMeasurable (ComplexModel V.dim) M (manifoldBorel M) _ P.toManifold
      (volume.restrict (Metric.closedBall (0 : ComplexModel V.dim) r)) := by
  let _ : MeasurableSpace M := manifoldBorel M
  let _ : BorelSpace M := ⟨rfl⟩
  exact (FirstPass.RegularPatchNeighborhood.RegularPatch.continuousOn_toManifold P).mono hr |>.aemeasurable
    Metric.isClosed_closedBall.measurableSet

/-- Evaluation of a Borel regular-branch pushforward on a Borel set is evaluation
of its parameter measure on the preimage. -/
theorem regularPatchClosedBallPushforwardBorel_apply
    {V : ClosedIrreducibleAnalyticSubvariety n M} (P : RegularPatch V) {r : ℝ}
    (hr : Metric.closedBall (0 : ComplexModel V.dim) r ⊆ P.parameterDomain)
    (s : Set M) (hs : @MeasurableSet M (manifoldBorel M) s) :
    regularPatchClosedBallPushforwardBorel P r s =
      (volume.restrict (Metric.closedBall (0 : ComplexModel V.dim) r))
        (P.toManifold ⁻¹' s) := by
  let _ : MeasurableSpace M := manifoldBorel M
  let _ : BorelSpace M := ⟨rfl⟩
  rw [regularPatchClosedBallPushforwardBorel,
    Measure.map_apply_of_aemeasurable
      (regularPatchAEMeasurableToManifoldRestrictClosedBallBorel P hr) hs]

/-- Every compact regular branch has finite Borel mass.  This is the local
finiteness input for a future construction of the integration current of an
analytic subvariety. -/
theorem regularPatchClosedBallPushforwardBorel_univ_lt_top
    {V : ClosedIrreducibleAnalyticSubvariety n M} (P : RegularPatch V) {r : ℝ}
    (hr : Metric.closedBall (0 : ComplexModel V.dim) r ⊆ P.parameterDomain) :
    regularPatchClosedBallPushforwardBorel P r Set.univ < ⊤ := by
  let _ : MeasurableSpace M := manifoldBorel M
  let _ : BorelSpace M := ⟨rfl⟩
  rw [regularPatchClosedBallPushforwardBorel_apply P hr Set.univ MeasurableSet.univ]
  simpa only [Set.preimage_univ, Measure.restrict_apply_univ] using
    (measure_closedBall_lt_top :
      volume (Metric.closedBall (0 : ComplexModel V.dim) r) < ⊤)

/-- Integration against the Borel measure of a compact regular branch is its
Lebesgue integral in the parameter ball. -/
theorem regularPatchLintegralClosedBallPushforwardBorel
    {V : ClosedIrreducibleAnalyticSubvariety n M} (P : RegularPatch V) {r : ℝ}
    (hr : Metric.closedBall (0 : ComplexModel V.dim) r ⊆ P.parameterDomain)
    (f : M → ENNReal)
    (hf : @AEMeasurable M ENNReal _ (manifoldBorel M) f
      (regularPatchClosedBallPushforwardBorel P r)) :
    ∫⁻ x, f x ∂regularPatchClosedBallPushforwardBorel P r =
      ∫⁻ w, f (P.toManifold w) ∂
        (volume.restrict (Metric.closedBall (0 : ComplexModel V.dim) r)) := by
  let _ : MeasurableSpace M := manifoldBorel M
  let _ : BorelSpace M := ⟨rfl⟩
  exact MeasureTheory.lintegral_map' hf
    (regularPatchAEMeasurableToManifoldRestrictClosedBallBorel P hr)

end

end SGPT.Foundations.Analysis.Pending.ManifoldBorelFoundation
