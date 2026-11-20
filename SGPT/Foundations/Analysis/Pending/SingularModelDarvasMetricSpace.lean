import SGPT.Foundations.Analysis.Pending.SingularModelDarvasEnergyContinuity
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasSeparation
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

/-!
# The native actual Darvas metric space and continuous model energy

Xia SGPT PDF0160--0161 and PDF0169 Theorem 4.3.3. The existing actual
metric laws construct a native MetricSpace on the actual E1 subtype.
Actual rooftop energy order supplies a native one-Lipschitz real energy
map. Completeness remains separate from the metric-space construction.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelDarvasMetricSpace

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
open RelativePreceqClasses SingularModelDarvasEnergyContinuity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal} {hφ : IsModelPotential θ φ}

/-- The actual full singularity-order finite-energy potential subtype. -/
abbrev ModelFiniteEnergyPotential (θ : ClosedRealOneOneForm n M) (φ : M → EReal)
    (hφ : IsModelPotential θ φ) := {u : M → EReal // RelativeFiniteEnergyPreceq θ φ u hφ}

/-- The native metric structure has exactly the actual defining Darvas distance. -/
@[instance_reducible]
def finiteEnergyMetricSpace (omega : KahlerBackground n M) :
    MetricSpace (ModelFiniteEnergyPotential θ φ hφ) where
  dist u v := relativeD1 θ φ hφ u.val v.val
  dist_self u := relativeD1_self u.property.1.plurisubharmonic
  dist_comm u v := relativeD1_comm θ φ hφ u.val v.val
  dist_triangle u v w := SingularModelDarvasContraction.relativeD1_triangle omega
    u.property w.property v.property
  eq_of_dist_eq_zero {u v} h := Subtype.ext
    (SingularModelDarvasSeparation.eq_of_relativeD1_eq_zero_of_preceq omega
      u.property v.property h)

/-- Native distance is transparently the actual Darvas functional. -/
theorem dist_eq_relativeD1 (omega : KahlerBackground n M)
    (u v : ModelFiniteEnergyPotential θ φ hφ) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    dist u v = relativeD1 θ φ hφ u.val v.val := rfl

/-- The actual real model energy is one-Lipschitz in its native actual Darvas metric. -/
theorem energy_lipschitzWith (omega : KahlerBackground n M) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    LipschitzWith 1 (fun u : ModelFiniteEnergyPotential θ φ hφ =>
      (energy θ φ hφ u.val).toReal) := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simp only [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_relativeD1]
  exact abs_energy_sub_le_relativeD1 omega u.property v.property

/-- Native continuity of the defining finite real model energy, on the full E1 subtype. -/
theorem energy_continuous (omega : KahlerBackground n M) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
    Continuous (fun u : ModelFiniteEnergyPotential θ φ hφ =>
      (energy θ φ hφ u.val).toReal) := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  exact (energy_lipschitzWith (θ := θ) (φ := φ) (hφ := hφ) omega).continuous

end

end SGPT.Foundations.Analysis.Pending.SingularModelDarvasMetricSpace
