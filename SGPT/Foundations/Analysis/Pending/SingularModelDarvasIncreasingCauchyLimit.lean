import SGPT.Foundations.Analysis.Pending.SingularModelDarvasSupremumControl
import SGPT.Foundations.Analysis.Pending.SingularModelBoundedSupremumEnergyClosure
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasMetricSpace
import Mathlib.Topology.MetricSpace.Cauchy

set_option autoImplicit false

/-!
# Actual increasing native Darvas Cauchy limits

Xia SGPT PDF0167, the increasing half of Theorem 4.3.2.
Actual native Cauchyness first produces a distance-to-model bound. The
actual source supremum estimate then produces global upper boundedness;
actual regularized-supremum closure produces the finite-energy limit.
The native Darvas uniformity and topology are explicitly selected.
The decreasing case and metric completeness are separate obligations.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelDarvasIncreasingCauchyLimit

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularModelDarvasMetricSpace

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal} {hφ : IsModelPotential θ φ}

/-- Actual native Cauchyness produces uniform distance-to-model boundedness. -/
theorem exists_pos_bound_relativeD1_of_cauchySeq (omega : KahlerBackground n M)
    (ui : ℕ → ModelFiniteEnergyPotential θ φ hφ) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    CauchySeq ui → ∃ R : ℝ, 0 < R ∧ ∀ i, relativeD1 θ φ hφ (ui i).val φ ≤ R := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  intro hc
  obtain ⟨R, hR, hbound⟩ := cauchySeq_bdd hc
  have hφfinite : RelativeFiniteEnergyPreceq θ φ φ hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      ⟨hφ.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩
  have hd0 : 0 ≤ relativeD1 θ φ hφ (ui 0).val φ :=
    SingularModelDarvasBasic.relativeD1_nonneg omega (ui 0).property hφfinite
  refine ⟨R + relativeD1 θ φ hφ (ui 0).val φ, add_pos_of_pos_of_nonneg hR hd0, ?_⟩
  intro i
  have hpair : relativeD1 θ φ hφ (ui i).val (ui 0).val < R := hbound i 0
  exact (SingularModelDarvasContraction.relativeD1_triangle omega
    (ui i).property hφfinite (ui 0).property).trans
    (add_le_add hpair.le le_rfl)

/-- An actual pointwise increasing native Cauchy sequence has its actual E1 metric limit produced. -/
theorem tendsto_uscRegularization_iSup_of_monotone_cauchySeq
    (omega : KahlerBackground n M) (ui : ℕ → ModelFiniteEnergyPotential θ φ hφ)
    (hm : ∀ x, Monotone fun i => (ui i).val x) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    letI : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
    CauchySeq ui →
      ∃ hU : RelativeFiniteEnergyPreceq θ φ
          (uscRegularization (⨆ i, (ui i).val)) hφ,
        Tendsto ui atTop (𝓝 (⟨uscRegularization (⨆ i, (ui i).val), hU⟩ :
          ModelFiniteEnergyPotential θ φ hφ)) := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  let : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  intro hc
  obtain ⟨R, _, hR⟩ := exists_pos_bound_relativeD1_of_cauchySeq omega ui hc
  obtain ⟨C, hC⟩ := SingularModelDarvasSupremumControl.exists_uniform_upper_bound_of_relativeD1_le
    omega (fun i => (ui i).property) hR
  have hU := SingularModelBoundedSupremumEnergyClosure.relativeFiniteEnergyPreceq_uscRegularization_iSup
    omega (fun i => (ui i).property) hC
  refine ⟨hU, tendsto_iff_dist_tendsto_zero.mpr ?_⟩
  exact SingularModelBoundedSupremumEnergyClosure.relativeD1_tendsto_zero_of_directed_monotone_uniformlyBounded
    omega (fun i => (ui i).property) hm hC

end

end SGPT.Foundations.Analysis.Pending.SingularModelDarvasIncreasingCauchyLimit
