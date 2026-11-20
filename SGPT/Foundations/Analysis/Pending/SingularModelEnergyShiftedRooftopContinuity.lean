import SGPT.Foundations.Analysis.Pending.SingularModelDarvasEnergyContinuity

set_option autoImplicit false

/-!
# Actual shifted rooftop exhaustion in finite energy

Xia SGPT PDF0134--0135 Proposition 3.1.24, with actual increasing
energy continuity from PDF0128--0129. A genuine common finite translation
transfers the actual normalized full-mass exhaustion to the full
singularity-order class. Actual shifted rooftop E1 membership and actual
increasing-net energy continuity produce real/extended energy limits,
and the ordered Darvas formula produces the distance limit.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyShiftedRooftopContinuity

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses ShiftedRooftopLimit

noncomputable section

private theorem regularization_iSup_add_const {X I : Type*} [TopologicalSpace X]
    (u : I → X → EReal) (c : ℝ) :
    uscRegularization (⨆ i, fun x => u i x + (c : EReal)) =
      fun x => uscRegularization (⨆ i, u i) x + (c : EReal) := by
  have hsup : (⨆ i, fun x => u i x + (c : EReal)) =
      fun x => (⨆ i, u i) x + (c : EReal) := by
    funext x
    simp only [iSup_apply]
    exact (NegligibleSetNotCharged.iSup_add_coe (fun i => u i x) c).symm
  rw [hsup, uscRegularization_add_coe_const]

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal} {hφ : IsModelPotential θ φ}

/-- Actual full-mass shifted rooftop exhaustion holds on the full singularity-order class. -/
theorem uscRegularization_iSup_rooftop_add_const_eq (omega : KahlerBackground n M)
    (hu : RelativeFullMassPreceq θ φ u hφ) (hv : RelativeFullMassPreceq θ φ v hφ) :
    uscRegularization (⨆ C : ℝ, rooftop θ u (fun x => v x + (C : EReal))) = u := by
  obtain ⟨c, hc₀, hc₁⟩ := exists_common_add_le hu.relativePSHPreceq hv.relativePSHPreceq
  have hreg := (FiniteGeodesicsFullMassAnyDim.uscRegularization_iSup_shiftedRooftop_eq
    omega θ φ (fun x => u x + (c : EReal)) (fun x => v x + (c : EReal)) hφ
    (hu.relativeFullMass_add hc₀) (hv.relativeFullMass_add hc₁)).2
  have hcov (C : ℝ) :
      shiftedRooftop θ (fun x => u x + (c : EReal)) (fun x => v x + (c : EReal)) C =
        fun x => rooftop θ u (fun y => v y + (C : EReal)) x + (c : EReal) := by
    change rooftop θ (fun x => u x + (c : EReal))
      (fun x => (v x + (c : EReal)) + (C : EReal)) = _
    rw [show (fun x => (v x + (c : EReal)) + (C : EReal)) =
        fun x => (v x + (C : EReal)) + (c : EReal) from
      funext fun x => add_right_comm (v x) (c : EReal) (C : EReal)]
    exact rooftop_add_const θ u (fun x => v x + (C : EReal)) c
  simp_rw [hcov] at hreg
  rw [regularization_iSup_add_const] at hreg
  exact funext fun x => add_coe_injective c (congrFun hreg x)

/-- Actual E1 shifted rooftops have actual real energies converging to the first obstacle energy. -/
theorem toReal_energy_rooftop_add_const_tendsto (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ) :
    Tendsto (fun C : ℝ => (energy θ φ hφ (rooftop θ u (fun x => v x + (C : EReal)))).toReal)
      atTop (𝓝 (energy θ φ hφ u).toReal) :=
  SingularModelEnergyIncreasingDirectedNets.toReal_energy_tendsto_of_directed_monotone_regularized
    omega (fun C => relativeFiniteEnergyPreceq_rooftop omega hu (hv.add_const omega C)) hu
    (fun x _ _ hCD => shiftedRooftop_monotone θ u v hCD x)
    (uscRegularization_iSup_rooftop_add_const_eq omega hu.1 hv.1)

/-- Actual finite-energy realification gives the defining extended shifted rooftop energy limit. -/
theorem energy_rooftop_add_const_tendsto (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ) :
    Tendsto (fun C : ℝ => energy θ φ hφ (rooftop θ u (fun x => v x + (C : EReal))))
      atTop (𝓝 (energy θ φ hφ u)) :=
  SingularModelEnergyIncreasingDirectedNets.energy_tendsto_of_directed_monotone_regularized
    omega (fun C => relativeFiniteEnergyPreceq_rooftop omega hu (hv.add_const omega C)) hu
    (fun x _ _ hCD => shiftedRooftop_monotone θ u v hCD x)
    (uscRegularization_iSup_rooftop_add_const_eq omega hu.1 hv.1)

/-- The true actual shifted rooftop energy limit also produces its actual Darvas distance limit. -/
theorem relativeD1_rooftop_add_const_tendsto_zero (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ) :
    Tendsto (fun C : ℝ => relativeD1 θ φ hφ (rooftop θ u (fun x => v x + (C : EReal))) u)
      atTop (𝓝 0) :=
  SingularModelDarvasEnergyContinuity.relativeD1_tendsto_zero_of_directed_monotone_regularized
    omega (fun C => relativeFiniteEnergyPreceq_rooftop omega hu (hv.add_const omega C)) hu
    (fun x _ _ hCD => shiftedRooftop_monotone θ u v hCD x)
    (uscRegularization_iSup_rooftop_add_const_eq omega hu.1 hv.1)

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyShiftedRooftopContinuity
