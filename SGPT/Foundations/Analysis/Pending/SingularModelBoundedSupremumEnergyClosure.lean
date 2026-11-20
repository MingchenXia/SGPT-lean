import SGPT.Foundations.Analysis.Pending.SingularModelDarvasEnergyContinuity
import SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyGapMax
import SGPT.Foundations.Analysis.Pending.RelativePreceqStatements

set_option autoImplicit false

/-!
# Actual bounded regularized supremum closure in the singularity-order classes

Xia SGPT PDF0134 Proposition 3.1.23, all three source preceq classes.
The actual bounded-family genuine supremum and the actual fixed-model
normalization produce the limit's singularity-order class. Existing genuine
full-mass/finite-energy upward closure then produces the actual membership.
The increasing directed Darvas consumer has its actual E1 limit produced here;
no genuine or finite-energy limit certificate is an input.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelBoundedSupremumEnergyClosure

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal} {hφ : IsModelPotential θ φ}
  {I : Type*} [Nonempty I] {ui : I → M → EReal} {C : ℝ}

omit [BorelSpace M] in
private theorem relativePSHPreceq_uscRegularization_iSup
    (hmodel : IsModelPotential θ φ)
    (hui : ∀ i, RelativePSHPreceq θ φ (ui i))
    (hC : ∀ i x, ui i x ≤ (C : EReal)) :
    RelativePSHPreceq θ φ (uscRegularization (⨆ i, ui i)) := by
  have hU := IncreasingMixedDirectedNets.isThetaPshPotential_regularized_of_uniformlyBounded
    (fun i => (hui i).1) hC
  have hle : (⨆ i, ui i) ≤ fun x => φ x + (C : EReal) := iSup_le fun i x =>
    RelativePreceqStatements.le_add_const_of_moreSingularOn_of_singularityEnvelope_eq
      (hui i).1 hmodel.envelope_eq.symm (hui i).2 (hC i) x
  have hUle : uscRegularization (⨆ i, ui i) ≤ fun x => φ x + (C : EReal) :=
    uscRegularization_le (hmodel.plurisubharmonic.add_const C).1.quasiPlurisubharmonic.upperSemicontinuous hle
  exact ⟨hU, ⟨C, fun x _ => hUle x⟩⟩

/-- Source Proposition 3.1.23 in the actual full-mass singularity-order class, in every dimension. -/
theorem relativeFullMassPreceq_uscRegularization_iSup (omega : KahlerBackground n M)
    (hui : ∀ i, RelativeFullMassPreceq θ φ (ui i) hφ)
    (hC : ∀ i x, ui i x ≤ (C : EReal)) :
    RelativeFullMassPreceq θ φ (uscRegularization (⨆ i, ui i)) hφ := by
  have hU := relativePSHPreceq_uscRegularization_iSup hφ (fun i => (hui i).relativePSHPreceq) hC
  let i0 : I := Classical.arbitrary I
  have hle : ui i0 ≤ uscRegularization (⨆ i, ui i) :=
    (le_iSup (fun i => ui i) i0).trans (le_uscRegularization _)
  exact RelativePreceqStatements.relativeFullMassPreceq_of_singularity_between omega
    (hui i0) hU.1 (MoreSingularOn.of_le fun x _ => hle x) hU.2

/-- Source Proposition 3.1.23 in the actual full finite-energy singularity-order class. -/
theorem relativeFiniteEnergyPreceq_uscRegularization_iSup (omega : KahlerBackground n M)
    (hui : ∀ i, RelativeFiniteEnergyPreceq θ φ (ui i) hφ)
    (hC : ∀ i x, ui i x ≤ (C : EReal)) :
    RelativeFiniteEnergyPreceq θ φ (uscRegularization (⨆ i, ui i)) hφ := by
  have hU := relativePSHPreceq_uscRegularization_iSup hφ
    (fun i => (hui i).1.relativePSHPreceq) hC
  let i0 : I := Classical.arbitrary I
  have hle : ui i0 ≤ uscRegularization (⨆ i, ui i) :=
    (le_iSup (fun i => ui i) i0).trans (le_uscRegularization _)
  exact SingularModelFiniteEnergyGapMax.relativeFiniteEnergyPreceq_of_le omega
    (hui i0) hU hle

include hφ in
omit [BorelSpace M] in
/-- Source Proposition 3.1.23 in the actual same-singularity-type class. -/
theorem relativeEInfinity_uscRegularization_iSup
    (hui : ∀ i, RelativeEInfinity θ φ (ui i))
    (hC : ∀ i x, ui i x ≤ (C : EReal)) :
    RelativeEInfinity θ φ (uscRegularization (⨆ i, ui i)) := by
  have hU := relativePSHPreceq_uscRegularization_iSup hφ
    (fun i => ⟨(hui i).1, (hui i).2.1⟩) hC
  let i0 : I := Classical.arbitrary I
  have hle : ui i0 ≤ uscRegularization (⨆ i, ui i) :=
    (le_iSup (fun i => ui i) i0).trans (le_uscRegularization _)
  exact ⟨hU.1, hU.2, (hui i0).2.2.trans (MoreSingularOn.of_le fun x _ => hle x)⟩

variable [ConnectedSpace M]

/-- A bounded increasing actual finite-energy net has its actual Darvas limit produced at its supremum. -/
theorem relativeD1_tendsto_zero_of_directed_monotone_uniformlyBounded
    [Preorder I] [IsDirectedOrder I] (omega : KahlerBackground n M)
    (hui : ∀ i, RelativeFiniteEnergyPreceq θ φ (ui i) hφ)
    (hm : ∀ x, Monotone fun i => ui i x) (hC : ∀ i x, ui i x ≤ (C : EReal)) :
    Tendsto (fun i => relativeD1 θ φ hφ (ui i) (uscRegularization (⨆ j, ui j)))
      atTop (𝓝 0) :=
  SingularModelDarvasEnergyContinuity.relativeD1_tendsto_zero_of_directed_monotone_regularized
    omega hui (relativeFiniteEnergyPreceq_uscRegularization_iSup omega hui hC) hm rfl

end

end SGPT.Foundations.Analysis.Pending.SingularModelBoundedSupremumEnergyClosure
