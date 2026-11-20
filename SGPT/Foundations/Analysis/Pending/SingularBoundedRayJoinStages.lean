import SGPT.Foundations.Analysis.Pending.SingularModelOriginRayEnergy
import SGPT.Foundations.Analysis.Pending.ModelRaySupremum
import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRestriction
import SGPT.Foundations.Analysis.Pending.DominationPrincipleReduction

set_option autoImplicit false

/-! # Actual terminal-maximum Perron stages for bounded rays -/

open Set

namespace SGPT.Foundations.Analysis.Pending.SingularBoundedRayJoinStages

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses RelativePreceqRays

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual closed Perron stage joins the model to the pointwise maximum of the two genuine terminal slices. -/
def joinStage (θ : ClosedRealOneOneForm n M) (φ : M → EReal)
    (ℓ ℓ' : ℝ → M → EReal) (T s : ℝ) : M → EReal :=
  closedSubgeodesicSlice (finiteGeodesic θ.val φ (fun x => max (ℓ T x) (ℓ' T x)))
    φ (fun x => max (ℓ T x) (ℓ' T x)) (s / T)

/-- The actual stage returns the model at its initial time. -/
theorem joinStage_zero (θ : ClosedRealOneOneForm n M) (φ : M → EReal)
    (ℓ ℓ' : ℝ → M → EReal) (T : ℝ) : joinStage θ φ ℓ ℓ' T 0 = φ := by
  simp only [joinStage, zero_div, closedSubgeodesicSlice_zero]

/-- The actual positive-length stage returns the exact terminal maximum. -/
theorem joinStage_terminal (θ : ClosedRealOneOneForm n M) (φ : M → EReal)
    (ℓ ℓ' : ℝ → M → EReal) {T : ℝ} (hT : 0 < T) :
    joinStage θ φ ℓ ℓ' T T = fun x => max (ℓ T x) (ℓ' T x) := by
  rw [joinStage, div_self hT.ne', closedSubgeodesicSlice_one]

/-- A genuine maximum of two actual finite-type potentials has that same finite singularity type, poles included. -/
theorem relativeEInfinity_max {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal}
    (hu : RelativeEInfinity θ φ u) (hv : RelativeEInfinity θ φ v) :
    RelativeEInfinity θ φ (fun x => max (u x) (v x)) := by
  refine ⟨SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max
    hu.plurisubharmonic hv.plurisubharmonic, ?_, ?_⟩
  · exact DominationPrincipleReduction.moreSingularOn_max
      hu.sameSingularityType.1 hv.sameSingularityType.1
  · exact hu.sameSingularityType.2.trans
      (MoreSingularOn.of_le fun _ _ => le_max_left _ _)

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal} {hφ : IsModelPotential θ φ}
  {ℓ ℓ' : ℝ → M → EReal}

/-- Genuine bounded source rays internally produce full-mass Perron joint PSH and actual finite-type class membership at every closed join-stage time. -/
theorem relativeEInfinity_joinStage (omega : KahlerBackground n M)
    (hℓ : IsBoundedRayFromModel θ φ hφ ℓ)
    (hℓ' : IsBoundedRayFromModel θ φ hφ ℓ')
    {T s : ℝ} (hT : 0 < T) (hs : s ∈ Icc (0 : ℝ) T) :
    RelativeEInfinity θ φ (joinStage θ φ ℓ ℓ' T s) := by
  have h0 : RelativeEInfinity θ φ φ :=
    ⟨hφ.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩
  have h1 : RelativeEInfinity θ φ (fun x => max (ℓ T x) (ℓ' T x)) :=
    relativeEInfinity_max (hℓ.1.2 T hT.le) (hℓ'.1.2 T hT.le)
  have hf0 : RelativeFiniteEnergyPreceq θ φ φ hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega h0
  have hf1 : RelativeFiniteEnergyPreceq θ φ (fun x => max (ℓ T x) (ℓ' T x)) hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega h1
  have hsub := finiteGeodesic_isSubgeodesicFrom_of_relativeFullMassPreceq omega hf0.1 hf1.1
  exact relativeEInfinity_closedSubgeodesicSlice_finiteGeodesic_of_interior
    θ φ φ (fun x => max (ℓ T x) (ℓ' T x)) hφ h0 h1 hsub.2.2.1
      ⟨div_nonneg hs.1 hT.le, (div_le_one hT).mpr hs.2⟩

end

end SGPT.Foundations.Analysis.Pending.SingularBoundedRayJoinStages
