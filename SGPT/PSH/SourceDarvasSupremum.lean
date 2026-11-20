import SGPT.PSH.SourceDarvasMetric
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasSupremumControl

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [CompactSpace M]

/-- The actual original whole-space non-pluripolar model mass. Genuine
finite measure and strict positivity justify its real readback below. -/
def sourceModelVolume (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) (hφ : SourceModelPotential θ φ) : ℝ :=
  (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal

theorem sourceModelVolume_eq_native
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ : SourceModelPotential θ φ) :
    sourceModelVolume θ φ hφ = RelativePreceqClasses.modelVolume
      (atlasClosedFormToNative θ) φ hφ.toNative := rfl

variable [BorelSpace M]

/-- Actual positive model mass and actual compact Kähler measure finiteness
produce strict positivity of the true scalar in the printed source bound. -/
theorem sourceModelVolume_pos (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : SourceModelPotential θ φ) : 0 < sourceModelVolume θ φ hφ := by
  rw [sourceModelVolume_eq_native]
  let := DiagonalMeasureRegularity.isFiniteMeasure_diagonalPotentialMeasure omega
    (atlasClosedFormToNative θ) hφ.toNative.plurisubharmonic
  exact ENNReal.toReal_pos hφ.toNative.positive_mass.ne' (measure_ne_top _ _)

/-- The genuine model itself is an original E1 potential, manufactured by
the actual same-type inclusion rather than supplied as a reference proof. -/
def sourceModelFiniteEnergyPotential (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ : SourceModelPotential θ φ) : SourceFiniteEnergyPotential θ φ hφ :=
  ⟨φ, (sourceRelativeFiniteEnergy_iff_native θ φ φ hφ).mpr
    (RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      ⟨hφ.toNative.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩)⟩

omit [BorelSpace M] in
/-- Actual positive mass, compact upper bounds and genuine nondegeneracy
exclude BOTH endpoints of the spatial supremum before real readback. -/
theorem sourceFiniteEnergyGlobalSup_finite
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    {hφ : SourceModelPotential θ φ} (u : SourceFiniteEnergyPotential θ φ hφ) :
    (⨆ x, u.val x) ≠ ⊤ ∧ (⨆ x, u.val x) ≠ ⊥ := by
  let : Nonempty M := ModelRaySupremum.nonempty_of_modelPotential hφ.toNative
  exact ModelRaySupremum.iSup_ne_top_ne_bot
    ((isThetaPSH_iff_nativeThetaPotential θ u.val).mp u.property.1.choose)

variable [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
  {hφ : SourceModelPotential θ φ}

/-- WHOLE original lma:d1bdsupX: both printed inequalities with the
actual original mass, true spatial supremum and uniform positive A,B.
All analytic uniform-integral/background inputs are produced internally. -/
theorem sourceDarvas_supremum_bounds (omega : KahlerBackground n M) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ u : SourceFiniteEnergyPotential θ φ hφ,
      -(sourceModelVolume θ φ hφ) * (⨆ x, u.val x).toReal ≤
          sourceDarvasDistance θ φ hφ u (sourceModelFiniteEnergyPotential omega θ φ hφ) ∧
      -(A * sourceDarvasDistance θ φ hφ u (sourceModelFiniteEnergyPotential omega θ φ hφ)) - B ≤
        -(sourceModelVolume θ φ hφ) * (⨆ x, u.val x).toReal := by
  obtain ⟨A, B, hA, hB, hbounds⟩ :=
    SingularModelDarvasSupremumControl.exists_pos_constants_supremum_bounds
      (θ := atlasClosedFormToNative θ) (φ := φ) (hφ := hφ.toNative) omega
  refine ⟨A, B, hA, hB, ?_⟩
  intro u
  have hn := hbounds u.val ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp u.property)
  simp only [sourceDarvasDistance_eq_native omega, sourceModelFiniteEnergyPotential,
    sourceModelVolume_eq_native]
  refine ⟨hn.1, ?_⟩
  linarith [hn.2]

/-- The genuine source supremum bound produces a uniform all-point bound
for an ARBITRARY Darvas-bounded original E1 family, without countability. -/
theorem sourceDarvas_bounded_family_global_upper {I : Type*}
    (omega : KahlerBackground n M) (ui : I → SourceFiniteEnergyPotential θ φ hφ)
    {R : ℝ} (hR : ∀ i, sourceDarvasDistance θ φ hφ (ui i)
      (sourceModelFiniteEnergyPotential omega θ φ hφ) ≤ R) :
    ∃ C : ℝ, ∀ i x, (ui i).val x ≤ (C : EReal) := by
  apply SingularModelDarvasSupremumControl.exists_uniform_upper_bound_of_relativeD1_le omega
    (fun i ↦ (sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp (ui i).property)
  intro i
  simpa only [sourceDarvasDistance_eq_native omega, sourceModelFiniteEnergyPotential] using hR i

end SGPT.PSH.VariableComplexAtlas
