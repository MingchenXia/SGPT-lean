import SGPT.Toric.GlobalTropicalChartMass
import SGPT.Toric.ProjectiveToricNonPluripolarMass
import SGPT.Okounkov.MultiplierCancellation

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open scoped Topology ContDiff RealInnerProductSpace

local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)

/-- The existing actual P1 patch supplies the local FS potential unchanged. -/
theorem projectiveTropicalLocalPotential :
    IsSmoothLocalPotential projectiveNativeFSBackground.form.val
      (projectiveNativeChart false) (tropicalSmoothDomain 1) projectiveFSPotential :=
  (projectiveToricPuncturedPatch isThetaPSH_projectiveZero).localPotential (0 : Fin 1)

/-- The original Euclidean profile is defined from the source function alone. -/
def projectiveToricEuclideanProfile (u : P1 → EReal)
    (x : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  (projectiveToricCorrectedDescent u x).toReal

private theorem projectiveEuclideanProfile_coe {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) (x : EuclideanSpace ℝ (Fin 1)) :
    (projectiveToricEuclideanProfile u x : EReal) = projectiveToricCorrectedDescent u x := by
  obtain ⟨g, _hg, he⟩ := exists_real_convex_projectiveToricCorrectedDescent hu hi
  simp only [projectiveToricEuclideanProfile, he, EReal.toReal_coe]

/-- Original source PSH and invariance manufacture convexity on the whole space. -/
theorem projectiveToricEuclideanProfile_convex {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    ConvexOn ℝ univ (projectiveToricEuclideanProfile u) := by
  obtain ⟨g, hg, he⟩ := exists_real_convex_projectiveToricCorrectedDescent hu hi
  have hfg : projectiveToricEuclideanProfile u = g := by
    funext x
    simp only [projectiveToricEuclideanProfile, he, EReal.toReal_coe]
  rw [hfg]
  exact hg

/-- The same actual inverse chart reads precisely the original finite profile. -/
theorem projectiveToricEuclideanProfile_corrected {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    EqOn (fun z => chartFunction u (projectiveNativeChart false) z +
      (projectiveFSPotential z : EReal))
      (fun z => (projectiveToricEuclideanProfile u (tropicalization z) : EReal))
      (tropicalSmoothDomain 1) := by
  intro z hz
  calc
    _ = projectiveToricCorrectedDescent u (tropicalization z) :=
      (projectiveToricCorrectedDescent_tropicalPullback hi hz).symm
    _ = _ := (projectiveEuclideanProfile_coe hu hi _).symm

/-- One independent genuine homogeneous-section function has both boundary poles. -/
def projectiveBoundaryPole (p : P1) : EReal :=
  projectiveLogSingularity p + projectiveOppositeLogSingularity p

/-- The actual two section corrections retain their literal poles in both charts. -/
theorem projectiveBoundaryPole_corrected_chart (b : Bool) (z : ComplexModel 1) :
    projectiveBoundaryPole ((projectiveNativeChart b).val.symm z) +
      ((2 * projectiveFSPotential z : ℝ) : EReal) = logNormSq (z 0) := by
  have hρ : ((2 * projectiveFSPotential z : ℝ) : EReal) =
      (projectiveFSPotential z : EReal) + (projectiveFSPotential z : EReal) := by
    rw [← EReal.coe_add]
    congr 1
    ring
  change (projectiveLogSingularity ((projectiveModelChart b).symm z) +
    projectiveOppositeLogSingularity ((projectiveModelChart b).symm z)) + _ = _
  rw [hρ]
  calc
    _ = (projectiveLogSingularity ((projectiveModelChart b).symm z) +
        (projectiveFSPotential z : EReal)) +
      (projectiveOppositeLogSingularity ((projectiveModelChart b).symm z) +
        (projectiveFSPotential z : EReal)) := by ac_rfl
    _ = _ := by
      rw [projectiveLogSingularity_corrected_chart,
        projectiveOppositeLogSingularity_corrected_chart]
      cases b <;> simp

/-- Genuine native positive-sum nondegeneracy is consumed, with no new germ assembly. -/
theorem isGlobalQuasiPshPotential_projectiveBoundaryPole :
    IsGlobalQuasiPshPotential (n := 1) projectiveBoundaryPole := by
  have h0 := isThetaPshPotential_projectiveNativeFS_of_source
    isThetaPSH_projectiveLogSingularity
  have h1 := isThetaPshPotential_projectiveNativeFS_of_source
    isThetaPSH_projectiveOppositeLogSingularity
  exact (SGPT.Okounkov.isThetaPshPotential_add_from_positive_sum h0 h1).quasiPshPotential

/-- The generic actual patch has the SAME original two-boundary-point complement. -/
theorem projectiveTropicalPatch_source {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    ((tropicalPotentialPatch (projectiveNativeChart false) projectiveTropicalLocalPotential
      (projectiveToricEuclideanProfile_convex hu hi)
      (projectiveToricEuclideanProfile_corrected hu hi)).source : Set P1) =
        projectiveToricBoundaryᶜ := by
  change ((projectiveToricPuncturedPatch hu).source : Set P1) = _
  exact projectiveToricPuncturedPatch_source hu

/-- The produced actual complement lies in the independent genuine pole locus. -/
theorem projectiveTropicalPatch_compl_subset_boundaryPole {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    (((tropicalPotentialPatch (projectiveNativeChart false) projectiveTropicalLocalPotential
      (projectiveToricEuclideanProfile_convex hu hi)
      (projectiveToricEuclideanProfile_corrected hu hi)).source : Set P1)ᶜ) ⊆
        {p | projectiveBoundaryPole p = ⊥} := by
  rw [projectiveTropicalPatch_source hu hi, compl_compl]
  intro p hp
  change p = projectiveOrigin ∨ p = projectiveInfinity at hp
  rcases hp with hp | hp
  · subst p
    simp [projectiveBoundaryPole, projectiveLogSingularity_origin,
      projectiveOppositeLogSingularity_origin]
  · subst p
    simp [projectiveBoundaryPole, projectiveLogSingularity_infinity,
      projectiveOppositeLogSingularity_infinity]

/-- The actual original measure directly consumes the produced generic geometric data. -/
theorem projectiveToricNonPluripolarMeasure_eq_tropicalCanonical {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    projectiveToricNonPluripolarMeasure hu =
      (tropicalPotentialPatch (projectiveNativeChart false) projectiveTropicalLocalPotential
        (projectiveToricEuclideanProfile_convex hu hi)
        (projectiveToricEuclideanProfile_corrected hu hi)).pushMeasure
          (tropicalCanonicalBTMeasure (projectiveToricEuclideanProfile_convex hu hi)) := by
  exact globalMixedMeasure_eq_tropical_chart_pushMeasure
    (isThetaPshPotential_projectiveNativeFS_of_source hu)
    (projectiveNativeChart false) projectiveTropicalLocalPotential
    (projectiveToricEuclideanProfile_convex hu hi)
    (projectiveToricEuclideanProfile_corrected hu hi)
    isGlobalQuasiPshPotential_projectiveBoundaryPole
    (projectiveTropicalPatch_compl_subset_boundaryPole hu hi)

/-- The genuine generic total uses the SAME Euclidean pairing and lattice Haar volume. -/
theorem projectiveToricNonPluripolarMeasure_univ_eq_euclideanNewton {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    projectiveToricNonPluripolarMeasure hu univ = volume
      (convexNewtonBody (conjugate (innerₗ (EuclideanSpace ℝ (Fin 1)))
        (fun x => (projectiveToricEuclideanProfile u x : EReal)))) := by
  simpa only [projectiveToricNonPluripolarMeasure,
    SGPT.Foundations.Analysis.Pending.DiagonalMass.diagonalPotentialMeasure,
    Nat.factorial_one, Nat.cast_one, one_mul] using
    globalMixedMeasure_univ_eq_tropicalNewtonBody
      (isThetaPshPotential_projectiveNativeFS_of_source hu)
      (projectiveNativeChart false) projectiveTropicalLocalPotential
      (projectiveToricEuclideanProfile_convex hu hi)
      (projectiveToricEuclideanProfile_corrected hu hi)
      isGlobalQuasiPshPotential_projectiveBoundaryPole
      (projectiveTropicalPatch_compl_subset_boundaryPole hu hi)

end SGPT.Toric
