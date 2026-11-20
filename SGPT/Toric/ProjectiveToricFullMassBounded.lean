import SGPT.Toric.ProjectiveToricNonPluripolarMass
import SGPT.Toric.TropicalFullMassCriterion
import SGPT.Foundations.Analysis.Pending.RelativePreceqClasses

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set MeasureTheory SGPT.PSH SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.RelativePreceqClasses
open scoped Topology RealInnerProductSpace

local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)
local notation "E1" => EuclideanSpace ℝ (Fin 1)
local notation "B" => innerₗ E1

/-- Actual native zero has all three model fields, including its genuine positive mass. -/
theorem isModelPotential_projectiveNativeZero :
    IsModelPotential projectiveNativeFSBackground.form (fun _ : P1 => (0 : EReal)) := by
  have h0 := isThetaPshPotential_projectiveNativeFS_of_source isThetaPSH_projectiveZero
  have hm : diagonalPotentialMass projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) h0 = 1 := by
    simpa only [diagonalPotentialMass, projectiveToricNonPluripolarMeasure] using
      projectiveToricNonPluripolarMeasure_zero_univ
  refine ⟨h0, ?_, ?_⟩
  · exact le_antisymm (self_le_singularityEnvelope h0 le_rfl)
      (singularityEnvelope_le_zero _ _)
  · rw [hm]
    exact zero_lt_one

/-- The actual NP total is the original Euclidean Alexandrov total, without new analysis. -/
theorem projectiveToricNonPluripolarMeasure_univ_eq_alexandrov {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    projectiveToricNonPluripolarMeasure hu univ =
      alexandrovMeasure B volume (projectiveToricCorrectedDescent u) univ := by
  have hf := projectiveToricCorrectedDescent_mem_growthClass hu hi
  have hlsc := lowerSemicontinuous_of_isClosedConvex
    (isClosedConvex_of_mem_growthClass _ isCompact_projectiveMomentInterval
      nonempty_projectiveMomentInterval hf)
  rw [projectiveToricNonPluripolarMeasure_univ_eq_newtonLength hu hi,
    alexandrovMeasure_univ_eq_closure_rawSubgradientImage _ hf.1 hlsc,
    ← projectiveToricNewtonBody_eq_closure_rawSubgradientImage hu hi]
  simp

/-- Original source PSH manufactures the finite comparison; no normalization is assumed. -/
theorem projectiveToric_mem_relativeFullMassPreceq_iff {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    RelativeFullMassPreceq projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) u isModelPotential_projectiveNativeZero ↔
        projectiveToricCorrectedDescent u ∈ FullMassClass B projectiveMomentInterval := by
  have hnative := isThetaPshPotential_projectiveNativeFS_of_source hu
  have hupper : MoreSingularOn u (fun _ : P1 => (0 : EReal)) univ := by
    obtain ⟨C, hC⟩ := exists_upper_bound_projectiveThetaPSH hu
    exact (singularityLE_iff_exists_real _ _).mpr ⟨C, by simpa using hC⟩
  have hm : diagonalPotentialMass projectiveNativeFSBackground.form u hnative =
      alexandrovMeasure B volume (projectiveToricCorrectedDescent u) univ :=
    projectiveToricNonPluripolarMeasure_univ_eq_alexandrov hu hi
  have hzero : diagonalPotentialMass projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) isModelPotential_projectiveNativeZero.plurisubharmonic =
        volume projectiveMomentInterval := by
    have hi0 : ProjectiveCircleInvariant (fun _ : P1 => (0 : EReal)) := fun _ _ _ => rfl
    simpa only [projectiveToricNewtonBody_zero, projectiveToricNonPluripolarMeasure,
      diagonalPotentialMass] using
      projectiveToricNonPluripolarMeasure_univ_eq_newtonLength isThetaPSH_projectiveZero hi0
  have hc : projectiveToricCorrectedDescent u ∈ FullMassClass B projectiveMomentInterval ↔
      alexandrovMeasure B volume (projectiveToricCorrectedDescent u) univ =
        volume projectiveMomentInterval := by
    simpa using mem_fullMassClass_iff_alexandrovMeasure_univ_eq_euclidean B
      isCompact_projectiveMomentInterval nonempty_projectiveMomentInterval
      convex_projectiveMomentInterval (projectiveToricCorrectedDescent_mem_growthClass hu hi)
  constructor
  · rintro ⟨hw, _horder, hmass⟩
    apply hc.mpr
    change diagonalPotentialMass projectiveNativeFSBackground.form u hnative =
      diagonalPotentialMass projectiveNativeFSBackground.form
        (fun _ : P1 => (0 : EReal)) isModelPotential_projectiveNativeZero.plurisubharmonic
      at hmass
    rwa [hm, hzero] at hmass
  · intro hfull
    refine ⟨hnative, hupper, ?_⟩
    rw [hm, hzero]
    exact hc.mp hfull

private theorem projectiveMomentInterval_interior_nonempty :
    (interior projectiveMomentInterval).Nonempty := by
  let m : E1 := WithLp.toLp 2 (fun _ => (1 / 2 : ℝ))
  have heval : Continuous (fun x : E1 => x 0) := by fun_prop
  have hU : IsOpen {x : E1 | 0 < x 0 ∧ x 0 < 1} :=
    (isOpen_lt continuous_const heval).inter (isOpen_lt heval continuous_const)
  refine ⟨m, mem_interior_iff_mem_nhds.mpr ?_⟩
  apply Filter.mem_of_superset (hU.mem_nhds (by norm_num [m]))
  intro x hx
  exact ⟨hx.1.le, hx.2.le⟩

/-- The whole multivalued-subgradient Newton body retains the original full-mass meaning. -/
theorem projectiveToric_mem_fullMassClass_iff_newtonBody_eq_interval {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    projectiveToricCorrectedDescent u ∈ FullMassClass B projectiveMomentInterval ↔
      projectiveToricNewtonBody u = projectiveMomentInterval := by
  have hne : interior projectiveMomentInterval ≠ ∅ :=
    projectiveMomentInterval_interior_nonempty.ne_empty
  constructor
  · rintro ⟨_hg, h | h⟩
    · exact (hne h).elim
    · rwa [← projectiveToricNewtonBody_eq_closure_rawSubgradientImage hu hi] at h
  · intro h
    refine ⟨projectiveToricCorrectedDescent_mem_growthClass hu hi, Or.inr ?_⟩
    rwa [← projectiveToricNewtonBody_eq_closure_rawSubgradientImage hu hi]

/-- Unnormalized native full mass is exactly the actual closed Legendre-domain interval. -/
theorem projectiveToric_mem_relativeFullMassPreceq_iff_newtonBody_eq_interval
    {u : P1 → EReal} (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    RelativeFullMassPreceq projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) u isModelPotential_projectiveNativeZero ↔
        projectiveToricNewtonBody u = projectiveMomentInterval :=
  (projectiveToric_mem_relativeFullMassPreceq_iff hu hi).trans
    (projectiveToric_mem_fullMassClass_iff_newtonBody_eq_interval hu hi)

/-- Both whole reference-support comparisons use the already proved finite constants. -/
theorem projectiveToricCorrectedDescent_zero_singularityEquiv_support :
    SingularityEquiv (projectiveToricCorrectedDescent (fun _ : P1 => (0 : EReal)))
      (support (innerₗ E1).flip projectiveMomentInterval) := by
  constructor
  · apply (singularityLE_iff_exists_real _ _).mpr
    refine ⟨Real.log 2, fun x => ?_⟩
    rw [projectiveToricCorrectedDescent, projectiveToricDescent,
      zero_add, support_projectiveMomentInterval, ← EReal.coe_add]
    exact EReal.coe_le_coe_iff.mpr (projectiveLineLogPartition_le_max (x 0))
  · apply (singularityLE_iff_exists_real _ _).mpr
    refine ⟨0, fun x => ?_⟩
    rw [projectiveToricCorrectedDescent, projectiveToricDescent,
      zero_add, support_projectiveMomentInterval, EReal.coe_zero, add_zero]
    exact EReal.coe_le_coe_iff.mpr (max_le_projectiveLineLogPartition (x 0))

/-- Bounded native singularity type equals the actual closed bounded-growth class. -/
theorem projectiveToric_mem_relativeEInfinity_iff_boundedGrowthClass {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    RelativeEInfinity projectiveNativeFSBackground.form (fun _ : P1 => (0 : EReal)) u ↔
      projectiveToricCorrectedDescent u ∈ BoundedGrowthClass B projectiveMomentInterval := by
  have hi0 : ProjectiveCircleInvariant (fun _ : P1 => (0 : EReal)) := fun _ _ _ => rfl
  have hforward := projectiveToricCorrectedDescent_singularityLE_iff
    hu isThetaPSH_projectiveZero hi hi0
  have hbackward := projectiveToricCorrectedDescent_singularityLE_iff
    isThetaPSH_projectiveZero hu hi0 hi
  have hclosed := isClosedConvex_of_mem_growthClass B isCompact_projectiveMomentInterval
    nonempty_projectiveMomentInterval (projectiveToricCorrectedDescent_mem_growthClass hu hi)
  constructor
  · rintro ⟨_hnative, htype⟩
    refine ⟨hclosed, ?_⟩
    exact singularityEquiv_trans ⟨hforward.mp htype.1, hbackward.mp htype.2⟩
      projectiveToricCorrectedDescent_zero_singularityEquiv_support
  · rintro ⟨_hclosed, htype⟩
    have hzero := singularityEquiv_trans htype
      (singularityEquiv_symm projectiveToricCorrectedDescent_zero_singularityEquiv_support)
    exact ⟨isThetaPshPotential_projectiveNativeFS_of_source hu,
      hforward.mpr hzero.1, hbackward.mpr hzero.2⟩

/-- The same actual bounded native class is the printed whole extended Legendre type. -/
theorem projectiveToric_mem_relativeEInfinity_iff_legendre_singularityEquiv
    {u : P1 → EReal} (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    RelativeEInfinity projectiveNativeFSBackground.form (fun _ : P1 => (0 : EReal)) u ↔
      SingularityEquiv (projectiveToricLegendre u)
        (projectiveToricLegendre (fun _ : P1 => (0 : EReal))) := by
  have hi0 : ProjectiveCircleInvariant (fun _ : P1 => (0 : EReal)) := fun _ _ _ => rfl
  have hforward := projectiveThetaPSH_singularityLE_iff_legendre
    hu isThetaPSH_projectiveZero hi hi0
  have hbackward := projectiveThetaPSH_singularityLE_iff_legendre
    isThetaPSH_projectiveZero hu hi0 hi
  constructor
  · rintro ⟨_hnative, htype⟩
    exact ⟨hbackward.mp htype.2, hforward.mp htype.1⟩
  · intro htype
    exact ⟨isThetaPshPotential_projectiveNativeFS_of_source hu,
      hforward.mpr htype.2, hbackward.mpr htype.1⟩

end SGPT.Toric
