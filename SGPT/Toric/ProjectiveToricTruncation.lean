import SGPT.Convex.ConjugateTruncationLimit
import SGPT.Toric.ProjectiveToricEnergyIdentity
import SGPT.PSH.AtlasQPSHAddition

set_option autoImplicit false

/-!
# Actual projective toric lower truncations

Original universal source theta-PSH, circle invariance and normalization
manufacture the genuine bounded projective lower truncations. Their literal
corrected profiles produce the actual conjugate order limit and extended-gap
monotone convergence, retaining positive infinity.
-/

noncomputable section

namespace SGPT.Toric

open Set Filter MeasureTheory SGPT.PSH SGPT.Convex
open SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
open scoped Topology ENNReal RealInnerProductSpace

local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)
local notation "E1" => EuclideanSpace ℝ (Fin 1)
local notation "B" => innerₗ E1

/-- The literal original projective lower truncation, retaining all boundary
values of the original input before taking its actual finite maximum. -/
def projectiveToricTruncation (u : P1 → EReal) (j : ℕ) (p : P1) : EReal :=
  max (u p) ((-(j : ℝ) : ℝ) : EReal)

/-- Original universal FS tests genuinely qualify the actual lower truncation. -/
theorem isThetaPSH_projectiveToricTruncation {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u) (j : ℕ) :
    projectiveLineAtlas.IsThetaPSH projectiveFSForm (projectiveToricTruncation u j) := by
  have hc : projectiveLineAtlas.IsThetaPSH projectiveFSForm
      (fun _ : P1 => ((-(j : ℝ) : ℝ) : EReal)) := by
    simpa only [zero_add] using isThetaPSH_projectiveZero.add_const (-(j : ℝ))
  exact hu.max hc

/-- The actual compact circle action preserves the literal lower truncation. -/
theorem ProjectiveCircleInvariant.truncation {u : P1 → EReal}
    (hi : ProjectiveCircleInvariant u) (j : ℕ) :
    ProjectiveCircleInvariant (projectiveToricTruncation u j) := by
  intro a ha p
  simp only [projectiveToricTruncation, hi a ha p]

/-- Original source normalization manufactures both whole-space finite bounds. -/
theorem isBoundedPotential_projectiveToricTruncation {u : P1 → EReal}
    (hle : u ≤ fun _ => (0 : EReal)) (j : ℕ) :
    IsBoundedPotential (projectiveToricTruncation u j) := by
  refine ⟨-(j : ℝ), 0, fun p => ⟨le_max_right _ _, ?_⟩⟩
  apply max_le (hle p)
  exact EReal.coe_le_coe_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg j))

/-- The actual finite FS correction commutes with the original lower maximum,
including at any infinite original boundary input. -/
theorem projectiveToricCorrectedDescent_truncation (u : P1 → EReal) (j : ℕ) :
    projectiveToricCorrectedDescent (projectiveToricTruncation u j) = fun x =>
      max (projectiveToricCorrectedDescent u x)
        (projectiveToricCorrectedDescent (fun _ : P1 => (0 : EReal)) x -
          ((j : ℝ) : EReal)) := by
  funext x
  simp only [projectiveToricCorrectedDescent, projectiveToricDescent,
    projectiveToricTruncation, zero_add]
  let p := OnePoint.equivProjectivization ℂ (expCoordinates x 0)
  let r := projectiveLineLogPartition (x 0)
  have he : ((-(j : ℝ) : ℝ) : EReal) + (r : EReal) =
      (r : EReal) - ((j : ℝ) : EReal) := by
    rw [← EReal.coe_add, ← EReal.coe_sub]
    congr 1
    ring
  change max (u p) ((-(j : ℝ) : ℝ) : EReal) + (r : EReal) =
    max (u p + (r : EReal)) ((r : EReal) - ((j : ℝ) : EReal))
  by_cases h : u p ≤ ((-(j : ℝ) : ℝ) : EReal)
  · rw [max_eq_right h, max_eq_right (by
      rw [← he]
      exact add_le_add h le_rfl)]
    exact he
  · have h' := le_of_not_ge h
    rw [max_eq_left h', max_eq_left (by
      rw [← he]
      exact add_le_add h' le_rfl)]

private theorem profile_coe_eq {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    (fun x => (projectiveToricEuclideanProfile u x : EReal)) =
      projectiveToricCorrectedDescent u := by
  obtain ⟨g, _hg, he⟩ := exists_real_convex_projectiveToricCorrectedDescent hu hi
  funext x
  simp only [projectiveToricEuclideanProfile, he, EReal.toReal_coe]

/-- Actual source finiteness makes the genuine real profile the literal finite
reference-floor truncation; no chart or convergence certificate is assumed. -/
theorem projectiveToricEuclideanProfile_truncation {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) (j : ℕ) :
    projectiveToricEuclideanProfile (projectiveToricTruncation u j) =
      realLowerTruncation (projectiveToricEuclideanProfile u)
        (projectiveToricEuclideanProfile (fun _ : P1 => (0 : EReal))) j := by
  have hi0 : ProjectiveCircleInvariant (fun _ : P1 => (0 : EReal)) := fun _ _ _ => rfl
  funext x
  unfold projectiveToricEuclideanProfile
  rw [projectiveToricCorrectedDescent_truncation]
  dsimp only
  rw [← congrFun (profile_coe_eq hu hi) x,
    ← congrFun (profile_coe_eq isThetaPSH_projectiveZero hi0) x, ← EReal.coe_sub]
  change (max (projectiveToricEuclideanProfile u x : EReal)
      ((projectiveToricEuclideanProfile (fun _ : P1 => (0 : EReal)) x - j : ℝ) : EReal)).toReal =
    max (projectiveToricEuclideanProfile u x)
      (projectiveToricEuclideanProfile (fun _ : P1 => (0 : EReal)) x - j)
  by_cases h : projectiveToricEuclideanProfile u x ≤
      projectiveToricEuclideanProfile (fun _ : P1 => (0 : EReal)) x - j
  · rw [max_eq_right (EReal.coe_le_coe_iff.mpr h), EReal.toReal_coe, max_eq_right h]
  · have h' := le_of_not_ge h
    rw [max_eq_left (EReal.coe_le_coe_iff.mpr h'), EReal.toReal_coe, max_eq_left h']

/-- The literal source lower floors give monotonicity of the actual extended
Legendre transforms, without discarding an infinite value. -/
theorem projectiveToricLegendre_truncation_mono (u : P1 → EReal) :
    Monotone (fun j : ℕ => projectiveToricLegendre (projectiveToricTruncation u j)) := by
  intro i j hij
  apply conjugate_antitone B
  intro x
  rw [projectiveToricCorrectedDescent_truncation,
    projectiveToricCorrectedDescent_truncation]
  apply max_le_max le_rfl
  simp only [sub_eq_add_neg]
  exact add_le_add le_rfl (EReal.neg_le_neg_iff.mpr
    (EReal.coe_le_coe_iff.mpr (Nat.cast_le.mpr hij)))

/-- The original source input produces the genuine whole extended conjugate
supremum of its actual lower truncations; top values are retained. -/
theorem projectiveToricLegendre_eq_iSup_truncation {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    projectiveToricLegendre u = fun m =>
      ⨆ j : ℕ, projectiveToricLegendre (projectiveToricTruncation u j) m := by
  have h := conjugate_eq_iSup_realLowerTruncation
    (projectiveToricEuclideanProfile u)
    (projectiveToricEuclideanProfile (fun _ : P1 => (0 : EReal)))
  rw [profile_coe_eq hu hi] at h
  have he (j : ℕ) :
      (fun x => (realLowerTruncation (projectiveToricEuclideanProfile u)
        (projectiveToricEuclideanProfile (fun _ : P1 => (0 : EReal))) j x : EReal)) =
      projectiveToricCorrectedDescent (projectiveToricTruncation u j) := by
    rw [← projectiveToricEuclideanProfile_truncation hu hi j]
    exact profile_coe_eq (isThetaPSH_projectiveToricTruncation hu j) (hi.truncation j)
  simp_rw [he] at h
  exact h

/-- Actual original source inputs produce extended nonnegative conjugate-gap
monotone convergence on the literal Euclidean interval, including top values. -/
theorem projectiveToricLegendre_gap_lintegral_eq_iSup_truncation {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    (∫⁻ m in projectiveMomentInterval,
      (projectiveToricLegendre u m -
        projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m).toENNReal) =
      ⨆ j : ℕ, ∫⁻ m in projectiveMomentInterval,
        (projectiveToricLegendre (projectiveToricTruncation u j) m -
          projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m).toENNReal := by
  have hi0 : ProjectiveCircleInvariant (fun _ : P1 => (0 : EReal)) := fun _ _ _ => rfl
  have hb0 : IsBoundedPotential (fun _ : P1 => (0 : EReal)) :=
    ⟨0, 0, fun _ => by simp⟩
  have hg : (fun x => (projectiveToricEuclideanProfile
      (fun _ : P1 => (0 : EReal)) x : EReal)) ∈ BoundedGrowthClass B projectiveMomentInterval := by
    rw [profile_coe_eq isThetaPSH_projectiveZero hi0]
    exact (projectiveToric_mem_relativeEInfinity_iff_boundedGrowthClass
      isThetaPSH_projectiveZero hi0).mp
      ⟨isThetaPshPotential_projectiveNativeFS_of_source isThetaPSH_projectiveZero,
        BoundedMongeAmpereEnergy.sameSingularityType_of_bounded hb0 hb0⟩
  have h := lintegral_conjugate_gap_eq_iSup_realLowerTruncation volume
    isCompact_projectiveMomentInterval nonempty_projectiveMomentInterval
    convex_projectiveMomentInterval (projectiveToricEuclideanProfile u)
    (projectiveToricEuclideanProfile (fun _ : P1 => (0 : EReal))) hg
  rw [profile_coe_eq hu hi, profile_coe_eq isThetaPSH_projectiveZero hi0] at h
  have he (j : ℕ) :
      (fun x => (realLowerTruncation (projectiveToricEuclideanProfile u)
        (projectiveToricEuclideanProfile (fun _ : P1 => (0 : EReal))) j x : EReal)) =
      projectiveToricCorrectedDescent (projectiveToricTruncation u j) := by
    rw [← projectiveToricEuclideanProfile_truncation hu hi j]
    exact profile_coe_eq (isThetaPSH_projectiveToricTruncation hu j) (hi.truncation j)
  simp_rw [he] at h
  exact h

end SGPT.Toric
