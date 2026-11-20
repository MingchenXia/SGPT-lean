import SGPT.Convex.BoundedLegendreVariation
import SGPT.Toric.ProjectiveToricSignedIntegral
import SGPT.Foundations.Analysis.Pending.BoundedMongeAmpereEnergy

set_option autoImplicit false

/-!
# Actual projective bounded Legendre variation

Original bounded invariant source potentials manufacture the convex bounded
growth inputs and all signed integrability. The genuine Alexandrov variation
inequality then transports to the actual global non-pluripolar measures.
This proves the bounded integrated tangent inequalities in SGPT `prop:Etoric`.
-/

noncomputable section

namespace SGPT.Toric

open Set Filter MeasureTheory SGPT.PSH SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.RelativePreceqClasses
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
open scoped Topology RealInnerProductSpace

local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)
local notation "E1" => EuclideanSpace ℝ (Fin 1)
local notation "B" => innerₗ E1

private theorem euclideanProfile_coe_eq {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    (fun x => (projectiveToricEuclideanProfile u x : EReal)) =
      projectiveToricCorrectedDescent u := by
  obtain ⟨g, _hg, he⟩ := exists_real_convex_projectiveToricCorrectedDescent hu hi
  funext x
  simp only [projectiveToricEuclideanProfile, he, EReal.toReal_coe]

private theorem boundedProfile_mem_boundedGrowthClass {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) (hb : IsBoundedPotential u) :
    (fun x => (projectiveToricEuclideanProfile u x : EReal)) ∈
      BoundedGrowthClass B projectiveMomentInterval := by
  rw [euclideanProfile_coe_eq hu hi]
  apply (projectiveToric_mem_relativeEInfinity_iff_boundedGrowthClass hu hi).mp
  have h0 : IsBoundedPotential (fun _ : P1 => (0 : EReal)) :=
    ⟨0, 0, fun _ => by simp⟩
  exact ⟨isThetaPshPotential_projectiveNativeFS_of_source hu,
    BoundedMongeAmpereEnergy.sameSingularityType_of_bounded hb h0⟩

/-- Actual bounded source potentials produce finite Legendre integrals on the
literal moment interval; integrability is not an extra certificate. -/
theorem projectiveToricLegendre_integrable_of_bounded {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) (hb : IsBoundedPotential u) :
    Integrable (fun m => (projectiveToricLegendre u m).toReal)
      (volume.restrict projectiveMomentInterval) := by
  have h := integrable_conjugateToReal_of_mem_boundedGrowthClass volume
    isCompact_projectiveMomentInterval nonempty_projectiveMomentInterval
    convex_projectiveMomentInterval
    (f := ⟨projectiveToricEuclideanProfile u, projectiveToricEuclideanProfile_convex hu hi⟩)
    (boundedProfile_mem_boundedGrowthClass hu hi hb)
  rw [euclideanProfile_coe_eq hu hi] at h
  exact h

private theorem bounded_toReal_integrable {u w : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hb : IsBoundedPotential u)
    (hw : projectiveLineAtlas.IsThetaPSH projectiveFSForm w) :
    Integrable (fun p => (u p).toReal) (projectiveToricNonPluripolarMeasure hw) := by
  let : IsFiniteMeasure (projectiveToricNonPluripolarMeasure hw) :=
    isFiniteMeasure_projectiveToricNonPluripolarMeasure hw
  obtain ⟨C, hC⟩ := GlobalSlotStokes.IsBoundedPotential.exists_abs_toReal_le hb
  exact GlobalSlotStokes.integrable_of_measurable_bounded
    (GlobalSlotStokes.ThetaPlurisubharmonic.measurable_toReal
      (isThetaPshPotential_projectiveNativeFS_of_source hu).1) hC _

private theorem bounded_gap_integral_eq_realMA {u v w : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hiu : ProjectiveCircleInvariant u) (hub : IsBoundedPotential u)
    (hv : projectiveLineAtlas.IsThetaPSH projectiveFSForm v)
    (hiv : ProjectiveCircleInvariant v) (hvb : IsBoundedPotential v)
    (hw : projectiveLineAtlas.IsThetaPSH projectiveFSForm w)
    (hiw : ProjectiveCircleInvariant w) :
    (∫ p, ((v p).toReal - (u p).toReal) ∂projectiveToricNonPluripolarMeasure hw) =
      ∫ x, (projectiveToricEuclideanProfile v x - projectiveToricEuclideanProfile u x)
        ∂alexandrovMeasure B volume (projectiveToricCorrectedDescent w) := by
  have iu := bounded_toReal_integrable hu hub hw
  have iv := bounded_toReal_integrable hv hvb hw
  have iu' := (projectiveToric_integrable_toReal_iff_realMA hu hiu hw hiw).mp iu
  have iv' := (projectiveToric_integrable_toReal_iff_realMA hv hiv hw hiw).mp iv
  rw [integral_sub iv iu,
    projectiveToricNonPluripolarMeasure_integral_toReal_eq_tropical hv hiv hw hiw iv,
    projectiveToricNonPluripolarMeasure_integral_toReal_eq_tropical hu hiu hw hiw iu,
    ← integral_sub iv' iu']
  apply integral_congr_ae
  exact Eventually.of_forall (fun _ => by ring)

/-- The original bounded projective inputs produce both genuine integrated
endpoint inequalities, with the literal rank-one normalization and actual NP
measures. This is the bounded variation step of the source energy formula. -/
theorem projectiveToricLegendre_variation_bounds {u v : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hiu : ProjectiveCircleInvariant u) (hub : IsBoundedPotential u)
    (hv : projectiveLineAtlas.IsThetaPSH projectiveFSForm v)
    (hiv : ProjectiveCircleInvariant v) (hvb : IsBoundedPotential v) :
    (∫ p, ((v p).toReal - (u p).toReal) ∂projectiveToricNonPluripolarMeasure hv) ≤
      (∫ m in projectiveMomentInterval,
        ((projectiveToricLegendre u m).toReal - (projectiveToricLegendre v m).toReal)) ∧
    (∫ m in projectiveMomentInterval,
        ((projectiveToricLegendre u m).toReal - (projectiveToricLegendre v m).toReal)) ≤
      ∫ p, ((v p).toReal - (u p).toReal) ∂projectiveToricNonPluripolarMeasure hu := by
  let f : RealConvexFunction E1 :=
    ⟨projectiveToricEuclideanProfile u, projectiveToricEuclideanProfile_convex hu hiu⟩
  let g : RealConvexFunction E1 :=
    ⟨projectiveToricEuclideanProfile v, projectiveToricEuclideanProfile_convex hv hiv⟩
  have h := integral_conjugate_variation_bounds volume
    isCompact_projectiveMomentInterval nonempty_projectiveMomentInterval
    convex_projectiveMomentInterval
    (f := f) (g := g)
    (boundedProfile_mem_boundedGrowthClass hu hiu hub)
    (boundedProfile_mem_boundedGrowthClass hv hiv hvb)
  dsimp only [f, g] at h
  rw [euclideanProfile_coe_eq hu hiu, euclideanProfile_coe_eq hv hiv] at h
  norm_num [projectiveToricLegendre] at h
  rw [bounded_gap_integral_eq_realMA hu hiu hub hv hiv hvb hv hiv,
    bounded_gap_integral_eq_realMA hu hiu hub hv hiv hvb hu hiu]
  exact h

end SGPT.Toric
