import SGPT.Convex.RankOneLegendreEnergy
import SGPT.Toric.ProjectiveToricLegendreVariation

set_option autoImplicit false

/-!
# The actual bounded projective toric energy identity

The literal rank-one Legendre energy integral identifies the actual native
finite-type energy, using its original two mixed endpoint measures. Bounded
original source inputs manufacture all integrability and exclude poles.
The arbitrary singular energy and the extended L1 criterion are not asserted.
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
open SGPT.Foundations.Analysis.Pending.RelativeEnergy
open scoped Topology RealInnerProductSpace

local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)
local notation "E1" => EuclideanSpace ℝ (Fin 1)
local notation "B" => innerₗ E1

private theorem profile_coe_eq {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    (fun x => (projectiveToricEuclideanProfile u x : EReal)) =
      projectiveToricCorrectedDescent u := by
  obtain ⟨g, _hg, he⟩ := exists_real_convex_projectiveToricCorrectedDescent hu hi
  funext x
  simp only [projectiveToricEuclideanProfile, he, EReal.toReal_coe]

private theorem profile_boundedGrowthClass {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) (hb : IsBoundedPotential u) :
    (fun x => (projectiveToricEuclideanProfile u x : EReal)) ∈
      BoundedGrowthClass B projectiveMomentInterval := by
  rw [profile_coe_eq hu hi]
  apply (projectiveToric_mem_relativeEInfinity_iff_boundedGrowthClass hu hi).mp
  have h0 : IsBoundedPotential (fun _ : P1 => (0 : EReal)) :=
    ⟨0, 0, fun _ => by simp⟩
  exact ⟨isThetaPshPotential_projectiveNativeFS_of_source hu,
    BoundedMongeAmpereEnergy.sameSingularityType_of_bounded hb h0⟩

private theorem bounded_integrable {u w : P1 → EReal}
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

private theorem bounded_gap_transport {φ u w : P1 → EReal}
    (hφ : projectiveLineAtlas.IsThetaPSH projectiveFSForm φ)
    (hiφ : ProjectiveCircleInvariant φ) (hφb : IsBoundedPotential φ)
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hiu : ProjectiveCircleInvariant u) (hub : IsBoundedPotential u)
    (hw : projectiveLineAtlas.IsThetaPSH projectiveFSForm w)
    (hiw : ProjectiveCircleInvariant w) :
    (∫ p, ((u p).toReal - (φ p).toReal) ∂projectiveToricNonPluripolarMeasure hw) =
      ∫ x, (projectiveToricEuclideanProfile u x - projectiveToricEuclideanProfile φ x)
        ∂alexandrovMeasure B volume (projectiveToricCorrectedDescent w) := by
  have iφ := bounded_integrable hφ hφb hw
  have iu := bounded_integrable hu hub hw
  have iφ' := (projectiveToric_integrable_toReal_iff_realMA hφ hiφ hw hiw).mp iφ
  have iu' := (projectiveToric_integrable_toReal_iff_realMA hu hiu hw hiw).mp iu
  rw [integral_sub iu iφ,
    projectiveToricNonPluripolarMeasure_integral_toReal_eq_tropical hu hiu hw hiw iu,
    projectiveToricNonPluripolarMeasure_integral_toReal_eq_tropical hφ hiφ hw hiw iφ,
    ← integral_sub iu' iφ']
  apply integral_congr_ae
  exact Eventually.of_forall (fun _ => by ring)

/-- The actual native finite-type energy equals the original Euclidean Legendre
gap integral for bounded invariant source inputs. Its original mixed endpoint
sum is expanded, rather than supplied through an energy identity premise. -/
theorem projectiveToric_relativeEnergyOfMinimalType_eq_legendre {φ u : P1 → EReal}
    (hφ : projectiveLineAtlas.IsThetaPSH projectiveFSForm φ)
    (hiφ : ProjectiveCircleInvariant φ) (hφb : IsBoundedPotential φ)
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hiu : ProjectiveCircleInvariant u) (hub : IsBoundedPotential u) :
    relativeEnergyOfMinimalType projectiveNativeFSBackground.form φ u
      (isThetaPshPotential_projectiveNativeFS_of_source hφ)
      (isThetaPshPotential_projectiveNativeFS_of_source hu) =
        ∫ m in projectiveMomentInterval,
          ((projectiveToricLegendre φ m).toReal - (projectiveToricLegendre u m).toReal) := by
  let f : RealConvexFunction E1 :=
    ⟨projectiveToricEuclideanProfile φ, projectiveToricEuclideanProfile_convex hφ hiφ⟩
  let g : RealConvexFunction E1 :=
    ⟨projectiveToricEuclideanProfile u, projectiveToricEuclideanProfile_convex hu hiu⟩
  have he := integral_conjugate_difference_eq_rankOneEnergy volume
    (EuclideanSpace.basisFun (Fin 1) ℝ)
    isCompact_projectiveMomentInterval nonempty_projectiveMomentInterval
    convex_projectiveMomentInterval (f := f) (g := g)
    (profile_boundedGrowthClass hφ hiφ hφb) (profile_boundedGrowthClass hu hiu hub)
  dsimp only [f, g] at he
  rw [profile_coe_eq hφ hiφ, profile_coe_eq hu hiu] at he
  have hcanonical : (fun p => canonicalERealDiffToReal (u p) (φ p)) =
      (fun p => (u p).toReal - (φ p).toReal) := by
    funext p
    simp only [canonicalERealDiffToReal, poleModifiedERealDiffToReal, hub.ne_bot p,
      false_and, if_false]
    exact EReal.toReal_sub (hub.ne_top p) (hub.ne_bot p) (hφb.ne_top p) (hφb.ne_bot p)
  have hm0 : endpointMixedMeasure projectiveNativeFSBackground.form φ u
      (isThetaPshPotential_projectiveNativeFS_of_source hφ)
      (isThetaPshPotential_projectiveNativeFS_of_source hu) (0 : Fin 2) =
      projectiveToricNonPluripolarMeasure hφ := by
    unfold endpointMixedMeasure projectiveToricNonPluripolarMeasure
      DiagonalMass.diagonalPotentialMeasure
    congr 1
  have hm1 : endpointMixedMeasure projectiveNativeFSBackground.form φ u
      (isThetaPshPotential_projectiveNativeFS_of_source hφ)
      (isThetaPshPotential_projectiveNativeFS_of_source hu) (1 : Fin 2) =
      projectiveToricNonPluripolarMeasure hu := by
    unfold endpointMixedMeasure projectiveToricNonPluripolarMeasure
      DiagonalMass.diagonalPotentialMeasure
    congr 1
    funext i
    fin_cases i
    rfl
  rw [relativeEnergyOfMinimalType, Fin.sum_univ_two]
  simp only [relativeEnergyTerm, hm0, hm1, hcanonical]
  rw [bounded_gap_transport hφ hiφ hφb hu hiu hub hφ hiφ,
    bounded_gap_transport hφ hiφ hφb hu hiu hub hu hiu]
  convert he.symm using 1 <;> norm_num [projectiveToricLegendre]

/-- The printed bounded source identity relative to the actual native zero
potential; arbitrary singular and extended energy remain separate obligations. -/
theorem projectiveToric_relativeEnergyOfMinimalType_zero_eq_legendre {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hiu : ProjectiveCircleInvariant u) (hub : IsBoundedPotential u) :
    relativeEnergyOfMinimalType projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) u
      (isThetaPshPotential_projectiveNativeFS_of_source isThetaPSH_projectiveZero)
      (isThetaPshPotential_projectiveNativeFS_of_source hu) =
        ∫ m in projectiveMomentInterval,
          ((projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m).toReal -
            (projectiveToricLegendre u m).toReal) := by
  exact projectiveToric_relativeEnergyOfMinimalType_eq_legendre
    isThetaPSH_projectiveZero (fun _ _ _ => rfl) ⟨0, 0, fun _ => by simp⟩ hu hiu hub

end SGPT.Toric
