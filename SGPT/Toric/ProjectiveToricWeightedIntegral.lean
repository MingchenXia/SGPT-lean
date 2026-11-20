import SGPT.Toric.ProjectiveGlobalTropicalData
import SGPT.Toric.ProjectiveToricFullMassBounded
import SGPT.Foundations.Analysis.Pending.ActualSingularChartMassLiminf

set_option autoImplicit false

/-!
# Actual projective toric weighted integrals

The genuine original NP measure is transported through its punctured native
chart and the original tropical Alexandrov pushforward. The source finite-energy
integral is thereby the actual real Alexandrov integral of `|F_u - F_0|`.
No finite-energy or desired Legendre-integral identity is assumed.

This supplies a prerequisite for the projective-line specialization of SGPT
`prop:Etoric` and `cor:toric-ample:L1092`. The Legendre `L¹(P)` equivalence and
the original energy value formula remain separate obligations.
-/

noncomputable section

namespace SGPT.Toric

open Set Filter MeasureTheory SGPT.PSH SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.RelativePreceqClasses
open scoped Topology ENNReal RealInnerProductSpace

local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)
local notation "E1" => EuclideanSpace ℝ (Fin 1)
local notation "B" => innerₗ E1

/-- The literal original source values are finite on the torus, after removing
the genuine finite FS correction. Neither boundary value is changed. -/
theorem projectiveToricEuclideanProfile_uncorrected {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) {z : ComplexModel 1}
    (hz : z ∈ complexTorus 1) :
    u ((projectiveModelChart false).symm z) =
      ((projectiveToricEuclideanProfile u (tropicalization z) -
        projectiveLineLogPartition (tropicalization z 0) : ℝ) : EReal) := by
  have h := projectiveToricEuclideanProfile_corrected hu hi hz
  change u ((projectiveModelChart false).symm z) + (projectiveFSPotential z : EReal) =
    (projectiveToricEuclideanProfile u (tropicalization z) : EReal) at h
  have hρ : projectiveFSPotential z = projectiveLineLogPartition (tropicalization z 0) := by
    rw [projectiveFSPotential_eq, projectiveLineLogPartition_tropicalization (hz 0)]
  have heq := congrArg (fun a : EReal => a + ((-projectiveFSPotential z : ℝ) : EReal)) h
  rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero,
    ← EReal.coe_add, hρ] at heq
  simpa only [sub_eq_add_neg] using heq

/-- Transport of every nonnegative measurable tropical weight through the actual
global NP measure. Extended integrals and singular measure parts are retained. -/
theorem projectiveToricNonPluripolarMeasure_lintegral_eq_tropical {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) (a : P1 → ℝ≥0∞) {q : E1 → ℝ≥0∞}
    (hq : Measurable q)
    (heq : ∀ z ∈ complexTorus 1,
      a ((projectiveModelChart false).symm z) = q (tropicalization z)) :
    (∫⁻ p, a p ∂projectiveToricNonPluripolarMeasure hu) =
      ∫⁻ x, q x ∂alexandrovMeasure B volume (projectiveToricCorrectedDescent u) := by
  let P := projectiveToricPuncturedPatch hu
  let ν := scalarCanonicalBTMeasure (projectiveToricScalarProfile_convex hu hi)
  have hs : ν (P.domain : Set (ComplexModel 1))ᶜ = 0 :=
    canonicalMixedBedfordTaylorMeasure_compl _ _ _
  have hwhole : projectiveToricNonPluripolarMeasure hu = P.pushMeasure ν := by
    have hae : ∀ᵐ p ∂projectiveToricNonPluripolarMeasure hu,
        p ∈ projectiveToricBoundaryᶜ := by
      apply ae_iff.mpr
      simpa only [mem_compl_iff, not_not, ofPred_mem_eq] using
        projectiveToricNonPluripolarMeasure_boundary hu
    exact (Measure.restrict_eq_self_of_ae_mem hae).symm.trans
      (projectiveToricNonPluripolarMeasure_restrict_punctured hu hi)
  obtain ⟨hT, _⟩ := exists_compact_tropical_torus_lift (n := 1) isCompact_empty
  calc
    _ = ∫⁻ z, a ((projectiveModelChart false).symm z) ∂ν := by
      rw [hwhole]
      exact ActualSingularChartMassLiminf.lintegral_pushMeasure P hs a
    _ = ∫⁻ z, q (tropicalization z) ∂ν := by
      apply lintegral_congr_ae
      have hae : ∀ᵐ z ∂ν, z ∈ P.domain := ae_iff.mpr hs
      filter_upwards [hae] with z hz
      exact heq z hz
    _ = ∫⁻ x, q x ∂Measure.map tropicalization ν := (lintegral_map hq hT).symm
    _ = _ := by rw [projectiveToricCanonicalBT_tropicalPushforward hu hi]

/-- The genuine original native finite-energy integral, relative to the zero
model potential, equals the actual real MA integral of the original profile gap. -/
theorem projectiveToric_relativeFiniteEnergyIntegral_eq_realMA {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    relativeFiniteEnergyIntegral projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) u
      (isThetaPshPotential_projectiveNativeFS_of_source hu) =
        ∫⁻ x, ENNReal.ofReal |projectiveToricEuclideanProfile u x -
          projectiveLineLogPartition (x 0)|
          ∂alexandrovMeasure B volume (projectiveToricCorrectedDescent u) := by
  let q : E1 → ℝ≥0∞ := fun x => ENNReal.ofReal |projectiveToricEuclideanProfile u x -
    projectiveLineLogPartition (x 0)|
  have hf : Continuous (projectiveToricEuclideanProfile u) :=
    continuousOn_univ.mp ((projectiveToricEuclideanProfile_convex hu hi).continuousOn isOpen_univ)
  have h0 : Continuous (fun x : E1 => projectiveLineLogPartition (x 0)) := by
    unfold projectiveLineLogPartition
    exact (show Continuous (fun x : E1 => 1 + Real.exp (x 0)) by fun_prop).log
      (fun x => ne_of_gt (by positivity))
  have hq : Measurable q := ENNReal.measurable_ofReal.comp ((hf.sub h0).abs.measurable)
  change (∫⁻ p, canonicalERealAbsDiff 0 (u p) ∂projectiveToricNonPluripolarMeasure hu) = _
  apply projectiveToricNonPluripolarMeasure_lintegral_eq_tropical hu hi _ hq
  intro z hz
  rw [projectiveToricEuclideanProfile_uncorrected hu hi hz]
  change canonicalERealAbsDiff ((0 : ℝ) : EReal) _ = _
  rw [canonicalERealAbsDiff_coe_coe, zero_sub, abs_neg]

/-- Actual unnormalized native E¹ is full Newton interval plus finiteness of
the produced real MA integral. No Legendre L¹ equivalence is asserted here. -/
theorem projectiveToric_mem_relativeFiniteEnergyPreceq_iff_realMA {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    RelativeFiniteEnergyPreceq projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) u isModelPotential_projectiveNativeZero ↔
        projectiveToricNewtonBody u = projectiveMomentInterval ∧
          (∫⁻ x, ENNReal.ofReal |projectiveToricEuclideanProfile u x -
            projectiveLineLogPartition (x 0)|
            ∂alexandrovMeasure B volume (projectiveToricCorrectedDescent u)) < ⊤ := by
  have hnative := isThetaPshPotential_projectiveNativeFS_of_source hu
  have hint := projectiveToric_relativeFiniteEnergyIntegral_eq_realMA hu hi
  constructor
  · rintro ⟨hmass, hv, hfin⟩
    refine ⟨(projectiveToric_mem_relativeFullMassPreceq_iff_newtonBody_eq_interval hu hi).mp
      hmass, ?_⟩
    rw [← hint]
    exact (relativeFiniteEnergyIntegral_proof_independent
      projectiveNativeFSBackground.form (fun _ : P1 => (0 : EReal)) u hv hnative) ▸ hfin
  · rintro ⟨hbody, hfin⟩
    refine ⟨(projectiveToric_mem_relativeFullMassPreceq_iff_newtonBody_eq_interval hu hi).mpr
      hbody, hnative, ?_⟩
    rwa [hint]

end SGPT.Toric
