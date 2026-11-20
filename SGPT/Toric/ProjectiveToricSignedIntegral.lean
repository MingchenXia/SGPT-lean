import SGPT.Toric.ProjectiveToricWeightedIntegral

set_option autoImplicit false

/-!
# Independent projective toric signed integrals

Two independent original invariant source potentials give an exact
integrability equivalence and signed integral transport through the actual NP
and Euclidean Alexandrov measures. This is the genuine measure bridge used by
the original affine-energy derivative, not an assumed energy identity.
-/

noncomputable section

namespace SGPT.Toric

open Set Filter MeasureTheory SGPT.PSH SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open scoped Topology ENNReal RealInnerProductSpace

local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)
local notation "E1" => EuclideanSpace ℝ (Fin 1)
local notation "B" => innerₗ E1

/-- Actual integrability transports with independent weight and measure inputs.
No normalization, full mass or finite-energy assumption is inserted. -/
theorem projectiveToric_integrable_toReal_iff_realMA {u v : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hiu : ProjectiveCircleInvariant u)
    (hv : projectiveLineAtlas.IsThetaPSH projectiveFSForm v)
    (hiv : ProjectiveCircleInvariant v) :
    Integrable (fun p => (u p).toReal) (projectiveToricNonPluripolarMeasure hv) ↔
      Integrable (fun x => projectiveToricEuclideanProfile u x -
        projectiveLineLogPartition (x 0))
        (alexandrovMeasure B volume (projectiveToricCorrectedDescent v)) := by
  let q : E1 → ℝ := fun x => projectiveToricEuclideanProfile u x -
    projectiveLineLogPartition (x 0)
  have hf : Continuous (projectiveToricEuclideanProfile u) :=
    continuousOn_univ.mp ((projectiveToricEuclideanProfile_convex hu hiu).continuousOn isOpen_univ)
  have h0 : Continuous (fun x : E1 => projectiveLineLogPartition (x 0)) := by
    unfold projectiveLineLogPartition
    exact (show Continuous (fun x : E1 => 1 + Real.exp (x 0)) by fun_prop).log
      (fun x => ne_of_gt (by positivity))
  have hq : Continuous q := hf.sub h0
  have ha : Measurable (fun p => (u p).toReal) :=
    GlobalSlotStokes.ThetaPlurisubharmonic.measurable_toReal
      (isThetaPshPotential_projectiveNativeFS_of_source hu).1
  have hnorm :
      (∫⁻ p, ENNReal.ofReal ‖(u p).toReal‖ ∂projectiveToricNonPluripolarMeasure hv) =
        ∫⁻ x, ENNReal.ofReal ‖q x‖
          ∂alexandrovMeasure B volume (projectiveToricCorrectedDescent v) := by
    apply projectiveToricNonPluripolarMeasure_lintegral_eq_tropical hv hiv _
      (ENNReal.measurable_ofReal.comp hq.norm.measurable)
    intro z hz
    rw [projectiveToricEuclideanProfile_uncorrected hu hiu hz, EReal.toReal_coe]
    rfl
  change Integrable (fun p => (u p).toReal) (projectiveToricNonPluripolarMeasure hv) ↔
    Integrable q (alexandrovMeasure B volume (projectiveToricCorrectedDescent v))
  constructor
  · intro hint
    refine ⟨hq.aestronglyMeasurable, (hasFiniteIntegral_iff_norm q).mpr ?_⟩
    rw [← hnorm]
    exact (hasFiniteIntegral_iff_norm _).mp hint.2
  · intro hint
    refine ⟨ha.aestronglyMeasurable, (hasFiniteIntegral_iff_norm _).mpr ?_⟩
    rw [hnorm]
    exact (hasFiniteIntegral_iff_norm q).mp hint.2

/-- Genuine signed cross-input transport for integrable original potentials,
retaining the singular parts of the actual measure used by the energy derivative. -/
theorem projectiveToricNonPluripolarMeasure_integral_toReal_eq_tropical {u v : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hiu : ProjectiveCircleInvariant u)
    (hv : projectiveLineAtlas.IsThetaPSH projectiveFSForm v)
    (hiv : ProjectiveCircleInvariant v)
    (hint : Integrable (fun p => (u p).toReal) (projectiveToricNonPluripolarMeasure hv)) :
    (∫ p, (u p).toReal ∂projectiveToricNonPluripolarMeasure hv) =
      ∫ x, (projectiveToricEuclideanProfile u x - projectiveLineLogPartition (x 0))
        ∂alexandrovMeasure B volume (projectiveToricCorrectedDescent v) := by
  let P := projectiveToricPuncturedPatch hv
  let ν := scalarCanonicalBTMeasure (projectiveToricScalarProfile_convex hv hiv)
  let q : E1 → ℝ := fun x => projectiveToricEuclideanProfile u x -
    projectiveLineLogPartition (x 0)
  have hs : ν (P.domain : Set (ComplexModel 1))ᶜ = 0 :=
    canonicalMixedBedfordTaylorMeasure_compl _ _ _
  have hwhole : projectiveToricNonPluripolarMeasure hv = P.pushMeasure ν := by
    rw [projectiveToricNonPluripolarMeasure_eq_push_scalarRadial hv hiv,
      ← scalarCanonicalBT_eq_map_radial]
  have hq : Integrable q (Measure.map tropicalization ν) := by
    rw [projectiveToricCanonicalBT_tropicalPushforward hv hiv]
    exact (projectiveToric_integrable_toReal_iff_realMA hu hiu hv hiv).mp hint
  obtain ⟨hT, _⟩ := exists_compact_tropical_torus_lift (n := 1) isCompact_empty
  calc
    _ = ∫ z, (u ((projectiveModelChart false).symm z)).toReal ∂ν := by
      rw [hwhole]
      exact P.integral_pushMeasure hs _
    _ = ∫ z, q (tropicalization z) ∂ν := by
      apply integral_congr_ae
      have hae : ∀ᵐ z ∂ν, z ∈ P.domain := ae_iff.mpr hs
      filter_upwards [hae] with z hz
      rw [projectiveToricEuclideanProfile_uncorrected hu hiu hz, EReal.toReal_coe]
    _ = ∫ x, q x ∂Measure.map tropicalization ν :=
      (integral_map hT.aemeasurable hq.aestronglyMeasurable).symm
    _ = _ := by rw [projectiveToricCanonicalBT_tropicalPushforward hv hiv]

end SGPT.Toric
