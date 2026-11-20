import SGPT.BDivisor.StrictVolume.MovingPencilCartier
import SGPT.BDivisor.StrictVolume.NativeProjectivePointIncidence
import SGPT.BDivisor.StrictVolume.OffCentreTrace
import SGPT.BDivisor.StrictVolume.HyperplaneCartierVolume
import SGPT.BDivisor.StrictVolume.SurfaceExceptionalImage

/-! The entire original moving-centre strict-volume b-divisor example. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.BDivisor.MovingPencilNext

open Set Filter
open SGPT.Projective SGPT.Projective.FsNormalizationNext
open SGPT.Toric SGPT.Toric.BlowdownDraft SGPT.Toric.F1IntersectionDraft
open SGPT.BDivisor.MovingCentresNext SGPT.BDivisor.StrictPencilNext
open SGPT.BDivisor.ProjectiveCurveEscapeNext SGPT.BDivisor.TraceOffCentreNext
open SGPT.BDivisor.BaseHyperplaneNext
open SGPT.Bergman.NativeHermitianMetric
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.NefMixedMass
open scoped Topology Manifold ContDiff ENNReal

attribute [local instance] MvPolynomial.gradedAlgebra

def originalMovingPencilModel (i : ℕ) : Modification 2 (ComplexProjectiveSpace 2) :=
  movedPencilModification blowup_edgeSmooth (i : ℂ) (Complex.exp (i : ℂ))

def originalMovingPencilBDivisor (i : ℕ) :
    WeilBDivisor 2 (ComplexProjectiveSpace 2) (by decide) :=
  movedPencilCartierBDivisor blowup_edgeSmooth (i : ℂ) (Complex.exp (i : ℂ))

theorem originalMovingPencilModel_isBlowup (i : ℕ) :
    IsBlowupAlong 2 ({projectiveCurveEscapingSequence i} : Set (ComplexProjectiveSpace 2))
      (originalMovingPencilModel i).map := by
  have h := movedBlowdown_isBlowupAlong blowup_edgeSmooth (i : ℂ) (Complex.exp (i : ℂ))
  rw [movedBlowupCentre_affinePoint] at h
  exact h

theorem originalMovingPencilBDivisor_realization (i : ℕ) :
    (originalMovingPencilBDivisor i).IsRealization (originalMovingPencilModel i)
      (classPullback (originalMovingPencilModel i).contMDiff_map
        (RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := 2))) -
        (show RealBottChern 2 (originalMovingPencilModel i).carrier from
          RealBottChern.ofRepresentative (originalExceptionalMetric blowup_edgeSmooth).form)) := by
  have h := WeilBDivisor.isRealization_cartierOf (hn := by decide)
    (movedPencilModification blowup_edgeSmooth (i : ℂ) (Complex.exp (i : ℂ)))
    (RealBottChern.ofRepresentative (originalPencilFsMetric blowup_edgeSmooth).form)
  exact (movedPencilClass_eq_pullbackH_sub_E blowup_edgeSmooth (i : ℂ) (Complex.exp (i : ℂ))) ▸ h

theorem originalMovingPencilClass_isNef (i : ℕ) :
    ClassNefWithRespectTo
      (show KahlerBackground 2 (originalMovingPencilModel i).carrier from
        polytopeToricKahlerBackground blowupGenerator blowup_edgeSmooth)
      (classPullback (originalMovingPencilModel i).contMDiff_map
        (RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := 2))) -
        (show RealBottChern 2 (originalMovingPencilModel i).carrier from
          RealBottChern.ofRepresentative (originalExceptionalMetric blowup_edgeSmooth).form)) := by
  have h : ClassNefWithRespectTo (polytopeToricKahlerBackground blowupGenerator blowup_edgeSmooth)
      (RealBottChern.ofRepresentative (originalPencilFsMetric blowup_edgeSmooth).form) :=
    classNefWithRespectTo_of_semipositive _ (originalPencilFsMetric_isSemipositive blowup_edgeSmooth)
  exact (movedPencilClass_eq_pullbackH_sub_E blowup_edgeSmooth (i : ℂ) (Complex.exp (i : ℂ))) ▸ h

theorem originalMovingPencilBDivisor_trace (i : ℕ)
    (rho : Modification 2 (ComplexProjectiveSpace 2))
    {U : Set (ComplexProjectiveSpace 2)} (hiso : IsIsomorphismOver 2 rho.map U)
    (hp : projectiveCurveEscapingSequence i ∈ U) :
    (originalMovingPencilBDivisor i).onModel rho = classPullback rho.contMDiff_map
      (RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := 2))) := by
  have hc : movedBlowupCentre (i : ℂ) (Complex.exp (i : ℂ)) ∈ U := by
    rwa [movedBlowupCentre_affinePoint]
  have h := original_recentered_exceptional_cartier_trace_eq_pullback blowup_edgeSmooth
    (pointTranslation (i : ℂ) (Complex.exp (i : ℂ)))
    (originalMovingPencilModel i).isAnalyticModification rho
    (RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := 2))) hiso hc
  change (WeilBDivisor.cartierOf (by decide) (originalMovingPencilModel i)
    (classPullback (originalMovingPencilModel i).contMDiff_map
      (RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := 2))) -
      (show RealBottChern 2 (originalMovingPencilModel i).carrier from
        RealBottChern.ofRepresentative (originalExceptionalMetric blowup_edgeSmooth).form))).onModel rho = _ at h
  have hEq : originalMovingPencilBDivisor i = WeilBDivisor.cartierOf (by decide)
      (originalMovingPencilModel i)
      (classPullback (originalMovingPencilModel i).contMDiff_map
        (RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := 2))) -
        (show RealBottChern 2 (originalMovingPencilModel i).carrier from
          RealBottChern.ofRepresentative (originalExceptionalMetric blowup_edgeSmooth).form)) :=
    congrArg (fun c : RealBottChern 2 (PolytopeToricVariety blowupGenerator blowup_edgeSmooth) =>
      WeilBDivisor.cartierOf (by decide)
        (movedPencilModification blowup_edgeSmooth (i : ℂ) (Complex.exp (i : ℂ))) c)
      (movedPencilClass_eq_pullbackH_sub_E blowup_edgeSmooth (i : ℂ) (Complex.exp (i : ℂ)))
  exact (congrArg (fun D => D.onModel rho) hEq).trans h

theorem originalMovingPencilBDivisor_eventually_trace
    (rho : Modification 2 (ComplexProjectiveSpace 2)) :
    ∀ᶠ i : ℕ in atTop, (originalMovingPencilBDivisor i).onModel rho =
      originalHyperplaneCartierBDivisor.onModel rho := by
  filter_upwards [originalSurfaceModel_eventually_isomorphism_near rho
    projectiveCurveEscapingSequence projectiveCurveEscapingSequence_injective]
    with i hi
  obtain ⟨U, _hU, hp, hiso⟩ := hi
  rw [originalHyperplaneCartierBDivisor_onModel]
  exact originalMovingPencilBDivisor_trace i rho hiso hp

theorem originalMovingPencilBDivisor_converges :
    WeilBDivisor.Converges atTop originalMovingPencilBDivisor originalHyperplaneCartierBDivisor := by
  intro rho
  let : TopologicalSpace (RealBottChern 2 rho.carrier) := euclideanTopology _
  exact tendsto_const_nhds.congr' (by
    filter_upwards [originalMovingPencilBDivisor_eventually_trace rho] with i hi
    exact hi.symm)

def originalMovingPencilSelfIntersection (i : ℕ) : ℝ := by
  letI : MeasurableSpace (originalMovingPencilModel i).carrier := borel _
  letI : BorelSpace (originalMovingPencilModel i).carrier := ⟨rfl⟩
  exact classSlotIntegral
      (show KahlerBackground 2 (originalMovingPencilModel i).carrier from
        polytopeToricKahlerBackground blowupGenerator blowup_edgeSmooth)
      (fun _ : Fin 2 => (originalMovingPencilBDivisor i).onModel (originalMovingPencilModel i))

theorem originalMovingPencilBDivisor_square_zero (i : ℕ) :
    originalMovingPencilSelfIntersection i = 0 := by
  unfold originalMovingPencilSelfIntersection
  change classSlotIntegral (polytopeToricKahlerBackground blowupGenerator blowup_edgeSmooth)
    (fun _ : Fin 2 => (movedPencilCartierBDivisor blowup_edgeSmooth (i : ℂ) (Complex.exp (i : ℂ))).onModel
      (movedPencilModification blowup_edgeSmooth (i : ℂ) (Complex.exp (i : ℂ)))) = 0
  simp_rw [movedPencilCartierBDivisor_onModel]
  rw [classSlotIntegral_ofRepresentative]
  exact originalPencil_nativeSelfIntersection_zero blowup_edgeSmooth _

theorem sourceOriginalStrictVolumeExample :
    Function.Injective projectiveCurveEscapingSequence ∧
    (∀ Z : Set (ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)),
      IsClosed Z → Z ≠ univ →
        {i : ℕ | actualNativeProjectivePoint (projectiveCurveEscapingSequence i) ∈ Z}.Finite) ∧
    (∀ i, IsBlowupAlong 2 ({projectiveCurveEscapingSequence i} : Set (ComplexProjectiveSpace 2))
      (originalMovingPencilModel i).map) ∧
    (∀ i, (originalMovingPencilBDivisor i).IsRealization (originalMovingPencilModel i)
      (classPullback (originalMovingPencilModel i).contMDiff_map
        (RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := 2))) -
        (show RealBottChern 2 (originalMovingPencilModel i).carrier from
          RealBottChern.ofRepresentative (originalExceptionalMetric blowup_edgeSmooth).form))) ∧
    (∀ i, ClassNefWithRespectTo
      (show KahlerBackground 2 (originalMovingPencilModel i).carrier from
        polytopeToricKahlerBackground blowupGenerator blowup_edgeSmooth)
      (classPullback (originalMovingPencilModel i).contMDiff_map
        (RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := 2))) -
        (show RealBottChern 2 (originalMovingPencilModel i).carrier from
          RealBottChern.ofRepresentative (originalExceptionalMetric blowup_edgeSmooth).form))) ∧
    (∀ i, (originalMovingPencilBDivisor i).IsNefCartier ∧
      (originalMovingPencilBDivisor i).IsPseudoeffective ∧ (originalMovingPencilBDivisor i).vol = 0) ∧
    (∀ i, originalMovingPencilSelfIntersection i = 0) ∧
    (∀ rho : Modification 2 (ComplexProjectiveSpace 2),
      ∀ᶠ i : ℕ in atTop, (originalMovingPencilBDivisor i).onModel rho =
        originalHyperplaneCartierBDivisor.onModel rho) ∧
    WeilBDivisor.Converges atTop originalMovingPencilBDivisor originalHyperplaneCartierBDivisor ∧
    originalHyperplaneCartierBDivisor.vol = 1 ∧
    classSlotIntegral (ComplexProjectiveSpace.fsBackground (N := 2))
      (fun _ : Fin 2 => RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := 2))) = 1 ∧
    RealBottChern.ofRepresentative (sourceNativeFirstChernForm nativeProjectiveHyperplaneBundle
      physicalProjectiveHyperplane_sourceSmooth) =
      RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := 2)) ∧
    Filter.limsup (fun i : ℕ => (originalMovingPencilBDivisor i).vol) atTop <
      originalHyperplaneCartierBDivisor.vol := by
  have hvol : (fun i : ℕ => (originalMovingPencilBDivisor i).vol) =
      (fun _ : ℕ => (0 : ℝ≥0∞)) :=
    funext fun i => movedPencilCartierBDivisor_volume_zero blowup_edgeSmooth (i : ℂ) (Complex.exp (i : ℂ))
  have hstrict : Filter.limsup (fun i : ℕ => (originalMovingPencilBDivisor i).vol) atTop <
      originalHyperplaneCartierBDivisor.vol := by
    rw [hvol, Filter.limsup_const, originalHyperplaneCartierBDivisor_volume_eq_one]
    exact zero_lt_one
  exact ⟨projectiveCurveEscapingSequence_injective,
    every_proper_native_projective_algebraic_closed_incidence_finite,
    originalMovingPencilModel_isBlowup, originalMovingPencilBDivisor_realization,
    originalMovingPencilClass_isNef,
    fun i => ⟨movedPencilCartierBDivisor_isNefCartier _ _ _,
      movedPencilCartierBDivisor_isPseudoeffective _ _ _, movedPencilCartierBDivisor_volume_zero _ _ _⟩,
    originalMovingPencilBDivisor_square_zero, originalMovingPencilBDivisor_eventually_trace,
    originalMovingPencilBDivisor_converges, originalHyperplaneCartierBDivisor_volume_eq_one,
    originalCP2_fs_classSlotIntegral_eq_one, physicalProjectiveHyperplane_firstChernClass, hstrict⟩

end SGPT.BDivisor.MovingPencilNext
