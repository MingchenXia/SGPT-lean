import SGPT.Okounkov.SourceSliceResolvedPositive
import SGPT.Okounkov.SourceSliceCorrection
import SGPT.Okounkov.PartialBodyBirational
import SGPT.Okounkov.TranscendentalLiftingResolution
import SGPT.Okounkov.ValuativeSliceBounded

/-! Original analytic source currents: the actual resolution is constructed
internally; the unchanged original body and genuine source trace are retained. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceSlice
open Set Matrix
open scoped Pointwise Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Foundations.Analysis.Pending.NaturalSubmanifoldSourceTraceDefinition
open SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalLifting
open SGPT.Okounkov.TranscendentalPartial SGPT.Okounkov.PartialBody
open SGPT.PSH
open SGPT.Okounkov.TranscendentalMain SGPT.Okounkov.TranscendentalSlice SGPT.Okounkov.TranscendentalWN

/-- The original analytic current, without a Kähler hypothesis, has the
ordinary restriction slice whenever that literal restriction is a genuine
potential. Resolution and metered divisor are internally manufactured. -/
theorem slice_zero_of_globalAnalytic_of_restriction_psh
    {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 2))
    {θ : ClosedRealOneOneForm (m + 2) F.carrier} {φ : F.carrier → EReal}
    (hφA : φ ∈ globalAnalyticCurrents θ)
    (hr : IsThetaPshPotential (firstFlagRestriction F θ).val
      (fun y : F.tail.carrier => φ y.val)) :
    firstCoordinateSlice (generalPartialBody F θ φ) 0 =
      generalPartialBody F.tail (firstFlagRestriction F θ)
        (fun y : F.tail.carrier => φ y.val) := by
  obtain ⟨c, I, ht⟩ := hφA.2
  obtain ⟨W, π, hp, D, hπ, hlog, hdata, hval⟩ :=
    exists_logResolution_flagLifting F θ hφA.1 ht
  obtain ⟨b, C, hb, hC, heq⟩ := hdata
  have hAπ := comp_mem_globalAnalyticCurrents hπ.1 hφA
  have hb' : IsThetaPshPotential
      (ClosedRealOneOneForm.pullback hπ.1.1 θ - D.curvature).val b := by
    refine ⟨hb, fun x U _ hxU => ?_⟩
    exact ⟨x, hxU, ne_bot_of_le_ne_bot (EReal.coe_ne_bot (-C)) (hC x).1⟩
  have hrπ := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    hπ.tailMap_isFlagLifting.1 (firstFlagRestriction F θ) hr
  have hnd : LocallyNondegenerate (fun y : W.tail.carrier => φ (π y.val)) := hrπ.2
  have hslice := slice_zero_of_actual_positive_resolved_decomposition W hAπ D hb'
    ⟨C, hC⟩ heq hnd
  have hbodytail : generalPartialBody W.tail
      (firstFlagRestriction W (ClosedRealOneOneForm.pullback hπ.1.1 θ))
      (fun y : W.tail.carrier => φ (π y.val)) =
      (fun y => y ᵥ* correctionMatrixReal hπ.tailMap_isFlagLifting) ''
        generalPartialBody F.tail (firstFlagRestriction F θ)
          (fun y : F.tail.carrier => φ y.val) := by
    exact (generalPartialBody_eq_of_geometricallyEq W.tail
      (firstFlagRestriction_pullback_geometricallyEq hπ θ) hrπ).trans
      (generalPartialBody_pullback hr hπ.tailMap_isFlagLifting)
  rw [generalPartialBody_pullback hφA.1 hπ,
    firstCoordinateSlice_image_correction hπ, hbodytail] at hslice
  exact (Set.image_injective.mpr
    (bijective_vecMul_correctionMatrixReal hπ.tailMap_isFlagLifting).injective) hslice

/-- Full analytic-singularity case of the original source `lma:slicepob`,
including every genuine source trace representative in the original class.
There is no supplied restriction, divisor, resolution or slice certificate. -/
theorem slice_zero_generalPartialBody_eq_of_globalAnalytic
    {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 2))
    {θ : ClosedRealOneOneForm (m + 2) F.carrier} {φ : F.carrier → EReal}
    (hφA : φ ∈ globalAnalyticCurrents θ)
    {τ : F.tail.carrier → EReal}
    (hτ : IsNaturalSourceTraceRepresentative F.omega F.firstDivisor φ τ)
    {ψ : F.tail.carrier → EReal}
    (hψ : IsThetaPshPotential (firstFlagRestriction F θ).val ψ)
    (hP : letI : MeasurableSpace F.tail.carrier := borel F.tail.carrier
      have _ : BorelSpace F.tail.carrier := ⟨rfl⟩
      SourcePEquivalent (n := m + 1) ψ τ) :
    firstCoordinateSlice (generalPartialBody F θ φ) 0 =
      generalPartialBody F.tail (firstFlagRestriction F θ) ψ := by
  let _ : MeasurableSpace F.tail.carrier := borel F.tail.carrier
  have _ : BorelSpace F.tail.carrier := ⟨rfl⟩
  have htr : IsSourceTraceRepresentativeAlong F.omega F.tail.omega
      (SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ (m + 1)) F.firstDivisor.2.2)
      φ τ := hτ
  have hτr := SGPT.Trace.sourcePEquivalent_trace_restriction_of_analytic
    (Nat.le_succ (m + 1)) F.tail.omega _ htr
    (globalAnalyticCurrents_subset_analyticCurrents θ hφA).2
  have hnd : LocallyNondegenerate (fun y : F.tail.carrier => φ y.val) := by
    obtain ⟨σ, hτpsh, hrpsh, _, _, _⟩ := hτr.1
    exact hrpsh.2
  have hr : IsThetaPshPotential (firstFlagRestriction F θ).val
      (fun y : F.tail.carrier => φ y.val) :=
    TranscendentalVolId.isThetaPshPotential_restrict
      (F := F) hφA.1.1 hnd (singularityLE_refl _)
  rw [slice_zero_of_globalAnalytic_of_restriction_psh F hφA hr]
  apply Subset.antisymm
  · exact Valuative.generalPartialBody_mono_of_iOrder hr hψ
      (GlobalPMultiplierOrder.iOrderOnManifold_of_sourcePOrder
        (SourcePOrder.trans F.tail.omega hτr.2 hP.2))
  · exact Valuative.generalPartialBody_mono_of_iOrder hψ hr
      (GlobalPMultiplierOrder.iOrderOnManifold_of_sourcePOrder
        (SourcePOrder.trans F.tail.omega hP.1 hτr.1))
end SGPT.Okounkov.SourceSlice
