import SGPT.Okounkov.PartialBodyDS
import SGPT.Okounkov.ValuativeSliceBounded
import SGPT.Foundations.Analysis.Pending.TraceRepresentativeStageGlobalPOrder

/-! Actual antitone native limits identify intersections of the same
original general bodies; Hausdorff convergence is an output of existing DS continuity. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceSlice
open Set Filter Metric MeasureTheory
open scoped Topology Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology
open SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDistance
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.PartialBody
open SGPT.Okounkov.TranscendentalMain

/-- A genuine antitone native limit at positive mass identifies the exact
intersection of the original bodies, with all indices and potentials retained. -/
theorem iInter_generalPartialBody_eq_of_antitone_native_limit
    {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    [MeasurableSpace F.carrier] [BorelSpace F.carrier]
    (ω : KahlerBackground (m + 1) F.carrier)
    (θ : ClosedRealOneOneForm (m + 1) F.carrier)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (u : ℕ → ThetaPshL1 θ.val) (v : ThetaPshL1 θ.val)
    (hv : HasPositivePotentialMass θ v.val v.property)
    (hanti : Antitone (fun j => (u j).val))
    (hlim : Tendsto u atTop (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace ω θ hbig).toUniformSpace.toTopologicalSpace v)) :
    (⋂ j, generalPartialBody F θ (u j).val) = generalPartialBody F θ v.val := by
  have hD := tendsto_hausdorffDist_generalPartialBody ω hbig atTop u v hv hlim
  apply Subset.antisymm
  · intro x hx
    let E := (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
    let B := euclideanImage (generalPartialBody F θ v.val)
    have hB : IsCompact B := (convex_isCompact_generalPartialBody v.property).2.image E.continuous
    have hBn : B.Nonempty := (nonempty_generalPartialBody v.property).image E
    have hxj (j : ℕ) : E x ∈ euclideanImage (generalPartialBody F θ (u j).val) :=
      ⟨x, mem_iInter.mp hx j, rfl⟩
    have hfin (j : ℕ) : hausdorffEDist
        (euclideanImage (generalPartialBody F θ (u j).val)) B ≠ ⊤ := by
      have hAj : IsCompact (euclideanImage (generalPartialBody F θ (u j).val)) :=
        (convex_isCompact_generalPartialBody (u j).property).2.image E.continuous
      exact hausdorffEDist_ne_top_of_nonempty_of_bounded ⟨E x, hxj j⟩ hBn
        hAj.isBounded hB.isBounded
    have hinf : infDist (E x) B = 0 := by
      apply le_antisymm ?_ infDist_nonneg
      exact le_of_tendsto_of_tendsto tendsto_const_nhds hD
        (Eventually.of_forall fun j => infDist_le_hausdorffDist_of_mem (hxj j) (hfin j))
    have hxB : E x ∈ B := by
      rw [← hB.isClosed.closure_eq]
      exact (mem_closure_iff_infDist_zero hBn).mpr hinf
    obtain ⟨y, hy, heq⟩ := hxB
    have hyx : y = x := E.injective heq
    exact hyx ▸ hy
  · refine subset_iInter fun j => ?_
    exact Valuative.generalPartialBody_mono_of_iOrder v.property (u j).property
      (GlobalPMultiplierOrder.iOrderOnManifold_of_sourcePOrder
        (TraceRepresentativeStageGlobalPOrder.sourcePOrder_le_stage_of_antitone_native_limit
          ω θ hbig u v hanti hlim j))
end SGPT.Okounkov.SourceSlice
