import SGPT.Projective.OkounkovOriginalBookPartial
import SGPT.Okounkov.OkoNSAlgebraic

/-! Actual ORIGINAL tensor-sum I-volume positivity, scalar flag calculation only.
Blueprint: okounkov-original-tensor-sum-ivolume.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.TranscendentalCore
open scoped Topology Pointwise ENNReal
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    {m : ℕ} [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f)
    [Nonempty (SchemeComplexPoint f)]
local instance tensorSumIVolumeTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance tensorSumIVolumeCharts : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (m+1)
local instance tensorSumIVolumeManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold (m+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (m+1)

theorem original_tensorSum_iVolume_pos {L N : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m+1) E L)
    (b : LineBundleAtlas N) (K : SchemeLineBundleMetric f (m+1) E N)
    (d : LineBundleAtlas (bundleTensor L N)) {φ ψ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated;letI := E.quasiCompact;IsThetaPshPotential (H.curvature a).val φ)
    (hψ : letI := E.isSeparated;letI := E.quasiCompact;IsThetaPshPotential (K.curvature b).val ψ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ →
    ∃ hsum : IsThetaPshPotential ((H.tensorProduct K a b).curvature d).val (fun x => φ x+ψ x),
      0 < iVolume ((H.tensorProduct K a b).curvature d)
        (LocalPotentials.closedRealOneOne_hasLocalPotentials _) (fun x => φ x+ψ x) hsum := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  intro hpos
  obtain ⟨Y,hY⟩ := exists_original_smoothFlag_allDimensions f (m+1) E
  let F := schemeFubiniStudyOriginalFlagGeometry f (m+1) E Y hY
  let : MeasurableSpace F.carrier := borel _
  have : BorelSpace F.carrier := ⟨rfl⟩
  let θ := H.curvature a
  let σ := K.curvature b
  have hsum := isThetaPshPotential_add_from_positive_sum hφ hψ
  have hvolA : 0<volume (PartialBody.generalPartialBody F θ φ) := by
    rw [PartialBody.volume_generalPartialBody_of_borelSpace hφ]
    exact ENNReal.div_pos hpos.ne' (ENNReal.natCast_ne_top _)
  have hrealA : 0<volume.real (PartialBody.generalPartialBody F θ φ) :=
    ENNReal.toReal_pos hvolA.ne' (PartialBody.convex_isCompact_generalPartialBody (F:=F) hφ).2.measure_lt_top.ne
  have hrealSum := OkoNS.volume_real_pos_of_add_subset
    (PartialBody.convex_isCompact_generalPartialBody (F:=F) hsum).2 hrealA
    (PartialBody.nonempty_generalPartialBody (F:=F) hψ)
    (PartialBody.generalPartialBody_add_subset (F:=F) hφ hψ)
  have hvolSum : 0<volume (PartialBody.generalPartialBody F (θ+σ) (fun x => φ x+ψ x)) :=
    (ENNReal.toReal_pos_iff.mp hrealSum).1
  rw [PartialBody.volume_generalPartialBody_of_borelSpace hsum] at hvolSum
  change 0 < iVolume (θ+σ) (LocalPotentials.closedRealOneOne_hasLocalPotentials _)
    (fun x => φ x+ψ x) hsum / ((m+1).factorial : ENNReal) at hvolSum
  have hraw : 0 < iVolume (θ+σ) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) (fun x => φ x+ψ x) hsum := by
    by_contra hn
    have hz : iVolume (θ+σ) (LocalPotentials.closedRealOneOne_hasLocalPotentials _)
        (fun x => φ x+ψ x) hsum = 0 := le_antisymm (le_of_not_gt hn) bot_le
    rw [hz,ENNReal.zero_div] at hvolSum
    exact (lt_irrefl 0) hvolSum
  have hgeo := H.curvature_tensorProduct K a b d
  have hphysical := (hgeo.thetaPshPotential_iff (fun x => φ x+ψ x)).mpr hsum
  refine ⟨hphysical,?_⟩
  have heq := SGPT.GAGA.H0L.iVolume_congr_geometricallyEq hgeo
    (LocalPotentials.closedRealOneOne_hasLocalPotentials _) (LocalPotentials.closedRealOneOne_hasLocalPotentials _)
    (fun x => φ x+ψ x) hphysical hsum
  rw [heq]
  exact hraw
end SGPT.Okounkov.OriginalBook
