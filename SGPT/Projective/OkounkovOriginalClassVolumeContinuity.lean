import SGPT.Projective.OkounkovOriginalPerturbGeometry

/-! Existing native ORIGINAL class I-volume right continuity on actual original schemes, all dimensions and zero mass.
Blueprint: okounkov-original-class-volume-continuity.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Okounkov.TranscendentalCore
open scoped Topology ENNReal
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f) [Nonempty (SchemeComplexPoint f)]
local instance classVolumeContinuityTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance classVolumeContinuityCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance classVolumeContinuityManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- True ORIGINAL I-volume class right continuity, every dimension including0, without any positive mass assumption. -/
theorem tendsto_original_iVolume_add_smul_allDimensions {L A : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
    (aA : LineBundleAtlas A) (K : SchemeLineBundleMetric f n E A)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (K.curvature aA).val.IsKahler)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsThetaPshPotential (H.curvature a).val φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let κ : KahlerBackground n (SchemeComplexPoint f) := ⟨K.curvature aA,hK⟩
    Tendsto (fun t : NNReal => iVolume (H.curvature a+(t:ℝ)•K.curvature aA)
      (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ
      (LocalPotentials.isThetaPshPotential_add_of_semipositive hφ
        (KahlerDomination.isSemipositive_smul κ.isSemipositive t.property)))
      (𝓝[>] (0:NNReal))
      (𝓝 (iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ)) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E n
  let κ : KahlerBackground n (SchemeComplexPoint f) := ⟨K.curvature aA,hK⟩
  cases n with
  | zero => simpa only [PobDimZero.iVolume_eq_one] using (tendsto_const_nhds : Tendsto (fun _ : NNReal => (1:ℝ≥0∞)) (𝓝[>] (0:NNReal)) (𝓝 1))
  | succ m => exact PartialBody.tendsto_iVolume_add_smul κ hφ
end SGPT.Okounkov.OriginalBook
