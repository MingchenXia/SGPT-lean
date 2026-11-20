import SGPT.Projective.OkounkovOriginalBookVolume
import SGPT.Okounkov.PobDimZeroBook

/-! Actual original dimension-zero own-cone partial bodies, no fabricated degree-two current.
Blueprint: okounkov-original-current-zero.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup
open scoped Topology ENNReal
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
  [SmoothOfRelativeDimension 0 f] (E : ClosedProjectiveEmbedding f) [Nonempty (SchemeComplexPoint f)]
local instance currentZeroTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance currentZeroCharts : ChartedSpace (ComplexModel 0) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f 0
local instance currentZeroManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold 0 (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f 0

/-- Actual original n0 own-cone body equality, with no current-equality or positivity premise. -/
theorem partialBodies_ownCones_eq_zeroDimension {L L' : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f 0 E L)
    (b : LineBundleAtlas L') (K : SchemeLineBundleMetric f 0 E L')
    (v : AddValuation X.functionField (WithTop (Lex (Fin 0 → ℤ)))) (c : X)
    {φ ψ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsThetaPshPotential (H.curvature a).val φ)
    (hψ : letI := E.isSeparated; letI := E.quasiCompact; IsThetaPshPotential (K.curvature b).val ψ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ∃ (hAc : IsCompact (okounkovBody v c a)) (hAv : Convex ℝ (okounkovBody v c a))
      (hBc : IsCompact (okounkovBody v c b)) (hBv : Convex ℝ (okounkovBody v c b)),
      okounkovBody v c a = okounkovBody v c b ∧
      iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ = 1 ∧
      iVolume (K.curvature b) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) ψ hψ = 1 ∧
      ValGen.partialBody f 0 E v c a (SGPT.GAGA.OkoClose.coneOver _ hAc hAv) φ =
        ValGen.partialBody f 0 E v c b (SGPT.GAGA.OkoClose.coneOver _ hBc hBv) ψ := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E 0
  obtain ⟨Y,hY⟩ := exists_original_smoothFlag_allDimensions f 0 E
  have hA := PobDimZero.valuation_okounkovBody_eq_univ f E Y hY a c v
  have hB := PobDimZero.valuation_okounkovBody_eq_univ f E Y hY b c v
  have hAc : IsCompact (okounkovBody v c a) := by rw [hA]; exact isCompact_univ
  have hAv : Convex ℝ (okounkovBody v c a) := by rw [hA]; exact convex_univ
  have hBc : IsCompact (okounkovBody v c b) := by rw [hB]; exact isCompact_univ
  have hBv : Convex ℝ (okounkovBody v c b) := by rw [hB]; exact convex_univ
  have h1A : ((0:Fin 0 → ℝ),(1:ℝ))∈(SGPT.GAGA.OkoClose.coneOver _ hAc hAv).cone := by
    refine ⟨zero_le_one,0,?_,by simp⟩
    rw [hA]
    exact mem_univ _
  have h1B : ((0:Fin 0 → ℝ),(1:ℝ))∈(SGPT.GAGA.OkoClose.coneOver _ hBc hBv).cone := by
    refine ⟨zero_le_one,0,?_,by simp⟩
    rw [hB]
    exact mem_univ _
  refine ⟨hAc,hAv,hBc,hBv,hA.trans hB.symm,
    PobDimZero.iVolume_eq_one (H.curvature a) _ hφ,PobDimZero.iVolume_eq_one (K.curvature b) _ hψ,?_⟩
  exact (PobDimZero.valuation_partialBody_eq_univ f E Y hY a c v hφ.quasiPshPotential _ h1A).trans
    (PobDimZero.valuation_partialBody_eq_univ f E Y hY b c v hψ.quasiPshPotential _ h1B).symm

end SGPT.Okounkov.OriginalBook
