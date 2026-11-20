import SGPT.Projective.OkounkovOriginalRightScalarBodyConvergence
import SGPT.Okounkov.PobDimZeroBook

/-! Actual original right-scalar own bodies and Kähler I-volume positivity, every dimension.
Blueprint: okounkov-original-right-scalar-all-dimensions.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Okounkov.AlgebraicValuation
open scoped Topology ENNReal
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
local instance rightScalarAllTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance rightScalarAllCharts {n : ℕ} [SmoothOfRelativeDimension n f] : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance rightScalarAllManifold {n : ℕ} [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- Actual original Kähler-current weights have positive ORIGINAL I-volume, including genuine dimension0. -/
theorem original_iVolume_pos_of_kahler_allDimensions
    (n : ℕ) [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
    [Nonempty (SchemeComplexPoint f)] {L : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsKahlerCurrentPotential (H.curvature a) φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ
      (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E n
  have hθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
  cases n with
  | zero => rw [PobDimZero.iVolume_eq_one (H.curvature a) _ hθ]; exact zero_lt_one
  | succ m =>
    exact (PartialBody.diagonalPotentialMass_pos_of_isKahlerCurrentPotential hφ hθ).trans_le
      (PartialBody.diagonalPotentialMass_le_iVolume (schemeProjectiveTNKahlerBackground f (m+1) E) hθ)

/-- SAME original own-cone right scalar Hausdorff convergence, ALL original dimensions. -/
theorem exists_right_scalar_partialBody_convergence_allDimensions
    (n : ℕ) [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
    [Nonempty (SchemeComplexPoint f)] {L : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L) (hbig : SGPT.LineBundle.IsBig f L n)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (hv : Function.Surjective v)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsKahlerCurrentPotential (H.curvature a) φ) :
    haveI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ (hKc : IsCompact (centreOkounkovBody f v a)) (hKv : Convex ℝ (centreOkounkovBody f v a))
      (r₁ : ℝ), 1<r₁ ∧
      (∀ r : Ioo (1:ℝ) r₁, IsKahlerCurrentPotential (H.curvature a) (fun x => (r.val:EReal)*φ x)) ∧
      ∀ (I : Type*) (l : Filter I) (r : I → Ioo (1:ℝ) r₁), Tendsto (fun i => (r i).val) l (𝓝 1) →
        Tendsto (fun i => Metric.hausdorffDist
          (ValGen.partialBody f n E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv)
            (fun x => ((r i).val:EReal)*φ x))
          (ValGen.partialBody f n E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ)) l (𝓝 0) := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  cases n with
  | succ m => exact exists_right_scalar_partialBody_convergence f E a H hbig v hv hφ
  | zero =>
    obtain ⟨r₁,hr1,hK⟩ := NativeRightScalarConvergence.exists_right_scalar_kahler_neighborhood hφ
    obtain ⟨Y,hY⟩ := exists_original_smoothFlag_allDimensions f 0 E
    have hfull : centreOkounkovBody f v a=univ :=
      PobDimZero.valuation_okounkovBody_eq_univ f E Y hY a (valuationCenter f v) v
    have hKc : IsCompact (centreOkounkovBody f v a) := by rw [hfull]; exact isCompact_univ
    have hKv : Convex ℝ (centreOkounkovBody f v a) := by rw [hfull]; exact convex_univ
    let C := SGPT.GAGA.OkoClose.coneOver _ hKc hKv
    have h1 : ((0:Fin 0 → ℝ),(1:ℝ))∈C.cone := ⟨zero_le_one,0,by rw [hfull]; exact mem_univ _,by simp⟩
    have hbody0 : ValGen.partialBody f 0 E v (valuationCenter f v) a C φ=univ :=
      PobDimZero.valuation_partialBody_eq_univ f E Y hY a (valuationCenter f v) v
        (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ).quasiPshPotential C h1
    have hscalar (r : Ioo (1:ℝ) r₁) := hK r.val r.property.1.le r.property.2.le
    refine ⟨hKc,hKv,r₁,hr1,hscalar,?_⟩
    intro I l r hr
    have hbodyr (i : I) : ValGen.partialBody f 0 E v (valuationCenter f v) a C
        (fun x => ((r i).val:EReal)*φ x)=univ :=
      PobDimZero.valuation_partialBody_eq_univ f E Y hY a (valuationCenter f v) v
        (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential (hscalar (r i))).quasiPshPotential C h1
    have hh : Tendsto (fun _ : I => (0:ℝ)) l (𝓝 0) := tendsto_const_nhds
    apply hh.congr
    intro i
    change 0=Metric.hausdorffDist
      (ValGen.partialBody f 0 E v (valuationCenter f v) a C (fun x => ((r i).val:EReal)*φ x))
      (ValGen.partialBody f 0 E v (valuationCenter f v) a C φ)
    rw [hbodyr,hbody0,Metric.hausdorffDist_self_zero]
end SGPT.Okounkov.OriginalBook
