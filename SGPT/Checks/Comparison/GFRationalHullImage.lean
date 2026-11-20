import SGPT.Checks.Comparison.GFRationalHullCurve
import SGPT.NAPotential.AnTransPLCurve

/-! # ORIGINAL rational hulls: actual section products and analytification at EVERY original point
Source: `lma:gfinimage`, closing paragraph and `eq:gf-rational-hull`.
Blueprint: `gf-rational-hull-image.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.BJ.GfIm.RationalHull

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas SGPT.Convex.CutSimplex
open SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision
open SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision.WholeHull
open SGPT.Foundations.Envelope
open scoped BigOperators Classical ENNReal

variable {X : Scheme.{0}} {L : X.Modules} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]

local instance hullImageProper : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance hullImagePointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance hullImagePointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance hullImagePointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

open SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
variable (b : LineBundleAtlas L) (HM : SchemeLineBundleMetric f n E L)

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]

/-- **The original rational GF function lies in the image of the ACTUAL original NA
analytification on ALL X^An, including n=0**, with the SAME actual original hull potential.
The actual curve, rational common-degree generating sections, and rational hull identity are
all produced from the original GF package internally. -/
theorem exists_originalHull_naPotentialAnAt_eq_of_isRationalGF {m : ℕ} (hm : 0 < m)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)
    {φ : BerkovichPoint f → EReal}
    (hφ : IsRationalGF f ((m : ℚ)⁻¹ • rationalPicardClass b) φ) :
    ∃ A : PiecewiseLinearData θ, OriginalHullRealization f n E b HM m A φ ∧
      ∀ ω : SourceKahlerForm n (SchemeComplexPoint f),
        naPotentialAnAt n E (PiecewiseLinearData.hullNAPotential A) ω = φ := by
  obtain ⟨A, hA⟩ := exists_originalHullRealization_of_isRationalGF f n E b HM hm hθ hφ
  refine ⟨A, hA, fun ω => funext fun v => ?_⟩
  rw [naPotentialAnAt_hullNAPotential, hA.2.2.2 v]
  have hpsh (s : ℝ) (hs : s ≤ A.τ 0) : IsThetaPshPotential (atlasClosedFormToNative θ).val
      (uscRegularization (A.pointwiseUpperConcaveEnvelope s)) := by
    rw [uscRegularization_pointwiseUpperConcaveEnvelope_eq_simplexValue]
    exact (isThetaPSH_iff_nativeThetaPotential θ _).mp (isThetaPSH_simplexValue A s hs)
  apply le_antisymm
  · apply iSup_le
    intro s
    apply (add_real_le_rational_iSup
      (potentialAn n E (uscRegularization (A.pointwiseUpperConcaveEnvelope (s : ℝ))) v)
      (s : ℝ)).trans
    apply iSup_le
    intro q
    apply iSup_le
    intro hq
    apply le_iSup_of_le q
    apply le_iSup_of_le (hq.trans s.2)
    apply add_le_add _ le_rfl
    apply BerkovichPoint.potentialAn_mono_of_multiplierIdealAlgebraic n E
      (SGPT.GAGA.H0S.multiplierIdealAlgebraic f E n) (hpsh s s.2.le)
      (hpsh q (hq.trans s.2).le)
    intro x
    simp only [uscRegularization_pointwiseUpperConcaveEnvelope_eq_simplexValue]
    exact simplexValue_antitone A x hq.le
  · apply iSup_le
    intro q
    apply iSup_le
    intro hq
    exact le_iSup (fun s : Set.Iio (A.τ 0) =>
      potentialAn n E (uscRegularization (A.pointwiseUpperConcaveEnvelope (s : ℝ))) v +
        ((s : ℝ) : EReal)) ⟨(q : ℝ), hq⟩

end SGPT.NAPotential.BJ.GfIm.RationalHull
