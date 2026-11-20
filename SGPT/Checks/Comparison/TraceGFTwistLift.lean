import SGPT.Checks.Comparison.TraceGFTwists
import SGPT.Checks.Comparison.SourceRationalHullImage

/-! Original GF hull construction in the SAME actual tensor Chern class.
Blueprint: trace-na-general-family.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison.GFTwist
open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Envelope
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
open SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (r : ℕ)
  [SmoothOfRelativeDimension (r+1) f] [IsIntegral X] [IsProjective f]
  (EX : ClosedProjectiveEmbedding f)
local instance twistLiftProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance twistLiftTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance twistLiftCharts : ChartedSpace (ComplexModel (r+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (r+1)
local instance twistLiftManifold : IsComplexManifold (r+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (r+1)
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]

/-- Actual original GF hull in the literal original tensor perturbation
class. Uses the original full-An hull producer with all original sections;
no supplied NA curve or value certificate. -/
theorem exists_originalGF_twist_lift
    {L S : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (r+1) EX L)
    (aS : LineBundleAtlas S) (HS : SchemeLineBundleMetric f (r+1) EX S)
    {d : ℕ} (hd : 0 < d)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel (r+1) (SchemeComplexPoint f))}
    (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((d : ℝ)⁻¹) • H.curvature a).val)
    (κX : SourceKahlerForm (r+1) (SchemeComplexPoint f)) (ε : ℚ) (hε : 0 ≤ ε)
    {ψ : BerkovichPoint f → EReal}
    (hGF : IsRationalGF f ((d : ℚ)⁻¹ • rationalPicardClass a + ε • rationalPicardClass aS) ψ) :
    ∃ G : SourceNAPotential (twistForm f (r+1) EX aS HS θ (ε : ℝ)),
      naPotentialAnAt (r+1) EX G κX = ψ := by
  have hd' : 0 < d * ε.den := Nat.mul_pos hd ε.den_pos
  rw [← rationalPicardClass_twist a aS hd ε hε] at hGF
  obtain ⟨D,_hD,hAn⟩ := BJ.SourceRationalHull.exists_originalHull_naPotentialAnAt_eq_of_isRationalGF
    f (r+1) EX (twistLineAtlas a aS ε.den (d*ε.num.toNat))
    (twistLineMetric f (r+1) EX a H aS HS ε.den (d*ε.num.toNat)) hd'
    (twistForm_geometricallyEq f (r+1) EX a H aS HS hd hθ ε hε) hGF
  exact ⟨Berkovich.PiecewiseLinearData.hullNAPotential D,hAn κX⟩

end SGPT.NAPotential.TraceComparison.GFTwist
