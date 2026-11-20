import SGPT.NAPotential.DecreasingInfimum
import SGPT.NAPotential.TowerAlgReflect
import SGPT.Checks.Comparison.GFRationalHull

/-! The GIVEN actual original NA curve is the actual original infimum.
Blueprint: trace-na-general-family.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison

open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Envelope
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ.NativePicard
open SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (r : ℕ)
  [SmoothOfRelativeDimension (r+1) f] [IsIntegral X] [IsProjective f]
  (EX : ClosedProjectiveEmbedding f)
local instance givenInfimumProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance givenInfimumTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance givenInfimumCharts : ChartedSpace (ComplexModel (r+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (r+1)
local instance givenInfimumManifold : IsComplexManifold (r+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (r+1)
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]

/-- An ACTUAL same-class approximating sequence with antitone full original
analytifications converging to the GIVEN curve has its genuine intrinsic
orders and cutoff bound produced internally, and its ACTUAL original NA
infimum equals that GIVEN curve. No order/bound/infimum certificate is supplied. -/
theorem exists_decreasingInf_eq_of_An_antitone_tendsto
    {θ : AtlasClosedRealOneOneForm (ofFixedModel (r+1) (SchemeComplexPoint f))}
    (omegaX : KahlerBackground (r+1) (SchemeComplexPoint f))
    (κX : SourceKahlerForm (r+1) (SchemeComplexPoint f))
    (Γ : SourceNAPotential θ) (T : ℕ → SourceNAPotential θ)
    (hanti : ∀ v, Antitone fun i => naPotentialAnAt (r+1) EX (T i) κX v)
    (hlim : ∀ v, Tendsto (fun i => naPotentialAnAt (r+1) EX (T i) κX v)
      atTop (𝓝 (naPotentialAnAt (r+1) EX Γ κX v))) :
    ∃ (ha : ∀ i j, i ≤ j → SourceNAPOrder (T j) (T i))
      (hb : BddBelow (range fun i => sourceNAPotentialCutoff omegaX (T i))),
      SourceNAPotential.decreasingInf omegaX T ha hb = Γ := by
  have hEq : ∀ v, naPotentialAnAt (r+1) EX Γ κX v =
      ⨅ i, naPotentialAnAt (r+1) EX (T i) κX v := fun v =>
    tendsto_nhds_unique (hlim v) (tendsto_atTop_iInf (hanti v))
  have ha : ∀ i j, i ≤ j → SourceNAPOrder (T j) (T i) := fun i j hij =>
    (TowerAlg.sourceNAPOrder_iff_naPotentialAnAt_le (E := EX) κX).mpr fun v => hanti v hij
  have hLower : ∀ i, SourceNAPOrder Γ (T i) := fun i =>
    (TowerAlg.sourceNAPOrder_iff_naPotentialAnAt_le (E := EX) κX).mpr fun v =>
      (hEq v).le.trans (iInf_le _ i)
  have hb : BddBelow (range fun i => sourceNAPotentialCutoff omegaX (T i)) := by
    refine ⟨sourceNAPotentialCutoff omegaX Γ, ?_⟩
    rintro _ ⟨i,rfl⟩
    change sourceNAPotentialCutoff omegaX Γ ≤ sourceNAPotentialCutoff omegaX (T i)
    rw [sourceNAPotentialCutoff_eq_component omegaX Γ κX,
      sourceNAPotentialCutoff_eq_component omegaX (T i) κX]
    exact ((sourceNAPOrder_iff_component Γ (T i) κX).mp (hLower i)).cutoff_le
  refine ⟨ha,hb,?_⟩
  apply SourceNAPOrder.antisymm
  · apply (TowerAlg.sourceNAPOrder_iff_naPotentialAnAt_le (E := EX) κX).mpr
    intro v
    exact ge_of_tendsto (hlim v) (Filter.Eventually.of_forall fun i =>
      DivDict2.naPotentialAnAt_mono (E := EX) (SourceNAPotential.decreasingInf_le omegaX T ha hb i) κX v)
  · exact SourceNAPotential.le_decreasingInf omegaX T ha hb Γ hLower

end SGPT.NAPotential.TraceComparison
