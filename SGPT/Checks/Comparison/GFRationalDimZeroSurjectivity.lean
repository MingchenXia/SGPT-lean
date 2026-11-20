import SGPT.Checks.Comparison.GFRationalDimZero
import SGPT.Checks.Comparison.BJCanonicalModuleTopology
import SGPT.NAPotential.DimZeroAnalytification
import SGPT.NAPotential.Homogeneous
import SGPT.NPP.DimensionZero

/-! # Actual original zero-dimensional psh finite constancy and NA preimages
Blueprint: `gf-rational-hull-dimension-zero-surjectivity.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.NAPotential.BJ.GfIm.RationalHull.NarrowDimensionZero

open Set AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.NAPotential.Berkovich SGPT.PSH.VariableComplexAtlas
open SGPT.NAPotential.BJ.Printed SGPT.NAPotential.BJ.NativePicard
open SGPT.Foundations.Envelope

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 0 f]
  [IsProjective f] [IsIntegral X]

local instance narrowSurjProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper

/-- Finite constancy follows DIRECTLY from the actual defining original GF-net predicate;
no approximation-sequence or finite-constancy certificate is supplied. -/
theorem exists_eq_const_of_isModuleTopologyPSH_of_dim_zero
    {Λ : RationalPicardSpace X} {ψ : BerkovichPoint f → EReal}
    (hψ : IsModuleTopologyPSH.{0} f Λ ψ) : ∃ c : ℝ, ψ = fun _ => (c : EReal) := by
  have := berkovichPoint_subsingleton_of_dim_zero f
  obtain ⟨v, hv⟩ := hψ.1
  have htop : ψ v ≠ ⊤ := IsPSHForNumericalTopology.ne_top f hψ v
  refine ⟨(ψ v).toReal, funext fun w => ?_⟩
  rw [Subsingleton.elim w v, EReal.coe_toReal htop hv]

variable (E : ClosedProjectiveEmbedding f)

local instance narrowSurjPointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance narrowSurjPointCharts : ChartedSpace (ComplexModel 0) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f 0
local instance narrowSurjPointManifold : IsComplexManifold 0 (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f 0

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel 0 (SchemeComplexPoint f))}

omit [IsIntegral X] in
/-- The actual original homogeneous metric translated by c has its ORIGINAL cutoff equal to c. -/
theorem component_max_translate_homogeneous_of_dim_zero (c : ℝ)
    (ω : SourceKahlerForm 0 (SchemeComplexPoint f)) :
    (((SourceNAPotential.homogeneous (SGPT.NPP.isThetaPSH_const_of_dim_zero θ 0)).translate c).component
      ω).val.max = c := by
  rw [← sourceNAPotentialCutoff_eq_component (sourceKahlerFormRepresentative ω),
    sourceNAPotentialCutoff_translate, sourceNAPotentialCutoff_homogeneous, zero_add]

/-- EVERY actual ORIGINAL psh function in dimension zero has an actual ORIGINAL NA preimage
on the FULL original Berkovich space. The preimage is manufactured internally. -/
theorem exists_original_naPotentialAnAt_eq_of_dim_zero
    {Λ : RationalPicardSpace X} {ψ : BerkovichPoint f → EReal}
    (hψ : IsModuleTopologyPSH.{0} f Λ ψ) (ω : SourceKahlerForm 0 (SchemeComplexPoint f)) :
    ∃ Γ : SourceNAPotential θ, ∀ v : BerkovichPoint f, naPotentialAnAt 0 E Γ ω v = ψ v := by
  obtain ⟨c, rfl⟩ := exists_eq_const_of_isModuleTopologyPSH_of_dim_zero f hψ
  refine ⟨(SourceNAPotential.homogeneous (SGPT.NPP.isThetaPSH_const_of_dim_zero θ 0)).translate c,
    fun v => ?_⟩
  rw [NANS.naPotentialAnAt_eq_of_dim_zero, component_max_translate_homogeneous_of_dim_zero f]

end SGPT.NAPotential.BJ.GfIm.RationalHull.NarrowDimensionZero
