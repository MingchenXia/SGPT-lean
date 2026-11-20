import SGPT.Projective.AlgebraicSectionZeroStalk

/-! FULL actual original zero-subscheme local-ring lengths equal the SAME
original section's FULL analytic normal orders; no quotient/length input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.NAPotential.FSPos
open DemaillyApproximantDivisorialLelong FixedGermNormalOrder

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
  [SmoothOfRelativeDimension 1 f]

local instance zeroLengthTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance zeroLengthCharts : ChartedSpace (ComplexModel 1) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f 1

/-- The original zero scheme's ACTUAL full local-ring length is the SAME
analytic zero order, at every closed original image point. All original
atlas frame germs and all multiplicities are retained and manufactured. -/
theorem exists_zeroStalk_length_eq_normalOrder (E : ClosedProjectiveEmbedding f)
    {L : X.Modules} (a : LineBundleAtlas L) (s : Γ(L, ⊤)) (hs : s ≠ 0)
    (z : sectionZeroSubscheme a s) (hz : IsClosed ({sectionZeroι a s z} : Set X)) :
    let := E.isSeparated
    let := E.quasiCompact
    let : ChartedSpace (ComplexModel (0 + 1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (0 + 1)
    let : IsComplexManifold (0 + 1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (0 + 1)
    ∃ (y : SchemeComplexPoint f) (himage : schemeComplexPointImage f y = sectionZeroι a s z),
      ∃ Ψ : DivisorFlattening (m := 0)
          (schemeNativeAlgebraicTrace f (closure {sectionZeroι a s z})) y,
        ∀ (i : a.I) (hi : sectionZeroι a s z ∈ a.opens i),
          Module.length ((sectionZeroSubscheme a s).presheaf.stalk z)
            ((sectionZeroSubscheme a s).presheaf.stalk z) =
          normalOrder Ψ (stalkToModel f 1 y
            (sectionStalkCoefficient a s i (schemeComplexPointImage f y) (himage.symm ▸ hi))) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : ChartedSpace (ComplexModel (0 + 1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (0 + 1)
  let : IsComplexManifold (0 + 1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (0 + 1)
  dsimp only
  obtain ⟨y, himage, Ψ, horder⟩ := exists_section_length_eq_normalOrder f E a s hs (sectionZeroι a s z) hz
  refine ⟨y, himage, Ψ, fun i hi => ?_⟩
  let hy : schemeComplexPointImage f y ∈ a.opens i := himage.symm ▸ hi
  have hpoints : (⟨schemeComplexPointImage f y, hy⟩ : a.opens i) = ⟨sectionZeroι a s z, hi⟩ :=
    Subtype.ext himage
  have hlengths := congrArg (fun p : a.opens i =>
    Module.length (X.presheaf.stalk p.1)
      ((X.presheaf.stalk p.1) ⧸ Ideal.span {sectionStalkCoefficient a s i p.1 p.2})) hpoints
  exact (sectionZeroStalk_length_eq_principalLength a s z i hi).trans
    (hlengths.symm.trans (horder i hy))

end SGPT.Projective.NumEq.AlgebraicCurveDegree
