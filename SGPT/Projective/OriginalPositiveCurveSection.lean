import SGPT.Projective.OriginalAlgebraicRegularCut
import SGPT.Projective.OriginalSectionOpenZeroGerm
import SGPT.Projective.WholeCurveZeroArtinian
import SGPT.GAGA.H0LRegular

/-! The SAME actual original regular section is nonzero on EVERY actual
original curve component, proved from genuine original stalk derivations.
Blueprint: original-positive-curve-section.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace
open SGPT.Okounkov SGPT.NAPotential.GAGAMult
open SGPT.Projective.NumEq.AlgebraicCurveDegree
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f]

local instance positiveCurveTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance positiveCurveCharts (d : ℕ) [SmoothOfRelativeDimension d f] :
    ChartedSpace (ComplexModel d) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f d
local instance positiveCurveManifold (d : ℕ) [SmoothOfRelativeDimension d f] :
    IsComplexManifold d (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f d

/-- Actual SAME-cut original derivations prove nonzero ordinary section on EACH original component. -/
theorem originalRegularCut_sectionNonzeroOnComponents (P : OriginalPositiveLine f 1 E)
    (C : OriginalRegularCut f 0 E P) : SectionNonzeroOnComponents f E C.originalSection := by
  let : LocallyOfFiniteType f := E.locallyOfFiniteType
  intro F hs
  let U := smoothProjectiveComponentOpen f 1 E F.val F.property
  obtain ⟨x, hx⟩ := F.property.1.nonempty
  have hxU : x ∈ U := hx
  obtain ⟨p, hpU, _⟩ := SGPT.GAGA.H0L.exists_specializes_schemeComplexPoint f hxU
  obtain ⟨j, hj⟩ := P.atlas.covers (schemeComplexPointImage f p)
  have hg : X.presheaf.germ (P.atlas.opens j) (schemeComplexPointImage f p) hj
      (algCoef (P.atlas.frame j) C.nativeCut.power C.originalSection) = 0 :=
    originalSection_coefficientGerm_eq_zero_of_open_pull_zero U C.originalSection hs
      ((P.atlas.frame j).tensorPower C.nativeCut.power) (schemeComplexPointImage f p) hpU hj
  have hvalue : schemeOpenRegularFunction f 1 E (P.atlas.opens j)
      (algCoef (P.atlas.frame j) C.nativeCut.power C.originalSection) p = 0 := by
    rw [schemeOpenRegularFunction_apply f 1 E (P.atlas.opens j) _ p hj, hg, map_zero, map_zero]
  have hsupp : schemeComplexPointImage f p ∈
      (sectionZeroIdealSheaf (P.atlas.tensorPower C.nativeCut.power) C.originalSection).support :=
    (sectionZero_support_iff_coefficient_zero f 1 E (P.atlas.tensorPower C.nativeCut.power)
      C.originalSection ((P.atlas.frame j).tensorPower C.nativeCut.power) p hj).mpr hvalue
  have hxD := (regularCut_support_iff_member f 1 E P.atlas P.metric P.positive
    C.nativeCut C.originalSection C.coefficient p).mp hsupp
  obtain ⟨δ, hδ⟩ := regularCut_stalk_derivation f 1 E P.atlas P.metric P.positive
    C.nativeCut C.originalSection C.coefficient j p hj hxD
  exact hδ (hg ▸ map_zero δ)

/-- Ordinary actual original positive-power sections are produced, with ALL components nonzero. -/
theorem exists_originalPositivePower_curveSection (P : OriginalPositiveLine f 1 E) :
    ∃ d : ℕ, 0 < d ∧ ∃ s : bundlePowerGlobalSections P.sheaf d,
      SectionNonzeroOnComponents f E s := by
  obtain ⟨C⟩ := exists_originalRegularCut f 0 E P
  exact ⟨C.nativeCut.power, C.nativeCut.power_pos, C.originalSection,
    originalRegularCut_sectionNonzeroOnComponents f E P C⟩

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
