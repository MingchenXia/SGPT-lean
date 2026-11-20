import SGPT.TestCurve.KFiltCurve

/-!
# The projective instance: scheme sections as a metered section ring

Sources `def:testcurve:L1134`, `ex:RWN` (chapter *Test curves*). Blueprint `claude-k-filt`, node
`claude-k-filt:scheme`.

The abstract construction of `ex:RWN` (`SGPT.TestCurve.KFilt.SectionMetric`,
`GradedFiltration.testCurvePotential`) is instantiated a second time by the scheme sections of
an integral smooth projective complex scheme with a structural smooth metric
(`schemeSectionMetric`). For a filtration `𝓕` of the projective formalization
(`SGPT.LineBundle.SectionFiltration`) and its image `GradedFiltration.ofScheme 𝓕`, the section
potentials, the obstacle, the test curve potentials `Γ^𝓕_τ` and the two clauses of `ex:RWN` of the
projective formalization (`SGPT.TestCurve.TestConf.RWNIModelClause`, `RWNMinimalClause`) are
literally those of the abstract construction (`sectionPotential_ofScheme`,
`testCurvePotential_ofScheme`, `iModelClause_ofScheme_iff`, `minimalClause_ofScheme_iff`, all by
`rfl`). Thus the projective and the compact Kähler formalizations of `ex:RWN` are two instances
of one construction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.KFilt

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set SGPT.Okounkov SGPT.LineBundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending

variable {X : Scheme} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  {E : ClosedProjectiveEmbedding f}

local instance kfiltSchemeTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance kfiltSchemeCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance kfiltSchemeManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

variable [IsSeparated f] [QuasiCompact f] [IsIntegral X] [Nonempty (SchemeComplexPoint f)]
variable {L : X.Modules} (H : SchemeLineBundleMetric f n E L) (a : LineBundleAtlas L)

/-- **The scheme section ring as a metered section ring**: `H⁰(X, L^k)` (`SectionSpace f L k`),
the section product, the squared norms `|s|²_{h^k}` of the structural metric `h = H` and
`θ = c₁(L, h) = H.curvature a`. -/
def schemeSectionMetric :
    SectionMetric n (SchemeComplexPoint f) (SectionSpace f L) (schemeMul f a) where
  θ := H.curvature a
  normSq k s p := H.sectionNormSq a k s p
  normSq_nonneg k s p := H.sectionNormSq_nonneg a k s p
  normSq_smul k c s p := H.sectionNormSq_smul a k c s p
  sqrt_normSq_add_le k s t p := map_add_le_add (Misc2RWN.pointSeminorm H a k p) s t
  normSq_mul k k' s t p := by
    change H.sectionNormSq a (k + k') (SectionSpace.mul f a k k' s t) p = _
    rw [SectionSpace.mul_apply]
    exact H.sectionNormSq_mul a k k' s t p
  continuous_normSq k s :=
    ProductTestForms.ChartSmooth.continuous (H.sectionNormSq_chartSmooth a k s)
  exists_normSq_ne_zero k s hs := by
    obtain ⟨q, -, hq⟩ := H.exists_sectionNormSq_ne_zero_of_isOpen a k s hs univ isOpen_univ
      univ_nonempty
    exact ⟨q, hq⟩
  mul_ne_zero k k' s t hs ht := SectionSpace.mul_ne_zero f a hs ht
  isThetaPsh k _ s hs := H.isThetaPshPotential_sectionLogNormSq a k s hs
  analyticType k s hs :=
    (H.sectionLogNormSq_hasAnalyticSingularities a k s hs).hasManifoldAnalyticSingularityType

variable {H a} (F : SectionFiltration f a)

/-- The section potentials `Γ^{𝓕,k}_τ` of the projective formalization are those of the abstract
construction. -/
theorem sectionPotential_ofScheme (k : ℕ) (τ : ℝ) :
    (GradedFiltration.ofScheme f a F).sectionPotential (schemeSectionMetric H a) k τ =
      F.sectionPotential H k τ := rfl

/-- The obstacles agree. -/
theorem obstacle_ofScheme (τ : ℝ) :
    (GradedFiltration.ofScheme f a F).obstacle (schemeSectionMetric H a) τ = F.obstacle H τ := rfl

/-- The test curve potentials `Γ^𝓕_τ` of the projective formalization are those of the abstract
construction. -/
theorem testCurvePotential_ofScheme (τ : ℝ) :
    (GradedFiltration.ofScheme f a F).testCurvePotential (schemeSectionMetric H a) τ =
      F.testCurvePotential H τ := rfl

/-- Clause (a) of `ex:RWN`: the projective and the abstract formulations agree. -/
theorem iModelClause_ofScheme_iff :
    (GradedFiltration.ofScheme f a F).IModelClause (schemeSectionMetric H a) ↔
      SGPT.TestCurve.TestConf.RWNIModelClause F H := Iff.rfl

/-- Clause (b) of `ex:RWN` (`eq:Gammatautheta`): the projective and the abstract formulations
agree. -/
theorem minimalClause_ofScheme_iff :
    (GradedFiltration.ofScheme f a F).MinimalClause (schemeSectionMetric H a) ↔
      SGPT.TestCurve.TestConf.RWNMinimalClause F H := Iff.rfl

end SGPT.TestCurve.KFilt
