import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalProperRestriction
import SGPT.Unibranch.OriginalLocalStrictWindowRegularity

/-! Actual full original inverse under internally manufactured proper open restriction.
Blueprint: prime-nov16-analytic-normalization-original-restricted-inverse.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalRestrictedInverse
open SourceReducedComplexSpace
open PrimeNov16AnalyticNormalizationOriginalProperRestriction

theorem restrictedMap_isIsoOver {Y X : SourceReducedComplexSpace} (f : Y ⟶ X)
    (hf : IsProperMap f.hom.left.base) (U : Opens X.obj.left) [ParacompactSpace U]
    (G : Set X.obj.left) (hIso : IsIsoOver f G) :
    IsIsoOver (restrictedMap f hf U) ((baseInclusion U).hom.left.base ⁻¹' G) := by
  apply OriginalLocalStrictWindowRegularity.isIsoOver_of_open_square f
    (restrictedMap f hf U) (sourceInclusion f hf U) (baseInclusion U)
    (sourceInclusion_isOpenImmersion f hf U) (baseInclusion_isOpenImmersion U)
    (restrictedMap_square f hf U) _ G hIso
  change range (Subtype.val : sourceOpen f U → Y.obj.left)=
    f.hom.left.base ⁻¹' range (Subtype.val : U → X.obj.left)
  ext p
  constructor
  · rintro ⟨v,rfl⟩
    exact ⟨⟨f.hom.left.base v.val,v.property⟩,rfl⟩
  · rintro ⟨u,hu⟩
    have hpU : f.hom.left.base p ∈ U := hu ▸ u.property
    exact ⟨⟨p,hpU⟩,rfl⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalRestrictedInverse
