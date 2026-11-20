import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalBaseScalarSections
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalDenominatorPullback

/-! Actual whole-source germ regularity of the manufactured scalar sections.
Blueprint: prime-nov16-analytic-normalization-original-source-scalar-regularity.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSourceScalarRegularity
open PrimeNov16AnalyticNormalizationLocalGraph
open SourceReducedComplexSpace
open PrimeNov16AnalyticNormalizationOriginalGraphPresentation
open PrimeNov16AnalyticNormalizationOriginalBaseScalarSections
open PrimeNov16AnalyticNormalizationOriginalGlobalSectionPullback
open PrimeNov16AnalyticNormalizationOriginalOpenTopGerms
open PrimeNov16AnalyticNormalizationOriginalDenominatorPullback
open NativeNov16SectionCoordinateMorphism
open HironakaActualAnalyticSubspace
open HironakaSmoothCentreRealDomainActualSheafStalk

theorem pulledBaseScalar_nonzero_every_germ {n m : ℕ} {Z : Set (ComplexModel n)}
    (d : GraphPresentation n Z) (P : Opens (ComplexModel m)) (C : Set P)
    (hC : IsComplexAnalyticSubset (n := m) C) (W : Opens (TopCat.of C))
    (f : coordinateSource P C hC W ⟶ d.target) (G : Set d.target.obj.left)
    (hIso : IsIsoOver f G) (hDense : Dense (f.hom.left.base ⁻¹' G))
    (F : ComplexModel n → ℂ) (hF : DifferentiableOn ℂ F (ballDomain (n := n) d.radius))
    (ht : ∀ b : d.target.obj.left,d.target.obj.left.presheaf.germ ⊤ b (by trivial)
      (baseScalarSection d F hF) ≠ 0) :
    ∀ p : C,∀ hp : p ∈ W,(actualSubspaceSheaf (n := m) C).presheaf.germ W p hp
      (pulledBaseScalar d P C hC W f F hF) ≠ 0 := by
  have hn := original_pullback_nonzero_every_stalk f G hIso hDense (baseScalarSection d F hF) ht
  intro p hp
  exact (openTopEquiv_germ_ne_zero_iff (sourceReducedComplexSpaceModel P C hC).obj.left W
    (pullTopRingHom f.hom.left (baseScalarSection d F hF)) (⟨p,hp⟩ : W)).mpr (hn ⟨p,hp⟩)

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSourceScalarRegularity
