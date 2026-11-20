import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNormalSourceSelectors
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalDenominatorPullback
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGlobalSectionFunctor
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalOpenTopGerms

/-! Actual whole normalizer good geometry manufactures denominator regularity on its true original source charts.
Blueprint: prime-nov16-analytic-normalization-original-chart-denominator.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalChartDenominator
open NativeNov16SectionCoordinateMorphism NativeNov16PartialBaseScalarSections
open PrimeNov16AnalyticNormalizationOriginalNormalSourceSelectors
open PrimeNov16AnalyticNormalizationOriginalGlobalSectionPullback
open PrimeNov16AnalyticNormalizationOriginalGlobalSectionFunctor
open PrimeNov16AnalyticNormalizationOriginalOpenTopGerms
open PrimeNov16AnalyticNormalizationOriginalDenominatorPullback
open HironakaActualAnalyticSubspace
open SourceReducedComplexSpace

theorem actual_chart_partial_pullback_nonzero {m n : ℕ}
    (Ps : Opens (ComplexModel m)) (Cs : Set Ps) (hCs : IsComplexAnalyticSubset (n := m) Cs)
    (Ws : Opens (TopCat.of Cs)) (Pt : Opens (ComplexModel n)) (Ct : Set Pt)
    (hCt : IsComplexAnalyticSubset (n := n) Ct) (Ut : Opens (TopCat.of Ct))
    {Y : SourceReducedComplexSpace}
    (f : Y ⟶ coordinateSource Pt Ct hCt Ut) (G : Set (coordinateSource Pt Ct hCt Ut).obj.left)
    (hIso : IsIsoOver f G) (hDense : Dense (f.hom.left.base ⁻¹' G))
    (j : coordinateSource Ps Cs hCs Ws ⟶ Y) [LocallyRingedSpace.IsOpenImmersion j.hom.left]
    (Ω : Opens (ComplexModel n)) (Q : ComplexModel n → ℂ) (hQ : DifferentiableOn ℂ Q Ω)
    (hland : ∀ b : Ct,b ∈ Ut → b.val.val ∈ Ω)
    (ht : ∀ b (hb : b ∈ Ut),(actualSubspaceSheaf (n := n) Ct).presheaf.germ Ut b hb
      (scalarSection Pt Ct Ut Ω Q hQ hland) ≠ 0) :
    ∀ x (hx : x ∈ Ws),(actualSubspaceSheaf (n := m) Cs).presheaf.germ Ws x hx
      (pulledPartialScalar Ps Cs hCs Ws Pt Ct hCt Ut (j ≫ f) Ω Q hQ hland) ≠ 0 := by
  let A := (sourceReducedComplexSpaceModel Ps Cs hCs).obj.left
  let B := (sourceReducedComplexSpaceModel Pt Ct hCt).obj.left
  let s := scalarSection Pt Ct Ut Ω Q hQ hland
  let t := (openTopEquiv B Ut).symm s
  have htTop : ∀ b : (coordinateSource Pt Ct hCt Ut).obj.left,
      (coordinateSource Pt Ct hCt Ut).obj.left.presheaf.germ ⊤ b (by trivial) t ≠ 0 := by
    intro b
    apply (openTopEquiv_germ_ne_zero_iff B Ut t b).mp
    have hn : B.presheaf.germ Ut b.val b.property s ≠ 0 := ht b.val b.property
    simpa only [t,RingEquiv.apply_symm_apply] using hn
  have hY := original_pullback_nonzero_every_stalk f G hIso hDense t htTop
  intro x hx
  change A.presheaf.germ Ws x hx
    (openTopEquiv A Ws (pullTopRingHom (j.hom.left ≫ f.hom.left) t)) ≠ 0
  apply (openTopEquiv_germ_ne_zero_iff A Ws _ (⟨x,hx⟩ : Ws)).mpr
  rw [pullTop_comp]
  exact pullTop_nonzero_of_openImmersion j.hom.left (pullTopRingHom f.hom.left t) hY ⟨x,hx⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalChartDenominator
