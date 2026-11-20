import SGPT.Projective.OkounkovOriginalPositiveMassConcavity
import SGPT.NAPotential.FSPosKahler

/-! ENTIRE printed thm:concOko, actual original positive NONPLURIPOLAR mass and all dimensions.
Blueprint: okounkov-original-book-concavity.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Foundations.Analysis.Pending.EndpointMixedMassConvexCombination
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup SGPT.NAPotential.FSPos
open scoped Topology Pointwise ENNReal
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    (n : ℕ) [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
    [Nonempty (SchemeComplexPoint f)]
local instance bookConcavityTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance bookConcavityCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance bookConcavityManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

theorem original_partialBody_real_concavity_allDimensions {L : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (hv : Function.Surjective v)
    {φ ψ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated;letI := E.quasiCompact;IsThetaPshPotential (H.curvature a).val φ)
    (hψ : letI := E.isSeparated;letI := E.quasiCompact;IsThetaPshPotential (H.curvature a).val ψ)
    {t : ℝ} (ht0 : 0<t) (ht1 : t<1) :
    letI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    HasPositivePotentialMass (H.curvature a) φ hφ →
    HasPositivePotentialMass (H.curvature a) ψ hψ →
    ∃ (hKc : IsCompact (centreOkounkovBody f v a)) (hKv : Convex ℝ (centreOkounkovBody f v a)),
      t • ValGen.partialBody f n E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ +
        (1-t) • ValGen.partialBody f n E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) ψ ⊆
      ValGen.partialBody f n E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) (convexComb t φ ψ) := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E n
  intro hmφ hmψ
  cases n with
  | succ m =>
    let P : SGPT.LineBundle.AmplePolarization f (hyperplaneBundle E) := {
      power := 1
      power_pos := one_pos
      ambientDimension := E.ambientDimension
      map := E.map
      isClosedImmersion := E.closedImmersion
      over_base := E.over_base
      iso := bundleTensorLeftUnitIso (hyperplaneBundle E) }
    exact original_partialBody_real_concavity_positive_mass f E a H (hyperplaneAtlas E)
      P (fubiniStudyMetric f E (m+1))
      (fubiniStudy_isKahler f E (m+1)) v hv hφ hψ ht0 ht1 hmφ hmψ
  | zero =>
    let c := valuationCenter f v
    have hpos := hmφ.trans_le
      (PartialBody.diagonalPotentialMass_le_iVolume (schemeProjectiveTNKahlerBackground f 0 E) hφ)
    have hbig := original_isBig_of_positive_iVolume_allDimensions f 0 E a H hφ hpos
    obtain ⟨hKc,hKv,hinter,_,_⟩ := sectionSemigroup_mem_ownBody_fullSemigroupLocus_allDimensions
      f a 0 E hbig v hv c
    let C := SGPT.GAGA.OkoClose.coneOver _ hKc hKv
    obtain ⟨Y,hY⟩ := exists_original_smoothFlag_allDimensions f 0 E
    have h1 := PobDimZero.mem_coneOver_zero_one hKc hKv (hinter.mono interior_subset)
    have hχ := isThetaPshPotential_convexComb_closed hφ hψ ht0.le ht1.le
    have hφ0 := PobDimZero.valuation_partialBody_eq_univ f E Y hY a c v hφ.quasiPshPotential C h1
    have hψ0 := PobDimZero.valuation_partialBody_eq_univ f E Y hY a c v hψ.quasiPshPotential C h1
    have hχ0 := PobDimZero.valuation_partialBody_eq_univ f E Y hY a c v hχ.quasiPshPotential C h1
    refine ⟨hKc,hKv,?_⟩
    change t • ValGen.partialBody f 0 E v c a C φ+(1-t) • ValGen.partialBody f 0 E v c a C ψ⊆
      ValGen.partialBody f 0 E v c a C (convexComb t φ ψ)
    rw [hφ0,hψ0,hχ0]
    exact subset_univ _
end SGPT.Okounkov.OriginalBook
