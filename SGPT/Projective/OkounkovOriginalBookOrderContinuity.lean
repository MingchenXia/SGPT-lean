import SGPT.Projective.OkounkovOriginalBookPartial
import SGPT.Okounkov.ValGenCont
import SGPT.Foundations.Analysis.Pending.DimZeroKahler

/-! Entire original I-order comparison and dS continuity, SAME own-body cone chosen BEFORE potentials.
Blueprint: okounkov-original-book-order-continuity.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending.DiagonalMass SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology
open SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDistance
open SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup
open SGPT.AlmostSemigroup.Okounkov SGPT.AlmostSemigroup.Class
open scoped Topology ENNReal
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
  [Nonempty (SchemeComplexPoint f)]
local instance originalBookOrderContinuityTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance originalBookOrderContinuityCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance originalBookOrderContinuityManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n
variable {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
  (hbig : SGPT.LineBundle.IsBig f L n)

include hbig in
/-- ACTUAL original class bigness from SAME original big line/metric, INCLUDING true dimension zero. -/
theorem original_isBigClass_of_isBig_allDimensions :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    IsBigClass (RealBottChern.ofRepresentative (H.curvature a)) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  obtain ⟨Y,hY⟩ := exists_original_smoothFlag_allDimensions f n E
  cases n with
  | succ m => exact SGPT.GAGA.OkoClose.isBigClass_of_isBig f E Y hY a H hbig
  | zero =>
    exact DimZeroKahler.isBigClass_of_dim_zero rfl
      (schemeProjectiveTNKahlerBackground f 0 E) (H.curvature a)

variable (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
  (hv : Function.Surjective v)
include E hbig hv

/-- ENTIRE printed I-order and dS-continuity sources, SAME actual own-body cone fixed before ALL potentials. -/
theorem exists_common_ownBody_order_continuous_partialBody_allDimensions :
    haveI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ∃ (hclass : IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
      (hKc : IsCompact (centreOkounkovBody f v a)) (hKv : Convex ℝ (centreOkounkovBody f v a)),
      (∀ (φ ψ : SchemeComplexPoint f → EReal)
        (hφ : IsThetaPshPotential (H.curvature a).val φ)
        (hψ : IsThetaPshPotential (H.curvature a).val ψ),
        HasPositivePotentialMass (H.curvature a) φ hφ →
        HasPositivePotentialMass (H.curvature a) ψ hψ →
        IOrderOnManifold (n:=n) φ ψ →
        ValGen.partialBody f n E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ ⊆
          ValGen.partialBody f n E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) ψ ∧
        ValGen.partialBody f n E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ ⊆
          (EuclideanSpace.equiv (Fin n) ℝ).symm '' centreOkounkovBody f v a) ∧
      (haveI : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E n
       letI : TopologicalSpace (ThetaPshL1 (H.curvature a).val) :=
         (singularityPseudoMetricSpace (schemeProjectiveTNKahlerBackground f n E)
           (H.curvature a) hclass).toUniformSpace.toTopologicalSpace
       ∃ G : {w : ThetaPshL1 (H.curvature a).val //
          HasPositivePotentialMass (H.curvature a) w.val w.property} → ConvexBody (EuclideanSpace ℝ (Fin n)),
         Continuous G ∧ ∀ w, (G w : Set (EuclideanSpace ℝ (Fin n))) =
           ValGen.partialBody f n E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) w.val.val) := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E n
  let c := valuationCenter f v
  obtain ⟨Y,hY⟩ := exists_original_smoothFlag_allDimensions f n E
  have hclass := original_isBigClass_of_isBig_allDimensions f n E a H hbig
  obtain ⟨hKc,hKv,hinter,hSL,hfull⟩ :=
    sectionSemigroup_mem_ownBody_fullSemigroupLocus_allDimensions f a n E hbig v hv c
  let C := SGPT.GAGA.OkoClose.coneOver _ hKc hKv
  have hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤ := hfull.2
  refine ⟨hclass,hKc,hKv,?_,?_⟩
  · intro φ ψ hφ hψ hmφ hmψ hI
    cases n with
    | succ m =>
      have hΓφ := ValGen.multiplierConeSubset_mem_almostSemigroupLocus_of_mass
        f E Y hY a H c v hSL hG hφ hmφ
      have hΓψ := ValGen.multiplierConeSubset_mem_almostSemigroupLocus_of_mass
        f E Y hY a H c v hSL hG hψ hmψ
      exact ⟨ValGen.partialBody_mono a (fun k hk => multiplierIdeal_le_of_iOrderOnManifold hI
        (by exact_mod_cast hk)) ⟨_,hΓφ⟩ ⟨_,hΓψ⟩,
        ValGen.partialBody_subset_okounkovBody a hSL hG ⟨_,hΓφ⟩⟩
    | zero =>
      have h1 := PobDimZero.mem_coneOver_zero_one hKc hKv (hinter.mono interior_subset)
      have hφ0 := PobDimZero.valuation_partialBody_eq_univ f E Y hY a c v hφ.quasiPshPotential C h1
      have hψ0 := PobDimZero.valuation_partialBody_eq_univ f E Y hY a c v hψ.quasiPshPotential C h1
      have hK0 := PobDimZero.valuation_okounkovBody_eq_univ f E Y hY a c v
      change ValGen.partialBody f 0 E v c a C φ ⊆ ValGen.partialBody f 0 E v c a C ψ ∧
        ValGen.partialBody f 0 E v c a C φ ⊆ (EuclideanSpace.equiv (Fin 0) ℝ).symm '' okounkovBody v c a
      rw [hφ0,hψ0,hK0]
      refine ⟨Subset.rfl,?_⟩
      intro z _
      exact ⟨(EuclideanSpace.equiv (Fin 0) ℝ) z,trivial,
        (EuclideanSpace.equiv (Fin 0) ℝ).symm_apply_apply z⟩
  · let : TopologicalSpace (ThetaPshL1 (H.curvature a).val) :=
      (singularityPseudoMetricSpace (schemeProjectiveTNKahlerBackground f n E)
        (H.curvature a) hclass).toUniformSpace.toTopologicalSpace
    cases n with
    | succ m => exact ValGen.exists_continuous_partialBody f E Y hY a H c v hclass hSL hG
    | zero =>
      have h1 := PobDimZero.mem_coneOver_zero_one hKc hKv (hinter.mono interior_subset)
      refine ⟨fun _ => ⟨univ,convex_univ,isCompact_univ,univ_nonempty⟩,continuous_const,?_⟩
      intro w
      exact (PobDimZero.valuation_partialBody_eq_univ f E Y hY a c v w.val.property.quasiPshPotential C h1).symm

end SGPT.Okounkov.OriginalBook
