import SGPT.BDivisor.BD7IntegralNumericalKleiman
import SGPT.BDivisor.BD7CompactCurveNormalizationGlobalLift
import SGPT.BDivisor.BD7CompactCurvePullbackPeriod
import SGPT.GAGA.OkoCloseDXMain

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.Okounkov Set
open SGPT.BDivisor.DFAlg SGPT.Projective.NumEq SGPT.Projective.NumEq.AlgebraicCurveDegree
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open scoped Manifold ContDiff BigOperators

local instance curveKleimanTopology {Y : Scheme.{0}} (g : Y ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g
local instance curveKleimanCharts {Y : Scheme.{0}} (g : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] :
    ChartedSpace (ComplexModel d) (SchemeComplexPoint g) := schemeAnalyticTNChartedSpace g d
local instance curveKleimanManifold {Y : Scheme.{0}} (g : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold d (SchemeComplexPoint g) := schemeAnalyticTN_isComplexManifold g d

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
    (m : ℕ) [SmoothOfRelativeDimension (m + 1) f] [IsSeparated f] [QuasiCompact f]

/-- All periods along a nonconstant compact holomorphic curve map are read by
the algebraic degree on its integral image, with one nonnegative factor. -/
theorem originalIntegralCurveNonnegativePeriodReadback_bd7 :
    OriginalIntegralCurveNonnegativePeriodReadback_bd7 f E m := by
  classical
  intro T _ _ _ _ _ κ g hg hconst
  let x₀ : T := Classical.choice (inferInstance : Nonempty T)
  have hnc : ∃ x y, g x ≠ g y := by
    by_contra hn
    apply hconst
    refine ⟨g x₀, funext fun x => ?_⟩
    by_contra h
    exact hn ⟨x, x₀, h⟩
  obtain ⟨I, hI, EI, hdim, himage, Y, hY, ρ, _, hsm, EY, ⟨j, hj⟩, L, hL, hfac⟩ :=
    exists_holomorphic_lift_to_normalization_of_compactCurve_bd7 f E (m + 1) g hg hnc
  letI := hI
  letI := hY
  let c := I.subschemeι ≫ f
  let C : OriginalIntegralCurveTest_bd7 f := {
    source := I.subscheme
    integral := hI
    structureMap := c
    inclusion := I.subschemeι
    closed := inferInstance
    over_base := rfl
    embedding := EI
    dimension := hdim }
  let ν := originalNormalizationMap C.source
  let fN := ν ≫ C.structureMap
  letI := originalNormalizationCurve_smoothOfRelativeDimension C.structureMap C.embedding C.dimension
  let EN := Classical.choice (normalizationProjectiveForCurves_bd7 C.structureMap C.embedding C.dimension)
  letI := EN.isSeparated
  letI := EN.quasiCompact
  letI : CompactSpace (SchemeComplexPoint fN) := EN.analyticCompact
  letI := hsm
  letI := EY.isSeparated
  letI := EY.quasiCompact
  have hjν : j.inv ≫ originalNormalizationMap I.subscheme = ρ := by
    rw [← hj, j.inv_hom_id_assoc]
  have hjinv : j.inv ≫ fN = ρ ≫ c := by
    simpa only [Category.assoc] using congrArg (fun u : Y ⟶ I.subscheme => u ≫ c) hjν
  let q : T → SchemeComplexPoint fN :=
    schemeComplexPointMap (ρ ≫ c) fN j.inv hjinv ∘ L
  have hq : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 1) ∞ q :=
    (SGPT.NAPotential.NativeSchemeImmersion.contMDiff_pointMap
      (ρ ≫ c) fN j.inv hjinv 1 1 ∞).comp hL
  have hNover : (ν ≫ C.inclusion) ≫ f = fN := by rw [Category.assoc, C.over_base]
  let k := schemeComplexPointMap fN f (ν ≫ C.inclusion) hNover
  have hk : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel (m + 1)) ∞ k :=
    SGPT.NAPotential.NativeSchemeImmersion.contMDiff_pointMap fN f (ν ≫ C.inclusion)
      hNover 1 (m + 1) ∞
  have hkq : k ∘ q = g := by
    funext x
    refine Eq.trans ?_ (hfac x)
    apply Subtype.ext
    let t : Spec (.of ℂ) ⟶ Y := (L x).val
    change ((t ≫ j.inv) ≫ ν ≫ I.subschemeι) = ((t ≫ ρ) ≫ I.subschemeι)
    simpa only [Category.assoc] using
      congrArg (fun u : Y ⟶ I.subscheme => t ≫ u ≫ I.subschemeι) hjν
  letI : Nonempty (SchemeComplexPoint fN) := ⟨q x₀⟩
  letI : ConnectedSpace (SchemeComplexPoint fN) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral fN EN 1
  let Apos := originalHyperplanePositiveLine fN 1 EN
  let κN : KahlerBackground 1 (SchemeComplexPoint fN) := ⟨Apos.curvature, Apos.positive⟩
  obtain ⟨a, ha, hperiod⟩ := exists_nonnegative_composedCurvePeriodFactor_bd7 κ κN hq hk
  let p : Spec (.of ℂ) := schemeComplexPointImage (𝟙 (Spec (.of ℂ))) ⟨𝟙 _, by simp⟩
  refine ⟨C, p, a, ?_, ha, ?_⟩
  · rw [← himage]
    change range (schemeComplexPointMap c f I.subschemeι rfl) =
      schemeNativeAlgebraicTrace f (range I.subschemeι)
    rw [closedImmersionComplexPointMap_range] <;> rfl
  · apply LinearMap.ext
    intro v
    let A : Fin v.support.card → IntrinsicLineBundle X := fun i => (v.support.equivFin.symm i).val
    let M := fun i => (A i).sheaf
    let b := fun i => (A i).atlas
    let H := fun i => schemeLineBundleMetric f (m + 1) E (b i)
    let r := fun i => v (A i)
    let β : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f) :=
      ∑ i, r i • (H i).curvature (b i)
    have hread : cartierChern_bd7 f E (m + 1) v = RealBottChern.ofRepresentative β := by
      have hs := originalLinearCombination_eq_supportFinSum v (fun B : IntrinsicLineBundle X =>
        RealBottChern.ofRepresentative ((schemeLineBundleMetric f (m + 1) E B.atlas).curvature B.atlas))
      change cartierChern_bd7 f E (m + 1) v =
        ∑ i, r i • RealBottChern.ofRepresentative ((H i).curvature (b i)) at hs
      refine hs.trans ?_
      change _ = RealBottChern.ofRepresentativeLinearMap (∑ i, r i • (H i).curvature (b i))
      rw [map_sum]
      simp only [map_smul, RealBottChern.ofRepresentativeLinearMap]
      rfl
    have hdegree : originalIntegralCurveDegreeLinear_bd7 f E C p v = degreeAlong κN hk β := by
      have hr : originalIntegralCurveDegreeLinear_bd7 f E C p v =
          ∑ i, r i * ((originalIntegralCurveLineDegree_bd7 C.structureMap C.embedding C.dimension
            (matePullbackAtlas C.inclusion (b i)) p : ℤ) : ℝ) := by
        simpa only [originalIntegralCurveDegreeLinear_bd7, smul_eq_mul, A, b, r] using
          originalLinearCombination_eq_supportFinSum v (fun B : IntrinsicLineBundle X =>
            ((originalIntegralCurveLineDegree_bd7 C.structureMap C.embedding C.dimension
              (matePullbackAtlas C.inclusion B.atlas) p : ℤ) : ℝ))
      exact hr.trans (originalWeightedIntegralCurveDegrees_eq_normalizedDegreeAlong_bd7
        f (m + 1) E C.inclusion C.structureMap C.over_base C.embedding C.dimension EN M b H r p κN)
    have hh : degreeAlong κ hg β = a * degreeAlong κN hk β := by
      have htransport (u u' : T → SchemeComplexPoint f) (he : u = u')
          (hu : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel (m + 1)) ∞ u)
          (hu' : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel (m + 1)) ∞ u') :
          degreeAlong κ hu β = degreeAlong κ hu' β := by
        subst u'
        rfl
      exact (htransport g (k ∘ q) hkq.symm hg (hk.comp hq)).trans (hperiod β)
    change classDegreeAlong κ hg (cartierChern_bd7 f E (m + 1) v) =
      a * originalIntegralCurveDegreeLinear_bd7 f E C p v
    rw [hread, classDegreeAlong_ofRepresentative, hdegree]
    exact hh

/-- The independent algebraic degree cone on the actual all-integral numerical
quotient agrees with native analytic nefness. -/
theorem originalIntegralDegreeNefCone_iff_nativeClassNef_bd7
    [IsIntegral X] [ConnectedSpace (SchemeComplexPoint f)]
    (omega : KahlerBackground (m + 1) (SchemeComplexPoint f))
    (α : OriginalIntegralCurveDegreeQuotient_bd7 f E) :
    α ∈ originalIntegralDegreeNefCone_bd7 f E ↔
      ClassNefWithRespectTo omega
        (originalIntegralQuotientChern_bd7 f E (m + 1) normalizationProjectiveForCurves_bd7 α) :=
  originalIntegralDegreeNefCone_iff_nativeClassNef_of_nonnegative_projection_bd7 f E m
    normalizationProjectiveForCurves_bd7 (originalIntegralCurveNonnegativePeriodReadback_bd7 f E m) omega α

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
