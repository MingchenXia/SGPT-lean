import SGPT.BDivisor.BD7IntegralNumericalNef
import SGPT.BDivisor.BD2Kleiman
import SGPT.Okounkov.SchemeNativeAnalyticSubset

/-! The projection formula for the image of a holomorphic curve supplies the
exact comparison needed to apply analytic Kleiman to the independent
all-integral degree quotient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.BDivisor.DFAlg SGPT.Projective.NumEq
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open scoped Manifold ContDiff

local instance integralKleimanTopology {Y : Scheme.{0}} (g : Y ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g
local instance integralKleimanCharts {Y : Scheme.{0}} (g : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] :
    ChartedSpace (ComplexModel d) (SchemeComplexPoint g) := schemeAnalyticTNChartedSpace g d
local instance integralKleimanManifold {Y : Scheme.{0}} (g : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold d (SchemeComplexPoint g) := schemeAnalyticTN_isComplexManifold g d

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
    (m : ℕ) [SmoothOfRelativeDimension (m + 1) f] [IsSeparated f] [QuasiCompact f]

private theorem degreeAlong_const_bd7 {T : Type} [TopologicalSpace T]
    [ChartedSpace (ComplexModel 1) T] [IsComplexManifold 1 T] [CompactSpace T]
    (κ : KahlerBackground 1 T) (x : SchemeComplexPoint f)
    (θ : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f)) :
    degreeAlong κ (contMDiff_const (c := x)) θ = 0 := by
  let : MeasurableSpace T := borel T
  let : BorelSpace T := ⟨rfl⟩
  have hpb : ClosedRealOneOneForm.pullback
      (contMDiff_const (c := x)) θ = (0 : ClosedRealOneOneForm 1 T) := by
    apply ClosedRealOneOneForm.ext
    intro e z
    ext w
    let d := complexChartAt (n := m + 1) x
    change (SmoothRealForm.chartPullbackCoeff θ.val (fun _ : T => x) e d z) w = 0
    have hconst : coordinateMap (fun _ : T => x) e d = fun _ => d.val x := rfl
    rw [SmoothRealForm.chartPullbackCoeff, hconst, fderiv_const_apply,
      ContinuousAlternatingMap.compContinuousLinearMap_apply]
    have hzero : (⇑(0 : ComplexModel 1 →L[ℝ] ComplexModel (m + 1)) ∘ w) = 0 := by
      funext j
      simp
    rw [hzero]
    exact (θ.val.coeff d (d.val x)).map_zero
  unfold degreeAlong
  rw [hpb]
  have hz := slotIntegral_update_zero κ (fun _ => (0 : ClosedRealOneOneForm 1 T)) 0
  simpa using hz

/-- The needed image-curve projection formula, stated as an equality of linear
functionals on the original Cartier combinations. The nonzero case is the
degree on the actual integral image multiplied by the mapping degree. -/
def OriginalIntegralCurvePeriodReadback_bd7 : Prop :=
  ∀ (T : Type) [TopologicalSpace T] [ChartedSpace (ComplexModel 1) T]
    [IsComplexManifold 1 T] [CompactSpace T] [ConnectedSpace T]
    (κ : KahlerBackground 1 T) (g : T → SchemeComplexPoint f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel (m + 1)) ∞ g),
    (¬ ∃ x : SchemeComplexPoint f, g = (fun _ : T => x)) →
    ∃ (C : OriginalIntegralCurveTest_bd7 f) (p : Spec (.of ℂ)) (a : ℝ),
      Set.range g = schemeNativeAlgebraicTrace f (Set.range C.inclusion) ∧ 0 < a ∧
      (classDegreeAlong κ hg).comp (cartierChern_bd7 f E (m + 1)) =
        a • originalIntegralCurveDegreeLinear_bd7 f E C p

/-- The needed image-curve projection formula, stated as an equality of linear
functionals on the original Cartier combinations, with a nonnegative factor. -/
def OriginalIntegralCurveNonnegativePeriodReadback_bd7 : Prop :=
  ∀ (T : Type) [TopologicalSpace T] [ChartedSpace (ComplexModel 1) T]
    [IsComplexManifold 1 T] [CompactSpace T] [ConnectedSpace T]
    (κ : KahlerBackground 1 T) (g : T → SchemeComplexPoint f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel (m + 1)) ∞ g),
    (¬ ∃ x : SchemeComplexPoint f, g = (fun _ : T => x)) →
    ∃ (C : OriginalIntegralCurveTest_bd7 f) (p : Spec (.of ℂ)) (a : ℝ),
      Set.range g = schemeNativeAlgebraicTrace f (Set.range C.inclusion) ∧ 0 ≤ a ∧
      (classDegreeAlong κ hg).comp (cartierChern_bd7 f E (m + 1)) =
        a • originalIntegralCurveDegreeLinear_bd7 f E C p

theorem originalIntegralCurveNonnegativePeriodReadback_of_positive_bd7
    (hperiod : OriginalIntegralCurvePeriodReadback_bd7 f E m) :
    OriginalIntegralCurveNonnegativePeriodReadback_bd7 f E m := by
  intro T _ _ _ _ _ κ g hg hconst
  obtain ⟨C, p, a, htrace, ha, hread⟩ := hperiod T κ g hg hconst
  exact ⟨C, p, a, htrace, ha.le, hread⟩

variable [ConnectedSpace (SchemeComplexPoint f)]

/-- The algebraic cone tests all the original integral images. The projection
formula transfers their inequalities to all holomorphic curve maps. -/
theorem originalIntegralQuotientChern_isCurveNef_of_nonnegative_projection_bd7
    (hprojective : NormalizationProjectiveForCurves)
    (hperiod : OriginalIntegralCurveNonnegativePeriodReadback_bd7 f E m)
    (α : OriginalIntegralCurveDegreeQuotient_bd7 f E)
    (hα : α ∈ originalIntegralDegreeNefCone_bd7 f E) :
    IsCurveNef (originalIntegralQuotientChern_bd7 f E (m + 1) hprojective α) := by
  obtain ⟨v, rfl⟩ := (originalIntegralCurveDegreeRelations_bd7 f E).mkQ_surjective α
  intro T _ _ _ _ _ κ g hg
  rw [originalIntegralQuotientChern_mkQ_bd7]
  by_cases hconst : ∃ x : SchemeComplexPoint f, g = (fun _ : T => x)
  · obtain ⟨x, rfl⟩ := hconst
    have hzero (γ : RealBottChern (m + 1) (SchemeComplexPoint f)) :
        classDegreeAlong κ hg γ = 0 := by
      induction γ using Quotient.inductionOn with
      | h θ => exact degreeAlong_const_bd7 f m κ x θ
    exact le_of_eq (hzero _).symm
  · change 0 ≤ ((classDegreeAlong κ hg).comp (cartierChern_bd7 f E (m + 1))) v
    obtain ⟨C, p, a, _, ha, heq⟩ := hperiod T κ g hg hconst
    rw [heq]
    have hd := (mem_originalIntegralDegreeNefCone_bd7 f E _).mp hα C p
    rw [originalIntegralCurveDegreeOnQuotient_mkQ_bd7] at hd
    change 0 ≤ a * originalIntegralCurveDegreeLinear_bd7 f E C p v
    exact mul_nonneg ha hd

/-- Analytic nefness agrees with the independently defined all-integral degree
cone once the image-curve projection formula is available. -/
theorem originalIntegralDegreeNefCone_iff_nativeClassNef_of_nonnegative_projection_bd7
    [IsIntegral X]
    (hprojective : NormalizationProjectiveForCurves)
    (hperiod : OriginalIntegralCurveNonnegativePeriodReadback_bd7 f E m)
    (omega : KahlerBackground (m + 1) (SchemeComplexPoint f))
    (α : OriginalIntegralCurveDegreeQuotient_bd7 f E) :
    α ∈ originalIntegralDegreeNefCone_bd7 f E ↔
      ClassNefWithRespectTo omega (originalIntegralQuotientChern_bd7 f E (m + 1) hprojective α) := by
  constructor
  · intro hα
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let A := originalHyperplanePositiveLine f (m + 1) E
    have hY : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) (SchemeComplexPoint f) :=
      SGPT.BDivisor.NSKodaira.isProjectiveManifold_iff_exists_kahler_mem_neronSeveri.mpr
        ⟨A.curvature, A.positive, originalPositiveLine_chern_mem_neronSeveri f (m + 1) E A⟩
    apply SGPT.BDivisor.Kleiman.classNef_of_isCurveNef hY omega
    · obtain ⟨v, rfl⟩ := (originalIntegralCurveDegreeRelations_bd7 f E).mkQ_surjective α
      rw [originalIntegralQuotientChern_mkQ_bd7,
        SGPT.BDivisor.BD6.neronSeveri_eq_span_algChern f E m, ← Finsupp.range_linearCombination]
      exact ⟨v, rfl⟩
    · exact originalIntegralQuotientChern_isCurveNef_of_nonnegative_projection_bd7 f E m hprojective hperiod α hα
  · exact originalIntegralDegreeNefCone_of_nativeClassNef_bd7 f E (m + 1) hprojective omega α

/-- A positive projection factor transfers the algebraic degree inequalities to all
holomorphic curve maps. -/
theorem originalIntegralQuotientChern_isCurveNef_of_projection_bd7
    (hprojective : NormalizationProjectiveForCurves)
    (hperiod : OriginalIntegralCurvePeriodReadback_bd7 f E m)
    (α : OriginalIntegralCurveDegreeQuotient_bd7 f E)
    (hα : α ∈ originalIntegralDegreeNefCone_bd7 f E) :
    IsCurveNef (originalIntegralQuotientChern_bd7 f E (m + 1) hprojective α) :=
  originalIntegralQuotientChern_isCurveNef_of_nonnegative_projection_bd7 f E m hprojective
    (originalIntegralCurveNonnegativePeriodReadback_of_positive_bd7 f E m hperiod) α hα

/-- A positive projection factor gives the equivalence of the algebraic and analytic cones. -/
theorem originalIntegralDegreeNefCone_iff_nativeClassNef_of_projection_bd7
    [IsIntegral X]
    (hprojective : NormalizationProjectiveForCurves)
    (hperiod : OriginalIntegralCurvePeriodReadback_bd7 f E m)
    (omega : KahlerBackground (m + 1) (SchemeComplexPoint f))
    (α : OriginalIntegralCurveDegreeQuotient_bd7 f E) :
    α ∈ originalIntegralDegreeNefCone_bd7 f E ↔
      ClassNefWithRespectTo omega (originalIntegralQuotientChern_bd7 f E (m + 1) hprojective α) :=
  originalIntegralDegreeNefCone_iff_nativeClassNef_of_nonnegative_projection_bd7 f E m hprojective
    (originalIntegralCurveNonnegativePeriodReadback_of_positive_bd7 f E m hperiod) omega α

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
