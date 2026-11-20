import SGPT.Projective.OriginalCurveNativeGeometry
import SGPT.Projective.OriginalAlgebraicCutPeriod

/-! Native degree of the ENTIRE SAME actual original algebraic terminal
curve equals its literal original physical mixed Chern period.
Blueprint: whole-original-ci-period.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set
open SGPT.Okounkov SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open NefMixedMass UniformNefCoreSupport
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open scoped Topology Manifold ContDiff BigOperators

local instance originalPeriodTopology {A : Scheme.{0}} (g : A ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g
local instance originalPeriodCharts {A : Scheme.{0}} (g : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] : ChartedSpace (ComplexModel d) (SchemeComplexPoint g) :=
  schemeAnalyticTNChartedSpace g d
local instance originalPeriodManifold {A : Scheme.{0}} (g : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold d (SchemeComplexPoint g) := schemeAnalyticTN_isComplexManifold g d

namespace WholeOriginalCITower

/-- The SAME actual chosen power product follows the literal original first-cut recursion. -/
theorem powers_real_prod_succ (k : ℕ) {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)}
    [SmoothOfRelativeDimension (k + 2) f] [IsSeparated f] [QuasiCompact f]
    {E : ClosedProjectiveEmbedding f} {P : Fin (k + 1) → OriginalPositiveLine f (k + 2) E}
    (T : WholeOriginalCITower (k + 1) f E P) :
    (∏ i, (powers (k + 1) T i : ℝ)) =
      (T.1.nativeCut.power : ℝ) * ∏ i, (powers k T.2 i : ℝ) := by
  simp only [Fin.prod_univ_succ, powers, Fin.cons_zero, Fin.cons_succ]

/-- The original positive power factor is strictly positive on the WHOLE actual algebraic tower. -/
theorem powers_real_prod_pos (k : ℕ) {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)}
    [SmoothOfRelativeDimension (k + 1) f] [IsSeparated f] [QuasiCompact f]
    {E : ClosedProjectiveEmbedding f} {P : Fin k → OriginalPositiveLine f (k + 1) E}
    (T : WholeOriginalCITower k f E P) : 0 < ∏ i, (powers k T i : ℝ) :=
  Finset.prod_pos (fun i _ => by exact_mod_cast powers_pos k T i)

/-- Degree on the ENTIRE actual ORIGINAL algebraic terminal curve equals the
SAME original positive power product times the original physical mixed period. -/
theorem terminal_degree_eq_power_product (k : ℕ) {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension (k + 1) f] [IsSeparated f] [QuasiCompact f]
    {E : ClosedProjectiveEmbedding f} {P : Fin k → OriginalPositiveLine f (k + 1) E}
    (T : WholeOriginalCITower k f E P) (κ : KahlerBackground (k + 1) (SchemeComplexPoint f))
    (κC : KahlerBackground 1 (SchemeComplexPoint (terminal k f T).structureMap))
    (alpha : ClosedRealOneOneForm (k + 1) (SchemeComplexPoint f)) :
    let : CompactSpace (SchemeComplexPoint (terminal k f T).structureMap) := (terminal k f T).native_compact E
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : MeasurableSpace (SchemeComplexPoint f) := borel _
    let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    degreeAlong κC ((terminal k f T).nativeMap (k + 1)).contMDiff alpha =
      (∏ i, (powers k T i : ℝ)) * slotIntegral κ (Fin.cons alpha (fun i => (P i).curvature)) := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  cases k with
  | zero =>
      revert κC
      erw [terminal.eq_1]
      dsimp only
      intro κC
      let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
      let Z : OriginalCurveOver f :=
        { source := X, structureMap := f, inclusion := 𝟙 X, over_base := Category.id_comp f,
          closed := inferInstance, smooth := inferInstance }
      have hmap : Z.nativeMap 1 =
          (⟨id, contMDiff_id⟩ : ContMDiffMap 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 1)
            (SchemeComplexPoint f) (SchemeComplexPoint f) ∞) := by
        apply ContMDiffMap.ext
        intro q
        apply Subtype.ext
        exact Category.comp_id q.val
      have hfirst := congrArg (fun G : ContMDiffMap 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 1)
        (SchemeComplexPoint f) (SchemeComplexPoint f) ∞ => degreeAlong κC G.contMDiff alpha) hmap
      have hempty : (fun i : Fin 0 => (P i).curvature) = Fin.elim0 := by funext i; exact Fin.elim0 i
      simp only [Fin.prod_univ_zero, one_mul, hempty]
      refine hfirst.trans ((slotIntegral_eq_of_bottChernRel κC _ _ ?_).trans
        (slotIntegral_eq_of_background κ κC (Fin.cons alpha Fin.elim0)))
      intro i
      fin_cases i
      exact ClosedRealOneOneForm.bottChernRel_of_geometricallyEq
        (SmoothRealForm.pullback_id_geometricallyEq alpha.val)
  | succ k =>
      revert κC
      erw [terminal.eq_1]
      dsimp only
      intro κC
      let C := T.1
      let Z := terminal k (C.inclusion ≫ f) T.2
      let R : OriginalCurveOver f :=
        { source := Z.source, structureMap := Z.structureMap, inclusion := Z.inclusion ≫ C.inclusion,
          over_base := by rw [Category.assoc, Z.over_base], closed := inferInstance, smooth := Z.smooth }
      let : CompactSpace (SchemeComplexPoint Z.structureMap) := Z.native_compact C.embedding
      let : CompactSpace (SchemeComplexPoint (C.inclusion ≫ f)) := C.embedding.analyticCompact
      let : MeasurableSpace (SchemeComplexPoint (C.inclusion ≫ f)) := borel _
      let : BorelSpace (SchemeComplexPoint (C.inclusion ≫ f)) := ⟨rfl⟩
      let Q := C.restrictLine (P 0)
      let κZ : KahlerBackground (k + 1) (SchemeComplexPoint (C.inclusion ≫ f)) := ⟨Q.curvature, Q.positive⟩
      let hι := schemeComplexPointMap_contMDiff f C.inclusion (k + 1) (k + 2) ∞
      let beta : Fin (k + 1) → ClosedRealOneOneForm (k + 2) (SchemeComplexPoint f) :=
        Fin.cons alpha (fun i => (P i.succ).curvature)
      let F : ContMDiffMap 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel (k + 2))
          (SchemeComplexPoint Z.structureMap) (SchemeComplexPoint f) ∞ :=
        ⟨schemeComplexPointMap (C.inclusion ≫ f) f C.inclusion rfl ∘ Z.nativeMap (k + 1),
          hι.comp (Z.nativeMap (k + 1)).contMDiff⟩
      have hmap : R.nativeMap (k + 2) = F := by
        apply ContMDiffMap.ext
        intro q
        exact congrFun (SGPT.NAPotential.NativeSchemeImmersion.pointMap_comp Z.structureMap
          (C.inclusion ≫ f) f Z.inclusion C.inclusion Z.over_base rfl) q
      have hfirst := (congrArg (fun G : ContMDiffMap 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel (k + 2))
        (SchemeComplexPoint Z.structureMap) (SchemeComplexPoint f) ∞ => degreeAlong κC G.contMDiff alpha) hmap).trans
          (degreeAlong_comp_actual κC hι (Z.nativeMap (k + 1)).contMDiff alpha)
      have htail := terminal_degree_eq_power_product k (C.inclusion ≫ f) T.2 κZ κC
        (ClosedRealOneOneForm.pullback hι alpha)
      have htuple : slotIntegral κZ
          (Fin.cons (ClosedRealOneOneForm.pullback hι alpha) (fun i => (C.restrictLine (P i.succ)).curvature)) =
          slotIntegral κZ (fun i => ClosedRealOneOneForm.pullback hι (beta i)) := by
        apply slotIntegral_eq_of_bottChernRel
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact ClosedRealOneOneForm.bottChernRel_of_geometricallyEq (fun _ _ _ => rfl)
        · exact ClosedRealOneOneForm.bottChernRel_of_geometricallyEq
            (OriginalPositiveLine.restrict_curvature (n := k + 1) f C.inclusion (k + 2) E C.embedding (P j.succ))
      let : SmoothOfRelativeDimension (k + 1)
          (sectionZeroι ((P 0).atlas.tensorPower C.nativeCut.power) C.originalSection ≫ f) := C.smooth
      have hperiod : slotIntegral κZ (fun i => ClosedRealOneOneForm.pullback hι (beta i)) =
          (C.nativeCut.power : ℝ) * slotIntegral κ (Fin.snoc beta (P 0).curvature) :=
        originalAlgebraicCut_slotIntegral f k E (P 0).atlas (P 0).metric (P 0).positive
          C.nativeCut C.originalSection C.coefficient κ κZ beta
      have hP : (Fin.cons (P 0).curvature (fun i : Fin k => (P i.succ).curvature) :
          Fin (k + 1) → ClosedRealOneOneForm (k + 2) (SchemeComplexPoint f)) = fun i => (P i).curvature := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      change _ = (C.nativeCut.power : ℝ) *
        slotIntegral κ (Fin.snoc (Fin.cons alpha (fun i : Fin k => (P i.succ).curvature)) (P 0).curvature) at hperiod
      rw [slotIntegral_cons_snoc_cycle, hP] at hperiod
      change degreeAlong κC (R.nativeMap (k + 2)).contMDiff alpha = _
      rw [hfirst, htail, htuple, hperiod, powers_real_prod_succ]
      ring
termination_by k

end WholeOriginalCITower
end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
