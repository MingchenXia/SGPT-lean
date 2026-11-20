import SGPT.NAPotential.ProjectiveGraphPointEvaluation
import SGPT.NAPotential.ProjectiveGraphUniqueness

/-!
# Actual smooth graph-open membership in the same original global graph

Literal original fraction equations give agreement on a genuine original
denominator open. Its actual preimage is dense, and closedness of the same
constructed global relation set extends membership to every actual point.
Blueprint: `projective-graph-open-membership.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphOpenMembership

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open SGPT.Okounkov SGPT.GAGA.H0S
open ProjectiveGraphRegularEvaluation ProjectiveGraphProjection ProjectiveGraphAnalyticMap
open ProjectiveGraphPointEvaluation ProjectiveGraphSegre ProjectiveGraphUniqueness
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)} {m s : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] [IsProper f]
  (E : ClosedProjectiveEmbedding f) (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
  (b : Fin s → X.functionField) (W : (Spec (.of (Algebra.adjoin Γ(X, U) (Set.range b)))).Opens)
  [SmoothOfRelativeDimension (m + 1) (openStructureMap (f := f) U hU b W)]
  [IsSeparated (openStructureMap (f := f) U hU b W)] [QuasiCompact (openStructureMap (f := f) U hU b W)]

local instance originalTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance originalCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (m + 1)
local instance originalManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (m + 1)
local instance openTopology : TopologicalSpace (SchemeComplexPoint (openStructureMap (f := f) U hU b W)) :=
  schemeAnalyticPointTopology (openStructureMap (f := f) U hU b W)
local instance openCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint (openStructureMap (f := f) U hU b W)) :=
  schemeAnalyticTNChartedSpace (openStructureMap (f := f) U hU b W) (m + 1)
local instance openManifold : IsComplexManifold (m + 1) (SchemeComplexPoint (openStructureMap (f := f) U hU b W)) :=
  schemeAnalyticTN_isComplexManifold (openStructureMap (f := f) U hU b W) (m + 1)

omit [SmoothOfRelativeDimension (m + 1) (openStructureMap (f := f) U hU b W)]
  [IsSeparated (openStructureMap (f := f) U hU b W)] [QuasiCompact (openStructureMap (f := f) U hU b W)] in
/-- Literal fraction equations identify the actual smooth-model graph point with the original regular graph point. -/
theorem agreement_of_fraction (V : X.Opens) (hV : genericPoint X ∈ V) (r : Fin s → Γ(X, V))
    (hr : ∀ i, X.presheaf.germ V (genericPoint X) hV (r i) = b i)
    (d a : Fin s → Γ(X, U))
    (hrel : ∀ i, X.germToFunctionField U (d i) * b i = X.germToFunctionField U (a i))
    (p : SchemeComplexPoint (openStructureMap (f := f) U hU b W))
    (hpV : schemeComplexPointImage f (openGraphMap (f := f) (m := m) U hU b W p).1 ∈ V)
    (hden : ∀ i, schemeOpenRegularFunction f (m + 1) E U (d i)
      (openGraphMap (f := f) (m := m) U hU b W p).1 ≠ 0) :
    openGraphMap (f := f) (m := m) U hU b W p =
      graphMap (m := m) E r (openGraphMap (f := f) (m := m) U hU b W p).1 := by
  let x := (openGraphMap (f := f) (m := m) U hU b W p).1
  have hxU : schemeComplexPointImage f x ∈ U := projection_mem U hU b _
  have hvalue (i : Fin s) : sectionEvaluation (openStructureMap (f := f) U hU b W) (openGraphSection U b W i) p =
      schemeOpenRegularFunction f (m + 1) E V (r i) x := by
    have hB : algebraMap Γ(X, U) (Algebra.adjoin Γ(X, U) (Set.range b)) (d i) *
        (⟨b i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ : Algebra.adjoin Γ(X, U) (Set.range b)) =
      algebraMap Γ(X, U) (Algebra.adjoin Γ(X, U) (Set.range b)) (a i) := by
      apply Subtype.ext
      exact hrel i
    have hpoint := congrArg (graphPointEval (f := f) U hU b W p) hB
    rw [map_mul, graphPointEval_generator,
      graphPointEval_coefficient U hU b W (m + 1) E p (d i),
      graphPointEval_coefficient U hU b W (m + 1) E p (a i)] at hpoint
    have hregular := ProjectiveGraphPointEvaluation.regular_fraction_value (U := U) (f := f)
      (m + 1) E V hV (b i) (r i) (hr i) (d i) (a i) (hrel i) x hxU hpV
    apply mul_left_cancel₀ (hden i)
    exact hpoint.trans hregular.symm
  have hlift : openGraphLift (f := f) U hU b W p = graphLift (m := m) E r x := by
    funext j
    refine Fin.cases (by simp [openGraphLift, graphLift]) (fun i => ?_) j
    simpa only [openGraphLift, graphLift, Fin.cons_succ] using hvalue i
  apply Prod.ext
  · rfl
  · change mk (openGraphLift (f := f) U hU b W p) _ = mk (graphLift (m := m) E r x) _
    apply (mk_eq_mk_iff _ _).mpr
    exact ⟨1, by simpa only [one_smul] using hlift.symm⟩

omit [SmoothOfRelativeDimension (m + 1) (openStructureMap (f := f) U hU b W)]
  [IsSeparated (openStructureMap (f := f) U hU b W)] [QuasiCompact (openStructureMap (f := f) U hU b W)] in
/-- A genuine original generic denominator open is produced for agreement with any actual original regular representatives. -/
theorem exists_denominator_agreement (V : X.Opens) (hV : genericPoint X ∈ V) (r : Fin s → Γ(X, V))
    (hr : ∀ i, X.presheaf.germ V (genericPoint X) hV (r i) = b i) :
    ∃ T : X.Opens, genericPoint X ∈ T ∧ T ≤ V ∧
      ∀ p : SchemeComplexPoint (openStructureMap (f := f) U hU b W),
        schemeComplexPointImage f (openGraphMap (f := f) (m := m) U hU b W p).1 ∈ T →
          openGraphMap (f := f) (m := m) U hU b W p =
            graphMap (m := m) E r (openGraphMap (f := f) (m := m) U hU b W p).1 := by
  classical
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  choose a d hd hfrac using fun i => IsFractionRing.div_surjective Γ(X, U) (b i)
  have hden (i : Fin s) : X.germToFunctionField U (d i) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hd i)
  have hrel (i : Fin s) : X.germToFunctionField U (d i) * b i = X.germToFunctionField U (a i) :=
    (mul_comm _ _).trans ((div_eq_iff (hden i)).mp (hfrac i)).symm
  have hηU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hηd (i : Fin s) : genericPoint X ∈ X.basicOpen (d i) := by
    rw [Scheme.mem_basicOpen _ _ _ hηU, isUnit_iff_ne_zero]
    exact hden i
  let T : X.Opens := (V ⊓ U) ⊓ ⨅ i, X.basicOpen (d i)
  have hηT : genericPoint X ∈ T := by
    refine ⟨⟨hV, hηU⟩, ?_⟩
    change genericPoint X ∈ ((⨅ i, X.basicOpen (d i) : X.Opens) : Set X)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hηd
  refine ⟨T, hηT, inf_le_left.trans inf_le_left, ?_⟩
  intro p hp
  apply agreement_of_fraction (m := m) E U hU b W V hV r hr d a hrel p hp.1.1
  intro i
  apply (schemeOpenRegularFunction_ne_zero_iff f E (m + 1) U (d i) _ hp.1.2).mpr
  exact (show T ≤ X.basicOpen (d i) from inf_le_right.trans (iInf_le _ i)) hp

/-- **Every actual smooth-open graph point belongs to the SAME original global full-relation analytic graph**. -/
theorem openGraphMap_mem_globalRelationGraph [Nonempty W]
    (p : SchemeComplexPoint (openStructureMap (f := f) U hU b W)) :
    openGraphMap (f := f) (m := m) U hU b W p ∈ globalRelationGraph (m := m) E b := by
  obtain ⟨V, hV, _, r, hr, hmem, _⟩ := exists_regularGraph_unique (m := m) E b
  obtain ⟨T, hT, hTV, hagree⟩ := exists_denominator_agreement (m := m) E U hU b W V hV r hr
  let D := ((openGraphMap (f := f) (m := m) U hU b W) ⁻¹' (Prod.fst ⁻¹' graphBase f T))ᶜ
  let C := (openGraphMap (f := f) (m := m) U hU b W) ⁻¹' globalRelationGraph (m := m) E b
  have hDense : Dense D := interior_eq_empty_iff_dense_compl.mp (openGraphMap_base_interior (f := f) (m := m) U hU b W T hT)
  have hC : IsClosed C := (isClosed_globalRelationGraph (m := m) E b).preimage
    (openGraphMap_contMDiff (f := f) (m := m) U hU b W).continuous
  have hDC : D ⊆ C := by
    intro q hq
    have hqT : schemeComplexPointImage f (openGraphMap (f := f) (m := m) U hU b W q).1 ∈ T := by
      simpa only [D, Set.mem_compl_iff, Set.mem_preimage, mem_graphBase, not_not] using hq
    change openGraphMap (f := f) (m := m) U hU b W q ∈ globalRelationGraph (m := m) E b
    rw [hagree q hqT]
    apply hmem
    simpa only [mem_graphBase, not_not] using hTV hqT
  change p ∈ C
  exact closure_minimal hDC hC (by rw [hDense.closure_eq]; trivial)

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphOpenMembership
