import SGPT.NAPotential.ProjectiveGraphRegularEvaluation
import SGPT.NAPotential.ProjectiveGraphProjection
import SGPT.NAPotential.NativeSchemeImmersion
import SGPT.NAPotential.AlgPrimes3GraphMap

/-!
# The actual smooth-open graph map into the original product manifold

The first component is the actual original graph projection. The second uses
actual generator sections and canonical native complex-point evaluation.
Blueprint: `projective-graph-analytic-map.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphAnalyticMap

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open SGPT.Okounkov
open ProjectiveGraphProjection ProjectiveGraphRegularEvaluation
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)} {m s : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] [IsProper f]
  (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U) (b : Fin s → X.functionField)
  (W : (Spec (.of (Algebra.adjoin Γ(X, U) (Set.range b)))).Opens)

/-- The original graph's actual first projection restricted to the actual original smooth open. -/
def openProjection : W.toScheme ⟶ X := W.ι ≫ projection U hU b

/-- The actual original structural morphism on the actual graph open. -/
def openStructureMap : W.toScheme ⟶ Spec (.of ℂ) := openProjection U hU b W ≫ f

/-- The actual generator section on the actual original graph open. -/
def openGraphSection (i : Fin s) : Γ(W.toScheme, ⊤) :=
  W.ι.appTop ((Scheme.ΓSpecIso (.of (Algebra.adjoin Γ(X, U) (Set.range b)))).inv
    (⟨b i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ : Algebra.adjoin Γ(X, U) (Set.range b)))

variable [SmoothOfRelativeDimension (m + 1) (openStructureMap (f := f) U hU b W)]
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

/-- The actual normalized lift of the original graph generators on this actual smooth open. -/
def openGraphLift (p : SchemeComplexPoint (openStructureMap (f := f) U hU b W)) : Fin (s + 1) → ℂ :=
  Fin.cons 1 (fun i => sectionEvaluation (openStructureMap (f := f) U hU b W) (openGraphSection U b W i) p)

omit [IsProper f] [IsSeparated (openStructureMap (f := f) U hU b W)]
  [QuasiCompact (openStructureMap (f := f) U hU b W)] in
theorem openGraphLift_ne_zero (p : SchemeComplexPoint (openStructureMap (f := f) U hU b W)) :
    openGraphLift (f := f) U hU b W p ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  exact one_ne_zero (by simpa only [openGraphLift, Fin.cons_zero, Pi.zero_apply] using h0)

/-- **The actual original smooth graph map into the original product graphAmbient**. -/
def openGraphMap (p : SchemeComplexPoint (openStructureMap (f := f) U hU b W)) : graphAmbient f m s :=
  (schemeComplexPointMap (openStructureMap (f := f) U hU b W) f (openProjection U hU b W) rfl p,
    mk (openGraphLift (f := f) U hU b W p) (openGraphLift_ne_zero (f := f) U hU b W p))

omit [SmoothOfRelativeDimension (m + 1) f] [IsProper f] in
/-- The original generator lift is actually holomorphic in the same native source charts. -/
theorem openGraphLift_contMDiff :
    ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, Fin (s + 1) → ℂ) ∞
      (openGraphLift (f := f) U hU b W) := by
  intro p
  rw [contMDiffAt_pi_space]
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa only [openGraphLift, Fin.cons_zero] using (contMDiffAt_const (c := (1 : ℂ)))
  · simpa only [openGraphLift, Fin.cons_succ] using
      (sectionEvaluation_contMDiff (openStructureMap (f := f) U hU b W) (m + 1) (openGraphSection U b W i) p)

/-- **Actual original product-map holomorphy**, with no supplied analytic graph-map certificate. -/
theorem openGraphMap_contMDiff :
    ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel ((m + 1) + s)) ∞
      (openGraphMap (f := f) (m := m) U hU b W) := by
  have hfirst := NativeSchemeImmersion.contMDiff_pointMap (openStructureMap (f := f) U hU b W)
    f (openProjection U hU b W) rfl (m + 1) (m + 1) ∞
  have hsecond : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel s) ∞
      (fun p => mk (openGraphLift (f := f) U hU b W p) (openGraphLift_ne_zero (f := f) U hU b W p)) := by
    intro p
    apply ComplexProjectiveSpace.contMDiffAt_of_lift (openGraphLift_contMDiff (f := f) U hU b W p)
      (openGraphLift_ne_zero (f := f) U hU b W p)
    exact Filter.Eventually.of_forall fun q => ⟨openGraphLift_ne_zero (f := f) U hU b W q, rfl⟩
  exact ProductComplexManifold.contMDiff_prodMk hfirst hsecond

omit [SmoothOfRelativeDimension (m + 1) (openStructureMap (f := f) U hU b W)]
  [IsSeparated (openStructureMap (f := f) U hU b W)] [QuasiCompact (openStructureMap (f := f) U hU b W)] in
/-- The actual product map's first component is the original graph projection's same native point map. -/
theorem openGraphMap_fst (p : SchemeComplexPoint (openStructureMap (f := f) U hU b W)) :
    (openGraphMap (f := f) (m := m) U hU b W p).1 =
      schemeComplexPointMap (openStructureMap (f := f) U hU b W) f (openProjection U hU b W) rfl p := rfl

omit [SmoothOfRelativeDimension (m + 1) f] [IsProper f]
  [SmoothOfRelativeDimension (m + 1) (openStructureMap (f := f) U hU b W)]
  [IsSeparated (openStructureMap (f := f) U hU b W)] [QuasiCompact (openStructureMap (f := f) U hU b W)] in
/-- The actual nonempty smooth graph open's original first projection preserves the actual generic point. -/
theorem openProjection_genericPoint [Nonempty W] :
    openProjection U hU b W (genericPoint W.toScheme) = genericPoint X := by
  change projection U hU b (W.ι (genericPoint W.toScheme)) = _
  rw [genericPoint_eq_of_isOpenImmersion W.ι, projection_genericPoint]

/-- **The actual original base-exceptional preimage has empty interior**, for the same constructed product map. -/
theorem openGraphMap_base_interior [Nonempty W] (V : X.Opens) (hV : genericPoint X ∈ V) :
    interior ((openGraphMap (f := f) (m := m) U hU b W) ⁻¹' (Prod.fst ⁻¹' graphBase f V)) = ∅ := by
  let Z : Set W.toScheme := (openProjection U hU b W) ⁻¹' ((V : Set X)ᶜ)
  have hZ : IsClosed Z := V.isOpen.isClosed_compl.preimage (openProjection U hU b W).continuous
  have hZne : Z ≠ Set.univ := by
    intro h
    have hη : genericPoint W.toScheme ∈ Z := by rw [h]; trivial
    exact hη (by rw [openProjection_genericPoint]; exact hV)
  have hset : ((openGraphMap (f := f) (m := m) U hU b W) ⁻¹' (Prod.fst ⁻¹' graphBase f V)) =
      schemeNativeAlgebraicTrace (openStructureMap (f := f) U hU b W) Z := by
    ext p
    change ((p.val ≫ openProjection U hU b W) default ∉ V) ↔
      (openProjection U hU b W (p.val default) ∉ V)
    rw [Scheme.Hom.comp_apply]
  rw [hset]
  exact schemeNativeAlgebraicTrace_interior_eq_empty (openStructureMap (f := f) U hU b W) (m + 1) Z hZ hZne

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphAnalyticMap
