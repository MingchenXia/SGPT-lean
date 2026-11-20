import SGPT.NAPotential.NativeDVRSmoothOpen
import SGPT.NAPotential.GraphDivisorAnalyticTrace
import SGPT.Okounkov.SchemeNativeStalkNaturality
import SGPT.NAPotential.TowerAlgOrder

/-!
# Literal original function orders for the produced actual graph divisor

Complete blueprint: `graph-divisor-function-order.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.GraphDivisorFunctionOrder

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes Filter Set
open SGPT.Okounkov SGPT.NAPotential.TowerAlg SGPT.NAPotential.FSPos
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open DemaillyApproximantDivisorialLelong FixedGermNormalOrder HironakaHolomorphicJetRankLoci
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold ContDiff

section NativeGerm

variable {X Y : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (ρ : Y ⟶ X) (m : ℕ)
  [SmoothOfRelativeDimension (m + 1) f] [SmoothOfRelativeDimension (m + 1) (ρ ≫ f)]
  [IsProper f] [IsSeparated (ρ ≫ f)] [QuasiCompact (ρ ≫ f)]

local instance targetTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance targetCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance targetManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)
local instance sourceTopology : TopologicalSpace (SchemeComplexPoint (ρ ≫ f)) :=
  schemeAnalyticPointTopology (ρ ≫ f)
local instance sourceCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint (ρ ≫ f)) :=
  schemeAnalyticTNChartedSpace (ρ ≫ f) (m + 1)
local instance sourceManifold : IsComplexManifold (m + 1) (SchemeComplexPoint (ρ ≫ f)) :=
  schemeAnalyticTN_isComplexManifold (ρ ≫ f) (m + 1)

/-- The original composed holomorphic representative has exactly the native germ of
the ACTUAL algebraic stalk pullback, by proved whole-stalk naturality. -/
theorem chartTranslatedGerm_pullback_stalkRep
    (y : SchemeComplexPoint (ρ ≫ f))
    (g : X.presheaf.stalk
      (schemeComplexPointImage f (schemeComplexPointMap (ρ ≫ f) f ρ rfl y)))
    (hcomp : HolomorphicAt (m + 1)
      (stalkRep m (schemeComplexPointMap (ρ ≫ f) f ρ rfl y) g ∘
        schemeComplexPointMap (ρ ≫ f) f ρ rfl) y) :
    chartTranslatedGerm y y (mem_chart_source _ y)
        (stalkRep m (schemeComplexPointMap (ρ ≫ f) f ρ rfl y) g ∘
          schemeComplexPointMap (ρ ≫ f) f ρ rfl) hcomp =
      stalkToModel (ρ ≫ f) (m + 1) y
        ((ρ.stalkMap (schemeComplexPointImage (ρ ≫ f) y)) g) := by
  change _ = NativeHolGerm.chartEquiv y
    (schemeNativeStalkGerm (ρ ≫ f) (m + 1) y
      ((ρ.stalkMap (schemeComplexPointImage (ρ ≫ f) y)) g))
  rw [schemeNativeStalkGerm_naturality f ρ (m + 1) (m + 1) y g]
  have hN : schemeMorphismNativeGermPullback f ρ (m + 1) (m + 1) y
      (schemeNativeStalkGerm f (m + 1) (schemeComplexPointMap (ρ ≫ f) f ρ rfl y) g) =
        NativeHolGerm.mk
          (stalkRep m (schemeComplexPointMap (ρ ≫ f) f ρ rfl y) g ∘
            schemeComplexPointMap (ρ ≫ f) f ρ rfl) hcomp := by
    rw [schemeNativeStalkGerm_eq_mk_stalkRep]
    apply Subtype.ext
    rfl
  rw [hN]
  apply Subtype.ext
  rw [NativeHolGerm.chartEquiv_mk]
  rfl

end NativeGerm

open SGPT.NAPotential.Berkovich SGPT.NAPotential.AlgPrimes3
open SGPT.NAPotential.AlgPrimes
open ProjectiveGraphAnalyticMap ProjectiveGraphCoordinateCharts
open GraphDivisorAnalyticTrace GraphProjectionNormalOrder
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)} {m : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] [IsProper f]

local instance originalTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance originalCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance originalManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

set_option maxHeartbeats 1600000 in
/-- The ORIGINAL divisor manufactures SAME native graph generators, actual smooth open,
ACTUAL global analytic Δ, its actual pullback flattening, and EXACT literal composed
function orders needed by ProductGraphData. No desired output certificate is assumed. -/
theorem exists_productDivisorNormalOrder (E : ClosedProjectiveEmbedding f)
    (D : PrimeDivisorOver X) (j : Fin (E.ambientDimension + 1))
    [hU : Nonempty (coordOpen E j)] (hpU : D.π D.point ∈ coordOpen E j) :
    ∃ (s : ℕ) (b : Fin s → X.functionField)
      (z : Spec (.of (Algebra.adjoin Γ(X, coordOpen E j) (Set.range b))))
      (W : (Spec (.of (Algebra.adjoin Γ(X, coordOpen E j) (Set.range b)))).Opens)
      (hzW : z ∈ W)
      (hsm : SmoothOfRelativeDimension (m + 1)
        (openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W))
      (hsep : IsSeparated (openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W))
      (hqc : QuasiCompact (openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W)),
      letI : Nonempty W := ⟨⟨z, hzW⟩⟩
      letI := hsm
      letI := hsep
      letI := hqc
      let fW := openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W
      letI : TopologicalSpace (SchemeComplexPoint fW) := schemeAnalyticPointTopology fW
      letI : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint fW) :=
        schemeAnalyticTNChartedSpace fW (m + 1)
      letI : IsComplexManifold (m + 1) (SchemeComplexPoint fW) :=
        schemeAnalyticTN_isComplexManifold fW (m + 1)
      let ι := openGraphMap (f := f) (m := m) (coordOpen E j) (isAffineOpen_coordOpen E j) b W
      let Δ := productDivisorLocus (m := m) E j b z.asIdeal
      ∃ (hι : ContMDiff 𝓘(ℂ, ComplexModel (m + 1))
        𝓘(ℂ, ComplexModel ((m + 1) + s)) ∞ ι)
        (n₀ : SchemeComplexPoint fW) (Ψ : DivisorFlattening (m := m) (ι ⁻¹' Δ) n₀),
        ∀ g : X.presheaf.stalk (schemeComplexPointImage f (ι n₀).1), g ≠ 0 →
          D.ord ((BerkovichPoint.specializationMap
            (ordVal_support_specializes f D (schemeComplexPointImage f (ι n₀).1))).hom g) =
            ((functionNormalOrder Ψ (stalkRep m (ι n₀).1 g ∘ (Prod.fst ∘ ι))
              (HolomorphicAt.comp_contMDiff (f := Prod.fst ∘ ι) (y := n₀)
                (stalkRep_holomorphicAt (ι n₀).1 g)
                (Eventually.of_forall fun _ =>
                  ((contMDiff_fst_graphAmbient s).comp hι).contMDiffAt))).toNat : ℤ) := by
  obtain ⟨hV, s, b₀, i, z, hi, hzi, hDVR, hz, hcenter, W, hWa, hzW, hsm, hsep, hqc, hnorm⟩ :=
    NativeDVRSmoothOpen.exists_prescribedGraph_smoothNormalOrder f m D
      (coordOpen E j) (isAffineOpen_coordOpen E j) hpU
  let b := fun k => OpenDivisorOrderTransport.originalFunctionFieldEquiv D (b₀ k)
  let fW := openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W
  let : Nonempty W := ⟨⟨z, hzW⟩⟩
  have hsm' : SmoothOfRelativeDimension (m + 1) fW := hsm
  have hsep' : IsSeparated fW := hsep
  have hqc' : QuasiCompact fW := hqc
  let := hsm'
  let := hsep'
  let := hqc'
  let : SmoothOfRelativeDimension (m + 1)
      (openProjection (coordOpen E j) (isAffineOpen_coordOpen E j) b W ≫ f) := hsm'
  let : IsSeparated (openProjection (coordOpen E j) (isAffineOpen_coordOpen E j) b W ≫ f) := hsep'
  let : QuasiCompact (openProjection (coordOpen E j) (isAffineOpen_coordOpen E j) b W ≫ f) := hqc'
  let : TopologicalSpace (SchemeComplexPoint fW) := schemeAnalyticPointTopology fW
  let : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint fW) :=
    schemeAnalyticTNChartedSpace fW (m + 1)
  let : IsComplexManifold (m + 1) (SchemeComplexPoint fW) :=
    schemeAnalyticTN_isComplexManifold fW (m + 1)
  have hι := openGraphMap_contMDiff (f := f) (m := m)
    (coordOpen E j) (isAffineOpen_coordOpen E j) b W
  refine ⟨s, b, z, W, hzW, hsm', hsep', hqc', hι, ?_⟩
  have hnorm' : ProjectionNormalOrder D fW m (⟨z, hzW⟩ : W.toScheme)
      (openProjection (coordOpen E j) (isAffineOpen_coordOpen E j) b W)
      (openProjection_genericPoint (coordOpen E j) (isAffineOpen_coordOpen E j) b W) := hnorm
  obtain ⟨y, hzy, Ψ, hreg, hrat⟩ := hnorm'
  have htrace := openGraphMap_preimage_productDivisorLocus (m := m) E j b W z hzW
  dsimp only
  rw [htrace]
  refine ⟨y, Ψ, ?_⟩
  intro g hg
  unfold functionNormalOrder
  dsimp only [openGraphMap, Function.comp_def]
  erw [chartTranslatedGerm_pullback_stalkRep f
    (openProjection (coordOpen E j) (isAffineOpen_coordOpen E j) b W) m]
  exact hreg g hg

end SGPT.NAPotential.GraphDivisorFunctionOrder
