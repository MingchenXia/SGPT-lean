import SGPT.NAPotential.NativeSchemeImmersion

/-! # Actual analytic embeddings and local image of native immersions
Blueprint: `native-graph-local-image.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SGPT.NAPotential.NativeImmersionEmbedding

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open SGPT.Okounkov
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

namespace Open
variable {X Y : Scheme.{0}} (fX : X ⟶ Spec (.of ℂ)) (fY : Y ⟶ Spec (.of ℂ))
  (j : X ⟶ Y) (hj : j ≫ fY = fX) (n : ℕ)
  [SmoothOfRelativeDimension n fX] [SmoothOfRelativeDimension n fY] [IsOpenImmersion j]
local instance sourceTopology : TopologicalSpace (SchemeComplexPoint fX) := schemeAnalyticPointTopology fX
local instance targetTopology : TopologicalSpace (SchemeComplexPoint fY) := schemeAnalyticPointTopology fY
local instance sourceCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint fX) := schemeAnalyticTNChartedSpace fX n
local instance targetCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint fY) := schemeAnalyticTNChartedSpace fY n

include n in
/-- Actual native open inverse continuity proves the SAME original point map is an analytic embedding. -/
theorem open_pointMap_isEmbedding (p₀ : SchemeComplexPoint fX) :
    Topology.IsEmbedding (schemeComplexPointMap fX fY j hj) := by
  let b := schemeComplexPointMap fX fY j hj
  have heq : (𝟙 X) ≫ fX = j ≫ fY := by rw [Category.id_comp, hj]
  let s := schemeNativeOpenInverseMap fY fX j (𝟙 X) heq p₀
  have hleft : Function.LeftInverse s b := by
    intro x
    exact schemeNativeOpenInverseMap_left_inv fY fX j (𝟙 X) heq p₀ j hj
      (Category.id_comp j) x ⟨schemeComplexPointImage fX x, rfl⟩
  have hleftfun : s ∘ b = id := funext hleft
  have hO : IsOpen {q : SchemeComplexPoint fY | schemeComplexPointImage fY q ∈ Set.range j} :=
    (IsOpenImmersion.isOpen_range j).preimage (schemeComplexPointImage_continuous fY)
  have hb := NativeSchemeImmersion.contMDiff_pointMap fX fY j hj n n ∞
  apply Topology.IsEmbedding.mk' b hleft.injective
  intro x
  have hbx : schemeComplexPointImage fY (b x) ∈ Set.range j :=
    ⟨schemeComplexPointImage fX x, (Scheme.Hom.comp_apply x.val j default).symm⟩
  have hs := (schemeNativeOpenInverseMap_contMDiffOn fY fX n n j (𝟙 X) heq p₀ ∞).contMDiffAt (hO.mem_nhds hbx)
  have hst := hs.continuousAt.tendsto
  change Tendsto s (𝓝 (b x)) (𝓝 (s (b x))) at hst
  rw [hleft x] at hst
  apply le_antisymm
  · have ht := hst.comp (tendsto_comap : Tendsto b (comap b (𝓝 (b x))) (𝓝 (b x)))
    simpa only [hleftfun, tendsto_id'] using ht
  · exact (hb x).continuousAt.tendsto.le_comap
end Open

namespace Immersion
variable {X Y : Scheme.{0}} (fX : X ⟶ Spec (.of ℂ)) (fY : Y ⟶ Spec (.of ℂ))
  (j : X ⟶ Y) (hj : j ≫ fY = fX) (n m : ℕ)
  [SmoothOfRelativeDimension n fX] [SmoothOfRelativeDimension m fY] [IsImmersion j]
local instance sourceTopology : TopologicalSpace (SchemeComplexPoint fX) := schemeAnalyticPointTopology fX
local instance targetTopology : TopologicalSpace (SchemeComplexPoint fY) := schemeAnalyticPointTopology fY
local instance sourceCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint fX) := schemeAnalyticTNChartedSpace fX n
local instance targetCharts : ChartedSpace (ComplexModel m) (SchemeComplexPoint fY) := schemeAnalyticTNChartedSpace fY m

include n m in
/-- **Every actual native immersion is an embedding in the SAME original analytic topology**. -/
theorem immersion_pointMap_isEmbedding (p₀ : SchemeComplexPoint fX) :
    Topology.IsEmbedding (schemeComplexPointMap fX fY j hj) := by
  let O := j.coborderRange
  let c := j.liftCoborder
  let fO := O.ι ≫ fY
  have hcf : c ≫ fO = fX := by
    rw [← Category.assoc]
    exact (congrArg (fun h : X ⟶ Y => h ≫ fY) j.liftCoborder_ι).trans hj
  let : SmoothOfRelativeDimension m fO := by
    have h : SmoothOfRelativeDimension (0 + m) (O.ι ≫ fY) := inferInstance
    simpa only [Nat.zero_add] using h
  let : TopologicalSpace (SchemeComplexPoint fO) := schemeAnalyticPointTopology fO
  let : ChartedSpace (ComplexModel m) (SchemeComplexPoint fO) := schemeAnalyticTNChartedSpace fO m
  have hc : Topology.IsEmbedding (schemeComplexPointMap fX fO c hcf) := by
    cases hcf
    exact closedImmersionComplexPointMap_isEmbedding fO c
  have ho := Open.open_pointMap_isEmbedding fO fY O.ι rfl m
    (schemeComplexPointMap fX fO c hcf p₀)
  have hmap : schemeComplexPointMap fX fY j hj =
      schemeComplexPointMap fO fY O.ι rfl ∘ schemeComplexPointMap fX fO c hcf := by
    funext x
    apply Subtype.ext
    change x.val ≫ j = (x.val ≫ c) ≫ O.ι
    rw [Category.assoc]
    exact congrArg (fun h : X ⟶ Y => x.val ≫ h) j.liftCoborder_ι.symm
  rw [hmap]
  exact ho.comp hc
end Immersion

end SGPT.NAPotential.NativeImmersionEmbedding
