import SGPT.NAPotential.NativeGraphImmersion

/-!
# Actual native locally closed immersion derivatives

The genuine coborder closed/open factorization reuses the already constructed
native closed-immersion derivative and original open-immersion inverse.
Blueprint: `native-graph-immersion.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.NativeSchemeImmersion

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter Manifold
open SGPT.Okounkov NativeOpenJacobian
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

section Structure

variable {X Y : Scheme.{0}} (fX : X ⟶ Spec (.of ℂ)) (fY : Y ⟶ Spec (.of ℂ))
  (j : X ⟶ Y) (hj : j ≫ fY = fX) (n m : ℕ)
  [SmoothOfRelativeDimension n fX] [SmoothOfRelativeDimension m fY]

local instance structureSourceTopology : TopologicalSpace (SchemeComplexPoint fX) := schemeAnalyticPointTopology fX
local instance structureTargetTopology : TopologicalSpace (SchemeComplexPoint fY) := schemeAnalyticPointTopology fY
local instance structureSourceCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint fX) := schemeAnalyticTNChartedSpace fX n
local instance structureTargetCharts : ChartedSpace (ComplexModel m) (SchemeComplexPoint fY) := schemeAnalyticTNChartedSpace fY m

/-- Original structural compatibility retains actual native holomorphy in arbitrary source/target dimensions. -/
theorem contMDiff_pointMap (k : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) k (schemeComplexPointMap fX fY j hj) := by
  cases hj
  exact schemeComplexPointMap_contMDiff fY j n m k

/-- Original structural compatibility retains the actual closed-immersion tangent injection. -/
theorem closedImmersion_mfderiv_injective [IsClosedImmersion j] (p : SchemeComplexPoint fX) :
    Function.Injective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m)
      (schemeComplexPointMap fX fY j hj) p) := by
  cases hj
  exact NativeGraphImmersion.closedImmersion_mfderiv_injective fY j n m p

end Structure

section Open

variable {X Y : Scheme.{0}} (fX : X ⟶ Spec (.of ℂ)) (fY : Y ⟶ Spec (.of ℂ))
  (j : X ⟶ Y) (hj : j ≫ fY = fX) (n : ℕ)
  [SmoothOfRelativeDimension n fX] [SmoothOfRelativeDimension n fY] [IsOpenImmersion j]

local instance openSourceTopology : TopologicalSpace (SchemeComplexPoint fX) := schemeAnalyticPointTopology fX
local instance openTargetTopology : TopologicalSpace (SchemeComplexPoint fY) := schemeAnalyticPointTopology fY
local instance openSourceCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint fX) := schemeAnalyticTNChartedSpace fX n
local instance openTargetCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint fY) := schemeAnalyticTNChartedSpace fY n

/-- The actual native open inverse makes the tangent map of an original open immersion injective. -/
theorem openImmersion_mfderiv_injective (p : SchemeComplexPoint fX) :
    Function.Injective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (schemeComplexPointMap fX fY j hj) p) := by
  let b := schemeComplexPointMap fX fY j hj
  have heq : (𝟙 X) ≫ fX = j ≫ fY := by rw [Category.id_comp, hj]
  let s := schemeNativeOpenInverseMap fY fX j (𝟙 X) heq p
  have hleft : Function.LeftInverse s b := by
    intro x
    exact schemeNativeOpenInverseMap_left_inv fY fX j (𝟙 X) heq p j hj
      (Category.id_comp j) x ⟨schemeComplexPointImage fX x, rfl⟩
  have hO : IsOpen {q : SchemeComplexPoint fY | schemeComplexPointImage fY q ∈ Set.range j} :=
    (IsOpenImmersion.isOpen_range j).preimage (schemeComplexPointImage_continuous fY)
  have hbp : schemeComplexPointImage fY (b p) ∈ Set.range j :=
    ⟨schemeComplexPointImage fX p, (Scheme.Hom.comp_apply p.val j default).symm⟩
  have hs := (schemeNativeOpenInverseMap_contMDiffOn fY fX n n j (𝟙 X) heq p ∞).contMDiffAt (hO.mem_nhds hbp)
  have hb := (contMDiff_pointMap fX fY j hj n n ∞).contMDiffAt (x := p)
  have hfun : s ∘ b = id := funext hleft
  have hchain := mfderiv_comp p (hs.mdifferentiableAt (by simp)) (hb.mdifferentiableAt (by simp))
  rw [hfun, mfderiv_id] at hchain
  have hleftD : Function.LeftInverse
      (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) s (b p))
      (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) b p) := by
    intro v
    exact (congrArg (fun L : ComplexModel n →L[ℂ] ComplexModel n => L v) hchain).symm
  exact hleftD.injective

end Open

/-- Composition is the literal original composition on actual native complex points. -/
theorem pointMap_comp {X Y Z : Scheme.{0}} (fX : X ⟶ Spec (.of ℂ))
    (fY : Y ⟶ Spec (.of ℂ)) (fZ : Z ⟶ Spec (.of ℂ))
    (i : X ⟶ Y) (j : Y ⟶ Z) (hi : i ≫ fY = fX) (hj : j ≫ fZ = fY) :
    schemeComplexPointMap fX fZ (i ≫ j) (by rw [Category.assoc, hj, hi]) =
      schemeComplexPointMap fY fZ j hj ∘ schemeComplexPointMap fX fY i hi := by
  funext p
  apply Subtype.ext
  exact (Category.assoc p.val i j).symm

section Immersion

variable {X Y : Scheme.{0}} (fX : X ⟶ Spec (.of ℂ)) (fY : Y ⟶ Spec (.of ℂ))
  (j : X ⟶ Y) (hj : j ≫ fY = fX) (n m : ℕ)
  [SmoothOfRelativeDimension n fX] [SmoothOfRelativeDimension m fY] [IsImmersion j]

local instance immersionSourceTopology : TopologicalSpace (SchemeComplexPoint fX) := schemeAnalyticPointTopology fX
local instance immersionTargetTopology : TopologicalSpace (SchemeComplexPoint fY) := schemeAnalyticPointTopology fY
local instance immersionSourceCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint fX) := schemeAnalyticTNChartedSpace fX n
local instance immersionTargetCharts : ChartedSpace (ComplexModel m) (SchemeComplexPoint fY) := schemeAnalyticTNChartedSpace fY m

/-- **Actual native locally closed immersion tangent injection**: the original coborder factorization
and original inverse germ prove the derivative in the unchanged book charts is injective. -/
theorem immersion_mfderiv_injective (p : SchemeComplexPoint fX) :
    Function.Injective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m)
      (schemeComplexPointMap fX fY j hj) p) := by
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
  have hmap : schemeComplexPointMap fX fY j hj =
      schemeComplexPointMap fO fY O.ι rfl ∘ schemeComplexPointMap fX fO c hcf := by
    funext x
    apply Subtype.ext
    change x.val ≫ j = (x.val ≫ c) ≫ O.ι
    rw [Category.assoc]
    exact congrArg (fun h : X ⟶ Y => x.val ≫ h) j.liftCoborder_ι.symm
  have hc := (contMDiff_pointMap fX fO c hcf n m ∞).contMDiffAt (x := p)
  have ho := (contMDiff_pointMap fO fY O.ι rfl m m ∞).contMDiffAt
    (x := schemeComplexPointMap fX fO c hcf p)
  rw [hmap, mfderiv_comp p (ho.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp))]
  exact (openImmersion_mfderiv_injective fO fY O.ι rfl m _).comp
    (closedImmersion_mfderiv_injective fX fO c hcf n m p)

end Immersion

end SGPT.NAPotential.NativeSchemeImmersion
