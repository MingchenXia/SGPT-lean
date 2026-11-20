import SGPT.PSH.AtlasBiholomorphicCohomology
import SGPT.PSH.AtlasNefPullback
import SGPT.PSH.SigmaNativeFormGluing

/-! Actual biholomorphic coordinate derivatives are injective by the TRUE
inverse chain rule; hence genuine original Kahler forms pull back strictly. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff Classical
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {A : VariableComplexAtlas X} {B : VariableComplexAtlas Y}

/-- The genuine original Kahler condition is strict positivity on ALL
actual original chart tangent lines. Closedness/type are the actual form fields. -/
def OriginalFormIsKahler (theta : AtlasClosedRealOneOneForm A) : Prop :=
  ∀ i z,z∈(A.chart i).target → IsStrictlyPositive (theta.coeff i z)

/-- The TRUE local inverse coordinate equality produces an actual left
inverse derivative, proving injectivity without a geometric/output flag. -/
theorem original_biholomorphic_coordinate_fderiv_injective
    (e : X ≃ₜ Y) (hf : A.IsHolomorphic B e) (hg : B.IsHolomorphic A e.symm)
    (i : A.Index) (j : B.Index) {z : ComplexModel (A.dimension i)}
    (hzj : z∈atlasCoordinateDomain A B e i j) :
    Function.Injective (fderiv ℝ (atlasCoordinateMap A B e i j) z) := by
  let F := atlasCoordinateMap A B e i j
  let G := atlasCoordinateMap B A e.symm j i
  have hgj : F z∈atlasCoordinateDomain B A e.symm j i := by
    refine ⟨atlasCoordinateMap_mem_target hzj,?_⟩
    change e.symm ((B.chart j).symm ((B.chart j) (e ((A.chart i).symm z))))∈(A.chart i).source
    rw [(B.chart j).left_inv hzj.2,e.symm_apply_apply]
    exact (A.chart i).map_target hzj.1
  have hFG : G ∘ F=ᶠ[𝓝 z] id := by
    filter_upwards [(atlasCoordinateDomain_isOpen hf i j).mem_nhds hzj] with y hy
    change (A.chart i) (e.symm ((B.chart j).symm ((B.chart j) (e ((A.chart i).symm y)))))=y
    rw [(B.chart j).left_inv hy.2,e.symm_apply_apply,(A.chart i).right_inv hy.1]
  have hF : DifferentiableAt ℝ F z := (atlasCoordinateMap_contDiffAt_real hf hzj).differentiableAt (by simp)
  have hG : DifferentiableAt ℝ G (F z) := (atlasCoordinateMap_contDiffAt_real hg hgj).differentiableAt (by simp)
  have hder : (fderiv ℝ G (F z)).comp (fderiv ℝ F z)=ContinuousLinearMap.id ℝ (ComplexModel (A.dimension i)) := by
    calc
      _ = fderiv ℝ (G ∘ F) z := (fderiv_comp z hG hF).symm
      _ = fderiv ℝ id z := hFG.fderiv_eq
      _ = _ := fderiv_id
  intro v w hvw
  have h := congrArg (fderiv ℝ G (F z)) hvw
  change ((fderiv ℝ G (F z)).comp (fderiv ℝ F z)) v=
    ((fderiv ℝ G (F z)).comp (fderiv ℝ F z)) w at h
  simpa only [hder,ContinuousLinearMap.id_apply] using h

/-- Actual strict positivity pulls back by an ACTUAL biholomorphism.
The derivative's genuine injectivity and complex-linearity supply every
strict source inequality; no positive lower-bound/output flag is assumed. -/
theorem OriginalFormIsKahler.biholomorphicPullback
    {theta : AtlasClosedRealOneOneForm B} (hK : OriginalFormIsKahler theta)
    (e : X ≃ₜ Y) (hf : A.IsHolomorphic B e) (hg : B.IsHolomorphic A e.symm) :
    OriginalFormIsKahler (theta.holomorphicPullback hf) := by
  intro i z hz v hv
  obtain ⟨j,hj⟩ := B.cover (e ((A.chart i).symm z))
  have hzj : z∈atlasCoordinateDomain A B e i j := ⟨hz,hj⟩
  let L := fderiv ℝ (atlasCoordinateMap A B e i j) z
  have hL := original_biholomorphic_coordinate_fderiv_injective e hf hg i j hzj
  have hvL : L v≠0 := by
    intro hzero
    exact hv (hL (hzero.trans (map_zero L).symm))
  have hpair : L ∘ ![v,Complex.I • v]=![L v,Complex.I • L v] := by
    funext t
    fin_cases t
    · rfl
    · exact atlasCoordinateMap_fderiv_map_smul_complex hf hzj Complex.I v
  rw [theta.holomorphicPullback_coeff hf i j hzj]
  change 0<theta.coeff j (atlasCoordinateMap A B e i j z) (L ∘ ![v,Complex.I • v])
  rw [hpair]
  exact hK j _ (atlasCoordinateMap_mem_target hzj) (L v) hvL

variable {I : Type u} {C : I → Type u} [∀ c,TopologicalSpace (C c)] {n : I → ℕ}
  [∀ c,ChartedSpace (ComplexModel (n c)) (C c)] [∀ c,IsComplexManifold (n c) (C c)]

/-- Actual global sigma Kahler forms give genuine native backgrounds on
EVERY independently dimensional component, with true closedness/type. -/
theorem sigmaRestrictedForm_isKahler
    {theta : AtlasClosedRealOneOneForm (sigmaNativeAtlas (n := n) (C := C))}
    (hK : OriginalFormIsKahler theta) (c : I) : (sigmaRestrictedForm theta c).val.IsKahler := by
  refine ⟨?_,(sigmaRestrictedForm theta c).2.1⟩
  intro e z hz
  exact ⟨theta.typeOneOne ⟨c,e⟩ z hz,hK ⟨c,e⟩ z hz⟩

/-- Genuine native smooth Kahler representatives GLUE into one actual
GLOBAL smooth closed strictly positive original form, no uniform dimension. -/
theorem sigmaGluedForm_isKahler (F : ∀ c,ClosedRealOneOneForm (n c) (C c))
    (hF : ∀ c,(F c).val.IsKahler) : OriginalFormIsKahler (sigmaGluedForm F) := by
  rintro ⟨c,e⟩ z hz
  exact (hF c).1 e z hz |>.2

end SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
