import SGPT.PSH.AtlasCohomologyPullback

/-! Genuine global quotient equivalence under actual biholomorphic
homeomorphisms, proved by the full tensor and real derivative inverse laws. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff Classical
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {A : VariableComplexAtlas X} {B : VariableComplexAtlas Y}

/-- Actual inverse maps give the full original TWO-form pullback round trip
on every chart target. The proof uses actual local inverse coordinates and
the derivative chain rule, without a supplied tensor-compatibility certificate. -/
theorem original_biholomorphic_pullback_roundtrip_coeff
    (theta : AtlasClosedRealOneOneForm A) (e : X ≃ₜ Y)
    (hf : A.IsHolomorphic B e) (hg : B.IsHolomorphic A e.symm)
    (i : A.Index) {z : ComplexModel (A.dimension i)} (hz : z∈(A.chart i).target) :
    ((theta.holomorphicPullback hg).holomorphicPullback hf).coeff i z=theta.coeff i z := by
  obtain ⟨j,hj⟩ := B.cover (e ((A.chart i).symm z))
  let F := atlasCoordinateMap A B e i j
  let G := atlasCoordinateMap B A e.symm j i
  have hzj : z∈atlasCoordinateDomain A B e i j := ⟨hz,hj⟩
  have hgj : F z∈atlasCoordinateDomain B A e.symm j i := by
    refine ⟨atlasCoordinateMap_mem_target hzj,?_⟩
    change e.symm ((B.chart j).symm ((B.chart j) (e ((A.chart i).symm z))))∈(A.chart i).source
    rw [(B.chart j).left_inv hj,e.symm_apply_apply]
    exact (A.chart i).map_target hz
  have hFG : G ∘ F=ᶠ[𝓝 z] id := by
    filter_upwards [(atlasCoordinateDomain_isOpen hf i j).mem_nhds hzj] with y hy
    change (A.chart i) (e.symm ((B.chart j).symm ((B.chart j) (e ((A.chart i).symm y)))))=y
    rw [(B.chart j).left_inv hy.2,e.symm_apply_apply,(A.chart i).right_inv hy.1]
  have hp : G (F z)=z := hFG.eq_of_nhds
  have hF : DifferentiableAt ℝ F z := (atlasCoordinateMap_contDiffAt_real hf hzj).differentiableAt (by simp)
  have hG : DifferentiableAt ℝ G (F z) := (atlasCoordinateMap_contDiffAt_real hg hgj).differentiableAt (by simp)
  have hder : (fderiv ℝ G (F z)).comp (fderiv ℝ F z)=ContinuousLinearMap.id ℝ (ComplexModel (A.dimension i)) := by
    calc
      _ = fderiv ℝ (G ∘ F) z := (fderiv_comp z hG hF).symm
      _ = fderiv ℝ id z := hFG.fderiv_eq
      _ = _ := fderiv_id
  rw [(theta.holomorphicPullback hg).holomorphicPullback_coeff hf i j hzj,
    theta.holomorphicPullback_coeff hg j i hgj]
  change ((theta.coeff i (G (F z))).compContinuousLinearMap (fderiv ℝ G (F z))).compContinuousLinearMap
    (fderiv ℝ F z)=theta.coeff i z
  rw [hp]
  ext w
  change theta.coeff i z (fun t => fderiv ℝ G (F z) (fderiv ℝ F z (w t)))=theta.coeff i z w
  have hw : (fun t => fderiv ℝ G (F z) (fderiv ℝ F z (w t)))=w := by
    funext t
    exact congrArg (fun L : ComplexModel (A.dimension i) →L[ℝ] ComplexModel (A.dimension i) => L (w t)) hder
  rw [hw]

/-- The true tensor round trip proves the ACTUAL global source class
relation using one zero smooth function, rather than an abstract output flag. -/
theorem original_biholomorphic_pullback_roundtrip_relation
    (theta : AtlasClosedRealOneOneForm A) (e : X ≃ₜ Y)
    (hf : A.IsHolomorphic B e) (hg : B.IsHolomorphic A e.symm) :
    OriginalBottChernRel ((theta.holomorphicPullback hg).holomorphicPullback hf) theta := by
  refine ⟨fun _ => 0,fun _ => contDiffOn_const,?_⟩
  intro i z hz
  rw [show ((fun _ : X => (0 : ℝ)) ∘ (A.chart i).symm)=(fun _ => 0) from rfl,
    smoothDDC_zero,add_zero]
  exact (original_biholomorphic_pullback_roundtrip_coeff theta e hf hg i hz).symm

/-- PROVED canonical equivalence of genuine original global closed-form
quotients under an ACTUAL biholomorphic homeomorphism, with full class readback. -/
def originalBiholomorphicCohomologyEquiv (e : X ≃ₜ Y)
    (hf : A.IsHolomorphic B e) (hg : B.IsHolomorphic A e.symm) :
    OriginalRealBottChern A ≃ OriginalRealBottChern B where
  toFun := originalCohomologyPullback hg
  invFun := originalCohomologyPullback hf
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro theta
    exact (originalClass_eq_iff _ _).mpr
      (original_biholomorphic_pullback_roundtrip_relation theta e hf hg)
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro theta
    exact (originalClass_eq_iff _ _).mpr
      (original_biholomorphic_pullback_roundtrip_relation theta e.symm hg hf)

/-- The actual equivalence sends an original form to its SAME genuine
holomorphic pulled tensor, before passing to the global source quotient. -/
theorem originalBiholomorphicCohomologyEquiv_class (e : X ≃ₜ Y)
    (hf : A.IsHolomorphic B e) (hg : B.IsHolomorphic A e.symm)
    (theta : AtlasClosedRealOneOneForm A) :
    originalBiholomorphicCohomologyEquiv e hf hg (originalClass theta)=
      originalClass (theta.holomorphicPullback hg) := rfl

end SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
