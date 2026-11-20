import SGPT.Unibranch.ComplexSpaceBimeromorphicDense
import SGPT.Unibranch.ComplexSpaceModelComponents
import SGPT.Unibranch.ComplexSpaceThetaPSHPullbackFinite

/-! Actual unbounded theta-PSH pullback between original singular spaces.
Blueprint: complex-space-theta-bimeromorphic-pullback.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
namespace SGPT.Unibranch.SourceReducedComplexSpace

/-- The ORIGINAL unbounded theta-PSH predicate pulls back along the SAME
actual proper bimeromorphic map to an intrinsically unibranch target.
All source-model component nondegeneracy is produced, including poles. -/
theorem IsThetaPSH.pullback_of_isProperBimeromorphic
    {X Y : SourceReducedComplexSpace} {θ : SpaceForm X 2} {φ : X.obj.left → EReal}
    (hφ : X.IsThetaPSH θ φ) (hX : X.IsUnibranch) (f : Y ⟶ X)
    (hf : IsProperBimeromorphic f) :
    Y.IsThetaPSH (SpaceForm.pullback θ f) (fun y => φ (f.hom.left.base y)) := by
  have hdBase := hφ.dense_finite_pullback_of_isProperBimeromorphic hX hf
  intro y
  obtain ⟨e,he,-,g,hg,hres,hpsh⟩ := hφ (f.hom.left.base y)
  obtain ⟨A,hA,hconn⟩ := SpaceForm.morphismChartLift_connected_cover f e y he
  let hc : ∀ c : A.source.carrier,
      (⟨A.lift c.val.val,A.maps c.val.property⟩ : e.ambient) ∈ e.carrier := by
    intro c
    obtain ⟨b,hb,-⟩ := A.factor c
    have hval : (⟨A.lift c.val.val,A.maps c.val.property⟩ : e.ambient) = b.val :=
      Subtype.ext hb.symm
    rw [hval]
    exact b.property
  let F := analyticModelMorphism A.source.analytic e.analytic A.lift A.holomorphic A.maps hc
  let u : e.carrier → EReal := fun b => (g b.val.val : EReal)+φ (e.toPoint b)
  let v : A.source.carrier → EReal := fun c => u (F.hom.left.base c)
  have heq : v = (fun c : A.source.carrier =>
      ((g ∘ A.lift) c.val.val : EReal)+φ (f.hom.left.base (A.source.toPoint c))) := by
    funext c
    obtain ⟨b,hb,hpb⟩ := A.factor c
    have hFb : F.hom.left.base c = b := by
      apply Subtype.ext
      apply Subtype.ext
      exact hb.symm
    change (g ((F.hom.left.base c).val.val) : EReal)+φ (e.toPoint (F.hom.left.base c)) = _
    rw [hFb,hb,hpb]
    rfl
  have hdLocal := hdBase.preimage A.source.isOpenEmbedding_toPoint.isOpenMap
  have hd : Dense {c : A.source.carrier | v c ≠ ⊥} := by
    rw [heq]
    exact hdLocal.mono (fun c hc => EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _,hc⟩)
  have hsource : (sourceReducedComplexSpaceModel A.source.ambient A.source.carrier
      A.source.analytic).IsPSH v := by
    refine ⟨componentNondegenerate_model_of_dense_finite hd,?_⟩
    exact locallyAmbientPSH_pullback_of_dense_finite hpsh.2 F hd
  refine ⟨A.source,hA,hconn,g ∘ A.lift,
    hg.comp (A.holomorphic.restrict_scalars ℝ) A.maps,
    SpaceForm.pullback_restrictsTo_ddc θ f hg hres A.source A.holomorphic A.maps A.factor,?_⟩
  rw [← heq]
  exact hsource

end SGPT.Unibranch.SourceReducedComplexSpace
