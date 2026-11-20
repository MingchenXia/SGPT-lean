import SGPT.Unibranch.HironakaG1NoncompactSmoothComponentModel
import SGPT.Unibranch.ComplexSpaceUnibranchFibers
import SGPT.Unibranch.ComplexSpaceBimeromorphicDense

/-! Recover the actual graph dimension on the SAME native smooth source.
Existing native manifold reconstruction is reused; no new resolution construction.
Blueprint first: `prime-nov16-noncompact-common-model.tex`.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.PrimeNov16NativeManifold
open Set CategoryTheory TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaG11IntrinsicRegularOpenImmersion BlowupTowers
open SGPT.Unibranch SourceReducedComplexSpace
open scoped Topology Manifold ContDiff

/-- Connected smooth original geometry and ONE actual n-dimensional chart
recover an n-manifold model with a FULL original locally ringed isomorphism. -/
theorem exists_native_manifold_of_regular_dimension {Z : SourceReducedComplexSpace}
    [ConnectedSpace Z.obj.left] (hZ : Z.IsSmooth) {n : ℕ}
    (x : Z.obj.left) (hx : intrinsicRegularAtDim Z.obj x n) :
    ∃ M : CMfd.{0} n, Nonempty (OriginalNativeModification.wholeModel (n := n) M ≅ Z) := by
  obtain ⟨m, hm⟩ := OriginalSmoothDimension.exists_uniform_smooth_models hZ
  obtain ⟨V, i, hi, hp, hxV⟩ := hm x
  obtain ⟨W, j, hj, hq, hxW⟩ := hx
  have hmn : m = n :=
    OriginalSmoothDimension.smooth_model_dimension_eq V W i j hi hj hp hq x hxV hxW
  subst m
  exact HironakaG1NoncompactSmoothComponentModel.exists_native_manifold_model_of_uniform hm

/-- A genuine connected dense good subset of an actual resolution internally
supplies connectedness and its exact graph dimension on the SAME source. -/
theorem exists_native_manifold_of_connected_dense_subset
    {A R : SourceReducedComplexSpace} (ρ : R ⟶ A) (hρ : IsResolution ρ)
    {T G : Set A.obj.left} (hiso : IsIsoOver ρ T)
    (hG : IsConnected G) (hd : Dense G) (hGT : G ⊆ T)
    {n : ℕ} (x : A.obj.left) (hx : x ∈ G)
    (hn : intrinsicRegularAtDim A.obj x n) :
    ∃ M : CMfd.{0} n, Nonempty (OriginalNativeModification.wholeModel (n := n) M ≅ R) := by
  have hconn : IsConnected (ρ.hom.left.base ⁻¹' G) :=
    hiso.isConnected_preimage_of_subset hG hGT
  have hdense : Dense (ρ.hom.left.base ⁻¹' G) := hρ.2.dense_preimage hd
  have hRuniv : IsConnected (univ : Set R.obj.left) := hdense.closure_eq ▸ hconn.closure
  let : ConnectedSpace R.obj.left := connectedSpace_iff_univ.mpr hRuniv
  obtain ⟨V, j, hj, hjr, hjρ, _hjρr⟩ := hiso
  obtain ⟨z, hz⟩ := hρ.2.surjective x
  have hzj : z ∈ range j.base := by
    rw [hjr]
    change ρ.hom.left.base z ∈ T
    rw [hz]
    exact hGT hx
  obtain ⟨v, hv⟩ := hzj
  have hcomm : j ≫ R.obj.hom = (j ≫ ρ.hom.left) ≫ A.obj.hom := by
    rw [Category.assoc, Over.w ρ.hom]
  have hdim : intrinsicRegularAtDim R.obj (j.base v) n := by
    apply (intrinsicRegularAtDim_iff_of_openImmersions j (j ≫ ρ.hom.left)
      hj hjρ hcomm v n).mpr
    change intrinsicRegularAtDim A.obj (ρ.hom.left.base (j.base v)) n
    rw [hv, hz]
    exact hn
  exact exists_native_manifold_of_regular_dimension hρ.1 (j.base v) hdim

end SGPT.PSH.PrimeNov16NativeManifold
