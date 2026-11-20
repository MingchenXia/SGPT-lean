import SGPT.Unibranch.ComplexIsoOverNativeModel

/-! Actual original open immersions preserve SAME genuine native model dimension and density.
Blueprint: complex-open-native-models.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.SourceReducedComplexSpace

variable {X Y : SourceReducedComplexSpace}

theorem isIsoOver_range_of_isOpenImmersion (j : Y ⟶ X)
    (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) :
    IsIsoOver j (range j.hom.left.base) := by
  refine ⟨Y.obj.left,𝟙 _,inferInstance,?_,?_,?_⟩
  · ext y
    constructor
    · intro _
      exact ⟨y,rfl⟩
    · intro _
      exact ⟨y,rfl⟩
  · simpa only [Category.id_comp] using hj
  · simp only [Category.id_comp]

theorem native_model_of_isOpenImmersion (j : Y ⟶ X)
    (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) (y : Y.obj.left) (d : ℕ)
    (V : Opens (ComplexModel d))
    (i : ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel d) V ⟶ X.obj.left)
    (hi : LocallyRingedSpace.IsOpenImmersion i) (hp : i ≫ X.obj.hom = ambientPointMap d V)
    (hx : j.hom.left.base y ∈ range i.base) :
    ∃ (T : Opens (ComplexModel d))
      (a : ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel d) T ⟶ Y.obj.left),
      LocallyRingedSpace.IsOpenImmersion a ∧ a ≫ Y.obj.hom = ambientPointMap d T ∧
      y ∈ range a.base :=
  (isIsoOver_range_of_isOpenImmersion j hj).native_model_of_target y ⟨y,rfl⟩ d V i hi hp hx

theorem dense_native_models_of_isOpenImmersion (j : Y ⟶ X)
    (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) (d : ℕ)
    (hdense : Dense {x : X.obj.left | ∃ (V : Opens (ComplexModel d))
      (i : ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel d) V ⟶ X.obj.left),
      LocallyRingedSpace.IsOpenImmersion i ∧ i ≫ X.obj.hom = ambientPointMap d V ∧ x ∈ range i.base}) :
    Dense {y : Y.obj.left | ∃ (V : Opens (ComplexModel d))
      (i : ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel d) V ⟶ Y.obj.left),
      LocallyRingedSpace.IsOpenImmersion i ∧ i ≫ Y.obj.hom = ambientPointMap d V ∧ y ∈ range i.base} := by
  apply (hdense.preimage hj.base_open.isOpenMap).mono
  intro y hy
  obtain ⟨V,i,hi,hp,hyi⟩ := hy
  exact native_model_of_isOpenImmersion j hj y d V i hi hp hyi

end SGPT.Unibranch.SourceReducedComplexSpace
