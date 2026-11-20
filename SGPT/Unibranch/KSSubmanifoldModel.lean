import SGPT.Unibranch.HironakaG1NoncompactSmoothComponentModel
import SGPT.Unibranch.OriginalNativeManifoldOpenImage
import SGPT.Foundations.Analysis.Pending.SubmanifoldCodRestrict

/-!
# A connected closed complex submanifold as a complex manifold and as a complex space

A closed complex submanifold `V` of a complex manifold `N` carries two structures used
in Appendix B of the book (`appendix_unibranch.tex`):

* the complex manifold `V` (flattening charts, `SubmanifoldChartedSpace.chartedSpace`), viewed as
  the complex space `wholeModel V = (V, 𝒪_V)`;
* the reduced closed subspace `(V, 𝒪_N / 𝓘_V)` (`SourceReducedComplexSpace.ofClosedAnalytic`),
  which is the source of the embedded resolutions of the project (`thm:res`, G11a).

`wholeModelIso` identifies them (for `V` connected): the identity of points underlies an
isomorphism of complex spaces.  The inverse is produced from the existing native manifold model
of the smooth complex space `(V, 𝒪_N/𝓘_V)`
(`HironakaG1NoncompactSmoothComponentModel.exists_connected_native_manifold_model`), holomorphy of
point maps of morphisms of whole models (`OriginalNativeManifoldOpenImage.pointMap_holomorphic`)
and holomorphy of maps into a closed submanifold (`SubmanifoldCodRestrict.contMDiff_codRestrict`);
both composites are identities on points, hence identities
(`SourceReducedComplexSpace.morphism_eq_of_pointwise_eq`).

This is what turns an embedded resolution `(V, 𝒪/𝓘_V) → X` into a proper bimeromorphic morphism
`wholeModel V → X` from the compact Kähler *manifold* `V`, as required by `cor:PSH` and
`def:unibranch:L212`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
  SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspaceMaps

namespace SGPT.Unibranch.KSSubmanifoldModel

open SourceReducedComplexSpace OriginalNativeModification

variable {n d : ℕ} {N : Type} [TopologicalSpace N] [ChartedSpace (ComplexModel n) N]
  [IsComplexManifold n N] {V : Set N}

/-- The reduced closed subspace `(V, 𝒪_N/𝓘_V)` of a closed complex submanifold. -/
abbrev subspace (hV : IsClosedSubmanifold n V) : SourceReducedComplexSpace :=
  ofClosedAnalytic V (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hV)

/-- The inclusion `V → N` as a morphism of complex spaces `(V, 𝒪/𝓘_V) → (N, 𝒪_N)`. -/
def subspaceInclusion (hV : IsClosedSubmanifold n V) : subspace hV ⟶ wholeModel (n := n) N :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap (f := (id : N → N)) contMDiff_id (C := V) (D := (univ : Set N))
      (fun _ _ => mem_univ _))
    (actualSubspaceMap_point contMDiff_id (fun _ _ => mem_univ _)))

section Instances

variable [ChartedSpace (ComplexModel d) V] [IsComplexManifold d V]

/-- The identity of points `V → V`, as a morphism of complex spaces from the manifold `V` to the
reduced closed subspace `(V, 𝒪/𝓘_V)`, given that the inclusion is holomorphic. -/
def toSubspace (hV : IsClosedSubmanifold n V)
    (hval : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : V → N)) :
    wholeModel (n := d) V ⟶ subspace hV :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap hval (C := (univ : Set V)) (D := V) (fun y _ => y.property))
    (actualSubspaceMap_point hval (fun y _ => y.property)))

theorem toSubspace_base (hV : IsClosedSubmanifold n V)
    (hval : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : V → N))
    (p : (wholeModel (n := d) V).obj.left) :
    ((toSubspace hV hval).hom.left.base p).val = p.val.val := rfl

/-- **The manifold `V` and the complex space `(V, 𝒪/𝓘_V)` are isomorphic**, by the identity
of points, for a connected closed complex submanifold whose manifold structure makes the
inclusion holomorphic and the holomorphic maps into `V` exactly those into `N` with values
in `V`. -/
theorem isIso_toSubspace [ConnectedSpace V] (hV : IsClosedSubmanifold n V)
    (hval : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : V → N))
    (hcod : ∀ (m : ℕ) (P : BlowupTowers.CMfd.{0} m) (f : P → N),
      ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f → ∀ hf : ∀ y, f y ∈ V,
        ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel d) ∞
          (fun y => (⟨f y, hf y⟩ : V))) :
    IsIso (toSubspace hV hval) := by
  have hsmooth : (subspace hV).IsSmooth := isSmooth_ofClosedAnalytic_of_isClosedSubmanifold hV
  have : ConnectedSpace (subspace hV).obj.left := inferInstanceAs (ConnectedSpace V)
  obtain ⟨m, P, ⟨I⟩⟩ :=
    HironakaG1NoncompactSmoothComponentModel.exists_connected_native_manifold_model hsmooth
  let τ : P → N := OriginalNativeManifoldOpenImage.pointMap (I.hom ≫ subspaceInclusion hV)
  have hτ : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ τ :=
    OriginalNativeManifoldOpenImage.pointMap_holomorphic _
  have hτval : ∀ x : P, τ x = (I.hom.hom.left.base ⟨x, mem_univ x⟩).val := fun _ => rfl
  have hτV : ∀ x : P, τ x ∈ V := fun x => by
    rw [hτval]
    exact (I.hom.hom.left.base ⟨x, mem_univ x⟩).property
  have hρ := hcod m P τ hτ hτV
  let inv : subspace hV ⟶ wholeModel (n := d) V := I.inv ≫ nativeMorphism hρ
  have hIinv : ∀ q, I.hom.hom.left.base (I.inv.hom.left.base q) = q := fun q =>
    congrArg (fun f : subspace hV ⟶ subspace hV => f.hom.left.base q) I.inv_hom_id
  refine ⟨inv, ?_, ?_⟩
  · apply morphism_eq_of_pointwise_eq
    intro p
    apply Subtype.ext
    apply Subtype.ext
    change τ (I.inv.hom.left.base ((toSubspace hV hval).hom.left.base p)).val = p.val.val
    exact (hτval _).trans ((congrArg Subtype.val (hIinv _)).trans (toSubspace_base hV hval p))
  · apply morphism_eq_of_pointwise_eq
    intro x
    apply Subtype.ext
    change τ (I.inv.hom.left.base x).val = x.val
    exact (hτval _).trans (congrArg Subtype.val (hIinv x))

/-- The isomorphism `wholeModel V ≅ (V, 𝒪/𝓘_V)`. -/
def wholeModelIso [ConnectedSpace V] (hV : IsClosedSubmanifold n V)
    (hval : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : V → N))
    (hcod : ∀ (m : ℕ) (P : BlowupTowers.CMfd.{0} m) (f : P → N),
      ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f → ∀ hf : ∀ y, f y ∈ V,
        ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel d) ∞
          (fun y => (⟨f y, hf y⟩ : V))) :
    wholeModel (n := d) V ≅ subspace hV :=
  have := isIso_toSubspace hV hval hcod
  asIso (toSubspace hV hval)

@[simp] theorem wholeModelIso_hom [ConnectedSpace V] (hV : IsClosedSubmanifold n V)
    (hval : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : V → N))
    (hcod : ∀ (m : ℕ) (P : BlowupTowers.CMfd.{0} m) (f : P → N),
      ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f → ∀ hf : ∀ y, f y ∈ V,
        ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel d) ∞
          (fun y => (⟨f y, hf y⟩ : V))) :
    (wholeModelIso hV hval hcod).hom = toSubspace hV hval := rfl

end Instances

/-! ### The flattening manifold structure of a submanifold -/

section Flattening

variable (hd : d ≤ n) (hreg : ∀ y ∈ V, RegularAtDim (n := n) V y d)

include hd hreg in
/-- The flattening charts satisfy the hypotheses of `isIso_toSubspace`. -/
theorem flattening_codRestrict :
    letI := SubmanifoldChartedSpace.chartedSpace hd hreg
    ∀ (m : ℕ) (P : BlowupTowers.CMfd.{0} m) (f : P → N),
      ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f → ∀ hf : ∀ y, f y ∈ V,
        ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel d) ∞
          (fun y => (⟨f y, hf y⟩ : V)) := by
  intro m P f hf hfV
  exact SubmanifoldCodRestrict.contMDiff_codRestrict hd hreg hf hfV

end Flattening

end SGPT.Unibranch.KSSubmanifoldModel
