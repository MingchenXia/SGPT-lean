import SGPT.Unibranch.NativeNov16NormalizationExistence
import SGPT.Unibranch.ComplexSpaceLocalEmbedding
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Maps.Proper.Basic

/-! Actual disjoint analytic windows over WHOLE finite fibres.
Blueprint FIRST: native-nov16-finite-fibre-chart-windows.tex.
No local potential, strict positivity, Kahler or extension certificate is input.
-/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace SGPT.Unibranch.NativeNov16FiniteFibreChartWindows

theorem exists_disjoint_chart_windows {X Y : SourceReducedComplexSpace}
    (p : Y ⟶ X) (hp : IsProperMap p.hom.left.base)
    (x : X.obj.left) (hf : (p.hom.left.base ⁻¹' {x}).Finite) :
    ∃ (V : Opens X.obj.left)
      (O : (p.hom.left.base ⁻¹' {x}) → Opens Y.obj.left),
      x ∈ V ∧
      (∀ q, q.val ∈ O q) ∧
      (Pairwise fun q r => Disjoint (O q : Set Y.obj.left) (O r : Set Y.obj.left)) ∧
      (∀ q, (O q : Set Y.obj.left) ⊆ range (LocalEmbedding.ofPoint Y q.val).toPoint) ∧
      ∀ y : Y.obj.left, p.hom.left.base y ∈ V →
        ∃! q : (p.hom.left.base ⁻¹' {x}), y ∈ O q := by
  classical
  have : T2Space Y.obj.left.toPresheafedSpace := Y.property.1
  obtain ⟨U,hU,hDisj⟩ := hf.t2_separation
  let O : (p.hom.left.base ⁻¹' {x}) → Opens Y.obj.left := fun q =>
    ⟨U q.val ∩ range (LocalEmbedding.ofPoint Y q.val).toPoint,
      (hU q.val).2.inter (LocalEmbedding.isOpen_range_toPoint _)⟩
  have hMem (q : (p.hom.left.base ⁻¹' {x})) : q.val ∈ O q :=
    ⟨(hU q.val).1,LocalEmbedding.mem_range_ofPoint Y q.val⟩
  have hPair : Pairwise fun q r =>
      Disjoint (O q : Set Y.obj.left) (O r : Set Y.obj.left) := by
    intro q r hqr
    apply (hDisj q.property r.property (fun h => hqr (Subtype.ext h))).mono
      (show (O q : Set Y.obj.left) ⊆ U q.val from inter_subset_left)
      (show (O r : Set Y.obj.left) ⊆ U r.val from inter_subset_left)
  let A : Set Y.obj.left := ⋃ q, (O q : Set Y.obj.left)
  have hA : IsOpen A := isOpen_iUnion fun q => (O q).isOpen
  let V : Opens X.obj.left :=
    ⟨(p.hom.left.base '' Aᶜ)ᶜ,(hp.isClosedMap _ hA.isClosed_compl).isOpen_compl⟩
  have hx : x ∈ V := by
    rintro ⟨y,hy,hpy⟩
    let q : p.hom.left.base ⁻¹' {x} := ⟨y,hpy⟩
    exact hy (mem_iUnion.mpr ⟨q,hMem q⟩)
  have hCover (y : Y.obj.left) (hy : p.hom.left.base y ∈ V) : y ∈ A := by
    by_contra hya
    exact hy ⟨y,hya,rfl⟩
  refine ⟨V,O,hx,hMem,hPair,?_,?_⟩
  · intro q
    exact inter_subset_right
  · intro y hy
    obtain ⟨q,hq⟩ := mem_iUnion.mp (hCover y hy)
    refine ⟨q,hq,?_⟩
    intro r hr
    by_contra hrq
    exact Set.disjoint_left.mp (hPair hrq) hr hq

theorem normalization_disjoint_chart_windows (X : SourceReducedComplexSpace)
    (x : X.obj.left) :
    let N := NativeNov16NormalizationSpace.source X
    let p := NativeNov16NormalizationSpace.projection X
    ∃ (V : Opens X.obj.left)
      (O : (p.hom.left.base ⁻¹' {x}) → Opens N.obj.left),
      x ∈ V ∧
      (∀ q, q.val ∈ O q) ∧
      (Pairwise fun q r => Disjoint (O q : Set N.obj.left) (O r : Set N.obj.left)) ∧
      (∀ q, (O q : Set N.obj.left) ⊆ range (LocalEmbedding.ofPoint N q.val).toPoint) ∧
      ∀ y : N.obj.left, p.hom.left.base y ∈ V →
        ∃! q : (p.hom.left.base ⁻¹' {x}), y ∈ O q := by
  exact exists_disjoint_chart_windows (NativeNov16NormalizationSpace.projection X)
    (NativeNov16NormalizationSpace.normal_proper_finite_surjective X).2.1 x
    ((NativeNov16NormalizationSpace.normal_proper_finite_surjective X).2.2.1 x)

end SGPT.Unibranch.NativeNov16FiniteFibreChartWindows
