import SGPT.Unibranch.HironakaG1NativeIsoOverDisjointCover
import SGPT.Unibranch.OriginalAnalyticCover

/-! Actual full-map proper-bimeromorphic locality. Full blueprint first. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace SGPT.PSH.PrimeNov16OriginalModificationLocality
open SGPT.Unibranch SourceReducedComplexSpace

theorem isProperBimeromorphic_of_actual_covers
    {ι : Type} {Y S : SourceReducedComplexSpace} {A Z : ι → SourceReducedComplexSpace}
    (F : S ⟶ Y) (hp : IsProperMap F.hom.left.base)
    (j : ∀ i, A i ⟶ Y) (k : ∀ i, Z i ⟶ S) (g : ∀ i, Z i ⟶ A i)
    (hj : ∀ i, LocallyRingedSpace.IsOpenImmersion (j i).hom.left)
    (hk : ∀ i, LocallyRingedSpace.IsOpenImmersion (k i).hom.left)
    (hjcover : ∀ y : Y.obj.left, ∃ (i : ι) (a : (A i).obj.left), (j i).hom.left.base a = y)
    (hkcover : ∀ s : S.obj.left, ∃ (i : ι) (z : (Z i).obj.left), (k i).hom.left.base z = s)
    (hdisj : Pairwise (fun i r => Disjoint (range (j i).hom.left.base) (range (j r).hom.left.base)))
    (hsq : ∀ i, k i ≫ F = g i ≫ j i)
    (hg : ∀ i, IsProperBimeromorphic (g i)) : IsProperBimeromorphic F := by
  choose E hEa hEt hpre hiso using fun i => (hg i).2
  let D := OriginalAnalyticCover.unionImages j E
  have hDa : Y.IsAnalyticSubset D :=
    OriginalAnalyticCover.unionImages_isAnalyticSubset j hj hjcover hdisj E hEa
  have hDt : interior D = ∅ :=
    OriginalAnalyticCover.unionImages_interior_eq_empty j hj hjcover hdisj E hEt
  have hDpre (i : ι) : (j i).hom.left.base ⁻¹' D = E i :=
    OriginalAnalyticCover.preimage_unionImages_eq j hj hdisj E i
  have hlocal (i : ι) : (k i).hom.left.base ⁻¹' (F.hom.left.base ⁻¹' D) =
      (g i).hom.left.base ⁻¹' E i :=
    (congrArg (fun H : Z i ⟶ Y => H.hom.left.base ⁻¹' D) (hsq i)).trans
      (congrArg (fun C : Set (A i).obj.left => (g i).hom.left.base ⁻¹' C) (hDpre i))
  have hthin : interior (F.hom.left.base ⁻¹' D) = ∅ :=
    OriginalAnalyticCover.interior_eq_empty_of_openImmersion_cover k hk hkcover _
      (fun i => (congrArg interior (hlocal i)).trans (hpre i))
  have hgood (i : ι) : IsIsoOver (g i) ((j i).hom.left.base ⁻¹' Dᶜ) := by
    have heq : (j i).hom.left.base ⁻¹' Dᶜ = (E i)ᶜ :=
      (preimage_compl).trans (congrArg compl (hDpre i))
    exact heq.symm ▸ hiso i
  have hglobal : IsIsoOver F Dᶜ :=
    HironakaG1NativeIsoOverDisjointCover.isIsoOver_of_disjoint_cover F j k g hj hk
      hjcover hkcover hdisj hsq Dᶜ hDa.isClosed.isOpen_compl hgood
  exact ⟨hp, D, hDa, hDt, hthin, hglobal⟩

end SGPT.PSH.PrimeNov16OriginalModificationLocality
