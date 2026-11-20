import SGPT.Unibranch.HironakaG10NativeNullstellensatz
import SGPT.Unibranch.HironakaG10ChowTrackedDatum
import SGPT.Foundations.Analysis.Pending.HironakaG10CoherentSupportIdeal
import SGPT.Foundations.Analysis.Pending.HironakaG10StrictIdealSourceRadical

/-!
# Germ strict membership of a coherent family and its actual reduced support

The reduced-support ideal is the original intrinsic native stalk image.
This compares the exact algebraic germ criteria; the geometric closure
identification for a strict transform is a separate statement.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace SGPT.Unibranch.HironakaG10ReducedSupportStrictMembership
open SGPT.Foundations.Analysis.Pending HironakaG10HirIdealGerms
  HironakaIntrinsicReducedCentreOpenPullback HironakaG10CoherentSupportIdeal
  HironakaG10StrictIdealSourceRadical
open SGPT.Unibranch.HironakaG10NativeNullstellensatz
  SGPT.Unibranch.HironakaG10ChowTrackedDatum
  SGPT.Unibranch.HironakaG10HirLocalFlattener

/-- At points of the actual open domain, a coherent ideal family and its
reduced support give identical germ strict-transform membership conditions. -/
theorem onStrictTransform_iff_reduced_support
    {X X' : SourceReducedComplexSpace} (σ : X' ⟶ X)
    (V : Set X.obj.left) (hV : IsOpen V)
    (J : ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x))
    (hJ : IsLocallyFinitelyGeneratedOn X.obj.left V J)
    (x' : X'.obj.left) (hx : σ.hom.left.base x' ∈ V)
    (D : Ideal (X.obj.left.presheaf.stalk (σ.hom.left.base x'))) :
    OnStrictTransform σ x' (J (σ.hom.left.base x')) D ↔
      OnStrictTransform σ x'
        (intrinsicCentreStalkRange X.obj.left {y | y ∈ V ∧ J y ≠ ⊤}
          (σ.hom.left.base x')) D := by
  let x := σ.hom.left.base x'
  let C : Set X.obj.left := {y | y ∈ V ∧ J y ≠ ⊤}
  let I := intrinsicCentreStalkRange X.obj.left C x
  have hJI : J x ≤ I := le_intrinsicCentreStalkRange_support X.obj.left V J hJ x hx
  have hC : ∀ᶠ y in 𝓝 x, J y ≠ ⊤ → y ∈ C := by
    filter_upwards [hV.mem_nhds hx] with y hy hproper
    exact ⟨hy, hproper⟩
  have hIJ : I ≤ (J x).radical :=
    intrinsicCentre_le_radical_of_support_subset V C hV J hJ x hx hC
  have hJIrad : J x ≤ I.radical := hJI.trans Ideal.le_radical
  constructor
  · intro h G hG hD htop
    apply h G hG hD
    exact (strictIdeal_eq_top_iff_of_source_radical_bounds
      (σ.hom.left.stalkMap x').hom (J x) I D G hJIrad hIJ).mpr htop
  · intro h G hG hD htop
    apply h G hG hD
    exact (strictIdeal_eq_top_iff_of_source_radical_bounds
      (σ.hom.left.stalkMap x').hom (J x) I D G hJIrad hIJ).mp htop

/-- The same exact germ criterion applies to the original nonreduced
local-flattener ideal and the intrinsic ideal of its actual support. -/
theorem onStrictTransform_flattener_iff_reduced_support
    {X X' Y : SourceReducedComplexSpace} {f : Y ⟶ X}
    (Z : LocalFlattener f) (σ : X' ⟶ X) (x' : X'.obj.left)
    (hx : σ.hom.left.base x' ∈ Z.V)
    (D : Ideal (X.obj.left.presheaf.stalk (σ.hom.left.base x'))) :
    OnStrictTransform σ x' (Z.H (σ.hom.left.base x')) D ↔
      OnStrictTransform σ x'
        (intrinsicCentreStalkRange X.obj.left Z.support (σ.hom.left.base x')) D :=
  onStrictTransform_iff_reduced_support σ Z.V Z.isOpen Z.H Z.fg x' hx D

end SGPT.Unibranch.HironakaG10ReducedSupportStrictMembership
