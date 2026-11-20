import SGPT.Unibranch.HironakaG10GenChow
import SGPT.Unibranch.HironakaG10SourceCSet
import SGPT.Unibranch.ComplexSpaceAnalyticPreimage
import SGPT.Unibranch.EmbeddedCommonResolutionGeneral

/-!
# Cancellation of proper bimeromorphic morphisms of reduced complex spaces

Run 0081 lane G10EP (SGPT consumer contract G10-05-01.sgpt).  Blueprint:
`hironaka-g10ep-chow-bridge.tex`.

If `g ≫ f = σ` with `f` and `σ` proper bimeromorphic, then `g` is proper bimeromorphic
(`isProperBimeromorphic_of_comp`).  No smoothness of any of the three spaces is assumed: the
source of `f` may be an arbitrary (singular, normal, ...) reduced complex space.  This is what turns
a Chow domination `g ≫ f = σ` of a proper bimeromorphic `f` into a proper bimeromorphic model
`g` over the source of `f`, as used by the book's `def:modelvalcurr`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace SGPT.Unibranch.HironakaG10EpBimeromorphicCancel

open SourceReducedComplexSpace HironakaG10ChowTowerDomination HironakaG10ChowNativeIsoCriterion
  HironakaG10GenChow

noncomputable section

/-- **Cancellation of proper bimeromorphic morphisms.**  Let `f : Y ⟶ X` and `σ : X' ⟶ X` be
proper bimeromorphic morphisms of reduced complex spaces and `g : X' ⟶ Y` with `g ≫ f = σ`.  Then
`g` is proper bimeromorphic: it is an isomorphism over the complement of `f⁻¹(T ∪ S)`, where `T`
and `S` are the bad sets of `f` and `σ`. -/
theorem isProperBimeromorphic_of_comp {X Y X' : SourceReducedComplexSpace} {f : Y ⟶ X}
    {σ : X' ⟶ X} (g : X' ⟶ Y) (hf : IsProperBimeromorphic f) (hσ : IsProperBimeromorphic σ)
    (hg : g ≫ f = σ) : IsProperBimeromorphic g := by
  let : T2Space Y.obj.left := Y.property.1
  have hgf : ∀ x, f.hom.left.base (g.hom.left.base x) = σ.hom.left.base x := fun x =>
    congrArg (fun H : X' ⟶ X => H.hom.left.base x) hg
  have hgp : IsProperMap g.hom.left.base := by
    have hσp : IsProperMap (fun x => f.hom.left.base (g.hom.left.base x)) := by
      have h : (fun x => f.hom.left.base (g.hom.left.base x)) = σ.hom.left.base :=
        funext hgf
      rw [h]
      exact hσ.1
    exact isProperMap_of_comp_of_t2 (X := X'.obj.left) (Y := Y.obj.left) (Z := X.obj.left)
      g.hom.left.base.hom.continuous f.hom.left.base.hom.continuous hσp
  have hfo := isOpenOffThin_of_isProperBimeromorphic hf
  have hσo := isOpenOffThin_of_isProperBimeromorphic hσ
  obtain ⟨-, T, hTa, hTi, -, hfT⟩ := hf
  obtain ⟨-, S, hSa, hSi, -, hσS⟩ := hσ
  have hTc : IsClosed T := isClosed_of_isIsoOver hfT
  have hSc : IsClosed S := isClosed_of_isIsoOver hσS
  let U : Set X.obj.left := (T ∪ S)ᶜ
  have hUo : IsOpen U := (hTc.union hSc).isOpen_compl
  have hUT : U ⊆ Tᶜ := fun x hx h => hx (Or.inl h)
  have hUS : U ⊆ Sᶜ := fun x hx h => hx (Or.inr h)
  have hfU : IsIsoOver f U := IsIsoOver.of_isOpen_subset hfT hUo hUT
  have hσU : IsIsoOver σ U := IsIsoOver.of_isOpen_subset hσS hUo hUS
  have hinj := injOn_of_isIsoOver hfU
  have hthin : interior (T ∪ S) = ∅ := by
    rw [interior_union_isClosed_of_interior_empty hTc hSi, hTi]
  have hpre : g.hom.left.base ⁻¹' (f.hom.left.base ⁻¹' (T ∪ S)) =
      σ.hom.left.base ⁻¹' (T ∪ S) := by
    ext x
    simp only [mem_preimage]
    rw [hgf]
  refine ⟨hgp, f.hom.left.base ⁻¹' (T ∪ S),
    (HironakaG10SourceCSet.analytic_union hTa hSa).preimage f,
    hfo.interior_preimage_eq_empty hthin, ?_, ?_⟩
  · rw [hpre]
    exact hσo.interior_preimage_eq_empty hthin
  · rw [← preimage_compl]
    obtain ⟨V, j, hj, hjr, hjσ, hjσr⟩ := hσU
    obtain ⟨V', k, hk, hkr, hkf, -⟩ := hfU
    let : LocallyRingedSpace.IsOpenImmersion j := hj
    let : LocallyRingedSpace.IsOpenImmersion k := hk
    let : LocallyRingedSpace.IsOpenImmersion (j ≫ σ.hom.left) := hjσ
    let : LocallyRingedSpace.IsOpenImmersion (k ≫ f.hom.left) := hkf
    have hjU : ∀ v, σ.hom.left.base (j.base v) ∈ U := by
      intro v
      have h : j.base v ∈ range j.base := ⟨v, rfl⟩
      rw [hjr] at h
      exact h
    have hrange : range (j ≫ g.hom.left).base ⊆ range k.base := by
      rintro _ ⟨v, rfl⟩
      rw [hkr]
      change f.hom.left.base (g.hom.left.base (j.base v)) ∈ U
      rw [hgf]
      exact hjU v
    let l := LocallyRingedSpace.IsOpenImmersion.lift k (j ≫ g.hom.left) hrange
    have hl : l ≫ k = j ≫ g.hom.left :=
      LocallyRingedSpace.IsOpenImmersion.lift_fac k (j ≫ g.hom.left) hrange
    have hgfL : g.hom.left ≫ f.hom.left = σ.hom.left :=
      congrArg (fun H : X' ⟶ X => H.hom.left) hg
    have hlf : l ≫ (k ≫ f.hom.left) = j ≫ σ.hom.left := by
      rw [← Category.assoc, hl, Category.assoc, hgfL]
    have : LocallyRingedSpace.IsOpenImmersion (l ≫ (k ≫ f.hom.left)) := by
      rw [hlf]
      infer_instance
    have : LocallyRingedSpace.IsOpenImmersion l :=
      HironakaG10ChowStrictTransformCalculus.isOpenImmersion_of_comp l (k ≫ f.hom.left)
    refine ⟨V, j, hj, ?_, ?_, ?_⟩
    · rw [hjr]
      ext x
      simp only [mem_preimage]
      rw [hgf]
    · rw [← hl]
      infer_instance
    · apply Subset.antisymm
      · rintro _ ⟨v, rfl⟩
        change f.hom.left.base (g.hom.left.base (j.base v)) ∈ U
        rw [hgf]
        exact hjU v
      · intro y hy
        have hfy : f.hom.left.base y ∈ range (j ≫ σ.hom.left).base := by
          rw [hjσr]
          exact hy
        obtain ⟨v, hv⟩ := hfy
        refine ⟨v, ?_⟩
        have hv' : σ.hom.left.base (j.base v) = f.hom.left.base y := hv
        apply hinj
        · change f.hom.left.base (g.hom.left.base (j.base v)) ∈ U
          rw [hgf]
          exact hjU v
        · exact hy
        · change f.hom.left.base (g.hom.left.base (j.base v)) = f.hom.left.base y
          rw [hgf, hv']

end

end SGPT.Unibranch.HironakaG10EpBimeromorphicCancel
