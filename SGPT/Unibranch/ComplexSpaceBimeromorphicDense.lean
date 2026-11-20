import SGPT.Unibranch.ComplexSpaceUnibranchPSHDensity
import SGPT.Unibranch.ComplexSpacePSHDensePullback

/-! Literal finite-locus transport under the actual original bimeromorphic
map. Blueprint: complex-space-bimeromorphic-dense.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace SGPT.Unibranch.SourceReducedComplexSpace

/-- Dense preimages for the ORIGINAL bimeromorphic morphism, using its
actual exceptional-set/open-immersion data internally. -/
theorem IsProperBimeromorphic.dense_preimage {X Y : SourceReducedComplexSpace}
    {f : Y ⟶ X} (hf : IsProperBimeromorphic f) {A : Set X.obj.left}
    (hA : Dense A) : Dense (f.hom.left.base ⁻¹' A) := by
  obtain ⟨_hproper,Z,_hZ,_hthin,hprethin,hiso⟩ := hf
  have hAc : interior Aᶜ = ∅ := by
    exact interior_eq_empty_iff_dense_compl.mpr (by simpa only [compl_compl] using hA)
  have h := hiso.interior_preimage_eq_empty hprethin hAc
  rw [preimage_compl] at h
  simpa only [compl_compl] using interior_eq_empty_iff_dense_compl.mp h

/-- The unbounded original PSH target condition manufactures density of
the SAME actual pulled-back finite locus. -/
theorem IsPSH.dense_finite_pullback_of_isProperBimeromorphic
    {X Y : SourceReducedComplexSpace} {φ : X.obj.left → EReal}
    (hφ : X.IsPSH φ) (hX : X.IsUnibranch) {f : Y ⟶ X}
    (hf : IsProperBimeromorphic f) :
    Dense {y : Y.obj.left | φ (f.hom.left.base y) ≠ ⊥} :=
  hf.dense_preimage (hφ.dense_finite_of_isUnibranch hX)

/-- The actual unbounded theta-PSH target condition manufactures density,
without requiring any source PSH or component certificate. -/
theorem IsThetaPSH.dense_finite_pullback_of_isProperBimeromorphic
    {X Y : SourceReducedComplexSpace} {θ : SpaceForm X 2} {φ : X.obj.left → EReal}
    (hφ : X.IsThetaPSH θ φ) (hX : X.IsUnibranch) {f : Y ⟶ X}
    (hf : IsProperBimeromorphic f) :
    Dense {y : Y.obj.left | φ (f.hom.left.base y) ≠ ⊥} :=
  hf.dense_preimage (hφ.dense_finite_of_isUnibranch hX)

/-- Every original source point, including poles, has a genuine local
ambient PSH pullback representative. Its finite witness is produced internally. -/
theorem IsPSH.locallyAmbient_pullback_of_isProperBimeromorphic
    {X Y : SourceReducedComplexSpace} {φ : X.obj.left → EReal}
    (hφ : X.IsPSH φ) (hX : X.IsUnibranch) {f : Y ⟶ X}
    (hf : IsProperBimeromorphic f) :
    ∀ y,Y.IsLocallyAmbientPSHAt (fun y => φ (f.hom.left.base y)) y := by
  exact locallyAmbientPSH_pullback_of_dense_finite hφ.2 f
    (hφ.dense_finite_pullback_of_isProperBimeromorphic hX hf)

end SGPT.Unibranch.SourceReducedComplexSpace
