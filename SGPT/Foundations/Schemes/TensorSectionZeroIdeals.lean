import SGPT.Foundations.Schemes.LineSectionZeroSubscheme
import SGPT.Foundations.Schemes.BundleMorphismGluing
import SGPT.Foundations.Schemes.LineBundleSectionRing

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The true restriction of an actual frame retains its original coefficient
map along the literal composite inclusion. -/
theorem bundleHomRestrictionIso_coefficients {X : Scheme.{u}} {L : X.Modules}
    {U V W : X.Opens} (e : LocalBundleFrame L U) (i : V ⟶ U) (j : W ⟶ V)
    (s : Γ(L, W)) :
    (show LocalBundleFrame L V from
      bundleHomRestrictionIso L (SheafOfModules.unit X.ringCatSheaf) i e).coefficients j s =
      e.coefficients (j ≫ i) s :=
  bundleHomRestriction_app L (SheafOfModules.unit X.ringCatSheaf) i e.hom (op (Over.mk j)) s

/-- Actual paired charts and true restricted tensor frames give the genuine
tensor-line atlas, without a global frame or affinity assumption. -/
def LineBundleAtlas.tensor {X : Scheme.{u}} {L M : X.Modules}
    (a : LineBundleAtlas L) (b : LineBundleAtlas M) : LineBundleAtlas (bundleTensor L M) where
  I := a.I × b.I
  opens ij := a.opens ij.1 ⊓ b.opens ij.2
  covers x := by
    obtain ⟨i, hi⟩ := a.covers x
    obtain ⟨j, hj⟩ := b.covers x
    exact ⟨(i, j), hi, hj⟩
  frame ij := by
    let U := a.opens ij.1 ⊓ b.opens ij.2
    let E : LocalBundleFrame L U :=
      bundleHomRestrictionIso L (SheafOfModules.unit X.ringCatSheaf)
        (Opens.infLELeft (a.opens ij.1) (b.opens ij.2)) (a.frame ij.1)
    let F : LocalBundleFrame M U :=
      bundleHomRestrictionIso M (SheafOfModules.unit X.ringCatSheaf)
        (Opens.infLERight (a.opens ij.1) (b.opens ij.2)) (b.frame ij.2)
    exact E.tensor F

/-- On ANY genuinely framed open, the SAME actual tensor-section evaluation
ideal is the product of the SAME original ideals, with no regularity premise. -/
theorem sectionZeroIdeal_tensorSection_eq_mul {X : Scheme.{u}} {L M : X.Modules}
    (s : Γ(L, ⊤)) (t : Γ(M, ⊤)) {U V : X.Opens}
    (e : LocalBundleFrame L U) (f : LocalBundleFrame M U) (i : V ⟶ U) :
    sectionZeroIdeal (bundleTensor L M) (tensorSection L M ⊤ s t) V =
      sectionZeroIdeal L s V * sectionZeroIdeal M t V := by
  have hc : (e.tensor f).coefficients i
      ((bundleTensor L M).presheaf.map V.leTop.op (tensorSection L M ⊤ s t)) =
      e.coefficients i (L.presheaf.map V.leTop.op s) *
        f.coefficients i (M.presheaf.map V.leTop.op t) := by
    change (e.tensor f).coefficients i
      ((bundleTensor L M).val.map V.leTop.op (tensorSection L M ⊤ s t)) =
      e.coefficients i (L.val.map V.leTop.op s) * f.coefficients i (M.val.map V.leTop.op t)
    rw [tensorSection_restrict, LocalBundleFrame.tensor_coefficients]
  rw [sectionZeroIdeal_eq_span_frame _ (e.tensor f) i, hc,
    sectionZeroIdeal_eq_span_frame s e i, sectionZeroIdeal_eq_span_frame t f i,
    Ideal.span_singleton_mul_span_singleton]

/-- Native actual ideal-sheaf equality, established on a genuine common
affine refinement. Scheme-theoretic tensor zeros multiply with no regularity. -/
theorem sectionZeroIdealSheaf_tensorSection {X : Scheme.{u}} {L M : X.Modules}
    (a : LineBundleAtlas L) (b : LineBundleAtlas M) (s : Γ(L, ⊤)) (t : Γ(M, ⊤)) :
    sectionZeroIdealSheaf (a.tensor b) (tensorSection L M ⊤ s t) =
      sectionZeroIdealSheaf a s * sectionZeroIdealSheaf b t := by
  let J := Σ i : a.I, Σ j : b.I, {U : X.affineOpens // U.val ≤ a.opens i ⊓ b.opens j}
  let U (k : J) : X.affineOpens := k.2.2.val
  have hcover : ∀ x : X, ∃ k : J, x ∈ (U k).val := by
    intro x
    obtain ⟨i, hi⟩ := a.covers x
    obtain ⟨j, hj⟩ := b.covers x
    obtain ⟨W, hW, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ a.opens i ⊓ b.opens j from ⟨hi, hj⟩)
    exact ⟨⟨i, j, ⟨⟨W, hW⟩, hWle⟩⟩, hxW⟩
  have hsup : (⨆ k : J, (U k).val) = ⊤ := by
    apply le_antisymm le_top
    intro x _
    obtain ⟨k, hk⟩ := hcover x
    exact Opens.mem_iSup.mpr ⟨k, hk⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U hsup
  intro k
  let E := bundleHomRestrictionIso L (SheafOfModules.unit X.ringCatSheaf)
    (Opens.infLELeft (a.opens k.1) (b.opens k.2.1)) (a.frame k.1)
  let F := bundleHomRestrictionIso M (SheafOfModules.unit X.ringCatSheaf)
    (Opens.infLERight (a.opens k.1) (b.opens k.2.1)) (b.frame k.2.1)
  exact sectionZeroIdeal_tensorSection_eq_mul s t E F (homOfLE k.2.2.property)

end
end SGPT.Foundations.Schemes
