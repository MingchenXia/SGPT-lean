import SGPT.PSH.GeometricQOpenBiholomorphicNaturality
import SGPT.PSH.GeometricQPreimageComposition

/-! Coefficient naturality for actual open biholomorphic squares. The original
atlas consumer constructs the square and every numerical equality internally. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.SourceLogSingularitiesDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff
universe u

section Topological
variable {M N S T : Type u}
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace S] [TopologicalSpace T]

/-- Actual bijections of both original open images and a commuting SAME-point
square prove the full inverse-image open equality. -/
theorem open_eq_preimage_of_square (e : M ≃ₜ N) (W : Opens M) (V : Opens N)
    (w : S ≃ₜ W) (v : T ≃ₜ V) (r : S ≃ₜ T)
    (h : ∀ s,e (w s).val=(v (r s)).val) : W=preimageOpen e V := by
  apply Opens.ext
  ext x
  constructor
  · intro hx
    let s := w.symm ⟨x,hx⟩
    have hs : (w s).val=x := congrArg Subtype.val (w.apply_symm_apply ⟨x,hx⟩)
    have hh := h s
    rw [hs] at hh
    change e x∈V
    exact hh.symm ▸ (v (r s)).property
  · intro hx
    change e x∈V at hx
    let t := v.symm ⟨e x,hx⟩
    let s := r.symm t
    have hr : r s=t := r.apply_symm_apply t
    have hv : (v t).val=e x := congrArg Subtype.val (v.apply_symm_apply ⟨e x,hx⟩)
    have hh := h s
    rw [hr,hv] at hh
    have hs : (w s).val=x := e.injective hh
    exact hs ▸ (w s).property

end Topological

section EqualDimension
variable {n : ℕ} {M N S T : Type u}
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace S] [TopologicalSpace T]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]
  [ChartedSpace (ComplexModel n) S] [IsComplexManifold n S]
  [ChartedSpace (ComplexModel n) T] [IsComplexManifold n T]

/-- FULL actual rational coefficient naturality of a genuine commuting open
square. The open equality is derived from the bijective square, not assumed. -/
theorem geometricQOpen_square (D : EffectiveGeometricQDivisor n N)
    (e : M ≃ₜ N) (W : Opens M) (V : Opens N)
    (w : S ≃ₜ W) (v : T ≃ₜ V) (r : S ≃ₜ T)
    (he : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e.symm)
    (hw : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ w)
    (hwi : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ w.symm)
    (hv : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ v)
    (hvi : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ v.symm)
    (hr : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ r)
    (hri : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ r.symm)
    (h : ∀ s,e (w s).val=(v (r s)).val) :
    geometricQDivisorBiholomorphicPreimage
      (geometricQDivisorOpenRestrictionAnyDimension
        (geometricQDivisorBiholomorphicPreimage D e he hei) W) w hw hwi =
    geometricQDivisorBiholomorphicPreimage
      (geometricQDivisorBiholomorphicPreimage
        (geometricQDivisorOpenRestrictionAnyDimension D V) v hv hvi) r hr hri := by
  have hW := open_eq_preimage_of_square e W V w v r h
  subst W
  rw [openRestriction_biholomorphic_naturality,
    geometricQPreimage_comp,geometricQPreimage_comp]
  apply geometricQPreimage_congr
  intro s
  apply Subtype.ext
  exact h s

end EqualDimension

section IndependentDimensions
variable {a b c d : ℕ} {M N S T : Type u}
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace S] [TopologicalSpace T]
  [ChartedSpace (ComplexModel a) M] [IsComplexManifold a M]
  [ChartedSpace (ComplexModel b) N] [IsComplexManifold b N]
  [ChartedSpace (ComplexModel c) S] [IsComplexManifold c S]
  [ChartedSpace (ComplexModel d) T] [IsComplexManifold d T]

/-- Honest pure substitution of independent original component dimensions;
no fixed uniform native dimension is required by the original atlas consumer. -/
theorem geometricQOpen_square_of_dimensions
    (hab : a=b) (hca : c=a) (hdb : d=b) (hcd : c=d)
    (D : EffectiveGeometricQDivisor b N)
    (e : M ≃ₜ N) (W : Opens M) (V : Opens N)
    (w : S ≃ₜ W) (v : T ≃ₜ V) (r : S ≃ₜ T)
    (he : ContMDiff 𝓘(ℂ,ComplexModel a) 𝓘(ℂ,ComplexModel b) ∞ e)
    (hei : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel a) ∞ e.symm)
    (hw : ContMDiff 𝓘(ℂ,ComplexModel c) 𝓘(ℂ,ComplexModel a) ∞ w)
    (hwi : ContMDiff 𝓘(ℂ,ComplexModel a) 𝓘(ℂ,ComplexModel c) ∞ w.symm)
    (hv : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel b) ∞ v)
    (hvi : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel d) ∞ v.symm)
    (hr : ContMDiff 𝓘(ℂ,ComplexModel c) 𝓘(ℂ,ComplexModel d) ∞ r)
    (hri : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel c) ∞ r.symm)
    (h : ∀ s,e (w s).val=(v (r s)).val) :
    geometricQDivisorBiholomorphicPreimageOfDimensionEq hca
      (geometricQDivisorOpenRestrictionAnyDimension
        (geometricQDivisorBiholomorphicPreimageOfDimensionEq hab D e he hei) W) w hw hwi =
    geometricQDivisorBiholomorphicPreimageOfDimensionEq hcd
      (geometricQDivisorBiholomorphicPreimageOfDimensionEq hdb
        (geometricQDivisorOpenRestrictionAnyDimension D V) v hv hvi) r hr hri := by
  subst b
  subst c
  subst d
  exact geometricQOpen_square D e W V w v r he hei hw hwi hv hvi hr hri h

end IndependentDimensions
end SGPT.PSH.SourceLogSingularitiesDraft
