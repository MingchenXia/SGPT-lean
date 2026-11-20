import SGPT.Projective.SourceFiniteSectionMap

/-! Actual fiber isomorphisms manufactured from equal actual projective maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Bergman.NativeKodairaPullback
open Bundle Set
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.AnalyticSectionProducts
open HermitianHolomorphicLineBundle SGPT.Projective
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff
variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Equality of actual generating-family projective maps produces one actual
nonzero scalar relating the ENTIRE original coordinate family in any two
actual frames at the same original point. -/
theorem sourceNativeGeneratingFamilies_exists_frameScalar
    (E F : HermitianHolomorphicLineBundle.{0,0} n X)
    (s : Fin (N+1) → HolomorphicSections (n := n) E.Fiber)
    (t : Fin (N+1) → HolomorphicSections (n := n) F.Fiber)
    (hs : ∀ x : X, ∃ j : Fin (N+1), s j x ≠ 0)
    (ht : ∀ x : X, ∃ j : Fin (N+1), t j x ≠ 0)
    (hSame : ∀ x : X, sourceNativeFiniteSectionProjectiveMap E s hs x =
      sourceNativeFiniteSectionProjectiveMap F t ht x)
    (e : AtlasFrame E) (f : AtlasFrame F) (x : X)
    (he : x ∈ e.val.baseSet) (hf : x ∈ f.val.baseSet) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ j : Fin (N+1),
      (f.val ⟨x, t j x⟩).2 = c * (e.val ⟨x, s j x⟩).2 := by
  have h := hSame x
  rw [sourceNativeFiniteSectionProjectiveMap_frame E s hs e x he,
    sourceNativeFiniteSectionProjectiveMap_frame F t ht f x hf] at h
  obtain ⟨c, hc, hcoord⟩ := ComplexProjectiveSpace.exists_eq_smul_of_mk_eq h
  refine ⟨c, hc, fun j => ?_⟩
  exact congrFun hcoord j

/-- The ACTUAL fiberwise complex-linear isomorphism. Source/target frames and
one common nonzero scalar are chosen internally from actual generation and
actual projective-map equality. No bundle isomorphism or local compatibility
certificate is supplied. Holomorphy is proved separately by frame formulas. -/
def sourceNativeGeneratingFamilies_fiberEquiv
    (E F : HermitianHolomorphicLineBundle.{0,0} n X)
    (s : Fin (N+1) → HolomorphicSections (n := n) E.Fiber)
    (t : Fin (N+1) → HolomorphicSections (n := n) F.Fiber)
    (hs : ∀ x : X, ∃ j : Fin (N+1), s j x ≠ 0)
    (ht : ∀ x : X, ∃ j : Fin (N+1), t j x ≠ 0)
    (hSame : ∀ x : X, sourceNativeFiniteSectionProjectiveMap E s hs x =
      sourceNativeFiniteSectionProjectiveMap F t ht x) (x : X) : E.Fiber x ≃ₗ[ℂ] F.Fiber x := by
  let e : AtlasFrame E := ⟨trivializationAt ℂ E.Fiber x, inferInstance⟩
  let f : AtlasFrame F := ⟨trivializationAt ℂ F.Fiber x, inferInstance⟩
  let he : x ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ E.Fiber x
  let hf : x ∈ f.val.baseSet := mem_baseSet_trivializationAt ℂ F.Fiber x
  let A := e.val.linearEquivAt ℂ x he
  let B := f.val.linearEquivAt ℂ x hf
  let scalar := sourceNativeGeneratingFamilies_exists_frameScalar E F s t hs ht hSame e f x he hf
  let c := scalar.choose
  have hc : c ≠ 0 := scalar.choose_spec.1
  exact
    { toFun := fun v => B.symm (c * A v)
      invFun := fun w => A.symm (c⁻¹ * B w)
      left_inv := by
        intro v
        apply A.injective
        simp only [LinearEquiv.apply_symm_apply]
        field_simp [hc]
      right_inv := by
        intro w
        apply B.injective
        simp only [LinearEquiv.apply_symm_apply]
        field_simp [hc]
      map_add' := by
        intro v w
        apply B.injective
        simp only [LinearEquiv.apply_symm_apply, map_add, mul_add]
      map_smul' := by
        intro d v
        apply B.injective
        simp only [LinearEquiv.apply_symm_apply, map_smul, smul_eq_mul, RingHom.id_apply]
        ring }

/-- Every actual original generating section value is sent to its partner.
The same actual fiber map works for the entire finite family. -/
theorem sourceNativeGeneratingFamilies_fiberEquiv_section
    (E F : HermitianHolomorphicLineBundle.{0,0} n X)
    (s : Fin (N+1) → HolomorphicSections (n := n) E.Fiber)
    (t : Fin (N+1) → HolomorphicSections (n := n) F.Fiber)
    (hs : ∀ x : X, ∃ j : Fin (N+1), s j x ≠ 0)
    (ht : ∀ x : X, ∃ j : Fin (N+1), t j x ≠ 0)
    (hSame : ∀ x : X, sourceNativeFiniteSectionProjectiveMap E s hs x =
      sourceNativeFiniteSectionProjectiveMap F t ht x) (x : X) (j : Fin (N+1)) :
    sourceNativeGeneratingFamilies_fiberEquiv E F s t hs ht hSame x (s j x) = t j x := by
  let e : AtlasFrame E := ⟨trivializationAt ℂ E.Fiber x, inferInstance⟩
  let f : AtlasFrame F := ⟨trivializationAt ℂ F.Fiber x, inferInstance⟩
  let he : x ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ E.Fiber x
  let hf : x ∈ f.val.baseSet := mem_baseSet_trivializationAt ℂ F.Fiber x
  let scalar := sourceNativeGeneratingFamilies_exists_frameScalar E F s t hs ht hSame e f x he hf
  apply (f.val.linearEquivAt ℂ x hf).injective
  change (f.val.linearEquivAt ℂ x hf)
    ((f.val.linearEquivAt ℂ x hf).symm
      (scalar.choose * (e.val.linearEquivAt ℂ x he) (s j x))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact (scalar.choose_spec.2 j).symm

end SGPT.Bergman.NativeKodairaPullback
