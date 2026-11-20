import SGPT.Projective.SourceFamilyFiberEquivalence

/-! Actual local fiber formulas remove all pointwise frame/scalar choices. -/
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

/-- A nonzero actual frame coefficient spans the SAME original physical
complex line, with its literal scalar coefficient. -/
theorem sourceNativeLineFiber_eq_coefficient_div_smul
    (E : HermitianHolomorphicLineBundle.{0,0} n X) (e : AtlasFrame E)
    (x : X) (he : x ∈ e.val.baseSet) (u : E.Fiber x)
    (hu : (e.val ⟨x, u⟩).2 ≠ 0) (v : E.Fiber x) :
    v = ((e.val ⟨x, v⟩).2 / (e.val ⟨x, u⟩).2) • u := by
  apply (e.val.linearEquivAt ℂ x he).injective
  rw [map_smul]
  change (e.val ⟨x, v⟩).2 =
    ((e.val ⟨x, v⟩).2 / (e.val ⟨x, u⟩).2) * (e.val ⟨x, u⟩).2
  field_simp [hu]

/-- A genuine complex-linear map agreeing on the actual generating family
is the internally manufactured actual fiber map. This is true uniqueness,
so no local compatibility of the chosen frames/scalars is assumed. -/
theorem sourceNativeGeneratingFamilies_fiberEquiv_unique
    (E F : HermitianHolomorphicLineBundle.{0,0} n X)
    (s : Fin (N+1) → HolomorphicSections (n := n) E.Fiber)
    (t : Fin (N+1) → HolomorphicSections (n := n) F.Fiber)
    (hs : ∀ x : X, ∃ j : Fin (N+1), s j x ≠ 0)
    (ht : ∀ x : X, ∃ j : Fin (N+1), t j x ≠ 0)
    (hSame : ∀ x : X, sourceNativeFiniteSectionProjectiveMap E s hs x =
      sourceNativeFiniteSectionProjectiveMap F t ht x) (x : X)
    (Ψ : E.Fiber x →ₗ[ℂ] F.Fiber x) (hΨ : ∀ j : Fin (N+1), Ψ (s j x) = t j x) :
    Ψ = (sourceNativeGeneratingFamilies_fiberEquiv E F s t hs ht hSame x).toLinearMap := by
  ext v
  obtain ⟨j, hj⟩ := hs x
  let e : AtlasFrame E := ⟨trivializationAt ℂ E.Fiber x, inferInstance⟩
  have he : x ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ E.Fiber x
  let A := e.val.linearEquivAt ℂ x he
  have hA : (e.val ⟨x, s j x⟩).2 ≠ 0 := by
    intro hz
    apply hj
    apply A.injective
    exact hz.trans (map_zero A).symm
  have hv := sourceNativeLineFiber_eq_coefficient_div_smul E e x he (s j x) hA v
  rw [hv, map_smul, map_smul, hΨ]
  exact congrArg (fun w : F.Fiber x =>
    ((e.val ⟨x, v⟩).2 / (e.val ⟨x, s j x⟩).2) • w)
      (sourceNativeGeneratingFamilies_fiberEquiv_section E F s t hs ht hSame x j).symm

/-- The manufactured actual fiber equivalence has the literal quotient
formula in EVERY pair of actual frames wherever one actual source section
coefficient is nonzero. This proves independence of every pointwise choice. -/
theorem sourceNativeGeneratingFamilies_fiberEquiv_frame_formula
    (E F : HermitianHolomorphicLineBundle.{0,0} n X)
    (s : Fin (N+1) → HolomorphicSections (n := n) E.Fiber)
    (t : Fin (N+1) → HolomorphicSections (n := n) F.Fiber)
    (hs : ∀ x : X, ∃ j : Fin (N+1), s j x ≠ 0)
    (ht : ∀ x : X, ∃ j : Fin (N+1), t j x ≠ 0)
    (hSame : ∀ x : X, sourceNativeFiniteSectionProjectiveMap E s hs x =
      sourceNativeFiniteSectionProjectiveMap F t ht x)
    (e : AtlasFrame E) (f : AtlasFrame F) (x : X)
    (he : x ∈ e.val.baseSet) (hf : x ∈ f.val.baseSet) (j : Fin (N+1))
    (hj : (e.val ⟨x, s j x⟩).2 ≠ 0) (v : E.Fiber x) :
    (f.val ⟨x, sourceNativeGeneratingFamilies_fiberEquiv E F s t hs ht hSame x v⟩).2 =
      ((f.val ⟨x, t j x⟩).2 / (e.val ⟨x, s j x⟩).2) * (e.val ⟨x, v⟩).2 := by
  let Φ := sourceNativeGeneratingFamilies_fiberEquiv E F s t hs ht hSame x
  let A := e.val.linearEquivAt ℂ x he
  let B := f.val.linearEquivAt ℂ x hf
  have hv := sourceNativeLineFiber_eq_coefficient_div_smul E e x he (s j x) hj v
  have hΦ : Φ (s j x) = t j x := sourceNativeGeneratingFamilies_fiberEquiv_section E F s t hs ht hSame x j
  change B (Φ v) = (B (t j x) / A (s j x)) * A v
  have hv' : v = (A v / A (s j x)) • s j x := hv
  calc
    B (Φ v) = B (Φ ((A v / A (s j x)) • s j x)) := congrArg (fun w => B (Φ w)) hv'
    _ = (A v / A (s j x)) * B (t j x) := by rw [map_smul, hΦ, map_smul, smul_eq_mul]
    _ = _ := by ring

/-- The actual inverse is EXACTLY the fiber map produced by the swapped
actual generating families. This uses genuine one-dimensional fiber
linearity, not regularity of any internal choice. -/
theorem sourceNativeGeneratingFamilies_fiberEquiv_symm_eq_swapped
    (E F : HermitianHolomorphicLineBundle.{0,0} n X)
    (s : Fin (N+1) → HolomorphicSections (n := n) E.Fiber)
    (t : Fin (N+1) → HolomorphicSections (n := n) F.Fiber)
    (hs : ∀ x : X, ∃ j : Fin (N+1), s j x ≠ 0)
    (ht : ∀ x : X, ∃ j : Fin (N+1), t j x ≠ 0)
    (hSame : ∀ x : X, sourceNativeFiniteSectionProjectiveMap E s hs x =
      sourceNativeFiniteSectionProjectiveMap F t ht x) (x : X) (v : F.Fiber x) :
    (sourceNativeGeneratingFamilies_fiberEquiv E F s t hs ht hSame x).symm v =
      sourceNativeGeneratingFamilies_fiberEquiv F E t s ht hs (fun y => (hSame y).symm) x v := by
  obtain ⟨j, hj⟩ := ht x
  let f : AtlasFrame F := ⟨trivializationAt ℂ F.Fiber x, inferInstance⟩
  have hf : x ∈ f.val.baseSet := mem_baseSet_trivializationAt ℂ F.Fiber x
  let B := f.val.linearEquivAt ℂ x hf
  have hB : (f.val ⟨x, t j x⟩).2 ≠ 0 := by
    intro hz
    apply hj
    apply B.injective
    exact hz.trans (map_zero B).symm
  have hv := sourceNativeLineFiber_eq_coefficient_div_smul F f x hf (t j x) hB v
  let Φ := sourceNativeGeneratingFamilies_fiberEquiv E F s t hs ht hSame x
  let Ψ := sourceNativeGeneratingFamilies_fiberEquiv F E t s ht hs (fun y => (hSame y).symm) x
  change Φ.symm v = Ψ v
  rw [hv, map_smul, map_smul]
  congr 1
  calc
    Φ.symm (t j x) = Φ.symm (Φ (s j x)) := congrArg Φ.symm
      (sourceNativeGeneratingFamilies_fiberEquiv_section E F s t hs ht hSame x j).symm
    _ = s j x := Φ.symm_apply_apply (s j x)
    _ = Ψ (t j x) := (sourceNativeGeneratingFamilies_fiberEquiv_section F E t s ht hs
      (fun y => (hSame y).symm) x j).symm

end SGPT.Bergman.NativeKodairaPullback
