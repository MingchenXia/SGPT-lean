import SGPT.Trace.BertiniHyperplaneQuotientFrame
import SGPT.Trace.BertiniSmoothConormal

/-! Exact original native defining-section equation in the original
pulled-back coordinate-section frame, beyond equality of zero sets. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini

open Bundle Set Filter
open scoped Manifold ContDiff Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.AnalyticSectionProducts
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace

variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Actual original physical affine formula for the actual native generating
family. Its projective coordinates internally supply the nonzero frame. -/
theorem nativeSectionFamily_affine_formula
    (E : HermitianHolomorphicLineBundle.{0,0} n X)
    (s : Fin (N + 1) → HolomorphicSections (n := n) E.Fiber)
    (hGen : ∀ x : X, ∃ i, s i x ≠ 0)
    (j : Fin (N + 1)) (x : X)
    (hx : sourceNativeFiniteSectionProjectiveMap E s hGen x ∈ (affineChart j).source) :
    s j x ≠ 0 ∧ ∀ a : Fin (N + 1) → ℂ,
      (∑ i, a i • s i x) =
        pairing a (affineLift j (affineChart j (sourceNativeFiniteSectionProjectiveMap E s hGen x))) • s j x := by
  classical
  let e : AtlasFrame E := ⟨trivializationAt ℂ E.Fiber x, inferInstance⟩
  let := e.property
  have he : x ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ E.Fiber x
  let A := e.val.linearEquivAt ℂ x he
  let u : Fin (N + 1) → ℂ := fun i => A (s i x)
  have hu : u ≠ 0 := by
    intro hzero
    obtain ⟨i, hi⟩ := hGen x
    apply hi
    apply A.injective
    change u i = A 0
    rw [map_zero]
    exact congrFun hzero i
  have hmap : sourceNativeFiniteSectionProjectiveMap E s hGen x =
      ComplexProjectiveSpace.mk u hu := sourceNativeFiniteSectionProjectiveMap_frame E s hGen e x he
  have huj : u j ≠ 0 := by
    rw [hmap] at hx
    exact (mk_mem_affineChart_source_iff j hu).mp hx
  have hlift : affineLift j (affineChart j (sourceNativeFiniteSectionProjectiveMap E s hGen x)) =
      (u j)⁻¹ • u := by
    rw [hmap, affineChart_mk j hu huj, affineLift_affineRatio j huj]
  refine ⟨?_, ?_⟩
  · intro hzero
    apply huj
    change A (s j x) = 0
    rw [hzero, map_zero]
  · intro a
    apply A.injective
    rw [map_smul, smul_eq_mul, hlift, pairing_smul_right]
    have hsum : A (∑ i, a i • s i x) = pairing a u := by
      simp only [map_sum, map_smul, smul_eq_mul, pairing]
      rfl
    rw [hsum]
    change pairing a u = ((u j)⁻¹ * pairing a u) * u j
    field_simp

/-- The literal actual pulled-back native coordinate section is a nonzero
physical frame on the original projective-coordinate domain. -/
theorem nativeBertiniCoordinateSection_ne_zero
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
      X (ComplexProjectiveSpace N) ∞) (j : Fin (N + 1)) (x : X)
    (hx : p x ∈ (affineChart j).source) : nativeBertiniCoordinateSection p j x ≠ 0 := by
  apply (nativeSectionFamily_affine_formula (nativeBertiniHyperplaneBundle p)
    (nativeBertiniCoordinateSection p) (nativeBertiniCoordinateSection_generating p) j x ?_).1
  rwa [nativeBertiniCoordinateSection_projectiveMap]

theorem nativeBertiniAffineSection_apply
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
      X (ComplexProjectiveSpace N) ∞) (i : Fin (N + 1)) (ζ : ComplexModel N) (x : X) :
    nativeBertiniAffineSection p i ζ x =
      ∑ k, affineLift i ζ k • nativeBertiniCoordinateSection p k x := by
  let ev : HolomorphicSections (n := n) (nativeBertiniHyperplaneBundle p).Fiber →ₗ[ℂ]
      (nativeBertiniHyperplaneBundle p).Fiber x := {
    toFun s := s x
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  change ev (∑ k, affineLift i ζ k • nativeBertiniCoordinateSection p k) = _
  rw [map_sum]
  rfl

/-- The original defining section is the exact original incidence equation
times its original pulled-back coordinate-section frame in the SAME fibre. -/
theorem nativeBertiniAffineSection_eq_originalEquation_smul
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
      X (ComplexProjectiveSpace N) ∞) (i : Fin (N + 1)) (ζ : ComplexModel N)
    (j : Fin (N + 1)) (x : X) (hx : p x ∈ (affineChart j).source) :
    nativeBertiniAffineSection p i ζ x =
      pairing (affineLift i ζ) (affineLift j (affineChart j (p x))) •
        nativeBertiniCoordinateSection p j x := by
  rw [nativeBertiniAffineSection_apply]
  have h := (nativeSectionFamily_affine_formula (nativeBertiniHyperplaneBundle p)
    (nativeBertiniCoordinateSection p) (nativeBertiniCoordinateSection_generating p) j x
    (by rwa [nativeBertiniCoordinateSection_projectiveMap])).2 (affineLift i ζ)
  rwa [nativeBertiniCoordinateSection_projectiveMap] at h

/-- Scalar coordinate of the SAME original native line fibre normalized
by the SAME original nonzero physical vector. -/
def nativeNonzeroFiberScalarEquiv (E : HermitianHolomorphicLineBundle.{0,0} n X)
    (x : X) (u : E.Fiber x) (hu : u ≠ 0) : E.Fiber x ≃ₗ[ℂ] ℂ := by
  let e : AtlasFrame E := ⟨trivializationAt ℂ E.Fiber x, inferInstance⟩
  let := e.property
  let A := e.val.linearEquivAt ℂ x (mem_baseSet_trivializationAt ℂ E.Fiber x)
  have hc : A u ≠ 0 := by
    intro hz
    apply hu
    apply A.injective
    rw [hz, map_zero]
  exact A.trans (LinearEquiv.smulOfNeZero ℂ ℂ (A u) hc).symm

theorem nativeNonzeroFiberScalarEquiv_self (E : HermitianHolomorphicLineBundle.{0,0} n X)
    (x : X) (u : E.Fiber x) (hu : u ≠ 0) : nativeNonzeroFiberScalarEquiv E x u hu u = 1 := by
  unfold nativeNonzeroFiberScalarEquiv
  dsimp only [LinearEquiv.trans_apply]
  let A := (trivializationAt ℂ E.Fiber x).linearEquivAt ℂ x
    (mem_baseSet_trivializationAt ℂ E.Fiber x)
  change (A u)⁻¹ * (A u) = (1 : ℂ)
  exact inv_mul_cancel₀ (by
    intro hz
    apply hu
    apply (trivializationAt ℂ E.Fiber x).linearEquivAt ℂ x
      (mem_baseSet_trivializationAt ℂ E.Fiber x) |>.injective
    rw [hz, map_zero])

theorem nativeNonzeroFiberScalarEquiv_symm_apply (E : HermitianHolomorphicLineBundle.{0,0} n X)
    (x : X) (u : E.Fiber x) (hu : u ≠ 0) (a : ℂ) :
    (nativeNonzeroFiberScalarEquiv E x u hu).symm a = a • u := by
  apply (nativeNonzeroFiberScalarEquiv E x u hu).injective
  rw [LinearEquiv.apply_symm_apply, map_smul, nativeNonzeroFiberScalarEquiv_self,
    smul_eq_mul, mul_one]

/-- The produced original physical scalar coordinate reads as the literal
ratio in EVERY genuine original native fibre frame. -/
theorem nativeNonzeroFiberScalarEquiv_in_frame (E : HermitianHolomorphicLineBundle.{0,0} n X)
    (x : X) (u : E.Fiber x) (hu : u ≠ 0) (f : AtlasFrame E) (hx : x ∈ f.val.baseSet)
    (v : E.Fiber x) :
    nativeNonzeroFiberScalarEquiv E x u hu v = (f.val ⟨x, v⟩).2 / (f.val ⟨x, u⟩).2 := by
  let := f.property
  let A := f.val.linearEquivAt ℂ x hx
  have hc : A u ≠ 0 := by
    intro hz
    apply hu
    apply A.injective
    rw [hz, map_zero]
  have hv : v = (A v / A u) • u := by
    apply A.injective
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hc]
  conv_lhs => rw [hv]
  rw [map_smul, nativeNonzeroFiberScalarEquiv_self, smul_eq_mul, mul_one]
  rfl

/-- The original pulled-back native coordinate vector gives an actual
scalar coordinate on the SAME original hyperplane fibre. -/
def nativeBertiniCoordinateFiberEquiv
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
      X (ComplexProjectiveSpace N) ∞) (j : Fin (N + 1)) (x : X)
    (hx : p x ∈ (affineChart j).source) : (nativeBertiniHyperplaneBundle p).Fiber x ≃ₗ[ℂ] ℂ :=
  nativeNonzeroFiberScalarEquiv (nativeBertiniHyperplaneBundle p) x
    (nativeBertiniCoordinateSection p j x) (nativeBertiniCoordinateSection_ne_zero p j x hx)

theorem nativeBertiniCoordinateFiberEquiv_coordinate
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
      X (ComplexProjectiveSpace N) ∞) (j : Fin (N + 1)) (x : X)
    (hx : p x ∈ (affineChart j).source) :
    nativeBertiniCoordinateFiberEquiv p j x hx (nativeBertiniCoordinateSection p j x) = 1 :=
  nativeNonzeroFiberScalarEquiv_self _ _ _ _

/-- The actual original defining section has exactly the original incidence
coefficient in the actual physical original coordinate-section fibre frame. -/
theorem nativeBertiniCoordinateFiberEquiv_definingSection
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
      X (ComplexProjectiveSpace N) ∞) (i : Fin (N + 1)) (ζ : ComplexModel N)
    (j : Fin (N + 1)) (x : X) (hx : p x ∈ (affineChart j).source) :
    nativeBertiniCoordinateFiberEquiv p j x hx (nativeBertiniAffineSection p i ζ x) =
      pairing (affineLift i ζ) (affineLift j (affineChart j (p x))) := by
  rw [nativeBertiniAffineSection_eq_originalEquation_smul p i ζ j x hx,
    map_smul, nativeBertiniCoordinateFiberEquiv_coordinate, smul_eq_mul, mul_one]

end SGPT.Trace.Bertini
