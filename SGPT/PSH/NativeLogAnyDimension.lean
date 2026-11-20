import SGPT.PSH.NativeGeometricLogPullback
import SGPT.PSH.BiholomorphicGeometricQPullback

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open scoped Topology Manifold ContDiff

universe u

/-- Actual reduced-component open restriction in positive dimension; the
zero branch uses the EXISTING genuine empty prime-family divisor. -/
def geometricQDivisorOpenRestrictionAnyDimension {n : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (D : EffectiveGeometricQDivisor n M) (U : Opens M) :
    EffectiveGeometricQDivisor n U := by
  cases n with
  | zero => exact emptyGeometricQDivisor 0 U
  | succ m => exact geometricQDivisorOpenRestriction D U

/-- The ENTIRE accepted positive-dimensional restriction is unchanged. -/
theorem geometricQDivisorOpenRestrictionAnyDimension_succ {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    (D : EffectiveGeometricQDivisor (m + 1) M) (U : Opens M) :
    geometricQDivisorOpenRestrictionAnyDimension D U = geometricQDivisorOpenRestriction D U := rfl

theorem geometricQDivisorOpenRestrictionAnyDimension_support {n : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (D : EffectiveGeometricQDivisor n M) (U : Opens M) :
    (geometricQDivisorOpenRestrictionAnyDimension D U).support =
      (Subtype.val : U → M) ⁻¹' D.support := by
  cases n with
  | zero =>
    change (emptyGeometricQDivisor 0 U).support = _
    rw [emptyGeometricQDivisor_support, D.support_eq_empty_of_dimension_zero, preimage_empty]
  | succ m => exact geometricQDivisorOpenRestriction_support D U

open Classical in
/-- The LITERAL complete native source condition in ANY dimension: original
QPSH, one open with DISTINCT actual primes, positive rational weights, ENTIRE
restricted coefficient field, SAME equations at EVERY reduced stalk, and one
real bound and pole-inclusive log equality on ALL that SAME open. -/
def NativeHasLogSingularitiesAlongAnyDimension {n : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (D : EffectiveGeometricQDivisor n M) (u : M → EReal) : Prop :=
  (VariableComplexAtlas.ofFixedModel n M).IsQPSH u ∧
    ∀ x : M, ∃ U : Opens M, x ∈ U ∧
      ∃ (r : ℕ) (W : Fin r → GeometricPrimeCarrier n U)
        (a : Fin r → ℚ) (p : Fin r → U → ℂ) (R : U → ℝ) (C : ℝ),
        Function.Injective W ∧ (∀ i, 0 < a i) ∧
        (∀ i y, HolomorphicAt n (p i) y) ∧
        (∀ i y b, (vanishingIdeal (n := n) (W i).val).mem y b ↔
          IsInSpanAt (n := n) (· = p i) y b) ∧
        (∀ A : GeometricPrimeCarrier n U,
          (geometricQDivisorOpenRestrictionAnyDimension D U).coefficient A =
            ∑ i, if W i = A then a i else 0) ∧
        0 ≤ C ∧ (∀ y, |R y| ≤ C) ∧
        ∀ y : U, u y =
          (∑ i, ((a i : ℝ) : EReal) * logNormSq (p i y)) + (R y : EReal)

/-- EXACT equivalence of EVERY field of the accepted positive-dimensional
predicate; no one-way proxy or support-only condition replaces it. -/
theorem nativeHasLogSingularitiesAlongAnyDimension_succ_iff {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    (D : EffectiveGeometricQDivisor (m + 1) M) (u : M → EReal) :
    NativeHasLogSingularitiesAlongAnyDimension D u ↔ NativeHasLogSingularitiesAlong D u := Iff.rfl

/-- The actual ORIGINAL modification internally supplies upstairs QPSH and
ALL local log fields, including the genuine empty-prime zero-dimensional branch. -/
theorem NativeHasLogSingularitiesAlongAnyDimension.comp_native_analyticModification
    {n : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]
    {D : EffectiveGeometricQDivisor n N} {u : N → EReal}
    (hu : NativeHasLogSingularitiesAlongAnyDimension D u) {π : M → N}
    (hπ : IsAnalyticModification (n := n) π) :
    NativeHasLogSingularitiesAlongAnyDimension
      (geometricQDivisorModificationPullbackAnyDimension D hπ) (u ∘ π) := by
  classical
  cases n with
  | zero =>
    refine ⟨hu.1.comp_native_analyticModification hπ, ?_⟩
    intro x
    obtain ⟨U, hxU, r, W, a, p, R, C, _hW, _ha, _hp, _hideal, _hcoeff, hC, hR, hlog⟩ := hu.2 (π x)
    let V : Opens M := ⟨π ⁻¹' (U : Set N), U.isOpen.preimage hπ.1.continuous⟩
    let F : V → U := fun z => ⟨π z, z.property⟩
    have hreal (z : U) : u z = (R z : EReal) := by
      have hz := hlog z
      have hsum : (∑ i, ((a i : ℝ) : EReal) * logNormSq (p i z)) = 0 :=
        Finset.sum_eq_zero (fun i _hi => isEmptyElim (W i))
      rwa [hsum, zero_add] at hz
    refine ⟨V, hxU, 0, (fun i => Fin.elim0 i), (fun i => Fin.elim0 i),
      (fun i => Fin.elim0 i), (fun z => R (F z)), C,
      (fun i => Fin.elim0 i), (fun i => Fin.elim0 i),
      (fun i => Fin.elim0 i), (fun i => Fin.elim0 i),
      (fun A => isEmptyElim A), hC, (fun z => hR (F z)), ?_⟩
    intro z
    simpa only [F, Function.comp_apply, Finset.univ_eq_empty, Finset.sum_empty, zero_add] using hreal (F z)
  | succ m =>
    apply (nativeHasLogSingularitiesAlongAnyDimension_succ_iff _ _).mpr
    exact ((nativeHasLogSingularitiesAlongAnyDimension_succ_iff D u).mp hu).comp_native_analyticModification hπ

/-- Actual biholomorphism supplies its full modification internally and the
ENTIRE genuine rational preimage, preserving all-dimensional logarithmic data. -/
theorem NativeHasLogSingularitiesAlongAnyDimension.comp_biholomorphic
    {n : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]
    {D : EffectiveGeometricQDivisor n N} {u : N → EReal}
    (hu : NativeHasLogSingularitiesAlongAnyDimension D u) (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm) :
    NativeHasLogSingularitiesAlongAnyDimension
      (geometricQDivisorBiholomorphicPreimage D e he hei) (u ∘ e) := by
  have h := hu.comp_native_analyticModification (nativeAnalyticModification_of_biholomorphic e he hei)
  rwa [geometricQDivisorModificationPullbackAnyDimension_biholomorphic] at h

end SGPT.PSH
