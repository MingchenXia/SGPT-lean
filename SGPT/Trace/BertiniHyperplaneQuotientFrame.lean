import SGPT.Trace.BertiniQuotientFrame
import SGPT.Trace.BertiniSetting
import SGPT.Projective.SourceNativeCoordinateFamily

/-!+# Quotient frames for the ACTUAL original hyperplane sections

The original map to projective space pulls back the independently constructed
native O(1) and its actual coordinate sections. Their actual linear forms
have exactly the literal Bertini member zero sets. The produced fixed
complement is then pulled back to the actual affine hyperplane parameter.
No source canonical bundle, restriction exactness or Nadel vanishing is assumed.
-/

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
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Bergman.AnalyticSectionProducts SGPT.Bergman.NativeKodairaPullback
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Toric.ExceptionalRestrictionDraft
open SGPT.Toric.F1IntersectionDraft

variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- A genuine native generating family reads homogeneous hyperplane
vanishing in its actual original physical fibres. -/
theorem nativeSectionFamily_linear_zero_iff
    (E : HermitianHolomorphicLineBundle n X)
    (s : Fin (N + 1) → HolomorphicSections (n := n) E.Fiber)
    (hGen : ∀ x : X, ∃ i, s i x ≠ 0)
    (a : Fin (N + 1) → ℂ) (x : X) :
    (∑ i, a i • s i x) = 0 ↔
      pairing a (sourceNativeFiniteSectionProjectiveMap E s hGen x).rep = 0 := by
  classical
  let e : AtlasFrame E := ⟨trivializationAt ℂ E.Fiber x, inferInstance⟩
  let := e.property
  have hx : x ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ E.Fiber x
  let A := e.val.linearEquivAt ℂ x hx
  let u : Fin (N + 1) → ℂ := fun i => (e.val ⟨x, s i x⟩).2
  have hu : u ≠ 0 := by
    intro hz
    obtain ⟨i, hi⟩ := hGen x
    apply hi
    apply A.injective
    have h := congrFun hz i
    change A (s i x) = 0 at h
    simpa using h
  have hmap : sourceNativeFiniteSectionProjectiveMap E s hGen x = mk u hu :=
    sourceNativeFiniteSectionProjectiveMap_frame E s hGen e x hx
  obtain ⟨c, hc, hrep⟩ := rep_smul (sourceNativeFiniteSectionProjectiveMap E s hGen x) hu hmap
  rw [hrep, pairing_smul_right]
  simp only [mul_eq_zero, hc, false_or]
  have hcoef : A (∑ i, a i • s i x) = pairing a u := by
    simp only [map_sum, map_smul, smul_eq_mul, pairing]
    rfl
  constructor
  · intro hz
    rw [← hcoef, hz, map_zero]
  · intro hz
    apply A.injective
    rw [hcoef, hz, map_zero]

/-- The independently constructed original native p^*O(1). -/
def nativeBertiniHyperplaneBundle
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
      X (ComplexProjectiveSpace N) ∞) : HermitianHolomorphicLineBundle n X :=
  nativeHolomorphicPullbackBundle (sourceProjectiveHyperplaneBundle N) p

/-- Actual coordinate sections of the original pulled-back O(1). -/
def nativeBertiniCoordinateSection
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
      X (ComplexProjectiveSpace N) ∞) (i : Fin (N + 1)) :
    HolomorphicSections (n := n) (nativeBertiniHyperplaneBundle p).Fiber :=
  sourceNativeHolomorphicSectionPullback (sourceProjectiveHyperplaneBundle N) p
    (sourceProjectiveCoordinateNativeSection N i)

theorem nativeBertiniCoordinateSection_generating
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
      X (ComplexProjectiveSpace N) ∞) :
    ∀ x : X, ∃ i, nativeBertiniCoordinateSection p i x ≠ 0 :=
  sourceNativeHolomorphicSectionPullback_generating (sourceProjectiveHyperplaneBundle N) p
    (sourceProjectiveCoordinateNativeSection N) (sourceProjectiveCoordinateNativeSection_generating N)

/-- The actual pulled-back native coordinate family recovers the ORIGINAL p. -/
theorem nativeBertiniCoordinateSection_projectiveMap
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
      X (ComplexProjectiveSpace N) ∞) (x : X) :
    sourceNativeFiniteSectionProjectiveMap (nativeBertiniHyperplaneBundle p)
      (nativeBertiniCoordinateSection p) (nativeBertiniCoordinateSection_generating p) x = p x := by
  change sourceNativeFiniteSectionProjectiveMap
    (nativeHolomorphicPullbackBundle (sourceProjectiveHyperplaneBundle N) p)
    (fun i => sourceNativeHolomorphicSectionPullback (sourceProjectiveHyperplaneBundle N) p
      (sourceProjectiveCoordinateNativeSection N i)) _ x = p x
  rw [sourceNativeFiniteFamily_projectiveMap_pullback (sourceProjectiveHyperplaneBundle N) p
    (sourceProjectiveCoordinateNativeSection N) (sourceProjectiveCoordinateNativeSection_generating N)]
  exact sourceProjectiveCoordinateNativeSection_projectiveMap_identity N (p x)

/-- The actual native defining section on an affine chart of the dual P^N. -/
def nativeBertiniAffineSection
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
      X (ComplexProjectiveSpace N) ∞) (j : Fin (N + 1)) (ζ : ComplexModel N) :
    HolomorphicSections (n := n) (nativeBertiniHyperplaneBundle p).Fiber :=
  ∑ i, affineLift j ζ i • nativeBertiniCoordinateSection p i

/-- The native defining section vanishes at precisely the literal original
scheme-theoretic member's underlying point set. -/
theorem nativeBertiniAffineSection_zero_iff
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
      X (ComplexProjectiveSpace N) ∞) (j : Fin (N + 1)) (ζ : ComplexModel N) (x : X) :
    nativeBertiniAffineSection p j ζ x = 0 ↔ x ∈ member p (affinePoint j ζ) := by
  let ev : HolomorphicSections (n := n) (nativeBertiniHyperplaneBundle p).Fiber →ₗ[ℂ]
      (nativeBertiniHyperplaneBundle p).Fiber x := {
    toFun s := s x
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have hsum : nativeBertiniAffineSection p j ζ x =
      ∑ i, affineLift j ζ i • nativeBertiniCoordinateSection p i x := by
    change ev (∑ i, affineLift j ζ i • nativeBertiniCoordinateSection p i) = _
    rw [map_sum]
    rfl
  rw [hsum, nativeSectionFamily_linear_zero_iff _ _
    (nativeBertiniCoordinateSection_generating p), nativeBertiniCoordinateSection_projectiveMap]
  change pairing (affineLift j ζ) (p x).rep = 0 ↔ IsIncident (affinePoint j ζ) (p x)
  conv_rhs => rw [← mk_rep (p x)]
  exact (isIncident_mk_mk_iff (affineLift_ne_zero j ζ) (p x).rep_ne_zero).symm

/-- An actual proper original member PRODUCES a nonzero native defining section. -/
theorem nativeBertiniAffineSection_ne_zero
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
      X (ComplexProjectiveSpace N) ∞) (j : Fin (N + 1)) (ζ : ComplexModel N)
    (hproper : ∃ x : X, x ∉ member p (affinePoint j ζ)) :
    nativeBertiniAffineSection p j ζ ≠ 0 := by
  obtain ⟨x, hx⟩ := hproper
  intro hz
  apply hx
  apply (nativeBertiniAffineSection_zero_iff p j ζ x).mp
  exact congrArg (fun s => s x) hz

/-- The actual original affine hyperplane section varies continuously in the
full native section norm, through its actual finite coordinate-section formula. -/
theorem continuous_nativeBertiniAffineSection [CompactSpace X]
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
      X (ComplexProjectiveSpace N) ∞) (j : Fin (N + 1)) :
    Continuous (nativeBertiniAffineSection p j) := by
  apply continuous_finsetSum Finset.univ
  intro i hi
  exact ((differentiable_affineLift_apply j i).continuous).smul continuous_const

/-- The original hyperplane parameter now has an actual fixed original
finite quotient frame, with its defining section's exact member zero locus. -/
theorem exists_nativeBertiniHyperplane_quotientBasis [CompactSpace X] [ConnectedSpace X]
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
      X (ComplexProjectiveSpace N) ∞)
    (E : HermitianHolomorphicLineBundle n X) {φ : X → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    (j : Fin (N + 1)) (ζ₀ : ComplexModel N)
    (hproper : ∃ x : X, x ∉ member p (affinePoint j ζ₀)) :
    ∃ r : ℕ, ∃ S : Fin r → nativeMultiplierSections (tensor E (nativeBertiniHyperplaneBundle p)) φ,
      ∃ U : Set (ComplexModel N), IsOpen U ∧ ζ₀ ∈ U ∧
        ∀ ζ ∈ U, ∃ b : Module.Basis (Fin r) ℂ
          ((nativeMultiplierSections (tensor E (nativeBertiniHyperplaneBundle p)) φ) ⧸
            (nativeMultiplierSectionMap E (nativeBertiniHyperplaneBundle p) hφ
              (nativeBertiniAffineSection p j ζ)).range),
          ∀ i, b i = (nativeMultiplierSectionMap E (nativeBertiniHyperplaneBundle p) hφ
            (nativeBertiniAffineSection p j ζ)).range.mkQ (S i) := by
  obtain ⟨r, S, U, hU, htU, hBasis⟩ :=
    exists_nativeMultiplier_quotientBasis E (nativeBertiniHyperplaneBundle p) hφ
      (nativeBertiniAffineSection p j ζ₀) (nativeBertiniAffineSection_ne_zero p j ζ₀ hproper)
  refine ⟨r, S, (nativeBertiniAffineSection p j) ⁻¹' U,
    hU.preimage (continuous_nativeBertiniAffineSection p j), htU, ?_⟩
  intro ζ hζ
  exact hBasis _ hζ

end SGPT.Trace.Bertini
