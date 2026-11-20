import SGPT.Trace.BertiniHyperplaneQuotientFrame
import SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace

/-! Actual restriction of the literal original Bertini quotient.

The map is produced from physical native pullback and the actual zero set of
the original defining section. No restriction exactness, cohomology vanishing
or canonical adjunction is assumed or claimed.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini

open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Bergman.NativeKodairaPullback SGPT.Toric.F1IntersectionDraft
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace

variable {n m N : ℕ} {X Y : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]

/-- The original physical section pullback is an actual complex linear map. -/
def nativeSectionPullbackLinearMap (A : HermitianHolomorphicLineBundle.{0,0} n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) Y X ∞) :
    HolomorphicSections (n := n) A.Fiber →ₗ[ℂ]
      HolomorphicSections (n := m) (nativeHolomorphicPullbackBundle A f).Fiber where
  toFun := sourceNativeHolomorphicSectionPullback A f
  map_add' S T := by
    apply ContMDiffSection.ext
    intro y
    rfl
  map_smul' a S := by
    apply ContMDiffSection.ext
    intro y
    rfl

theorem nativeSectionPullbackLinearMap_apply (A : HermitianHolomorphicLineBundle.{0,0} n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) Y X ∞)
    (S : HolomorphicSections (n := n) A.Fiber) (y : Y) :
    nativeSectionPullbackLinearMap A f S y = S (f y) := rfl

/-- Genuine quotient restriction, obtained by proving that the actual
original multiplication image is killed on the actual original zero set. -/
def nativeMultiplierQuotientRestriction
    (E P : HermitianHolomorphicLineBundle.{0,0} n X) {φ : X → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    (t : HolomorphicSections (n := n) P.Fiber)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) Y X ∞)
    (ht : ∀ y, t (f y) = 0) :
    ((nativeMultiplierSections (tensor E P) φ) ⧸ (nativeMultiplierSectionMap E P hφ t).range) →ₗ[ℂ]
      HolomorphicSections (n := m) (nativeHolomorphicPullbackBundle (tensor E P) f).Fiber := by
  let R : nativeMultiplierSections (tensor E P) φ →ₗ[ℂ]
      HolomorphicSections (n := m) (nativeHolomorphicPullbackBundle (tensor E P) f).Fiber := {
    toFun S := nativeSectionPullbackLinearMap (tensor E P) f S.val
    map_add' S T := by
      apply ContMDiffSection.ext
      intro y
      rfl
    map_smul' a S := by
      apply ContMDiffSection.ext
      intro y
      rfl }
  apply (nativeMultiplierSectionMap E P hφ t).range.liftQ R
  rintro S ⟨u, rfl⟩
  apply ContMDiffSection.ext
  intro y
  change u.val (f y) ⊗ₜ[ℂ] t (f y) = 0
  rw [ht y, TensorProduct.tmul_zero]

theorem nativeMultiplierQuotientRestriction_mk
    (E P : HermitianHolomorphicLineBundle.{0,0} n X) {φ : X → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    (t : HolomorphicSections (n := n) P.Fiber)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) Y X ∞)
    (ht : ∀ y, t (f y) = 0) (S : nativeMultiplierSections (tensor E P) φ) :
    nativeMultiplierQuotientRestriction E P hφ t f ht
      ((nativeMultiplierSectionMap E P hφ t).range.mkQ S) =
      sourceNativeHolomorphicSectionPullback (tensor E P) f S.val := rfl

theorem nativeMultiplierQuotientRestriction_mk_apply
    (E P : HermitianHolomorphicLineBundle.{0,0} n X) {φ : X → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    (t : HolomorphicSections (n := n) P.Fiber)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) Y X ∞)
    (ht : ∀ y, t (f y) = 0) (S : nativeMultiplierSections (tensor E P) φ) (y : Y) :
    nativeMultiplierQuotientRestriction E P hφ t f ht
      ((nativeMultiplierSectionMap E P hφ t).range.mkQ S) y = S.val (f y) := rfl

section Member

variable (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
    X (ComplexProjectiveSpace N) ∞) (j : Fin (N + 1)) (ζ : ComplexModel N)
    {k : ℕ} (hk : k ≤ n)
    (hsm : IsSmoothMemberOfDim p p.contMDiff (affinePoint j ζ) k)

/-- Actual inclusion of the original smooth member, with the complex
structure internally produced from original regular-member data. -/
def nativeBertiniMemberInclusion :
    letI := SubmanifoldChartedSpace.chartedSpace hk hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hsm.1
    ContMDiffMap 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n)
      (member p (affinePoint j ζ)) X ∞ := by
  letI := SubmanifoldChartedSpace.chartedSpace hk hsm.1
  letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hsm.1
  exact ⟨Subtype.val, SubmanifoldChartedSpace.contMDiff_val hk hsm.1⟩

/-- The actual original quotient restricts to sections of the actual native
restricted bundle on the original smooth member. -/
def nativeBertiniMemberQuotientRestriction
    (E : HermitianHolomorphicLineBundle.{0,0} n X) {φ : X → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ) :
    letI := SubmanifoldChartedSpace.chartedSpace hk hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hsm.1
    ((nativeMultiplierSections (tensor E (nativeBertiniHyperplaneBundle p)) φ) ⧸
      (nativeMultiplierSectionMap E (nativeBertiniHyperplaneBundle p) hφ
        (nativeBertiniAffineSection p j ζ)).range) →ₗ[ℂ]
      HolomorphicSections (n := k)
        (nativeHolomorphicPullbackBundle (tensor E (nativeBertiniHyperplaneBundle p))
          (nativeBertiniMemberInclusion p j ζ hk hsm)).Fiber := by
  letI := SubmanifoldChartedSpace.chartedSpace hk hsm.1
  letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hsm.1
  exact nativeMultiplierQuotientRestriction E (nativeBertiniHyperplaneBundle p) hφ
    (nativeBertiniAffineSection p j ζ) (nativeBertiniMemberInclusion p j ζ hk hsm)
    (fun y => (nativeBertiniAffineSection_zero_iff p j ζ y.val).mpr y.property)

theorem nativeBertiniMemberQuotientRestriction_mk_apply
    (E : HermitianHolomorphicLineBundle.{0,0} n X) {φ : X → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    (S : nativeMultiplierSections (tensor E (nativeBertiniHyperplaneBundle p)) φ)
    (y : member p (affinePoint j ζ)) :
    letI := SubmanifoldChartedSpace.chartedSpace hk hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hsm.1
    nativeBertiniMemberQuotientRestriction p j ζ hk hsm E hφ
      ((nativeMultiplierSectionMap E (nativeBertiniHyperplaneBundle p) hφ
        (nativeBertiniAffineSection p j ζ)).range.mkQ S) y = S.val y.val := rfl

end Member

end SGPT.Trace.Bertini
