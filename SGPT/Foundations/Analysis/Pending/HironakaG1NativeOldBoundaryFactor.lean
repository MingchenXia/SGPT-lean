import SGPT.Foundations.Analysis.Pending.HironakaActualIntrinsicWeightedBoundaryDerivations
import SGPT.Foundations.Analysis.Pending.HironakaG10ChowGermIdealDictionary
import SGPT.Foundations.Analysis.Pending.HironakaNormalCrossingsOriginalExponents

/-!
# Entire native old-boundary factors on the SAME singular strict source

The actual inclusion/projection stalk maps push the held whole ambient
member factorization to arbitrary closed analytic heads. Every original
label, weight, zero/unit image and genuine exceptional factor is retained.
No quotient cancellation or independently embedded history is asserted.

Blueprint FIRST: `hironaka-g1-native-old-boundary-factor.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter TopologicalSpace CategoryTheory
open scoped Topology Manifold ContDiff BigOperators Pointwise

namespace SGPT.Foundations.Analysis.Pending.HironakaG1NativeOldBoundaryFactor

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  RelativePrincipalizationSpan InvertibleIdealQuotient
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaG10ChowGermIdealDictionary
  HironakaActualAnalyticSubspace HironakaActualIntrinsicLabelledBoundaryIdeals
  HironakaActualIntrinsicWeightedBoundaryDerivations HironakaSingularSubspaceBlowupLift
  HironakaSingularSubspaceBlowupCartier NormalCrossings BlowupStrictSubmanifold BlowupTowers

noncomputable section

section WholeStalkAlgebra

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem wholeIdeal_congr_mem (A B : GermIdeal n M) (x : M)
    (h : ∀ f, A.mem x f ↔ B.mem x f) :
    actualWholeSheafStalkIdeal A x = actualWholeSheafStalkIdeal B x := by
  apply congrArg Ideal.span
  ext r
  constructor <;> rintro ⟨f, hf, hmem, hr⟩
  · exact ⟨f, hf, (h f).mp hmem, hr⟩
  · exact ⟨f, hf, (h f).mpr hmem, hr⟩

private theorem wholeIdeal_mul (A B : GermIdeal n M) (x : M)
    (hA : ∀ f, A.mem x f → HolomorphicAt n f x)
    (hB : ∀ f, B.mem x f → HolomorphicAt n f x) :
    actualWholeSheafStalkIdeal (A.mul B) x =
      actualWholeSheafStalkIdeal A x * actualWholeSheafStalkIdeal B x := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨f, hf, hmem, rfl⟩
    rcases hmem with ⟨_, l, s, a, hs, ha, heq⟩
    have hsh : ∀ i, HolomorphicAt n (s i) x := by
      intro i
      rcases hs i with ⟨g, h, hg, hh, he⟩
      rw [he]
      exact (hA g hg).mul (hB h hh)
    have hsum := HolomorphicAt.sum Finset.univ fun i _ => (ha i).mul (hsh i)
    rw [(originalGerm_congr x hf hsum heq).trans (originalGerm_sum_mul x a s ha hsh hsum)]
    apply Ideal.sum_mem
    intro i _
    apply Ideal.mul_mem_left
    rcases hs i with ⟨g, h, hg, hh, he⟩
    have heG := originalGerm_congr x (hsh i) ((hA g hg).mul (hB h hh))
      (Eventually.of_forall fun y => congrFun he y)
    rw [heG]
    rw [originalGerm_mul x g h (hA g hg) (hB h hh)]
    exact Ideal.mul_mem_mul (Ideal.subset_span ⟨g, hA g hg, hg, rfl⟩)
      (Ideal.subset_span ⟨h, hB h hh, hh, rfl⟩)
  · change Ideal.span _ * Ideal.span _ ≤ _
    rw [Ideal.span_mul_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨_, ⟨f, hf, hfm, rfl⟩, _, ⟨g, hg, hgm, rfl⟩, rfl⟩
    change actualOriginalFunctionGerm x f hf * actualOriginalFunctionGerm x g hg ∈ _
    rw [← originalGerm_mul x f g hf hg]
    have hm : (A.mul B).mem x (fun y => f y * g y) := by
      change IsInSpanAt (n := n)
        (fun s => ∃ a b, A.mem x a ∧ B.mem x b ∧ s = a * b) x _
      exact isInSpanAt_self ⟨f, g, hfm, hgm, rfl⟩ (hf.mul hg)
    exact Ideal.subset_span ⟨fun y => f y * g y, hf.mul hg, hm, rfl⟩

end WholeStalkAlgebra

variable {n : ℕ} {M Y : CMfd.{0} n}

/-- Actual LOCAL containment determines the retained old-member exponent. -/
def centreMemberExponent (C H : Set M) (x : M) : ℕ := by
  classical
  exact if ∀ᶠ y in 𝓝 x, y ∈ C → y ∈ H then 1 else 0

variable (hn : 0 < n) {C W : Set M} {π : Y → M} (hπ : IsBlowupAlong n C π)
  {E : List (Set M)} (hE : IsSNCDivisor n E) (hNC : HasNormalCrossings n C E)
  (hW : IsComplexAnalyticSubset (n := n) W)

include hn hE hNC

/-- Every entire original Cartier IMAGE retains its actual old/born factor,
even on a singular, tangent or contained head quotient. -/
theorem native_old_boundary_factor (i : Fin E.length) (z : strictTransform n π W) :
    Ideal.map ((strictTransformProjection hπ hW.isClosed).stalkMap z).hom
      (actualLabelledBoundaryTraceIdeal W E i
        ((strictTransformProjection hπ hW.isClosed).base z)) =
      (actualLabelledBoundaryTraceIdeal (strictTransform n π W) [π ⁻¹' C] 0 z) ^
          centreMemberExponent C (E.get i) (π z.val) *
        actualLabelledBoundaryTraceIdeal (strictTransform n π W)
          [geoStrictTransform π C (E.get i)] 0 z := by
  have hMap := map_actualSubspace_stalk_ideal_pullback hπ.contMDiff
    (fun y (hy : y ∈ strictTransform n π W) =>
      (closure_minimal sdiff_subset (hW.isClosed.preimage hπ.contMDiff.continuous)) hy)
    (vanishingIdeal (n := n) (E.get i))
    (VanishingIdealCoherent.isCoherent_vanishingIdeal
      (MonomialPart.isClosedSubmanifold_get hn hE i)) z
  change Ideal.map _ (Ideal.map _ _) = _
  apply hMap.trans
  by_cases hCH : ∀ᶠ y in 𝓝 (π z.val), y ∈ C → y ∈ E.get i
  · have hmem (f : Y → ℂ) := MemberPullback.mem_pullback_member_iff_of_subset
      hπ hE hNC i hCH f
    have hWhole := wholeIdeal_congr_mem _ _ z.val hmem
    rw [HironakaNormalCrossingsOriginalExponents.exceptionalIdeal_eq_vanishingIdeal hπ] at hWhole
    rw [hWhole, wholeIdeal_mul (vanishingIdeal (n := n) (π ⁻¹' C))
      (vanishingIdeal (n := n) (geoStrictTransform π C (E.get i))) z.val
      (fun _ hf => hf.1) (fun _ hf => hf.1), Ideal.map_mul]
    simp only [centreMemberExponent, if_pos hCH, pow_one, actualLabelledBoundaryTraceIdeal]
    rfl
  · have hmem (f : Y → ℂ) := MemberPullback.mem_pullback_member_iff_of_not_subset
      hπ hE hNC i hCH f
    rw [wholeIdeal_congr_mem _ _ z.val hmem]
    simp only [centreMemberExponent, if_neg hCH, pow_zero, one_mul,
      actualLabelledBoundaryTraceIdeal]
    rfl

/-- ALL original weights and labels retain the full common born exponent
and actual strict-member image product, with no factor cancelled. -/
theorem native_weighted_old_boundary_factor (m : Fin E.length → ℕ)
    (z : strictTransform n π W) :
    Ideal.map ((strictTransformProjection hπ hW.isClosed).stalkMap z).hom
      (actualWeightedBoundaryTraceIdeal W E m
        ((strictTransformProjection hπ hW.isClosed).base z)) =
      (actualLabelledBoundaryTraceIdeal (strictTransform n π W) [π ⁻¹' C] 0 z) ^
          (∑ i : Fin E.length, centreMemberExponent C (E.get i) (π z.val) * m i) *
        ∏ i : Fin E.length,
          (actualLabelledBoundaryTraceIdeal (strictTransform n π W)
            [geoStrictTransform π C (E.get i)] 0 z) ^ m i := by
  classical
  rw [weightedBoundaryTraceIdeal_eq_prod]
  change (Ideal.mapHom ((strictTransformProjection hπ hW.isClosed).stalkMap z).hom)
    (∏ i : Fin E.length, (actualLabelledBoundaryTraceIdeal W E i
      ((strictTransformProjection hπ hW.isClosed).base z)) ^ m i) = _
  rw [map_prod]
  simp only [Ideal.mapHom_apply, Ideal.map_pow,
    native_old_boundary_factor hn hπ hE hNC hW, mul_pow, ← pow_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

end
end SGPT.Foundations.Analysis.Pending.HironakaG1NativeOldBoundaryFactor
