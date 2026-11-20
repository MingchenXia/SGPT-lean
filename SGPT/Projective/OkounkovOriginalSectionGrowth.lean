import SGPT.Okounkov.ValGenSections

/-! The SAME original section slices have genuine finite polynomial growth.
Blueprint: okounkov-original-section-growth.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Okounkov.BodyFromGrowth
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.ValGen SGPT.LineBundle SGPT.AlmostSemigroup

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
  {L : X.Modules} (a : LineBundleAtlas L) (c : X)
  (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))

omit [SmoothOfRelativeDimension n f] in
theorem valueSet_sectionToField_eq_image (k : ℕ) :
    (let := schemeFunctionFieldAlgebra f; valueSet v (sectionToField f c a k)) =
      (fun x : Fin n → ℤ => ((toLex x : Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ)))) ''
        vectorSet f c a v k ⊤ := by
  let := schemeFunctionFieldAlgebra f
  ext w
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨sectionVector v c a k s hs, ⟨s, hs, Submodule.mem_top, rfl⟩, ?_⟩
    rw [valuation_sectionToField, sectionValue_eq_vector c a k s hs]
  · rintro ⟨x, ⟨s, hs, _, hx⟩, rfl⟩
    refine ⟨s, hs, ?_⟩
    rw [valuation_sectionToField, sectionValue_eq_vector c a k s hs, hx]

omit [SmoothOfRelativeDimension n f] in
include E in
theorem original_vectorSet_finite (k : ℕ) : (vectorSet f c a v k ⊤).Finite := by
  let := schemeFunctionFieldAlgebra f
  have := SectionSpace.finiteDimensional f E a k
  have hι : Function.Injective (fun x : Fin n → ℤ =>
      ((toLex x : Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ)))) :=
    fun x y h => toLex.injective (WithTop.coe_injective h)
  have hfin := valueSet_finite v (sectionToField f c a k)
    (sectionToField_injective f c a k) (fun z hz => valuation_algebraMap_complex v hz)
  rw [valueSet_sectionToField_eq_image f n a c v k, Set.finite_image_iff hι.injOn] at hfin
  exact hfin

omit [SmoothOfRelativeDimension n f] in
include E in
theorem original_card_vectorSet_le_h0 (k : ℕ) :
    Nat.card (vectorSet f c a v k ⊤) ≤ h0 f L k := by
  let := schemeFunctionFieldAlgebra f
  have := SectionSpace.finiteDimensional f E a k
  have hι : Function.Injective (fun x : Fin n → ℤ =>
      ((toLex x : Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ)))) :=
    fun x y h => toLex.injective (WithTop.coe_injective h)
  rw [← Nat.card_image_of_injective hι, ← valueSet_sectionToField_eq_image f n a c v k]
  exact card_valueSet_le_finrank v (sectionToField f c a k)
    (sectionToField_injective f c a k) (fun z hz => valuation_algebraMap_complex v hz)

omit [SmoothOfRelativeDimension n f] in
include f E in
theorem original_sectionSemigroup_slice_finite (k : ℤ) :
    (slice (sectionSemigroup v c a : Set ((Fin n → ℤ) × ℤ)) k).Finite := by
  by_cases hk : 0 ≤ k
  · lift k to ℕ using hk with k
    rw [slice_sectionSemigroup_eq f c a v k]
    exact original_vectorSet_finite f n E a c v k
  · have he : slice (sectionSemigroup v c a : Set ((Fin n → ℤ) × ℤ)) k = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hk (sectionSemigroup_degree_nonneg (v := v) c a (x, k) hx)
    rw [he]
    exact Set.finite_empty

omit [SmoothOfRelativeDimension n f] in
include E in
theorem original_sectionSemigroup_card_slice_le_h0 (k : ℕ) :
    Nat.card (slice (sectionSemigroup v c a : Set ((Fin n → ℤ) × ℤ)) (k : ℤ)) ≤ h0 f L k := by
  rw [slice_sectionSemigroup_eq f c a v k]
  exact original_card_vectorSet_le_h0 f n E a c v k

local instance : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n
variable (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

include f E Y hY in
theorem exists_original_sectionSemigroup_card_le_pow :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, 1 ≤ k →
      (Nat.card (slice (sectionSemigroup v c a : Set ((Fin n → ℤ) × ℤ)) (k : ℤ)) : ℝ) ≤
        B * (k : ℝ) ^ n := by
  obtain ⟨B, hB⟩ := ValGen.exists_h0_le_pow f n E Y hY a
  have hB0 : 0 ≤ B := (Nat.cast_nonneg (h0 f L 1)).trans (by simpa using hB 1 le_rfl)
  refine ⟨B, hB0, fun k hk => ?_⟩
  have hcount : (Nat.card (slice (sectionSemigroup v c a : Set ((Fin n → ℤ) × ℤ)) (k : ℤ)) : ℝ) ≤ (h0 f L k : ℝ) := by
    exact_mod_cast original_sectionSemigroup_card_slice_le_h0 f n E a c v k
  exact hcount.trans (hB k hk)
end SGPT.Okounkov.BodyFromGrowth
