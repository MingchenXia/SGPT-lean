import SGPT.PSH.HermitianComparisonResidualTrace
import SGPT.PSH.HermitianCorrectedTraceReadback

/-! The proper residual subsets retain actual ordinary corrected traces;
their finite combinatorics then give a uniform canonical pure-trace budget. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparisonPureBudget

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open Hermitian HermitianGlobalProducts HermitianComparisonBackgroundTorsion
  LocalProductCurrents LocalBedfordTaylorProducts StronglyPositiveForms
  HermitianComparisonPureTraces HermitianPureTraceReadback HermitianComparisonResidualTrace
open scoped Topology Distributions

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  {omega : Background (m + 1) M}

/-- The actual proper-subset corrected ordinary trace budget of the
original bounded global tuple on its original correction patch. -/
def patchProperBudget (P : BackgroundPatch omega) (u : Fin m → M → EReal)
    (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (A : Set (ComplexModel (m + 1))) : ℝ :=
  properCorrectedTraceBudget m
    (oneCurrentOf (U := P.geometry.domain) (by omega : 1 + m = m + 1))
    (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _)
    (fun i => P.correctedReal (u i))
    (fun i => P.correctedReal_isLocallyBoundedPshOn (hu i) (hb i)) P.residual_smooth A

omit [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M] in
/-- The original subset expansion contributes at most `2^m` terms,
each of whose own subset expansion contributes at most `2^m` terms. -/
theorem sum_proper_subsets_le_four_pow (m : ℕ) (f : Finset (Fin m) → ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ s, s.card < m → f s ≤ (2 : ℝ) ^ s.card * B) :
    (∑ s : Finset (Fin m) with s.card < m, f s) ≤ (4 : ℝ) ^ m * B := by
  classical
  have hterm (s : Finset (Fin m)) (hs : s.card < m) : f s ≤ (2 : ℝ) ^ m * B := by
    apply (hf s hs).trans
    apply mul_le_mul_of_nonneg_right _ hB
    gcongr
    norm_num
  calc
    _ ≤ ∑ s : Finset (Fin m) with s.card < m, (2 : ℝ) ^ m * B := by
      apply Finset.sum_le_sum
      intro s hs
      exact hterm s (Finset.mem_filter.mp hs).2
    _ ≤ ∑ _s : Finset (Fin m), (2 : ℝ) ^ m * B :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => mul_nonneg (by positivity) hB)
    _ = (4 : ℝ) ^ m * B := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
      simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [← mul_assoc, ← mul_pow]
      norm_num

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Every proper original residual trace budget is controlled by a
uniform finite sum of the actual canonical global pure traces. All lower
selected tuples, ordinary trace readbacks and their bounds are internal. -/
theorem properCorrectedTraceBudget_le_pureTrace_sum
    (P : BackgroundPatch omega) {h : M → EReal} (hh : IsHermitianPSH omega h)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ h x ∧ h x ≤ (b : EReal))
    (v : Fin m → M → EReal) (hv : ∀ i, IsHermitianPSH omega (v i))
    (hvb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ v i x ∧ v i x ≤ (b : EReal))
    (hvalues : ∀ i, v i = h ∨ v i = fun _ => 0)
    (A : Set (ComplexModel (m + 1))) (E : Set M)
    (hA : A ⊆ P.geometry.domain) (hAE : ∀ z ∈ A, P.geometry.chart.val.symm z ∈ E)
    (C : NNReal) (hC : 1 ≤ C)
    (hres : ∀ z ∈ P.geometry.domain,
      IsSemipositiveOneOne ((C : ℝ) • omega.form.coeff P.geometry.chart z - -P.residual z))
    (hbeta : ∀ z ∈ P.geometry.domain,
      IsSemipositiveOneOne ((C : ℝ) • omega.form.coeff P.geometry.chart z - kahlerForm (m + 1))) :
    patchProperBudget P v hv hvb A ≤ (4 : ℝ) ^ m * (C : ℝ) ^ (m + 1) *
      ∑ j ∈ Finset.range (m + 1), pureTraceMass omega hh hb E j := by
  classical
  let B : ℝ := (C : ℝ) ^ (m + 1) *
    ∑ j ∈ Finset.range (m + 1), pureTraceMass omega hh hb E j
  have hB : 0 ≤ B := mul_nonneg (pow_nonneg C.coe_nonneg _)
    (Finset.sum_nonneg fun j _ => pureTraceMass_nonneg hh hb E j)
  unfold patchProperBudget properCorrectedTraceBudget
  have hterm (s : Finset (Fin m)) (hs : s.card < m) :
      (((HermitianComparisonOneFactor.backgroundResidual m
        (oneCurrentOf (U := P.geometry.domain) (by omega : 1 + m = m + 1))
        (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _)
        (fun i => P.correctedReal (v i))
        (fun i => P.correctedReal_isLocallyBoundedPshOn (hv i) (hvb i))
        P.residual_smooth s).positive.traceMeasure) A).toReal ≤ (2 : ℝ) ^ s.card * B := by
    rw [backgroundResidual_unit_traceMeasure]
    have hbound := btProduct_traceMass_le_pureTrace_sum P (by omega : s.card < m + 1)
      (by omega : 1 + (m - s.card) + s.card = m + 1) hh hb
      (fun i => v (s.orderEmbOfFin rfl i)) (fun i => hvalues _) A E hA hAE C hC hres hbeta
    simpa only [correctedOrdinaryTraceMeasure, B, mul_assoc] using hbound
  exact (sum_proper_subsets_le_four_pow m _ hB hterm).trans_eq (by dsimp only [B]; ring)

end SGPT.PSH.HermitianComparisonPureBudget
