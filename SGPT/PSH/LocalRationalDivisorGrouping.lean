import SGPT.PSH.CartierLogarithmicRemainder
import Mathlib.Topology.LocallyFinite
import Mathlib.Data.Rat.Floor
import SGPT.Foundations.Analysis.Pending.MeteredDivisorSingleGenerator

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff


/-- The ORIGINAL finite positive rational family internally produces its
positive LOCAL denominator and actual positive integer numerators. -/
theorem exists_finite_positive_rational_denominator {ι : Type*}
    (s : Finset ι) (w : ι → ℚ) (hw : ∀ i ∈ s, 0 < w i) :
    ∃ (d : ℕ) (a : ι → ℕ), 0 < d ∧ ∀ i ∈ s, 0 < a i ∧ w i = (a i : ℚ) / (d : ℚ) := by
  classical
  let I := {i // i ∈ s}
  let E := Fintype.equivFin I
  let v : Fin (Fintype.card I) → ℚ := fun j => w (E.symm j).val
  obtain ⟨d, a, hd, heq⟩ := MeteredDivisorSingleGenerator.exists_commonDenominator v
    (fun j => (hw (E.symm j).val (E.symm j).property).le)
  let A : ι → ℕ := fun i => if hi : i ∈ s then a (E ⟨i, hi⟩) else 0
  refine ⟨d, A, hd, ?_⟩
  intro i hi
  have hreal := heq (E ⟨i, hi⟩)
  simp only [v, E.symm_apply_apply] at hreal
  have hrat : w i = (a (E ⟨i, hi⟩) : ℚ) / (d : ℚ) := by
    apply Rat.cast_injective (α := ℝ)
    simpa only [Rat.cast_div, Rat.cast_natCast] using hreal
  have hpos : 0 < a (E ⟨i, hi⟩) := by
    by_contra hbad
    have hzero := Nat.eq_zero_of_not_pos hbad
    rw [hzero, Nat.cast_zero, zero_div] at hrat
    exact (ne_of_gt (hw i hi)) hrat
  simpa only [A, dif_pos hi] using And.intro hpos hrat


/-- The internally produced LOCAL denominator groups the SAME original
finite rational logarithms literally, including all poles and empty products. -/
theorem exists_finite_rational_logarithmic_product_grouping {ι : Type*}
    (s : Finset ι) (w : ι → ℚ) (hw : ∀ i ∈ s, 0 < w i) :
    ∃ (d : ℕ) (a : ι → ℕ), 0 < d ∧
      (∀ i ∈ s, 0 < a i ∧ w i = (a i : ℚ) / (d : ℚ)) ∧
      ∀ h : ι → ℂ,
        (∑ i : {i // i ∈ s}, ((w i.val : ℝ) : EReal) * logNormSq (h i.val)) =
          (((1 / (d : ℚ) : ℚ) : ℝ) : EReal) *
            logNormSq (∏ i : {i // i ∈ s}, h i.val ^ a i.val) := by
  classical
  obtain ⟨d, a, hd, ha⟩ := exists_finite_positive_rational_denominator s w hw
  refine ⟨d, a, hd, ha, ?_⟩
  intro h
  have hone : logNormSq (1 : ℂ) = 0 := by simp [logNormSq]
  have hlog : logNormSq (∏ i : {i // i ∈ s}, h i.val ^ a i.val) =
      ∑ i : {i // i ∈ s}, ((a i.val : ℝ) : EReal) * logNormSq (h i.val) := by
    simpa only [mul_one, hone, add_zero] using
      logNormSq_geometric_product (fun i : {i // i ∈ s} => h i.val) (fun i => a i.val) 1
  have hcR : 0 ≤ ((1 / (d : ℚ) : ℚ) : ℝ) := by positivity
  rw [hlog, MeteredDivisorSingleGenerator.coe_mul_finsetSum hcR]
  apply Finset.sum_congr rfl
  intro i _
  have hcoef : (((1 / (d : ℚ) : ℚ) : ℝ) : EReal) * ((a i.val : ℝ) : EReal) =
      ((w i.val : ℝ) : EReal) := by
    rw [← EReal.coe_mul]
    congr 1
    have hQ : (1 / (d : ℚ)) * (a i.val : ℚ) = w i.val := by
      rw [(ha i.val i.property).2]
      ring
    exact_mod_cast hQ
  rw [← mul_assoc, hcoef]

/-- ORIGINAL locally finite actual carriers and positive rational weights
internally select their exact finite nearby ORIGINAL indices and only a
finite LOCAL denominator, retaining every original extended logarithm. -/
theorem exists_original_locally_finite_rational_grouping {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {ι : Type*} (P : ι → ClosedIrreducibleAnalyticSubvariety n M)
    (w : ι → ℚ) (hw : ∀ i, 0 < w i) (hLF : LocallyFinite (fun i => (P i).carrier)) (x : M) :
    ∃ U : Opens M, x ∈ U ∧ ∃ (s : Finset ι) (d : ℕ) (a : ι → ℕ),
      (∀ i, i ∈ s ↔ ((P i).carrier ∩ (U : Set M)).Nonempty) ∧ 0 < d ∧
      (∀ i ∈ s, 0 < a i ∧ w i = (a i : ℚ) / (d : ℚ)) ∧
      (∀ y ∈ U, y ∈ ⋃ i, (P i).carrier ↔ ∃ i ∈ s, y ∈ (P i).carrier) ∧
      ∀ h : ι → ℂ,
        (∑ i : {i // i ∈ s}, ((w i.val : ℝ) : EReal) * logNormSq (h i.val)) =
          (((1 / (d : ℚ) : ℚ) : ℝ) : EReal) *
            logNormSq (∏ i : {i // i ∈ s}, h i.val ^ a i.val) := by
  classical
  obtain ⟨N, hN, hfinite⟩ := hLF x
  obtain ⟨U, hUN, hU, hxU⟩ := _root_.mem_nhds_iff.mp hN
  have hfiniteU : {i | ((P i).carrier ∩ U).Nonempty}.Finite :=
    hfinite.subset (fun i hi => hi.mono (inter_subset_inter_right _ hUN))
  let s := hfiniteU.toFinset
  have hs (i : ι) : i ∈ s ↔ ((P i).carrier ∩ U).Nonempty := hfiniteU.mem_toFinset
  obtain ⟨d, a, hd, ha, hlog⟩ := exists_finite_rational_logarithmic_product_grouping s w
    (fun i _ => hw i)
  refine ⟨⟨U, hU⟩, hxU, s, d, a, hs, hd, ha, ?_, hlog⟩
  intro y hyU
  constructor
  · intro hy
    obtain ⟨i, hyi⟩ := mem_iUnion.mp hy
    exact ⟨i, (hs i).mpr ⟨y, hyi, hyU⟩, hyi⟩
  · rintro ⟨i, _, hyi⟩
    exact mem_iUnion.mpr ⟨i, hyi⟩

#print axioms exists_finite_positive_rational_denominator
#print axioms exists_finite_rational_logarithmic_product_grouping
#print axioms exists_original_locally_finite_rational_grouping
end SGPT.PSH
