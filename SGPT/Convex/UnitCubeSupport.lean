import SGPT.Convex.GrowthClasses
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false
noncomputable section
namespace SGPT.Convex
open Set MeasureTheory
open scoped Topology RealInnerProductSpace
/-- The actual closed coordinate unit cube in unchanged Euclidean real space. -/
def euclideanUnitCube (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {m | ∀ i, m i ∈ Icc (0 : ℝ) 1}

/-- Actual compact scalar intervals and the genuine coordinate identification
produce compactness, including the zero-dimensional singleton. -/
theorem isCompact_euclideanUnitCube (n : ℕ) : IsCompact (euclideanUnitCube n) := by
  have heq : euclideanUnitCube n = (WithLp.toLp 2) ''
      (pi univ (fun _ : Fin n => Icc (0 : ℝ) 1)) := by
    ext m
    constructor
    · intro hm
      exact ⟨m.ofLp, fun i _ => hm i, rfl⟩
    · rintro ⟨x, hx, rfl⟩ i
      exact hx i (mem_univ i)
  rw [heq]
  exact (isCompact_univ_pi (fun _ : Fin n => isCompact_Icc)).image
    (PiLp.continuous_toLp 2 _)

/-- The literal original zero point lies in the actual cube. -/
theorem nonempty_euclideanUnitCube (n : ℕ) : (euclideanUnitCube n).Nonempty :=
  ⟨0, fun _ => by simp⟩

/-- Both actual endpoint inequalities are preserved by real convex combinations. -/
theorem convex_euclideanUnitCube (n : ℕ) : Convex ℝ (euclideanUnitCube n) := by
  intro x hx y hy a b ha hb hab i
  change 0 ≤ a * x i + b * y i ∧ a * x i + b * y i ≤ 1
  exact ⟨add_nonneg (mul_nonneg ha (hx i).1) (mul_nonneg hb (hy i).1),
    by nlinarith [(hx i).2, (hy i).2]⟩

/-- The actual coordinate vertex attains the literal original support supremum. -/
theorem support_euclideanUnitCube (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    support (innerₗ (EuclideanSpace ℝ (Fin n))).flip (euclideanUnitCube n) x =
      ((∑ i : Fin n, max 0 (x i) : ℝ) : EReal) := by
  let m : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => if 0 ≤ x i then 1 else 0)
  have hm : m ∈ euclideanUnitCube n := by
    intro i
    change (if 0 ≤ x i then (1 : ℝ) else 0) ∈ Icc 0 1
    split_ifs <;> simp
  have hdot (p : euclideanUnitCube n) :
      inner ℝ x p.val ≤ ∑ i : Fin n, max 0 (x i) := by
    rw [PiLp.inner_apply]
    apply Finset.sum_le_sum
    intro i _
    change p.val i * x i ≤ max 0 (x i)
    by_cases hxi : 0 ≤ x i
    · rw [max_eq_right hxi]
      nlinarith [(p.property i).2]
    · rw [max_eq_left (le_of_not_ge hxi)]
      exact mul_nonpos_of_nonneg_of_nonpos (p.property i).1 (le_of_not_ge hxi)
  have hmax : inner ℝ x m = ∑ i : Fin n, max 0 (x i) := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    change (if 0 ≤ x i then (1 : ℝ) else 0) * x i = max 0 (x i)
    split_ifs with hxi
    · simp only [one_mul, max_eq_right hxi]
    · simp only [zero_mul, max_eq_left (le_of_not_ge hxi)]
  apply le_antisymm
  · apply iSup_le
    intro p
    exact EReal.coe_le_coe (hdot p)
  · apply le_iSup_of_le (⟨m, hm⟩ : euclideanUnitCube n)
    rw [← hmax]
    exact le_rfl

/-- Genuine orthonormal coordinate-volume preservation gives actual cube volume
one; the empty product remains one. -/
theorem volume_euclideanUnitCube (n : ℕ) : volume (euclideanUnitCube n) = 1 := by
  let Q := pi univ (fun _ : Fin n => Icc (0 : ℝ) 1)
  have hQ : MeasurableSet Q :=
    (isCompact_univ_pi (fun _ : Fin n => isCompact_Icc)).isClosed.measurableSet
  have heq : euclideanUnitCube n = (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) ⁻¹' Q := by
    ext m
    change (∀ i : Fin n, m i ∈ Icc (0 : ℝ) 1) ↔
      ∀ i : Fin n, i ∈ univ → m i ∈ Icc (0 : ℝ) 1
    simp only [mem_univ, forall_const]
  rw [heq, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage hQ.nullMeasurableSet]
  change volume (pi univ (fun _ : Fin n => Icc (0 : ℝ) 1)) = 1
  rw [volume_pi_pi]
  simp [Real.volume_Icc]

end SGPT.Convex
