import SGPT.Convex.BoundedLegendrePathEnergy
import SGPT.Convex.BernsteinIntegral
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

set_option autoImplicit false
noncomputable section
namespace SGPT.Convex
open Set Filter MeasureTheory SGPT.PSH
open scoped Topology NNReal ENNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
local notation "B" => innerₗ E

/-- The literal canonical mixed endpoint tuple, with `g` in its first `j` slots. -/
def mixedEndpointTuple {n : ℕ} (f g : RealConvexFunction E) (j : ℕ)
    (i : Fin n) : RealConvexFunction E := if i.val < j then g else f

private def binarySlotSubsetEquiv (n : ℕ) : (Fin n → Fin 2) ≃ Finset (Fin n) where
  toFun a := Finset.univ.filter (fun i => a i ≠ 0)
  invFun S i := if i ∈ S then 1 else 0
  left_inv a := by
    funext i
    change (if i ∈ Finset.univ.filter (fun k => a k ≠ 0) then 1 else 0) = a i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h : a i = 0 ∨ a i = 1 := by omega
    rcases h with h | h <;> simp [h]
  right_inv S := by
    ext i
    by_cases hi : i ∈ S <;> simp [hi]

private theorem binary_subset_weight {n : ℕ} (S : Finset (Fin n)) (t : ℝ) :
    (∏ i : Fin n, if (binarySlotSubsetEquiv n).symm S i = 0 then 1 - t else t) =
      t ^ S.card * (1 - t) ^ (n - S.card) := by
  classical
  have hin : (Finset.univ.filter (fun i : Fin n => i ∈ S)) = S := by ext i; simp
  have hnot : (Finset.univ.filter (fun i : Fin n => i ∉ S)).card = n - S.card := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i : Fin n => i ∈ S)
    rw [hin, Finset.card_univ, Fintype.card_fin] at h
    omega
  calc
    _ = ∏ i : Fin n, if i ∈ S then t else 1 - t := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ S <;> simp [binarySlotSubsetEquiv, hi]
    _ = _ := by
      rw [Finset.prod_ite, hin, Finset.prod_const, Finset.prod_const, hnot]

private theorem mixed_subset_eq_prefix (μ : Measure E) [μ.IsAddHaarMeasure]
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (f g : RealConvexFunction E)
    (S : Finset (Fin n)) :
    mixedAlexandrovMeasure μ b (fun i => if i ∈ S then g else f) =
      mixedAlexandrovMeasure μ b (mixedEndpointTuple f g S.card) := by
  classical
  let T : Finset (Fin n) := Finset.univ.filter (fun i => i.val < S.card)
  have hcard : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hT : T.card = S.card := by
    simp only [T, Fin.card_filter_val_lt, min_eq_right hcard]
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq T S hT
  have hmem (i : Fin n) : σ i ∈ S ↔ i.val < S.card := by
    have hm : σ i ∈ S ↔ i ∈ T := by
      constructor
      · intro hi
        have hi' : σ i ∈ T.map σ.toEmbedding := hσ.symm ▸ hi
        obtain ⟨k, hk, hki⟩ := Finset.mem_map.mp hi'
        have he : k = i := σ.injective hki
        simpa only [he] using hk
      · intro hi
        have hi' : σ i ∈ T.map σ.toEmbedding := Finset.mem_map.mpr ⟨i, hi, rfl⟩
        rwa [hσ] at hi'
    simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using hm
  have htuple : (fun i => if σ i ∈ S then g else f) = mixedEndpointTuple f g S.card := by
    funext i
    simp only [hmem, mixedEndpointTuple]
  have h := mixedAlexandrovMeasure_perm μ b (fun i => if i ∈ S then g else f) σ
  rw [htuple] at h
  exact h.symm

private theorem mixed_binary_subset (μ : Measure E) [μ.IsAddHaarMeasure]
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (f g : RealConvexFunction E)
    (S : Finset (Fin n)) :
    mixedAlexandrovMeasure μ b
        (fun i => binaryConvexFamily f g ((binarySlotSubsetEquiv n).symm S i)) =
      mixedAlexandrovMeasure μ b (mixedEndpointTuple f g S.card) := by
  rw [show (fun i => binaryConvexFamily f g ((binarySlotSubsetEquiv n).symm S i)) =
      (fun i => if i ∈ S then g else f) from by
    funext i
    by_cases hi : i ∈ S <;> simp [binarySlotSubsetEquiv, binaryConvexFamily, hi]]
  exact mixed_subset_eq_prefix μ b f g S

/-- Actual binary finite-subset cardinality and genuine mixed slot symmetry give
exactly the original Bernstein mixed endpoint expansion. -/
theorem affineTangentPolynomial_eq_bernsteinMixedEndpoint (μ : Measure E) [μ.IsAddHaarMeasure]
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (f g : RealConvexFunction E) (t : ℝ) :
    affineTangentPolynomial μ b f g t =
      ∑ j ∈ Finset.range (n + 1), (bernsteinPolynomial ℝ n j).eval t *
        ∫ x, (g.val x - f.val x) ∂mixedAlexandrovMeasure μ b (mixedEndpointTuple f g j) := by
  classical
  let J : ℕ → ℝ := fun j => ∫ x, (g.val x - f.val x)
    ∂mixedAlexandrovMeasure μ b (mixedEndpointTuple f g j)
  have hsum : (∑ S : Finset (Fin n), t ^ S.card * (1 - t) ^ (n - S.card) * J S.card) =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * (t ^ j * (1 - t) ^ (n - j) * J j) := by
    have h := Finset.sum_powerset_apply_card (fun j => t ^ j * (1 - t) ^ (n - j) * J j)
      (x := (Finset.univ : Finset (Fin n)))
    have hpow : (Finset.univ : Finset (Fin n)).powerset = Finset.univ := by
      ext S
      simp
    rw [hpow, Finset.card_univ, Fintype.card_fin] at h
    simpa only [nsmul_eq_mul] using h
  calc
    affineTangentPolynomial μ b f g t =
        ∑ S : Finset (Fin n), t ^ S.card * (1 - t) ^ (n - S.card) * J S.card := by
      unfold affineTangentPolynomial
      apply Fintype.sum_equiv (binarySlotSubsetEquiv n)
      intro a
      have ha : a = (binarySlotSubsetEquiv n).symm ((binarySlotSubsetEquiv n) a) :=
        ((binarySlotSubsetEquiv n).symm_apply_apply a).symm
      rw [ha, binary_subset_weight, mixed_binary_subset]
      simp only [Equiv.apply_symm_apply, J]
    _ = _ := by
      rw [hsum]
      apply Finset.sum_congr rfl
      intro j _
      simp [bernsteinPolynomial, J, mul_assoc]

/-- The original general-rank bounded Legendre energy is the actual finite mixed
endpoint sum with coefficient `1/(n+1)` and literal Euclidean factorial. -/
theorem integral_conjugate_difference_eq_mixedEndpointEnergy (μ : Measure E) [μ.IsAddHaarMeasure]
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    {f g : RealConvexFunction E}
    (hf : (fun x => (f.val x : EReal)) ∈ BoundedGrowthClass B P)
    (hg : (fun x => (g.val x : EReal)) ∈ BoundedGrowthClass B P) :
    (n.factorial : ℝ) * (∫ m in P,
        ((conjugate B (fun x => (f.val x : EReal)) m).toReal -
          (conjugate B (fun x => (g.val x : EReal)) m).toReal) ∂μ) =
      (1 / (n + 1 : ℝ)) * ∑ j ∈ Finset.range (n + 1),
        ∫ x, (g.val x - f.val x) ∂mixedAlexandrovMeasure μ b (mixedEndpointTuple f g j) := by
  rw [integral_conjugate_difference_eq_affinePathEnergy μ b hP hne hconv hf hg]
  simp_rw [affineTangentPolynomial_eq_bernsteinMixedEndpoint μ b f g]
  rw [intervalIntegral.integral_finsetSum (fun j _ => by
    have hc : Continuous (fun t : ℝ => (bernsteinPolynomial ℝ n j).eval t) :=
      continuous_iff_continuousAt.mpr (fun t => (bernsteinPolynomial ℝ n j).hasDerivAt t |>.continuousAt)
    exact (hc.mul continuous_const).intervalIntegrable 0 1)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show (fun t : ℝ => (bernsteinPolynomial ℝ n j).eval t *
      ∫ x, (g.val x - f.val x) ∂mixedAlexandrovMeasure μ b (mixedEndpointTuple f g j)) =
      (fun t : ℝ => (∫ x, (g.val x - f.val x) ∂mixedAlexandrovMeasure μ b (mixedEndpointTuple f g j)) *
        (bernsteinPolynomial ℝ n j).eval t) from funext (fun _ => mul_comm _ _),
    intervalIntegral.integral_const_mul, integral_bernsteinPolynomial_eq n j
      (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
  exact mul_comm _ _
end SGPT.Convex
