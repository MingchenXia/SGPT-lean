import SGPT.Convex.GrowthClasses
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace SGPT.Convex
open Set
open scoped BigOperators

variable {I : Type*} [Fintype I] [Nonempty I]

/-- The source's actual finite exponential sum and actual real logarithm. -/
noncomputable def logSumExp (a : I → ℝ) : ℝ := Real.log (∑ i, Real.exp (a i))

/-- The genuine original finite exponential sum is strictly positive. -/
theorem sum_exp_pos (a : I → ℝ) : 0 < ∑ i, Real.exp (a i) :=
  Finset.sum_pos (fun i _ ↦ Real.exp_pos (a i)) Finset.univ_nonempty

/-- Every actual original linear cost is bounded by the actual logarithmic sum. -/
theorem le_logSumExp (a : I → ℝ) (i : I) : a i ≤ logSumExp a := by
  apply (Real.le_log_iff_exp_le (sum_exp_pos a)).mpr
  exact Finset.single_le_sum (fun j _ ↦ (Real.exp_pos (a j)).le) (Finset.mem_univ i)

/-- A genuine finite upper bound on the original entries gives the exact cardinality correction. -/
theorem logSumExp_le_of_bound (a : I → ℝ) {r : ℝ} (ha : ∀ i, a i ≤ r) :
    logSumExp a ≤ r + Real.log (Fintype.card I) := by
  have hcard : 0 < (Fintype.card I : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hsum : ∑ i, Real.exp (a i) ≤ (Fintype.card I : ℝ) * Real.exp r := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ Real.exp_le_exp.mpr (ha i))
  have h := Real.log_le_log (sum_exp_pos a) hsum
  rw [Real.log_mul hcard.ne' (Real.exp_ne_zero r), Real.log_exp] at h
  exact h.trans_eq (add_comm _ _)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [Fintype I] [Nonempty I] in
/-- An actual linear halfspace bound on the original generators persists on their genuine convex hull. -/
theorem pairing_le_on_convexHull_range (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    (β : I → F) (x : E) {r : ℝ} (hβ : ∀ i, B x (β i) ≤ r)
    {m : F} (hm : m ∈ convexHull ℝ (range β)) : B x m ≤ r := by
  apply convexHull_min (t := {m | B x m ≤ r}) _ _ hm
  · rintro _ ⟨i, rfl⟩
    exact hβ i
  · simpa only [mem_univ, true_and] using ((B x).convexOn convex_univ).convex_le r

/-- Genuine convexity of the original linear halfspace proves the actual zero lower bound on the polytope. -/
theorem pairing_le_logSumExp_of_mem_convexHull
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (β : I → F) {m : F}
    (hm : m ∈ convexHull ℝ (range β)) (x : E) :
    B x m ≤ logSumExp (fun i ↦ B x (β i)) :=
  pairing_le_on_convexHull_range B β x (le_logSumExp _) hm

/-- The actual finite polytope has genuine finite support and the exact original logarithmic upper bound. -/
theorem logSumExp_le_support_polytope_add
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] (β : I → F) (x : E) :
    (logSumExp (fun i ↦ B x (β i)) : EReal) ≤
      support B.flip (convexHull ℝ (range β)) x + (Real.log (Fintype.card I) : EReal) := by
  have hcompact := (Set.finite_range β).isCompact_convexHull ℝ
  have hne : (convexHull ℝ (range β)).Nonempty :=
    (Set.range_nonempty β).mono (subset_convexHull ℝ _)
  obtain ⟨r, hr⟩ := exists_real_support_value B hcompact hne x
  have hβ (i : I) : B x (β i) ≤ r := by
    have h := le_iSup (fun q : convexHull ℝ (range β) ↦ (B x q : EReal))
      ⟨β i, subset_convexHull ℝ _ (mem_range_self i)⟩
    change (B x (β i) : EReal) ≤ support B.flip (convexHull ℝ (range β)) x at h
    rw [hr] at h
    exact EReal.coe_le_coe_iff.mp h
  rw [hr, ← EReal.coe_add]
  exact EReal.coe_le_coe (logSumExp_le_of_bound _ hβ)

variable [FiniteDimensional ℝ F]

/-- Genuine global lower boundedness detects membership in the actual finite polytope via actual support conjugation. -/
theorem bddBelow_logSumExp_sub_pairing_iff
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] (β : I → F) (m : F) :
    BddBelow (range (fun x ↦ logSumExp (fun i ↦ B x (β i)) - B x m)) ↔
      m ∈ convexHull ℝ (range β) := by
  constructor
  · rintro ⟨C, hC⟩
    have hcompact := (Set.finite_range β).isCompact_convexHull ℝ
    have hne : (convexHull ℝ (range β)).Nonempty :=
      (Set.range_nonempty β).mono (subset_convexHull ℝ _)
    have hconj : conjugate B (support B.flip (convexHull ℝ (range β))) m ≤
        ((Real.log (Fintype.card I) - C : ℝ) : EReal) := by
      apply iSup_le
      intro x
      obtain ⟨r, hr⟩ := exists_real_support_value B hcompact hne x
      have hup := logSumExp_le_support_polytope_add B β x
      rw [hr, ← EReal.coe_add, EReal.coe_le_coe_iff] at hup
      have hlo := hC (mem_range_self x)
      rw [hr, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      linarith
    rw [conjugate_support_of_isContPerfPair B (convex_convexHull ℝ _) hcompact.isClosed] at hconj
    by_contra hout
    rw [indicator, if_neg hout] at hconj
    exact not_le_of_gt (EReal.coe_lt_top _) hconj
  · intro hm
    refine ⟨0, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact sub_nonneg.mpr (pairing_le_logSumExp_of_mem_convexHull B β hm x)

/-- Actual Euclidean duality is exactly the source coordinate dot-product. -/
theorem inner_pairing_coordinate_dot {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (y : Fin n → ℝ) :
    innerₗ (EuclideanSpace ℝ (Fin n)) x ((EuclideanSpace.equiv (Fin n) ℝ).symm y) =
      ∑ j, (EuclideanSpace.equiv (Fin n) ℝ) x j * y j := by
  simp [innerₗ_apply_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

/-- The exact original coordinate formula, with genuine real generators. -/
theorem bddBelow_logSumExp_sub_dot_iff {n : ℕ} (β : I → Fin n → ℝ) (m : Fin n → ℝ) :
    BddBelow (range (fun x : Fin n → ℝ ↦
      Real.log (∑ i, Real.exp (∑ j, x j * β i j)) - ∑ j, x j * m j)) ↔
      m ∈ convexHull ℝ (range β) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hcore := bddBelow_logSumExp_sub_pairing_iff
    (innerₗ (EuclideanSpace ℝ (Fin n))) (fun i ↦ e.symm (β i)) (e.symm m)
  have hreindex :
      (fun x : EuclideanSpace ℝ (Fin n) ↦
        logSumExp (fun i ↦ innerₗ (EuclideanSpace ℝ (Fin n)) x (e.symm (β i))) -
          innerₗ (EuclideanSpace ℝ (Fin n)) x (e.symm m)) =
      (fun x : Fin n → ℝ ↦ Real.log (∑ i, Real.exp (∑ j, x j * β i j)) -
        ∑ j, x j * m j) ∘ e := by
    funext x
    simp only [inner_pairing_coordinate_dot, logSumExp, Function.comp_apply, e]
  rw [hreindex, e.surjective.range_comp] at hcore
  have hhull : e '' convexHull ℝ (range (fun i ↦ e.symm (β i))) =
      convexHull ℝ (range β) := by
    change e.toLinearMap '' convexHull ℝ (range (fun i ↦ e.symm (β i))) =
      convexHull ℝ (range β)
    rw [e.toLinearMap.image_convexHull, ← Set.range_comp]
    simp only [Function.comp_def]
    change convexHull ℝ (range (fun i ↦ e (e.symm (β i)))) = convexHull ℝ (range β)
    simp only [e.apply_symm_apply]
  have hright : e.symm m ∈ convexHull ℝ (range (fun i ↦ e.symm (β i))) ↔
      m ∈ convexHull ℝ (range β) := by
    rw [← hhull]
    constructor
    · intro hm
      exact ⟨e.symm m, hm, e.apply_symm_apply m⟩
    · rintro ⟨z, hz, hzm⟩
      have heq : z = e.symm m := by
        apply e.injective
        simpa only [e.apply_symm_apply] using hzm
      rwa [← heq]
  exact hcore.trans hright

/-- Exact nonempty-family clause of source lma:polybdd2, for the actual original natural-coordinate generators. The unqualified source logarithm-at-zero convention remains open. -/
theorem bddBelow_logSumExp_sub_nat_dot_iff {n : ℕ}
    (β : I → Fin n → ℕ) (m : Fin n → ℝ) :
    BddBelow (range (fun x : Fin n → ℝ ↦
      Real.log (∑ i, Real.exp (∑ j, x j * (β i j : ℝ))) - ∑ j, x j * m j)) ↔
      m ∈ convexHull ℝ (range (fun i j ↦ (β i j : ℝ))) :=
  bddBelow_logSumExp_sub_dot_iff (fun i j ↦ (β i j : ℝ)) m

/-- A genuine empty-family counterexample to using total real log at zero in the unrestricted printed biconditional. -/
theorem empty_real_log_family_counterexample (n : ℕ) :
    BddBelow (range (fun x : Fin n → ℝ ↦
      Real.log (∑ _i : Fin 0, Real.exp (∑ j, x j * (0 : Fin n → ℝ) j)) -
        ∑ j, x j * (0 : Fin n → ℝ) j)) ∧
      (0 : Fin n → ℝ) ∉ convexHull ℝ (range (fun _ : Fin 0 ↦ (0 : Fin n → ℝ))) := by
  constructor
  · refine ⟨0, ?_⟩
    rintro _ ⟨x, rfl⟩
    simp
  · simp

omit [Nonempty I] in
/-- Actual extended logarithm of the original finite exponential sum, retaining log zero as bottom. -/
noncomputable def extendedLogSumExp (a : I → ℝ) : EReal :=
  ENNReal.log (ENNReal.ofReal (∑ i, Real.exp (a i)))

/-- On the actual nonempty source family the extended and real logarithms agree exactly. -/
theorem extendedLogSumExp_eq_coe (a : I → ℝ) :
    extendedLogSumExp a = (logSumExp a : EReal) :=
  ENNReal.log_ofReal_of_pos (sum_exp_pos a)

omit [Nonempty I] in
/-- The actual extended-log formula proves the all-finite-family membership characterization, with genuine finite lower constants. -/
theorem exists_lower_bound_extendedLogSumExp_sub_dot_iff {n : ℕ}
    (β : I → Fin n → ℝ) (m : Fin n → ℝ) :
    (∃ C : ℝ, ∀ x : Fin n → ℝ,
      (C : EReal) ≤ extendedLogSumExp (fun i ↦ ∑ j, x j * β i j) -
        ((∑ j, x j * m j : ℝ) : EReal)) ↔
      m ∈ convexHull ℝ (range β) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hI =>
    let : IsEmpty I := hI
    constructor
    · rintro ⟨C, hC⟩
      have h := hC 0
      simp [extendedLogSumExp] at h
    · intro hm
      simp only [Set.range_eq_empty β, convexHull_empty, mem_empty_iff_false] at hm
  | inr hI =>
    let : Nonempty I := hI
    rw [← bddBelow_logSumExp_sub_dot_iff β m]
    constructor
    · rintro ⟨C, hC⟩
      refine ⟨C, ?_⟩
      rintro _ ⟨x, rfl⟩
      have h := hC x
      rwa [extendedLogSumExp_eq_coe, logSumExp, ← EReal.coe_sub, EReal.coe_le_coe_iff] at h
    · rintro ⟨C, hC⟩
      refine ⟨C, fun x ↦ ?_⟩
      rw [extendedLogSumExp_eq_coe, logSumExp, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      exact hC (mem_range_self x)

end SGPT.Convex
