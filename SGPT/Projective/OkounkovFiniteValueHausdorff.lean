import SGPT.GAGA.OkoCloseBig
import SGPT.Okounkov.AlgPOBCounting

/-! Actual raw lattice-value Hausdorff convergence from upper control and true counts.
Blueprint: okounkov-finite-value-hausdorff.tex. No semigroup or cone is supplied. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
namespace SGPT.Okounkov.FiniteValueHausdorff
open Set Filter MeasureTheory Metric
open SGPT.AlmostSemigroup SGPT.AlmostSemigroup.Okounkov
open scoped Topology Pointwise

/-- Manufacture an actual bounding cone, then apply genuine lattice filling to the original family. -/
theorem tendsto_hausdorffDist_of_upper_and_count {n : ℕ} {K : Set (Fin n → ℝ)}
    (hKc : IsCompact K) (hKv : Convex ℝ K) (hvol : 0 < volume.real K)
    (Q : ℕ → Set (Fin n → ℤ))
    (hup : ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop, ∀ x ∈ Q k,
      (k : ℝ)⁻¹ • Counting.integerCast x ∈ cthickening η K)
    (hcount : Tendsto (fun k : ℕ => (k : ℝ)⁻¹ ^ n * (Nat.card (Q k) : ℝ))
      atTop (𝓝 (volume.real K))) :
    Tendsto (fun k : ℕ => hausdorffDist
      ((EuclideanSpace.equiv (Fin n) ℝ).symm ''
        convexHull ℝ ((fun x => (k : ℝ)⁻¹ • Counting.integerCast x) '' Q k))
      ((EuclideanSpace.equiv (Fin n) ℝ).symm '' K)) atTop (𝓝 0) := by
  classical
  obtain ⟨R, hR⟩ := (hKc.isBounded.cthickening (δ := 1)).subset_closedBall (0 : Fin n → ℝ)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (hup 1 zero_lt_one)
  let B : Set (Fin n → ℝ) := closedBall 0 R
  have hBc : IsCompact B := isCompact_closedBall 0 R
  have hBv : Convex ℝ B := convex_closedBall 0 R
  let C := SGPT.GAGA.OkoClose.coneOver B hBc hBv
  let S₀ : Set ((Fin n → ℤ) × ℤ) := {z | ∃ k : ℕ, max k₀ 1 ≤ k ∧ z.2 = (k : ℤ) ∧ z.1 ∈ Q k}
  have hSC : S₀ ⊆ (latticePoints C.cone : Set _) := by
    rintro ⟨x,l⟩ ⟨k,hk,hl,hx⟩
    have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right k₀ 1).trans hk)
    have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
    have hy : (k : ℝ)⁻¹ • Counting.integerCast x ∈ B :=
      hR (hk₀ k ((le_max_left k₀ 1).trans hk) x hx)
    change l = (k : ℤ) at hl
    subst l
    change 0 ≤ ((k : ℤ) : ℝ) ∧ ∃ y ∈ B,
      Counting.integerCast x = ((k : ℤ) : ℝ) • y
    refine ⟨by positivity, (k : ℝ)⁻¹ • Counting.integerCast x, hy, ?_⟩
    simp only [Int.cast_natCast, smul_smul, mul_inv_cancel₀ hkR.ne', one_smul]
  let S : ConeSubset C := ⟨S₀,hSC⟩
  have hslice {k : ℕ} (hk : max k₀ 1 ≤ k) : slice S.val (k : ℤ) = Q k := by
    ext x
    change (∃ j : ℕ, max k₀ 1 ≤ j ∧ (k : ℤ) = (j : ℤ) ∧ x ∈ Q j) ↔ x ∈ Q k
    constructor
    · rintro ⟨j,hj,hkj,hx⟩
      have heq : k = j := by exact_mod_cast hkj
      simpa only [← heq] using hx
    · exact fun hx => ⟨k,hk,rfl,hx⟩
  have hcard {k : ℕ} (hk : max k₀ 1 ≤ k) :
      S.normalizedCardinality k = (k : ℝ)⁻¹ ^ n * (Nat.card (Q k) : ℝ) := by
    unfold ConeSubset.normalizedCardinality
    congr 1
    have heq : Nat.card (Q k) = (S.slices k).card := by
      rw [← hslice hk]
      exact Nat.card_eq_card_finite_toFinset (S.finite_slice k)
    exact_mod_cast heq.symm
  have hScount : Tendsto S.normalizedCardinality atTop (𝓝 (volume.real K)) :=
    hcount.congr' (by filter_upwards [eventually_ge_atTop (max k₀ 1)] with k hk; exact (hcard hk).symm)
  have hKC : K ⊆ heightOne C.cone := by
    rw [SGPT.GAGA.OkoClose.heightOne_coneOver hBc hBv]
    exact fun x hx => hR (self_subset_cthickening K hx)
  have hupper : ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop, ∀ x ∈ S.slices k,
      (k : ℝ)⁻¹ • Counting.integerCast x ∈ cthickening η K := by
    intro η hη
    filter_upwards [hup η hη, eventually_ge_atTop (max k₀ 1)] with k hu hk x hx
    exact hu x ((hslice hk) ▸ ((ConeSubset.mem_slices S k x).mp hx))
  have hlower : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      volume.real K - ε ≤ S.normalizedCardinality k := by
    intro ε hε
    exact ((tendsto_order.mp hScount).1 (volume.real K - ε) (by linarith)).mono
      (fun _ hk => hk.le)
  have hlim := AlgPOB.tendsto_hausdorffDist_of_fills C hKc hKv hKC S hvol hupper hlower
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (max k₀ 1)] with k hk
  simp only [AlgPOB.euclideanDegreePolytope, hslice hk]

/-- The same genuine counting criterion, with upper control in the actual Euclidean coordinates. -/
theorem tendsto_hausdorffDist_of_euclidean_upper_and_count {n : ℕ} {K : Set (Fin n → ℝ)}
    (hKc : IsCompact K) (hKv : Convex ℝ K) (hvol : 0 < volume.real K)
    (Q : ℕ → Set (Fin n → ℤ))
    (hup : ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop, ∀ x ∈ Q k,
      ∃ z ∈ (EuclideanSpace.equiv (Fin n) ℝ).symm '' K,
        dist ((EuclideanSpace.equiv (Fin n) ℝ).symm
          ((k : ℝ)⁻¹ • Counting.integerCast x)) z ≤ η)
    (hcount : Tendsto (fun k : ℕ => (k : ℝ)⁻¹ ^ n * (Nat.card (Q k) : ℝ))
      atTop (𝓝 (volume.real K))) :
    Tendsto (fun k : ℕ => hausdorffDist
      ((EuclideanSpace.equiv (Fin n) ℝ).symm ''
        convexHull ℝ ((fun x => (k : ℝ)⁻¹ • Counting.integerCast x) '' Q k))
      ((EuclideanSpace.equiv (Fin n) ℝ).symm '' K)) atTop (𝓝 0) := by
  let e := (EuclideanSpace.equiv (Fin n) ℝ).symm
  let c : ℝ := ‖(e.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℝ))‖ + 1
  have hc : 0 < c := by dsimp only [c]; positivity
  apply tendsto_hausdorffDist_of_upper_and_count hKc hKv hvol Q ?_ hcount
  intro η hη
  filter_upwards [hup (η / c) (by positivity)] with k hk x hx
  obtain ⟨_,⟨z,hz,rfl⟩,hd⟩ := hk x hx
  have hnorm : dist ((k : ℝ)⁻¹ • Counting.integerCast x) z ≤ η := by
    calc
      _ = ‖e.symm (e ((k : ℝ)⁻¹ • Counting.integerCast x) - e z)‖ := by
        rw [map_sub, e.symm_apply_apply, e.symm_apply_apply, dist_eq_norm]
      _ ≤ ‖(e.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℝ))‖ *
          ‖e ((k : ℝ)⁻¹ • Counting.integerCast x) - e z‖ :=
        (e.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℝ)).le_opNorm _
      _ ≤ c * dist (e ((k : ℝ)⁻¹ • Counting.integerCast x)) (e z) := by
        rw [dist_eq_norm]
        exact mul_le_mul_of_nonneg_right (by dsimp only [c]; linarith) (norm_nonneg _)
      _ ≤ c * (η / c) := mul_le_mul_of_nonneg_left hd hc.le
      _ = η := by field_simp
  rw [mem_cthickening_iff]
  exact (infEDist_le_edist_of_mem hz).trans (by simpa only [edist_dist] using ENNReal.ofReal_le_ofReal hnorm)
end SGPT.Okounkov.FiniteValueHausdorff
