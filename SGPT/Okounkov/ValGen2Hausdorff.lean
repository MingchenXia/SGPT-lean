import SGPT.Okounkov.ValGenBodies

/-!
# A sandwich criterion for the Hausdorff convergence of normalized polytopes

Lane POB-VALGEN2, blueprint `claude-val-gen2.tex`. Source: chapter *The theory of Okounkov
bodies*, proof of `prop:Deltaconvtwisted`: from injections
`H⁰(X, L^{k-k₀}) → H⁰(X, T ⊗ L^k) → H⁰(X, L^{k+k₀})` (multiplication by fixed sections, which
shift the values by fixed vectors) the source concludes
`(k-k₀) Δ_{k-k₀}(L) + ν(s₁) ⊆ k Δ_{k,T}(L) ⊆ (k+k₀) Δ_{k+k₀}(L) - ν(s₀)` and hence the Hausdorff
convergence of `Δ_{k,T}(L)` from that of `Δ_k(L)`. This file proves the purely metric step.

For a family `Q k ⊆ ℤⁿ` let `poly Q k = Conv{k⁻¹ x : x ∈ Q k} ⊆ ℝⁿ` (Euclidean coordinates).
**`tendsto_hausdorffDist_poly_of_sandwich`**: if `poly P j → K` (a compact convex set) in the
Hausdorff metric, `P j` is eventually nonempty and finite, and for fixed `k₀, k₁, w₀, w₁`,
`P j + w₁ ⊆ Q (j + k₁)` and `Q k + w₀ ⊆ P (k + k₀)`, then `poly Q k → K`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.ValGen2

open Set Filter Metric
open scoped Topology Pointwise

variable {n : ℕ}

/-- Lattice points in Euclidean coordinates. -/
def euclideanCast (n : ℕ) : (Fin n → ℤ) →+ EuclideanSpace ℝ (Fin n) where
  toFun x := (EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => (x i : ℝ))
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

/-- `Conv{k⁻¹ x : x ∈ Q k}` in Euclidean coordinates. -/
def poly (Q : ℕ → Set (Fin n → ℤ)) (k : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  convexHull ℝ ((fun x => ((k : ℝ)⁻¹) • euclideanCast n x) '' Q k)

/-- The Euclidean copy of a normalized convex hull is `poly`. -/
theorem image_convexHull_eq_poly (Q : ℕ → Set (Fin n → ℤ)) (k : ℕ) :
    (EuclideanSpace.equiv (Fin n) ℝ).symm ''
        convexHull ℝ ((fun x => ((k : ℝ)⁻¹) • SGPT.AlmostSemigroup.Counting.integerCast x) '' Q k) =
      poly Q k := by
  have h : (EuclideanSpace.equiv (Fin n) ℝ).symm '' convexHull ℝ
      ((fun x => ((k : ℝ)⁻¹) • SGPT.AlmostSemigroup.Counting.integerCast x) '' Q k) =
      convexHull ℝ ((EuclideanSpace.equiv (Fin n) ℝ).symm ''
        ((fun x => ((k : ℝ)⁻¹) • SGPT.AlmostSemigroup.Counting.integerCast x) '' Q k)) :=
    LinearMap.image_convexHull (EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearMap _
  rw [poly, h, Set.image_image]
  exact congrArg _ (Set.image_congr fun x _ => by rw [map_smul]; try rfl)

theorem isBounded_poly {Q : ℕ → Set (Fin n → ℤ)} {k : ℕ} (hQ : (Q k).Finite) :
    Bornology.IsBounded (poly Q k) :=
  isBounded_convexHull.mpr (Set.Finite.isBounded (hQ.image _))

theorem poly_nonempty {Q : ℕ → Set (Fin n → ℤ)} {k : ℕ} (hQ : (Q k).Nonempty) :
    (poly Q k).Nonempty :=
  (hQ.image _).convexHull

/-- **Sandwich criterion.** -/
theorem tendsto_hausdorffDist_poly_of_sandwich {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : IsCompact K) (hKv : Convex ℝ K) (hKne : K.Nonempty)
    (P Q : ℕ → Set (Fin n → ℤ)) (hPfin : ∀ j, (P j).Finite)
    (hP : Tendsto (fun j => hausdorffDist (poly P j) K) atTop (𝓝 0))
    (hPne : ∀ᶠ j in atTop, (P j).Nonempty) (k₀ k₁ : ℕ) (w₀ w₁ : Fin n → ℤ)
    (hlow : ∀ j, ∀ x ∈ P j, x + w₁ ∈ Q (j + k₁))
    (hup : ∀ k, ∀ y ∈ Q k, y + w₀ ∈ P (k + k₀)) :
    Tendsto (fun k => hausdorffDist (poly Q k) K) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η := ε / 2 with hη
  have hηpos : 0 < η := half_pos hε
  obtain ⟨R, hR⟩ := hKc.isBounded.exists_norm_le
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR _ hKne.some_mem)
  set A := R + η / 2 with hA
  have hA0 : 0 ≤ A := by positivity
  -- the polytopes of `P` are eventually `η/2`-close to `K` and nonempty
  obtain ⟨J, hJ⟩ := eventually_atTop.mp
    ((hP.eventually (gt_mem_nhds (half_pos hηpos))).and (hPne.and (eventually_ge_atTop 1)))
  -- the error terms are eventually small
  set B := (k₀ : ℝ) * A + ‖(euclideanCast n) w₀‖ + (k₁ : ℝ) * A + ‖(euclideanCast n) w₁‖ with hB
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (B / (η / 2))
  refine ⟨N₀ + J + k₁ + 1, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := by omega
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hkB : B / k ≤ η / 2 := by
    rw [div_le_iff₀ hkpos]
    rw [div_lt_iff₀ (half_pos hηpos)] at hN₀
    have : (N₀ : ℝ) ≤ k := by exact_mod_cast (show N₀ ≤ k by omega)
    nlinarith
  have hw0 := norm_nonneg ((euclideanCast n) w₀)
  have hw1 := norm_nonneg ((euclideanCast n) w₁)
  have hk0A : 0 ≤ (k₀ : ℝ) * A := by positivity
  have hk1A : 0 ≤ (k₁ : ℝ) * A := by positivity
  have hB1 : ((k₀ : ℝ) * A + ‖(euclideanCast n) w₀‖) / k ≤ η / 2 :=
    le_trans (div_le_div_of_nonneg_right (by linarith) hkpos.le) hkB
  have hB2 : ((k₁ : ℝ) * A + ‖(euclideanCast n) w₁‖) / k ≤ η / 2 :=
    le_trans (div_le_div_of_nonneg_right (by linarith) hkpos.le) hkB
  -- closeness of `P`-polytopes to `K`
  have hclose : ∀ j, J ≤ j → hausdorffDist (poly P j) K < η / 2 ∧ (P j).Nonempty ∧ 1 ≤ j :=
    fun j hj => ⟨(hJ j hj).1, (hJ j hj).2.1, (hJ j hj).2.2⟩
  have hfin : ∀ j, J ≤ j → hausdorffEDist (poly P j) K ≠ ⊤ := fun j hj =>
    hausdorffEDist_ne_top_of_nonempty_of_bounded (poly_nonempty (hclose j hj).2.1) hKne
      (isBounded_poly (hPfin j)) hKc.isBounded
  have hdist_le : hausdorffDist (poly Q k) K ≤ η := by
    apply hausdorffDist_le_of_mem_dist hηpos.le
    · -- every point of `poly Q k` is `η`-close to `K`
      have hsub : poly Q k ⊆ K + closedBall (0 : EuclideanSpace ℝ (Fin n)) η := by
        refine convexHull_min ?_ (hKv.add (convex_closedBall 0 η))
        rintro _ ⟨y, hy, rfl⟩
        set j := k + k₀ with hj
        have hJj : J ≤ j := by omega
        have hjpos : (0 : ℝ) < j := by
          have := (hclose j hJj).2.2
          exact_mod_cast (show 0 < j by omega)
        set p := ((j : ℝ)⁻¹) • (euclideanCast n) (y + w₀) with hp
        have hpD : p ∈ poly P j := subset_convexHull ℝ _ ⟨y + w₀, hup k y hy, rfl⟩
        obtain ⟨z, hzK, hpz⟩ := exists_dist_lt_of_hausdorffDist_lt hpD (hclose j hJj).1
          (hfin j hJj)
        have hpn : ‖p‖ ≤ A := by
          have h1 : ‖p‖ ≤ ‖z‖ + dist p z := by
            rw [dist_eq_norm]
            calc ‖p‖ = ‖z + (p - z)‖ := by rw [add_sub_cancel]
              _ ≤ ‖z‖ + ‖p - z‖ := norm_add_le _ _
          linarith [hR z hzK]
        have hdiff : ((k : ℝ)⁻¹) • (euclideanCast n) y - p = ((k₀ : ℝ) / k) • p - ((k : ℝ)⁻¹) • (euclideanCast n) w₀ := by
          rw [hp, map_add]
          have hjk : (j : ℝ) = k + k₀ := by rw [hj]; push_cast; ring
          match_scalars <;> field_simp <;> rw [hjk] <;> ring
        have hqp : dist (((k : ℝ)⁻¹) • (euclideanCast n) y) p ≤ η / 2 := by
          rw [dist_eq_norm, hdiff]
          calc ‖((k₀ : ℝ) / k) • p - ((k : ℝ)⁻¹) • (euclideanCast n) w₀‖
              ≤ ‖((k₀ : ℝ) / k) • p‖ + ‖((k : ℝ)⁻¹) • (euclideanCast n) w₀‖ := norm_sub_le _ _
            _ = ((k₀ : ℝ) / k) * ‖p‖ + (k : ℝ)⁻¹ * ‖(euclideanCast n) w₀‖ := by
                rw [norm_smul ((k₀ : ℝ) / k) p, norm_smul ((k : ℝ)⁻¹) ((euclideanCast n) w₀),
                  Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
            _ ≤ ((k₀ : ℝ) / k) * A + (k : ℝ)⁻¹ * ‖(euclideanCast n) w₀‖ := by gcongr
            _ = ((k₀ : ℝ) * A + ‖(euclideanCast n) w₀‖) / k := by field_simp
            _ ≤ η / 2 := hB1
        refine ⟨z, hzK, ((k : ℝ)⁻¹) • (euclideanCast n) y - z, ?_, add_sub_cancel _ _⟩
        rw [mem_closedBall_zero_iff, ← dist_eq_norm]
        calc dist (((k : ℝ)⁻¹) • (euclideanCast n) y) z ≤ dist (((k : ℝ)⁻¹) • (euclideanCast n) y) p + dist p z :=
              dist_triangle _ _ _
          _ ≤ η / 2 + η / 2 := add_le_add hqp hpz.le
          _ = η := by ring
      intro x hx
      obtain ⟨z, hz, b, hb, rfl⟩ := hsub hx
      refine ⟨z, hz, ?_⟩
      rw [dist_eq_norm, add_sub_cancel_left]
      exact mem_closedBall_zero_iff.mp hb
    · -- every point of `K` is `η`-close to `poly Q k`
      intro y hy
      obtain ⟨j, rfl⟩ : ∃ j, k = j + k₁ := ⟨k - k₁, by omega⟩
      have hJj : J ≤ j := by omega
      have hjpos : (0 : ℝ) < j := by
        have := (hclose j hJj).2.2
        exact_mod_cast (show 0 < j by omega)
      obtain ⟨u, huD, huy⟩ := exists_dist_lt_of_hausdorffDist_lt' hy (hclose j hJj).1 (hfin j hJj)
      set c : ℝ := (j : ℝ) / ((j + k₁ : ℕ) : ℝ) with hc
      set d := (((j + k₁ : ℕ) : ℝ)⁻¹) • (euclideanCast n) w₁ with hd
      let Aff : EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] EuclideanSpace ℝ (Fin n) :=
        ⟨fun x => c • x + d, c • LinearMap.id, by
          intro p v
          simp only [vadd_eq_add, smul_add, LinearMap.smul_apply, LinearMap.id_apply]
          abel_nf⟩
      have hAff : ∀ x, Aff x = c • x + d := fun _ => rfl
      have hmaps : poly P j ⊆ Aff ⁻¹' poly Q (j + k₁) := by
        refine convexHull_min ?_ ((convex_convexHull ℝ _).affine_preimage Aff)
        rintro _ ⟨x, hx, rfl⟩
        refine subset_convexHull ℝ _ ⟨x + w₁, hlow j x hx, ?_⟩
        rw [hAff, hc, hd]
        simp only [map_add]
        match_scalars <;> field_simp
      have hAu : Aff u ∈ poly Q (j + k₁) := hmaps huD
      refine ⟨Aff u, hAu, ?_⟩
      have hun : ‖u‖ ≤ A := by
        have h1 : ‖u‖ ≤ ‖y‖ + dist u y := by
          rw [dist_eq_norm]
          calc ‖u‖ = ‖y + (u - y)‖ := by rw [add_sub_cancel]
            _ ≤ ‖y‖ + ‖u - y‖ := norm_add_le _ _
        linarith [hR y hy]
      have hkR : ((j + k₁ : ℕ) : ℝ) = (j : ℝ) + k₁ := by push_cast; ring
      have hdiff : u - Aff u = ((k₁ : ℝ) / ((j + k₁ : ℕ) : ℝ)) • u - d := by
        rw [hAff, hc]
        have hk0 : ((j + k₁ : ℕ) : ℝ) ≠ 0 := hkpos.ne'
        match_scalars
        · field_simp
          ring
        · rfl
      have hua : dist u (Aff u) ≤ η / 2 := by
        rw [dist_eq_norm, hdiff, hd]
        calc ‖((k₁ : ℝ) / ((j + k₁ : ℕ) : ℝ)) • u - (((j + k₁ : ℕ) : ℝ)⁻¹) • (euclideanCast n) w₁‖
            ≤ ‖((k₁ : ℝ) / ((j + k₁ : ℕ) : ℝ)) • u‖ + ‖(((j + k₁ : ℕ) : ℝ)⁻¹) • (euclideanCast n) w₁‖ :=
              norm_sub_le _ _
          _ = ((k₁ : ℝ) / ((j + k₁ : ℕ) : ℝ)) * ‖u‖ + ((j + k₁ : ℕ) : ℝ)⁻¹ * ‖(euclideanCast n) w₁‖ := by
              rw [norm_smul ((k₁ : ℝ) / ((j + k₁ : ℕ) : ℝ)) u,
                norm_smul (((j + k₁ : ℕ) : ℝ)⁻¹) ((euclideanCast n) w₁), Real.norm_of_nonneg (by positivity),
                Real.norm_of_nonneg (by positivity)]
          _ ≤ ((k₁ : ℝ) / ((j + k₁ : ℕ) : ℝ)) * A + ((j + k₁ : ℕ) : ℝ)⁻¹ * ‖(euclideanCast n) w₁‖ := by
              gcongr
          _ = ((k₁ : ℝ) * A + ‖(euclideanCast n) w₁‖) / ((j + k₁ : ℕ) : ℝ) := by field_simp
          _ ≤ η / 2 := hB2
      calc dist y (Aff u) ≤ dist y u + dist u (Aff u) := dist_triangle _ _ _
        _ ≤ η / 2 + η / 2 := add_le_add (by rw [dist_comm]; exact huy.le) hua
        _ = η := by ring
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hausdorffDist_nonneg]
  linarith

end SGPT.Okounkov.ValGen2
