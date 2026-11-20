import SGPT.Toric.Toric5YaoTheorem
import SGPT.Toric.Toric5Weights
import SGPT.AlmostSemigroup.Counting

/-!
# The asymptotic dimension of `H⁰(X, L^k ⊗ 𝓘(kφ))`

Source `chapter_toric_ample.tex`, `cor:DXmaintoric`: for `φ ∈ PSH_tor(X, ω)`,

`lim_{k → ∞} n!/k^n h⁰(X, L^k ⊗ 𝓘(kφ)) = n! vol Δ(ω, φ)`.

We prove it for an arbitrary torus-invariant divisor `D` with a `T_c`-invariant metric `h`
(`BigToricMetric.tendsto_finrank_toricMultiplierSections`) and specialize it to the ample case
(`dxMainToric`).  The proof follows the source:

* `h⁰(X, L^k ⊗ 𝓘(kφ)) = #{m : χ^m ∈ H⁰(X, L^k ⊗ 𝓘(kφ))}` (`T_c`-weight decomposition,
  `finrank_toricMultiplierSections`);
* lower bound: `kΔ ∩ M` consists of such `m` (`thm:Yao` (1) for `L^k`, `kφ`);
* upper bound: such `m` lie within distance `Λ` of `kΔ`, `Λ` independent of `k`
  (`thm:Yao` (2) for `L^k`, `kφ`, and the separating hyperplane: the nearest point projection
  onto `kΔ`), hence in `k Δ^ε` for `k ≥ Λ/ε`;
* `#(kK ∩ M)/k^n → vol K` for convex bodies (`thm:KK12growth`,
  `SGPT.AlmostSemigroup.Counting.tendsto_integer_lattice_count`) and
  `vol Δ^ε → vol Δ` as `ε → 0` (continuity of the volume, `thm:contvol`; here
  `tendsto_measure_cthickening_of_isCompact`).

The sequence is indexed by `k + 1`, `k ∈ ℕ` (`H⁰(X, L^k ⊗ 𝓘(kφ))` is formed for `k ≥ 1`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff BigOperators Manifold ENNReal Pointwise

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-! ### Lattice point counts in the Euclidean model -/

/-- Source `thm:KK12growth` (convex bodies) in the Euclidean model of `M_ℝ`:
`#(kK ∩ M)/k^n → vol K`. -/
theorem tendsto_latticeCount_euclidean {Kb : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact Kb)
    (hconv : Convex ℝ Kb) :
    Tendsto (fun k : ℕ => (k : ℝ)⁻¹ ^ n *
      ({m : Fin n → ℤ | latticeVector m ∈ (k : ℝ) • Kb}.ncard : ℝ)) atTop
      (𝓝 (volume.real Kb)) := by
  set K' : Set (Fin n → ℝ) := (WithLp.toLp 2) ⁻¹' Kb
  have hK'img : K' = (WithLp.ofLp) '' Kb := by
    ext x; constructor
    · intro hx; exact ⟨WithLp.toLp 2 x, hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩; simpa [K'] using hy
  have hK'c : IsCompact K' := by
    rw [hK'img]; exact hK.image (PiLp.continuous_ofLp 2 _)
  have hK'v : Convex ℝ K' := by
    rw [hK'img]
    exact hconv.linear_image (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap
  have hvol : volume.real K' = volume.real Kb := by
    simp only [Measure.real, K']
    rw [(PiLp.volume_preserving_toLp (Fin n)).measure_preimage hK.measurableSet.nullMeasurableSet]
  have h := SGPT.AlmostSemigroup.Counting.tendsto_integer_lattice_count hK'c hK'v
  rw [hvol] at h
  refine h.congr fun k => ?_
  congr 2
  rw [SGPT.AlmostSemigroup.Counting.integerLatticeCount, Nat.card_coe_set_eq]
  congr 1
  ext m
  simp only [SGPT.AlmostSemigroup.Counting.integerPoints, mem_preimage, mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, hxm⟩
    refine ⟨WithLp.toLp 2 x, hx, ?_⟩
    ext i
    have := congrFun hxm i
    simpa [SGPT.AlmostSemigroup.Counting.integerCast] using this
  · rintro ⟨x, hx, hxm⟩
    refine ⟨WithLp.ofLp x, by simpa [K'] using hx, ?_⟩
    funext i
    have := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z i) hxm
    simpa [SGPT.AlmostSemigroup.Counting.integerCast] using this

namespace BigToricMetric

variable {D : ToricDivisor γ hs} (h : BigToricMetric D)

/-! ### The uniform distance bound -/

/-- Source proof of `cor:DXmaintoric`, consequence of `thm:Yao` (2) for `L^k`, `kφ` on a maximal
cone, with nonnegative coefficients: if `χ^m ∈ H⁰(X, L^k ⊗ 𝓘(kφ))` and `a_j ≥ 0`, then
`⟨m, -∑ a_j u_j(v)⟩ - k Supp_Δ(-∑ a_j u_j(v)) ≤ ∑ a_j`. -/
theorem latticeFunctional_sub_newtonSupport_le {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ h.PSHTor) {k : ℕ} (hk : 0 < k) {m : Fin n → ℤ}
    (hmem : (fun a => (latticeCharacter m a : ℂ)) ∈
      toricMultiplierSections ((k : ℤ) • D) (by exact_mod_cast hk : (0 : ℝ) < k) (h.isQPSH_of_mem hu))
    (v : latticePolytopeVertices γ) (a : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j) :
    latticeFunctional m (-∑ j, a j • latticeVector (polytopeToricRayGenerator γ hs v j)) -
        k * h.newtonSupport u (-∑ j, a j • latticeVector (polytopeToricRayGenerator γ hs v j)) ≤
      ∑ j, a j := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hlat := mem_toricLatticePoints_of_latticeCharacter_mem hmem.1
  set U : Fin n → EuclideanSpace ℝ (Fin n) := fun j => latticeVector (polytopeToricRayGenerator γ hs v j)
  set w := ∑ j, a j • U j
  obtain ⟨ρ, hρ0, hρ⟩ := h.exists_newtonSupport_le_add hu
  set E : EuclideanSpace ℝ (Fin n) := ∑ j, U j
  set Lc : ℝ := (‖latticeVector m‖ + k * ρ) * ‖E‖ + n
  by_contra hcon
  push Not at hcon
  set gap := latticeFunctional m (-w) - k * h.newtonSupport u (-w) - ∑ j, a j
  have hgap : 0 < gap := by simp only [gap]; linarith
  set ε : ℝ := gap / (2 * (Lc + 1))
  have hLc : 0 ≤ Lc := by positivity
  have hε : 0 < ε := by positivity
  set c : Fin n → ℝ := fun j => a j + ε
  have hc : ∀ j, 0 < c j := fun j => by have := ha j; simp only [c]; linarith
  have hcw : ∑ j, c j • U j = w + ε • E := by
    simp only [c, add_smul, Finset.sum_add_distrib, E, Finset.smul_sum, w]
  have hsumc : ∑ j, c j = ∑ j, a j + ε * n := by
    simp only [c, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  apply h.not_multiplierIntegrableAt_toricMonomial hu hk hlat v c hc
  · rw [hcw, hsumc]
    have hS : h.newtonSupport u (-(w + ε • E)) ≤ h.newtonSupport u (-w) + ρ * (ε * ‖E‖) := by
      have := hρ (-(w + ε • E)) (-w)
      have hn : ‖-(w + ε • E) - -w‖ = ε * ‖E‖ := by
        rw [neg_add, add_sub_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg hε.le]
      rw [hn] at this
      exact this
    have heq : latticeFunctional m (-(w + ε • E)) =
        latticeFunctional m (-w) - ε * inner ℝ (latticeVector m) E := by
      rw [← inner_latticeVector, ← inner_latticeVector, neg_add, inner_add_right,
        inner_neg_right (y := ε • E), inner_smul_right]
      ring
    have h1 : ε * inner ℝ (latticeVector m) E ≤ ε * (‖latticeVector m‖ * ‖E‖) :=
      mul_le_mul_of_nonneg_left (real_inner_le_norm _ _) hε.le
    have hkS : (k : ℝ) * h.newtonSupport u (-(w + ε • E)) ≤
        k * (h.newtonSupport u (-w) + ρ * (ε * ‖E‖)) := mul_le_mul_of_nonneg_left hS hkpos.le
    have hεbound : ε * (Lc + 1) < gap := by
      simp only [ε]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    rw [heq]
    simp only [gap, Lc] at hεbound
    nlinarith
  · have hcoeff := (mem_toricMultiplierSections_iff _ _ _).mp hmem
    exact hcoeff.2 v _ (differentiable_toricMonomial _ v m).continuous
      (latticeCharacter_eq_toricMonomial _ hlat v) 0

/-- Source proof of `cor:DXmaintoric`: there is `Λ` (independent of `k`) such that every `m` with
`χ^m ∈ H⁰(X, L^k ⊗ 𝓘(kφ))` lies within distance `Λ` of `kΔ(θ, φ)`. -/
theorem exists_dist_le_of_mem {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ (k : ℕ) (hk : 0 < k) (m : Fin n → ℤ),
      (fun a => (latticeCharacter m a : ℂ)) ∈
        toricMultiplierSections ((k : ℤ) • D) (by exact_mod_cast hk : (0 : ℝ) < k)
          (h.isQPSH_of_mem hu) →
      ∃ p ∈ (k : ℝ) • h.newtonBody u, dist (latticeVector m) p ≤ Λ := by
  have hP := h.nonempty_toricDivisorPolytope_of_mem hu
  obtain ⟨hne, hcpt, hconv, -⟩ := h.newtonBody_properties hP hu
  -- a bound for the edge vectors
  have hvfin := finite_latticePolytopeVertices γ
  have : Finite (latticePolytopeVertices γ) := hvfin.to_subtype
  obtain ⟨B, hB⟩ := (Set.finite_univ (α := latticePolytopeVertices γ × Fin n)).image
    (fun p => ‖latticeVector (originalPolytopeNativeBasis γ hs p.1 p.2)‖) |>.bddAbove
  have hB' : ∀ v j, ‖latticeVector (originalPolytopeNativeBasis γ hs v j)‖ ≤ B := fun v j =>
    hB ⟨(v, j), mem_univ _, rfl⟩
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  refine ⟨n * max B 0, by positivity, fun k hk m hmem => ?_⟩
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  set Kk := (k : ℝ) • h.newtonBody u
  have hKne : Kk.Nonempty := hne.smul_set
  have hKc : IsCompact Kk := hcpt.smul _
  have hKv : Convex ℝ Kk := hconv.smul _
  obtain ⟨p, hp, hpmin⟩ := exists_norm_eq_iInf_of_complete_convex hKne hKc.isComplete hKv
    (latticeVector m)
  have hobt := (norm_eq_iInf_iff_real_inner_le_zero hKv hp).mp hpmin
  refine ⟨p, hp, ?_⟩
  set y := latticeVector m - p
  rw [dist_eq_norm]
  change ‖y‖ ≤ _
  -- `k Supp_Δ(y) ≤ ⟨y, p⟩`
  have hsupp : (k : ℝ) * h.newtonSupport u y ≤ inner ℝ y p := by
    have : h.newtonSupport u y ≤ inner ℝ y p / k := by
      apply h.newtonSupport_le_of_forall hu
      intro x hx
      have := hobt ((k : ℝ) • x) (Set.smul_mem_smul_set hx)
      rw [inner_sub_right, inner_smul_right] at this
      rw [le_div_iff₀ hkpos]
      linarith
    rw [le_div_iff₀ hkpos] at this
    linarith
  -- `y` lies in some `-σ_v`
  obtain ⟨v, hv⟩ := exists_vertex_mem_negCone (hs := hs) y
  set a : Fin n → ℝ := fun j => -latticeFunctional (originalPolytopeNativeBasis γ hs v j) y
  have ha : ∀ j, 0 ≤ a j := fun j => by simp only [a]; linarith [hv j]
  have hy : y = -∑ j, a j • latticeVector (polytopeToricRayGenerator γ hs v j) := by
    conv_lhs => rw [eq_sum_basis_smul_rayVector (hs := hs) v y]
    simp only [a, neg_smul, Finset.sum_neg_distrib, neg_neg]
  have hbound := h.latticeFunctional_sub_newtonSupport_le hu hk hmem v a ha
  rw [← hy] at hbound
  -- `‖y‖² ≤ ⟨m, y⟩ - k Supp_Δ(y)`
  have hsq : ‖y‖ ^ 2 ≤ latticeFunctional m y - k * h.newtonSupport u y := by
    have hyy : ‖y‖ ^ 2 = inner ℝ (latticeVector m) y - inner ℝ y p := by
      rw [← real_inner_self_eq_norm_sq]
      have : inner ℝ y y = inner ℝ (latticeVector m - p) y := rfl
      rw [this, inner_sub_left, real_inner_comm p y]
    rw [← inner_latticeVector]
    linarith
  -- `∑ a_j ≤ n B ‖y‖`
  have hsum : ∑ j, a j ≤ n * max B 0 * ‖y‖ := by
    calc ∑ j, a j ≤ ∑ _j : Fin n, max B 0 * ‖y‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          simp only [a]
          rw [← inner_latticeVector]
          have := real_inner_le_norm (-latticeVector (originalPolytopeNativeBasis γ hs v j)) y
          rw [inner_neg_left, norm_neg] at this
          exact this.trans (mul_le_mul_of_nonneg_right ((hB' v j).trans (le_max_left _ _))
            (norm_nonneg _))
      _ = n * max B 0 * ‖y‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hfin : ‖y‖ ^ 2 ≤ n * max B 0 * ‖y‖ := by linarith
  by_cases hy0 : ‖y‖ = 0
  · rw [hy0]; positivity
  · have hypos : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hy0)
    nlinarith

/-! ### The asymptotic count -/

/-- Source `cor:DXmaintoric` (in the big setting, normalized): for `φ ∈ PSH_tor(X, θ)`,
`k^{-n} h⁰(X, L^k ⊗ 𝓘(kφ)) → vol Δ(θ, φ)` (`k = 1, 2, …`). -/
theorem tendsto_finrank_toricMultiplierSections {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ h.PSHTor) :
    Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ)⁻¹ ^ n *
      (Module.finrank ℂ (toricMultiplierSections (((k + 1 : ℕ) : ℤ) • D)
        (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ)) (h.isQPSH_of_mem hu)) : ℝ))
      atTop (𝓝 (volume.real (h.newtonBody u))) := by
  have hP := h.nonempty_toricDivisorPolytope_of_mem hu
  obtain ⟨hne, hcpt, hconv, -⟩ := h.newtonBody_properties hP hu
  obtain ⟨Λ, hΛ0, hΛ⟩ := h.exists_dist_le_of_mem hu
  set Δ := h.newtonBody u
  set T : ℕ → Set (Fin n → ℤ) := fun k => {m | (fun a => (latticeCharacter m a : ℂ)) ∈
      toricMultiplierSections (((k + 1 : ℕ) : ℤ) • D)
        (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ)) (h.isQPSH_of_mem hu)}
  have hfinrank : ∀ k : ℕ, Module.finrank ℂ (toricMultiplierSections (((k + 1 : ℕ) : ℤ) • D)
      (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ)) (h.isQPSH_of_mem hu)) = (T k).ncard :=
    fun k => finrank_toricMultiplierSections _ _ hu.2
  simp only [hfinrank]
  have hTfin : ∀ k, (T k).Finite := fun k =>
    (finite_toricLatticePoints _).subset (setOf_latticeCharacter_mem_subset _ _)
  -- the counting functions
  set cnt : Set (EuclideanSpace ℝ (Fin n)) → ℕ → ℝ := fun Kb k =>
    (k : ℝ)⁻¹ ^ n * ({m : Fin n → ℤ | latticeVector m ∈ (k : ℝ) • Kb}.ncard : ℝ)
  have hshift : ∀ {Kb : Set (EuclideanSpace ℝ (Fin n))}, IsCompact Kb → Convex ℝ Kb →
      Tendsto (fun k : ℕ => cnt Kb (k + 1)) atTop (𝓝 (volume.real Kb)) := fun hK hv =>
    (tendsto_latticeCount_euclidean hK hv).comp (tendsto_add_atTop_nat 1)
  have hfinK : ∀ {Kb : Set (EuclideanSpace ℝ (Fin n))}, IsCompact Kb → ∀ k : ℕ,
      {m : Fin n → ℤ | latticeVector m ∈ (k : ℝ) • Kb}.Finite := by
    intro Kb hK k
    have hKk : IsCompact ((k : ℝ) • Kb) := hK.smul _
    obtain ⟨R, hR⟩ := hKk.isBounded.subset_closedBall 0
    have hsub : {m : Fin n → ℤ | latticeVector m ∈ (k : ℝ) • Kb} ⊆
        Set.pi univ (fun _ => Set.Icc (-⌈R⌉) ⌈R⌉) := by
      intro m hm i _
      have h1 : ‖latticeVector m‖ ≤ R := by simpa using hR hm
      have h2 : |(m i : ℝ)| ≤ R := by
        have := PiLp.norm_apply_le (latticeVector m) i
        rw [Real.norm_eq_abs] at this
        simpa using this.trans h1
      rw [abs_le] at h2
      constructor
      · have := Int.le_ceil R
        exact_mod_cast (by linarith : (-(⌈R⌉ : ℝ)) ≤ m i)
      · exact_mod_cast (h2.2.trans (Int.le_ceil R))
    exact (Set.Finite.pi fun _ => Set.finite_Icc _ _).subset hsub
  -- lower bound
  have hlow : ∀ k : ℕ, cnt Δ (k + 1) ≤ ((k + 1 : ℕ) : ℝ)⁻¹ ^ n * ((T k).ncard : ℝ) := by
    intro k
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact_mod_cast Set.ncard_le_ncard (fun m hm =>
      h.latticeCharacter_mem_toricMultiplierSections hu (Nat.succ_pos k) hm) (hTfin k)
  -- upper bound
  have hup : ∀ ε > 0, ∀ k : ℕ, Λ / ((k + 1 : ℕ) : ℝ) ≤ ε →
      ((k + 1 : ℕ) : ℝ)⁻¹ ^ n * ((T k).ncard : ℝ) ≤ cnt (Metric.cthickening ε Δ) (k + 1) := by
    intro ε hε k hk
    have hk1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Nat.cast_le.mpr
    apply Set.ncard_le_ncard _ (hfinK (hcpt.cthickening) (k + 1))
    intro m hm
    obtain ⟨p, hp, hdist⟩ := hΛ (k + 1) (Nat.succ_pos k) m hm
    obtain ⟨x, hx, rfl⟩ := hp
    refine ⟨((k + 1 : ℕ) : ℝ)⁻¹ • latticeVector m, ?_, ?_⟩
    · apply Metric.mem_cthickening_of_dist_le _ x _ _ hx
      have : dist (((k + 1 : ℕ) : ℝ)⁻¹ • latticeVector m) x =
          ((k + 1 : ℕ) : ℝ)⁻¹ * dist (latticeVector m) (((k + 1 : ℕ) : ℝ) • x) := by
        rw [dist_eq_norm, dist_eq_norm, ← norm_smul_of_nonneg (by positivity), smul_sub,
          smul_smul, inv_mul_cancel₀ hk1.ne', one_smul]
      rw [this]
      calc ((k + 1 : ℕ) : ℝ)⁻¹ * dist (latticeVector m) (((k + 1 : ℕ) : ℝ) • x)
          ≤ ((k + 1 : ℕ) : ℝ)⁻¹ * Λ := mul_le_mul_of_nonneg_left hdist (by positivity)
        _ = Λ / ((k + 1 : ℕ) : ℝ) := by rw [div_eq_inv_mul]
        _ ≤ ε := hk
    · show ((k + 1 : ℕ) : ℝ) • (((k + 1 : ℕ) : ℝ)⁻¹ • latticeVector m) = latticeVector m
      rw [smul_smul, mul_inv_cancel₀ hk1.ne', one_smul]
  -- squeeze
  rw [tendsto_order]
  constructor
  · intro b hb
    filter_upwards [(tendsto_order.1 (hshift hcpt hconv)).1 b hb] with k hk
    exact lt_of_lt_of_le hk (hlow k)
  · intro b hb
    -- choose `ε > 0` with `vol Δ^ε < b`
    have hcth := tendsto_measure_cthickening_of_isCompact (μ := (volume : Measure
      (EuclideanSpace ℝ (Fin n)))) hcpt
    have hfinΔ : volume Δ ≠ ⊤ := hcpt.measure_lt_top.ne
    have hb' : volume Δ < ENNReal.ofReal b := by
      rw [← ENNReal.ofReal_toReal hfinΔ]
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt measureReal_nonneg hb)).mpr hb
    obtain ⟨ε, hε, hεb⟩ : ∃ ε > 0, volume (Metric.cthickening ε Δ) < ENNReal.ofReal b := by
      have hev := (tendsto_order.1 hcth).2 _ hb'
      obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
      have hd : dist (δ / 2) (0 : ℝ) < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
        linarith
      exact ⟨δ / 2, by positivity, hball hd⟩
    have hεb' : volume.real (Metric.cthickening ε Δ) < b := by
      have hfin' : volume (Metric.cthickening ε Δ) ≠ ⊤ :=
        (hcpt.cthickening (r := ε)).measure_lt_top.ne
      rw [Measure.real, ← ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hfin']
      exact hεb
    have hthick := hshift (hcpt.cthickening (r := ε)) (hconv.cthickening ε)
    have hlarge : ∀ᶠ k : ℕ in atTop, Λ / ((k + 1 : ℕ) : ℝ) ≤ ε := by
      have : Tendsto (fun k : ℕ => Λ / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
        have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul Λ
        simpa [div_eq_mul_inv, one_div] using this
      exact (tendsto_order.1 this).2 ε hε |>.mono fun k hk => hk.le
    filter_upwards [(tendsto_order.1 hthick).2 b hεb', hlarge] with k hk hkε
    exact lt_of_le_of_lt (hup ε hε k hkε) hk

end BigToricMetric

/-- Source `cor:DXmaintoric`: for `φ ∈ PSH_tor(X, ω)`,
`lim_{k → ∞} n!/k^n h⁰(X, L^k ⊗ 𝓘(kφ)) = n! vol Δ(ω, φ)`, with `L = O(D_P)`, `L^k = O(kD_P)`
and `h⁰(X, L^k ⊗ 𝓘(kφ)) = dim H⁰(X, O(kD_P) ⊗ 𝓘(kφ))` (`k = 1, 2, …`). -/
theorem dxMainToric {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ PolytopeToricPSH γ hs) :
    Tendsto (fun k : ℕ => (n.factorial : ℝ) / ((k + 1 : ℕ) : ℝ) ^ n *
      (Module.finrank ℂ (toricMultiplierSections
        (((k + 1 : ℕ) : ℤ) • polytopeToricAmpleDivisor γ hs)
        (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ)) (isQPSH_of_mem_polytopeToricPSH hu)) : ℝ))
      atTop (𝓝 ((n.factorial : ℝ) * volume.real (polytopeToricNewtonBody γ hs u))) := by
  have hu' : u ∈ (guilleminBigToricMetric γ hs).PSHTor := hu
  have h := ((guilleminBigToricMetric γ hs).tendsto_finrank_toricMultiplierSections hu').const_mul
    (n.factorial : ℝ)
  rw [guilleminBigToricMetric_newtonBody hu] at h
  refine h.congr fun k => ?_
  rw [div_eq_mul_inv, inv_pow, mul_assoc]

end SGPT.Toric
