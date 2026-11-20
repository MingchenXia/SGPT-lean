import SGPT.Toric.Toric5Yao
import SGPT.Toric.BigToricAmple

/-!
# Yao's theorem

Source `chapter_toric_ample.tex`, `thm:Yao` (and its form for `L^k`, `kφ`, used in the proof of
`cor:DXmaintoric`): for `φ ∈ PSH_tor(X, ω)` and `m ∈ M`,

1. if `m ∈ Δ(ω, φ)`, then `χ^m ∈ H⁰(X, L ⊗ 𝓘(φ))`;
2. if `σ ∈ Σ` has rays `ρ_1, …, ρ_p`, `c_i > 0`, `∑ c_i = 1`, `u = ∑ c_i u_{ρ_i}` and
   `⟨m, -u⟩ - Supp_{Δ(ω, φ)}(-u) > 1`, then `χ^m ∉ H⁰(X, L ⊗ 𝓘(φ))`.

We prove it for an arbitrary torus-invariant divisor `D`, an arbitrary `T_c`-invariant metric
`h` on `O(D)` (`θ = c_1(O(D), h)`, `BigToricMetric`) and every power `L^k = O(kD)` with the
potential `kφ` (the Newton body of `kφ` for `h^k` is `kΔ(θ, φ)`, so `Supp_{kΔ} = k Supp_Δ`):
`BigToricMetric.latticeCharacter_mem_toricMultiplierSections` and
`BigToricMetric.latticeCharacter_not_mem_toricMultiplierSections`.  The source theorem is the
case of the ample divisor `D_P` with the Guillemin metric (`θ = ω`) and `k = 1`:
`yao_mem` and `yao_not_mem`.

The source proves (1) after replacing `φ` by `P_ω[φ]` (`prop:PandPI`); here (1) follows from
the direct estimate `multiplierIntegrableAt_toricMonomial_of_exponent`, choosing `x₀` with
`G_φ(x₀) < ∞` close to `m / k`.  For (2), the cone `σ` is a face of a maximal cone `σ_v`; the
coefficients are extended by a small `ε > 0` to all rays of `σ_v`, which keeps the strict
inequality, and `not_multiplierIntegrableAt_toricMonomial` is applied at the torus-fixed point
of `σ_v`.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology ContDiff BigOperators Manifold ENNReal Pointwise

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The rays `u_j(v)`, `j ∈ Fin n`, of a maximal cone are pairwise distinct. -/
theorem polytopeToricRayGenerator_injective (v : latticePolytopeVertices γ) :
    Function.Injective (polytopeToricRayGenerator γ hs v) := by
  intro i j hij
  have h1 := intPairing_basis_rayGenerator γ hs v i i
  have h2 := intPairing_basis_rayGenerator γ hs v i j
  rw [if_pos rfl] at h1
  rw [← hij, h1] at h2
  by_contra hne
  rw [if_neg hne] at h2
  exact one_ne_zero h2

theorem polytopeToricRay_injective (v : latticePolytopeVertices γ) :
    Function.Injective (polytopeToricRay γ hs v) := fun _ _ hij =>
  polytopeToricRayGenerator_injective v (congrArg Subtype.val hij)

namespace BigToricMetric

variable {D : ToricDivisor γ hs} (h : BigToricMetric D)

/-- The coefficient of a character in a vertex chart is the monomial `χ^{m - m_v}`. -/
theorem coeff_latticeCharacter_eq {D' : ToricDivisor γ hs} {m : Fin n → ℤ}
    (hm : m ∈ toricLatticePoints D') (v : latticePolytopeVertices γ) {f : ComplexModel n → ℂ}
    (hf : Continuous f)
    (hgf : ∀ a, (latticeCharacter m a : ℂ) =
      f (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) *
        latticeCharacter (toricCartierDatum D' v) a) :
    f = toricMonomial D' v m :=
  toricSectionCoeff_unique (D := D') v hf (differentiable_toricMonomial D' v m).continuous hgf
    (latticeCharacter_eq_toricMonomial D' hm v)

/-- `Δ(θ, φ) ⊆ P_D`, hence `kΔ(θ, φ) ∩ M ⊆ M ∩ P_{kD}`. -/
theorem mem_toricLatticePoints_of_mem_smul_newtonBody {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ h.PSHTor) {k : ℕ} (hk : 0 < k) {m : Fin n → ℤ}
    (hm : latticeVector m ∈ (k : ℝ) • h.newtonBody u) : m ∈ toricLatticePoints ((k : ℤ) • D) := by
  obtain ⟨-, -, -, hsub⟩ := h.newtonBody_properties (h.nonempty_toricDivisorPolytope_of_mem hu) hu
  change latticeVector m ∈ toricDivisorPolytope ((k : ℤ) • D)
  rw [mem_toricDivisorPolytope_smul_iff D hk]
  exact Set.smul_set_mono hsub hm

/-- Source `thm:Yao` (1), for `L^k = O(kD)` and `kφ`: if `m ∈ kΔ(θ, φ)` then
`χ^m ∈ H⁰(X, L^k ⊗ 𝓘(kφ))`. -/
theorem latticeCharacter_mem_toricMultiplierSections {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ h.PSHTor) {k : ℕ} (hk : 0 < k) {m : Fin n → ℤ}
    (hm : latticeVector m ∈ (k : ℝ) • h.newtonBody u) :
    (fun a => (latticeCharacter m a : ℂ)) ∈
      toricMultiplierSections ((k : ℤ) • D) (by exact_mod_cast hk : (0 : ℝ) < k) (h.isQPSH_of_mem hu) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hP := h.nonempty_toricDivisorPolytope_of_mem hu
  have hlat := h.mem_toricLatticePoints_of_mem_smul_newtonBody hu hk hm
  rw [mem_toricMultiplierSections_iff]
  refine ⟨latticeCharacter_mem_toricSections _ hlat, ?_⟩
  intro v f hf hgf z
  rw [coeff_latticeCharacter_eq hlat v hf hgf]
  -- choose `x₀ ∈ {G_φ < ∞}` close to `m / k`
  set y : EuclideanSpace ℝ (Fin n) := (k : ℝ)⁻¹ • latticeVector m
  have hy : y ∈ h.newtonBody u := by
    obtain ⟨x, hx, hxm⟩ := hm
    have hyx : y = x := by
      simp only [y, ← hxm, smul_smul, inv_mul_cancel₀ hkpos.ne', one_smul]
    rw [hyx]; exact hx
  rw [h.newtonBody_eq_closure_effectiveDomain hP hu] at hy
  set M : ℝ := ∑ j, ‖latticeVector (polytopeToricRayGenerator γ hs v j)‖ + 1
  have hM : 0 < M := by positivity
  obtain ⟨x₀, hx₀, hdist⟩ := Metric.mem_closure_iff.mp hy (1 / (2 * k * M)) (by positivity)
  apply h.multiplierIntegrableAt_toricMonomial_of_exponent hu hk hlat v hx₀
  intro j
  have hsplit : latticeVector m - (k : ℝ) • x₀ = (k : ℝ) • (y - x₀) := by
    simp only [y, smul_sub, smul_smul, mul_inv_cancel₀ hkpos.ne', one_smul]
  rw [hsplit, map_smul, smul_eq_mul, ← inner_latticeVector]
  have h1 : |inner ℝ (latticeVector (polytopeToricRayGenerator γ hs v j)) (y - x₀)| ≤
      ‖latticeVector (polytopeToricRayGenerator γ hs v j)‖ * ‖y - x₀‖ := abs_real_inner_le_norm _ _
  have h2 : ‖latticeVector (polytopeToricRayGenerator γ hs v j)‖ ≤ M := by
    have := Finset.single_le_sum (f := fun j => ‖latticeVector (polytopeToricRayGenerator γ hs v j)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    simp only [M]; linarith
  have h3 : ‖y - x₀‖ < 1 / (2 * k * M) := by rw [← dist_eq_norm]; exact hdist
  have h4 : ‖latticeVector (polytopeToricRayGenerator γ hs v j)‖ * ‖y - x₀‖ ≤ M * (1 / (2 * k * M)) :=
    mul_le_mul h2 h3.le (norm_nonneg _) hM.le
  have h5 : M * (1 / (2 * k * M)) = 1 / (2 * k) := by field_simp
  have h6 : (k : ℝ) * (1 / (2 * k)) = 1 / 2 := by field_simp
  have h7 := neg_abs_le (inner ℝ (latticeVector (polytopeToricRayGenerator γ hs v j)) (y - x₀))
  have h8 : (k : ℝ) * (-(1 / (2 * k))) ≤
      k * inner ℝ (latticeVector (polytopeToricRayGenerator γ hs v j)) (y - x₀) :=
    mul_le_mul_of_nonneg_left (by linarith) hkpos.le
  linarith

/-- Source `thm:Yao` (2), for `L^k = O(kD)` and `kφ` (`Supp_{kΔ} = k Supp_Δ`): if `σ ∈ Σ` has
rays `R = σ(1)`, `c_ρ > 0` on `R`, `∑_{ρ ∈ R} c_ρ = 1`, `u = ∑_{ρ ∈ R} c_ρ u_ρ` and
`⟨m, -u⟩ - k Supp_{Δ(θ, φ)}(-u) > 1`, then `χ^m ∉ H⁰(X, L^k ⊗ 𝓘(kφ))`. -/
theorem latticeCharacter_not_mem_toricMultiplierSections {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ h.PSHTor) {k : ℕ} (hk : 0 < k) (m : Fin n → ℤ)
    (R : Finset (PolytopeToricRays γ hs)) (hR : IsToricFanCone (R : Set (PolytopeToricRays γ hs)))
    (c : PolytopeToricRays γ hs → ℝ) (hc : ∀ ρ ∈ R, 0 < c ρ) (hsum : ∑ ρ ∈ R, c ρ = 1)
    (hH : 1 < latticeFunctional m (-∑ ρ ∈ R, c ρ • latticeVector ρ.val) -
      k * h.newtonSupport u (-∑ ρ ∈ R, c ρ • latticeVector ρ.val)) :
    (fun a => (latticeCharacter m a : ℂ)) ∉
      toricMultiplierSections ((k : ℤ) • D) (by exact_mod_cast hk : (0 : ℝ) < k) (h.isQPSH_of_mem hu) := by
  classical
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  intro hmem
  have hlat := mem_toricLatticePoints_of_latticeCharacter_mem hmem.1
  obtain ⟨v, J, hRJ⟩ := hR
  -- the face `σ` of the maximal cone `σ_v`
  set J' : Finset (Fin n) := Finset.univ.filter (· ∈ J)
  have hRimage : R = J'.image (polytopeToricRay γ hs v) := by
    ext ρ
    have := congrArg (ρ ∈ ·) hRJ
    simp only [Finset.mem_coe, eq_iff_iff] at this
    rw [this, Finset.mem_image]
    simp [J']
  set U : Fin n → EuclideanSpace ℝ (Fin n) := fun j =>
    latticeVector (polytopeToricRayGenerator γ hs v j)
  have hsumU : ∑ ρ ∈ R, c ρ • latticeVector ρ.val = ∑ j ∈ J', c (polytopeToricRay γ hs v j) • U j := by
    rw [hRimage, Finset.sum_image fun _ _ _ _ hij => polytopeToricRay_injective v hij]
    rfl
  have hsumc : ∑ ρ ∈ R, c ρ = ∑ j ∈ J', c (polytopeToricRay γ hs v j) := by
    rw [hRimage, Finset.sum_image fun _ _ _ _ hij => polytopeToricRay_injective v hij]
  set u₀ := ∑ ρ ∈ R, c ρ • latticeVector ρ.val
  -- perturbed coefficients on all rays of `σ_v`
  obtain ⟨ρ₀, hρ₀0, hρ₀⟩ := h.exists_newtonSupport_le_add hu
  set Ru : ℝ := ∑ j, ‖U j‖
  set Lc : ℝ := (‖latticeVector m‖ + k * ρ₀) * Ru + n
  set gap : ℝ := latticeFunctional m (-u₀) - k * h.newtonSupport u (-u₀) - 1
  have hgap : 0 < gap := by simp only [gap]; linarith
  set ε : ℝ := gap / (2 * (Lc + 1))
  have hLc : 0 ≤ Lc := by positivity
  have hε : 0 < ε := by positivity
  set c' : Fin n → ℝ := fun j => if j ∈ J' then c (polytopeToricRay γ hs v j) else ε
  have hc' : ∀ j, 0 < c' j := by
    intro j
    by_cases hj : j ∈ J'
    · simp only [c', if_pos hj]
      exact hc _ (by rw [hRimage]; exact Finset.mem_image_of_mem _ hj)
    · simp only [c', if_neg hj]; exact hε
  set E : EuclideanSpace ℝ (Fin n) := ∑ j ∈ Finset.univ.filter (· ∉ J'), U j
  have hu' : ∑ j, c' j • U j = u₀ + ε • E := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ J')]
    simp only [c', E, Finset.smul_sum]
    congr 1
    · rw [hsumU]
      refine Finset.sum_congr (by ext j; simp [J']) fun j hj => ?_
      rw [if_pos hj]
    · exact Finset.sum_congr rfl fun j hj => by
        simp only [Finset.mem_filter] at hj
        rw [if_neg hj.2]
  have hsumc' : ∑ j, c' j ≤ 1 + ε * n := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ J')]
    have h1 : ∑ j ∈ Finset.univ.filter (· ∈ J'), c' j = 1 := by
      rw [← hsum, hsumc]
      refine Finset.sum_congr (by ext j; simp [J']) fun j hj => ?_
      simp only [c', if_pos hj]
    have h2 : ∑ j ∈ Finset.univ.filter (· ∉ J'), c' j ≤ ε * n := by
      calc ∑ j ∈ Finset.univ.filter (· ∉ J'), c' j = ∑ j ∈ Finset.univ.filter (· ∉ J'), ε :=
            Finset.sum_congr rfl fun j hj => by
              simp only [Finset.mem_filter] at hj; simp only [c', if_neg hj.2]
        _ = (Finset.univ.filter (· ∉ J')).card * ε := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ n * ε := by
            apply mul_le_mul_of_nonneg_right _ hε.le
            have := Finset.card_filter_le Finset.univ (· ∉ J')
            rw [Finset.card_univ, Fintype.card_fin] at this
            exact_mod_cast this
        _ = ε * n := mul_comm _ _
    linarith
  have hEnorm : ‖E‖ ≤ Ru := by
    refine (norm_sum_le _ _).trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun _ _ _ => norm_nonneg _
  have hH' : ∑ j, c' j < latticeFunctional m (-∑ j, c' j • U j) -
      k * h.newtonSupport u (-∑ j, c' j • U j) := by
    rw [hu']
    have hS : h.newtonSupport u (-(u₀ + ε • E)) ≤ h.newtonSupport u (-u₀) + ρ₀ * (ε * Ru) := by
      have := hρ₀ (-(u₀ + ε • E)) (-u₀)
      have hn : ‖-(u₀ + ε • E) - -u₀‖ = ε * ‖E‖ := by
        rw [neg_add, add_sub_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg hε.le]
      rw [hn] at this
      have : ρ₀ * (ε * ‖E‖) ≤ ρ₀ * (ε * Ru) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEnorm hε.le) hρ₀0
      linarith
    have hm1 : latticeFunctional m (-u₀) - ‖latticeVector m‖ * (ε * Ru) ≤
        latticeFunctional m (-(u₀ + ε • E)) := by
      have heq : latticeFunctional m (-(u₀ + ε • E)) =
          latticeFunctional m (-u₀) - ε * inner ℝ (latticeVector m) E := by
        rw [← inner_latticeVector, ← inner_latticeVector, neg_add, inner_add_right,
          inner_neg_right (y := ε • E), inner_smul_right]
        ring
      rw [heq]
      have h1 := real_inner_le_norm (latticeVector m) E
      have h2 : ‖latticeVector m‖ * ‖E‖ ≤ ‖latticeVector m‖ * Ru :=
        mul_le_mul_of_nonneg_left hEnorm (norm_nonneg _)
      have h3 : ε * inner ℝ (latticeVector m) E ≤ ε * (‖latticeVector m‖ * Ru) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) hε.le
      nlinarith
    have hkS : (k : ℝ) * h.newtonSupport u (-(u₀ + ε • E)) ≤
        k * (h.newtonSupport u (-u₀) + ρ₀ * (ε * Ru)) := mul_le_mul_of_nonneg_left hS hkpos.le
    have hεbound : ε * (Lc + 1) < gap := by
      simp only [ε]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    have : ε * ((‖latticeVector m‖ + k * ρ₀) * Ru + n) < gap := by
      have : ε * ((‖latticeVector m‖ + k * ρ₀) * Ru + n) ≤ ε * (Lc + 1) :=
        mul_le_mul_of_nonneg_left (by simp only [Lc]; linarith) hε.le
      linarith
    simp only [gap] at this
    nlinarith
  apply h.not_multiplierIntegrableAt_toricMonomial hu hk hlat v c' hc' hH'
  have hcoeff := (mem_toricMultiplierSections_iff _ _ _).mp hmem
  exact hcoeff.2 v _ (differentiable_toricMonomial _ v m).continuous
    (latticeCharacter_eq_toricMonomial _ hlat v) 0

end BigToricMetric

/-! ### The ample case: the source statement -/

/-- The Newton body of the big chapter for the Guillemin metric is the Newton body
`Δ(ω, φ)` of the ample chapter. -/
theorem guilleminBigToricMetric_newtonBody {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) :
    (guilleminBigToricMetric γ hs).newtonBody u = polytopeToricNewtonBody γ hs u := by
  rw [BigToricMetric.newtonBody, guilleminBigToricMetric_profile,
    polytopeToricNewtonBody_eq_closure_rawSubgradientImage γ hs hu]

/-- `ω`-psh functions are quasi-psh. -/
theorem isQPSH_of_mem_polytopeToricPSH {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) :
    (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH u := ⟨_, hu.1⟩

variable (γ hs) in
/-- Source `thm:Yao`: the space `H⁰(X, L ⊗ 𝓘(φ))`, `L = O(D_P)` the ample line bundle of the
Delzant polytope `P` (with its Guillemin metric, curvature `ω`), for `φ ∈ PSH_tor(X, ω)`. -/
abbrev ampleMultiplierSections {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) : Submodule ℂ ((Fin n → ℂˣ) → ℂ) :=
  toricMultiplierSections (polytopeToricAmpleDivisor γ hs) one_pos (isQPSH_of_mem_polytopeToricPSH hu)

/-- Source `thm:Yao` (1): for `φ ∈ PSH_tor(X, ω)` and `m ∈ M ∩ Δ(ω, φ)`,
`χ^m ∈ H⁰(X, L ⊗ 𝓘(φ))`. -/
theorem yao_mem {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ PolytopeToricPSH γ hs)
    {m : Fin n → ℤ} (hm : latticeVector m ∈ polytopeToricNewtonBody γ hs u) :
    (fun a => (latticeCharacter m a : ℂ)) ∈ ampleMultiplierSections γ hs hu := by
  have hu' : u ∈ (guilleminBigToricMetric γ hs).PSHTor := hu
  have h := (guilleminBigToricMetric γ hs).latticeCharacter_mem_toricMultiplierSections hu'
    one_pos (m := m) (by
      rw [guilleminBigToricMetric_newtonBody hu, Nat.cast_one, one_smul]; exact hm)
  rwa [toricMultiplierSections_congr (by rw [Nat.cast_one, one_smul]) Nat.cast_one] at h

/-- Source `thm:Yao` (2): for `φ ∈ PSH_tor(X, ω)`, a cone `σ ∈ Σ` with rays `R = σ(1)`,
`c_ρ > 0` on `R` with `∑_{ρ ∈ R} c_ρ = 1` and `u = ∑_{ρ ∈ R} c_ρ u_ρ`, if
`⟨m, -u⟩ - Supp_{Δ(ω, φ)}(-u) > 1` then `χ^m ∉ H⁰(X, L ⊗ 𝓘(φ))`. -/
theorem yao_not_mem {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ PolytopeToricPSH γ hs)
    (m : Fin n → ℤ) (R : Finset (PolytopeToricRays γ hs))
    (hR : IsToricFanCone (R : Set (PolytopeToricRays γ hs)))
    (c : PolytopeToricRays γ hs → ℝ) (hc : ∀ ρ ∈ R, 0 < c ρ) (hsum : ∑ ρ ∈ R, c ρ = 1)
    (hH : (1 : EReal) <
      ((latticeFunctional m (-∑ ρ ∈ R, c ρ • latticeVector ρ.val) : ℝ) : EReal) -
        support (innerₗ (EuclideanSpace ℝ (Fin n))).flip (polytopeToricNewtonBody γ hs u)
          (-∑ ρ ∈ R, c ρ • latticeVector ρ.val)) :
    (fun a => (latticeCharacter m a : ℂ)) ∉ ampleMultiplierSections γ hs hu := by
  have hu' : u ∈ (guilleminBigToricMetric γ hs).PSHTor := hu
  rw [← guilleminBigToricMetric_newtonBody hu,
    (guilleminBigToricMetric γ hs).support_newtonBody_eq hu', ← EReal.coe_sub, ← EReal.coe_one,
    EReal.coe_lt_coe_iff] at hH
  have h := (guilleminBigToricMetric γ hs).latticeCharacter_not_mem_toricMultiplierSections hu'
    one_pos m R hR c hc hsum (by rw [Nat.cast_one, one_mul]; exact hH)
  rwa [toricMultiplierSections_congr (by rw [Nat.cast_one, one_smul]) Nat.cast_one] at h

end SGPT.Toric
