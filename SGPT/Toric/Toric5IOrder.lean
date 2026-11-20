import SGPT.Toric.Toric5Volume
import SGPT.Toric.Toric3PEquivalence
import SGPT.PSH.SourceComparisonEnvelopeCharacterizations

/-!
# The `𝓘`-order of toric potentials

Source `chapter_toric_big.tex`, `cor:PequivtorD`: for `φ, ψ ∈ PSH_tor(X, θ)` the following are
equivalent: (1) `φ ≼_P ψ`; (2) `φ ≼_𝓘 ψ`; (3) `Δ(θ, φ) ⊆ Δ(θ, ψ)`; and `cor:bij_conv_torpsh`:
`PSH_tor(X, θ)/∼_P = PSH_tor(X, θ)/∼_𝓘`.

(1) ⇔ (3) is `BigToricMetric.sourcePOrder_iff_newtonBody_subset_all` and (1) ⇒ (2) is
`cor:PimpliesI` (`sourceIOrder_of_sourcePOrder`).  The source deduces (2) ⇒ (1) from the
`𝓘`-goodness of toric potentials (`ex:toricIgood`, which uses `thm:DXmain1`).  Here (2) ⇒ (3)
is proved directly from Yao's theorem for all powers `L^k`, `kφ`:

* if `Δ(θ, φ)` has interior points, every interior point `x` is approximated by `m_k / k` with
  `m_k = round(k x) ∈ kΔ(θ, φ) ∩ M`; then `χ^{m_k} ∈ H⁰(X, L^k ⊗ 𝓘(kφ)) ⊆ H⁰(X, L^k ⊗ 𝓘(kψ))`
  (the `𝓘`-order compares the multiplier ideals at every level), so `m_k` lies within the
  uniform distance `Λ` of `kΔ(θ, ψ)` (`exists_dist_le_of_mem`), and `x ∈ Δ(θ, ψ)`;
* in general, the `𝓘`-order does not depend on `θ`: in the background `θ + ω`
  (`BigToricMetric.addGuillemin`) the Newton bodies are `Δ(θ, ·) + P`, which have interior points,
  and the Minkowski summand `P` cancels (`subset_of_add_subset_add`).
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

/-- `φ ≼_𝓘 ψ` gives `H⁰(X, O(D) ⊗ 𝓘(cφ)) ⊆ H⁰(X, O(D) ⊗ 𝓘(cψ))`. -/
theorem toricMultiplierSections_mono_of_sourceIOrder {D : ToricDivisor γ hs} {c : ℝ} (hc : 0 < c)
    {φ ψ : PolytopeToricVariety γ hs → EReal}
    (hI : sourceIOrder (ofFixedModel n (PolytopeToricVariety γ hs)) φ ψ)
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hψ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH ψ) :
    toricMultiplierSections D hc hφ ≤ toricMultiplierSections D hc hψ := by
  have hle := Pending.PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_iOrderOnManifold
    ((sourceIOrder_iff_native hI.1 hI.2.1).mp hI) hc
  rintro g ⟨hg, hcoef⟩
  exact ⟨hg, fun v f hf hgf x hx => hle x _ (hcoef v f hf hgf x hx)⟩

/-- The nearest lattice point `round(k x)` is within distance `n + 1` of `k x`. -/
theorem norm_latticeVector_round_sub_le (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    ‖latticeVector (fun i => round (t * x i)) - t • x‖ ≤ n + 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hcoord : ∀ i, ‖(latticeVector (fun i => round (t * x i)) - t • x) i‖ ^ 2 ≤ 1 := by
    intro i
    simp only [PiLp.sub_apply, latticeVector_apply, PiLp.smul_apply, smul_eq_mul,
      Real.norm_eq_abs, sq_abs]
    have h1 := abs_sub_round (t * x i)
    rw [abs_sub_comm] at h1
    have h2 : |((round (t * x i) : ℤ) : ℝ) - t * x i| ^ 2 ≤ (1 / 2) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs] at h2
    linarith
  calc ∑ i, ‖(latticeVector (fun i => round (t * x i)) - t • x) i‖ ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => hcoord i
    _ = n := by simp
    _ ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith

namespace BigToricMetric

variable {D : ToricDivisor γ hs} (h : BigToricMetric D)

/-- Source `cor:PequivtorD`, (2) ⇒ (3), when `Δ(θ, φ)` has interior points. -/
theorem newtonBody_subset_of_sourceIOrder_of_interior {φ ψ : PolytopeToricVariety γ hs → EReal}
    (hφ : φ ∈ h.PSHTor) (hψ : ψ ∈ h.PSHTor)
    (hI : sourceIOrder (ofFixedModel n (PolytopeToricVariety γ hs)) φ ψ)
    (hint : (interior (h.newtonBody φ)).Nonempty) : h.newtonBody φ ⊆ h.newtonBody ψ := by
  have hP := h.nonempty_toricDivisorPolytope_of_mem hφ
  obtain ⟨-, hcφ, hvφ, -⟩ := h.newtonBody_properties hP hφ
  obtain ⟨-, hcψ, -, -⟩ := h.newtonBody_properties hP hψ
  obtain ⟨Λ, hΛ0, hΛ⟩ := h.exists_dist_le_of_mem hψ
  suffices hsub : interior (h.newtonBody φ) ⊆ h.newtonBody ψ by
    calc h.newtonBody φ = closure (h.newtonBody φ) := hcφ.isClosed.closure_eq.symm
      _ = closure (interior (h.newtonBody φ)) :=
          (hvφ.closure_interior_eq_closure_of_nonempty_interior hint).symm
      _ ⊆ closure (h.newtonBody ψ) := closure_mono hsub
      _ = h.newtonBody ψ := hcψ.isClosed.closure_eq
  intro x hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  rw [← hcψ.isClosed.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  -- a large `k`
  set B : ℝ := max (((n : ℝ) + 1) / r) (((n : ℝ) + 1 + Λ) / ε)
  set k : ℕ := ⌈B⌉₊ + 1
  have hkB : B < k := by
    have := Nat.le_ceil B
    simp only [k]; push_cast; linarith
  have hk : 0 < k := Nat.succ_pos _
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hkr : ((n : ℝ) + 1) / k < r := by
    rw [div_lt_iff₀ hkpos]
    have : ((n : ℝ) + 1) / r < k := lt_of_le_of_lt (le_max_left _ _) hkB
    rw [div_lt_iff₀ hr] at this
    linarith
  have hkε : ((n : ℝ) + 1 + Λ) / k < ε := by
    rw [div_lt_iff₀ hkpos]
    have : ((n : ℝ) + 1 + Λ) / ε < k := lt_of_le_of_lt (le_max_right _ _) hkB
    rw [div_lt_iff₀ hε] at this
    linarith
  -- the lattice point `m = round(k x)`
  set m : Fin n → ℤ := fun i => round ((k : ℝ) * x i)
  have hround := norm_latticeVector_round_sub_le x (k : ℝ)
  have hmΔ : latticeVector m ∈ (k : ℝ) • h.newtonBody φ := by
    refine ⟨(k : ℝ)⁻¹ • latticeVector m, interior_subset (hball ?_), ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      have : (k : ℝ)⁻¹ • latticeVector m - x = (k : ℝ)⁻¹ • (latticeVector m - (k : ℝ) • x) := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ hkpos.ne', one_smul]
      rw [this, norm_smul, Real.norm_of_nonneg (by positivity), ← div_eq_inv_mul]
      calc ‖latticeVector m - (k : ℝ) • x‖ / k ≤ ((n : ℝ) + 1) / k :=
            div_le_div_of_nonneg_right hround hkpos.le
        _ < r := hkr
    · show (k : ℝ) • ((k : ℝ)⁻¹ • latticeVector m) = latticeVector m
      rw [smul_smul, mul_inv_cancel₀ hkpos.ne', one_smul]
  have hmem := h.latticeCharacter_mem_toricMultiplierSections hφ hk hmΔ
  have hmem' := toricMultiplierSections_mono_of_sourceIOrder _ hI _ (h.isQPSH_of_mem hψ) hmem
  obtain ⟨p, hp, hd⟩ := hΛ k hk m hmem'
  obtain ⟨y, hy, rfl⟩ := hp
  refine ⟨y, hy, ?_⟩
  rw [dist_eq_norm]
  have hsplit : x - y = (k : ℝ)⁻¹ • (((k : ℝ) • x - latticeVector m) +
      (latticeVector m - (k : ℝ) • y)) := by
    rw [sub_add_sub_cancel, smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hkpos.ne', one_smul,
      one_smul]
  rw [hsplit, norm_smul, Real.norm_of_nonneg (by positivity), ← div_eq_inv_mul]
  have h1 : ‖(k : ℝ) • x - latticeVector m‖ ≤ n + 1 := by rw [norm_sub_rev]; exact hround
  have h2 : ‖latticeVector m - (k : ℝ) • y‖ ≤ Λ := by rw [← dist_eq_norm]; exact hd
  calc ‖((k : ℝ) • x - latticeVector m) + (latticeVector m - (k : ℝ) • y)‖ / k
      ≤ ((n : ℝ) + 1 + Λ) / k :=
        div_le_div_of_nonneg_right ((norm_add_le _ _).trans (by linarith)) hkpos.le
    _ < ε := hkε

/-- Source `cor:PequivtorD`, (2) ⇒ (3): `φ ≼_𝓘 ψ ⇒ Δ(θ, φ) ⊆ Δ(θ, ψ)`, for all toric potentials. -/
theorem newtonBody_subset_of_sourceIOrder {φ ψ : PolytopeToricVariety γ hs → EReal}
    (hφ : φ ∈ h.PSHTor) (hψ : ψ ∈ h.PSHTor)
    (hI : sourceIOrder (ofFixedModel n (PolytopeToricVariety γ hs)) φ ψ) :
    h.newtonBody φ ⊆ h.newtonBody ψ := by
  have hP := h.nonempty_toricDivisorPolytope_of_mem hφ
  have hφ' := h.mem_PSHTor_addGuillemin hφ
  have hψ' := h.mem_PSHTor_addGuillemin hψ
  have hint : (interior (h.addGuillemin.newtonBody φ)).Nonempty := by
    rw [h.newtonBody_addGuillemin hP hφ]
    obtain ⟨x₀, hx₀⟩ := (h.newtonBody_properties hP hφ).1
    obtain ⟨p₀, hp₀⟩ := interior_polytopeToricMomentPolytope_nonempty γ hs
    exact ⟨x₀ + p₀, subset_interior_add_right ⟨x₀, hx₀, p₀, hp₀, rfl⟩⟩
  have hsub := h.addGuillemin.newtonBody_subset_of_sourceIOrder_of_interior hφ' hψ' hI hint
  rw [h.newtonBody_addGuillemin hP hφ, h.newtonBody_addGuillemin hP hψ] at hsub
  obtain ⟨-, hcψ, hvψ, -⟩ := h.newtonBody_properties hP hψ
  exact subset_of_add_subset_add hcψ.isClosed hvψ (isCompact_polytopeToricMomentPolytope γ).isBounded
    (nonempty_polytopeToricMomentPolytope γ) hsub

/-- Source `cor:PequivtorD`, (2) ⇔ (3): `φ ≼_𝓘 ψ ⇔ Δ(θ, φ) ⊆ Δ(θ, ψ)`. -/
theorem sourceIOrder_iff_newtonBody_subset {φ ψ : PolytopeToricVariety γ hs → EReal}
    (hφ : φ ∈ h.PSHTor) (hψ : ψ ∈ h.PSHTor) :
    sourceIOrder (ofFixedModel n (PolytopeToricVariety γ hs)) φ ψ ↔
      h.newtonBody φ ⊆ h.newtonBody ψ := by
  refine ⟨h.newtonBody_subset_of_sourceIOrder hφ hψ, fun hsub => ?_⟩
  have hP := h.nonempty_toricDivisorPolytope_of_mem hφ
  exact sourceIOrder_of_sourcePOrder (h.isQPSH_of_mem hφ) (h.isQPSH_of_mem hψ)
    ((h.sourcePOrder_iff_newtonBody_subset_all hP hφ hψ).mpr hsub)

/-- Source `cor:PequivtorD`, (1) ⇔ (2): `φ ≼_P ψ ⇔ φ ≼_𝓘 ψ`. -/
theorem sourcePOrder_iff_sourceIOrder {φ ψ : PolytopeToricVariety γ hs → EReal}
    (hφ : φ ∈ h.PSHTor) (hψ : ψ ∈ h.PSHTor) :
    GlobalPComparison.sourcePOrder (n := n) φ ψ ↔
      sourceIOrder (ofFixedModel n (PolytopeToricVariety γ hs)) φ ψ := by
  rw [h.sourceIOrder_iff_newtonBody_subset hφ hψ,
    h.sourcePOrder_iff_newtonBody_subset_all (h.nonempty_toricDivisorPolytope_of_mem hφ) hφ hψ]

/-- Source `cor:PequivtorD`: the three conditions (1) `φ ≼_P ψ`, (2) `φ ≼_𝓘 ψ`,
(3) `Δ(θ, φ) ⊆ Δ(θ, ψ)` are equivalent, for all `φ, ψ ∈ PSH_tor(X, θ)`. -/
theorem pequivtorD {φ ψ : PolytopeToricVariety γ hs → EReal}
    (hφ : φ ∈ h.PSHTor) (hψ : ψ ∈ h.PSHTor) :
    (GlobalPComparison.sourcePOrder (n := n) φ ψ ↔
        sourceIOrder (ofFixedModel n (PolytopeToricVariety γ hs)) φ ψ) ∧
      (sourceIOrder (ofFixedModel n (PolytopeToricVariety γ hs)) φ ψ ↔
        h.newtonBody φ ⊆ h.newtonBody ψ) :=
  ⟨h.sourcePOrder_iff_sourceIOrder hφ hψ, h.sourceIOrder_iff_newtonBody_subset hφ hψ⟩

/-- Source `cor:bij_conv_torpsh`: `φ ∼_𝓘 ψ ⇔ Δ(θ, φ) = Δ(θ, ψ)`. -/
theorem sourceIEquivalent_iff_newtonBody_eq {φ ψ : PolytopeToricVariety γ hs → EReal}
    (hφ : φ ∈ h.PSHTor) (hψ : ψ ∈ h.PSHTor) :
    sourceIEquivalent (ofFixedModel n (PolytopeToricVariety γ hs)) φ ψ ↔
      h.newtonBody φ = h.newtonBody ψ := by
  change sourceIOrder _ φ ψ ∧ sourceIOrder _ ψ φ ↔ _
  rw [h.sourceIOrder_iff_newtonBody_subset hφ hψ, h.sourceIOrder_iff_newtonBody_subset hψ hφ]
  exact ⟨fun h' => Subset.antisymm h'.1 h'.2, fun h' => ⟨h'.le, h'.ge⟩⟩

/-- Source `cor:bij_conv_torpsh`: `PSH_tor(X, θ)/∼_P = PSH_tor(X, θ)/∼_𝓘`, i.e.
`φ ∼_P ψ ⇔ φ ∼_𝓘 ψ`. -/
theorem sourcePEquivalent_iff_sourceIEquivalent {φ ψ : PolytopeToricVariety γ hs → EReal}
    (hφ : φ ∈ h.PSHTor) (hψ : ψ ∈ h.PSHTor) :
    GlobalPComparison.sourcePEquivalent (n := n) φ ψ ↔
      sourceIEquivalent (ofFixedModel n (PolytopeToricVariety γ hs)) φ ψ := by
  rw [h.sourceIEquivalent_iff_newtonBody_eq hφ hψ,
    h.sourcePEquivalent_iff_newtonBody_eq_all (h.nonempty_toricDivisorPolytope_of_mem hφ) hφ hψ]

end BigToricMetric

end SGPT.Toric
