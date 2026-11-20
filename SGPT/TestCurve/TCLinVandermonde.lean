import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Separating weights by finitely many points of `𝔾_m`

Lane TC-LIN (linearized test configurations, [BHJ17, Def. 2.2 and Prop. 2.15]). A vector of a
`𝔾_m`-representation is a finite sum `v = Σ_ν v_ν` of weight vectors, and the action of
`c ∈ ℂ^*` is `c · v = Σ_ν c^ν v_ν`. Every weight component `v_μ` is a linear combination of
finitely many translates `c · v` (an interpolation / Vandermonde argument), and a family of
weight vectors with `Σ_ν c^ν v_ν = 0` for all `c` vanishes.

## Main results

* `exists_interpolation`: for a finite set `S ⊆ ℤ` and `μ ∈ ℤ` there are finitely many
  `c ∈ ℂ^*` and coefficients `b_c` with `Σ_c b_c c^ν = δ_{νμ}` for every `ν ∈ S`.
* `eq_zero_of_forall_sum_zpow_mul`: if `Σ_{ν ∈ S} κ(c^ν) b_ν = 0` for every `c ∈ ℂ^*`
  (`κ : ℂ →+* A`), then every `b_ν` vanishes.
* `eq_sum_zpow_smul`: the weight component formula `v_μ = Σ_c b_c • (Σ_ν c^ν v_ν)`.

The proof of `exists_interpolation` uses Artin's linear independence of the characters
`c ↦ c^ν` of `ℂ^*` (Mathlib's `linearIndependent_monoidHom`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.TestCurve.TCLin

open Finset

/-- The character `c ↦ c^ν` of `ℂ^*`. -/
def zpowChar (ν : ℤ) : ℂˣ →* ℂ := (Units.coeHom ℂ).comp (zpowGroupHom ν)

@[simp] theorem zpowChar_apply (ν : ℤ) (c : ℂˣ) : zpowChar ν c = ((c ^ ν : ℂˣ) : ℂ) := rfl

theorem zpowChar_injective : Function.Injective zpowChar := by
  intro ν ν' h
  have h2 := DFunLike.congr_fun h (Units.mk0 (2 : ℂ) two_ne_zero)
  simp only [zpowChar_apply, Units.val_zpow_eq_zpow_val, Units.val_mk0] at h2
  have h2' : ((2 : ℝ) ^ ν : ℝ) = (2 : ℝ) ^ ν' := by
    have := congrArg Complex.re h2
    rwa [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_zpow, ← Complex.ofReal_zpow,
      Complex.ofReal_re, Complex.ofReal_re] at this
  exact zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num) h2'

/-- The characters `c ↦ c^ν`, `ν ∈ S`, are linearly independent: a vanishing combination
`Σ_ν β_ν c^ν = 0` (for all `c ∈ ℂ^*`) is trivial. -/
theorem eq_zero_of_forall_sum_zpow (S : Finset ℤ) (β : ℤ → ℂ)
    (h : ∀ c : ℂˣ, ∑ ν ∈ S, β ν * ((c ^ ν : ℂˣ) : ℂ) = 0) : ∀ ν ∈ S, β ν = 0 := by
  have hli : LinearIndependent ℂ (fun ν : S => (zpowChar (ν : ℤ) : ℂˣ → ℂ)) :=
    (linearIndependent_monoidHom ℂˣ ℂ).comp (fun ν : S => zpowChar (ν : ℤ))
      (zpowChar_injective.comp Subtype.val_injective)
  have hsum : ∑ ν : S, β ν • (zpowChar (ν : ℤ) : ℂˣ → ℂ) = 0 := by
    funext c
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, zpowChar_apply, Pi.zero_apply]
    rw [Finset.sum_coe_sort S (fun ν => β ν * ((c ^ ν : ℂˣ) : ℂ))]
    exact h c
  intro ν hν
  exact Fintype.linearIndependent_iff.mp hli (fun ν : S => β ν) hsum ⟨ν, hν⟩

/-- **Interpolation of a weight**: for a finite set `S ⊆ ℤ` and `μ ∈ ℤ` there are finitely many
`c ∈ ℂ^*` and coefficients `b_c` with `Σ_c b_c c^ν = δ_{νμ}` for all `ν ∈ S`. -/
theorem exists_interpolation (S : Finset ℤ) (μ : ℤ) :
    ∃ (C : Finset ℂˣ) (b : ℂˣ → ℂ), ∀ ν ∈ S,
      ∑ c ∈ C, b c * ((c ^ ν : ℂˣ) : ℂ) = if ν = μ then 1 else 0 := by
  classical
  let v : ℂˣ → (S → ℂ) := fun c ν => ((c ^ (ν : ℤ) : ℂˣ) : ℂ)
  have htop : Submodule.span ℂ (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    apply hφ
    have hφv : ∀ x : S → ℂ, φ x = ∑ ν : S, x ν * φ (Pi.single ν 1) := by
      intro x
      conv_lhs => rw [show x = ∑ ν : S, x ν • Pi.single ν (1 : ℂ) by
        ext ν'; simp [Finset.sum_apply, Pi.single_apply]]
      simp [map_sum, map_smul]
    have hβ := eq_zero_of_forall_sum_zpow S
      (fun ν => if h : ν ∈ S then φ (Pi.single ⟨ν, h⟩ 1) else 0) (by
        intro c
        have h0 : φ (v c) = 0 := hle (Submodule.subset_span ⟨c, rfl⟩)
        rw [hφv] at h0
        rw [← Finset.sum_coe_sort S]
        refine Eq.trans ?_ h0
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [dif_pos ν.2]
        simp only [Subtype.coe_eta, v]
        ring)
    apply LinearMap.ext
    intro x
    rw [hφv, LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun ν _ => ?_
    have := hβ ν ν.2
    rw [dif_pos ν.2] at this
    simp only [Subtype.coe_eta] at this
    rw [this, mul_zero]
  let e : S → ℂ := fun ν => if (ν : ℤ) = μ then 1 else 0
  have he : e ∈ Submodule.span ℂ (Set.range v) := by rw [htop]; exact Submodule.mem_top
  obtain ⟨b, hb⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp he
  refine ⟨b.support, b, fun ν hν => ?_⟩
  have := congrFun hb ⟨ν, hν⟩
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v, e] at this
  exact this

/-- **Weight vectors of distinct weights are independent** (ring form): if
`Σ_{ν ∈ S} κ(c^ν) b_ν = 0` for every `c ∈ ℂ^*`, then every `b_ν`, `ν ∈ S`, vanishes. -/
theorem eq_zero_of_forall_sum_zpow_mul {A : Type*} [CommRing A] (κ : ℂ →+* A) (S : Finset ℤ)
    (b : ℤ → A) (h : ∀ c : ℂˣ, ∑ ν ∈ S, κ ((c ^ ν : ℂˣ) : ℂ) * b ν = 0) :
    ∀ μ ∈ S, b μ = 0 := by
  classical
  intro μ hμ
  obtain ⟨C, β, hβ⟩ := exists_interpolation S μ
  have key : ∑ ν ∈ S, (if ν = μ then b ν else 0) =
      ∑ c ∈ C, κ (β c) * ∑ ν ∈ S, κ ((c ^ ν : ℂˣ) : ℂ) * b ν := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν hν => ?_
    simp_rw [← mul_assoc, ← map_mul, ← Finset.sum_mul, ← map_sum, hβ ν hν]
    split_ifs <;> simp
  simp only [Finset.sum_ite_eq', hμ, if_true] at key
  rw [key]
  exact Finset.sum_eq_zero fun c _ => by rw [h c, mul_zero]

/-- **The weight component formula** (module form): for `v_ν ∈ M`, `ν ∈ S`, and `μ ∈ S`,
`v_μ = Σ_c b_c • Σ_ν c^ν • v_ν` with the interpolation coefficients of `exists_interpolation`. -/
theorem eq_sum_zpow_smul {M : Type*} [AddCommGroup M] [Module ℂ M] (S : Finset ℤ) (v : ℤ → M)
    {μ : ℤ} (hμ : μ ∈ S) :
    ∃ (C : Finset ℂˣ) (b : ℂˣ → ℂ),
      v μ = ∑ c ∈ C, b c • ∑ ν ∈ S, ((c ^ ν : ℂˣ) : ℂ) • v ν := by
  classical
  obtain ⟨C, β, hβ⟩ := exists_interpolation S μ
  refine ⟨C, β, ?_⟩
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have : ∀ ν ∈ S, ∑ c ∈ C, (β c * ((c ^ ν : ℂˣ) : ℂ)) • v ν = if ν = μ then v ν else 0 := by
    intro ν hν
    rw [← Finset.sum_smul, hβ ν hν]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl this]
  simp [hμ]

end SGPT.TestCurve.TCLin
