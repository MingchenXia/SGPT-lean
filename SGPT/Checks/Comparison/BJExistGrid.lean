import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Upper dyadic grid maxima of a Legendre-type supremum

Real-analysis step of the existence clause of `cor:testcurvegivepshme`
(`chapter_NApotential.tex`, *The algebraic setting*). For a non-Archimedean potential `Γ`,
`Γ^An(v) = sup_{τ < Γ_max} (Γ_τ^An(v) + τ)` (`eq:psiandef`). It is approximated from above by the
**upper dyadic grid maxima**

`D_a = max (F_lim(a) - a, max_{k} (F_a(k/2^a) + (k+1)/2^a))`,

the maximum over the integers `k` with `-a ≤ k/2^a < Γ_max` (`gridIndex`). Here `F_a(t)` is an
upper approximant of `Γ_t^An(v)` that decreases in `t` and in `a` and converges to `Γ_t^An(v)` as
`a → ∞` (in the application `F_a(t) = -J_a⁻¹ v(𝓘(J_a Γ_t))`), and `F_lim(a)` dominates every
`F_a(t)` (the same approximant of the limit potential `Γ_{-∞}`); the term `F_lim(a) - a` covers
the parameters `τ < -a`.

## Main results

* `gridApprox_succ_le`, `antitone_gridApprox`: `D_a` decreases in `a`.
* `iInf_gridApprox`: `inf_a D_a = sup_{τ < T} (A(τ) + τ)`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.BJ.Exist

open Filter Set
open scoped Topology

/-! ### The dyadic grid -/

/-- The integers `k` with `-a ≤ k/2^a < T`: the dyadic grid of mesh `2^{-a}` on `[-a, T)`. -/
def gridIndex (T : ℝ) (a : ℕ) : Finset ℤ :=
  (Finset.Icc (-(a : ℤ) * 2 ^ a) ⌈T * 2 ^ a⌉).filter fun k => (k : ℝ) / 2 ^ a < T

theorem mem_gridIndex {T : ℝ} {a : ℕ} {k : ℤ} :
    k ∈ gridIndex T a ↔ -(a : ℤ) * 2 ^ a ≤ k ∧ (k : ℝ) / 2 ^ a < T := by
  unfold gridIndex
  rw [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, ?_⟩, h2⟩
    have hpos : (0 : ℝ) < 2 ^ a := by positivity
    have hk : (k : ℝ) < T * 2 ^ a := (div_lt_iff₀ hpos).mp h2
    exact Int.cast_le.mp ((hk.trans_le (Int.le_ceil _)).le)

/-- The grid point `⌊τ 2^a⌋ / 2^a` below `τ ∈ [-a, T)`. -/
theorem floor_mem_gridIndex {T : ℝ} {a : ℕ} {τ : ℝ} (h1 : -(a : ℝ) ≤ τ) (h2 : τ < T) :
    ⌊τ * 2 ^ a⌋ ∈ gridIndex T a ∧ ((⌊τ * 2 ^ a⌋ : ℤ) : ℝ) / 2 ^ a ≤ τ ∧
      τ < (((⌊τ * 2 ^ a⌋ : ℤ) : ℝ) + 1) / 2 ^ a := by
  have hpos : (0 : ℝ) < 2 ^ a := by positivity
  have hle : ((⌊τ * 2 ^ a⌋ : ℤ) : ℝ) / 2 ^ a ≤ τ :=
    (div_le_iff₀ hpos).mpr (Int.floor_le _)
  refine ⟨mem_gridIndex.mpr ⟨?_, hle.trans_lt h2⟩, hle, ?_⟩
  · apply Int.le_floor.mpr
    push_cast
    nlinarith
  · exact (lt_div_iff₀ hpos).mpr (Int.lt_floor_add_one _)

/-! ### The grid maxima -/

/-- The upper dyadic grid maximum at level `a`:
`max (F_lim(a) - a, max_{k ∈ gridIndex T a} (F_a(k/2^a) + (k+1)/2^a))`. -/
def gridApprox (F : ℕ → ℝ → EReal) (Flim : ℕ → EReal) (T : ℝ) (a : ℕ) : EReal :=
  max (Flim a + ((-(a : ℝ) : ℝ) : EReal))
    (⨆ k : gridIndex T a, F a (((k : ℤ) : ℝ) / 2 ^ a) + (((((k : ℤ) : ℝ) + 1) / 2 ^ a : ℝ) : EReal))

theorem le_gridApprox_grid (F : ℕ → ℝ → EReal) (Flim : ℕ → EReal) (T : ℝ) (a : ℕ) {k : ℤ}
    (hk : k ∈ gridIndex T a) :
    F a ((k : ℝ) / 2 ^ a) + ((((k : ℝ) + 1) / 2 ^ a : ℝ) : EReal) ≤ gridApprox F Flim T a :=
  le_trans (le_iSup (fun k : gridIndex T a => F a (((k : ℤ) : ℝ) / 2 ^ a) +
    (((((k : ℤ) : ℝ) + 1) / 2 ^ a : ℝ) : EReal)) ⟨k, hk⟩) (le_max_right _ _)

theorem le_gridApprox_tail (F : ℕ → ℝ → EReal) (Flim : ℕ → EReal) (T : ℝ) (a : ℕ) :
    Flim a + ((-(a : ℝ) : ℝ) : EReal) ≤ gridApprox F Flim T a :=
  le_max_left _ _

section Hyp

variable {F : ℕ → ℝ → EReal} {Flim : ℕ → EReal} {T : ℝ}

/-- The grid maxima decrease. -/
theorem gridApprox_succ_le
    (hFlim : ∀ a t, t < T → F a t ≤ Flim a)
    (hanti_t : ∀ a s t, s ≤ t → t < T → F a t ≤ F a s)
    (hanti_a : ∀ a t, t < T → F (a + 1) t ≤ F a t)
    (hFlim_anti : ∀ a, Flim (a + 1) ≤ Flim a) (a : ℕ) :
    gridApprox F Flim T (a + 1) ≤ gridApprox F Flim T a := by
  apply max_le
  · refine le_trans (add_le_add (hFlim_anti a) (EReal.coe_le_coe_iff.mpr ?_))
      (le_gridApprox_tail F Flim T a)
    push_cast
    linarith
  · refine iSup_le fun ⟨k', hk'⟩ => ?_
    obtain ⟨hk'1, hk'2⟩ := mem_gridIndex.mp hk'
    have hpos : (0 : ℝ) < 2 ^ a := by positivity
    have h2 : (2 : ℝ) ^ (a + 1) = 2 * 2 ^ a := by ring
    set t' : ℝ := (k' : ℝ) / 2 ^ (a + 1) with ht'
    by_cases hcase : -(a : ℝ) ≤ t'
    · obtain ⟨hk, hle, hlt⟩ := floor_mem_gridIndex (a := a) hcase hk'2
      set k := ⌊t' * 2 ^ a⌋
      have hF : F (a + 1) t' ≤ F a ((k : ℝ) / 2 ^ a) :=
        (hanti_t (a + 1) _ _ hle hk'2).trans (hanti_a a _ (hle.trans_lt hk'2))
      refine le_trans (add_le_add hF (EReal.coe_le_coe_iff.mpr ?_))
        (le_gridApprox_grid F Flim T a hk)
      -- `k' + 1 ≤ 2 (k + 1)`
      have hlt' : (k' : ℝ) < 2 * ((k : ℝ) + 1) := by
        rw [ht', h2, div_lt_div_iff₀ (by positivity) hpos] at hlt
        nlinarith
      have hint : k' + 1 ≤ 2 * (k + 1) := by
        have : k' < 2 * (k + 1) := by exact_mod_cast hlt'
        omega
      have hint' : (k' : ℝ) + 1 ≤ 2 * ((k : ℝ) + 1) := by exact_mod_cast hint
      rw [h2, div_le_div_iff₀ (by positivity) hpos]
      nlinarith
    · rw [not_le] at hcase
      have hF : F (a + 1) t' ≤ Flim a := (hFlim (a + 1) t' hk'2).trans (hFlim_anti a)
      refine le_trans (add_le_add hF (EReal.coe_le_coe_iff.mpr ?_)) (le_gridApprox_tail F Flim T a)
      have hk'lt : (k' : ℝ) < -(a : ℝ) * 2 ^ (a + 1) := by
        rw [ht', div_lt_iff₀ (by positivity)] at hcase
        linarith
      have hint : k' + 1 ≤ -(a : ℤ) * 2 ^ (a + 1) := by
        have : k' < -(a : ℤ) * 2 ^ (a + 1) := by exact_mod_cast hk'lt
        omega
      have hint' : (k' : ℝ) + 1 ≤ -(a : ℝ) * 2 ^ (a + 1) := by exact_mod_cast hint
      rw [div_le_iff₀ (by positivity)]
      linarith

theorem antitone_gridApprox
    (hFlim : ∀ a t, t < T → F a t ≤ Flim a)
    (hanti_t : ∀ a s t, s ≤ t → t < T → F a t ≤ F a s)
    (hanti_a : ∀ a t, t < T → F (a + 1) t ≤ F a t)
    (hFlim_anti : ∀ a, Flim (a + 1) ≤ Flim a) :
    Antitone (gridApprox F Flim T) :=
  antitone_nat_of_succ_le (gridApprox_succ_le hFlim hanti_t hanti_a hFlim_anti)

/-- Every term `A(τ) + τ` of the supremum lies below every grid maximum. -/
theorem le_gridApprox {A : ℝ → EReal} (hFA : ∀ a t, t < T → A t ≤ F a t)
    (hFlim : ∀ a t, t < T → F a t ≤ Flim a)
    (hanti_t : ∀ a s t, s ≤ t → t < T → F a t ≤ F a s) (a : ℕ) {τ : ℝ} (hτ : τ < T) :
    A τ + (τ : EReal) ≤ gridApprox F Flim T a := by
  by_cases hcase : -(a : ℝ) ≤ τ
  · obtain ⟨hk, hle, hlt⟩ := floor_mem_gridIndex (a := a) hcase hτ
    exact le_trans (add_le_add ((hFA a τ hτ).trans (hanti_t a _ _ hle hτ))
      (EReal.coe_le_coe_iff.mpr hlt.le)) (le_gridApprox_grid F Flim T a hk)
  · rw [not_le] at hcase
    exact le_trans (add_le_add ((hFA a τ hτ).trans (hFlim a τ hτ))
      (EReal.coe_le_coe_iff.mpr hcase.le)) (le_gridApprox_tail F Flim T a)

/-- **The grid maxima converge to the Legendre-type supremum**:
`inf_a D_a = sup_{τ < T} (A(τ) + τ)`. -/
theorem iInf_gridApprox {A : ℝ → EReal} (hFA : ∀ a t, t < T → A t ≤ F a t)
    (hFlim : ∀ a t, t < T → F a t ≤ Flim a)
    (hanti_t : ∀ a s t, s ≤ t → t < T → F a t ≤ F a s)
    (hlim : ∀ t, t < T → Tendsto (fun a => F a t) atTop (𝓝 (A t)))
    (hnonpos : ∀ a t, t < T → F a t ≤ 0) (hFlim_nonpos : ∀ a, Flim a ≤ 0) :
    ⨅ a, gridApprox F Flim T a = ⨆ τ : Iio T, A τ + ((τ : ℝ) : EReal) := by
  set S := ⨆ τ : Iio T, A τ + ((τ : ℝ) : EReal) with hS
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro c hc
    obtain ⟨c₀, hSc₀, hc₀c⟩ := EReal.lt_iff_exists_real_btwn.mp hc
    obtain ⟨c₁, hc₀c₁, hc₁c⟩ := EReal.lt_iff_exists_real_btwn.mp hc₀c
    have hc₀₁ : c₀ < c₁ := EReal.coe_lt_coe_iff.mp hc₀c₁
    refine le_trans ?_ hc₁c.le
    set η : ℝ := (c₁ - c₀) / 3 with hη
    have hηpos : 0 < η := by rw [hη]; linarith
    obtain ⟨N₁, hN₁⟩ := exists_pow_lt_of_lt_one hηpos (by norm_num : (1 / 2 : ℝ) < 1)
    set b₀ : ℕ := max N₁ ⌈1 - c₁⌉₊ with hb₀
    have hb₀η : (1 / 2 : ℝ) ^ b₀ < η :=
      lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_left _ _)) hN₁
    have hb₀c : 1 - c₁ ≤ (b₀ : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right N₁ ⌈1 - c₁⌉₊)
    -- eventually, at every grid point of level `b₀`, `F_a(s) < c₀ - s`
    have hev : ∀ᶠ a in atTop, ∀ k ∈ gridIndex T b₀,
        F a ((k : ℝ) / 2 ^ b₀) < (((c₀ - (k : ℝ) / 2 ^ b₀) : ℝ) : EReal) := by
      rw [eventually_all_finset]
      intro k hk
      have hkT := (mem_gridIndex.mp hk).2
      have hAk : A ((k : ℝ) / 2 ^ b₀) + (((k : ℝ) / 2 ^ b₀ : ℝ) : EReal) < (c₀ : EReal) :=
        lt_of_le_of_lt (le_iSup (fun τ : Iio T => A τ + ((τ : ℝ) : EReal))
          ⟨(k : ℝ) / 2 ^ b₀, hkT⟩) hSc₀
      have hAk' : A ((k : ℝ) / 2 ^ b₀) < (((c₀ - (k : ℝ) / 2 ^ b₀) : ℝ) : EReal) := by
        rw [EReal.coe_sub]
        exact (EReal.lt_sub_iff_add_lt (Or.inl (EReal.coe_ne_bot _))
          (Or.inl (EReal.coe_ne_top _))).mpr hAk
      exact (hlim _ hkT).eventually_lt_const hAk'
    obtain ⟨a, ha, hab₀⟩ := (hev.and (eventually_ge_atTop b₀)).exists
    refine (iInf_le _ a).trans (max_le ?_ (iSup_le fun ⟨k, hk⟩ => ?_))
    · -- the tail term: `F_lim(a) - a ≤ -a ≤ c₁`
      refine le_trans (add_le_add (hFlim_nonpos a) le_rfl) ?_
      rw [zero_add, EReal.coe_le_coe_iff]
      have : (b₀ : ℝ) ≤ a := by exact_mod_cast hab₀
      linarith
    · obtain ⟨hk1, hkT⟩ := mem_gridIndex.mp hk
      have hpa : (0 : ℝ) < 2 ^ a := by positivity
      have hinv : (1 : ℝ) / 2 ^ a ≤ (1 / 2) ^ b₀ := by
        rw [one_div_pow]
        exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hab₀)
      set t : ℝ := (k : ℝ) / 2 ^ a with ht
      have hterm : ((k : ℝ) + 1) / 2 ^ a = t + 1 / 2 ^ a := by rw [ht]; ring
      by_cases hcase : -(b₀ : ℝ) ≤ t
      · obtain ⟨hs, hsle, hslt⟩ := floor_mem_gridIndex (a := b₀) hcase hkT
        set s : ℝ := ((⌊t * 2 ^ b₀⌋ : ℤ) : ℝ) / 2 ^ b₀ with hsdef
        have hF : F a t < (((c₀ - s) : ℝ) : EReal) :=
          lt_of_le_of_lt (hanti_t a _ _ hsle hkT) (ha _ hs)
        have hst : t < s + (1 / 2) ^ b₀ := by
          rw [hsdef, one_div_pow, ← add_div] at *
          exact hslt
        refine le_of_lt (lt_of_lt_of_le (EReal.add_lt_add_right_coe hF _) ?_)
        rw [← EReal.coe_add, EReal.coe_le_coe_iff, hterm]
        linarith
      · rw [not_le] at hcase
        refine le_trans (add_le_add (hnonpos a t hkT) le_rfl) ?_
        rw [zero_add, EReal.coe_le_coe_iff, hterm]
        have : (1 : ℝ) / 2 ^ a ≤ 1 := by
          rw [div_le_one hpa]
          exact one_le_pow₀ (by norm_num)
        linarith
  · exact le_iInf fun a => iSup_le fun τ => le_gridApprox hFA hFlim hanti_t a τ.2

end Hyp

end SGPT.NAPotential.BJ.Exist
