import SGPT.Envelopes.MADirichletSubsolution
import SGPT.Foundations.Analysis.Pending.BedfordTaylorSlotAdd

/-!
# Superadditivity of the Monge–Ampère operator and domination of subsolutions

* `ma_add_ge` (superadditivity): for locally bounded psh `φ, ρ` on `Ω ⊆ ℂⁿ`, `n ≥ 1`,
  `(ddᶜ(φ + ρ))ⁿ ≥ (ddᶜφ)ⁿ + (ddᶜρ)ⁿ`. This is the expansion
  `(ddᶜ(φ + ρ))ⁿ = ∑ₖ (n choose k) (ddᶜφ)ᵏ ∧ (ddᶜρ)ⁿ⁻ᵏ` with the mixed terms, which are positive,
  dropped (FPT, proof of `thm:compact-bounded-subsolution-ball-dirichlet`, Step 1, and
  `cor:bt-local-domination`). The proof expands one slot at a time with TN's slot additivity
  (`IsBTLimit.add_slot`); `SGPT.PSH.BookDeepDomination.le_of_isBTLimit_add` is the weaker
  statement keeping only `(ddᶜρ)ⁿ`.
* `le_of_ma_le_of_le_ma` (domination of subsolutions by supersolutions): let `Ω` be a bounded
  open set, `U, v` locally bounded psh on `Ω` with `liminf (U - v) ≥ 0` at `∂Ω`, and `α` a
  finite measure with `(ddᶜU)ⁿ ≤ α ≤ (ddᶜv)ⁿ` on `Ω`. Then `v ≤ U` on `Ω`.
  This is FPT's argument in Step 5 of `thm:continuous-density-ball-dirichlet`, Step 3 of
  `thm:bounded-density-ball-dirichlet` and Step 4 of
  `thm:compact-bounded-subsolution-ball-dirichlet`: for `v_ε = v + ε(|z|² - M)` the comparison
  principle (`SGPT.PSH.BookDeepDomination.measure_lt_le_of_boundary`) and superadditivity give
  `α(S) + εⁿ (n!/πⁿ) |S| ≤ α(S)` on `S = {U < v_ε}`, so `S` is Lebesgue null, hence empty
  (plurisubharmonic functions agreeing almost everywhere agree), and `ε → 0`.
  In particular the bounded solution of a Dirichlet problem `(ddᶜU)ⁿ = α`, `U = φ` on `∂Ω`, is
  unique and is the largest subsolution (`eq_of_ma_eq`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ENNReal

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.NPP.LogConcavityDinew

variable {n : ℕ}

/-- The tuple whose first `k` slots are `σ` and whose other slots are those of `c`. -/
def prefixTuple (k : ℕ) (σ : ComplexModel n → ℝ) (c : Fin n → ComplexModel n → ℝ) :
    Fin n → ComplexModel n → ℝ :=
  fun i => if i.val < k then σ else c i

theorem prefixTuple_update_self {k : ℕ} (hk : k < n) (σ τ : ComplexModel n → ℝ)
    (c : Fin n → ComplexModel n → ℝ) :
    Function.update (prefixTuple k σ c) ⟨k, hk⟩ τ = prefixTuple k σ (Function.update c ⟨k, hk⟩ τ) := by
  funext i
  by_cases hi : i = ⟨k, hk⟩
  · subst hi
    simp [prefixTuple]
  · rw [Function.update_of_ne hi]
    simp only [prefixTuple]
    split_ifs
    · rfl
    · rw [Function.update_of_ne hi]

theorem prefixTuple_succ {k : ℕ} (hk : k < n) (σ : ComplexModel n → ℝ)
    (c : Fin n → ComplexModel n → ℝ) :
    prefixTuple (k + 1) σ c = prefixTuple k σ (Function.update c ⟨k, hk⟩ σ) := by
  funext i
  simp only [prefixTuple]
  by_cases hi : i = ⟨k, hk⟩
  · subst hi
    simp
  · have hik : i.val ≠ k := fun h => hi (Fin.ext h)
    rw [Function.update_of_ne hi]
    by_cases hlt : i.val < k
    · simp [hlt, Nat.lt_succ_of_lt hlt]
    · have : ¬ i.val < k + 1 := by omega
      simp [hlt, this]

theorem isLocallyBoundedPshOn_prefixTuple {Ω : Opens (ComplexModel n)} {k : ℕ}
    {σ : ComplexModel n → ℝ} (hσ : IsLocallyBoundedPshOn Ω σ) {c : Fin n → ComplexModel n → ℝ}
    (hc : ∀ i, IsLocallyBoundedPshOn Ω (c i)) (i : Fin n) :
    IsLocallyBoundedPshOn Ω (prefixTuple k σ c i) := by
  simp only [prefixTuple]
  split_ifs
  · exact hσ
  · exact hc i

/-- **Dropping a summand in the first `k` slots** decreases the mixed Bedford–Taylor measure. -/
theorem isBTLimit_prefix_le {Ω : Opens (ComplexModel n)} {φ ρ σ : ComplexModel n → ℝ}
    (hφ : IsLocallyBoundedPshOn Ω φ) (hρ : IsLocallyBoundedPshOn Ω ρ)
    (hσ : ∀ z, σ z = φ z + ρ z) :
    ∀ k, k ≤ n → ∀ c : Fin n → ComplexModel n → ℝ, (∀ i, IsLocallyBoundedPshOn Ω (c i)) →
      ∀ μ ν : Measure (ComplexModel n), IsBTLimit Ω (prefixTuple k σ c) μ →
        IsBTLimit Ω (prefixTuple k φ c) ν → ν ≤ μ := by
  have hσb : IsLocallyBoundedPshOn Ω σ := by
    have h := SGPT.PSH.BookDeepDomination.isLocallyBoundedPshOn_add hφ hρ
    have e : σ = fun z => φ z + ρ z := funext hσ
    rwa [e]
  intro k
  induction k with
  | zero =>
    intro _ c _ μ ν hμ hν
    have e : prefixTuple 0 σ c = prefixTuple 0 φ c := by
      funext i; simp [prefixTuple]
    rw [e] at hμ
    exact (hν.unique hμ).le
  | succ k ih =>
    intro hk c hc μ ν hμ hν
    have hk' : k < n := hk
    set i₀ : Fin n := ⟨k, hk'⟩ with hi₀
    -- split the slot `k`
    have hupd : prefixTuple (k + 1) σ c =
        Function.update (prefixTuple k σ c) i₀ fun z => φ z + ρ z := by
      rw [prefixTuple_succ hk', prefixTuple_update_self hk']
      congr 2
      exact funext hσ
    rw [hupd] at hμ
    have hcφ : ∀ i, IsLocallyBoundedPshOn Ω (Function.update c i₀ φ i) := fun i => by
      by_cases hi : i = i₀
      · subst hi; simpa using hφ
      · rw [Function.update_of_ne hi]; exact hc i
    have hcρ : ∀ i, IsLocallyBoundedPshOn Ω (Function.update c i₀ ρ i) := fun i => by
      by_cases hi : i = i₀
      · subst hi; simpa using hρ
      · rw [Function.update_of_ne hi]; exact hc i
    obtain ⟨μa, hμa⟩ := exists_isBTLimit_of_isLocallyBoundedPshOn
      (u := prefixTuple k σ (Function.update c i₀ φ))
      (isLocallyBoundedPshOn_prefixTuple hσb hcφ)
    obtain ⟨μb, hμb⟩ := exists_isBTLimit_of_isLocallyBoundedPshOn
      (u := prefixTuple k σ (Function.update c i₀ ρ))
      (isLocallyBoundedPshOn_prefixTuple hσb hcρ)
    have hsum := hμ.add_slot i₀ (by rw [prefixTuple_update_self hk']; exact hμa)
      (by rw [prefixTuple_update_self hk']; exact hμb)
    have hν' : IsBTLimit Ω (prefixTuple k φ (Function.update c i₀ φ)) ν := by
      rwa [← prefixTuple_succ hk']
    have := ih (Nat.le_of_succ_le hk) _ hcφ μa ν hμa hν'
    rw [hsum]
    exact this.trans (Measure.le_add_right le_rfl)

/-- **Superadditivity**: `(ddᶜ(φ + ρ))ⁿ ≥ (ddᶜφ)ⁿ + (ddᶜρ)ⁿ`. -/
theorem isBTLimit_add_ge (hn : 0 < n) {Ω : Opens (ComplexModel n)} {φ ρ : ComplexModel n → ℝ}
    (hφ : IsLocallyBoundedPshOn Ω φ) (hρ : IsLocallyBoundedPshOn Ω ρ)
    {μ μφ μρ : Measure (ComplexModel n)} (hμ : IsBTLimit Ω (fun _ => fun z => φ z + ρ z) μ)
    (hμφ : IsBTLimit Ω (fun _ => φ) μφ) (hμρ : IsBTLimit Ω (fun _ => ρ) μρ) :
    μφ + μρ ≤ μ := by
  set σ : ComplexModel n → ℝ := fun z => φ z + ρ z with hσdef
  have hσb : IsLocallyBoundedPshOn Ω σ :=
    SGPT.PSH.BookDeepDomination.isLocallyBoundedPshOn_add hφ hρ
  have hk : n - 1 < n := Nat.sub_lt hn one_pos
  set i₀ : Fin n := ⟨n - 1, hk⟩ with hi₀
  set c : Fin n → ComplexModel n → ℝ := fun _ => φ with hc
  have hall : ∀ τ : ComplexModel n → ℝ, Function.update (prefixTuple (n - 1) σ c) i₀ τ =
      prefixTuple (n - 1) σ (fun i => if i = i₀ then τ else φ) := by
    intro τ
    rw [prefixTuple_update_self hk]
    congr 1
    funext i
    by_cases hi : i = i₀
    · rw [if_pos hi, hi, hi₀, Function.update_self]
    · rw [if_neg hi, Function.update_of_ne hi]
  have hfull : (fun _ : Fin n => σ) = Function.update (prefixTuple (n - 1) σ c) i₀ σ := by
    funext i
    by_cases hi : i = i₀
    · subst hi; simp
    · rw [Function.update_of_ne hi]
      have : i.val < n - 1 := by
        have h1 := i.isLt
        have h2 : i.val ≠ n - 1 := fun h => hi (Fin.ext h)
        omega
      simp [prefixTuple, this]
  rw [hfull] at hμ
  have hcτ : ∀ τ : ComplexModel n → ℝ, IsLocallyBoundedPshOn Ω τ →
      ∀ i, IsLocallyBoundedPshOn Ω ((fun i => if i = i₀ then τ else φ) i) := by
    intro τ hτ i
    simp only
    split_ifs
    · exact hτ
    · exact hφ
  obtain ⟨μa, hμa⟩ := exists_isBTLimit_of_isLocallyBoundedPshOn
    (u := prefixTuple (n - 1) σ (fun i => if i = i₀ then φ else φ))
    (isLocallyBoundedPshOn_prefixTuple hσb (hcτ φ hφ))
  obtain ⟨μb, hμb⟩ := exists_isBTLimit_of_isLocallyBoundedPshOn
    (u := prefixTuple (n - 1) σ (fun i => if i = i₀ then ρ else φ))
    (isLocallyBoundedPshOn_prefixTuple hσb (hcτ ρ hρ))
  have hsum := hμ.add_slot i₀ (by rw [hall]; exact hμa) (by rw [hall]; exact hμb)
  -- the first summand dominates `(ddᶜφ)ⁿ`
  have h1 : μφ ≤ μa := by
    refine isBTLimit_prefix_le hφ hρ (fun z => rfl) (n - 1) (Nat.sub_le n 1) _
      (hcτ φ hφ) μa μφ hμa ?_
    have e : prefixTuple (n - 1) φ (fun i => if i = i₀ then φ else φ) = fun _ => φ := by
      funext i; simp [prefixTuple]
    rw [e]; exact hμφ
  -- the second dominates `(ddᶜρ)ⁿ`
  have h2 : μρ ≤ μb := by
    have hσ' : ∀ z, σ z = ρ z + φ z := fun z => add_comm _ _
    refine isBTLimit_prefix_le hρ hφ hσ' (n - 1) (Nat.sub_le n 1) _ (hcτ ρ hρ) μb μρ hμb ?_
    have e : prefixTuple (n - 1) ρ (fun i => if i = i₀ then ρ else φ) = fun _ => ρ := by
      funext i
      simp only [prefixTuple]
      by_cases hi : i = i₀
      · simp [hi]
      · have : i.val < n - 1 := by
          have h1 := i.isLt
          have h2 : i.val ≠ n - 1 := fun h => hi (Fin.ext h)
          omega
        simp [this]
    rw [e]; exact hμρ
  rw [hsum]
  exact add_le_add h1 h2

/-- **Superadditivity of the Monge–Ampère operator**, canonical-measure form. -/
theorem ma_add_ge (hn : 0 < n) {Ω : Opens (ComplexModel n)} {φ ρ : ComplexModel n → ℝ}
    (hφ : IsLocallyBoundedPshOn Ω φ) (hρ : IsLocallyBoundedPshOn Ω ρ)
    (hφρ : IsLocallyBoundedPshOn Ω fun z => φ z + ρ z) :
    canonicalBedfordTaylorMeasure Ω φ hφ + canonicalBedfordTaylorMeasure Ω ρ hρ ≤
      canonicalBedfordTaylorMeasure Ω _ hφρ :=
  isBTLimit_add_ge hn hφ hρ (isBTLimit_canonicalBedfordTaylorMeasure hφρ)
    (isBTLimit_canonicalBedfordTaylorMeasure hφ) (isBTLimit_canonicalBedfordTaylorMeasure hρ)

/-- **A strict perturbation**: `(ddᶜ(v + ε(|z|² - M)))ⁿ ≥ (ddᶜv)ⁿ + εⁿ (n!/πⁿ) dV` on `Ω`. -/
theorem ma_add_normSq_ge (hn : 0 < n) {Ω : Opens (ComplexModel n)} {v : ComplexModel n → ℝ}
    (hv : IsLocallyBoundedPshOn Ω v) {ε : ℝ} (hε : 0 < ε) (M : ℝ)
    (hvε : IsLocallyBoundedPshOn Ω fun z => v z + ε * (‖z‖ ^ 2 - M)) :
    canonicalBedfordTaylorMeasure Ω v hv +
        ENNReal.ofReal (mongeAmpereConst n * ε ^ n) • volume.restrict (Ω : Set (ComplexModel n)) ≤
      canonicalBedfordTaylorMeasure Ω _ hvε := by
  have hv' : IsLocallyBoundedPshOn Ω fun z => v z + -(ε * M) :=
    IsLocallyBoundedPshOn.add_const hv _
  have hq := SGPT.PSH.BookDeepDomination.isLocallyBoundedPshOn_mul_normSq Ω hε
  have e : (fun z => v z + ε * (‖z‖ ^ 2 - M)) = fun z => (v z + -(ε * M)) + ε * ‖z‖ ^ 2 := by
    funext z; ring
  have hsum := isBTLimit_add_ge hn hv' hq (by rw [← e]; exact isBTLimit_canonicalBedfordTaylorMeasure hvε)
    ((isBTLimit_canonicalBedfordTaylorMeasure hv).add_const_diag _)
    (SGPT.PSH.BookDeepDomination.isBTLimit_mul_normSq Ω hε.le)
  refine le_trans (le_of_eq ?_) hsum
  congr 1
  rw [ENNReal.ofReal_mul mongeAmpereConst_pos.le, ENNReal.ofReal_pow hε.le, mul_comm,
    mongeAmpereConst]

/-- **Domination of subsolutions by supersolutions.** Let `Ω ⊆ ℂⁿ` be a bounded open set,
`n ≥ 1`, and `U, v` locally bounded psh on `Ω` with `liminf (U - v) ≥ 0` at every boundary point.
If `α` is a finite measure with `(ddᶜU)ⁿ ≤ α` and `α ≤ (ddᶜv)ⁿ` on `Ω`, then `v ≤ U` on `Ω`. -/
theorem le_of_ma_le_of_le_ma (hn : 0 < n) {Ω : Opens (ComplexModel n)}
    (hΩ : Bornology.IsBounded (Ω : Set (ComplexModel n))) {U v : ComplexModel n → ℝ}
    (hU : IsLocallyBoundedPshOn Ω U) (hv : IsLocallyBoundedPshOn Ω v)
    (hbd : ∀ ζ ∈ frontier (Ω : Set (ComplexModel n)), ∀ δ > 0,
      ∀ᶠ z in 𝓝[(Ω : Set (ComplexModel n))] ζ, v z - U z < δ)
    {α : Measure (ComplexModel n)} (hαfin : α (Ω : Set (ComplexModel n)) < ⊤)
    (hUα : canonicalBedfordTaylorMeasure Ω U hU ≤ α)
    (hαv : α.restrict (Ω : Set (ComplexModel n)) ≤ canonicalBedfordTaylorMeasure Ω v hv) :
    ∀ z ∈ Ω, v z ≤ U z := by
  obtain ⟨R, hR⟩ := hΩ.subset_closedBall 0
  set M : ℝ := R ^ 2 + 1 with hMdef
  have hM : ∀ z ∈ Ω, ‖z‖ ^ 2 < M := by
    intro z hz
    have h := hR hz
    rw [mem_closedBall, dist_zero_right] at h
    have hR0 : 0 ≤ R := (norm_nonneg z).trans h
    nlinarith [norm_nonneg z]
  have hε : ∀ ε : ℝ, 0 < ε → ∀ z ∈ Ω, v z + ε * (‖z‖ ^ 2 - M) ≤ U z := by
    intro ε hε
    set vε : ComplexModel n → ℝ := fun z => v z + ε * (‖z‖ ^ 2 - M) with hvεdef
    have hvεb : IsLocallyBoundedPshOn Ω vε := by
      have e : vε = fun z => (v z + -(ε * M)) + ε * ‖z‖ ^ 2 := by funext z; simp only [hvεdef]; ring
      rw [e]
      exact SGPT.PSH.BookDeepDomination.isLocallyBoundedPshOn_add
        (IsLocallyBoundedPshOn.add_const hv _)
        (SGPT.PSH.BookDeepDomination.isLocallyBoundedPshOn_mul_normSq Ω hε)
    have hbd' : ∀ ζ ∈ frontier (Ω : Set (ComplexModel n)), ∀ δ > 0,
        ∀ᶠ z in 𝓝[(Ω : Set (ComplexModel n))] ζ, vε z - U z < δ := by
      intro ζ hζ δ hδ
      filter_upwards [hbd ζ hζ δ hδ, self_mem_nhdsWithin] with z hz hzΩ
      have hneg : ε * (‖z‖ ^ 2 - M) < 0 := mul_neg_of_pos_of_neg hε (by linarith [hM z hzΩ])
      simp only [hvεdef]
      linarith
    have hcomp := SGPT.PSH.BookDeepDomination.measure_lt_le_of_boundary hn hΩ hU hvεb hbd'
      (isBTLimit_canonicalBedfordTaylorMeasure hU) (isBTLimit_canonicalBedfordTaylorMeasure hvεb)
    set S : Set (ComplexModel n) := {z | z ∈ Ω ∧ U z < vε z} with hSdef
    have hSΩ : S ⊆ Ω := fun z hz => hz.1
    have hlow := ma_add_normSq_ge hn hv hε M hvεb
    have hαS : α S < ⊤ := (measure_mono hSΩ).trans_lt hαfin
    have hvS : α S ≤ canonicalBedfordTaylorMeasure Ω v hv S := by
      have h := hαv S
      rwa [Measure.restrict_apply' Ω.isOpen.measurableSet, inter_eq_left.mpr hSΩ] at h
    have hkey : α S + ENNReal.ofReal (mongeAmpereConst n * ε ^ n) *
        volume.restrict (Ω : Set (ComplexModel n)) S ≤ α S := by
      calc α S + ENNReal.ofReal (mongeAmpereConst n * ε ^ n) *
            volume.restrict (Ω : Set (ComplexModel n)) S
          ≤ canonicalBedfordTaylorMeasure Ω v hv S + ENNReal.ofReal (mongeAmpereConst n * ε ^ n) *
            volume.restrict (Ω : Set (ComplexModel n)) S := add_le_add_left hvS _
        _ ≤ canonicalBedfordTaylorMeasure Ω vε hvεb S := hlow S
        _ ≤ canonicalBedfordTaylorMeasure Ω U hU S := hcomp
        _ ≤ α S := hUα S
    have hvol : volume.restrict (Ω : Set (ComplexModel n)) S = 0 := by
      have h0 : ENNReal.ofReal (mongeAmpereConst n * ε ^ n) *
          volume.restrict (Ω : Set (ComplexModel n)) S = 0 := by
        have hk' : α S + ENNReal.ofReal (mongeAmpereConst n * ε ^ n) *
            volume.restrict (Ω : Set (ComplexModel n)) S ≤ α S + 0 := by rw [add_zero]; exact hkey
        exact le_antisymm (ENNReal.le_of_add_le_add_left hαS.ne hk') bot_le
      rcases mul_eq_zero.mp h0 with h | h
      · exfalso
        exact (ENNReal.ofReal_pos.mpr (mul_pos mongeAmpereConst_pos (pow_pos hε n))).ne' h
      · exact h
    have hae : (fun z => ((max (vε z) (U z) : ℝ) : EReal)) =ᵐ[volume.restrict (Ω : Set _)]
        fun z => ((U z : ℝ) : EReal) := by
      have hnot : ∀ᵐ z ∂volume.restrict (Ω : Set (ComplexModel n)), z ∉ S :=
        measure_eq_zero_iff_ae_notMem.mp hvol
      filter_upwards [hnot, ae_restrict_mem Ω.isOpen.measurableSet] with z hz hzΩ
      have : vε z ≤ U z := not_lt.mp fun h => hz ⟨hzΩ, h⟩
      rw [max_eq_right this]
    have heq := PlurisubharmonicOn.eqOn_of_ae_eq
      (IsLocallyBoundedPshOn.max hvεb hU).1 hU.1 Ω.isOpen volume hae
    intro z hz
    have h := heq hz
    simp only [EReal.coe_eq_coe_iff] at h
    exact max_eq_right_iff.mp h
  intro z hz
  have hMz : 0 < M - ‖z‖ ^ 2 := by linarith [hM z hz]
  refine le_of_forall_pos_le_add fun η hη => ?_
  have h := hε (η / (M - ‖z‖ ^ 2)) (div_pos hη hMz) z hz
  have hcalc : η / (M - ‖z‖ ^ 2) * (‖z‖ ^ 2 - M) = -η := by
    field_simp
    ring
  rw [hcalc] at h
  linarith

/-- **Uniqueness for the Dirichlet problem with finite measure data.** Two locally bounded psh
functions on a bounded open set with the same Monge–Ampère measure `α`, `α(Ω) < ∞`, and the same
boundary values (`U - V → 0` at `∂Ω`) coincide. -/
theorem eq_of_ma_eq (hn : 0 < n) {Ω : Opens (ComplexModel n)}
    (hΩ : Bornology.IsBounded (Ω : Set (ComplexModel n))) {U V : ComplexModel n → ℝ}
    (hU : IsLocallyBoundedPshOn Ω U) (hV : IsLocallyBoundedPshOn Ω V)
    (hbd : ∀ ζ ∈ frontier (Ω : Set (ComplexModel n)), ∀ δ > 0,
      ∀ᶠ z in 𝓝[(Ω : Set (ComplexModel n))] ζ, |U z - V z| < δ)
    (hfin : canonicalBedfordTaylorMeasure Ω U hU (Ω : Set (ComplexModel n)) < ⊤)
    (heq : canonicalBedfordTaylorMeasure Ω U hU = canonicalBedfordTaylorMeasure Ω V hV) :
    ∀ z ∈ Ω, U z = V z := by
  have hres : ∀ (W : ComplexModel n → ℝ) (hW : IsLocallyBoundedPshOn Ω W),
      (canonicalBedfordTaylorMeasure Ω W hW).restrict (Ω : Set (ComplexModel n)) =
        canonicalBedfordTaylorMeasure Ω W hW := fun W hW =>
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr (canonicalBedfordTaylorMeasure_compl Ω W hW))
  have h1 := le_of_ma_le_of_le_ma hn hΩ hU hV (fun ζ hζ δ hδ => by
      filter_upwards [hbd ζ hζ δ hδ] with z hz
      linarith [(abs_lt.mp hz).1]) hfin le_rfl (by rw [hres, heq])
  have h2 := le_of_ma_le_of_le_ma hn hΩ hV hU (fun ζ hζ δ hδ => by
      filter_upwards [hbd ζ hζ δ hδ] with z hz
      linarith [(abs_lt.mp hz).2]) hfin heq.symm.le (by rw [hres])
  exact fun z hz => le_antisymm (h2 z hz) (h1 z hz)

end SGPT.Envelopes.MADirichlet
