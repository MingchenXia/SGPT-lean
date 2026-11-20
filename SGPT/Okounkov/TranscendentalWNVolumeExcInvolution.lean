import SGPT.Okounkov.TranscendentalWNVolumeExcRestriction

/-!
# The partial Legendre transform of an inverse Legendre transform (package WN-VF3)

Blueprint node `tok-wn-vf3:involution` (chapter `claude-tok-wn-vf3`), an input of
`tok-wn-vf3:bundle-legendre-ma`; source D. Witt Nyström, arXiv:2103.03660 (WN21), §3:

> Let `v_λ`, `λ ∈ [a, b]` be a concave family of psh functions on `U`.  If
> `u(z, τ) := sup_{λ ∈ [a,b]} {v_λ(z) + λ ln |τ|²}` is psh then we see from the involution property of
> the Legendre transform that `û_λ = v_λ` for `λ ∈ [a,b]` and `û_λ = -∞` for `λ ∉ [a,b]`.

For a family `v_λ(x)` which is concave and finite on `[a, b]` at the point `x`:

* `partialLegendre_inverseLegendre`: `û_λ(x) = v_λ(x)` for `λ` in the open interval `(a, b)`
  (a supergradient of the concave function `λ ↦ v_λ(x)` at an interior point gives the
  minimizing `τ`, with `log |τ|²` minus the supergradient);
* `partialLegendre_inverseLegendre_eq_bot`: `û_λ(x) = -∞` for `λ ∉ [a, b]` (when `v_·(x)` is
  bounded above on `[a, b]`; let `log |τ|² → ±∞`).

At the endpoints `λ = a, b` the transform is the upper semicontinuous regularization, which
is irrelevant for the Monge–Ampère identity (`dλ`-null).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter
open scoped Topology

/-- **A supergradient of a concave function at an interior point.** -/
theorem exists_supergradient_of_concaveOn {f : ℝ → ℝ} {a b : ℝ} (hf : ConcaveOn ℝ (Icc a b) f)
    {y : ℝ} (hy : y ∈ Ioo a b) : ∃ s : ℝ, ∀ t ∈ Icc a b, f t ≤ f y + s * (t - y) := by
  have hg : ConvexOn ℝ (Icc a b) (fun t => -f t) := hf.neg
  have hyi : y ∈ interior (Icc a b) := by rw [interior_Icc]; exact hy
  refine ⟨-derivWithin (fun t => -f t) (Ioi y) y, fun t ht => ?_⟩
  rcases lt_trichotomy y t with hyt | rfl | hty
  · have h := hg.rightDeriv_le_slope_of_mem_interior hyi ht hyt
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h
    linarith
  · simp
  · have h1 := hg.slope_le_leftDeriv_of_mem_interior ht hyi hty
    have h2 := hg.leftDeriv_le_rightDeriv_of_mem_interior hyi
    rw [slope_def_field, div_le_iff₀ (by linarith)] at h1
    nlinarith

/-- A concave family which is finite on `[a, b]` at `x` gives a real concave function. -/
theorem concaveOn_toReal_of_isConcaveFamilyAt {X : Type*} {v : ℝ → X → EReal} {a b : ℝ}
    {x : X} (hconc : IsConcaveFamilyAt v (Icc a b) x)
    (hfin : ∀ lam ∈ Icc a b, v lam x ≠ ⊥ ∧ v lam x ≠ ⊤) :
    ConcaveOn ℝ (Icc a b) (fun lam => (v lam x).toReal) := by
  refine ⟨convex_Icc a b, fun l₁ hl₁ l₂ hl₂ s t hs ht hst => ?_⟩
  have ht' : t = 1 - s := by linarith
  subst ht'
  have hs1 : s ≤ 1 := by linarith
  have h := hconc l₁ hl₁ l₂ hl₂ s hs hs1
  have hmem : s * l₁ + (1 - s) * l₂ ∈ Icc a b := (convex_Icc a b) hl₁ hl₂ hs ht hst
  rw [← EReal.coe_toReal (hfin l₁ hl₁).2 (hfin l₁ hl₁).1,
    ← EReal.coe_toReal (hfin l₂ hl₂).2 (hfin l₂ hl₂).1,
    ← EReal.coe_toReal (hfin _ hmem).2 (hfin _ hmem).1, ← EReal.coe_mul, ← EReal.coe_mul,
    ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  simpa only [smul_eq_mul] using h

/-- Subtracting a real number cancels its addition in `EReal`. -/
theorem ereal_add_coe_sub_coe (A : EReal) (r : ℝ) : A + (r : EReal) - (r : EReal) = A := by
  rw [sub_eq_add_neg, ← EReal.coe_neg]
  exact SGPT.Foundations.Analysis.Pending.MeteredDivisorPositivity.add_coe_add_neg_coe A r

/-- **The involution property** (WN21 §3): for `v_·(x)` concave and finite on `[a, b]` and
`λ₀ ∈ (a, b)`, the partial Legendre transform of `sup_{λ ∈ [a,b]} (v_λ + λ log |τ|²)` at `λ₀` is
`v_{λ₀}(x)`. -/
theorem partialLegendre_inverseLegendre {X : Type*} {v : ℝ → X → EReal} {a b : ℝ} {x : X}
    (hconc : IsConcaveFamilyAt v (Icc a b) x)
    (hfin : ∀ lam ∈ Icc a b, v lam x ≠ ⊥ ∧ v lam x ≠ ⊤) {lam₀ : ℝ} (h₀ : lam₀ ∈ Ioo a b) :
    partialLegendre (inverseLegendre v a b) lam₀ x = v lam₀ x := by
  have h₀' : lam₀ ∈ Icc a b := Ioo_subset_Icc_self h₀
  apply le_antisymm
  · -- the minimizing `τ`: `log |τ|² = -s` for a supergradient `s`
    set f : ℝ → ℝ := fun lam => (v lam x).toReal with hf
    obtain ⟨s, hs⟩ := exists_supergradient_of_concaveOn
      (concaveOn_toReal_of_isConcaveFamilyAt hconc hfin) h₀
    set τ : ℂ := Complex.exp (((-s : ℝ) : ℂ) / 2) with hτ
    have hτ0 : τ ≠ 0 := Complex.exp_ne_zero _
    have hL : logNormSq τ = -s := logNormSq_exp_half (-s)
    refine (iInf_le _ (⟨τ, hτ0⟩ : puncturedPlane)).trans ?_
    simp only [inverseLegendre, hL]
    have hsup : (⨆ lam ∈ Icc a b, v lam x + ((lam * -s : ℝ) : EReal)) ≤
        ((f lam₀ - s * lam₀ : ℝ) : EReal) := by
      refine iSup₂_le fun lam hl => ?_
      rw [← EReal.coe_toReal (hfin lam hl).2 (hfin lam hl).1, ← EReal.coe_add,
        EReal.coe_le_coe_iff]
      have := hs lam hl
      simp only [hf] at this ⊢
      nlinarith
    have h2 := EReal.sub_le_sub hsup (le_refl (((lam₀ * -s : ℝ) : EReal)))
    refine h2.trans (le_of_eq ?_)
    rw [← EReal.coe_sub, ← EReal.coe_toReal (hfin lam₀ h₀').2 (hfin lam₀ h₀').1]
    congr 1
    simp only [hf]
    ring
  · refine le_iInf fun τ => ?_
    have h1 : v lam₀ x + ((lam₀ * logNormSq τ : ℝ) : EReal) ≤ inverseLegendre v a b x τ :=
      le_iSup₂ (f := fun lam (_ : lam ∈ Icc a b) => v lam x + ((lam * logNormSq τ : ℝ) : EReal))
        lam₀ h₀'
    have h2 := EReal.sub_le_sub h1 (le_refl (((lam₀ * logNormSq τ : ℝ) : EReal)))
    rwa [ereal_add_coe_sub_coe] at h2

/-- **Outside `[a, b]` the transform is `-∞`** (WN21 §3): if `v_·(x)` is bounded above on
`[a, b]` and `λ₀ ∉ [a, b]`, the partial Legendre transform of the inverse transform at `λ₀`
is `-∞`. -/
theorem partialLegendre_inverseLegendre_eq_bot {X : Type*} {v : ℝ → X → EReal} {a b : ℝ}
    {x : X} {C : ℝ} (hC : ∀ lam ∈ Icc a b, v lam x ≤ (C : EReal)) {lam₀ : ℝ}
    (h₀ : lam₀ ∉ Icc a b) : partialLegendre (inverseLegendre v a b) lam₀ x = ⊥ := by
  rw [EReal.eq_bot_iff_forall_lt]
  intro y
  -- the value at `log |τ|² = s`
  have hval : ∀ s : ℝ, (∀ lam ∈ Icc a b, (lam - lam₀) * s ≤ y - C - 1) →
      partialLegendre (inverseLegendre v a b) lam₀ x < (y : EReal) := by
    intro s hs
    set τ : ℂ := Complex.exp ((s : ℂ) / 2) with hτ
    have hτ0 : τ ≠ 0 := Complex.exp_ne_zero _
    have hL : logNormSq τ = s := logNormSq_exp_half s
    refine lt_of_le_of_lt (iInf_le _ (⟨τ, hτ0⟩ : puncturedPlane)) ?_
    simp only [inverseLegendre, hL]
    have hsup : (⨆ lam ∈ Icc a b, v lam x + ((lam * s : ℝ) : EReal)) ≤
        ((y - 1 + lam₀ * s : ℝ) : EReal) := by
      refine iSup₂_le fun lam hl => ?_
      have h1 := add_le_add (hC lam hl) (le_refl ((lam * s : ℝ) : EReal))
      refine h1.trans ?_
      rw [← EReal.coe_add, EReal.coe_le_coe_iff]
      have := hs lam hl
      nlinarith
    refine lt_of_le_of_lt (EReal.sub_le_sub hsup le_rfl) ?_
    rw [← EReal.coe_sub, EReal.coe_lt_coe_iff]
    linarith
  rcases not_and_or.mp h₀ with h | h
  · -- `λ₀ < a`: take `s → -∞`
    replace h := lt_of_not_ge h
    refine hval (min 0 ((y - C - 1) / (a - lam₀))) fun lam hl => ?_
    set s := min 0 ((y - C - 1) / (a - lam₀)) with hsdef
    have hs0 : s ≤ 0 := min_le_left _ _
    have hs1 : s ≤ (y - C - 1) / (a - lam₀) := min_le_right _ _
    have hpos : 0 < a - lam₀ := by linarith
    rw [le_div_iff₀ hpos] at hs1
    nlinarith [hl.1]
  · -- `λ₀ > b`: take `s → +∞`
    replace h := lt_of_not_ge h
    refine hval (max 0 ((y - C - 1) / (b - lam₀))) fun lam hl => ?_
    set s := max 0 ((y - C - 1) / (b - lam₀)) with hsdef
    have hs0 : 0 ≤ s := le_max_left _ _
    have hs1 : (y - C - 1) / (b - lam₀) ≤ s := le_max_right _ _
    have hneg : b - lam₀ < 0 := by linarith
    rw [div_le_iff_of_neg hneg] at hs1
    nlinarith [hl.2]

end SGPT.Okounkov.TranscendentalWN
