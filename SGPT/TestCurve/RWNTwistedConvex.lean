import SGPT.PSH.SourceTestCurveFoundation

/-!
# One-variable Legendre duality for twisted test curves

Source `rmk:testcurve:L815` (chapter *Test curves*). The proofs of `prop:Gammaclosed`,
`prop:Leginvtc`, `lma:testcurvelegusc` and `lma:LegendsRtoTC` use, at every point `x ∈ X`,
elementary facts on the concave decreasing function `τ ↦ Γ_τ(x)` and on the convex function
`t ↦ ℓ_t(x)`. In the untwisted setting they are formalized for `SourceTestCurvePredata`, whose
normalisation `Γ_τ ≤ 0` comes from `P_θ[Γ_τ] = Γ_τ`. A twisted test curve is only bounded from
above by `Φ`, and its values at the cut-off `Γ_max` may be identically `-∞`, so the
one-variable facts are proved here for an arbitrary family bounded from above:

* `iSup_real_eq_iSup_Iio`: the supremum `sup_τ (tτ + q(τ))` of a decreasing function vanishing
  (`= -∞`) above `m` is the supremum over `τ < m`.
* `iInf_sub_eq_bot_of_linear_bound`: `inf_{s > 0} (F(s) - sτ) = -∞` for `τ > m` when
  `F(s) ≤ c + sm`.
* `legendre_inverse_le`: the Legendre inversion `inf_{t > 0} (sup_{σ < m} (tσ + f(σ)) - tτ) ≤ f(τ)`
  for a decreasing, concave, left-continuous `f` bounded from above (`prop:Leginvtc`).
* `boundary_le_iSup_iInf`: for a convex `g` on `(0, ∞)` with limit `L` at `0`,
  `L ≤ sup_{τ < c} inf_{t > 0} (g(t) - tτ)` (the duality used at the end of `lma:LegendsRtoTC`).
* `upperSemicontinuous_iSup_affine`: for a decreasing family of upper semicontinuous functions
  bounded from above, `x ↦ sup_{σ < m} (tσ + f_σ(x))` is upper semicontinuous (`t > 0`); this is
  the reason why no regularization is needed in `def:Legtrans`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.TestCurve.RWNTwisted

open Set Filter Topology
open SGPT.PSH.VariableComplexAtlas

/-- An extended real number `≠ ⊤` is bounded by `B` as soon as all its real minorants are. -/
theorem ereal_le_coe_of_forall_real {g : EReal} {B : ℝ} (hg : g ≠ ⊤)
    (h : ∀ y : ℝ, (y : EReal) ≤ g → y ≤ B) : g ≤ (B : EReal) := by
  induction g using EReal.rec with
  | bot => exact bot_le
  | coe y => exact EReal.coe_le_coe (h y le_rfl)
  | top => exact absurd rfl hg

/-- The supremum defining the Legendre transform of a decreasing function which is `-∞` above
`m` may be taken over `τ < m`. -/
theorem iSup_real_eq_iSup_Iio {q : ℝ → EReal} {m : ℝ} (hanti : Antitone q)
    (hbot : ∀ τ, m < τ → q τ = ⊥) (t : ℝ) :
    (⨆ τ : ℝ, ((t * τ : ℝ) : EReal) + q τ) =
      ⨆ τ : Iio m, ((t * τ.1 : ℝ) : EReal) + q τ.1 := by
  apply le_antisymm
  · apply iSup_le
    intro τ
    rcases lt_trichotomy τ m with hlt | heq | hgt
    · exact le_iSup (fun σ : Iio m ↦ ((t * σ.1 : ℝ) : EReal) + q σ.1) ⟨τ, hlt⟩
    · subst heq
      cases hq : q τ using EReal.rec with
      | bot => simp
      | top =>
        have h1 : q (τ - 1) = ⊤ := top_unique (hq ▸ hanti (by linarith : τ - 1 ≤ τ))
        refine le_top.trans ?_
        refine le_trans ?_ (le_iSup (fun σ : Iio τ ↦ ((t * σ.1 : ℝ) : EReal) + q σ.1)
          ⟨τ - 1, by change τ - 1 < τ; linarith⟩)
        rw [h1, EReal.coe_add_top]
      | coe c =>
        have hlim : Tendsto (fun s : ℝ ↦ ((t * s + c : ℝ) : EReal)) (𝓝[<] τ)
            (𝓝 ((t * τ + c : ℝ) : EReal)) :=
          (continuous_coe_real_ereal.comp ((continuous_const.mul continuous_id).add
            continuous_const)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        rw [← EReal.coe_add]
        apply le_of_tendsto hlim
        filter_upwards [self_mem_nhdsWithin] with s hs
        have hs' : s < τ := hs
        have hh : (c : EReal) ≤ q s := hq ▸ hanti hs'.le
        have hadd : ((t * s + c : ℝ) : EReal) ≤ ((t * s : ℝ) : EReal) + q s := by
          simpa only [EReal.coe_add] using add_le_add (le_refl ((t * s : ℝ) : EReal)) hh
        exact hadd.trans
          (le_iSup (fun σ : Iio τ ↦ ((t * σ.1 : ℝ) : EReal) + q σ.1) ⟨s, hs'⟩)
    · simp [hbot τ hgt]
  · exact iSup_le fun τ ↦ le_iSup (fun s : ℝ ↦ ((t * s : ℝ) : EReal) + q s) τ.1

/-- Above the slope `m` of a linear upper bound, the inverse Legendre transform is `-∞`. -/
theorem iInf_sub_eq_bot_of_linear_bound {F : ℝ → EReal} {c m τ : ℝ}
    (hF : ∀ s, 0 < s → F s ≤ ((c + s * m : ℝ) : EReal)) (hτ : m < τ) :
    (⨅ s : Ioi (0 : ℝ), F s.1 - ((s.1 * τ : ℝ) : EReal)) = ⊥ := by
  apply le_bot_iff.mp
  apply EReal.le_of_forall_lt_iff_le.mp
  intro r _
  let s : ℝ := max 1 ((r - c) / (m - τ))
  have hs : 0 < s := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hδ : m - τ < 0 := sub_neg.mpr hτ
  have hmul : s * (m - τ) ≤ r - c := by
    have hh := mul_le_mul_of_nonpos_right (le_max_right (1 : ℝ) ((r - c) / (m - τ))) hδ.le
    simpa only [div_mul_cancel₀ _ hδ.ne] using hh
  refine (iInf_le (fun s : Ioi (0 : ℝ) ↦ F s.1 - ((s.1 * τ : ℝ) : EReal)) ⟨s, hs⟩).trans ?_
  refine (EReal.sub_le_sub (hF s hs) le_rfl).trans ?_
  rw [← EReal.coe_sub]
  exact EReal.coe_le_coe (by linarith [show s * (m - τ) = s * m - s * τ by ring])

/-- The three-point inequality for a family which is concave in the sense of `def:testcur`
(convexity of the epigraph of the negative trace), with real bounds at the three points. -/
theorem concave_three_point {X : Type*} {m : ℝ} {family : Iio m → X → EReal} {x : X}
    (hconc : SGPT.Convex.IsConvex (sourceTestCurveNegativeTrace m family x))
    {p q r : Iio m} (hpq : p.1 < q.1) (hqr : q.1 < r.1) {yp yq yr : ℝ}
    (hp : (yp : EReal) ≤ family p x) (hr : (yr : EReal) ≤ family r x)
    (hq : family q x ≤ (yq : EReal)) :
    (r.1 - q.1) * yp + (q.1 - p.1) * yr ≤ (r.1 - p.1) * yq := by
  have hpe : (p.1, -yp) ∈ SGPT.Convex.epigraph (sourceTestCurveNegativeTrace m family x) := by
    change sourceTestCurveNegativeTrace m family x p.1 ≤ ((-yp : ℝ) : EReal)
    rw [sourceTestCurveNegativeTrace, dif_pos (show p.1 < m from p.2), EReal.coe_neg]
    exact EReal.neg_le_neg_iff.mpr hp
  have hre : (r.1, -yr) ∈ SGPT.Convex.epigraph (sourceTestCurveNegativeTrace m family x) := by
    change sourceTestCurveNegativeTrace m family x r.1 ≤ ((-yr : ℝ) : EReal)
    rw [sourceTestCurveNegativeTrace, dif_pos (show r.1 < m from r.2), EReal.coe_neg]
    exact EReal.neg_le_neg_iff.mpr hr
  have hD : 0 < r.1 - p.1 := by linarith
  have hc := hconc hpe hre (a := (r.1 - q.1) / (r.1 - p.1)) (b := (q.1 - p.1) / (r.1 - p.1))
    (div_nonneg (by linarith) hD.le) (div_nonneg (by linarith) hD.le)
    (by field_simp; ring)
  have hpt : (r.1 - q.1) / (r.1 - p.1) * p.1 + (q.1 - p.1) / (r.1 - p.1) * r.1 = q.1 := by
    field_simp
    ring
  change sourceTestCurveNegativeTrace m family x
      ((r.1 - q.1) / (r.1 - p.1) * p.1 + (q.1 - p.1) / (r.1 - p.1) * r.1) ≤
    (((r.1 - q.1) / (r.1 - p.1) * (-yp) + (q.1 - p.1) / (r.1 - p.1) * (-yr) : ℝ) : EReal) at hc
  rw [hpt, sourceTestCurveNegativeTrace, dif_pos (show q.1 < m from q.2)] at hc
  have h2 : -(yq : EReal) ≤ -family q x := EReal.neg_le_neg_iff.mpr hq
  have h3 := h2.trans hc
  rw [← EReal.coe_neg, EReal.coe_le_coe_iff] at h3
  have h4 : (r.1 - q.1) / (r.1 - p.1) * yp + (q.1 - p.1) / (r.1 - p.1) * yr ≤ yq := by
    linarith
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_le_iff₀ hD] at h4
  linarith

/-- **Legendre inversion** (`prop:Leginvtc`) at one point: for a decreasing, concave,
left-continuous family bounded from above, the inverse Legendre transform of
`t ↦ sup_{σ < m} (tσ + f(σ))` at `τ < m` is at most `f(τ)`. -/
theorem legendre_inverse_le {X : Type*} {m : ℝ} {family : Iio m → X → EReal} {x : X}
    (hanti : Antitone (fun τ ↦ family τ x))
    (hconc : SGPT.Convex.IsConvex (sourceTestCurveNegativeTrace m family x))
    (hleft : ∀ (τ : Iio m) (r : ℝ), family τ x < r →
      ∃ σ : Iio m, σ.1 < τ.1 ∧ family σ x < r)
    {c : ℝ} (hc : ∀ τ, family τ x ≤ c) (τ : Iio m) :
    (⨅ t : Ioi (0 : ℝ), (⨆ σ : Iio m, ((t.1 * σ.1 : ℝ) : EReal) + family σ x) -
      ((t.1 * τ.1 : ℝ) : EReal)) ≤ family τ x := by
  apply EReal.le_of_forall_lt_iff_le.mp
  intro r hr
  obtain ⟨σ₁, hσ₁, hfσ₁⟩ := hleft τ r hr
  have hτm : τ.1 < m := τ.2
  suffices h : ∃ t : ℝ, 0 < t ∧ ∀ σ : Iio m, ∀ y : ℝ, (y : EReal) ≤ family σ x →
      t * σ.1 + y ≤ r + t * τ.1 by
    obtain ⟨t, ht, hbound⟩ := h
    refine (iInf_le (fun t : Ioi (0 : ℝ) ↦ (⨆ σ : Iio m, ((t.1 * σ.1 : ℝ) : EReal) +
      family σ x) - ((t.1 * τ.1 : ℝ) : EReal)) ⟨t, ht⟩).trans ?_
    have hsup : (⨆ σ : Iio m, ((t * σ.1 : ℝ) : EReal) + family σ x) ≤
        ((r + t * τ.1 : ℝ) : EReal) := by
      apply iSup_le
      intro σ
      have hne : family σ x ≠ ⊤ := ne_of_lt ((hc σ).trans_lt (EReal.coe_lt_top c))
      have h1 : family σ x ≤ ((r + t * τ.1 - t * σ.1 : ℝ) : EReal) :=
        ereal_le_coe_of_forall_real hne (fun y hy ↦ by linarith [hbound σ y hy])
      calc ((t * σ.1 : ℝ) : EReal) + family σ x
          ≤ ((t * σ.1 : ℝ) : EReal) + ((r + t * τ.1 - t * σ.1 : ℝ) : EReal) :=
            add_le_add le_rfl h1
        _ = ((r + t * τ.1 : ℝ) : EReal) := by
          rw [← EReal.coe_add]
          congr 1
          ring
    calc (⨆ σ : Iio m, ((t * σ.1 : ℝ) : EReal) + family σ x) - ((t * τ.1 : ℝ) : EReal)
        ≤ ((r + t * τ.1 : ℝ) : EReal) - ((t * τ.1 : ℝ) : EReal) := EReal.sub_le_sub hsup le_rfl
      _ = (r : EReal) := by
        rw [← EReal.coe_sub]
        congr 1
        ring
  let τ' : Iio m := ⟨(σ₁.1 + τ.1) / 2, by change (σ₁.1 + τ.1) / 2 < m; linarith⟩
  have hσ₁τ' : σ₁.1 < τ'.1 := by change σ₁.1 < (σ₁.1 + τ.1) / 2; linarith
  have hτ'τ : τ'.1 < τ.1 := by change (σ₁.1 + τ.1) / 2 < τ.1; linarith
  have hfτ'σ₁ : family τ' x ≤ family σ₁ x := hanti (show σ₁ ≤ τ' from hσ₁τ'.le)
  by_cases hbot : family τ' x = ⊥
  · -- the family is `-∞` from `τ'` on
    have hd : 0 < τ.1 - τ'.1 := by linarith
    let t : ℝ := max 1 ((c - r) / (τ.1 - τ'.1))
    have ht : 0 < t := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hmul : c - r ≤ t * (τ.1 - τ'.1) := by
      have h1 : (c - r) / (τ.1 - τ'.1) ≤ t := le_max_right _ _
      calc c - r = (c - r) / (τ.1 - τ'.1) * (τ.1 - τ'.1) := (div_mul_cancel₀ _ hd.ne').symm
        _ ≤ t * (τ.1 - τ'.1) := mul_le_mul_of_nonneg_right h1 hd.le
    refine ⟨t, ht, fun σ y hy ↦ ?_⟩
    by_cases hσ : τ'.1 ≤ σ.1
    · have h1 : family σ x ≤ family τ' x := hanti (show τ' ≤ σ from hσ)
      rw [hbot] at h1
      exact absurd (hy.trans h1) (by simp)
    · have hσ' : σ.1 < τ'.1 := lt_of_not_ge hσ
      have hyc : y ≤ c := EReal.coe_le_coe_iff.mp (hy.trans (hc σ))
      nlinarith [mul_pos ht (sub_pos.mpr hσ')]
  · have hτ'top : family τ' x ≠ ⊤ := ne_of_lt ((hc τ').trans_lt (EReal.coe_lt_top c))
    have hσ₁top : family σ₁ x ≠ ⊤ := ne_of_lt ((hc σ₁).trans_lt (EReal.coe_lt_top c))
    have hσ₁bot : family σ₁ x ≠ ⊥ := fun h ↦ hbot (le_bot_iff.mp (h ▸ hfτ'σ₁))
    obtain ⟨y', hy'⟩ : ∃ y' : ℝ, family τ' x = (y' : EReal) :=
      ⟨(family τ' x).toReal, (EReal.coe_toReal hτ'top hbot).symm⟩
    obtain ⟨y₁, hy₁⟩ : ∃ y₁ : ℝ, family σ₁ x = (y₁ : EReal) :=
      ⟨(family σ₁ x).toReal, (EReal.coe_toReal hσ₁top hσ₁bot).symm⟩
    have hy'y₁ : y' ≤ y₁ := by
      rw [hy', hy₁] at hfτ'σ₁
      exact EReal.coe_le_coe_iff.mp hfτ'σ₁
    have hy₁r : y₁ < r := by
      rw [hy₁] at hfσ₁
      exact EReal.coe_lt_coe_iff.mp hfσ₁
    have hd : 0 < τ'.1 - σ₁.1 := by linarith
    have hmτ : 0 < m - τ.1 := by linarith
    let t₀ : ℝ := (y₁ - y') / (τ'.1 - σ₁.1)
    let ε : ℝ := (r - y₁) / (m - τ.1)
    have ht₀ : 0 ≤ t₀ := div_nonneg (by linarith) hd.le
    have hε0 : 0 < ε := div_pos (by linarith) hmτ
    have ht₀d : t₀ * (τ'.1 - σ₁.1) = y₁ - y' := div_mul_cancel₀ _ hd.ne'
    have hεm : ε * (m - τ.1) = r - y₁ := div_mul_cancel₀ _ hmτ.ne'
    refine ⟨t₀ + ε, by linarith, fun σ y hy ↦ ?_⟩
    have hσm : σ.1 < m := σ.2
    rcases le_or_gt σ.1 σ₁.1 with h1 | h1
    · have hb : (τ'.1 - σ₁.1) * y ≤ (τ'.1 - σ₁.1) * y₁ + (σ₁.1 - σ.1) * (y₁ - y') := by
        rcases h1.eq_or_lt with heq | hlt
        · have hσeq : σ = σ₁ := Subtype.ext heq
          subst hσeq
          have hyy₁ : y ≤ y₁ := by
            rw [hy₁] at hy
            exact EReal.coe_le_coe_iff.mp hy
          nlinarith
        · have h3 := concave_three_point hconc hlt hσ₁τ' hy hy'.ge hy₁.le
          nlinarith
      have hy2 : y ≤ y₁ + t₀ * (σ₁.1 - σ.1) := by
        have h4 : (τ'.1 - σ₁.1) * y ≤ (τ'.1 - σ₁.1) * (y₁ + t₀ * (σ₁.1 - σ.1)) := by
          nlinarith
        exact le_of_mul_le_mul_left h4 hd
      nlinarith [mul_nonneg hε0.le (show (0 : ℝ) ≤ τ.1 - σ.1 by linarith),
        mul_nonneg ht₀ (show (0 : ℝ) ≤ τ.1 - σ₁.1 by linarith)]
    · have hyy₁ : y ≤ y₁ := by
        have h2 : (y : EReal) ≤ family σ₁ x := hy.trans (hanti (show σ₁ ≤ σ from h1.le))
        rw [hy₁] at h2
        exact EReal.coe_le_coe_iff.mp h2
      rcases le_or_gt σ.1 τ.1 with h2 | h2
      · nlinarith [mul_nonneg (show (0 : ℝ) ≤ t₀ + ε by linarith) (sub_nonneg.mpr h2)]
      · have hτ'σ : τ'.1 < σ.1 := by linarith
        have h3 := concave_three_point hconc hσ₁τ' hτ'σ hy₁.ge hy hy'.le
        have hy3 : y ≤ y' - t₀ * (σ.1 - τ'.1) := by
          have h4 : (τ'.1 - σ₁.1) * y ≤ (τ'.1 - σ₁.1) * (y' - t₀ * (σ.1 - τ'.1)) := by
            nlinarith
          exact le_of_mul_le_mul_left h4 hd
        nlinarith [mul_nonneg hε0.le (show (0 : ℝ) ≤ m - σ.1 by linarith),
          mul_nonneg ht₀ (show (0 : ℝ) ≤ τ.1 - τ'.1 by linarith)]

/-- **Boundary duality** (end of the proof of `lma:LegendsRtoTC`): a convex function `g` on
`(0, ∞)` with limit `L` at `0` satisfies `L ≤ sup_{τ < c} inf_{t > 0} (g(t) - tτ)`. -/
theorem boundary_le_iSup_iInf {g : ℝ → EReal}
    (hconv : Convex ℝ {p : ℝ × ℝ | 0 < p.1 ∧ g p.1 ≤ (p.2 : EReal)})
    (hfin : ∀ t, 0 < t → g t < ⊤) {L : EReal} (hL : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 L)) (c : ℝ) :
    L ≤ ⨆ τ : Iio c, ⨅ t : Ioi (0 : ℝ), g t.1 - ((t.1 * τ.1 : ℝ) : EReal) := by
  apply EReal.ge_of_forall_gt_iff_ge.mp
  intro r hr
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (r : EReal) < g t := hL.eventually (lt_mem_nhds hr)
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp hev
  have hu0 : (0 : ℝ) < u := hu
  obtain ⟨δ, hδu⟩ : ∃ δ : ℝ, δ = u / 2 := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδu]; positivity
  have hnear : ∀ t, 0 < t → t ≤ δ → (r : EReal) < g t := by
    intro t ht htδ
    exact hsub ⟨ht, by change t < u; linarith⟩
  have hR0 := hnear (δ / 2) (by positivity) (by linarith)
  obtain ⟨R, hR⟩ : ∃ R : ℝ, g (δ / 2) = (R : EReal) :=
    ⟨(g (δ / 2)).toReal, (EReal.coe_toReal (ne_of_lt (hfin _ (by positivity)))
      (ne_of_gt (bot_lt_iff_ne_bot.mpr (ne_bot_of_gt hR0)))).symm⟩
  have hrR : r < R := by
    rw [hR] at hR0
    exact EReal.coe_lt_coe_iff.mp hR0
  obtain ⟨τ₀, hτ₀def⟩ : ∃ τ₀ : ℝ, τ₀ = 2 * (r - R) / δ := ⟨_, rfl⟩
  have hτ₀δ : τ₀ * δ = 2 * (r - R) := by rw [hτ₀def]; exact div_mul_cancel₀ _ hδ.ne'
  have hτ₀ : τ₀ < 0 := by rw [hτ₀def]; exact div_neg_of_neg_of_pos (by linarith) hδ
  let τ : Iio c := ⟨min τ₀ (c - 1), by
    change min τ₀ (c - 1) < c
    exact (min_le_right _ _).trans_lt (by linarith)⟩
  have hττ₀ : τ.1 ≤ τ₀ := min_le_left _ _
  refine le_trans ?_ (le_iSup (fun τ : Iio c ↦ ⨅ t : Ioi (0 : ℝ),
    g t.1 - ((t.1 * τ.1 : ℝ) : EReal)) τ)
  apply le_iInf
  intro t
  have ht : 0 < t.1 := t.2
  rcases le_or_gt t.1 δ with htδ | htδ
  · have h1 := (hnear t.1 ht htδ).le
    have h2 : (0 : EReal) ≤ ((-(t.1 * τ.1) : ℝ) : EReal) :=
      EReal.coe_nonneg.mpr (by nlinarith)
    calc (r : EReal) = (r : EReal) + 0 := (add_zero _).symm
      _ ≤ g t.1 + ((-(t.1 * τ.1) : ℝ) : EReal) := add_le_add h1 h2
      _ = g t.1 - ((t.1 * τ.1 : ℝ) : EReal) := by rw [EReal.coe_neg, sub_eq_add_neg]
  · have hclaim : ((r + t.1 * τ₀ : ℝ) : EReal) ≤ g t.1 := by
      apply EReal.le_of_forall_lt_iff_le.mp
      intro y hy
      apply EReal.coe_le_coe
      have hp1 : ((δ / 2, R) : ℝ × ℝ) ∈ {p : ℝ × ℝ | 0 < p.1 ∧ g p.1 ≤ (p.2 : EReal)} :=
        ⟨by positivity, hR.le⟩
      have hp2 : ((t.1, y) : ℝ × ℝ) ∈ {p : ℝ × ℝ | 0 < p.1 ∧ g p.1 ≤ (p.2 : EReal)} :=
        ⟨ht, hy.le⟩
      have hden : 0 < t.1 - δ / 2 := by linarith
      have hc := hconv hp1 hp2 (a := (t.1 - δ) / (t.1 - δ / 2)) (b := (δ / 2) / (t.1 - δ / 2))
        (div_nonneg (by linarith) hden.le) (div_nonneg (by positivity) hden.le)
        (by rw [← add_div, div_eq_one_iff_eq hden.ne']; ring)
      have hpt : (t.1 - δ) / (t.1 - δ / 2) * (δ / 2) + (δ / 2) / (t.1 - δ / 2) * t.1 = δ := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hden.ne']
        ring
      have hc2 : g ((t.1 - δ) / (t.1 - δ / 2) * (δ / 2) + (δ / 2) / (t.1 - δ / 2) * t.1) ≤
          (((t.1 - δ) / (t.1 - δ / 2) * R + (δ / 2) / (t.1 - δ / 2) * y : ℝ) : EReal) := hc.2
      rw [hpt] at hc2
      have h5 := (hnear δ hδ le_rfl).trans_le hc2
      rw [EReal.coe_lt_coe_iff, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
        lt_div_iff₀ hden] at h5
      nlinarith
    have h3 : (0 : EReal) ≤ ((t.1 * τ₀ - t.1 * τ.1 : ℝ) : EReal) :=
      EReal.coe_nonneg.mpr (by nlinarith)
    calc (r : EReal) = ((r + t.1 * τ₀ : ℝ) : EReal) + ((-(t.1 * τ₀) : ℝ) : EReal) := by
          rw [← EReal.coe_add]
          congr 1
          ring
      _ ≤ g t.1 + ((-(t.1 * τ₀) : ℝ) : EReal) := add_le_add hclaim le_rfl
      _ = g t.1 + ((-(t.1 * τ₀) : ℝ) : EReal) + 0 := (add_zero _).symm
      _ ≤ g t.1 + ((-(t.1 * τ₀) : ℝ) : EReal) + ((t.1 * τ₀ - t.1 * τ.1 : ℝ) : EReal) :=
        add_le_add le_rfl h3
      _ = g t.1 - ((t.1 * τ.1 : ℝ) : EReal) := by
        rw [add_assoc, ← EReal.coe_add,
          show g t.1 - ((t.1 * τ.1 : ℝ) : EReal) = g t.1 + ((-(t.1 * τ.1) : ℝ) : EReal) by
            rw [EReal.coe_neg, sub_eq_add_neg]]
        congr 2
        ring

/-- For a decreasing family of upper semicontinuous functions bounded from above, the raw
supremum `x ↦ sup_{σ < m} (tσ + f_σ(x))`, `t > 0`, is upper semicontinuous: on a grid of step
`δ` the supremum is, up to `tδ`, a locally finite maximum. -/
theorem upperSemicontinuous_iSup_affine {X : Type*} [TopologicalSpace X] {m : ℝ}
    {family : Iio m → X → EReal} (husc : ∀ τ, UpperSemicontinuous (family τ))
    (hanti : ∀ x, Antitone (fun τ ↦ family τ x)) {c : ℝ} (hc : ∀ τ x, family τ x ≤ c)
    {t : ℝ} (ht : 0 < t) :
    UpperSemicontinuous (fun x ↦ ⨆ σ : Iio m, ((t * σ.1 : ℝ) : EReal) + family σ x) := by
  intro x₀ y hy
  obtain ⟨r₂, h12, hr₂y⟩ := EReal.exists_between_coe_real hy
  obtain ⟨r₁, hr₁, hr₁₂⟩ := EReal.exists_between_coe_real h12
  have hr : r₁ < r₂ := EReal.coe_lt_coe_iff.mp hr₁₂
  let δ : ℝ := (r₂ - r₁) / t
  have hδ : 0 < δ := div_pos (by linarith) ht
  have htδ : t * δ = r₂ - r₁ := mul_div_cancel₀ _ ht.ne'
  obtain ⟨K, hK⟩ := exists_nat_gt ((c + t * m - r₁) / (t * δ))
  have hK' : c + t * m - r₁ < K * (t * δ) := (div_lt_iff₀ (by positivity)).mp hK
  let G : ℕ → Iio m := fun k ↦ ⟨m - (k + 1) * δ, by
    change m - ((k : ℝ) + 1) * δ < m
    have : 0 < ((k : ℝ) + 1) * δ := by positivity
    linarith⟩
  have hk : ∀ k : ℕ, ∀ᶠ x in 𝓝 x₀, ((t * (G k).1 : ℝ) : EReal) + family (G k) x < (r₁ : EReal) := by
    intro k
    have hx₀ : family (G k) x₀ < ((r₁ - t * (G k).1 : ℝ) : EReal) := by
      by_contra hcon
      have h1 := not_lt.mp hcon
      have h2 : (r₁ : EReal) ≤ ((t * (G k).1 : ℝ) : EReal) + family (G k) x₀ := by
        calc (r₁ : EReal) = ((t * (G k).1 : ℝ) : EReal) + ((r₁ - t * (G k).1 : ℝ) : EReal) := by
              rw [← EReal.coe_add]
              congr 1
              ring
          _ ≤ ((t * (G k).1 : ℝ) : EReal) + family (G k) x₀ := add_le_add le_rfl h1
      exact absurd (h2.trans (le_iSup (fun σ : Iio m ↦ ((t * σ.1 : ℝ) : EReal) + family σ x₀)
        (G k))) (not_le.mpr hr₁)
    filter_upwards [husc (G k) x₀ _ hx₀] with x hx
    calc ((t * (G k).1 : ℝ) : EReal) + family (G k) x
        < ((t * (G k).1 : ℝ) : EReal) + ((r₁ - t * (G k).1 : ℝ) : EReal) :=
          EReal.add_lt_add_left_coe hx _
      _ = (r₁ : EReal) := by
        rw [← EReal.coe_add]
        congr 1
        ring
  have hall : ∀ᶠ x in 𝓝 x₀, ∀ k ∈ Finset.range K,
      ((t * (G k).1 : ℝ) : EReal) + family (G k) x < (r₁ : EReal) :=
    (Filter.eventually_all_finset (Finset.range K)).mpr (fun k _ ↦ hk k)
  filter_upwards [hall] with x hx
  refine lt_of_le_of_lt ?_ hr₂y
  apply iSup_le
  intro σ
  have hσm : σ.1 < m := σ.2
  have hpos : 0 ≤ (m - σ.1) / δ := div_nonneg (by linarith) hδ.le
  let k : ℕ := ⌊(m - σ.1) / δ⌋₊
  have hk1 : (k : ℝ) ≤ (m - σ.1) / δ := Nat.floor_le hpos
  have hk2 : (m - σ.1) / δ < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hk1' : (k : ℝ) * δ ≤ m - σ.1 := (le_div_iff₀ hδ).mp hk1
  have hk2' : m - σ.1 < ((k : ℝ) + 1) * δ := (div_lt_iff₀ hδ).mp hk2
  have hGσ : (G k).1 < σ.1 := by change m - ((k : ℝ) + 1) * δ < σ.1; linarith
  have hGval : (G k).1 = m - ((k : ℝ) + 1) * δ := rfl
  by_cases hkK : k < K
  · have h1 := (hx k (Finset.mem_range.mpr hkK)).le
    have h2 : family σ x ≤ family (G k) x := hanti x (show G k ≤ σ from hGσ.le)
    calc ((t * σ.1 : ℝ) : EReal) + family σ x
        ≤ ((t * (G k).1 + t * δ : ℝ) : EReal) + family (G k) x :=
          add_le_add (EReal.coe_le_coe (by nlinarith)) h2
      _ = ((t * δ : ℝ) : EReal) + (((t * (G k).1 : ℝ) : EReal) + family (G k) x) := by
        rw [EReal.coe_add, add_comm ((t * (G k).1 : ℝ) : EReal), add_assoc]
      _ ≤ ((t * δ : ℝ) : EReal) + (r₁ : EReal) := add_le_add le_rfl h1
      _ = (r₂ : EReal) := by
        rw [← EReal.coe_add]
        congr 1
        linarith
  · have hKk : (K : ℝ) ≤ k := by exact_mod_cast not_lt.mp hkK
    calc ((t * σ.1 : ℝ) : EReal) + family σ x
        ≤ ((t * σ.1 : ℝ) : EReal) + (c : EReal) := add_le_add le_rfl (hc σ x)
      _ = ((t * σ.1 + c : ℝ) : EReal) := (EReal.coe_add _ _).symm
      _ ≤ (r₂ : EReal) := by
        apply EReal.coe_le_coe
        have h3 : (K : ℝ) * (t * δ) ≤ (k : ℝ) * (t * δ) :=
          mul_le_mul_of_nonneg_right hKk (by positivity)
        nlinarith

end SGPT.TestCurve.RWNTwisted
