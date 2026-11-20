import SGPT.Foundations.Analysis.Pending.FiniteGeodesicsTimeConvexity
import SGPT.Foundations.Analysis.Pending.SubgeodesicInfimum
import SGPT.Foundations.Analysis.FirstPass.SubgeodesicClosedRestriction

set_option autoImplicit false

/-!
# Monotonicity of the Perron geodesic between ordered endpoints

Xia, Lemma 4.2.2 (`xia-sgpt:page-0156`; blueprint `trace:finite-geodesic-monotone`): if
`u₁ ≤ u₀`, the Perron finite geodesic `t ↦ u_t` from `u₀` to `u₁` is decreasing on `[0, 1]`.

The source assumes in addition that the geodesic, with its two endpoints, is a subgeodesic.  That
hypothesis is not needed (`finiteGeodesic_antitoneOn`, `antitoneOn_closedSubgeodesicSlice`):

* the constant family `u₁` is a Perron competitor (`u₁ ≤ u₀`), so `u₁ ≤ u_t`;
* the chord bound gives `u_t ≤ (1 - t) u₀ + t u₁ ≤ u₀`;
* at a point where the slices are finite, `f(t) = u_t(x)` is convex on `(0, 1)`
  (`finiteGeodesic_verticalTrace_convexity_dichotomy`), `f ≥ c = u₁(x)`, and
  `f(b) ≤ c + (1 - b)(u₀(x) - c)`.  If `f(s) < f(t)` for some `s < t`, the slope `δ > 0` of `f` on
  `[s, t]` is at most its slope on `[t, b]`, so `f(b) ≥ c + δ (b - t)` for every `b ∈ (t, 1)`,
  which contradicts the upper bound for `b` close to `1`.

No compactness, connectedness, Kähler form or mass hypothesis is used.  Sorry-free.
-/

open Set

namespace SGPT.Foundations.Analysis.Pending.FiniteGeodesicMonotone

open FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

variable {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}

/-- **A convex function that stays above `c` and is bounded near `1` by the chord towards `c`
cannot increase.**  Elementary real lemma behind Xia's Lemma 4.2.2. -/
theorem antitoneOn_of_convexOn_of_le_chord {f : ℝ → ℝ} {A c : ℝ}
    (hf : ConvexOn ℝ (Ioo (0 : ℝ) 1) f) (hlow : ∀ t ∈ Ioo (0 : ℝ) 1, c ≤ f t)
    (hup : ∀ t ∈ Ioo (0 : ℝ) 1, f t ≤ (1 - t) * A + t * c) :
    AntitoneOn f (Ioo (0 : ℝ) 1) := by
  intro s hs t ht hst
  rcases eq_or_lt_of_le hst with rfl | hlt
  · exact le_rfl
  by_contra hcon
  rw [not_le] at hcon
  set δ : ℝ := (f t - f s) / (t - s) with hδ
  have hts : 0 < t - s := sub_pos.mpr hlt
  have hδpos : 0 < δ := div_pos (sub_pos.mpr hcon) hts
  set D : ℝ := max (A - c) 0 with hD
  have hD0 : 0 ≤ D := le_max_right _ _
  have hDA : A - c ≤ D := le_max_left _ _
  have h1t : 0 < 1 - t := sub_pos.mpr ht.2
  set e : ℝ := (1 - t) * δ / (2 * (δ + D)) with he
  have hδD : 0 < δ + D := by linarith
  have hepos : 0 < e := div_pos (mul_pos h1t hδpos) (by linarith)
  have he_eq : e * (δ + D) = (1 - t) * δ / 2 := by
    rw [he]
    field_simp
  have hele : e ≤ (1 - t) / 2 := by
    rw [he, div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  set b : ℝ := 1 - e with hb
  have hbt : t < b := by rw [hb]; linarith
  have hb1 : b < 1 := by rw [hb]; linarith
  have hbmem : b ∈ Ioo (0 : ℝ) 1 := ⟨ht.1.trans hbt, hb1⟩
  have hslope := hf.slope_mono_adjacent hs hbmem hlt hbt
  have hbt' : 0 < b - t := sub_pos.mpr hbt
  have hfb : f t + δ * (b - t) ≤ f b := by
    have := (le_div_iff₀ hbt').mp hslope
    linarith
  have hupb := hup b hbmem
  have hlowt := hlow t ht
  have h1b : 1 - b = e := by rw [hb]; ring
  have hkey : δ * (b - t) ≤ e * D := by
    have : f b ≤ c + (1 - b) * (A - c) := by linarith
    rw [h1b] at this
    nlinarith
  have hbt_eq : b - t = (1 - t) - e := by rw [hb]; ring
  rw [hbt_eq] at hkey
  have : δ * (1 - t) ≤ e * (δ + D) := by nlinarith
  rw [he_eq] at this
  nlinarith

/-- The upper endpoint bounds every slice from below when it lies below the lower one. -/
theorem le_finiteGeodesic_of_le (hu₁ : IsThetaPshPotential θ u₁) (h10 : u₁ ≤ u₀) (t : ℝ) :
    u₁ ≤ finiteGeodesic θ u₀ u₁ t :=
  le_finiteGeodesic_of_le_endpoints hu₁ h10 le_rfl t

/-- Every interior slice lies below the first endpoint when `u₁ ≤ u₀`. -/
theorem finiteGeodesic_le_of_le (hu₀ : IsThetaPshPotential θ u₀)
    (hu₁ : IsThetaPshPotential θ u₁) (h10 : u₁ ≤ u₀) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    finiteGeodesic θ u₀ u₁ t ≤ u₀ := by
  intro x
  refine (finiteGeodesic_le_eRealChord hu₀ hu₁ ht x).trans ?_
  calc eRealChord (u₀ x) (u₁ x) t ≤ eRealChord (u₀ x) (u₀ x) t :=
        eRealChord_mono le_rfl (h10 x) ht.1.le ht.2.le
    _ ≤ u₀ x := by
        by_cases hbot : u₀ x = ⊥
        · rw [SubgeodesicInfimum.eRealChord_eq_bot_of_endpoint_eq_bot (Or.inl hbot) ht]
          exact bot_le
        · have htop : u₀ x ≠ ⊤ := hu₀.1.quasiPlurisubharmonic.ne_top x
          rw [← EReal.coe_toReal htop hbot, SubgeodesicInfimum.eRealChord_coe_coe]
          exact EReal.coe_le_coe_iff.mpr (le_of_eq (by ring))

/-- **The Perron geodesic between ordered endpoints is decreasing in time on `(0, 1)`.**  No
subgeodesic hypothesis on the geodesic is needed. -/
theorem finiteGeodesic_antitoneOn (hu₀ : IsThetaPshPotential θ u₀)
    (hu₁ : IsThetaPshPotential θ u₁) (h10 : u₁ ≤ u₀) (x : M) :
    AntitoneOn (fun t => finiteGeodesic θ u₀ u₁ t x) (Ioo (0 : ℝ) 1) := by
  rcases finiteGeodesic_verticalTrace_convexity_dichotomy hu₀ hu₁ x with hall | ⟨hfin, hconv⟩
  · intro s hs t ht _
    simp only [hall s hs, hall t ht, le_refl]
  set f : ℝ → ℝ := fun t => (finiteGeodesic θ u₀ u₁ t x).toReal with hf
  have hreal : ∀ t ∈ Ioo (0 : ℝ) 1, finiteGeodesic θ u₀ u₁ t x = (f t : EReal) :=
    fun t ht => (EReal.coe_toReal (hfin t ht).1 (hfin t ht).2).symm
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hu1top : u₁ x ≠ ⊤ := hu₁.1.quasiPlurisubharmonic.ne_top x
  have hu0top : u₀ x ≠ ⊤ := hu₀.1.quasiPlurisubharmonic.ne_top x
  have hchord : ∀ t ∈ Ioo (0 : ℝ) 1,
      finiteGeodesic θ u₀ u₁ t x ≤ eRealChord (u₀ x) (u₁ x) t :=
    fun t ht => finiteGeodesic_le_eRealChord hu₀ hu₁ ht x
  have hu1bot : u₁ x ≠ ⊥ := by
    intro h
    have hc := hchord _ hhalf
    rw [SubgeodesicInfimum.eRealChord_eq_bot_of_endpoint_eq_bot (Or.inr h) hhalf] at hc
    exact (hfin _ hhalf).2 (le_bot_iff.mp hc)
  have hu0bot : u₀ x ≠ ⊥ := ne_bot_of_le_ne_bot hu1bot (h10 x)
  set A : ℝ := (u₀ x).toReal with hA
  set c : ℝ := (u₁ x).toReal with hc
  have hu0 : u₀ x = (A : EReal) := (EReal.coe_toReal hu0top hu0bot).symm
  have hu1 : u₁ x = (c : EReal) := (EReal.coe_toReal hu1top hu1bot).symm
  have hup : ∀ t ∈ Ioo (0 : ℝ) 1, f t ≤ (1 - t) * A + t * c := by
    intro t ht
    have h := hchord t ht
    rw [hreal t ht, hu0, hu1, SubgeodesicInfimum.eRealChord_coe_coe] at h
    exact EReal.coe_le_coe_iff.mp h
  have hlow : ∀ t ∈ Ioo (0 : ℝ) 1, c ≤ f t := by
    intro t ht
    have h := le_finiteGeodesic_of_le hu₁ h10 t x
    rw [hreal t ht, hu1] at h
    exact EReal.coe_le_coe_iff.mp h
  have hanti := antitoneOn_of_convexOn_of_le_chord hconv hlow hup
  intro s hs t ht hst
  simp only
  rw [hreal s hs, hreal t ht]
  exact EReal.coe_le_coe_iff.mpr (hanti hs ht hst)

/-- **Xia, Lemma 4.2.2, on the closed interval**: with the endpoint values `u₀` at `0` and `u₁`
at `1`, the extended family `t ↦ u_t` is decreasing on `[0, 1]` when `u₁ ≤ u₀`.  No subgeodesic
hypothesis is needed. -/
theorem antitoneOn_closedSubgeodesicSlice (hu₀ : IsThetaPshPotential θ u₀)
    (hu₁ : IsThetaPshPotential θ u₁) (h10 : u₁ ≤ u₀) (x : M) :
    AntitoneOn (fun t => closedSubgeodesicSlice (finiteGeodesic θ u₀ u₁) u₀ u₁ t x)
      (Icc (0 : ℝ) 1) := by
  have hint : ∀ t ∈ Icc (0 : ℝ) 1, t ≠ 0 → t ≠ 1 → t ∈ Ioo (0 : ℝ) 1 :=
    fun t ht h0 h1 => ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩
  intro s hs t ht hst
  simp only [closedSubgeodesicSlice]
  by_cases ht0 : t = 0
  · subst ht0
    have hs0 : s = 0 := le_antisymm hst hs.1
    subst hs0
    simp
  by_cases hs1 : s = 1
  · subst hs1
    have ht1 : t = 1 := le_antisymm ht.2 hst
    subst ht1
    simp
  by_cases hs0 : s = 0
  · subst hs0
    simp only [if_true, if_neg ht0]
    by_cases ht1 : t = 1
    · simp only [if_pos ht1]
      exact h10 x
    · simp only [if_neg ht1]
      exact finiteGeodesic_le_of_le hu₀ hu₁ h10 (hint t ht ht0 ht1) x
  · simp only [if_neg hs0, if_neg hs1, if_neg ht0]
    by_cases ht1 : t = 1
    · simp only [if_pos ht1]
      exact le_finiteGeodesic_of_le hu₁ h10 s x
    · simp only [if_neg ht1]
      exact finiteGeodesic_antitoneOn hu₀ hu₁ h10 x (hint s hs hs0 hs1) (hint t ht ht0 ht1) hst

/-- **`trace:finite-geodesic-monotone` as stated** (Xia, Lemma 4.2.2): with the additional
hypothesis of the source that the geodesic is a subgeodesic from `u₀` to `u₁`, which the proof
does not use. -/
theorem antitoneOn_closedSubgeodesicSlice_of_isSubgeodesicFrom
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁) (h10 : u₁ ≤ u₀)
    (_hsub : IsSubgeodesicFrom θ (finiteGeodesic θ u₀ u₁) u₀ u₁) (x : M) :
    AntitoneOn (fun t => closedSubgeodesicSlice (finiteGeodesic θ u₀ u₁) u₀ u₁ t x)
      (Icc (0 : ℝ) 1) :=
  antitoneOn_closedSubgeodesicSlice hu₀ hu₁ h10 x

end

end SGPT.Foundations.Analysis.Pending.FiniteGeodesicMonotone
