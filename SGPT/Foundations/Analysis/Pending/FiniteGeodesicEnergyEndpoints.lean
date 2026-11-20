import SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality
import SGPT.Foundations.Analysis.Pending.BoundedMongeAmpereEnergy
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicsFullMassAnyDim
import SGPT.Foundations.Analysis.Pending.Subgeodesics
import SGPT.Foundations.Analysis.FirstPass.FiniteGeodesicRooftopEndpoint
import SGPT.Foundations.Analysis.FirstPass.SubgeodesicConvexity

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Bounded Perron geodesics: affine barriers, Lipschitz slices, energy at the endpoints

Source: Xia, SGPT, proof of Proposition 4.3.3 (`xia-sgpt:page-0170`, (4.26), and
`xia-sgpt:page-0172`, the end of Step 2: "Affine barriers and Proposition 4.1.2 give ...").

Let `θ` be a smooth real `2`-form on a complex manifold `M`, let `u₀`, `u₁` be bounded and let
`U = finiteGeodesic θ u₀ u₁` be the Perron geodesic, assumed to be a subgeodesic from `u₀` to `u₁`.
Choose `C ≥ 0` with `u₁ ≤ u₀ + C` and `u₀ ≤ u₁ + C`. Then, for `0 < s, t < 1`:

* the **affine barriers** (`finiteGeodesic_barriers`):
  `u₀ - C t ≤ U_t ≤ u₀ + C t` and `u₁ - C (1 - t) ≤ U_t ≤ u₁ + C (1 - t)`; the lower barriers are
  the subgeodesics `u₀ - C t`, `u₁ - C (1 - t)` (`affineRooftopLower_le_finiteGeodesic`), the upper
  ones the chord bound (Xia, Proposition 4.1.2);
* the slices are **uniformly bounded** (`finiteGeodesic_uniformly_bounded`) and **`C`-Lipschitz in
  time** (`abs_finiteGeodesic_toReal_sub_le`): `|U_t - U_s| ≤ C |t - s|` pointwise, by the
  convexity of `t ↦ U_t(x)` and the barriers at both ends;
* on a compact Kähler manifold, for a closed real `(1,1)`-form `θ` and a bounded model `φ`, the
  energy is `C vol`-Lipschitz along the geodesic and continuous at the endpoints
  (`abs_energy_finiteGeodesic_sub_le`, `abs_energy_finiteGeodesic_sub_left_le`,
  `abs_energy_finiteGeodesic_sub_right_le`), from `|E(u) - E(v)| ≤ sup |u - v| · vol`
  (`abs_relativeEnergyOfMinimalType_sub_le`, by monotonicity and the translation formula);
* the hypotheses of `FiniteGeodesicMaximality` hold, so the complexified geodesic solves the
  homogeneous complex Monge--Ampère equation near every point
  (`exists_isBTLimit_eq_zero_finiteGeodesic_of_bounded`); for endpoints of bounded singularity type
  relative to a bounded model potential the subgeodesic hypothesis is automatic
  (`exists_isBTLimit_eq_zero_finiteGeodesic_of_relativeEInfinity`).
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.FiniteGeodesicEnergyEndpoints

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar BoundedGlobalProduct RelativeEnergy
open BoundedMongeAmpereEnergy FiniteGeodesicMaximality BedfordTaylor

noncomputable section

/-! ### Real bounds from extended-real bounds -/

theorem eq_coe_toReal_of_coe_le_le {y : EReal} {l h : ℝ} (hl : (l : EReal) ≤ y)
    (hh : y ≤ (h : EReal)) : y = (y.toReal : EReal) ∧ l ≤ y.toReal ∧ y.toReal ≤ h := by
  have hbot : y ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot l) hl
  have htop : y ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top h) hh
  have hy : y = (y.toReal : EReal) := (EReal.coe_toReal htop hbot).symm
  refine ⟨hy, ?_, ?_⟩
  · rw [hy] at hl
    exact EReal.coe_le_coe_iff.mp hl
  · rw [hy] at hh
    exact EReal.coe_le_coe_iff.mp hh

section Barriers

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- Two bounded potentials differ by at most a constant `C ≥ 0`, in both directions. -/
theorem exists_nonneg_le_add_of_bounded {u₀ u₁ : M → EReal} (hb₀ : IsBoundedPotential u₀)
    (hb₁ : IsBoundedPotential u₁) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x, u₁ x ≤ u₀ x + (C : EReal)) ∧ ∀ x, u₀ x ≤ u₁ x + (C : EReal) := by
  obtain ⟨a₀, b₀, h₀⟩ := hb₀
  obtain ⟨a₁, b₁, h₁⟩ := hb₁
  refine ⟨max (max (b₁ - a₀) (b₀ - a₁)) 0, le_max_right _ _, fun x => ?_, fun x => ?_⟩
  · calc u₁ x ≤ (b₁ : EReal) := (h₁ x).2
      _ = ((a₀ + (b₁ - a₀) : ℝ) : EReal) := by ring_nf
      _ ≤ ((a₀ + max (max (b₁ - a₀) (b₀ - a₁)) 0 : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.mpr (by
          have := le_max_left (b₁ - a₀) (b₀ - a₁)
          have := le_max_left (max (b₁ - a₀) (b₀ - a₁)) 0
          linarith)
      _ = (a₀ : EReal) + ((max (max (b₁ - a₀) (b₀ - a₁)) 0 : ℝ) : EReal) := EReal.coe_add _ _
      _ ≤ u₀ x + ((max (max (b₁ - a₀) (b₀ - a₁)) 0 : ℝ) : EReal) := add_le_add (h₀ x).1 le_rfl
  · calc u₀ x ≤ (b₀ : EReal) := (h₀ x).2
      _ = ((a₁ + (b₀ - a₁) : ℝ) : EReal) := by ring_nf
      _ ≤ ((a₁ + max (max (b₁ - a₀) (b₀ - a₁)) 0 : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.mpr (by
          have := le_max_right (b₁ - a₀) (b₀ - a₁)
          have := le_max_left (max (b₁ - a₀) (b₀ - a₁)) 0
          linarith)
      _ = (a₁ : EReal) + ((max (max (b₁ - a₀) (b₀ - a₁)) 0 : ℝ) : EReal) := EReal.coe_add _ _
      _ ≤ u₁ x + ((max (max (b₁ - a₀) (b₀ - a₁)) 0 : ℝ) : EReal) := add_le_add (h₁ x).1 le_rfl

/-- **Lower affine barrier at `t = 1`**: the time reversal of
`affineRooftopLower_le_finiteGeodesic`. -/
theorem affineRooftopLower_right_le_finiteGeodesic {θ : SmoothRealForm n M 2}
    {u₀ u₁ : M → EReal} (hu₁ : IsThetaPshPotential θ u₁) {C : ℝ}
    (hC : ∀ x, u₁ x ≤ u₀ x + (C : EReal)) (t : ℝ) (x : M) :
    u₁ x + (((-C) * (1 - t) : ℝ) : EReal) ≤ finiteGeodesic θ u₀ u₁ t x := by
  have h := affineRooftopLower_le_finiteGeodesic (θ := θ) (u₀ := u₁) (u₁ := u₀) hu₁ le_rfl
    (fun y => hC y) (1 - t) x
  rwa [finiteGeodesic_timeReversal, sub_sub_cancel] at h

/-- **The affine barriers** (Xia, proof of Proposition 4.3.3, (4.26) and Step 2). For bounded
endpoints whose Perron geodesic is a subgeodesic between them, and `C` with `u₁ ≤ u₀ + C` and
`u₀ ≤ u₁ + C`, every interior slice is finite and
`u₀ - C t ≤ U_t ≤ u₀ + C t`, `u₁ - C (1 - t) ≤ U_t ≤ u₁ + C (1 - t)`. -/
theorem finiteGeodesic_barriers {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (hsub : IsSubgeodesicFrom θ (finiteGeodesic θ u₀ u₁) u₀ u₁)
    (hb₀ : IsBoundedPotential u₀) (hb₁ : IsBoundedPotential u₁) {C : ℝ}
    (hC₁ : ∀ x, u₁ x ≤ u₀ x + (C : EReal)) (hC₀ : ∀ x, u₀ x ≤ u₁ x + (C : EReal))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : M) :
    finiteGeodesic θ u₀ u₁ t x = ((finiteGeodesic θ u₀ u₁ t x).toReal : EReal) ∧
      |(finiteGeodesic θ u₀ u₁ t x).toReal - (u₀ x).toReal| ≤ C * t ∧
      |(finiteGeodesic θ u₀ u₁ t x).toReal - (u₁ x).toReal| ≤ C * (1 - t) := by
  set g := finiteGeodesic θ u₀ u₁ t x with hg
  set a := (u₀ x).toReal
  set b := (u₁ x).toReal
  have ha : u₀ x = (a : EReal) := (EReal.coe_toReal (hb₀.ne_top x) (hb₀.ne_bot x)).symm
  have hb : u₁ x = (b : EReal) := (EReal.coe_toReal (hb₁.ne_top x) (hb₁.ne_bot x)).symm
  have hba : b ≤ a + C := by
    have := hC₁ x
    rw [ha, hb, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
    exact this
  have hab : a ≤ b + C := by
    have := hC₀ x
    rw [ha, hb, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
    exact this
  -- lower barriers
  have hl₀ : ((a + (-C) * t : ℝ) : EReal) ≤ g := by
    have h : u₀ x + (((-C) * t : ℝ) : EReal) ≤ finiteGeodesic θ u₀ u₁ t x :=
      affineRooftopLower_le_finiteGeodesic hsub.1 le_rfl hC₀ t x
    rwa [ha, ← EReal.coe_add] at h
  have hl₁ : ((b + (-C) * (1 - t) : ℝ) : EReal) ≤ g := by
    have h := affineRooftopLower_right_le_finiteGeodesic hsub.2.1 hC₁ t x
    rwa [hb, ← EReal.coe_add] at h
  -- the chord bound
  have hch : g ≤ (((1 - t) * a + t * b : ℝ) : EReal) := by
    have h := FirstPass.IsSubgeodesicFrom.le_eRealChord hsub ht x
    rw [ha, hb] at h
    refine h.trans_eq ?_
    simp only [eRealChord]
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  obtain ⟨hgeq, hgl, hgh⟩ := eq_coe_toReal_of_coe_le_le hl₀ hch
  have hgl' : b + (-C) * (1 - t) ≤ g.toReal := by
    rw [hgeq] at hl₁
    exact EReal.coe_le_coe_iff.mp hl₁
  have ht0 := ht.1
  have ht1 := ht.2
  refine ⟨hgeq, abs_le.mpr ⟨by nlinarith, by nlinarith⟩, abs_le.mpr ⟨by nlinarith, by nlinarith⟩⟩

/-- **The slices are uniformly bounded** (the hypothesis `hbd` of
`FiniteGeodesicMaximality`). -/
theorem finiteGeodesic_uniformly_bounded {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (hsub : IsSubgeodesicFrom θ (finiteGeodesic θ u₀ u₁) u₀ u₁)
    (hb₀ : IsBoundedPotential u₀) (hb₁ : IsBoundedPotential u₁) :
    ∃ A B : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, (A : EReal) ≤ finiteGeodesic θ u₀ u₁ t x ∧
      finiteGeodesic θ u₀ u₁ t x ≤ (B : EReal) := by
  obtain ⟨C, hC, hC₁, hC₀⟩ := exists_nonneg_le_add_of_bounded hb₀ hb₁
  obtain ⟨a₀, b₀, h₀⟩ := hb₀
  refine ⟨a₀ - C, b₀ + C, fun t ht x => ?_⟩
  obtain ⟨hgeq, hg, -⟩ := finiteGeodesic_barriers hsub ⟨a₀, b₀, h₀⟩ hb₁ hC₁ hC₀ ht x
  have hu₀ : u₀ x = ((u₀ x).toReal : EReal) :=
    (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top b₀) (h₀ x).2)
      (ne_bot_of_le_ne_bot (EReal.coe_ne_bot a₀) (h₀ x).1)).symm
  have hlo : a₀ ≤ (u₀ x).toReal := by
    have := (h₀ x).1
    rw [hu₀] at this
    exact EReal.coe_le_coe_iff.mp this
  have hhi : (u₀ x).toReal ≤ b₀ := by
    have := (h₀ x).2
    rw [hu₀] at this
    exact EReal.coe_le_coe_iff.mp this
  have hCt : C * t ≤ C := by nlinarith [ht.2]
  have habs := abs_le.mp hg
  rw [hgeq]
  exact ⟨EReal.coe_le_coe_iff.mpr (by linarith), EReal.coe_le_coe_iff.mpr (by linarith)⟩

/-- **The slices are `C`-Lipschitz in time.** With the hypotheses of `finiteGeodesic_barriers`,
`|U_t(x) - U_s(x)| ≤ C |t - s|` for `0 < s, t < 1`: the trace `t ↦ U_t(x)` is convex, and the
barriers bound its slopes by `-C` near `t = 0` and by `C` near `t = 1`. -/
theorem abs_finiteGeodesic_toReal_sub_le {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (hsub : IsSubgeodesicFrom θ (finiteGeodesic θ u₀ u₁) u₀ u₁)
    (hb₀ : IsBoundedPotential u₀) (hb₁ : IsBoundedPotential u₁) {C : ℝ}
    (hC₁ : ∀ x, u₁ x ≤ u₀ x + (C : EReal)) (hC₀ : ∀ x, u₀ x ≤ u₁ x + (C : EReal))
    {s t : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) (x : M) :
    |(finiteGeodesic θ u₀ u₁ t x).toReal - (finiteGeodesic θ u₀ u₁ s x).toReal| ≤
      C * |t - s| := by
  have hbar := fun r (hr : r ∈ Ioo (0 : ℝ) 1) => finiteGeodesic_barriers hsub hb₀ hb₁ hC₁ hC₀ hr x
  have hfin : ∀ r ∈ Ioo (0 : ℝ) 1, finiteGeodesic θ u₀ u₁ r x ≠ ⊥ := fun r hr => by
    rw [(hbar r hr).1]
    exact EReal.coe_ne_bot _
  -- the estimate for `s < t`
  have key : ∀ s t : ℝ, s ∈ Ioo (0 : ℝ) 1 → t ∈ Ioo (0 : ℝ) 1 → s < t →
      |(finiteGeodesic θ u₀ u₁ t x).toReal - (finiteGeodesic θ u₀ u₁ s x).toReal| ≤ C * (t - s) := by
    intro s t hs ht hst
    refine abs_le.mpr ⟨?_, ?_⟩
    · -- lower: the chord on `[r, t]` through `s`, then `r → 0⁺`
      have hlow : ∀ r ∈ Ioo (0 : ℝ) s,
          -C * (t - s) * (s + r) / (s - r) ≤ (finiteGeodesic θ u₀ u₁ t x).toReal - (finiteGeodesic θ u₀ u₁ s x).toReal := by
        intro r hr
        have hr1 : r ∈ Ioo (0 : ℝ) 1 := ⟨hr.1, hr.2.trans hs.2⟩
        have h := hsub.interior.toReal_le_chord_between hr1 ht hr.2 hst x hfin
        have hsr : 0 < s - r := sub_pos.mpr hr.2
        have htr : 0 < t - r := by linarith [hr.2]
        have hr0 := abs_le.mp (hbar r hr1).2.1
        have hs0 := abs_le.mp (hbar s hs).2.1
        have h' : (t - r) * (finiteGeodesic θ u₀ u₁ s x).toReal ≤
            (t - s) * (finiteGeodesic θ u₀ u₁ r x).toReal + (s - r) * (finiteGeodesic θ u₀ u₁ t x).toReal := by
          have e1 : 1 - (s - r) / (t - r) = (t - s) / (t - r) := by field_simp; ring
          rw [e1] at h
          have h2 := mul_le_mul_of_nonneg_left h htr.le
          have e2 : (t - r) * ((t - s) / (t - r) * (finiteGeodesic θ u₀ u₁ r x).toReal +
              (s - r) / (t - r) * (finiteGeodesic θ u₀ u₁ t x).toReal) =
              (t - s) * (finiteGeodesic θ u₀ u₁ r x).toReal + (s - r) * (finiteGeodesic θ u₀ u₁ t x).toReal := by field_simp
          linarith
        rw [div_le_iff₀ hsr]
        have h3 : (t - s) * (-C * (s + r)) ≤ (t - s) * ((finiteGeodesic θ u₀ u₁ s x).toReal - (finiteGeodesic θ u₀ u₁ r x).toReal) :=
          mul_le_mul_of_nonneg_left (by linarith [hr0.2, hs0.1]) (sub_nonneg.mpr hst.le)
        nlinarith
      have htend : Tendsto (fun r => -C * (t - s) * (s + r) / (s - r)) (𝓝[>] (0 : ℝ))
          (𝓝 (-C * (t - s))) := by
        have hc : ContinuousAt (fun r : ℝ => -C * (t - s) * (s + r) / (s - r)) 0 :=
          ((continuous_const.mul (continuous_const.add continuous_id)).continuousAt).div
            (continuous_const.sub continuous_id).continuousAt (by simpa using hs.1.ne')
        have h0 : -C * (t - s) * (s + 0) / (s - 0) = -C * (t - s) := by
          rw [add_zero, sub_zero, mul_div_assoc, div_self hs.1.ne', mul_one]
        have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        rwa [h0] at h
      have := le_of_tendsto htend (by
        filter_upwards [Ioo_mem_nhdsGT hs.1] with r hr using hlow r hr)
      linarith
    · -- upper: the chord on `[s, w]` through `t`, then `w → 1⁻`
      have hup : ∀ w ∈ Ioo t 1,
          (finiteGeodesic θ u₀ u₁ t x).toReal - (finiteGeodesic θ u₀ u₁ s x).toReal ≤ C * (t - s) * (2 - w - s) / (w - s) := by
        intro w hw
        have hw1 : w ∈ Ioo (0 : ℝ) 1 := ⟨ht.1.trans hw.1, hw.2⟩
        have h := hsub.interior.toReal_le_chord_between hs hw1 hst hw.1 x hfin
        have hws : 0 < w - s := by linarith [hw.1]
        have hw0 := abs_le.mp (hbar w hw1).2.2
        have hs0 := abs_le.mp (hbar s hs).2.2
        have h' : (w - s) * (finiteGeodesic θ u₀ u₁ t x).toReal ≤
            (w - t) * (finiteGeodesic θ u₀ u₁ s x).toReal + (t - s) * (finiteGeodesic θ u₀ u₁ w x).toReal := by
          have e1 : 1 - (t - s) / (w - s) = (w - t) / (w - s) := by field_simp; ring
          rw [e1] at h
          have h2 := mul_le_mul_of_nonneg_left h hws.le
          have e2 : (w - s) * ((w - t) / (w - s) * (finiteGeodesic θ u₀ u₁ s x).toReal +
              (t - s) / (w - s) * (finiteGeodesic θ u₀ u₁ w x).toReal) =
              (w - t) * (finiteGeodesic θ u₀ u₁ s x).toReal + (t - s) * (finiteGeodesic θ u₀ u₁ w x).toReal := by field_simp
          linarith
        rw [le_div_iff₀ hws]
        have h3 : (t - s) * ((finiteGeodesic θ u₀ u₁ w x).toReal - (finiteGeodesic θ u₀ u₁ s x).toReal) ≤ (t - s) * (C * (2 - w - s)) :=
          mul_le_mul_of_nonneg_left (by linarith [hw0.2, hs0.1]) (sub_nonneg.mpr hst.le)
        nlinarith
      have htend : Tendsto (fun w => C * (t - s) * (2 - w - s) / (w - s)) (𝓝[<] (1 : ℝ))
          (𝓝 (C * (t - s))) := by
        have hs1 : (1 : ℝ) - s ≠ 0 := sub_ne_zero.mpr hs.2.ne'
        have hc : ContinuousAt (fun w : ℝ => C * (t - s) * (2 - w - s) / (w - s)) 1 :=
          ((continuous_const.mul ((continuous_const.sub continuous_id).sub
            continuous_const)).continuousAt).div
            (continuous_id.sub continuous_const).continuousAt hs1
        have h1 : C * (t - s) * (2 - 1 - s) / (1 - s) = C * (t - s) := by
          rw [show (2 : ℝ) - 1 - s = 1 - s by ring, mul_div_assoc, div_self hs1, mul_one]
        have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
        rwa [h1] at h
      exact ge_of_tendsto htend (by
        filter_upwards [Ioo_mem_nhdsLT ht.2] with w hw using hup w hw)
  rcases lt_trichotomy s t with hst | rfl | hts
  · rw [abs_of_pos (sub_pos.mpr hst)]
    exact key s t hs ht hst
  · simp
  · rw [abs_sub_comm, abs_of_neg (sub_neg.mpr hts), neg_sub]
    exact key t s ht hs hts

end Barriers

/-! ### Maximality for bounded endpoints -/

section Maximality

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **The complexified bounded geodesic solves the homogeneous complex Monge--Ampère equation**
on every strip witness: `FiniteGeodesicMaximality.isBTLimit_modelStripOpens_eq_zero_finiteGeodesic`
with the bound on the slices discharged for bounded endpoints. -/
theorem isBTLimit_modelStripOpens_eq_zero_finiteGeodesic_of_bounded {θ : SmoothRealForm n M 2}
    {u₀ u₁ : M → EReal} (hsub : IsSubgeodesicFrom θ (finiteGeodesic θ u₀ u₁) u₀ u₁)
    (hb₀ : IsBoundedPotential u₀) (hb₁ : IsBoundedPotential u₁)
    (e : ComplexChart n M) {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ e W ρ)
    (hpsh : PlurisubharmonicOn (subgeodesicChartFunction (finiteGeodesic θ u₀ u₁) e ρ)
      (geodesicChartDomain W))
    {μ : Measure (ComplexModel (n + 1))}
    (hμ : IsBTLimit (modelStripOpens W hρ.1)
      (fun _ => modelChartFunction (finiteGeodesic θ u₀ u₁) e ρ) μ) :
    μ = 0 := by
  obtain ⟨A, B, hbd⟩ := finiteGeodesic_uniformly_bounded hsub hb₀ hb₁
  exact isBTLimit_modelStripOpens_eq_zero_finiteGeodesic hsub hbd e hρ hpsh hμ

/-- **Maximality near every point.** For bounded endpoints whose Perron geodesic is a subgeodesic
between them, every point of every chart has a strip witness `(W, ρ)` of the geodesic on which
every Bedford--Taylor limit of `(h, …, h)` (`n + 1` copies of the corrected complexification) is
zero. -/
theorem exists_isBTLimit_eq_zero_finiteGeodesic_of_bounded {θ : SmoothRealForm n M 2}
    {u₀ u₁ : M → EReal} (hsub : IsSubgeodesicFrom θ (finiteGeodesic θ u₀ u₁) u₀ u₁)
    (hb₀ : IsBoundedPotential u₀) (hb₁ : IsBoundedPotential u₁)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    ∃ (W : Set (ComplexModel n)) (ρ : ComplexModel n → ℝ) (hρ : IsSmoothLocalPotential θ e W ρ),
      z ∈ W ∧
      PlurisubharmonicOn (subgeodesicChartFunction (finiteGeodesic θ u₀ u₁) e ρ)
        (geodesicChartDomain W) ∧
      ∀ μ : Measure (ComplexModel (n + 1)), IsBTLimit (modelStripOpens W hρ.1)
        (fun _ => modelChartFunction (finiteGeodesic θ u₀ u₁) e ρ) μ → μ = 0 := by
  obtain ⟨W, ρ, hzW, hρ, hpsh⟩ := hsub.2.2.1.2 e z hz
  exact ⟨W, ρ, hρ, hzW, hpsh, fun μ hμ =>
    isBTLimit_modelStripOpens_eq_zero_finiteGeodesic_of_bounded hsub hb₀ hb₁ e hρ hpsh hμ⟩

end Maximality

/-! ### The energy along a bounded geodesic -/

section Energy

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] in
theorem isBoundedPotential_sub_const {u : M → EReal} (hu : IsBoundedPotential u) (c : ℝ) :
    IsBoundedPotential fun x => u x - (c : EReal) := by
  obtain ⟨a, b, h⟩ := hu
  refine ⟨a - c, b - c, fun x => ⟨?_, ?_⟩⟩
  · rw [EReal.coe_sub]
    exact EReal.sub_le_sub (h x).1 le_rfl
  · rw [EReal.coe_sub]
    exact EReal.sub_le_sub (h x).2 le_rfl

/-- **The energy is Lipschitz in the sup norm** (Xia, Lemma 3.1.3 and (3.31)): for bounded
`θ`-PSH `u`, `v` and a bounded model `φ`, `|E^φ(u) - E^φ(v)| ≤ sup |u - v| · ∫ θ_φ^n`. -/
theorem abs_relativeEnergyOfMinimalType_sub_le (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u v : M → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hφb : IsBoundedPotential φ) (hub : IsBoundedPotential u) (hvb : IsBoundedPotential v)
    {c : ℝ} (hc : ∀ x, |(u x).toReal - (v x).toReal| ≤ c) :
    |relativeEnergyOfMinimalType θ φ u hφ hu - relativeEnergyOfMinimalType θ φ v hφ hv| ≤
      c * (globalMixedMeasure (fun _ => θ) (fun _ => φ) (fun _ => hφ.1)).real univ := by
  have hv₁ := hv.sub_const c
  have hv₂ := hv.sub_const (-c)
  have hcoe : ∀ x, u x = ((u x).toReal : EReal) ∧ v x = ((v x).toReal : EReal) := fun x =>
    ⟨(EReal.coe_toReal (hub.ne_top x) (hub.ne_bot x)).symm,
      (EReal.coe_toReal (hvb.ne_top x) (hvb.ne_bot x)).symm⟩
  have hle₁ : (fun x => v x - (c : EReal)) ≤ u := fun x => by
    show v x - (c : EReal) ≤ u x
    rw [(hcoe x).1, (hcoe x).2, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    have := abs_le.mp (hc x)
    linarith
  have hle₂ : u ≤ fun x => v x - ((-c : ℝ) : EReal) := fun x => by
    show u x ≤ v x - ((-c : ℝ) : EReal)
    rw [(hcoe x).1, (hcoe x).2, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    have := abs_le.mp (hc x)
    linarith
  have h1 := relativeEnergyOfMinimalType_mono omega θ hφ hv₁ hu hφb
    (isBoundedPotential_sub_const hvb c) hub hle₁
  rw [relativeEnergyOfMinimalType_sub_const omega θ hφ hv hφb hvb c hv₁] at h1
  have h2 := relativeEnergyOfMinimalType_mono omega θ hφ hu hv₂ hφb hub
    (isBoundedPotential_sub_const hvb (-c)) hle₂
  rw [relativeEnergyOfMinimalType_sub_const omega θ hφ hv hφb hvb (-c) hv₂] at h2
  rw [abs_le]
  constructor <;> linarith

theorem isBoundedPotential_finiteGeodesic {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (hsub : IsSubgeodesicFrom θ (finiteGeodesic θ u₀ u₁) u₀ u₁)
    (hb₀ : IsBoundedPotential u₀) (hb₁ : IsBoundedPotential u₁) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : IsBoundedPotential (finiteGeodesic θ u₀ u₁ t) := by
  obtain ⟨A, B, hbd⟩ := finiteGeodesic_uniformly_bounded hsub hb₀ hb₁
  exact ⟨A, B, hbd t ht⟩

/-- **The energy is `C vol`-Lipschitz along a bounded geodesic** (Xia, proof of Proposition 4.3.3,
Step 1: "the local Lipschitz continuity of `t ↦ E(φ_t)`"; here on all of `(0, 1)`). -/
theorem abs_energy_finiteGeodesic_sub_le (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u₀ u₁ : M → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hφb : IsBoundedPotential φ)
    (hsub : IsSubgeodesicFrom θ.val (finiteGeodesic θ.val u₀ u₁) u₀ u₁)
    (hb₀ : IsBoundedPotential u₀) (hb₁ : IsBoundedPotential u₁) {C : ℝ}
    (hC₁ : ∀ x, u₁ x ≤ u₀ x + (C : EReal)) (hC₀ : ∀ x, u₀ x ≤ u₁ x + (C : EReal))
    {s t : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hUs : IsThetaPshPotential θ.val (finiteGeodesic θ.val u₀ u₁ s))
    (hUt : IsThetaPshPotential θ.val (finiteGeodesic θ.val u₀ u₁ t)) :
    |relativeEnergyOfMinimalType θ φ _ hφ hUt - relativeEnergyOfMinimalType θ φ _ hφ hUs| ≤
      C * |t - s| * (globalMixedMeasure (fun _ => θ) (fun _ => φ) (fun _ => hφ.1)).real univ :=
  abs_relativeEnergyOfMinimalType_sub_le omega θ hφ hUt hUs hφb
    (isBoundedPotential_finiteGeodesic hsub hb₀ hb₁ ht)
    (isBoundedPotential_finiteGeodesic hsub hb₀ hb₁ hs)
    fun x => abs_finiteGeodesic_toReal_sub_le hsub hb₀ hb₁ hC₁ hC₀ hs ht x

/-- **Continuity of the energy at `t = 0`** (Xia, proof of Proposition 4.3.3, end of Step 2):
`|E(U_t) - E(u₀)| ≤ C t vol`. -/
theorem abs_energy_finiteGeodesic_sub_left_le (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u₀ u₁ : M → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hφb : IsBoundedPotential φ)
    (hsub : IsSubgeodesicFrom θ.val (finiteGeodesic θ.val u₀ u₁) u₀ u₁)
    (hb₀ : IsBoundedPotential u₀) (hb₁ : IsBoundedPotential u₁) {C : ℝ}
    (hC₁ : ∀ x, u₁ x ≤ u₀ x + (C : EReal)) (hC₀ : ∀ x, u₀ x ≤ u₁ x + (C : EReal))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hUt : IsThetaPshPotential θ.val (finiteGeodesic θ.val u₀ u₁ t)) :
    |relativeEnergyOfMinimalType θ φ _ hφ hUt - relativeEnergyOfMinimalType θ φ u₀ hφ hsub.1| ≤
      C * t * (globalMixedMeasure (fun _ => θ) (fun _ => φ) (fun _ => hφ.1)).real univ :=
  abs_relativeEnergyOfMinimalType_sub_le omega θ hφ hUt hsub.1 hφb
    (isBoundedPotential_finiteGeodesic hsub hb₀ hb₁ ht) hb₀
    fun x => (finiteGeodesic_barriers hsub hb₀ hb₁ hC₁ hC₀ ht x).2.1

/-- **Continuity of the energy at `t = 1`**: `|E(U_t) - E(u₁)| ≤ C (1 - t) vol`. -/
theorem abs_energy_finiteGeodesic_sub_right_le (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u₀ u₁ : M → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hφb : IsBoundedPotential φ)
    (hsub : IsSubgeodesicFrom θ.val (finiteGeodesic θ.val u₀ u₁) u₀ u₁)
    (hb₀ : IsBoundedPotential u₀) (hb₁ : IsBoundedPotential u₁) {C : ℝ}
    (hC₁ : ∀ x, u₁ x ≤ u₀ x + (C : EReal)) (hC₀ : ∀ x, u₀ x ≤ u₁ x + (C : EReal))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hUt : IsThetaPshPotential θ.val (finiteGeodesic θ.val u₀ u₁ t)) :
    |relativeEnergyOfMinimalType θ φ _ hφ hUt - relativeEnergyOfMinimalType θ φ u₁ hφ hsub.2.1| ≤
      C * (1 - t) * (globalMixedMeasure (fun _ => θ) (fun _ => φ) (fun _ => hφ.1)).real univ :=
  abs_relativeEnergyOfMinimalType_sub_le omega θ hφ hUt hsub.2.1 hφb
    (isBoundedPotential_finiteGeodesic hsub hb₀ hb₁ ht) hb₁
    fun x => (finiteGeodesic_barriers hsub hb₀ hb₁ hC₁ hC₀ ht x).2.2

/-! ### Endpoints of bounded singularity type relative to a bounded model potential -/

variable [ConnectedSpace M]

/-- For endpoints in `E^∞(X, θ; φ)` with `φ` a bounded model potential, the Perron geodesic is a
subgeodesic between bounded endpoints (`trace:finite-geodesic-einfinity`), so all of the above
applies; in particular the complexified geodesic is maximal near every point. -/
theorem exists_isBTLimit_eq_zero_finiteGeodesic_of_relativeEInfinity
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) {φ u₀ u₁ : M → EReal}
    (hφ : IsModelPotential θ φ) (hφb : IsBoundedPotential φ)
    (hu₀ : RelativeEInfinity θ φ u₀) (hu₁ : RelativeEInfinity θ φ u₁)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    IsSubgeodesicFrom θ.val (finiteGeodesic θ.val u₀ u₁) u₀ u₁ ∧
      IsBoundedPotential u₀ ∧ IsBoundedPotential u₁ ∧
      ∃ (W : Set (ComplexModel n)) (ρ : ComplexModel n → ℝ)
        (hρ : IsSmoothLocalPotential θ.val e W ρ),
        z ∈ W ∧
        PlurisubharmonicOn (subgeodesicChartFunction (finiteGeodesic θ.val u₀ u₁) e ρ)
          (geodesicChartDomain W) ∧
        ∀ μ : Measure (ComplexModel (n + 1)), IsBTLimit (modelStripOpens W hρ.1)
          (fun _ => modelChartFunction (finiteGeodesic θ.val u₀ u₁) e ρ) μ → μ = 0 := by
  have hsub := FiniteGeodesicsFullMassAnyDim.finiteGeodesic_isSubgeodesicFrom_of_relativeEInfinity
    omega θ φ u₀ u₁ hφ hu₀ hu₁
  have hb₀ := isBoundedPotential_of_sameSingularityType hφb hu₀.2
  have hb₁ := isBoundedPotential_of_sameSingularityType hφb hu₁.2
  exact ⟨hsub, hb₀, hb₁, exists_isBTLimit_eq_zero_finiteGeodesic_of_bounded hsub hb₀ hb₁ e hz⟩

end Energy

end

end SGPT.Foundations.Analysis.Pending.FiniteGeodesicEnergyEndpoints
