import SGPT.TestCurve.RWNTwistedCorrespondence

/-!
# The normalization of twisted test curves (`rmk:testcurve:L815`, snapshot `c88c7ff4`)

Source `rmk:testcurve:L815` (chapter *Test curves*, `author/chapter_testcurve.tex:809–821` of
`c88c7ff4`; ERRATA I05/I09, corrected upstream). After the bijection between geodesic rays
emanating from `Φ ∈ 𝓔(X, θ; φ)` and `Φ`-twisted test curves, the remark now says:

> For `t > 0`, the normalization in `lma:suplegenlinear` becomes
> `sup_{Φ > -∞} (Γ*_t - Φ) = tΓ_max`.
> Indeed, `Γ_τ ≤ Φ` for every `τ < Γ_max`, and `sup_{Φ > -∞} (Γ_τ - Φ) = 0` for each such `τ`
> by the envelope condition above. Taking the supremum in the Legendre formula gives the identity.

The two-sided bound behind the identity is `SGPT.TestCurve.RWNTwisted.twistedLegendre_supremum_whole`
(`Γ*_t ≤ Φ + tΓ_max`, and `Φ(x) + c < Γ*_t(x)` somewhere for every `c < tΓ_max`). This file
states the remark's identities literally, as suprema over `{Φ > -∞}` in `EReal`:

* `twistedPotential_iSup_sub_eq_zero`: `sup_{Φ > -∞} (Γ_τ - Φ) = 0` for every `τ < Γ_max`
  (with `Γ_τ ≤ Φ`, `SourceTwistedTestCurve.potential_le_limit`);
* `twistedLegendreRay_iSup_sub_eq`: `sup_{Φ > -∞} (Γ*_t - Φ) = tΓ_max` for every `t > 0`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.TestCurve.RWNTwisted

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas
open SGPT.TestCurve.TestConf

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {Φ : M → EReal}

/-- **`rmk:testcurve:L815`, the envelope step**: for a `Φ`-twisted test curve and every
`τ < Γ_max`, `sup_{Φ > -∞} (Γ_τ - Φ) = 0`. -/
theorem twistedPotential_iSup_sub_eq_zero (Γ : SourceTwistedTestCurve θ Φ) (τ : Iio Γ.max) :
    ⨆ x : {x : M // Φ x ≠ ⊥}, (Γ.potential τ x - Φ x) = 0 := by
  apply le_antisymm
  · refine iSup_le fun x => EReal.sub_le_of_le_add' ?_
    rw [add_zero]
    exact Γ.potential_le_limit τ x
  · refine EReal.ge_of_forall_gt_iff_ge.mp fun z hz => ?_
    have hz0 : z < 0 := by exact_mod_cast hz
    obtain ⟨x, hx⟩ := twisted_exists_close Γ τ (neg_pos.mpr hz0)
    rw [neg_neg] at hx
    have hle := Γ.potential_le_limit τ x
    have hΦ : Φ x ≠ ⊥ := by
      intro h
      rw [h, EReal.bot_add] at hx
      rw [h] at hle
      exact lt_irrefl _ (hx.trans_le hle)
    refine le_iSup_of_le (⟨x, hΦ⟩ : {x : M // Φ x ≠ ⊥}) ?_
    exact ((EReal.lt_sub_iff_add_lt (.inr (EReal.coe_ne_top z)) (.inr (EReal.coe_ne_bot z))).mpr
      (by rwa [add_comm])).le

/-- **`rmk:testcurve:L815`, the twisted normalization**: for a `Φ`-twisted test curve and every
`t > 0`, `sup_{Φ > -∞} (Γ*_t - Φ) = tΓ_max`. -/
theorem twistedLegendreRay_iSup_sub_eq (Γ : SourceTwistedTestCurve θ Φ) {t : ℝ} (ht : 0 < t) :
    ⨆ x : {x : M // Φ x ≠ ⊥}, (twistedLegendreRay Γ ⟨t, ht.le⟩ x - Φ x) =
      ((t * Γ.max : ℝ) : EReal) := by
  obtain ⟨hup, hclose, -⟩ := twistedLegendre_supremum_whole Γ
  have hray : twistedLegendreRay Γ ⟨t, ht.le⟩ = twistedRawLegendre Γ t :=
    twistedLegendreRay_pos Γ (t := ⟨t, ht.le⟩) ht.ne'
  apply le_antisymm
  · exact iSup_le fun x => EReal.sub_le_of_le_add' (hup ⟨t, ht.le⟩ x)
  · refine EReal.ge_of_forall_gt_iff_ge.mp fun c hc => ?_
    have hc' : c < t * Γ.max := by exact_mod_cast hc
    obtain ⟨x, hx⟩ := hclose t ht c hc'
    rw [← hray] at hx
    have hle := hup ⟨t, ht.le⟩ x
    have hΦ : Φ x ≠ ⊥ := by
      intro h
      rw [h, EReal.bot_add] at hx hle
      exact lt_irrefl _ (hx.trans_le hle)
    refine le_iSup_of_le (⟨x, hΦ⟩ : {x : M // Φ x ≠ ⊥}) ?_
    exact ((EReal.lt_sub_iff_add_lt (.inr (EReal.coe_ne_top c)) (.inr (EReal.coe_ne_bot c))).mpr
      (by rwa [add_comm])).le

end SGPT.TestCurve.RWNTwisted

end
