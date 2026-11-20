import SGPT.TestCurve.RWNTwistedRayToCurve

/-!
# From `Φ`-twisted test curves to geodesic rays emanating from `Φ`

Source `rmk:testcurve:L815` (chapter *Test curves*): the twisted versions of `prop:Leginvtc`,
`lma:testcurvelegusc`, `cor:GammastarP`, `lma:suplegenlinear` and `lma:LegsendsTCtoR`, for a
`Φ`-twisted test curve `Γ` with `Φ ∈ 𝓔(X, θ; φ)`.

* `SourceTwistedTestCurve.potential_eq_iInf_earlier`: `Γ_τ = inf_{σ < τ} Γ_σ` (`eq:Gammataucont`).
* `twistedLegendre_inverse_whole` (twisted `prop:Leginvtc`): `Γ_τ = inf_{t > 0} (Γ*_t - tτ)`
  for every `τ ∈ ℝ`, with the extension of `rmk:extendtestcur`.
* `twistedLegendreRay_isSubgeodesic`, `twistedLegendre_joint_upperSemicontinuous` (twisted
  `lma:testcurvelegusc`): `Γ*` is a subgeodesic ray, jointly upper semicontinuous on
  `X × (0, ∞)`; the raw supremum needs no regularization (`upperSemicontinuous_iSup_affine`).
* `twistedLegendre_fullMass` (twisted `cor:GammastarP`): `Γ*_t ∈ 𝓔(X, θ; φ)`.
* `twistedLegendre_supremum_whole` (twisted `lma:suplegenlinear`): `Γ*_t ≤ Φ + tΓ_max`, the bound
  is sharp (`sup_{Φ > -∞} (Γ*_t - Φ) = tΓ_max`), and `t ↦ Γ*_t - tΓ_max` decreases. The untwisted
  clause `sup_X Γ*_t = tΓ_max` does **not** hold in the twisted setting (it fails for the
  constant curve `Γ_τ = Φ` whenever `sup_X Φ ≠ 0`, see `twistedConstCurve_sup`).
* `twistedLegendreRay_mem` (twisted `lma:LegsendsTCtoR`): `Γ* ∈ 𝓡(X, θ; φ)` emanating from `Φ`.

Differences with the untwisted proofs. The untwisted proofs use the normalisation `Γ_τ ≤ 0`; for
twisted curves only `Γ_τ ≤ Φ` holds. Hence: the noncollapse of `inf_{σ < τ} Γ_σ` is obtained
from the lower bound `Γ_τ` instead of the normalisation; `Γ*_t ∈ 𝓔(X, θ; φ)` is proved from
`Γ_τ + tτ ≤ Γ*_t ≤ Φ + tΓ_max` and the continuity of masses along `τ → -∞`; and in the proof of
`lma:LegsendsTCtoR` the replacement potentials `Γ'_τ` are compared with `Φ` (through
`Γ'_τ ≤ ℓ_0 = Φ`) instead of `0`, and the twisted fixed point `P_θ[Γ_τ](Φ) = Γ_τ` replaces the
model property. The monotonicity of `t ↦ Γ*_t - tΓ_max` holds pointwise without normalisation.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.TestCurve.RWNTwisted

open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas
open SGPT.TestCurve.TestConf

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {Φ : M → EReal}

/-- The raw Legendre transform `Γ*_t = sup_{τ < Γ_max} (tτ + Γ_τ)` of a twisted test curve. -/
def twistedRawLegendre (Γ : SourceTwistedTestCurve θ Φ) (t : ℝ) (x : M) : EReal :=
  ⨆ σ : Iio Γ.max, ((t * σ.1 : ℝ) : EReal) + Γ.potential σ x

theorem twistedLegendreRay_pos (Γ : SourceTwistedTestCurve θ Φ) {t : Ici (0 : ℝ)}
    (ht : t.1 ≠ 0) : twistedLegendreRay Γ t = twistedRawLegendre Γ t.1 := by
  funext x
  simp only [twistedLegendreRay, if_neg ht, twistedRawLegendre]

theorem twistedLegendreRay_zero (Γ : SourceTwistedTestCurve θ Φ) :
    twistedLegendreRay Γ ⟨0, by simp⟩ = Φ := by
  funext x
  simp [twistedLegendreRay]

theorem twistedLegendre_extension_pos (Γ : SourceTwistedTestCurve θ Φ) {t : ℝ} (ht : 0 < t) :
    sourceRayExtension (twistedLegendreRay Γ) t = twistedRawLegendre Γ t := by
  rw [sourceRayExtension_nonneg _ t ht.le]
  exact twistedLegendreRay_pos Γ (t := ⟨t, ht.le⟩) ht.ne'

theorem twistedLegendre_extension_zero (Γ : SourceTwistedTestCurve θ Φ) :
    sourceRayExtension (twistedLegendreRay Γ) 0 = Φ := by
  rw [sourceRayExtension_nonneg _ 0 le_rfl]
  exact twistedLegendreRay_zero Γ

/-- `Γ_σ + tσ ≤ Γ*_t`. -/
theorem le_twistedRawLegendre (Γ : SourceTwistedTestCurve θ Φ) (t : ℝ) (σ : Iio Γ.max) (x : M) :
    ((t * σ.1 : ℝ) : EReal) + Γ.potential σ x ≤ twistedRawLegendre Γ t x :=
  le_iSup (fun σ : Iio Γ.max ↦ ((t * σ.1 : ℝ) : EReal) + Γ.potential σ x) σ

/-- `Γ*_t ≤ Φ + tΓ_max` for `t ≥ 0`. -/
theorem twistedRawLegendre_le (Γ : SourceTwistedTestCurve θ Φ) {t : ℝ} (ht : 0 ≤ t) (x : M) :
    twistedRawLegendre Γ t x ≤ Φ x + ((t * Γ.max : ℝ) : EReal) := by
  apply iSup_le
  intro σ
  rw [add_comm]
  exact add_le_add (Γ.potential_le_limit σ x)
    (EReal.coe_le_coe (mul_le_mul_of_nonneg_left (le_of_lt σ.2) ht))

/-- The assigned ray has the linear bound `Γ*_t ≤ C + tΓ_max` when `Φ ≤ C`. -/
theorem twistedLegendreRay_le_linear (Γ : SourceTwistedTestCurve θ Φ) {C : ℝ}
    (hC : ∀ x, Φ x ≤ C) (t : Ici (0 : ℝ)) (x : M) :
    twistedLegendreRay Γ t x ≤ ((C + t.1 * Γ.max : ℝ) : EReal) := by
  by_cases ht : t.1 = 0
  · simp only [twistedLegendreRay, if_pos ht]
    rw [ht, zero_mul, add_zero]
    exact hC x
  · rw [twistedLegendreRay_pos Γ ht]
    refine (twistedRawLegendre_le Γ t.2 x).trans ?_
    rw [EReal.coe_add]
    exact add_le_add (hC x) le_rfl

/-- Pointwise monotonicity `Γ*_b ≤ Γ*_s + (b - s)Γ_max` for `s ≤ b` (twisted
`lma:suplegenlinear`, second clause; no normalisation is needed). -/
theorem twistedRawLegendre_le_add (Γ : SourceTwistedTestCurve θ Φ) {s b : ℝ} (hsb : s ≤ b)
    (x : M) : twistedRawLegendre Γ b x ≤
      twistedRawLegendre Γ s x + (((b - s) * Γ.max : ℝ) : EReal) := by
  apply iSup_le
  intro σ
  calc ((b * σ.1 : ℝ) : EReal) + Γ.potential σ x
      = (((s * σ.1 : ℝ) : EReal) + Γ.potential σ x) + (((b - s) * σ.1 : ℝ) : EReal) := by
        rw [add_comm (((s * σ.1 : ℝ) : EReal)), add_assoc, ← EReal.coe_add, add_comm]
        congr 2
        ring
    _ ≤ twistedRawLegendre Γ s x + (((b - s) * Γ.max : ℝ) : EReal) :=
        add_le_add (le_twistedRawLegendre Γ s σ x)
          (EReal.coe_le_coe (mul_le_mul_of_nonneg_left (le_of_lt σ.2) (sub_nonneg.mpr hsb)))

/-! ### Left continuity in `τ` (`eq:Gammataucont`) -/

/-- Pointwise left continuity of a concave decreasing family at a point where it is finite a
bit beyond `τ`. -/
theorem iInf_earlier_le_of_finite {X : Type*} {m : ℝ} {family : Iio m → X → EReal} {x : X}
    (hanti : Antitone (fun τ ↦ family τ x))
    (hconc : SGPT.Convex.IsConvex (sourceTestCurveNegativeTrace m family x))
    (htop : ∀ σ, family σ x ≠ ⊤) (τ b : Iio m) (hτb : τ.1 < b.1) (hb : family b x ≠ ⊥) :
    ⨅ σ : Iio τ.1, family ⟨σ.1, lt_trans (show σ.1 < τ.1 from σ.2) (show τ.1 < m from τ.2)⟩ x ≤
      family τ x := by
  have hbτ : family b x ≤ family τ x := hanti (show τ ≤ b from hτb.le)
  have hτbot : family τ x ≠ ⊥ := ne_bot_of_le_ne_bot hb hbτ
  obtain ⟨yb, hyb⟩ : ∃ y : ℝ, family b x = (y : EReal) :=
    ⟨(family b x).toReal, (EReal.coe_toReal (htop b) hb).symm⟩
  obtain ⟨yτ, hyτ⟩ : ∃ y : ℝ, family τ x = (y : EReal) :=
    ⟨(family τ x).toReal, (EReal.coe_toReal (htop τ) hτbot).symm⟩
  have hybτ : yb ≤ yτ := by
    rw [hyb, hyτ] at hbτ
    exact EReal.coe_le_coe_iff.mp hbτ
  apply EReal.le_of_forall_lt_iff_le.mp
  intro z hz
  rw [hyτ] at hz
  have hz' : yτ < z := EReal.coe_lt_coe_iff.mp hz
  have hbτ' : 0 < b.1 - τ.1 := sub_pos.mpr hτb
  have hden : 0 < yτ - yb + 1 := by linarith
  let δ : ℝ := min 1 ((z - yτ) * (b.1 - τ.1) / (yτ - yb + 1))
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos (mul_pos (by linarith) hbτ') hden)
  have hδle : δ * (yτ - yb + 1) ≤ (z - yτ) * (b.1 - τ.1) :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  let σ' : Iio m := ⟨τ.1 - δ, by
    change τ.1 - δ < m
    have : τ.1 < m := τ.2
    linarith⟩
  have hσ'τ : σ'.1 < τ.1 := by change τ.1 - δ < τ.1; linarith
  have hσ'bot : family σ' x ≠ ⊥ := ne_bot_of_le_ne_bot hτbot (hanti (show σ' ≤ τ from hσ'τ.le))
  obtain ⟨yσ, hyσ⟩ : ∃ y : ℝ, family σ' x = (y : EReal) :=
    ⟨(family σ' x).toReal, (EReal.coe_toReal (htop σ') hσ'bot).symm⟩
  have h3 := concave_three_point hconc hσ'τ hτb hyσ.ge hyb.ge hyτ.le
  have hτσ : τ.1 - σ'.1 = δ := by change τ.1 - (τ.1 - δ) = δ; ring
  have hbσ : b.1 - σ'.1 = b.1 - τ.1 + δ := by change b.1 - (τ.1 - δ) = b.1 - τ.1 + δ; ring
  rw [hτσ, hbσ] at h3
  have hyσz : yσ < z := by
    have h4 : (b.1 - τ.1) * (yσ - yτ) ≤ δ * (yτ - yb) := by nlinarith
    have h5 : δ * (yτ - yb) < δ * (yτ - yb + 1) := by nlinarith
    have h6 : (b.1 - τ.1) * (yσ - yτ) < (b.1 - τ.1) * (z - yτ) := by nlinarith
    have h7 := lt_of_mul_lt_mul_left h6 hbτ'.le
    linarith
  calc ⨅ σ : Iio τ.1, family ⟨σ.1, lt_trans (show σ.1 < τ.1 from σ.2)
        (show τ.1 < m from τ.2)⟩ x
      ≤ family σ' x := iInf_le (fun σ : Iio τ.1 ↦ family ⟨σ.1, lt_trans
          (show σ.1 < τ.1 from σ.2) (show τ.1 < m from τ.2)⟩ x) ⟨σ'.1, hσ'τ⟩
    _ = (yσ : EReal) := hyσ
    _ ≤ (z : EReal) := EReal.coe_le_coe hyσz.le

variable [CompactSpace M] [ConnectedSpace M]

/-- **Left continuity** (`eq:Gammataucont`) of a twisted test curve: `Γ_τ = inf_{σ < τ} Γ_σ`
everywhere. -/
theorem twistedPotential_eq_iInf_earlier (Γ : SourceTwistedTestCurve θ Φ)
    (τ : Iio Γ.max) :
    (fun x ↦ ⨅ σ : Iio τ.1, Γ.potential ⟨σ.1, lt_trans (show σ.1 < τ.1 from σ.2)
      (show τ.1 < Γ.max from τ.2)⟩ x) = Γ.potential τ := by
  let u : Iio τ.1 → M → EReal := fun σ ↦ Γ.potential ⟨σ.1, lt_trans (show σ.1 < τ.1 from σ.2)
    (show τ.1 < Γ.max from τ.2)⟩
  have hu (σ : Iio τ.1) : IsThetaPshPotential (atlasClosedFormToNative θ).val (u σ) :=
    (isThetaPSH_iff_nativeThetaPotential θ _).mp (Γ.thetaPSH _)
  have hanti (x : M) : Antitone (fun σ ↦ u σ x) := fun σ σ' h ↦ Γ.antitone x
    (show (⟨σ.1, _⟩ : Iio Γ.max) ≤ ⟨σ'.1, _⟩ from h)
  have hτu (σ : Iio τ.1) : Γ.potential τ ≤ u σ := fun x ↦ Γ.antitone x
    (show (⟨σ.1, _⟩ : Iio Γ.max) ≤ τ from le_of_lt σ.2)
  obtain ⟨x₀, hx₀⟩ := thetaPSH_exists_ne_bot (Γ.thetaPSH τ)
  obtain ⟨a, -, ha⟩ := EReal.exists_between_coe_real (bot_lt_iff_ne_bot.mpr hx₀)
  have hlow (σ : Iio τ.1) : (a : EReal) ≤ ⨆ x, u σ x :=
    ha.le.trans ((hτu σ x₀).trans (le_iSup (fun x ↦ u σ x) x₀))
  have : Nonempty (Iio τ.1) := ⟨⟨τ.1 - 1, by change τ.1 - 1 < τ.1; linarith⟩⟩
  have hinf := (SGPT.PSH.isThetaPshPotential_iInf_of_compact_antitone_iSup_lower_bound
    hu hanti a hlow).1
  have hinf' : (ofFixedModel n M).IsThetaPSH θ (fun x ↦ ⨅ σ, u σ x) :=
    (isThetaPSH_iff_nativeThetaPotential θ _).mpr hinf
  apply le_antisymm
  · apply (sourceQuasiEverywhere_le_iff hinf' (Γ.thetaPSH τ)).mp
    apply (sourceQuasiEverywhere_iff_native _).mpr
    let b : Iio Γ.max := ⟨(τ.1 + Γ.max) / 2, by
      change (τ.1 + Γ.max) / 2 < Γ.max
      have : τ.1 < Γ.max := τ.2
      linarith⟩
    have hτb : τ.1 < b.1 := by
      change τ.1 < (τ.1 + Γ.max) / 2
      have : τ.1 < Γ.max := τ.2
      linarith
    apply (quasiPsh_finite_quasiEverywhere ((isThetaPSH_iff_nativeThetaPotential θ _).mp
      (Γ.thetaPSH b)).quasiPshPotential).mono
    intro x hx
    exact iInf_earlier_le_of_finite (Γ.antitone x) (Γ.concave x)
      (fun σ ↦ thetaPSH_ne_top (Γ.thetaPSH σ) x) τ b hτb hx.1
  · intro x
    exact le_iInf fun σ ↦ hτu σ x

/-- Left continuity in the form used by the Legendre inversion. -/
theorem twisted_exists_earlier_lt (Γ : SourceTwistedTestCurve θ Φ) (x : M)
    (τ : Iio Γ.max) (r : ℝ) (hr : Γ.potential τ x < r) :
    ∃ σ : Iio Γ.max, σ.1 < τ.1 ∧ Γ.potential σ x < r := by
  rw [← congrFun (twistedPotential_eq_iInf_earlier Γ τ) x] at hr
  obtain ⟨σ, hσ⟩ := iInf_lt_iff.mp hr
  exact ⟨_, (show σ.1 < τ.1 from σ.2), hσ⟩

/-! ### Legendre inversion (twisted `prop:Leginvtc`) -/

/-- Inversion below the cut-off: `Γ_τ = inf_{t > 0} (Γ*_t - tτ)` for `τ < Γ_max`. -/
theorem twistedInverse_eq (hΦ : (ofFixedModel n M).IsThetaPSH θ Φ)
    (Γ : SourceTwistedTestCurve θ Φ) (τ : Iio Γ.max) :
    sourcePositiveRayInverse (twistedLegendreRay Γ) τ.1 = Γ.potential τ := by
  obtain ⟨C, hC⟩ := thetaPSH_exists_upper hΦ
  funext x
  have hrw : sourcePositiveRayInverse (twistedLegendreRay Γ) τ.1 x =
      ⨅ t : Ioi (0 : ℝ), (⨆ σ : Iio Γ.max, ((t.1 * σ.1 : ℝ) : EReal) + Γ.potential σ x) -
        ((t.1 * τ.1 : ℝ) : EReal) := by
    unfold sourcePositiveRayInverse
    apply iInf_congr
    intro t
    rw [twistedLegendre_extension_pos Γ t.2]
    rfl
  apply le_antisymm
  · rw [hrw]
    exact legendre_inverse_le (Γ.antitone x) (Γ.concave x) (twisted_exists_earlier_lt Γ x) (c := C)
      (fun σ ↦ (Γ.potential_le_limit σ x).trans (hC x)) τ
  · apply le_iInf
    intro t
    rw [twistedLegendre_extension_pos Γ t.2]
    apply (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))).mpr
    rw [add_comm]
    exact le_twistedRawLegendre Γ t.1 τ x

/-- Inversion above the cut-off: the inverse transform is `-∞` for `τ > Γ_max`. -/
theorem twistedInverse_eq_bot (hΦ : (ofFixedModel n M).IsThetaPSH θ Φ)
    (Γ : SourceTwistedTestCurve θ Φ) {τ : ℝ} (hτ : Γ.max < τ) :
    sourcePositiveRayInverse (twistedLegendreRay Γ) τ = ⊥ := by
  obtain ⟨C, hC⟩ := thetaPSH_exists_upper hΦ
  exact rayInverse_eq_bot_of_linear_bound (twistedLegendreRay_le_linear Γ hC) hτ

/-- The extension of a twisted test curve to all `τ ∈ ℝ` (`rmk:extendtestcur`): `Γ_τ` for
`τ < Γ_max`, `inf_{σ < Γ_max} Γ_σ` at `Γ_max` and `-∞` beyond. -/
def twistedTestCurveAt (Γ : SourceTwistedTestCurve θ Φ) (τ : ℝ) : M → EReal :=
  if hτ : τ < Γ.max then Γ.potential ⟨τ, hτ⟩
  else if τ = Γ.max then fun x ↦ ⨅ σ : Iio Γ.max, Γ.potential σ x else ⊥

omit [CompactSpace M] [ConnectedSpace M] in
theorem twistedTestCurveAt_antitone (Γ : SourceTwistedTestCurve θ Φ) (x : M) :
    Antitone (fun τ ↦ twistedTestCurveAt Γ τ x) := by
  intro s t hst
  change twistedTestCurveAt Γ t x ≤ twistedTestCurveAt Γ s x
  by_cases ht : t < Γ.max
  · have hs : s < Γ.max := hst.trans_lt ht
    simp only [twistedTestCurveAt, dif_pos ht, dif_pos hs]
    exact Γ.antitone x hst
  by_cases hte : t = Γ.max
  · subst hte
    rcases hst.eq_or_lt with rfl | hs
    · exact le_rfl
    · simp only [twistedTestCurveAt, dif_pos hs, lt_irrefl, dif_neg, not_false_eq_true, if_true]
      exact iInf_le (fun r : Iio Γ.max ↦ Γ.potential r x) ⟨s, hs⟩
  · have hgt : ¬ t < Γ.max ∧ t ≠ Γ.max := ⟨ht, hte⟩
    simp only [twistedTestCurveAt, dif_neg hgt.1, if_neg hgt.2, Pi.bot_apply]
    exact bot_le

/-- **Twisted `prop:Leginvtc`**: `Γ_τ = inf_{t > 0} (Γ*_t - tτ)` for every `τ ∈ ℝ` (with the
extension of `rmk:extendtestcur`), and `Γ_τ = inf_{t ≥ 0} (Γ*_t - tτ)` with `Γ*_0 = Φ`. -/
theorem twistedLegendre_inverse_whole (hΦ : (ofFixedModel n M).IsThetaPSH θ Φ)
    (Γ : SourceTwistedTestCurve θ Φ) :
    (∀ τ, twistedTestCurveAt Γ τ = sourcePositiveRayInverse (twistedLegendreRay Γ) τ) ∧
      ∀ τ x, twistedTestCurveAt Γ τ x =
        ⨅ t : Ici (0 : ℝ), twistedLegendreRay Γ t x - ((t.1 * τ : ℝ) : EReal) := by
  have hpos : ∀ τ, twistedTestCurveAt Γ τ = sourcePositiveRayInverse (twistedLegendreRay Γ) τ := by
    intro τ
    by_cases hτ : τ < Γ.max
    · simp only [twistedTestCurveAt, dif_pos hτ]
      exact (twistedInverse_eq hΦ Γ ⟨τ, hτ⟩).symm
    by_cases he : τ = Γ.max
    · subst he
      simp only [twistedTestCurveAt, lt_irrefl, dif_neg, not_false_eq_true, if_true]
      funext x
      apply le_antisymm
      · apply le_iInf
        intro t
        rw [twistedLegendre_extension_pos Γ t.2]
        apply (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot _))
          (.inl (EReal.coe_ne_top _))).mpr
        have hsup := iSup_real_eq_iSup_Iio (q := fun τ ↦ twistedTestCurveAt Γ τ x) (m := Γ.max)
          (twistedTestCurveAt_antitone Γ x) (fun s (hs : Γ.max < s) ↦ by
            simp only [twistedTestCurveAt, dif_neg (not_lt.mpr hs.le), if_neg (ne_of_gt hs),
              Pi.bot_apply]) t.1
        have h1 := le_iSup (fun s : ℝ ↦ ((t.1 * s : ℝ) : EReal) + twistedTestCurveAt Γ s x)
          Γ.max
        rw [hsup] at h1
        simp only [twistedTestCurveAt, lt_irrefl, dif_neg, not_false_eq_true, if_true] at h1
        rw [add_comm]
        refine h1.trans (le_of_eq ?_)
        apply iSup_congr
        intro σ
        rw [dif_pos (show σ.1 < Γ.max from σ.2)]
      · apply le_iInf
        intro σ
        rw [← congrFun (twistedInverse_eq hΦ Γ σ) x]
        exact sourceRayLegendre_inverse_antitone _ x (le_of_lt σ.2)
    · have hgt : Γ.max < τ := lt_of_le_of_ne (not_lt.mp hτ) (Ne.symm he)
      simp only [twistedTestCurveAt, dif_neg hτ, if_neg he]
      exact (twistedInverse_eq_bot hΦ Γ hgt).symm
  refine ⟨hpos, fun τ x ↦ ?_⟩
  rw [hpos τ]
  apply le_antisymm
  · apply le_iInf
    intro t
    by_cases ht : t.1 = 0
    · have ht0 : t = ⟨0, by simp⟩ := Subtype.ext ht
      rw [ht0, twistedLegendreRay_zero Γ]
      simp only [zero_mul, EReal.coe_zero, sub_zero]
      exact (rayInverse_le_initial' Γ τ x)
    · have htp : 0 < t.1 := lt_of_le_of_ne t.2 (Ne.symm ht)
      have hh := iInf_le (fun s : Ioi (0 : ℝ) ↦ sourceRayExtension (twistedLegendreRay Γ) s.1 x -
        ((s.1 * τ : ℝ) : EReal)) ⟨t.1, htp⟩
      rwa [sourceRayExtension_nonneg _ t.1 t.2] at hh
  · apply le_iInf
    intro t
    have hh := iInf_le (fun s : Ici (0 : ℝ) ↦ twistedLegendreRay Γ s x - ((s.1 * τ : ℝ) : EReal))
      ⟨t.1, show (0 : ℝ) ≤ t.1 from le_of_lt t.2⟩
    rwa [← sourceRayExtension_nonneg (twistedLegendreRay Γ) t.1 (le_of_lt t.2)] at hh
where
  /-- `inf_{t > 0} (Γ*_t - tτ) ≤ Γ_{-∞} = Φ`. -/
  rayInverse_le_initial' (Γ : SourceTwistedTestCurve θ Φ) (τ : ℝ) (x : M) :
      sourcePositiveRayInverse (twistedLegendreRay Γ) τ x ≤ Φ x := by
    by_cases hτ : τ < Γ.max
    · rw [congrFun (twistedInverse_eq hΦ Γ ⟨τ, hτ⟩) x]
      exact Γ.potential_le_limit _ x
    · let σ : Iio Γ.max := ⟨Γ.max - 1, by change Γ.max - 1 < Γ.max; linarith⟩
      refine (sourceRayLegendre_inverse_antitone _ x
        (show σ.1 ≤ τ by change Γ.max - 1 ≤ τ; linarith [not_lt.mp hτ])).trans ?_
      show sourcePositiveRayInverse (twistedLegendreRay Γ) σ.1 x ≤ Φ x
      rw [congrFun (twistedInverse_eq hΦ Γ σ) x]
      exact Γ.potential_le_limit σ x

/-! ### The Legendre transform is a subgeodesic ray (twisted `lma:testcurvelegusc`) -/

/-- For `t ≥ 0`, the regularized supremum `usc sup_σ (Γ_σ + tσ)` is the assigned Legendre
transform: at `t = 0` because `Γ_{-∞} = Φ`, for `t > 0` because the raw supremum is already
upper semicontinuous. -/
theorem twisted_uscSup_affine_eq (hΦ : (ofFixedModel n M).IsThetaPSH θ Φ)
    (Γ : SourceTwistedTestCurve θ Φ) {t : ℝ} (ht : 0 ≤ t) :
    SGPT.PSH.uscSup (fun σ : Iio Γ.max ↦ fun x ↦ Γ.potential σ x + ((t * σ.1 : ℝ) : EReal)) =
      sourceRayExtension (twistedLegendreRay Γ) t := by
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    rw [twistedLegendre_extension_zero]
    refine Eq.trans ?_ Γ.limit_eq
    apply congrArg uscRegularization
    funext x
    simp only [zero_mul, EReal.coe_zero, add_zero]
  · rw [twistedLegendre_extension_pos Γ hpos]
    obtain ⟨C, hC⟩ := thetaPSH_exists_upper hΦ
    have husc := upperSemicontinuous_iSup_affine
      (fun σ ↦ sourceThetaPSH_upperSemicontinuous (Γ.thetaPSH σ)) Γ.antitone
      (c := C) (fun σ x ↦ (Γ.potential_le_limit σ x).trans (hC x)) hpos
    have heq : (fun x ↦ ⨆ σ : Iio Γ.max, Γ.potential σ x + ((t * σ.1 : ℝ) : EReal)) =
        twistedRawLegendre Γ t := by
      funext x
      exact iSup_congr fun σ ↦ add_comm _ _
    change uscRegularization (fun x ↦ ⨆ σ : Iio Γ.max,
      Γ.potential σ x + ((t * σ.1 : ℝ) : EReal)) = _
    rw [heq]
    exact le_antisymm (uscRegularization_le husc le_rfl) (le_uscRegularization _)

variable [MeasurableSpace M] [BorelSpace M]

/-- **Twisted `lma:testcurvelegusc`** (first part): the Legendre transform of a twisted test
curve, with `Γ*_0 = Φ`, is a subgeodesic ray. -/
theorem twistedLegendreRay_isSubgeodesic (omega : KahlerBackground n M)
    (hΦ : (ofFixedModel n M).IsThetaPSH θ Φ) (Γ : SourceTwistedTestCurve θ Φ) :
    SourceIsSubgeodesicRay omega θ (twistedLegendreRay Γ) := by
  obtain ⟨C, hC⟩ := thetaPSH_exists_upper hΦ
  intro a b ha hab
  have hb : 0 ≤ b := ha.trans hab
  have : Nonempty (Iio Γ.max) := ⟨⟨Γ.max - 1, by change Γ.max - 1 < Γ.max; linarith⟩⟩
  let curve : Iio Γ.max → ℝ → M → EReal := fun σ s x ↦
    Γ.potential σ x + ((((b - a) * σ.1) * s + a * σ.1 : ℝ) : EReal)
  let u₀ : Iio Γ.max → M → EReal := fun σ x ↦ Γ.potential σ x + ((a * σ.1 : ℝ) : EReal)
  let u₁ : Iio Γ.max → M → EReal := fun σ x ↦ Γ.potential σ x + ((b * σ.1 : ℝ) : EReal)
  have h (σ : Iio Γ.max) : SourceSubgeodesicFrom omega θ (curve σ) (u₀ σ) (u₁ σ) := by
    have hh := (sourceSubgeodesic_const omega (Γ.thetaPSH σ)).affineTranslated
      ((b - a) * σ.1) (a * σ.1)
    change SourceSubgeodesicFrom omega θ
      (fun s x ↦ Γ.potential σ x + ((((b - a) * σ.1) * s + a * σ.1 : ℝ) : EReal))
      (fun x ↦ Γ.potential σ x + ((a * σ.1 : ℝ) : EReal))
      (fun x ↦ Γ.potential σ x + (((b - a) * σ.1 + a * σ.1 : ℝ) : EReal)) at hh
    have he : (b - a) * σ.1 + a * σ.1 = b * σ.1 := by ring
    simpa only [curve, u₀, u₁, he] using hh
  have hbound (t : ℝ) (ht : 0 ≤ t) (σ : Iio Γ.max) (x : M) :
      Γ.potential σ x + ((t * σ.1 : ℝ) : EReal) ≤ ((C + t * Γ.max : ℝ) : EReal) := by
    rw [EReal.coe_add]
    exact add_le_add ((Γ.potential_le_limit σ x).trans (hC x))
      (EReal.coe_le_coe (mul_le_mul_of_nonneg_left (le_of_lt σ.2) ht))
  have hP := sourceSubgeodesic_uscSup omega h ⟨_, hbound a ha⟩ ⟨_, hbound b hb⟩
  have he₀ : SGPT.PSH.uscSup u₀ = sourceRayExtension (twistedLegendreRay Γ) a :=
    twisted_uscSup_affine_eq hΦ Γ ha
  have he₁ : SGPT.PSH.uscSup u₁ = sourceRayExtension (twistedLegendreRay Γ) b :=
    twisted_uscSup_affine_eq hΦ Γ hb
  rw [he₀, he₁] at hP
  refine ⟨hab, ?_⟩
  apply hP.congr_Ioo
  intro s hs
  have htime : 0 ≤ s * b + (1 - s) * a := by
    have hh := mul_nonneg hs.1.le (sub_nonneg.mpr hab)
    nlinarith
  rw [← twisted_uscSup_affine_eq hΦ Γ htime]
  apply congrArg uscRegularization
  funext x
  apply iSup_congr
  intro σ
  change Γ.potential σ x + _ = Γ.potential σ x + _
  congr 2
  ring

/-- **Twisted `lma:testcurvelegusc`** (second part): `Γ*` is upper semicontinuous on
`X × (0, ∞)`. -/
theorem twistedLegendre_joint_upperSemicontinuous (omega : KahlerBackground n M)
    (hΦ : (ofFixedModel n M).IsThetaPSH θ Φ) (Γ : SourceTwistedTestCurve θ Φ) :
    UpperSemicontinuous (fun p : M × Ioi (0 : ℝ) ↦ twistedRawLegendre Γ p.2.1 p.1) := by
  have hh := (twistedLegendreRay_isSubgeodesic omega hΦ Γ).joint_positive_upperSemicontinuous
  have heq : (fun p : M × Ioi (0 : ℝ) ↦ sourceRayExtension (twistedLegendreRay Γ) p.2.1 p.1) =
      (fun p : M × Ioi (0 : ℝ) ↦ twistedRawLegendre Γ p.2.1 p.1) := by
    funext p
    rw [twistedLegendre_extension_pos Γ p.2.2]
  rwa [heq] at hh

/-- `Γ*_t` is `θ`-psh for `t > 0`. -/
theorem twistedRawLegendre_thetaPSH (omega : KahlerBackground n M)
    (hΦ : (ofFixedModel n M).IsThetaPSH θ Φ) (Γ : SourceTwistedTestCurve θ Φ) {t : ℝ}
    (ht : 0 < t) : (ofFixedModel n M).IsThetaPSH θ (twistedRawLegendre Γ t) := by
  have hh := (twistedLegendreRay_isSubgeodesic omega hΦ Γ).thetaPSH ⟨t, ht.le⟩
  rwa [twistedLegendreRay_pos Γ (t := ⟨t, ht.le⟩) ht.ne'] at hh

/-! ### Full mass (twisted `cor:GammastarP`) -/

/-- **Twisted `cor:GammastarP`**: for `Φ ∈ 𝓔(X, θ; φ)`, `Γ*_t ∈ 𝓔(X, θ; φ)` for every `t > 0`. -/
theorem twistedLegendre_fullMass (omega : KahlerBackground n M) {φ : M → EReal}
    {hφ : SourceModelPotential θ φ} (hΦ : SourceRelativeFullMass θ φ Φ hφ)
    (Γ : SourceTwistedTestCurve θ Φ) {t : ℝ} (ht : 0 < t) :
    SourceRelativeFullMass θ φ (twistedRawLegendre Γ t) hφ := by
  have hΦpsh : (ofFixedModel n M).IsThetaPSH θ Φ := hΦ.choose
  have hpsh := twistedRawLegendre_thetaPSH omega hΦpsh Γ ht
  have hsingΦ : SGPT.PSH.SingularityLE (twistedRawLegendre Γ t) Φ :=
    (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr
      ⟨t * Γ.max, fun x ↦ twistedRawLegendre_le Γ ht.le x⟩
  have hsingφ := hsingΦ.trans hΦ.choose_spec.1
  refine ⟨hpsh, hsingφ, le_antisymm ?_ ?_⟩
  · exact sourcePotentialNonPluripolarMass_mono omega hpsh hφ.thetaPSH hsingφ
  · rw [← hΦ.choose_spec.2]
    have : Nonempty (OrderDual (Iio Γ.max)) :=
      ⟨⟨Γ.max - 1, by change Γ.max - 1 < Γ.max; linarith⟩⟩
    obtain ⟨C, hC⟩ := thetaPSH_exists_upper hΦpsh
    have hm (j : Fin n) : Monotone
        (fun τ : OrderDual (Iio Γ.max) ↦ Γ.potential τ) := by
      intro a b hab x
      exact Γ.antitone x hab
    have hlim := sourceIncreasingMixed_mass_tendsto omega
      (θ := fun _ : Fin n ↦ θ)
      (u := fun τ : OrderDual (Iio Γ.max) ↦ fun _ : Fin n ↦ Γ.potential τ)
      (fun τ _ ↦ Γ.thetaPSH τ) hm (C := fun _ ↦ C)
      (fun _ τ x ↦ (Γ.potential_le_limit τ x).trans (hC x))
    have hU : uscRegularization (⨆ τ : OrderDual (Iio Γ.max), Γ.potential τ) = Φ := by
      refine Eq.trans ?_ Γ.limit_eq
      apply congrArg uscRegularization
      funext x
      exact iSup_apply
    have hlim' : Tendsto (fun τ : OrderDual (Iio Γ.max) ↦
        sourcePotentialNonPluripolarMeasure θ (Γ.potential τ) (Γ.thetaPSH τ) univ) atTop
        (𝓝 (sourcePotentialNonPluripolarMeasure θ Φ hΦpsh univ)) := by
      simpa only [hU, sourceMixedNonPluripolarMass, sourceMixedNonPluripolarMeasure,
        sourcePotentialNonPluripolarMeasure, DiagonalMass.diagonalPotentialMeasure] using hlim
    apply le_of_tendsto' hlim'
    intro σ
    apply sourcePotentialNonPluripolarMass_mono omega (Γ.thetaPSH σ) hpsh
    refine (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨-(t * (σ : Iio Γ.max).1), fun x ↦ ?_⟩
    have h1 := le_twistedRawLegendre Γ t σ x
    calc Γ.potential σ x = (((t * (σ : Iio Γ.max).1 : ℝ) : EReal) + Γ.potential σ x) +
          ((-(t * (σ : Iio Γ.max).1) : ℝ) : EReal) := by
          rw [add_comm (((t * (σ : Iio Γ.max).1 : ℝ) : EReal)), add_assoc, ← EReal.coe_add,
            add_neg_cancel, EReal.coe_zero, add_zero]
      _ ≤ twistedRawLegendre Γ t x + ((-(t * (σ : Iio Γ.max).1) : ℝ) : EReal) :=
          add_le_add h1 le_rfl

/-! ### Supremum (twisted `lma:suplegenlinear`) -/

omit [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- A twisted test curve comes close to `Φ` somewhere: `sup_{Φ > -∞} (Γ_τ - Φ) = 0`. -/
theorem twisted_exists_close (Γ : SourceTwistedTestCurve θ Φ) (τ : Iio Γ.max) {ε : ℝ}
    (hε : 0 < ε) : ∃ x, Φ x + ((-ε : ℝ) : EReal) < Γ.potential τ x := by
  by_contra hne
  simp only [not_exists, not_lt] at hne
  have hw : (ofFixedModel n M).IsThetaPSH θ (fun x ↦ Γ.potential τ x + (ε : EReal)) :=
    sourceThetaPSH_add_const (Γ.thetaPSH τ) ε
  have hwΦ : (fun x ↦ Γ.potential τ x + (ε : EReal)) ≤ Φ := by
    intro x
    calc Γ.potential τ x + (ε : EReal) ≤ (Φ x + ((-ε : ℝ) : EReal)) + (ε : EReal) :=
          add_le_add (hne x) le_rfl
      _ = Φ x := by rw [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero]
  have hsing : SGPT.PSH.SingularityLE (fun x ↦ Γ.potential τ x + (ε : EReal)) (Γ.potential τ) :=
    (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨ε, fun x ↦ le_rfl⟩
  have hle := (le_sourceRelativeEnvelope hw hwΦ hsing).trans_eq (Γ.twistedFixedPoint τ)
  obtain ⟨x₀, hx₀⟩ : ∃ x, Γ.potential τ x ≠ ⊥ := by
    obtain ⟨y, -, hy⟩ := ((isThetaPSH_iff_nativeThetaPotential θ _).mp (Γ.thetaPSH τ)).2
      (Classical.arbitrary M) univ isOpen_univ (mem_univ _)
    exact ⟨y, hy⟩
  have h1 : Γ.potential τ x₀ + (ε : EReal) ≤ Γ.potential τ x₀ := hle x₀
  obtain ⟨y, hy⟩ : ∃ y : ℝ, Γ.potential τ x₀ = (y : EReal) :=
    ⟨(Γ.potential τ x₀).toReal,
      (EReal.coe_toReal (thetaPSH_ne_top (Γ.thetaPSH τ) x₀) hx₀).symm⟩
  rw [hy, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
  linarith

end SGPT.TestCurve.RWNTwisted
