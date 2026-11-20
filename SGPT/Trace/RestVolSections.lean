import SGPT.IGood.DXLow2DXMain
import SGPT.IGood.DXLow2Upper
import SGPT.Trace.OTExtGlobalReduction
import SGPT.Bergman.SourceTensorIdealGlobalSections

/-!
# Sections of `L^k ⊗ T ⊗ 𝓡_k` and their asymptotics

Lane TRACE-RV, blueprint `claude-rest-vol.tex`, nodes `claude-rest-vol:ideal-h0`,
`claude-rest-vol:lower-core`, `claude-rest-vol:upper-core`.  Source: `chapter_trace.tex`,
Section *Restricted volumes of line bundles* (`thm:rest_volume`, `thm:rest_volume_2`).

On a compact connected complex manifold `V` of dimension `m` with holomorphic line bundles
`L`, `T` carrying smooth Hermitian metrics, and a family of ideal sheaves `𝓡_k ⊆ 𝒪_V`, we write

* `IdealTwistedSections L T k 𝓡 = H⁰(V, L^k ⊗ T ⊗ 𝓡)`: the global sections of the sheaf tensor
  product (`TensorIdealGlobalSections`, the same construction as the Bergman chapter's
  `LiteralTwistedMultiplierSections`, for an arbitrary ideal sheaf);
* `idealH0 L T k 𝓡 = h⁰(V, L^k ⊗ T ⊗ 𝓡)` and
  `normalizedIdealH0 L T 𝓡 k = m!/k^m · h⁰(V, L^k ⊗ T ⊗ 𝓡_k)`.

The two core estimates of the book's proof of `thm:rest_volume` are proved here in this
abstract form, from the asymptotic Riemann–Roch formula `thm:DXmain1` on `V`:

* `le_liminf_normalizedIdealH0` (the lower bound): if `𝓘(kψ) ⊆ 𝓡_k` for all `k ≥ 1`, then
  `vol θ_ψ ≤ liminf_k m!/k^m h⁰(V, L^k ⊗ T ⊗ 𝓡_k)`;
* `limsup_normalizedIdealH0_le` (the upper bound): if `θ = c₁(L, h)` carries a Kähler current
  and for every `M' > M` there is `ψ ∈ PSH(V, θ)` with `vol θ_ψ < M'` and `𝓡_k ⊆ 𝓘(kψ)` for
  `k` large, then `limsup_k m!/k^m h⁰(V, L^k ⊗ T ⊗ 𝓡_k) ≤ M`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.RestVol

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.NativeHermitianMetric
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.Quant2
open HermitianHolomorphicLineBundle

variable {m : ℕ} {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel m) V]
  [IsComplexManifold m V]

/-! ### The section spaces -/

/-- **`H⁰(V, L^k ⊗ T ⊗ 𝓡)`** for an ideal sheaf `𝓡 ⊆ 𝒪_V`: the global sections of the sheaf
tensor product of the holomorphic line bundle `L^k ⊗ T` with `𝓡` (for `𝓡 = 𝓘(kφ)` this is the
Bergman chapter's `LiteralTwistedMultiplierSections`). -/
abbrev IdealTwistedSections (L T : HermitianHolomorphicLineBundle.{0, 0} m V) (k : ℕ)
    (R : GermIdeal m V) :=
  TensorIdealGlobalSections (n := m) (twistedPower L T k).Fiber R

/-- `h⁰(V, L^k ⊗ T ⊗ 𝓡)`. -/
def idealH0 (L T : HermitianHolomorphicLineBundle.{0, 0} m V) (k : ℕ) (R : GermIdeal m V) : ℕ :=
  Module.finrank ℂ (IdealTwistedSections L T k R)

/-- The normalized dimension `m!/k^m · h⁰(V, L^k ⊗ T ⊗ 𝓡_k)`. -/
def normalizedIdealH0 (L T : HermitianHolomorphicLineBundle.{0, 0} m V) (R : ℕ → GermIdeal m V)
    (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((m.factorial : ℝ) / (k : ℝ) ^ m * idealH0 L T k (R k))

theorem idealH0_eq_finrank (L T : HermitianHolomorphicLineBundle.{0, 0} m V) (k : ℕ)
    (R : GermIdeal m V) :
    idealH0 L T k R = Module.finrank ℂ
      ↥(fullHolomorphicIdealSections (n := m) (twistedPower L T k).Fiber R) :=
  (tensorIdealGlobalSectionEquiv (n := m) (twistedPower L T k).Fiber R).finrank_eq

theorem finrank_literal_eq (L T : HermitianHolomorphicLineBundle.{0, 0} m V) (k : ℕ)
    (φ : V → EReal) :
    Module.finrank ℂ (LiteralTwistedMultiplierSections L T k φ) = Module.finrank ℂ
      ↥(fullHolomorphicIdealSections (n := m) (twistedPower L T k).Fiber
        (sourceDegreeMultiplierIdeal (n := m) k φ)) :=
  (literalTwistedMultiplierSectionEquiv L T k φ).finrank_eq

variable [CompactSpace V]

/-- `h⁰` is monotone in the ideal sheaf. -/
theorem finrank_fullHolomorphicIdealSections_mono
    (L T : HermitianHolomorphicLineBundle.{0, 0} m V) (k : ℕ) {A B : GermIdeal m V}
    (h : A.Le B) :
    Module.finrank ℂ ↥(fullHolomorphicIdealSections (n := m) (twistedPower L T k).Fiber A) ≤
      Module.finrank ℂ ↥(fullHolomorphicIdealSections (n := m) (twistedPower L T k).Fiber B) := by
  have := twistedSections_finiteDimensional L T k
  exact Submodule.finrank_mono
    (SGPT.Trace.OTExt.fullHolomorphicIdealSections_mono (twistedPower L T k).Fiber h)

theorem idealH0_mono (L T : HermitianHolomorphicLineBundle.{0, 0} m V) (k : ℕ)
    {A B : GermIdeal m V} (h : A.Le B) : idealH0 L T k A ≤ idealH0 L T k B := by
  rw [idealH0_eq_finrank, idealH0_eq_finrank]
  exact finrank_fullHolomorphicIdealSections_mono L T k h

/-- If `𝓘(kψ) ⊆ 𝓡` then `h⁰(V, L^k ⊗ T ⊗ 𝓘(kψ)) ≤ h⁰(V, L^k ⊗ T ⊗ 𝓡)`. -/
theorem finrank_literal_le_idealH0 (L T : HermitianHolomorphicLineBundle.{0, 0} m V) (k : ℕ)
    {ψ : V → EReal} {R : GermIdeal m V} (h : (sourceDegreeMultiplierIdeal (n := m) k ψ).Le R) :
    Module.finrank ℂ (LiteralTwistedMultiplierSections L T k ψ) ≤ idealH0 L T k R := by
  rw [finrank_literal_eq, idealH0_eq_finrank]
  exact finrank_fullHolomorphicIdealSections_mono L T k h

/-- If `𝓡 ⊆ 𝓘(kψ)` then `h⁰(V, L^k ⊗ T ⊗ 𝓡) ≤ h⁰(V, L^k ⊗ T ⊗ 𝓘(kψ))`. -/
theorem idealH0_le_finrank_literal (L T : HermitianHolomorphicLineBundle.{0, 0} m V) (k : ℕ)
    {ψ : V → EReal} {R : GermIdeal m V} (h : R.Le (sourceDegreeMultiplierIdeal (n := m) k ψ)) :
    idealH0 L T k R ≤ Module.finrank ℂ (LiteralTwistedMultiplierSections L T k ψ) := by
  rw [finrank_literal_eq, idealH0_eq_finrank]
  exact finrank_fullHolomorphicIdealSections_mono L T k h

theorem normalizedH0_le_normalizedIdealH0 (L T : HermitianHolomorphicLineBundle.{0, 0} m V)
    {ψ : V → EReal} {R : ℕ → GermIdeal m V} {k : ℕ}
    (h : (sourceDegreeMultiplierIdeal (n := m) k ψ).Le (R k)) :
    normalizedH0 L T ψ k ≤ normalizedIdealH0 L T R k := by
  unfold normalizedH0 normalizedIdealH0
  apply ENNReal.ofReal_le_ofReal
  have h0 : (0 : ℝ) ≤ (m.factorial : ℝ) / (k : ℝ) ^ m := by positivity
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast finrank_literal_le_idealH0 L T k h) h0

theorem normalizedIdealH0_le_normalizedH0 (L T : HermitianHolomorphicLineBundle.{0, 0} m V)
    {ψ : V → EReal} {R : ℕ → GermIdeal m V} {k : ℕ}
    (h : (R k).Le (sourceDegreeMultiplierIdeal (n := m) k ψ)) :
    normalizedIdealH0 L T R k ≤ normalizedH0 L T ψ k := by
  unfold normalizedH0 normalizedIdealH0
  apply ENNReal.ofReal_le_ofReal
  have h0 : (0 : ℝ) ≤ (m.factorial : ℝ) / (k : ℝ) ^ m := by positivity
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast idealH0_le_finrank_literal L T k h) h0

/-! ### The two core estimates -/

variable [MeasurableSpace V] [BorelSpace V] [ConnectedSpace V]

/-- **The lower bound** (the first two lines of the book's estimates in the proof of
`thm:rest_volume`): by `thm:DXmain1` on `V`, if `𝓘(kψ) ⊆ 𝓡_k` for every `k ≥ 1`, then
`vol θ_ψ ≤ liminf_k m!/k^m h⁰(V, L^k ⊗ T ⊗ 𝓡_k)`. -/
theorem le_liminf_normalizedIdealH0 (ωV : KahlerBackground m V)
    {L T : HermitianHolomorphicLineBundle.{0, 0} m V}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {ψ : V → EReal} (hψ : (ofFixedModel m V).IsThetaPSH (chernForm L hL) ψ)
    {R : ℕ → GermIdeal m V}
    (hR : ∀ k : ℕ, 0 < k → (sourceDegreeMultiplierIdeal (n := m) k ψ).Le (R k)) :
    sourceIVolume (chernForm L hL) ψ hψ ≤
      liminf (fun k => normalizedIdealH0 L T R k) atTop := by
  obtain ⟨hψ', hlow⟩ := SGPT.IGood.DXLow2.riemannRochLowerBound_of_kahler ωV hL hT hψ
  refine (le_of_eq (sourceIVolume_proof_independent _ _ hψ hψ')).trans (hlow.trans ?_)
  refine liminf_le_liminf ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  exact normalizedH0_le_normalizedIdealH0 L T (hR k hk)

/-- **The upper bound** (the last lines of the book's estimates in Step 1 of the proof of
`thm:rest_volume`): if `θ = c₁(L, h)` carries a Kähler current and for every `M' > M` there is
`ψ ∈ PSH(V, θ)` with `vol θ_ψ < M'` and `𝓡_k ⊆ 𝓘(kψ)` for all large `k`, then
`limsup_k m!/k^m h⁰(V, L^k ⊗ T ⊗ 𝓡_k) ≤ M`. -/
theorem limsup_normalizedIdealH0_le (ωV : KahlerBackground m V)
    {L T : HermitianHolomorphicLineBundle.{0, 0} m V}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {ψ₀ : V → EReal} (hψ₀ : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) ψ₀)
    {R : ℕ → GermIdeal m V} {M : ℝ≥0∞}
    (happrox : ∀ M' : ℝ≥0∞, M < M' → ∃ (ψ : V → EReal)
      (hψ : (ofFixedModel m V).IsThetaPSH (chernForm L hL) ψ),
      sourceIVolume (chernForm L hL) ψ hψ < M' ∧
        ∀ᶠ k in atTop, (R k).Le (sourceDegreeMultiplierIdeal (n := m) k ψ)) :
    limsup (fun k => normalizedIdealH0 L T R k) atTop ≤ M := by
  obtain ⟨ωn, hωn⟩ := SGPT.IGood.DXLow2.exists_normalized_kahlerBackground ωV
  refine le_of_forall_gt fun M' hM' => ?_
  obtain ⟨ψ, hψ, hvol, hev⟩ := happrox M' hM'
  obtain ⟨hψ', hup⟩ :=
    SGPT.IGood.DXLow2.riemannRochUpperBound_of_kahlerCurrent ωn hωn hL hT hψ₀ hψ
  refine lt_of_le_of_lt ?_ hvol
  refine le_trans (limsup_le_limsup ?_) (hup.trans (le_of_eq
    (sourceIVolume_proof_independent _ _ hψ' hψ)))
  filter_upwards [hev] with k hk
  exact normalizedIdealH0_le_normalizedH0 L T hk

end SGPT.Trace.RestVol
