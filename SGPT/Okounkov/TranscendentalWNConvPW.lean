import SGPT.Okounkov.TranscendentalWNConv7Core
import SGPT.Okounkov.TranscendentalLiftingBlowupKahler
import SGPT.Okounkov.TranscendentalDensity
import SGPT.PSH.LogResolution
import SGPT.Foundations.Analysis.Pending.RueckertNullstellensatz
import SGPT.Foundations.Analysis.Pending.MeteredDivisorGlobalIdeal
import SGPT.Foundations.Analysis.Pending.StepFourNoComponentContainsW
import SGPT.Foundations.Analysis.Pending.UniformPerturbedKahlerLowerBound
import SGPT.Foundations.Analysis.Pending.IdealComparisonResidual

/-!
# The perturbed weight of WN21 §7

Blueprint `claude-tok-wn-conv7`, node `tok-wn-conv7:weight-perturbation`, and
`claude-tok-wn-pw` (nodes `tok-wn-pw:*`); source WN21 §7, first paragraph (``by possibly
increasing `ε` by an arbitrarily small amount while adding arbitrarily small multiples of
`ln|s_{E_i}|²` to `ψ` one can make sure that `ω̃` is Kähler''), with the rescaling
`ψ ↦ (1 - s)ψ` recorded by lane WN-CONV7 (it keeps `ũ ⪯ Ψ`).

## Main results

* `exists_weight_domination` (`tok-wn-pw:domination`): on a compact complex manifold, if a metered
  effective `ℚ`-divisor `F` is supported in the support of an effective divisor `D` with a smooth
  metric `ψ_D`, then `F ≤ N D` in the weight sense: `N ψ_D ≤ ψ_F + C` for some `N > 0`
  (Rückert's Nullstellensatz with a uniform exponent, TN's `RueckertNullstellensatz`).
* `exists_rat_smul_mem_gentleKahlerCurrents` (`tok-wn-pw:rescale`): for `ψ ∈ Ω(Θ)` there is a
  rational `a ∈ (0, 1)` with `aψ ∈ Ω(Θ)`.
* `exists_perturbedWeight_of_mem_gentleKahlerCurrents` (`tok-wn-pw:perturbation`): on a compact
  connected Kähler manifold, for every `ψ₁ ∈ Ω(Θ)` there are a `Θ`-psh `Ψ` with
  `ψ₁ ⪯ Ψ ⪯ ψ₂` for some `ψ₂ ∈ Ω(Θ)`, a finite sequence of blow-ups `π : 𝒵 → X` with exceptional
  locus in `Supp D'`, a metered effective `ℚ`-divisor `D'` and a smooth `h` with
  `Ψ ∘ π = ψ_{D'} + h` and `π^*Θ - Θ_{D'} + dd^c h` Kähler.
* `perturbedWeight : PerturbedWeightStatement F` (`tok-wn-conv7:weight-perturbation`).
* `contactMassLimit_of_fibreLimit`, `keyConvergence_of_measureControl_of_fibreLimit`
  (`tok-wn-pw:fibre-reduction`): the analytic core of WN21 §7 and `tok-wn:convergence` now only
  need `FibreLimitStatement F` (and `MeasureControlStatement F`); these two are **conditional**.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Okounkov.TranscendentalMain
open SGPT.Okounkov.TranscendentalCore

/-! ### Extended-real bookkeeping -/

/-- `N • x = N x` on `EReal`. -/
private theorem nsmul_eq_coe_mul_ereal : ∀ (N : ℕ) (x : EReal), N • x = ((N : ℝ) : EReal) * x
  | 0, x => by simp
  | (k + 1), x => by
      have h1 : (((k + 1 : ℕ) : ℝ) : EReal) = ((k : ℝ) : EReal) + ((1 : ℝ) : EReal) := by
        rw [← EReal.coe_add]; norm_num
      rw [succ_nsmul, nsmul_eq_coe_mul_ereal k x, h1,
        EReal.right_distrib_of_nonneg
          (EReal.coe_nonneg.mpr (by positivity)) (EReal.coe_nonneg.mpr zero_le_one)]
      norm_num

/-- The lower bound `ψ₁ ∘ π ≤ Ψ ∘ π + C` of the perturbed weight, pointwise: with `ψ₁ ∘ π = cψ_D + ρ`,
`Ψ ∘ π = acψ_D + δψ_F + v`, `Nψ_D ≤ ψ_F + C'`, `ψ_D ≤ K` and `ac + δN ≤ c`. -/
private theorem lower_aux {c a δ N C K B H : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hcoef : a * c + δ * N ≤ c) {w f : EReal} {ρ v : ℝ} (hw : w ≤ (K : EReal)) (hf : f ≠ ⊤)
    (hdom : (N : EReal) * w ≤ f + (C : EReal)) (hρ : |ρ| ≤ B) (hv : |v| ≤ H) :
    (c : EReal) * w + (ρ : EReal) ≤
      ((a * c : ℝ) : EReal) * w + (δ : EReal) * f + (v : EReal) +
        ((B + δ * |C| + (c - a * c - δ * N) * |K| + H : ℝ) : EReal) := by
  induction w using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos hc, EReal.bot_add]; exact bot_le
  | top => exact absurd hw (not_le.mpr (EReal.coe_lt_top K))
  | coe r =>
    induction f using EReal.rec with
    | bot =>
      rw [EReal.bot_add, ← EReal.coe_mul] at hdom
      exact absurd (le_bot_iff.mp hdom) (EReal.coe_ne_bot _)
    | top => exact absurd rfl hf
    | coe t =>
      have hr : r ≤ K := EReal.coe_le_coe_iff.mp hw
      have hdom' : N * r ≤ t + C := by exact_mod_cast hdom
      have h1 : 0 ≤ c - a * c - δ * N := by linarith
      have h2 : (c - a * c - δ * N) * r ≤ (c - a * c - δ * N) * |K| :=
        mul_le_mul_of_nonneg_left (hr.trans (le_abs_self K)) h1
      have h3 : δ * (N * r) ≤ δ * (t + C) := mul_le_mul_of_nonneg_left hdom' hδ.le
      have h4 : δ * C ≤ δ * |C| := mul_le_mul_of_nonneg_left (le_abs_self C) hδ.le
      have h5 := (abs_le.mp hρ).2
      have h6 := (abs_le.mp hv).1
      have key : c * r + ρ ≤ a * c * r + δ * t + v + (B + δ * |C| + (c - a * c - δ * N) * |K| + H) := by
        nlinarith
      exact_mod_cast key

/-- The upper bound `Ψ ∘ π ≤ ψ₂ ∘ π + C` of the perturbed weight, pointwise: with
`Ψ ∘ π = acψ_D + δψ_F + v`, `ψ₂ ∘ π = a(cψ_D + ρ)`, `ψ_F ≤ K`. -/
private theorem upper_aux {c a δ K B H : ℝ} (hc : 0 < c) (ha : 0 < a) (hδ : 0 < δ)
    {w f : EReal} {ρ v : ℝ} (hw : w ≠ ⊤) (hf : f ≤ (K : EReal)) (hρ : |ρ| ≤ B) (hv : |v| ≤ H) :
    ((a * c : ℝ) : EReal) * w + (δ : EReal) * f + (v : EReal) ≤
      (a : EReal) * ((c : EReal) * w + (ρ : EReal)) + ((δ * |K| + H + a * B : ℝ) : EReal) := by
  induction w using EReal.rec with
  | bot =>
    rw [EReal.coe_mul_bot_of_pos (mul_pos ha hc), EReal.bot_add, EReal.bot_add]; exact bot_le
  | top => exact absurd rfl hw
  | coe r =>
    induction f using EReal.rec with
    | bot => rw [EReal.coe_mul_bot_of_pos hδ, EReal.add_bot, EReal.bot_add]; exact bot_le
    | top => exact absurd hf (not_le.mpr (EReal.coe_lt_top K))
    | coe t =>
      have ht : t ≤ K := EReal.coe_le_coe_iff.mp hf
      have h1 : δ * t ≤ δ * |K| := mul_le_mul_of_nonneg_left (ht.trans (le_abs_self K)) hδ.le
      have h2 := (abs_le.mp hρ).1
      have h3 := (abs_le.mp hv).2
      have h4 : a * (-B) ≤ a * ρ := mul_le_mul_of_nonneg_left h2 ha.le
      have key : a * c * r + δ * t + v ≤ a * (c * r + ρ) + (δ * |K| + H + a * B) := by nlinarith
      exact_mod_cast key

/-! ### Domination of a divisor supported in the support of another -/

section Domination

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- **`tok-wn-pw:domination`.** On a compact complex manifold, let `D` be an effective divisor
with a smooth metric `ψ_D` (`IsDivisorMetric D E_D`) and `F` a metered effective `ℚ`-divisor with
`Supp F ⊆ Supp D`. Then `F ≤ N D` in the weight sense: `N ψ_D ≤ ψ_F + C` for some `N > 0` and
`C`. (`ψ_F` has analytic singularities of type `(c_F, 𝔞_F)`, `𝔞_F` invertible with
`Z(𝔞_F) = Supp F`; Rückert's Nullstellensatz gives `𝒪(-D)^N ⊆ 𝔞_F`.) -/
theorem exists_weight_domination [CompactSpace Y] {D : EffectiveDivisor n Y}
    {ED F : MeteredEffectiveQDivisor n Y} (hED : DivisorMetric.IsDivisorMetric D ED)
    (hsupp : F.support ⊆ D.support) :
    ∃ N C : ℝ, 0 < N ∧ ∀ y, (N : EReal) * ED.weight y ≤ F.weight y + (C : EReal) := by
  obtain ⟨cF, 𝔞F, hcF, hinvF, htypeF⟩ :=
    MeteredDivisorGlobalIdeal.exists_hasAnalyticSingularitiesOfType F
  have hEDt := DivisorMetric.hasAnalyticSingularitiesOfType_of_isDivisorMetric hED
  have hEDc := IdealComparisonResidual.hasAnalyticSingularitiesOfType_smul hcF hEDt
  rw [mul_one] at hEDc
  have hz : 𝔞F.zeroLocus ⊆ D.ideal.zeroLocus := by
    rw [← StepFourNoComponentContainsW.poleSet_eq_zeroLocus htypeF]
    exact hsupp
  obtain ⟨N, hN, hle⟩ := RueckertNullstellensatz.exists_idealPow_le_of_zeroLocus_subset
    (DivisorMetric.isCoherent_of_isInvertible D.isInvertible)
    (DivisorMetric.isCoherent_of_isInvertible hinvF) hz
  have hpow := IdealWeightPowers.hasAnalyticSingularitiesOfType_pow hEDc N
  obtain ⟨C, hC⟩ := IdealWeightComparison.moreSingularOn_univ_of_le hpow htypeF hle
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hcFR : (0 : ℝ) < (cF : ℝ) := by exact_mod_cast hcF
  refine ⟨(N : ℝ) * (cF : ℝ), C, mul_pos hNR hcFR, fun y => ?_⟩
  have h := hC y (mem_univ y)
  simp only at h
  rwa [nsmul_eq_coe_mul_ereal, ← mul_assoc, ← EReal.coe_mul] at h

end Domination

/-! ### Rescaling a Kähler current with gentle singularities -/

section Rescale

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] [ConnectedSpace M]

/-- **`tok-wn-pw:rescale`.** For `ψ ∈ Ω(Θ)` on a compact connected manifold there is a rational
`a ∈ (0, 1)` with `aψ ∈ Ω(Θ)`: if `Θ + dd^c ψ ≥ κ` and `Θ + Aκ ≥ 0`, then
`Θ + dd^c(aψ) = a(Θ + dd^c ψ) + (1 - a)Θ ≥ κ/2` as soon as `(1 - a)(1 + A) ≤ 1/2`. -/
theorem exists_rat_smul_mem_gentleKahlerCurrents {Θ : ClosedRealOneOneForm n M}
    {ψ : M → EReal} (hψ : ψ ∈ gentleKahlerCurrents Θ) :
    ∃ a : ℚ, 0 < a ∧ a < 1 ∧
      (fun x => ((a : ℝ) : EReal) * ψ x) ∈ gentleKahlerCurrents Θ := by
  obtain ⟨κ, hκ⟩ := hψ.2
  obtain ⟨A, hA, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul κ Θ
  obtain ⟨s, hs0, hs⟩ := exists_rat_btwn (show (0 : ℝ) < 1 / (2 * (1 + A)) by positivity)
  have hsA : (s : ℝ) * (1 + A) < 1 / 2 := by
    rw [lt_div_iff₀ (by positivity)] at hs
    linarith
  have hs1 : (s : ℝ) < 1 := by nlinarith
  refine ⟨1 - s, by
    have : (s : ℚ) < 1 := by exact_mod_cast hs1
    linarith, by
    have : (0 : ℚ) < s := by exact_mod_cast hs0
    linarith, ?_⟩
  set a : ℚ := 1 - s with ha_def
  have haR : (a : ℝ) = 1 - (s : ℝ) := by rw [ha_def]; push_cast; ring
  have ha : (0 : ℚ) < a := by
    have : (s : ℚ) < 1 := by exact_mod_cast hs1
    rw [ha_def]; linarith
  have hg := TranscendentalDensity.smul_mem_gentleKahlerCurrents hψ ha
  have h1 := isThetaPshPotential_nonneg_smul hκ (c := (a : ℝ)) (by rw [haR]; linarith)
  set σ : ClosedRealOneOneForm n M :=
    (s : ℝ) • (Θ + A • κ.form) + ((1 / 2 : ℝ) - (s : ℝ) * (1 + A)) • κ.form with hσ_def
  have hσ : σ.val.IsSemipositive :=
    UniformPerturbedKahlerLowerBound.isSemipositive_add
      (KahlerDomination.isSemipositive_smul hsemi hs0.le)
      (KahlerDomination.isSemipositive_smul κ.isSemipositive (by linarith))
  have h2 := LocalPotentials.isThetaPshPotential_add_of_semipositive h1 hσ
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hform : (a : ℝ) • (Θ - κ.form) + σ = Θ - (KahlerBackground.smul hhalf κ).form := by
    rw [KahlerBackground.smul_form, hσ_def, haR]
    module
  rw [hform] at h2
  have h3 := LocalPotentials.isThetaPshPotential_add_of_semipositive h2
    (KahlerBackground.smul hhalf κ).isSemipositive
  rw [sub_add_cancel] at h3
  exact ⟨⟨h3, hg.1.2⟩, ⟨KahlerBackground.smul hhalf κ, h2⟩⟩

end Rescale

/-! ### The perturbed weight -/

/-- `atlasClosedFormToNative ∘ nativeClosedFormToAtlas = id`. -/
private theorem atlasClosedFormToNative_nativeClosedFormToAtlas' {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (θ : ClosedRealOneOneForm n M) :
    SGPT.PSH.VariableComplexAtlas.atlasClosedFormToNative
      (SGPT.PSH.VariableComplexAtlas.nativeClosedFormToAtlas θ) = θ := by
  rcases θ with ⟨θ, hθ⟩
  cases θ
  rfl

/-- **`tok-wn-pw:perturbation`** (WN21 §7, first paragraph, with the rescaling `ψ₁ ↦ aψ₁`). On a
compact connected Kähler manifold `(M, η)`, let `ψ₁ ∈ Ω(Θ)`. There are a `Θ`-psh `Ψ` with
`ψ₁ ⪯ Ψ ⪯ ψ₂` for some `ψ₂ ∈ Ω(Θ)`, a finite sequence of blow-ups with smooth centres
`π : 𝒵 → M` from a compact connected manifold whose exceptional locus lies in `Supp D'`, a metered
effective `ℚ`-divisor `D'` on `𝒵` and a smooth `h` with `Ψ ∘ π = ψ_{D'} + h` and
`π^*Θ - Θ_{D'} + dd^c h` Kähler.

Proof: `ψ₂ = aψ₁ ∈ Ω(Θ)` (`a ∈ (0,1)` rational, `exists_rat_smul_mem_gentleKahlerCurrents`); `π` is
the principalization of the ideal `𝔞` of `ψ₁` (type `(c, 𝔞)`), `π^*𝔞 = 𝒪(-D₀)`,
`ψ₁ ∘ π = cψ_{D₀} + O(1)`, `π` an isomorphism over `X \ Z(𝔞)`, so `Exc(π) ⊆ Supp D₀`; the
exceptional divisor `F` of `tok:ext-blowup-kahler` has `Supp F ⊆ Exc(π)`, hence
`Nψ_{D₀} ≤ ψ_F + C` (`exists_weight_domination`); `π^*Θ - δΘ_F + dd^c(ψ₂ ∘ π)` is a Kähler current
for small rational `δ > 0`, taken with `δN ≤ (1 - a)c`; its log singularities along `acD₀` give a
smooth `h` with `π^*Θ - δΘ_F - acΘ_{D₀} + dd^c h` Kähler (the Kähler half of `lma:logsingrem`);
`D' = acD₀ + δF`, `Φ = ψ_{D'} + h` is `π^*Θ`-psh and descends to `Ψ`. -/
theorem exists_perturbedWeight_of_mem_gentleKahlerCurrents {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    [CompactSpace M] [ConnectedSpace M] (η : KahlerBackground (m + 1) M)
    {Θ : ClosedRealOneOneForm (m + 1) M} {ψ₁ : M → EReal} (hψ₁ : ψ₁ ∈ gentleKahlerCurrents Θ) :
    ∃ Ψ : M → EReal, IsThetaPshPotential Θ.val Ψ ∧ SGPT.PSH.SingularityLE ψ₁ Ψ ∧
      (∃ ψ₂ ∈ gentleKahlerCurrents Θ, SGPT.PSH.SingularityLE Ψ ψ₂) ∧
      ∃ (𝒵 : Type u) (_ : TopologicalSpace 𝒵) (_ : ChartedSpace (ComplexModel (m + 1)) 𝒵)
        (_ : IsComplexManifold (m + 1) 𝒵) (π : 𝒵 → M)
        (hπ : IsBlowupSequence (m + 1) M 𝒵 π)
        (D' : MeteredEffectiveQDivisor (m + 1) 𝒵) (h : 𝒵 → ℝ)
        (hh : ChartSmooth (n := m + 1) h),
        CompactSpace 𝒵 ∧ ConnectedSpace 𝒵 ∧ exceptionalLocus (m + 1) π ⊆ D'.support ∧
        (∀ z, Ψ (π z) = D'.weight z + (h z : EReal)) ∧
        ((ClosedRealOneOneForm.pullback hπ.contMDiff Θ - D'.curvature) +
          ddcClosedForm h hh).val.IsKahler := by
  classical
  -- the rescaled current `ψ₂ = aψ₁ ∈ Ω(Θ)`
  obtain ⟨a, ha, ha1, hψ₂⟩ := exists_rat_smul_mem_gentleKahlerCurrents hψ₁
  set ψ₂ : M → EReal := fun x => ((a : ℝ) : EReal) * ψ₁ x with hψ₂_def
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have ha1R : (a : ℝ) < 1 := by exact_mod_cast ha1
  -- the analytic type `(c, 𝔞)` of `ψ₁` and its principalization
  obtain ⟨⟨hψpsh, c, 𝔞, -, hgentle⟩, -⟩ := hψ₁
  have htype := hgentle.2.1
  have hc : (0 : ℚ) < c := htype.1
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hQ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) M).IsQPSH ψ₁ :=
    ⟨SGPT.PSH.VariableComplexAtlas.nativeClosedFormToAtlas Θ,
      (SGPT.PSH.VariableComplexAtlas.isThetaPSH_iff_nativeThetaPotential _ ψ₁).mpr
        (by rwa [atlasClosedFormToNative_nativeClosedFormToAtlas'])⟩
  obtain ⟨Y, tY, cY, mY, π, D, E, hseq, hcpt, -, -, -, hsupp, hiso, hmod,
      ⟨ED, hEDs, hED, ⟨L⟩⟩, -⟩ := SGPT.PSH.exists_principalization_logSingularities hQ htype
  have hπ : IsBlowupSequence (m + 1) M Y π := hseq.isBlowupSequence
  have hconn : ConnectedSpace Y := BlowupConnected.connectedSpace_of_isBlowupSequence π hπ
  have hsurj : Function.Surjective π :=
    (StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hπ).2
  have : Nonempty Y := ConnectedSpace.toNonempty
  -- the exceptional locus lies in `Supp D₀ = π⁻¹ Z(𝔞)`
  have hExc : exceptionalLocus (m + 1) π ⊆ D.support := by
    intro z hz
    rw [hsupp]
    by_contra hzc
    exact disjoint_left.mp hiso.2 (show z ∈ π ⁻¹' 𝔞.zeroLocusᶜ from hzc) hz
  -- the exceptional divisor of `tok:ext-blowup-kahler`
  obtain ⟨Ex, hExsupp, -, hExK⟩ :=
    TranscendentalLifting.exists_exceptional_kahler_perturbation η hπ
  obtain ⟨δ₀, hδ₀, hδ₀K⟩ := hExK Θ ψ₂ hψ₂.2
  -- `F ≤ N D₀`
  obtain ⟨N, C, hN, hdom⟩ := exists_weight_domination hED (hExsupp.trans hExc)
  -- a rational `δ ∈ (0, δ₀]` with `δN ≤ (1 - a)c`
  obtain ⟨δ, hδ0, hδlt⟩ := exists_rat_btwn
    (show (0 : ℝ) < min δ₀ ((1 - (a : ℝ)) * (c : ℝ) / N) by
      refine lt_min hδ₀ (div_pos (mul_pos (by linarith) hcR) hN))
  have hδR : (0 : ℝ) < (δ : ℝ) := hδ0
  have hδq : (0 : ℚ) ≤ δ := by exact_mod_cast hδR.le
  have hδle : (δ : ℝ) ≤ δ₀ := hδlt.le.trans (min_le_left _ _)
  have hcoef : (a : ℝ) * (c : ℝ) + (δ : ℝ) * N ≤ (c : ℝ) := by
    have h1 : (δ : ℝ) < (1 - (a : ℝ)) * (c : ℝ) / N := hδlt.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ hN] at h1
    linarith
  -- `π^*Θ - δΘ_F + dd^c(ψ₂ ∘ π)` is a Kähler current with log singularities along `acD₀`
  have hT := hδ₀K (δ : ℝ) hδR hδle
  have hac : (0 : ℚ) ≤ a * c := (mul_pos ha hc).le
  let L₂ : ResidualNefReduction.HasLogSingularitiesAlong (MeteredDivisorScaling.smul hac ED)
      (fun z => ψ₂ (π z)) :=
    { residual := fun z => (a : ℝ) * L.residual z
      bound := (a : ℝ) * L.bound
      residual_bound := fun z => by
        rw [abs_mul, abs_of_pos haR]
        exact mul_le_mul_of_nonneg_left (L.residual_bound z) haR.le
      weight_add := fun z => by
        have e1 : ψ₁ (π z) = ((c : ℝ) : EReal) * ED.weight z + (L.residual z : EReal) :=
          L.weight_add z
        show ((a : ℝ) : EReal) * ψ₁ (π z) =
          (((a * c : ℚ) : ℝ) : EReal) * ED.weight z + (((a : ℝ) * L.residual z : ℝ) : EReal)
        rw [e1, EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr haR.le)
          (EReal.coe_ne_top _), ← mul_assoc, ← EReal.coe_mul, ← EReal.coe_mul, Rat.cast_mul] }
  obtain ⟨h, hh, hA⟩ := TranscendentalLifting.exists_kahlerForm_of_logSingularities hT L₂
  -- the divisor `D' = acD₀ + δF` and the weight `Φ = ψ_{D'} + h`
  set D' : MeteredEffectiveQDivisor (m + 1) Y :=
    MeteredDivisorOperations.add (MeteredDivisorScaling.smul hac ED)
      (MeteredDivisorScaling.smul hδq Ex) with hD'_def
  have hD'w : ∀ z, D'.weight z = (((a : ℝ) * (c : ℝ) : ℝ) : EReal) * ED.weight z +
      ((δ : ℝ) : EReal) * Ex.weight z := fun z => by
    show (((a * c : ℚ) : ℝ) : EReal) * ED.weight z + ((δ : ℝ) : EReal) * Ex.weight z = _
    rw [Rat.cast_mul]
  have hD'c : D'.curvature =
      (MeteredDivisorScaling.smul hac ED).curvature + (δ : ℝ) • Ex.curvature := rfl
  set Aform : ClosedRealOneOneForm (m + 1) Y :=
    (ClosedRealOneOneForm.pullback hπ.contMDiff Θ - D'.curvature) + ddcClosedForm h hh
    with hAform_def
  have hAK : Aform.val.IsKahler := by
    have hAeq : Aform = ((ClosedRealOneOneForm.pullback hπ.contMDiff Θ - (δ : ℝ) • Ex.curvature) -
        (MeteredDivisorScaling.smul hac ED).curvature) + ddcClosedForm h hh := by
      rw [hAform_def, hD'c]
      abel
    rw [hAeq]
    exact hA
  set Φ : Y → EReal := fun z => D'.weight z + (h z : EReal) with hΦ_def
  -- bounds
  obtain ⟨H, hH⟩ : ∃ H : ℝ, ∀ z, |h z| ≤ H := by
    have hcont : Continuous fun z => |h z| := (ProductTestForms.ChartSmooth.continuous hh).abs
    obtain ⟨z₀, -, hz₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hcont.continuousOn
    exact ⟨_, fun z => hz₀ (mem_univ z)⟩
  obtain ⟨KD, hKD⟩ := MeteredDivisorScaling.exists_forall_weight_le ED
  obtain ⟨KF, hKF⟩ := MeteredDivisorScaling.exists_forall_weight_le Ex
  have hExtop : ∀ z, Ex.weight z ≠ ⊤ := fun z => ne_top_of_le_ne_top (EReal.coe_ne_top KF) (hKF z)
  have hEDtop : ∀ z, ED.weight z ≠ ⊤ := fun z => ne_top_of_le_ne_top (EReal.coe_ne_top KD) (hKD z)
  -- `ψ₁ ∘ π ≤ Φ + C₁`
  set C₁ : ℝ := L.bound + (δ : ℝ) * |C| + ((c : ℝ) - (a : ℝ) * (c : ℝ) - (δ : ℝ) * N) * |KD| + H
  have hlow : ∀ z, ψ₁ (π z) ≤ Φ z + (C₁ : EReal) := fun z => by
    have e1 : ψ₁ (π z) = ((c : ℝ) : EReal) * ED.weight z + (L.residual z : EReal) :=
      L.weight_add z
    rw [e1, hΦ_def]
    simp only
    rw [hD'w z]
    exact lower_aux hcR hδR hcoef (hKD z) (hExtop z) (hdom z) (L.residual_bound z) (hH z)
  -- `Φ ≤ ψ₂ ∘ π + C₂`
  set C₂ : ℝ := (δ : ℝ) * |KF| + H + (a : ℝ) * L.bound
  have hup : ∀ z, Φ z ≤ ψ₂ (π z) + (C₂ : EReal) := fun z => by
    have e1 : ψ₁ (π z) = ((c : ℝ) : EReal) * ED.weight z + (L.residual z : EReal) :=
      L.weight_add z
    rw [hΦ_def, hψ₂_def]
    simp only
    rw [hD'w z, e1]
    exact upper_aux hcR haR hδR (hEDtop z) (hKF z) (L.residual_bound z) (hH z)
  -- `Φ` is `π^*Θ`-psh: `π^*Θ + dd^c Φ = A + [D'] ≥ 0`
  have hwpsh := MeteredDivisorPositivity.thetaPlurisubharmonic_weight D'
  let Akb : KahlerBackground (m + 1) Y := ⟨Aform, hAK⟩
  have hw1 := LocalPotentials.thetaPlurisubharmonic_add_of_semipositive hwpsh Akb.isSemipositive
  have hneg : ChartSmooth (n := m + 1) (fun z => -h z) := fun e => (hh e).neg
  have hΦpsh' : ThetaPlurisubharmonic (ClosedRealOneOneForm.pullback hπ.contMDiff Θ).val
      (fun z => D'.weight z - (((fun z => -h z) z : ℝ) : EReal)) := by
    refine GlobalPotentialTransforms.thetaPlurisubharmonic_sub_smooth hneg
      (fun e z hz => ?_) hw1
    show (ClosedRealOneOneForm.pullback hπ.contMDiff Θ).val.coeff e z =
      (D'.curvature + Aform).val.coeff e z + smoothDDC (fun y => -h (e.val.symm y)) z
    rw [smoothDDC_neg e.val.open_target (hh e) hz, hAform_def, ClosedRealOneOneForm.coeff_add,
      ClosedRealOneOneForm.coeff_add, BlowupBigPullback.coeff_sub, ddcClosedForm_coeff]
    abel
  have hΦfun : (fun z => D'.weight z - (((fun z => -h z) z : ℝ) : EReal)) = Φ := by
    funext z
    rw [hΦ_def]
    simp only
    rw [sub_eq_add_neg, EReal.coe_neg, neg_neg]
  rw [hΦfun] at hΦpsh'
  -- `Φ` is not identically `-∞`
  have hΦne : ∃ z, Φ z ≠ ⊥ := by
    obtain ⟨x₀⟩ : Nonempty M := ConnectedSpace.toNonempty
    obtain ⟨x, -, hx⟩ := hψpsh.2 x₀ univ isOpen_univ (mem_univ x₀)
    obtain ⟨z, rfl⟩ := hsurj x
    refine ⟨z, fun hz => hx ?_⟩
    have h1 := hlow z
    rw [hz, EReal.bot_add] at h1
    exact le_bot_iff.mp h1
  have hΦpot : IsThetaPshPotential (ClosedRealOneOneForm.pullback hπ.contMDiff Θ).val Φ :=
    ⟨hΦpsh', ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot hΦpsh' hΦne⟩
  -- descent
  obtain ⟨Ψ, hΨ, hΨπ⟩ := TranscendentalLifting.exists_descent hmod Θ hΦpot
  refine ⟨Ψ, hΨ, ?_, ⟨ψ₂, hψ₂, ?_⟩, Y, tY, cY, mY, π, hπ, D', h, hh, hcpt, hconn, ?_, hΨπ, hAK⟩
  · refine (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨C₁, fun x => ?_⟩
    obtain ⟨z, rfl⟩ := hsurj x
    rw [hΨπ z]
    exact hlow z
  · refine (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨C₂, fun x => ?_⟩
    obtain ⟨z, rfl⟩ := hsurj x
    rw [hΨπ z]
    exact hup z
  · intro z hz
    have hzD : ED.weight z = ⊥ := by
      have : z ∈ ED.support := by rw [hEDs]; exact hExc hz
      exact this
    show D'.weight z = ⊥
    rw [hD'w z, hzD, EReal.coe_mul_bot_of_pos (mul_pos haR hcR), EReal.bot_add]

/-! ### `PerturbedWeightStatement` -/

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- **`tok-wn-conv7:weight-perturbation`** (WN21 §7, first paragraph, with the rescaling
`ψ ↦ (1 - s)ψ`): `PerturbedWeightStatement F` holds. The weight `ψ₁ ∈ Ω(θ̃ + εη')` with
`ũ ≤ ψ₁` is `exists_gentle_ge_thetaPshSupremum` (`tok:sing-decrease`); the rest is
`exists_perturbedWeight_of_mem_gentleKahlerCurrents`. -/
theorem perturbedWeight : PerturbedWeightStatement F := by
  intro E hE hE0 𝒳 _ _ _ μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc η' ε hε
  set θ₀ := deformationForm F hμ.contMDiff θ b c Eℰ with hθ₀
  have := compactSpace_normalCone F hμ
  have := connectedSpace_normalCone F hμ
  obtain ⟨hbig, -, -, -⟩ := betaBig F E hE 𝒳 μ hμ Eℰ hEℰ.isDivisorMetric θ b c hc
    (by linarith) hξ hξc.1
  have hbigC : IsBigClass (RealBottChern.ofRepresentative θ₀) :=
    (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp hbig
  have hV : IsThetaPshPotential θ₀.val (thetaPshSupremum θ₀.val) :=
    MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum θ₀ hbigC
  obtain ⟨ψ₁, hψ₁, hle⟩ := exists_gentle_ge_thetaPshSupremum hV η' hε
  obtain ⟨Ψ, hΨ, hψ₁Ψ, hψ₂, hrest⟩ := exists_perturbedWeight_of_mem_gentleKahlerCurrents η' hψ₁
  refine ⟨Ψ, hΨ, SGPT.PSH.singularityLE_trans ?_ hψ₁Ψ, hψ₂, hrest⟩
  refine (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨0, fun z => ?_⟩
  rw [EReal.coe_zero, add_zero]
  exact hle z

/-! ### The remaining input of the analytic core of WN21 §7 -/

/-- **`tok-wn-pw:fibre-reduction`, first half**: the analytic core
`ContactMassLimitStatement F` (`tok-wn-conv7:contact-limit`) follows from the fibre limit
`FibreLimitStatement F` alone (conditional: `FibreLimitStatement F` is open). -/
theorem contactMassLimit_of_fibreLimit (hL : FibreLimitStatement F) :
    ContactMassLimitStatement F :=
  contactMassLimit_of_perturbedWeight_of_fibreLimit F (perturbedWeight F) hL

/-- **`tok-wn-pw:fibre-reduction`, second half**: `tok-wn:convergence`
(`KeyConvergenceStatement F`) follows from measure control (WN21 §6) and the fibre limit
(conditional on both). -/
theorem keyConvergence_of_measureControl_of_fibreLimit (hMC : MeasureControlStatement F)
    (hL : FibreLimitStatement F) : KeyConvergenceStatement F :=
  keyConvergence_of_perturbedWeight_of_fibreLimit F hMC (perturbedWeight F) hL

end SGPT.Okounkov.TranscendentalWN
