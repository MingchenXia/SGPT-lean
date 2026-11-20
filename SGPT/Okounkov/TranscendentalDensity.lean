import SGPT.Okounkov.TranscendentalDensityStatement
import SGPT.Okounkov.TranscendentalDensityNormalize
import SGPT.Okounkov.TranscendentalCoreValuationBounded
import SGPT.Okounkov.TranscendentalCoreGentleSum
import SGPT.Okounkov.TranscendentalBodySingDecrease
import SGPT.Okounkov.TranscendentalBodyConvex
import SGPT.Foundations.Analysis.Pending.IEnvelopeOrder
import SGPT.Foundations.Analysis.Pending.RelativePreceqClasses

/-!
# Gentle Kähler currents are dense for the valuation

Source: blueprint nodes `tok:density` (DRWNXZ Lemma 3.1 and Definition 3.2) and
`tok:partial-analytic` (DRWNXZ Lemma 5.3), chapter `claude-okounkov-transcendental`.

All results of this file take Skoda's theorem, in the manifold form
`SGPT.Okounkov.TranscendentalSkoda.ManifoldSkodaStatement` of the SKODA package, as the explicit
hypothesis `hS`. The SKODA package proves it (`manifoldSkodaStatement`); the unconditional
theorems are in `TranscendentalDensityTheorem.lean`.

## The route (`tok:density`)

Let `T = θ + dd^c φ ∈ 𝒜(ξ)` and `S ∈ Ω(ξ)`. The current `(1 - t)T + tS` (`t ∈ ℚ ∩ (0, 1)`) is a
Kähler current in `𝒜(ξ)` of valuation `(1 - t)ν(T) + tν(S)`, so one may assume `T` Kähler. Some
integer multiple `Φ = Nφ` is `log ∑ |gᵢ|² + O(1)` near every point
(`exists_nat_unitLogPresentedAt`). Let `v_j` be the gentle approximations of `Φ`
(`tok:sing-decrease` (a), types `(1/K, 𝓘(KΦ))`, `K = 2^{j+1}`) and `w = v_{j₁}` the one of level
`m = 2^{j₁ + 1} ≥ n`. For `K > m`, Skoda's theorem gives `v_j = (k/K) Φ + (m/K) w + O(1)`,
`k = K - m` (`sameSingularityTypeAt_of_manifoldSkoda`), hence (the valuation only depends on the
multiplier-ideal class and is linear) `ν(v_j) = (1 - m/K) ν(Φ) + (m/K) ν(w) → ν(Φ)`
(`exists_gentle_approximants`). Rescaling by `1/N` gives elements of `Ω(ξ)`.

Adaptation (recorded in the blueprint): DRWNXZ use `m = n - 1` and a global potential `ψ` of the
multiplier ideal `𝓘(mφ)` (`tok:ideal-potential`); here `m = 2^{j₁+1} ≥ n` (the published
Skoda statement is for `m ≥ n`; one fixed `m` suffices) and `ψ = m w` is itself a term of the
approximation, so `tok:ideal-potential` is not needed by the route.

## `tok:partial-analytic`

For `G = θ + dd^c φ ∈ 𝒜(ξ; R)`, `R = θ + dd^c u` a Kähler current in `𝒜(ξ)`: replace `G` by
`(1 - t)G + tR` (Kähler, still `⪯ R`), then by `φ + δu` (Kähler for small `δ`, of valuation
`ν(G) + δν(R)`, with `φ + δu ⪯ (1 + δ)u`). Its gentle approximants satisfy
`v ≤ a (φ + δu) + O(1)` with `a ≥ 1/(1 + δ)` (`exists_gentle_approximant_near`), so
`v ≤ a(1 + δ)u + O(1) ≤ u + O(1)` (`u` is bounded above), i.e. `v ∈ Ω(ξ; R)`.

## Main results

* `exists_gentle_approximants`, `exists_gentle_approximant_near`: the approximation of a
  normalized Kähler potential.
* `flagValuation_mem_closure_gentleKahlerCurrents`: `tok:density` (conditional on Skoda).
* `densityStatement_of_manifoldSkoda : ManifoldSkodaStatement → DensityStatement`.
* `tradOkounkovBody_eq_closure_gentleKahler`, `tradOkounkovBody_eq_closure_analytic`,
  `bodyEqualityStatement_of_manifoldSkoda`: `Δ(ξ) = closure ν(Ω(ξ)) = closure ν(𝒜(ξ))`.
* `closure_gentleKahlerCurrentsBelow_eq`, `partialAnalyticStatement_of_manifoldSkoda`:
  `tok:partial-analytic` (conditional on Skoda).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalDensity

open Set Filter
open scoped Topology NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.IdealWeightComparison
open SGPT.PSH SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalSkoda

/-! ### The singularity order -/

section Order

variable {X : Type*}

/-- `φ ⪯ ψ` is preserved by nonnegative scalars. -/
theorem singularityLE_smul {φ ψ : X → EReal} (h : SingularityLE φ ψ) {a : ℝ} (ha : 0 ≤ a) :
    SingularityLE (fun x => (a : EReal) * φ x) (fun x => (a : EReal) * ψ x) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨a * C, fun x hx => ?_⟩
  calc (a : EReal) * φ x ≤ (a : EReal) * (ψ x + (C : EReal)) :=
        monotone_eReal_const_mul ha (hC x hx)
    _ = (a : EReal) * ψ x + ((a * C : ℝ) : EReal) := by
        rw [EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr ha)
          (EReal.coe_ne_top _), EReal.coe_mul]

/-- `φ ⪯ ψ` and `φ' ⪯ ψ'` give `φ + φ' ⪯ ψ + ψ'`. -/
theorem singularityLE_add {φ ψ φ' ψ' : X → EReal} (h : SingularityLE φ ψ)
    (h' : SingularityLE φ' ψ') :
    SingularityLE (fun x => φ x + φ' x) (fun x => ψ x + ψ' x) := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨C', hC'⟩ := h'
  refine ⟨C + C', fun x hx => ?_⟩
  calc φ x + φ' x ≤ (ψ x + (C : EReal)) + (ψ' x + (C' : EReal)) := add_le_add (hC x hx) (hC' x hx)
    _ = (ψ x + ψ' x) + ((C + C' : ℝ) : EReal) := by
        rw [EReal.coe_add]
        exact add_add_add_comm _ _ _ _

/-- A pointwise inequality is a singularity comparison. -/
theorem singularityLE_of_le {φ ψ : X → EReal} (h : ∀ x, φ x ≤ ψ x) : SingularityLE φ ψ :=
  ⟨0, fun x _ => by simpa using h x⟩

/-- A pointwise equality is a singularity comparison. -/
theorem singularityLE_of_eq {φ ψ : X → EReal} (h : ∀ x, φ x = ψ x) : SingularityLE φ ψ :=
  singularityLE_of_le fun x => (h x).le

/-- If `u ≤ M` then `s u ⪯ u` for `s ≥ 1`. -/
theorem singularityLE_smul_self {u : X → EReal} {M : ℝ} (hM : ∀ x, u x ≤ (M : EReal)) {s : ℝ}
    (hs : 1 ≤ s) : SingularityLE (fun x => (s : EReal) * u x) u := by
  refine ⟨(s - 1) * |M|, fun x _ => ?_⟩
  show (s : EReal) * u x ≤ u x + (((s - 1) * |M| : ℝ) : EReal)
  have hux := hM x
  revert hux
  induction u x using EReal.rec with
  | bot =>
      intro _
      rw [EReal.coe_mul_bot_of_pos (by linarith)]
      exact bot_le
  | top => intro hux; exact absurd hux (by simp)
  | coe r =>
      intro hux
      have hr : r ≤ M := EReal.coe_le_coe_iff.mp hux
      rw [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have h1 : (s - 1) * r ≤ (s - 1) * |M| :=
        mul_le_mul_of_nonneg_left (hr.trans (le_abs_self M)) (by linarith)
      linarith

end Order

/-! ### The approximation of a normalized Kähler potential -/

section Approximation

variable {n : ℕ} (F : OriginalFlagGeometry.{u} n)

/-- **The gentle approximants of a normalized Kähler potential** (the computation of
`tok:density`, conditional on Skoda's theorem). Let `θ + dd^c Φ ≥ κ` with
`Φ = log ∑ |gᵢ|² + O(1)` near every point. There are `m > 0`, a quasi-psh `w` and potentials
`v_j` such that for all large `j`: `m < 2^{j+1}`, `v_j ∈ Ω(θ)`,
`ν(v_j) = (1 - β_j) ν(Φ) + β_j ν(w)` and `v_j ≤ (1 - β_j) Φ + O(1)`, where `β_j = m / 2^{j+1}`. -/
theorem exists_gentle_approximants (hS : ManifoldSkodaStatement.{u}) (hn : 0 < n)
    {θ : ClosedRealOneOneForm n F.carrier} {κ : KahlerBackground n F.carrier}
    {Φ : F.carrier → EReal} (hΦ : IsThetaPshPotential (θ - κ.form).val Φ)
    (hpres : ∀ x, UnitLogPresentedAt (n := n) Φ x) :
    ∃ (m : ℕ) (w : F.carrier → EReal) (σ : ClosedRealOneOneForm n F.carrier)
      (v : ℕ → F.carrier → EReal) (j₀ : ℕ), 0 < m ∧ IsThetaPshPotential σ.val w ∧
      ∀ j, j₀ ≤ j → v j ∈ gentleKahlerCurrents θ ∧
        flagValuation F (v j) = (1 - (m : ℝ) / 2 ^ (j + 1)) • flagValuation F Φ +
          ((m : ℝ) / 2 ^ (j + 1)) • flagValuation F w ∧
        ∃ C : ℝ, ∀ y, v j y ≤ (((1 - (m : ℝ) / 2 ^ (j + 1) : ℝ)) : EReal) * Φ y + (C : EReal) := by
  obtain ⟨v, -, hgentle, j₀, hj₀⟩ :=
    TranscendentalBody.exists_gentle_approximation_of_kahlerCurrent hΦ
  have hnm : n ≤ 2 ^ (n + 1) :=
    (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n))
  obtain ⟨⟨σ, hσ⟩, hwg⟩ := hgentle n
  refine ⟨2 ^ (n + 1), v n, σ, v, max j₀ (n + 1), by positivity, hσ, fun j hj => ?_⟩
  set m : ℕ := 2 ^ (n + 1) with hm
  set w := v n with hw
  have hjn : n + 1 ≤ j := le_of_max_le_right hj
  have hj0 : j₀ ≤ j := le_of_max_le_left hj
  have hmK : m < 2 ^ (j + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  set k : ℕ := 2 ^ (j + 1) - m with hkdef
  have hkm : k + m = 2 ^ (j + 1) := Nat.sub_add_cancel hmK.le
  have hk : 0 < k := Nat.sub_pos_of_lt hmK
  have hvtype : HasAnalyticSingularitiesOfType (n := n) (v j) (((k + m : ℕ) : ℚ)⁻¹)
      (multiplierIdeal (n := n) ((k + m : ℕ) : ℝ) Φ) := by
    rw [hkm]
    exact (hgentle j).2.2.1
  have hwtype : HasAnalyticSingularitiesOfType (n := n) w (((m : ℕ) : ℚ)⁻¹)
      (multiplierIdeal (n := n) (m : ℝ) Φ) := hwg.2.1
  -- the coefficients
  set a : ℝ := (k : ℝ) / ((k + m : ℕ) : ℝ) with ha
  set b : ℝ := (m : ℝ) / ((k + m : ℕ) : ℝ) with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hKcast : ((k + m : ℕ) : ℝ) = (2 : ℝ) ^ (j + 1) := by rw [hkm]; push_cast; ring
  have hkcast : (k : ℝ) = (2 : ℝ) ^ (j + 1) - m := by
    have : ((k + m : ℕ) : ℝ) = (k : ℝ) + m := by push_cast; ring
    linarith
  have hbeq : b = (m : ℝ) / 2 ^ (j + 1) := by rw [hb, hKcast]
  have haeq : a = 1 - (m : ℝ) / 2 ^ (j + 1) := by
    rw [ha, hKcast, hkcast]
    field_simp
  -- the local comparisons and their globalization
  have hloc : ∀ x, SameSingularityTypeAt (v j)
      (fun y => (a : EReal) * Φ y + (b : EReal) * w y) x := fun x => by
    obtain ⟨U₀, hU₀, hx₀, r, g, hg, R₀, C₀, hR₀, hΦeq⟩ := hpres x
    exact sameSingularityTypeAt_of_manifoldSkoda hS hn hΦ.quasiPshPotential.1 hU₀ hx₀ hg hR₀
      hΦeq hk hnm hvtype hwtype
  obtain ⟨C₁, hC₁⟩ := moreSingularOn_univ_of_forall_moreSingularAt fun x => (hloc x).1
  obtain ⟨C₂, hC₂⟩ := moreSingularOn_univ_of_forall_moreSingularAt fun x => (hloc x).2
  -- membership in `Ω(θ)`
  have hvj := hj₀ j hj0
  have hquarter : (0 : ℝ) < 1 / 4 := by norm_num
  have hvθ : IsThetaPshPotential θ.val (v j) := by
    refine TranscendentalBody.isThetaPshPotential_of_le hvj ?_
    have heq : θ - (θ - (1 / 4 : ℝ) • κ.form) = (1 / 4 : ℝ) • κ.form := by abel
    rw [heq]
    exact KahlerDomination.isSemipositive_smul κ.isSemipositive hquarter.le
  have hmem : v j ∈ gentleKahlerCurrents θ :=
    ⟨⟨hvθ, _, _, hgentle j⟩, KahlerBackground.smul hquarter κ, by
      simpa only [KahlerBackground.smul_form] using hvj⟩
  -- the comparison potential is quasi-psh
  have hcombo := isThetaPshPotential_add_from_positive_sum
    (isThetaPshPotential_nonneg_smul hΦ ha0) (isThetaPshPotential_nonneg_smul hσ hb0)
  have hI : IEquivalentOnManifold (n := n) (v j)
      (fun y => (a : EReal) * Φ y + (b : EReal) * w y) :=
    ⟨iOrderOnManifold_of_le_add hcombo.quasiPshPotential.1 fun x => hC₁ x (mem_univ x),
      iOrderOnManifold_of_le_add hvθ.quasiPshPotential.1 fun x => hC₂ x (mem_univ x)⟩
  refine ⟨hmem, ?_, ?_⟩
  · rw [flagValuation_eq_of_iEquivalent hvθ hcombo hI, flagValuation_add_smul hΦ hσ ha0 hb0,
      haeq, hbeq]
  · obtain ⟨M, hM⟩ := RelativePreceqClasses.exists_le_coe_of_isThetaPshPotential hσ
    refine ⟨C₁ + b * M, fun y => ?_⟩
    calc v j y ≤ ((a : EReal) * Φ y + (b : EReal) * w y) + (C₁ : EReal) := hC₁ y (mem_univ y)
      _ ≤ ((a : EReal) * Φ y + ((b * M : ℝ) : EReal)) + (C₁ : EReal) := by
          gcongr
          rw [EReal.coe_mul]
          exact monotone_eReal_const_mul hb0 (hM y)
      _ = (((1 - (m : ℝ) / 2 ^ (j + 1) : ℝ)) : EReal) * Φ y + ((C₁ + b * M : ℝ) : EReal) := by
          rw [haeq, add_assoc, ← EReal.coe_add, add_comm (b * M)]

/-- **A gentle approximant with valuation `ε`-close to `ν(Φ)`** (conditional on Skoda's
theorem): for a normalized Kähler potential `Φ` and `ε > 0` there is `v ∈ Ω(θ)` with
`dist(ν(v), ν(Φ)) < ε` and `v ≤ aΦ + O(1)` for some `a ∈ [1 - ε, 1]`. -/
theorem exists_gentle_approximant_near (hS : ManifoldSkodaStatement.{u}) (hn : 0 < n)
    {θ : ClosedRealOneOneForm n F.carrier} {κ : KahlerBackground n F.carrier}
    {Φ : F.carrier → EReal} (hΦ : IsThetaPshPotential (θ - κ.form).val Φ)
    (hpres : ∀ x, UnitLogPresentedAt (n := n) Φ x) {ε : ℝ} (hε : 0 < ε) :
    ∃ v ∈ gentleKahlerCurrents θ, dist (flagValuation F v) (flagValuation F Φ) < ε ∧
      ∃ a : ℝ, 1 - ε ≤ a ∧ a ≤ 1 ∧ ∃ C : ℝ, ∀ y, v y ≤ (a : EReal) * Φ y + (C : EReal) := by
  obtain ⟨m, w, σ, v, j₀, hm, -, hv⟩ := exists_gentle_approximants F hS hn hΦ hpres
  set L := ‖flagValuation F w - flagValuation F Φ‖ with hL
  have hL0 : 0 ≤ L := norm_nonneg _
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((m : ℝ) * (L + 1) / ε)
  set j := max j₀ N₀ with hj
  obtain ⟨hvmem, hval, C, hC⟩ := hv j (le_max_left _ _)
  have hpow : (N₀ : ℝ) < (2 : ℝ) ^ (j + 1) := by
    have h1 : N₀ < 2 ^ (j + 1) :=
      (le_max_right j₀ N₀).trans_lt ((Nat.lt_two_pow_self).trans
        (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self j)))
    exact_mod_cast h1
  set β : ℝ := (m : ℝ) / 2 ^ (j + 1) with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hβL : β * (L + 1) < ε := by
    have h2 : (0 : ℝ) < 2 ^ (j + 1) := by positivity
    have h3 : (m : ℝ) * (L + 1) / ε < 2 ^ (j + 1) := hN₀.trans hpow
    rw [div_lt_iff₀ hε] at h3
    rw [hβ, div_mul_eq_mul_div, div_lt_iff₀ h2]
    linarith
  refine ⟨v j, hvmem, ?_, 1 - β, ?_, by linarith, C, hC⟩
  · rw [dist_eq_norm, hval]
    have : (1 - β) • flagValuation F Φ + β • flagValuation F w - flagValuation F Φ =
        β • (flagValuation F w - flagValuation F Φ) := by module
    rw [this, norm_smul, Real.norm_of_nonneg hβ0, ← hL]
    nlinarith
  · nlinarith

end Approximation

/-! ### Rescaling gentle Kähler currents -/

section Rescale

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X] [ConnectedSpace X]

/-- `aT ∈ Ω(aξ)` for `T ∈ Ω(ξ)` and `a ∈ ℚ_{>0}`. -/
theorem smul_mem_gentleKahlerCurrents {θ : ClosedRealOneOneForm n X} {φ : X → EReal}
    (hφ : φ ∈ gentleKahlerCurrents θ) {a : ℚ} (ha : 0 < a) :
    (fun x => ((a : ℝ) : EReal) * φ x) ∈ gentleKahlerCurrents ((a : ℝ) • θ) := by
  have h := add_smul_mem_gentleKahlerCurrents hφ hφ.1 ha (le_refl (0 : ℚ))
  have hfun : (fun x => ((a : ℝ) : EReal) * φ x + (((0 : ℚ) : ℝ) : EReal) * φ x) =
      fun x => ((a : ℝ) : EReal) * φ x := by
    funext x
    simp
  have hform : (a : ℝ) • θ + ((0 : ℚ) : ℝ) • θ = (a : ℝ) • θ := by simp
  rwa [hfun, hform] at h

end Rescale

/-! ### Density -/

section Density

variable {n : ℕ} (F : OriginalFlagGeometry.{u} n)

/-- The convex combination `(1 - t)φ + tψ` of a `θ`-psh `φ` and a Kähler potential `ψ`
(`θ + dd^c ψ ≥ κ`) is a Kähler potential (`θ + dd^c ≥ tκ`). -/
theorem isThetaPshPotential_convex_kahler {θ : ClosedRealOneOneForm n F.carrier}
    {κ : KahlerBackground n F.carrier} {φ ψ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hψ : IsThetaPshPotential (θ - κ.form).val ψ)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    IsThetaPshPotential (θ - (KahlerBackground.smul ht κ).form).val
      (fun x => ((1 - t : ℝ) : EReal) * φ x + (t : EReal) * ψ x) := by
  have h := isThetaPshPotential_add_from_positive_sum
    (isThetaPshPotential_nonneg_smul hφ (by linarith : (0 : ℝ) ≤ 1 - t))
    (isThetaPshPotential_nonneg_smul hψ ht.le)
  have hform : (1 - t) • θ + t • (θ - κ.form) = θ - (KahlerBackground.smul ht κ).form := by
    rw [KahlerBackground.smul_form]
    module
  rwa [hform] at h

/-- **`tok:density` for Kähler currents with analytic singularities** (conditional on Skoda's
theorem): if `θ + dd^c φ ≥ κ` and `φ` has analytic singularities, then
`ν(φ) ∈ closure ν(Ω(θ))`. -/
theorem flagValuation_mem_closure_of_kahler (hS : ManifoldSkodaStatement.{u}) (hn : 0 < n)
    {θ : ClosedRealOneOneForm n F.carrier} {κ : KahlerBackground n F.carrier}
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential (θ - κ.form).val φ)
    (hφA : HasManifoldAnalyticSingularityType (n := n) φ) :
    flagValuation F φ ∈ closure (flagValuation F '' gentleKahlerCurrents θ) := by
  obtain ⟨N, hN, hpres⟩ := exists_nat_unitLogPresentedAt hφA
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hΦ : IsThetaPshPotential ((N : ℝ) • θ - (KahlerBackground.smul hNR κ).form).val
      (fun y => ((N : ℝ) : EReal) * φ y) := by
    have h := isThetaPshPotential_nonneg_smul hφ hNR.le
    have hform : (N : ℝ) • (θ - κ.form) = (N : ℝ) • θ - (KahlerBackground.smul hNR κ).form := by
      rw [KahlerBackground.smul_form, smul_sub]
    rwa [hform] at h
  have hνΦ : flagValuation F (fun y => ((N : ℝ) : EReal) * φ y) =
      (N : ℝ) • flagValuation F φ := flagValuation_smul hφ hNR.le
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨v, hv, hdist, -⟩ := exists_gentle_approximant_near F hS hn hΦ hpres
    (by positivity : (0 : ℝ) < N * ε)
  have hNQ : (0 : ℚ) < ((N : ℚ))⁻¹ := by positivity
  have hv' := smul_mem_gentleKahlerCurrents hv hNQ
  have hform : (((N : ℚ)⁻¹ : ℚ) : ℝ) • ((N : ℝ) • θ) = θ := by
    rw [smul_smul]
    push_cast
    rw [inv_mul_cancel₀ hNR.ne', one_smul]
  rw [hform] at hv'
  refine ⟨_, ⟨_, hv', rfl⟩, ?_⟩
  have hvθ : IsThetaPshPotential ((N : ℝ) • θ).val v := hv.1.1
  rw [flagValuation_smul hvθ (by positivity), dist_comm, dist_eq_norm]
  have hsub : ((((N : ℚ)⁻¹ : ℚ) : ℝ)) • flagValuation F v - flagValuation F φ =
      ((N : ℝ))⁻¹ • (flagValuation F v - flagValuation F (fun y => ((N : ℝ) : EReal) * φ y)) := by
    rw [hνΦ, smul_sub, smul_smul, inv_mul_cancel₀ hNR.ne', one_smul]
    push_cast
    rfl
  rw [hsub, norm_smul, Real.norm_of_nonneg (by positivity), ← dist_eq_norm]
  calc ((N : ℝ))⁻¹ * dist (flagValuation F v) (flagValuation F fun y => ((N : ℝ) : EReal) * φ y)
      < ((N : ℝ))⁻¹ * (N * ε) := mul_lt_mul_of_pos_left hdist (by positivity)
    _ = ε := by field_simp

/-- **`tok:density`** (DRWNXZ Lemma 3.1; conditional on Skoda's theorem
`ManifoldSkodaStatement`): if `Ω(ξ) ≠ ∅` (e.g. `ξ` big), then `ν(T) ∈ closure ν(Ω(ξ))` for every
`T ∈ 𝒜(ξ)`. -/
theorem flagValuation_mem_closure_gentleKahlerCurrents (hS : ManifoldSkodaStatement.{u})
    {θ : ClosedRealOneOneForm n F.carrier} (hne : (gentleKahlerCurrents θ).Nonempty)
    {φ : F.carrier → EReal} (hφ : φ ∈ analyticCurrents θ) :
    flagValuation F φ ∈ closure (flagValuation F '' gentleKahlerCurrents θ) := by
  obtain ⟨ψ, hψ⟩ := hne
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact subset_closure ⟨ψ, hψ, Subsingleton.elim _ _⟩
  obtain ⟨κ, hκ⟩ := hψ.2
  rw [Metric.mem_closure_iff]
  intro ε hε
  set L := ‖flagValuation F ψ - flagValuation F φ‖ with hL
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 * (L + 1) / ε)
  set t : ℚ := ((N₀ : ℚ) + 1)⁻¹ with ht
  have ht0 : (0 : ℚ) < t := by positivity
  have ht0R : (0 : ℝ) < t := by exact_mod_cast ht0
  have ht1 : (t : ℝ) ≤ 1 := by
    rw [ht]; push_cast
    rw [inv_le_one₀ (by positivity)]
    linarith [(N₀.cast_nonneg : (0 : ℝ) ≤ N₀)]
  have htL : (t : ℝ) * (L + 1) < ε / 2 := by
    have hN : (0 : ℝ) < (N₀ : ℝ) + 1 := by positivity
    have h2 : 2 * (L + 1) / ε < (N₀ : ℝ) + 1 := hN₀.trans (lt_add_one _)
    rw [div_lt_iff₀ hε] at h2
    rw [ht]; push_cast
    rw [inv_mul_eq_div, div_lt_iff₀ hN]
    linarith
  -- the Kähler convex combination
  set φt : F.carrier → EReal := fun x => ((1 - (t : ℝ) : ℝ) : EReal) * φ x + ((t : ℝ) : EReal) * ψ x
    with hφt
  have hφtpsh := isThetaPshPotential_convex_kahler F hφ.1 hκ ht0R ht1
  have hφtA : HasManifoldAnalyticSingularityType (n := n) φt := by
    have h1 := hasManifoldAnalyticSingularityType_nonneg_rat_smul hφ.2
      (show (0 : ℚ) ≤ 1 - t by
        have : (t : ℝ) ≤ 1 := ht1
        exact_mod_cast (show ((1 - t : ℚ) : ℝ) ≥ 0 by push_cast; linarith))
    have h2 := hasManifoldAnalyticSingularityType_nonneg_rat_smul
      (gentleCurrents_subset_analyticCurrents θ hψ.1).2 ht0.le
    have h := hasManifoldAnalyticSingularityType_add h1 h2
    have hfun : (fun x => (((1 - t : ℚ) : ℝ) : EReal) * φ x + ((t : ℝ) : EReal) * ψ x) = φt := by
      funext x
      simp [hφt]
    rwa [hfun] at h
  have hνt : flagValuation F φt = (1 - (t : ℝ)) • flagValuation F φ + (t : ℝ) • flagValuation F ψ :=
    flagValuation_add_smul hφ.1 hψ.1.1 (by linarith) ht0R.le
  obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.mp
    (flagValuation_mem_closure_of_kahler F hS hn hφtpsh hφtA) (ε / 2) (by positivity)
  refine ⟨b, hb, ?_⟩
  have hd1 : dist (flagValuation F φ) (flagValuation F φt) < ε / 2 := by
    rw [dist_comm, dist_eq_norm, hνt]
    have : (1 - (t : ℝ)) • flagValuation F φ + (t : ℝ) • flagValuation F ψ - flagValuation F φ =
        (t : ℝ) • (flagValuation F ψ - flagValuation F φ) := by module
    rw [this, norm_smul, Real.norm_of_nonneg ht0R.le, ← hL]
    nlinarith [norm_nonneg (flagValuation F ψ - flagValuation F φ)]
  calc dist (flagValuation F φ) b ≤ dist (flagValuation F φ) (flagValuation F φt) +
        dist (flagValuation F φt) b := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hd1 hdist
    _ = ε := add_halves ε

/-- `tok:density`, as the published statement (conditional on Skoda's theorem). -/
theorem densityStatement_of_manifoldSkoda (hS : ManifoldSkodaStatement.{u}) :
    DensityStatement.{u} :=
  fun _ F _ hne _ hφ => flagValuation_mem_closure_gentleKahlerCurrents F hS hne hφ

/-- `closure ν(Ω(ξ)) = closure ν(𝒜(ξ))` when `Ω(ξ) ≠ ∅` (conditional on Skoda's theorem). -/
theorem closure_gentleKahler_eq_closure_analytic (hS : ManifoldSkodaStatement.{u})
    {θ : ClosedRealOneOneForm n F.carrier} (hne : (gentleKahlerCurrents θ).Nonempty) :
    closure (flagValuation F '' gentleKahlerCurrents θ) =
      closure (flagValuation F '' analyticCurrents θ) := by
  refine le_antisymm (closure_mono (image_mono ?_)) ?_
  · exact gentleKahlerCurrents_subset_gentleCurrents.trans
      (gentleCurrents_subset_analyticCurrents θ)
  · refine closure_minimal ?_ isClosed_closure
    rintro _ ⟨φ, hφ, rfl⟩
    exact flagValuation_mem_closure_gentleKahlerCurrents F hS hne hφ

/-- `Δ(ξ) = closure ν(Ω(ξ))` when `Ω(ξ) ≠ ∅` (conditional on Skoda's theorem). -/
theorem tradOkounkovBody_eq_closure_gentleKahler (hS : ManifoldSkodaStatement.{u})
    {θ : ClosedRealOneOneForm n F.carrier} (hne : (gentleKahlerCurrents θ).Nonempty) :
    tradOkounkovBody F θ = closure (flagValuation F '' gentleKahlerCurrents θ) := by
  rw [tradOkounkovBody_eq_closure_image]
  refine le_antisymm ?_ (closure_mono (image_mono gentleKahlerCurrents_subset_gentleCurrents))
  rw [closure_gentleKahler_eq_closure_analytic F hS hne]
  exact closure_mono (image_mono (gentleCurrents_subset_analyticCurrents θ))

/-- `Δ(ξ) = closure ν(𝒜(ξ))` when `Ω(ξ) ≠ ∅` (conditional on Skoda's theorem). -/
theorem tradOkounkovBody_eq_closure_analytic (hS : ManifoldSkodaStatement.{u})
    {θ : ClosedRealOneOneForm n F.carrier} (hne : (gentleKahlerCurrents θ).Nonempty) :
    tradOkounkovBody F θ = closure (flagValuation F '' analyticCurrents θ) := by
  rw [tradOkounkovBody_eq_closure_gentleKahler F hS hne,
    closure_gentleKahler_eq_closure_analytic F hS hne]

/-- **`tok:density`, consequence** (DRWNXZ Definition 3.2; conditional on Skoda's theorem): for
a big class, `Δ(ξ) = closure ν(Ω(ξ)) = closure ν(𝒜(ξ))`. -/
theorem bodyEqualityStatement_of_manifoldSkoda (hS : ManifoldSkodaStatement.{u}) :
    BodyEqualityStatement.{u} := fun _ F _ hbig =>
  ⟨tradOkounkovBody_eq_closure_gentleKahler F hS
      (TranscendentalBody.exists_mem_gentleKahlerCurrents_of_isBig hbig),
    tradOkounkovBody_eq_closure_analytic F hS
      (TranscendentalBody.exists_mem_gentleKahlerCurrents_of_isBig hbig)⟩

end Density

end SGPT.Okounkov.TranscendentalDensity
