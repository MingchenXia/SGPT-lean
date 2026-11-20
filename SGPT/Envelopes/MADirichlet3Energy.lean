import SGPT.Envelopes.MADirichletCapacity
import SGPT.Foundations.Analysis.Pending.BedfordTaylorFixedWeight

/-!
# Cegrell's class `ℰ₀` and local energy moments

Xia, *Foundations of pluripotential theory* (FPT), `sec:local-energy-moments`.

* `IsCegrellE0 D φ` is FPT `def:bounded-zero-boundary-energy`, for a bounded open set
  `D ⊆ ℂⁿ` (FPT works on balls; the Dirichlet problems of this series are solved on polydisks):
  bounded plurisubharmonic `φ ≤ 0` on `D` with boundary values `0` and Monge–Ampère measure of
  finite mass. `localEnergy D p φ` is the local energy moment `e_p(φ) = ∫_D (-φ)ᵖ (ddᶜφ)ⁿ`.
* `exists_isCompact_sublevel`: the sublevel sets `{φ ≤ -s}`, `s > 0`, are relatively compact in
  `D` (FPT, remark after the definition).
* `measure_sublevel_le_localEnergy`: the **tail bound** of FPT
  `thm:bounded-subsolution-local-energy-moments`: if `μ ≤ (ddᶜw)ⁿ` on `D` for a plurisubharmonic
  `w` of oscillation `M` on `D`, then `μ({φ < -t}) ≤ 2ⁿ⁺ᵖ Mⁿ e_p(φ) t^{-(n+p)}` for `p > 0`.
  FPT's constant `κ_{n,p} = 2ⁿ⁺ᵖ (n+1)! Mⁿ` is larger (`measure_sublevel_le_kappa`).

  *Proof.* We do not use Błocki's estimate (FPT's route): `μ ≤ (ddᶜw)ⁿ ≤ Mⁿ Cap_D` (TN
  `canonicalBedfordTaylorMeasure_le_relCapacity_of_bounds`), and the capacity of sublevel sets
  (MA-DIR `pow_mul_relCapacity_le`, FPT `lem:local-comparison-capacity-sublevels`, applied to
  `φ` and `0`) gives `(t/2)ⁿ Cap_D({φ < -t}) ≤ (ddᶜφ)ⁿ({φ < -t/2}) ≤ (t/2)⁻ᵖ e_p(φ)`.
* `lintegral_neg_rpow_le`: the **moment bound** `∫_D (-φ)ᵖ dμ ≤ A_p e_p(φ)^{p/(n+p)}` with FPT's
  constant `A_p = (1 + p/n) κ_{n,p}^{p/(n+p)} m^{n/(n+p)}`, `m = μ(D)` (`energyMomentConst`), by
  the layer-cake formula. For `p = 1` this is the **Cegrell–Persson estimate**
  `∫(-φ)(ddᶜw)ⁿ ≤ C e₁(φ)^{1/(n+1)}`.
* `localEnergy_le_of_moment_control`: the **uniform energy bound** of FPT
  `prop:canonical-grid-energy-control` (4): if a solution `U ∈ ℰ₀(D)` satisfies
  `e_p(U) ≤ c ∫(-U)ᵖ dμ` (for approximants of `μ`: the sub-mean value property), then
  `e_p(U) ≤ (c A_p)^{(n+p)/n}`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor

variable {n : ℕ}

/-- **Cegrell's class `ℰ₀(D)`** (FPT `def:bounded-zero-boundary-energy`, on a bounded open set
`D ⊆ ℂⁿ` instead of a ball): bounded plurisubharmonic functions `φ ≤ 0` on `D` with
`φ(z) → 0` as `z → ζ ∈ ∂D` and `∫_D (ddᶜφ)ⁿ < ∞`. -/
structure IsCegrellE0 (D : Opens (ComplexModel n)) (φ : ComplexModel n → ℝ) : Prop where
  psh : IsLocallyBoundedPshOn D φ
  bddBelow : ∃ C : ℝ, ∀ z ∈ D, -C ≤ φ z
  nonpos : ∀ z ∈ D, φ z ≤ 0
  tendsto_frontier : ∀ ζ ∈ frontier (D : Set (ComplexModel n)),
    Tendsto φ (𝓝[(D : Set (ComplexModel n))] ζ) (𝓝 0)
  mass_lt_top : canonicalBedfordTaylorMeasure D φ psh D < ∞

/-- The **local energy moment** `e_p(φ) = ∫_D (-φ)ᵖ (ddᶜφ)ⁿ` (FPT
`def:bounded-zero-boundary-energy`). -/
def localEnergy (D : Opens (ComplexModel n)) (p : ℝ) (φ : ComplexModel n → ℝ)
    (hφ : IsLocallyBoundedPshOn D φ) : ℝ≥0∞ :=
  ∫⁻ z in (D : Set (ComplexModel n)), ENNReal.ofReal ((-φ z) ^ p)
    ∂canonicalBedfordTaylorMeasure D φ hφ

theorem localEnergy_congr {D : Opens (ComplexModel n)} (p : ℝ) {φ : ComplexModel n → ℝ}
    (hφ hφ' : IsLocallyBoundedPshOn D φ) : localEnergy D p φ hφ = localEnergy D p φ hφ' := rfl

/-- **Sublevel sets are relatively compact** (FPT, remark after
`def:bounded-zero-boundary-energy`): for a bounded open `D` and `φ` with boundary values `0`,
the closure of `{z ∈ D : φ z ≤ -s}`, `s > 0`, is a compact subset of `D`. -/
theorem exists_isCompact_sublevel {D : Opens (ComplexModel n)}
    (hDb : Bornology.IsBounded (D : Set (ComplexModel n))) {φ : ComplexModel n → ℝ}
    (hbd : ∀ ζ ∈ frontier (D : Set (ComplexModel n)),
      Tendsto φ (𝓝[(D : Set (ComplexModel n))] ζ) (𝓝 0)) {s : ℝ} (hs : 0 < s) :
    IsCompact (closure {z | z ∈ D ∧ φ z ≤ -s}) ∧
      closure {z | z ∈ D ∧ φ z ≤ -s} ⊆ (D : Set (ComplexModel n)) := by
  set S : Set (ComplexModel n) := {z | z ∈ D ∧ φ z ≤ -s} with hSdef
  have hSD : S ⊆ D := fun z hz => hz.1
  refine ⟨(hDb.subset hSD).isCompact_closure, fun x hx => ?_⟩
  by_contra hxD
  have hfr : x ∈ frontier (D : Set (ComplexModel n)) :=
    ⟨closure_mono hSD hx, by rwa [D.isOpen.interior_eq]⟩
  have h1 : ∀ᶠ z in 𝓝[S] x, -s < φ z :=
    nhdsWithin_mono x hSD ((hbd x hfr).eventually (Ioi_mem_nhds (by linarith)))
  have h2 : ∀ᶠ z in 𝓝[S] x, z ∈ S := self_mem_nhdsWithin
  have := mem_closure_iff_nhdsWithin_neBot.mp hx
  obtain ⟨z, hz1, hz2⟩ := (h1.and h2).exists
  exact absurd hz2.2 (not_le.mpr hz1)

/-- `(ddᶜw)ⁿ ≤ Mⁿ Cap_D` for `a ≤ w ≤ a + M` (TN's diagonal domination, extended to `M = 0` on
sets of finite capacity). -/
theorem ma_le_ofReal_pow_mul_relCapacity {D : Opens (ComplexModel n)} {w : ComplexModel n → ℝ}
    (hw : IsLocallyBoundedPshOn D w) {a M : ℝ} (hM : 0 ≤ M)
    (hwb : ∀ z ∈ D, a ≤ w z ∧ w z ≤ a + M) {E : Set (ComplexModel n)} (hE : relCapacity D E ≠ ∞) :
    canonicalBedfordTaylorMeasure D w hw E ≤ ENNReal.ofReal (M ^ n) * relCapacity D E := by
  have hlim : Tendsto (fun M' : ℝ => ENNReal.ofReal (M' ^ n) * relCapacity D E) (𝓝[>] M)
      (𝓝 (ENNReal.ofReal (M ^ n) * relCapacity D E)) :=
    ENNReal.Tendsto.mul_const
      (((ENNReal.continuous_ofReal.comp (continuous_pow n)).tendsto M).mono_left
        nhdsWithin_le_nhds) (Or.inr hE)
  refine ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun M' (hM' : M < M') => ?_)
  have := canonicalBedfordTaylorMeasure_le_relCapacity_of_bounds hw
    (show a < a + M' by linarith)
    (fun z hz => ⟨(hwb z hz).1, (hwb z hz).2.trans (by linarith)⟩) E
  simpa only [add_sub_cancel_left] using this

/-- The constant function `0` is locally bounded plurisubharmonic. -/
theorem isLocallyBoundedPshOn_zero (D : Opens (ComplexModel n)) :
    IsLocallyBoundedPshOn D (fun _ => (0 : ℝ)) := by
  refine ⟨fun x _ => plurisubharmonicAt_const _ (EReal.coe_ne_top _) x, fun z hz => ?_⟩
  exact ⟨D, hz, le_rfl, 0, fun _ _ => by simp⟩

/-- **Markov's inequality for the energy**: `(ddᶜφ)ⁿ({φ < -s}) ≤ s⁻ᵖ e_p(φ)`. -/
theorem ma_sublevel_le_localEnergy {D : Opens (ComplexModel n)} {φ : ComplexModel n → ℝ}
    (hφ : IsLocallyBoundedPshOn D φ) {p s : ℝ} (hp : 0 < p) (hs : 0 < s) :
    canonicalBedfordTaylorMeasure D φ hφ {z | z ∈ D ∧ φ z < -s} ≤
      ENNReal.ofReal (s ^ (-p)) * localEnergy D p φ hφ := by
  set ν := canonicalBedfordTaylorMeasure D φ hφ
  set E : Set (ComplexModel n) := {z | z ∈ D ∧ φ z < -s} with hEdef
  have hEo : IsOpen E := isOpen_setOf_mem_and_lt_of_plurisubharmonicOn hφ.1 (-s)
  calc ν E = ∫⁻ _ in E, 1 ∂ν := (setLIntegral_one E).symm
    _ ≤ ∫⁻ z in E, ENNReal.ofReal (s ^ (-p)) * ENNReal.ofReal ((-φ z) ^ p) ∂ν := by
        refine setLIntegral_mono' hEo.measurableSet fun z hz => ?_
        have hz' : s < -φ z := by linarith [hz.2]
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _), ← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : s ^ p ≤ (-φ z) ^ p := Real.rpow_le_rpow hs.le hz'.le hp.le
        have h2 : s ^ (-p) * s ^ p = 1 := by
          rw [← Real.rpow_add hs, neg_add_cancel, Real.rpow_zero]
        calc (1 : ℝ) = s ^ (-p) * s ^ p := h2.symm
          _ ≤ s ^ (-p) * (-φ z) ^ p := by gcongr
    _ = ENNReal.ofReal (s ^ (-p)) * ∫⁻ z in E, ENNReal.ofReal ((-φ z) ^ p) ∂ν :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (s ^ (-p)) * localEnergy D p φ hφ := by
        gcongr
        exact lintegral_mono_set fun z hz => hz.1

/-- The real identity behind the constant of the tail bound. -/
theorem tail_const_eq {M t p : ℝ} (ht : 0 < t) (k : ℕ) :
    M ^ k * ((t / 2) ^ k)⁻¹ * (t / 2) ^ (-p) = 2 ^ ((k : ℝ) + p) * M ^ k * t ^ (-((k : ℝ) + p)) := by
  have ht2 : 0 < t / 2 := by positivity
  have h1 : ((t / 2) ^ k)⁻¹ * (t / 2) ^ (-p) = (t / 2) ^ (-((k : ℝ) + p)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg ht2.le, ← Real.rpow_add ht2, neg_add]
  have h2 : (t / 2) ^ (-((k : ℝ) + p)) = 2 ^ ((k : ℝ) + p) * t ^ (-((k : ℝ) + p)) := by
    rw [Real.div_rpow ht.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul,
      mul_comm]
  rw [mul_assoc, h1, h2]
  ring

/-- **The tail bound** of FPT `thm:bounded-subsolution-local-energy-moments`
(`eq:local-energy-measure-tail`, with the smaller constant `2ⁿ⁺ᵖ Mⁿ`): if `μ ≤ (ddᶜw)ⁿ` on the
bounded open set `D`, with `a ≤ w ≤ a + M` on `D`, and `φ` is locally bounded psh on `D` with
boundary values `0`, then `μ({z ∈ D : φ z < -t}) ≤ 2ⁿ⁺ᵖ Mⁿ t^{-(n+p)} e_p(φ)` for `p, t > 0`. -/
theorem measure_sublevel_le_localEnergy (hn : 0 < n) {D : Opens (ComplexModel n)}
    (hDb : Bornology.IsBounded (D : Set (ComplexModel n))) {φ : ComplexModel n → ℝ}
    (hφ : IsLocallyBoundedPshOn D φ)
    (hbd : ∀ ζ ∈ frontier (D : Set (ComplexModel n)),
      Tendsto φ (𝓝[(D : Set (ComplexModel n))] ζ) (𝓝 0))
    {w : ComplexModel n → ℝ} (hw : IsLocallyBoundedPshOn D w) {a M : ℝ} (hM : 0 ≤ M)
    (hwb : ∀ z ∈ D, a ≤ w z ∧ w z ≤ a + M) {μ : Measure (ComplexModel n)}
    (hμ : μ.restrict D ≤ canonicalBedfordTaylorMeasure D w hw) {p t : ℝ} (hp : 0 < p)
    (ht : 0 < t) :
    μ {z | z ∈ D ∧ φ z < -t} ≤
      ENNReal.ofReal (2 ^ ((n : ℝ) + p) * M ^ n * t ^ (-((n : ℝ) + p))) *
        localEnergy D p φ hφ := by
  set E : Set (ComplexModel n) := {z | z ∈ D ∧ φ z < -t} with hEdef
  set E' : Set (ComplexModel n) := {z | z ∈ D ∧ φ z < -(t / 2)} with hE'def
  set ν := canonicalBedfordTaylorMeasure D φ hφ
  have ht2 : 0 < t / 2 := by positivity
  obtain ⟨hKc, hKD⟩ := exists_isCompact_sublevel hDb hbd ht2
  have hE'K : {z | z ∈ D ∧ φ z < (fun _ => (0 : ℝ)) z - t / 2} ⊆
      closure {z | z ∈ D ∧ φ z ≤ -(t / 2)} :=
    fun z hz => subset_closure ⟨hz.1, by simp only at hz; linarith [hz.2]⟩
  have hcap := pow_mul_relCapacity_le hn hφ (isLocallyBoundedPshOn_zero D) (t / 2) ht2 hKc hKD
    hE'K
  have hsetE : {z | z ∈ D ∧ φ z < (fun _ => (0 : ℝ)) z - t / 2 - t / 2} = E := by
    ext z
    simp only [hEdef, mem_ofPred_eq]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
  have hsetE' : {z | z ∈ D ∧ φ z < (fun _ => (0 : ℝ)) z - t / 2} = E' := by
    ext z
    simp only [hE'def, mem_ofPred_eq]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
  rw [hsetE, hsetE'] at hcap
  have hc0 : ENNReal.ofReal (t / 2) ^ n ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.mpr ht2).ne'
  have hcT : ENNReal.ofReal (t / 2) ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hCap : relCapacity D E ≤ (ENNReal.ofReal (t / 2) ^ n)⁻¹ * ν E' :=
    (ENNReal.mul_le_iff_le_inv hc0 hcT).mp hcap
  have hE'K' : E' ⊆ closure {z | z ∈ D ∧ φ z ≤ -(t / 2)} :=
    fun z hz => subset_closure ⟨hz.1, hz.2.le⟩
  have hE'fin : ν E' < ∞ :=
    (measure_mono hE'K').trans_lt
      (canonicalBedfordTaylorMeasure_finiteOnCompacts hφ hKc hKD)
  have hCapfin : relCapacity D E ≠ ∞ :=
    (hCap.trans_lt (ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hc0))
      hE'fin)).ne
  have hED : E ⊆ D := fun z hz => hz.1
  calc μ E = μ.restrict D E := (Measure.restrict_eq_self μ hED).symm
    _ ≤ canonicalBedfordTaylorMeasure D w hw E := hμ E
    _ ≤ ENNReal.ofReal (M ^ n) * relCapacity D E :=
        ma_le_ofReal_pow_mul_relCapacity hw hM hwb hCapfin
    _ ≤ ENNReal.ofReal (M ^ n) * ((ENNReal.ofReal (t / 2) ^ n)⁻¹ *
          (ENNReal.ofReal ((t / 2) ^ (-p)) * localEnergy D p φ hφ)) := by
        gcongr
        exact hCap.trans (by gcongr; exact ma_sublevel_le_localEnergy hφ hp ht2)
    _ = ENNReal.ofReal (2 ^ ((n : ℝ) + p) * M ^ n * t ^ (-((n : ℝ) + p))) *
          localEnergy D p φ hφ := by
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_pow ht2.le,
          ← ENNReal.ofReal_inv_of_pos (pow_pos ht2 n),
          ← ENNReal.ofReal_mul (pow_nonneg hM n),
          ← ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hM n) (inv_nonneg.mpr (pow_pos ht2 n).le)),
          tail_const_eq ht]

/-- The real identity behind FPT's choice of the splitting level `T` in the proof of
`eq:local-energy-measure-moment`. -/
theorem moment_split_eq {B m N p : ℝ} (hB : 0 < B) (hm : 0 < m) (hN : 0 < N) (hp : 0 < p) :
    m * (B / m) ^ (p / (N + p)) + p / N * (B * ((B / m) ^ (p / (N + p))) ^ (-N / p)) =
      (1 + p / N) * B ^ (p / (N + p)) * m ^ (N / (N + p)) := by
  have hNp : 0 < N + p := by linarith
  set θ := p / (N + p) with hθ
  set X := Real.exp (θ * Real.log B + N / (N + p) * Real.log m) with hX
  have hS : (B / m) ^ θ = Real.exp ((Real.log B - Real.log m) * θ) := by
    rw [Real.rpow_def_of_pos (div_pos hB hm), Real.log_div hB.ne' hm.ne']
  have k1 : m * (B / m) ^ θ = X := by
    rw [hS, hX]
    conv_lhs => rw [← Real.exp_log hm]
    rw [← Real.exp_add]
    congr 1
    rw [Real.log_exp, hθ]
    field_simp
    ring
  have k2 : B * ((B / m) ^ θ) ^ (-N / p) = X := by
    rw [hS, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, hX]
    conv_lhs => rw [← Real.exp_log hB]
    rw [← Real.exp_add]
    congr 1
    rw [Real.log_exp, hθ]
    field_simp
    ring
  have k3 : B ^ θ * m ^ (N / (N + p)) = X := by
    rw [Real.rpow_def_of_pos hB, Real.rpow_def_of_pos hm, ← Real.exp_add, hX]
    congr 1
    ring
  rw [k1, k2, mul_assoc, k3]
  ring

/-- **Layer-cake integration of a tail bound**: if `ν(X) ≤ m` and
`ν({f > t}) ≤ B t^{-(N+p)}` for all `t > 0`, then
`∫ fᵖ dν ≤ (1 + p/N) B^{p/(N+p)} m^{N/(N+p)}` (the computation of FPT
`thm:bounded-subsolution-local-energy-moments`, with the splitting level
`T = (B/m)^{1/(N+p)}`). -/
theorem lintegral_rpow_le_of_tail {X : Type*} [MeasurableSpace X] (ν : Measure X) {f : X → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hfm : AEMeasurable f ν) {m B N p : ℝ} (hm : 0 ≤ m) (hB : 0 ≤ B)
    (hN : 0 < N) (hp : 0 < p) (hνm : ν univ ≤ ENNReal.ofReal m)
    (htail : ∀ t : ℝ, 0 < t → ν {x | t < f x} ≤ ENNReal.ofReal (B * t ^ (-(N + p)))) :
    ∫⁻ x, ENNReal.ofReal (f x ^ p) ∂ν ≤
      ENNReal.ofReal ((1 + p / N) * B ^ (p / (N + p)) * m ^ (N / (N + p))) := by
  have hNp : 0 < N + p := by linarith
  have hfp : AEMeasurable (fun x => f x ^ p) ν := hfm.pow_const p
  rw [lintegral_eq_lintegral_meas_lt ν (Eventually.of_forall fun x => Real.rpow_nonneg (hf0 x) p)
    hfp]
  -- the pointwise bounds on the distribution function
  have hset : ∀ s : ℝ, 0 < s → {x | s < f x ^ p} ⊆ {x | s ^ (1 / p) < f x} := by
    intro s hs x hx
    have h := Real.rpow_lt_rpow hs.le hx (one_div_pos.mpr hp)
    rwa [← Real.rpow_mul (hf0 x), mul_one_div_cancel hp.ne', Real.rpow_one] at h
  have hbd1 : ∀ s : ℝ, 0 < s → ν {x | s < f x ^ p} ≤ ENNReal.ofReal m :=
    fun s _ => (measure_mono (subset_univ _)).trans hνm
  have hbd2 : ∀ s : ℝ, 0 < s →
      ν {x | s < f x ^ p} ≤ ENNReal.ofReal (B * s ^ (-(N + p) / p)) := by
    intro s hs
    refine (measure_mono (hset s hs)).trans ((htail _ (Real.rpow_pos_of_pos hs _)).trans ?_)
    rw [← Real.rpow_mul hs.le, show 1 / p * -(N + p) = -(N + p) / p by ring]
  rcases hm.eq_or_lt with hm0 | hmpos
  · -- `ν = 0`
    have : ∀ s : ℝ, 0 < s → ν {x | s < f x ^ p} = 0 := fun s hs =>
      le_antisymm ((hbd1 s hs).trans (by rw [← hm0, ENNReal.ofReal_zero])) bot_le
    rw [setLIntegral_congr_fun measurableSet_Ioi (fun s hs => this s hs), lintegral_zero]
    exact bot_le
  rcases hB.eq_or_lt with hB0 | hBpos
  · have : ∀ s : ℝ, 0 < s → ν {x | s < f x ^ p} = 0 := fun s hs =>
      le_antisymm ((hbd2 s hs).trans (by rw [← hB0, zero_mul, ENNReal.ofReal_zero])) bot_le
    rw [setLIntegral_congr_fun measurableSet_Ioi (fun s hs => this s hs), lintegral_zero]
    exact bot_le
  set S := (B / m) ^ (p / (N + p)) with hSdef
  have hS : 0 < S := Real.rpow_pos_of_pos (div_pos hBpos hmpos) _
  have hq : -(N + p) / p < -1 := by
    rw [div_lt_iff₀ hp]
    linarith
  have hint : IntegrableOn (fun s : ℝ => B * s ^ (-(N + p) / p)) (Ioi S) :=
    (integrableOn_Ioi_rpow_of_lt hq hS).const_mul B
  have hval : ∫ s in Ioi S, B * s ^ (-(N + p) / p) = p / N * (B * S ^ (-N / p)) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt hq hS]
    have h1 : -(N + p) / p + 1 = -N / p := by field_simp; ring
    rw [h1]
    field_simp
  rw [← Ioc_union_Ioi_eq_Ioi hS.le, lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same]
  calc (∫⁻ s in Ioc 0 S, ν {x | s < f x ^ p}) + ∫⁻ s in Ioi S, ν {x | s < f x ^ p}
      ≤ (∫⁻ _ in Ioc 0 S, ENNReal.ofReal m) +
          ∫⁻ s in Ioi S, ENNReal.ofReal (B * s ^ (-(N + p) / p)) := by
        exact add_le_add (setLIntegral_mono' measurableSet_Ioc fun s hs => hbd1 s hs.1)
          (setLIntegral_mono' measurableSet_Ioi fun s hs => hbd2 s (hS.trans hs))
    _ = ENNReal.ofReal (m * S + p / N * (B * S ^ (-N / p))) := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero,
          ← ofReal_integral_eq_lintegral_ofReal hint
            (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs =>
              mul_nonneg hB (Real.rpow_nonneg (hS.trans hs).le _)),
          hval, ← ENNReal.ofReal_mul hm,
          ← ENNReal.ofReal_add (mul_nonneg hm hS.le)
            (mul_nonneg (div_nonneg hp.le hN.le) (mul_nonneg hB (Real.rpow_nonneg hS.le _)))]
    _ = ENNReal.ofReal ((1 + p / N) * B ^ (p / (N + p)) * m ^ (N / (N + p))) := by
        rw [hSdef, moment_split_eq hBpos hmpos hN hp]

/-- FPT's constant `A_p = (1 + p/n) κ_{n,p}^{p/(n+p)} m^{n/(n+p)}`, `κ_{n,p} = 2ⁿ⁺ᵖ (n+1)! Mⁿ`
(FPT `thm:bounded-subsolution-local-energy-moments`). -/
def energyMomentConst (n : ℕ) (p m M : ℝ) : ℝ :=
  (1 + p / n) * (2 ^ ((n : ℝ) + p) * ((n + 1).factorial : ℝ) * M ^ n) ^ (p / (n + p)) *
    m ^ ((n : ℝ) / (n + p))

theorem energyMomentConst_nonneg (n : ℕ) {p m M : ℝ} (hp : 0 ≤ p) (hm : 0 ≤ m) (hM : 0 ≤ M) :
    0 ≤ energyMomentConst n p m M := by
  unfold energyMomentConst
  have : 0 ≤ 1 + p / n := by positivity
  positivity

/-- The tail bound with FPT's constant `κ_{n,p} = 2ⁿ⁺ᵖ (n+1)! Mⁿ`
(`eq:local-energy-measure-tail`). -/
theorem measure_sublevel_le_kappa (hn : 0 < n) {D : Opens (ComplexModel n)}
    (hDb : Bornology.IsBounded (D : Set (ComplexModel n))) {φ : ComplexModel n → ℝ}
    (hφ : IsLocallyBoundedPshOn D φ)
    (hbd : ∀ ζ ∈ frontier (D : Set (ComplexModel n)),
      Tendsto φ (𝓝[(D : Set (ComplexModel n))] ζ) (𝓝 0))
    {w : ComplexModel n → ℝ} (hw : IsLocallyBoundedPshOn D w) {a M : ℝ} (hM : 0 ≤ M)
    (hwb : ∀ z ∈ D, a ≤ w z ∧ w z ≤ a + M) {μ : Measure (ComplexModel n)}
    (hμ : μ.restrict D ≤ canonicalBedfordTaylorMeasure D w hw) {p t : ℝ} (hp : 0 < p)
    (ht : 0 < t) :
    μ {z | z ∈ D ∧ φ z < -t} ≤
      ENNReal.ofReal (2 ^ ((n : ℝ) + p) * ((n + 1).factorial : ℝ) * M ^ n * t ^ (-((n : ℝ) + p))) *
        localEnergy D p φ hφ := by
  refine (measure_sublevel_le_localEnergy hn hDb hφ hbd hw hM hwb hμ hp ht).trans ?_
  have h1 : (1 : ℝ) ≤ ((n + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  gcongr
  exact le_mul_of_one_le_right (by positivity) h1

/-- **The moment bound** of FPT `thm:bounded-subsolution-local-energy-moments`
(`eq:local-energy-measure-moment`): under the hypotheses of the tail bound, with `μ(D) < ∞` and
`e_p(φ) < ∞`, `∫_D (-φ)ᵖ dμ ≤ A_p e_p(φ)^{p/(n+p)}`, `A_p = energyMomentConst n p μ(D) M`.
For `p = 1` this is the Cegrell–Persson estimate. -/
theorem lintegral_neg_rpow_le (hn : 0 < n) {D : Opens (ComplexModel n)}
    (hDb : Bornology.IsBounded (D : Set (ComplexModel n))) {φ : ComplexModel n → ℝ}
    (hφ : IsLocallyBoundedPshOn D φ) (hφ0 : ∀ z ∈ D, φ z ≤ 0)
    (hbd : ∀ ζ ∈ frontier (D : Set (ComplexModel n)),
      Tendsto φ (𝓝[(D : Set (ComplexModel n))] ζ) (𝓝 0))
    {w : ComplexModel n → ℝ} (hw : IsLocallyBoundedPshOn D w) {a M : ℝ} (hM : 0 ≤ M)
    (hwb : ∀ z ∈ D, a ≤ w z ∧ w z ≤ a + M) {μ : Measure (ComplexModel n)}
    (hμ : μ.restrict D ≤ canonicalBedfordTaylorMeasure D w hw) (hμD : μ D ≠ ∞) {p : ℝ}
    (hp : 0 < p) (he : localEnergy D p φ hφ ≠ ∞) :
    ∫⁻ z in (D : Set (ComplexModel n)), ENNReal.ofReal ((-φ z) ^ p) ∂μ ≤
      ENNReal.ofReal (energyMomentConst n p (μ D).toReal M *
        (localEnergy D p φ hφ).toReal ^ (p / (n + p))) := by
  set e := (localEnergy D p φ hφ).toReal with hedef
  have he0 : 0 ≤ e := ENNReal.toReal_nonneg
  set κ := 2 ^ ((n : ℝ) + p) * ((n + 1).factorial : ℝ) * M ^ n with hκdef
  have hκ : 0 ≤ κ := by positivity
  set f : ComplexModel n → ℝ := fun z => -((D : Set (ComplexModel n)).indicator φ z) with hfdef
  have hfm : Measurable f := (measurable_indicator_of_plurisubharmonicOn hφ.1).neg
  have hf0 : ∀ z, 0 ≤ f z := by
    intro z
    by_cases hz : z ∈ (D : Set (ComplexModel n))
    · simp only [hfdef, indicator_of_mem hz]; linarith [hφ0 z hz]
    · simp [hfdef, indicator_of_notMem hz]
  have heq : ∫⁻ z in (D : Set (ComplexModel n)), ENNReal.ofReal ((-φ z) ^ p) ∂μ =
      ∫⁻ z, ENNReal.ofReal (f z ^ p) ∂μ.restrict D :=
    setLIntegral_congr_fun D.isOpen.measurableSet fun z hz => by
      simp only [hfdef, indicator_of_mem hz]
  rw [heq]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have key := lintegral_rpow_le_of_tail (μ.restrict D) hf0 hfm.aemeasurable
    (m := (μ D).toReal) (B := κ * e) ENNReal.toReal_nonneg (mul_nonneg hκ he0) hn' hp
    (by rw [Measure.restrict_apply_univ, ENNReal.ofReal_toReal hμD]) (fun t ht => by
      rw [Measure.restrict_apply' D.isOpen.measurableSet]
      have hset : {x | t < f x} ∩ (D : Set (ComplexModel n)) = {z | z ∈ D ∧ φ z < -t} := by
        ext z
        simp only [mem_inter_iff, mem_ofPred_eq, hfdef]
        constructor
        · rintro ⟨h1, h2⟩
          rw [indicator_of_mem h2] at h1
          exact ⟨h2, by linarith⟩
        · rintro ⟨h1, h2⟩
          rw [indicator_of_mem h1]
          exact ⟨by linarith, h1⟩
      rw [hset]
      refine (measure_sublevel_le_kappa hn hDb hφ hbd hw hM hwb hμ hp ht).trans ?_
      rw [← ENNReal.ofReal_toReal he, ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (le_of_eq (by rw [hedef]; ring)))
  refine key.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  unfold energyMomentConst
  rw [Real.mul_rpow hκ he0]
  ring

/-- Elements of `ℰ₀(D)` have finite energy moments. -/
theorem IsCegrellE0.localEnergy_ne_top {D : Opens (ComplexModel n)} {φ : ComplexModel n → ℝ}
    (hφ : IsCegrellE0 D φ) {p : ℝ} (hp : 0 ≤ p) : localEnergy D p φ hφ.psh ≠ ∞ := by
  obtain ⟨C, hC⟩ := hφ.bddBelow
  refine (lt_of_le_of_lt (setLIntegral_mono' D.isOpen.measurableSet fun z hz =>
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by linarith [hφ.nonpos z hz])
      (show -φ z ≤ C by linarith [hC z hz]) hp)) ?_).ne
  rw [setLIntegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hφ.mass_lt_top

/-- From `x ≤ c x^θ` with `0 ≤ θ < 1` to `x ≤ c^{1/(1-θ)}`. -/
theorem le_rpow_of_le_mul_rpow {x c θ : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) (hθ : θ < 1)
    (h : x ≤ c * x ^ θ) : x ≤ c ^ (1 - θ)⁻¹ := by
  rcases hx.eq_or_lt with hx0 | hxpos
  · rw [← hx0]; exact Real.rpow_nonneg hc _
  have h1 : x ^ (1 - θ) ≤ c := by
    rw [Real.rpow_sub hxpos, Real.rpow_one, div_le_iff₀ (Real.rpow_pos_of_pos hxpos θ)]
    exact h
  have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hx _) h1
    (inv_nonneg.mpr (show (0 : ℝ) ≤ 1 - θ by linarith))
  rwa [← Real.rpow_mul hx, mul_inv_cancel₀ (by linarith), Real.rpow_one] at h2

/-- **Uniform energy bound** (FPT `prop:canonical-grid-energy-control` (4), abstract form): let
`μ ≤ (ddᶜw)ⁿ` be finite on the bounded open set `D`, `a ≤ w ≤ a + M`, and let `U ∈ ℰ₀(D)` satisfy
`e_p(U) ≤ c ∫_D (-U)ᵖ dμ` (for the solution `U` of `(ddᶜU)ⁿ = μ'` this is the comparison of `μ'`
with `μ` on `(-U)ᵖ`: FPT's sub-mean value estimate `eq:canonical-grid-polydisc-average`). Then
`e_p(U) ≤ (c A_p)^{(n+p)/n}`. -/
theorem localEnergy_le_of_moment_control (hn : 0 < n) {D : Opens (ComplexModel n)}
    (hDb : Bornology.IsBounded (D : Set (ComplexModel n))) {U : ComplexModel n → ℝ}
    (hU : IsCegrellE0 D U) {w : ComplexModel n → ℝ} (hw : IsLocallyBoundedPshOn D w) {a M : ℝ}
    (hM : 0 ≤ M) (hwb : ∀ z ∈ D, a ≤ w z ∧ w z ≤ a + M) {μ : Measure (ComplexModel n)}
    (hμ : μ.restrict D ≤ canonicalBedfordTaylorMeasure D w hw) (hμD : μ D ≠ ∞) {p c : ℝ}
    (hp : 0 < p) (hc : 0 ≤ c)
    (hctrl : localEnergy D p U hU.psh ≤
      ENNReal.ofReal c * ∫⁻ z in (D : Set (ComplexModel n)), ENNReal.ofReal ((-U z) ^ p) ∂μ) :
    (localEnergy D p U hU.psh).toReal ≤
      (c * energyMomentConst n p (μ D).toReal M) ^ (((n : ℝ) + p) / n) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have he := hU.localEnergy_ne_top hp.le
  have hmom := lintegral_neg_rpow_le hn hDb hU.psh hU.nonpos hU.tendsto_frontier hw hM hwb hμ hμD
    hp he
  have hA := energyMomentConst_nonneg n hp.le (μ D).toReal_nonneg hM
  have h1 : (localEnergy D p U hU.psh).toReal ≤
      (c * energyMomentConst n p (μ D).toReal M) *
        (localEnergy D p U hU.psh).toReal ^ (p / (n + p)) := by
    have := hctrl.trans (mul_le_mul_right hmom (ENNReal.ofReal c))
    rw [← ENNReal.ofReal_mul hc] at this
    rw [mul_assoc]
    exact (ENNReal.toReal_le_of_le_ofReal (by positivity) this)
  have hθ : p / (n + p) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have h2 := le_rpow_of_le_mul_rpow ENNReal.toReal_nonneg (mul_nonneg hc hA) hθ h1
  have h3 : (1 - p / (n + p))⁻¹ = ((n : ℝ) + p) / n := by
    have : (n : ℝ) + p ≠ 0 := by positivity
    rw [one_sub_div this, add_sub_cancel_right, inv_div]
  rwa [h3] at h2

end SGPT.Envelopes.MADirichlet
