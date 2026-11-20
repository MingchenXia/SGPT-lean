import SGPT.Envelopes.MADirichlet3Approximants
import SGPT.Foundations.Analysis.Pending.BedfordTaylorCompactMassEquality
import SGPT.Foundations.Analysis.Pending.BoundedPairMaxLocality

/-!
# Truncations of `ℰ₀` functions and capacity tails

Xia, *Foundations of pluripotential theory* (FPT), `sec:canonical-grid-capacity-convergence`.

* `relCapacity_sublevel_le_localEnergy`: FPT `prop:energy-controlled-local-capacity-tails` (1),
  `Cap_D({φ < -T}) ≤ 2ⁿ⁺ᵖ e_p(φ) T^{-(n+p)}` for `φ` with boundary values `0` on a bounded open
  `D` (FPT's constant `2ⁿ⁺ᵖ (n+1)!` is larger: `relCapacity_sublevel_le_kappa`).
* `IsCegrellE0.truncation`: FPT `lem:zero-boundary-truncation-mass`: for `φ ∈ ℰ₀(D)` and `T > 0`,
  `φ_T = max(φ, -T) ∈ ℰ₀(D)`, the Monge–Ampère measures of `φ_T` and `φ` agree on `{φ > -T}`, have
  the same total mass and the same mass `m_T ≤ e_p(φ) T⁻ᵖ` on `F_T = {φ ≤ -T}` (this is the total
  variation bound `‖(ddᶜφ_T)ⁿ - (ddᶜφ)ⁿ‖ ≤ 2 e_p(φ) T⁻ᵖ`), and `e_p(φ_T) ≤ e_p(φ)`.
  Ingredients: TN's maximum locality (`restrict_eq_of_bounded_pair_max`) and TN's local Stokes
  mass equality for potentials agreeing off a compact set
  (`canonicalBedfordTaylorMeasure_eq_of_eqOn_compl`, FPT `lem:compact-perturbation-mass`).
* `ma_le_relCapacity_add_localEnergy`: FPT `eq:energy-measure-capacity-modulus`,
  `(ddᶜφ)ⁿ(E) ≤ Tⁿ Cap_D(E) + e_p(φ) T⁻ᵖ` for `E ⊆ D`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor

variable {n : ℕ}

/-- **Capacity of sublevel sets** (FPT `prop:energy-controlled-local-capacity-tails` (1), with the
constant `2ⁿ⁺ᵖ`): `Cap_D({φ < -t}) ≤ 2ⁿ⁺ᵖ t^{-(n+p)} e_p(φ)`. -/
theorem relCapacity_sublevel_le_localEnergy (hn : 0 < n) {D : Opens (ComplexModel n)}
    (hDb : Bornology.IsBounded (D : Set (ComplexModel n))) {φ : ComplexModel n → ℝ}
    (hφ : IsLocallyBoundedPshOn D φ)
    (hbd : ∀ ζ ∈ frontier (D : Set (ComplexModel n)),
      Tendsto φ (𝓝[(D : Set (ComplexModel n))] ζ) (𝓝 0)) {p t : ℝ} (hp : 0 < p) (ht : 0 < t) :
    relCapacity D {z | z ∈ D ∧ φ z < -t} ≤
      ENNReal.ofReal (2 ^ ((n : ℝ) + p) * t ^ (-((n : ℝ) + p))) * localEnergy D p φ hφ := by
  have ht2 : 0 < t / 2 := by positivity
  obtain ⟨hKc, hKD⟩ := exists_isCompact_sublevel hDb hbd ht2
  have hE'K : {z | z ∈ D ∧ φ z < (fun _ => (0 : ℝ)) z - t / 2} ⊆
      closure {z | z ∈ D ∧ φ z ≤ -(t / 2)} :=
    fun z hz => subset_closure ⟨hz.1, by simp only at hz; linarith [hz.2]⟩
  have hcap := pow_mul_relCapacity_le hn hφ (isLocallyBoundedPshOn_zero D) (t / 2) ht2 hKc hKD
    hE'K
  have hsetE : {z | z ∈ D ∧ φ z < (fun _ => (0 : ℝ)) z - t / 2 - t / 2} =
      {z | z ∈ D ∧ φ z < -t} := by
    ext z
    simp only [mem_ofPred_eq]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
  have hsetE' : {z | z ∈ D ∧ φ z < (fun _ => (0 : ℝ)) z - t / 2} =
      {z | z ∈ D ∧ φ z < -(t / 2)} := by
    ext z
    simp only [mem_ofPred_eq]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
  rw [hsetE, hsetE'] at hcap
  have hc0 : ENNReal.ofReal (t / 2) ^ n ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.mpr ht2).ne'
  have hcT : ENNReal.ofReal (t / 2) ^ n ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  calc relCapacity D {z | z ∈ D ∧ φ z < -t}
      ≤ (ENNReal.ofReal (t / 2) ^ n)⁻¹ *
          canonicalBedfordTaylorMeasure D φ hφ {z | z ∈ D ∧ φ z < -(t / 2)} :=
        (ENNReal.mul_le_iff_le_inv hc0 hcT).mp hcap
    _ ≤ (ENNReal.ofReal (t / 2) ^ n)⁻¹ *
          (ENNReal.ofReal ((t / 2) ^ (-p)) * localEnergy D p φ hφ) := by
        gcongr
        exact ma_sublevel_le_localEnergy hφ hp ht2
    _ = ENNReal.ofReal (2 ^ ((n : ℝ) + p) * t ^ (-((n : ℝ) + p))) * localEnergy D p φ hφ := by
        rw [← mul_assoc, ← ENNReal.ofReal_pow ht2.le,
          ← ENNReal.ofReal_inv_of_pos (pow_pos ht2 n),
          ← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_pos ht2 n).le)]
        congr 2
        have := tail_const_eq (M := 1) (p := p) ht n
        rw [one_pow, one_mul, mul_one] at this
        exact this

/-- FPT `prop:energy-controlled-local-capacity-tails` (1) with FPT's constant `2ⁿ⁺ᵖ (n+1)!`. -/
theorem relCapacity_sublevel_le_kappa (hn : 0 < n) {D : Opens (ComplexModel n)}
    (hDb : Bornology.IsBounded (D : Set (ComplexModel n))) {φ : ComplexModel n → ℝ}
    (hφ : IsLocallyBoundedPshOn D φ)
    (hbd : ∀ ζ ∈ frontier (D : Set (ComplexModel n)),
      Tendsto φ (𝓝[(D : Set (ComplexModel n))] ζ) (𝓝 0)) {p t : ℝ} (hp : 0 < p) (ht : 0 < t) :
    relCapacity D {z | z ∈ D ∧ φ z < -t} ≤
      ENNReal.ofReal (2 ^ ((n : ℝ) + p) * ((n + 1).factorial : ℝ) * t ^ (-((n : ℝ) + p))) *
        localEnergy D p φ hφ := by
  refine (relCapacity_sublevel_le_localEnergy hn hDb hφ hbd hp ht).trans ?_
  have h1 : (1 : ℝ) ≤ ((n + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  gcongr
  exact le_mul_of_one_le_right (by positivity) h1

/-- **Markov's inequality on the closed sublevel set**: `(ddᶜφ)ⁿ({φ ≤ -s}) ≤ s⁻ᵖ e_p(φ)`. -/
theorem ma_closedSublevel_le_localEnergy {D : Opens (ComplexModel n)} {φ : ComplexModel n → ℝ}
    (hφ : IsLocallyBoundedPshOn D φ) {p s : ℝ} (hp : 0 < p) (hs : 0 < s) :
    canonicalBedfordTaylorMeasure D φ hφ {z | z ∈ D ∧ φ z ≤ -s} ≤
      ENNReal.ofReal (s ^ (-p)) * localEnergy D p φ hφ := by
  set ν := canonicalBedfordTaylorMeasure D φ hφ
  set F : Set (ComplexModel n) := {z | z ∈ D ∧ φ z ≤ -s} with hFdef
  have hFm : MeasurableSet F := by
    have hm := measurable_indicator_of_plurisubharmonicOn hφ.1
    have : F = (D : Set (ComplexModel n)) ∩
        ((D : Set (ComplexModel n)).indicator φ) ⁻¹' Iic (-s) := by
      ext z
      simp only [hFdef, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Iic]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [indicator_of_mem h1]⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [indicator_of_mem h1] at h2⟩
    rw [this]
    exact D.isOpen.measurableSet.inter (hm measurableSet_Iic)
  calc ν F = ∫⁻ _ in F, 1 ∂ν := (setLIntegral_one F).symm
    _ ≤ ∫⁻ z in F, ENNReal.ofReal (s ^ (-p)) * ENNReal.ofReal ((-φ z) ^ p) ∂ν := by
        refine setLIntegral_mono' hFm fun z hz => ?_
        have hz' : s ≤ -φ z := by linarith [hz.2]
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _), ← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : s ^ p ≤ (-φ z) ^ p := Real.rpow_le_rpow hs.le hz' hp.le
        have h2 : s ^ (-p) * s ^ p = 1 := by
          rw [← Real.rpow_add hs, neg_add_cancel, Real.rpow_zero]
        calc (1 : ℝ) = s ^ (-p) * s ^ p := h2.symm
          _ ≤ s ^ (-p) * (-φ z) ^ p := by gcongr
    _ = ENNReal.ofReal (s ^ (-p)) * ∫⁻ z in F, ENNReal.ofReal ((-φ z) ^ p) ∂ν :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (s ^ (-p)) * localEnergy D p φ hφ := by
        gcongr
        exact lintegral_mono_set fun z hz => hz.1

theorem measurableSet_superlevel {D : Opens (ComplexModel n)} {φ : ComplexModel n → ℝ}
    (hφ : IsLocallyBoundedPshOn D φ) (c : ℝ) :
    MeasurableSet {z | z ∈ D ∧ c < φ z} := by
  have hm := measurable_indicator_of_plurisubharmonicOn hφ.1
  have : {z | z ∈ D ∧ c < φ z} = (D : Set (ComplexModel n)) ∩
      ((D : Set (ComplexModel n)).indicator φ) ⁻¹' Ioi c := by
    ext z
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioi]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [indicator_of_mem h1]⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [indicator_of_mem h1] at h2⟩
  rw [this]
  exact D.isOpen.measurableSet.inter (hm measurableSet_Ioi)

/-- **Truncation of `ℰ₀` functions** (FPT `lem:zero-boundary-truncation-mass`): for `φ ∈ ℰ₀(D)`
on a bounded open `D` and `T > 0`, the truncation `φ_T = max(φ, -T)` belongs to `ℰ₀(D)`; its
Monge–Ampère measure agrees with that of `φ` on `{φ > -T}`; both measures give the same mass to
`D` and to `F_T = {φ ≤ -T}`; that mass is at most `e_p(φ) T⁻ᵖ`; and `e_p(φ_T) ≤ e_p(φ)`. -/
theorem IsCegrellE0.truncation (hn : 0 < n) {D : Opens (ComplexModel n)}
    (hDb : Bornology.IsBounded (D : Set (ComplexModel n))) {φ : ComplexModel n → ℝ}
    (hφ : IsCegrellE0 D φ) {T : ℝ} (hT : 0 < T) {p : ℝ} (hp : 0 < p) :
    ∃ hφT : IsCegrellE0 D (fun z => max (φ z) (-T)),
      (canonicalBedfordTaylorMeasure D _ hφT.psh).restrict {z | z ∈ D ∧ -T < φ z} =
        (canonicalBedfordTaylorMeasure D φ hφ.psh).restrict {z | z ∈ D ∧ -T < φ z} ∧
      canonicalBedfordTaylorMeasure D _ hφT.psh D = canonicalBedfordTaylorMeasure D φ hφ.psh D ∧
      canonicalBedfordTaylorMeasure D _ hφT.psh {z | z ∈ D ∧ φ z ≤ -T} =
        canonicalBedfordTaylorMeasure D φ hφ.psh {z | z ∈ D ∧ φ z ≤ -T} ∧
      canonicalBedfordTaylorMeasure D φ hφ.psh {z | z ∈ D ∧ φ z ≤ -T} ≤
        ENNReal.ofReal (T ^ (-p)) * localEnergy D p φ hφ.psh ∧
      localEnergy D p _ hφT.psh ≤ localEnergy D p φ hφ.psh := by
  classical
  have hall : ∀ P : Prop, (∀ _ : Fin n, P) ↔ P := fun P => ⟨fun h => h ⟨0, hn⟩, fun h _ => h⟩
  have hc : IsLocallyBoundedPshOn D (fun _ => -T) := by
    refine ⟨fun x _ => plurisubharmonicAt_const _ (EReal.coe_ne_top _) x, fun z hz => ?_⟩
    exact ⟨D, hz, le_rfl, |-T|, fun _ _ => le_rfl⟩
  have hTpsh : IsLocallyBoundedPshOn D (fun z => max (φ z) (-T)) :=
    IsLocallyBoundedPshOn.max hφ.psh hc
  set ν := canonicalBedfordTaylorMeasure D φ hφ.psh with hνdef
  set νT := canonicalBedfordTaylorMeasure D _ hTpsh with hνTdef
  set G : Set (ComplexModel n) := {z | z ∈ D ∧ -T < φ z} with hGdef
  set F : Set (ComplexModel n) := {z | z ∈ D ∧ φ z ≤ -T} with hFdef
  have hGm : MeasurableSet G := measurableSet_superlevel hφ.psh (-T)
  have hDm : MeasurableSet (D : Set (ComplexModel n)) := D.isOpen.measurableSet
  have hFG : F = (D : Set (ComplexModel n)) \ G := by
    ext z
    simp only [hFdef, hGdef, mem_ofPred_eq, Set.mem_sdiff, not_and, not_lt]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun _ => h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2 h1⟩
  have hFm : MeasurableSet F := by rw [hFG]; exact hDm.diff hGm
  have hGD : G ⊆ D := fun z hz => hz.1
  have hdisj : Disjoint F G := by
    rw [hFG]; exact disjoint_sdiff_left
  have hFGD : F ∪ G = D := by rw [hFG, sdiff_union_of_subset hGD]
  -- maximum locality on `G`
  have hloc : νT.restrict G = ν.restrict G := by
    have h := BoundedPairMaxLocality.restrict_eq_of_bounded_pair_max
      (u := fun _ => φ) (w := fun _ => fun z => max (φ z) (-T)) (g := fun _ => fun _ => -T)
      (isBTLimit_canonicalBedfordTaylorMeasure hφ.psh)
      (isBTLimit_canonicalBedfordTaylorMeasure hTpsh) (fun _ => hc) (fun _ z _ => rfl)
    simp only [hall] at h
    exact h
  have hlocG : ∀ E, νT (E ∩ G) = ν (E ∩ G) := fun E => by
    rw [← Measure.restrict_apply' hGm, hloc, Measure.restrict_apply' hGm]
  -- equal total masses (local Stokes)
  obtain ⟨hKc, hKD⟩ := exists_isCompact_sublevel hDb hφ.tendsto_frontier hT
  obtain ⟨V0, hV0o, hKV0, hV0D, hV0c⟩ :=
    exists_open_between_and_isCompact_closure hKc D.isOpen hKD
  set V : Opens (ComplexModel n) := ⟨V0, hV0o⟩
  have hVrc : RelativelyCompactIn V D := ⟨hV0c, hV0D⟩
  have hVD : (V : Set (ComplexModel n)) ⊆ D := subset_closure.trans hV0D
  have hVeq : νT V = ν V := by
    have := canonicalBedfordTaylorMeasure_eq_of_eqOn_compl hTpsh hφ.psh hVrc hKc hKV0
      (fun z hzD hzK => ?_)
    · exact this
    · have : -T < φ z := by
        by_contra h
        exact hzK (subset_closure ⟨hzD, not_lt.mp h⟩)
      exact max_eq_left this.le
  have hDV : (D : Set (ComplexModel n)) \ V ⊆ G := by
    rintro z ⟨hzD, hzV⟩
    refine ⟨hzD, ?_⟩
    by_contra h
    exact hzV (hKV0 (subset_closure ⟨hzD, not_lt.mp h⟩))
  have hVm : MeasurableSet (V : Set (ComplexModel n)) := hV0o.measurableSet
  have hmassD : νT D = ν D := by
    rw [← measure_inter_add_sdiff (D : Set (ComplexModel n)) hVm,
      ← measure_inter_add_sdiff (μ := ν) (D : Set (ComplexModel n)) hVm,
      inter_eq_right.mpr hVD, hVeq]
    congr 1
    have h1 := hlocG ((D : Set (ComplexModel n)) \ V)
    rwa [inter_eq_left.mpr hDV] at h1
  -- equal masses of `F`
  have hνD : ν D ≠ ⊤ := hφ.mass_lt_top.ne
  have hνG : ν G ≠ ⊤ := ne_top_of_le_ne_top hνD (measure_mono hGD)
  have hmassF : νT F = ν F := by
    have h1 : νT D = νT F + νT G := by rw [← hFGD, measure_union hdisj hGm]
    have h2 : ν D = ν F + ν G := by rw [← hFGD, measure_union hdisj hGm]
    have hGG : νT G = ν G := by have := hlocG G; rwa [inter_self] at this
    rw [hmassD, h2, hGG] at h1
    exact ((ENNReal.add_left_inj hνG).mp h1).symm
  have hFle : ν F ≤ ENNReal.ofReal (T ^ (-p)) * localEnergy D p φ hφ.psh :=
    ma_closedSublevel_le_localEnergy hφ.psh hp hT
  -- the truncation is in `ℰ₀(D)`
  have hφT : IsCegrellE0 D (fun z => max (φ z) (-T)) := by
    refine ⟨hTpsh, ⟨T, fun z _ => le_max_right _ _⟩,
      fun z hz => max_le (hφ.nonpos z hz) (by linarith), fun ζ hζ => ?_, ?_⟩
    · have := (hφ.tendsto_frontier ζ hζ).max (tendsto_const_nhds (x := -T))
      rwa [max_eq_left (by linarith : (-T : ℝ) ≤ 0)] at this
    · change νT D < ⊤
      rw [hmassD]
      exact hφ.mass_lt_top
  refine ⟨hφT, hloc, hmassD, hmassF, hFle, ?_⟩
  -- the energy decreases
  change ∫⁻ z in (D : Set (ComplexModel n)), ENNReal.ofReal ((-max (φ z) (-T)) ^ p) ∂νT ≤
    ∫⁻ z in (D : Set (ComplexModel n)), ENNReal.ofReal ((-φ z) ^ p) ∂ν
  rw [← hFGD, lintegral_union hGm hdisj, lintegral_union hGm hdisj]
  refine add_le_add ?_ ?_
  · -- on `F` the truncation is `-T`
    calc ∫⁻ z in F, ENNReal.ofReal ((-max (φ z) (-T)) ^ p) ∂νT
        = ∫⁻ _ in F, ENNReal.ofReal (T ^ p) ∂νT := by
          refine setLIntegral_congr_fun hFm fun z hz => ?_
          show ENNReal.ofReal ((-max (φ z) (-T)) ^ p) = ENNReal.ofReal (T ^ p)
          rw [max_eq_right hz.2, neg_neg]
      _ = ENNReal.ofReal (T ^ p) * ν F := by rw [setLIntegral_const, hmassF]
      _ = ∫⁻ _ in F, ENNReal.ofReal (T ^ p) ∂ν := by rw [setLIntegral_const]
      _ ≤ ∫⁻ z in F, ENNReal.ofReal ((-φ z) ^ p) ∂ν := by
          refine setLIntegral_mono' hFm fun z hz => ENNReal.ofReal_le_ofReal ?_
          exact Real.rpow_le_rpow hT.le (by linarith [hz.2]) hp.le
  · -- on `G` the two integrands and measures agree
    rw [hloc]
    refine le_of_eq (setLIntegral_congr_fun hGm fun z hz => ?_)
    show ENNReal.ofReal ((-max (φ z) (-T)) ^ p) = ENNReal.ofReal ((-φ z) ^ p)
    rw [max_eq_left hz.2.le]

/-- **Capacity modulus of `ℰ₀` measures** (FPT `eq:energy-measure-capacity-modulus`): for
`φ ∈ ℰ₀(D)`, `T, p > 0` and `E ⊆ D`, `(ddᶜφ)ⁿ(E) ≤ Tⁿ Cap_D(E) + e_p(φ) T⁻ᵖ`. -/
theorem ma_le_relCapacity_add_localEnergy (hn : 0 < n) {D : Opens (ComplexModel n)}
    (hDb : Bornology.IsBounded (D : Set (ComplexModel n))) {φ : ComplexModel n → ℝ}
    (hφ : IsCegrellE0 D φ) {T : ℝ} (hT : 0 < T) {p : ℝ} (hp : 0 < p) {E : Set (ComplexModel n)}
    (hED : E ⊆ D) :
    canonicalBedfordTaylorMeasure D φ hφ.psh E ≤
      ENNReal.ofReal (T ^ n) * relCapacity D E +
        ENNReal.ofReal (T ^ (-p)) * localEnergy D p φ hφ.psh := by
  obtain ⟨hφT, hloc, -, -, hFle, -⟩ := hφ.truncation hn hDb hT hp
  set ν := canonicalBedfordTaylorMeasure D φ hφ.psh
  set νT := canonicalBedfordTaylorMeasure D _ hφT.psh
  set G : Set (ComplexModel n) := {z | z ∈ D ∧ -T < φ z} with hGdef
  have hGm : MeasurableSet G := measurableSet_superlevel hφ.psh (-T)
  have hsub : E ⊆ (E ∩ G) ∪ {z | z ∈ D ∧ φ z ≤ -T} := by
    intro z hz
    by_cases h : -T < φ z
    · exact Or.inl ⟨hz, hED hz, h⟩
    · exact Or.inr ⟨hED hz, not_lt.mp h⟩
  have hEG : ν (E ∩ G) = νT (E ∩ G) := by
    rw [← Measure.restrict_apply' hGm, ← hloc, Measure.restrict_apply' hGm]
  have hcapT : νT E ≤ ENNReal.ofReal (T ^ n) * relCapacity D E := by
    have := canonicalBedfordTaylorMeasure_le_relCapacity_of_bounds hφT.psh (a := -T) (b := 0)
      (by linarith) (fun z hz => ⟨le_max_right _ _, hφT.nonpos z hz⟩) E
    simpa only [zero_sub, neg_neg] using this
  calc ν E ≤ ν ((E ∩ G) ∪ {z | z ∈ D ∧ φ z ≤ -T}) := measure_mono hsub
    _ ≤ ν (E ∩ G) + ν {z | z ∈ D ∧ φ z ≤ -T} := measure_union_le _ _
    _ ≤ νT E + ENNReal.ofReal (T ^ (-p)) * localEnergy D p φ hφ.psh := by
        rw [hEG]
        exact add_le_add (measure_mono inter_subset_left) hFle
    _ ≤ _ := add_le_add hcapT le_rfl

/-- **Uniform capacity domination of the approximating measures** (the modulus `ω` of FPT's
proof of `thm:compact-bounded-subsolution-ball-dirichlet`, Step 2): if `φⱼ ∈ ℰ₀(D)` have
`e₁(φⱼ) ≤ C`, then `(ddᶜφⱼ)ⁿ(E) ≤ Tⁿ Cap_D(E) + C/T` for all `j`, all `E ⊆ D` and `T > 0`. -/
theorem ma_le_relCapacity_add_of_localEnergy_le (hn : 0 < n) {D : Opens (ComplexModel n)}
    (hDb : Bornology.IsBounded (D : Set (ComplexModel n))) {ι : Type*}
    {φ : ι → ComplexModel n → ℝ} (hφ : ∀ j, IsCegrellE0 D (φ j)) {C : ℝ}
    (hC : ∀ j, (localEnergy D 1 (φ j) (hφ j).psh).toReal ≤ C) (j : ι) {T : ℝ} (hT : 0 < T)
    {E : Set (ComplexModel n)} (hED : E ⊆ D) :
    canonicalBedfordTaylorMeasure D (φ j) (hφ j).psh E ≤
      ENNReal.ofReal (T ^ n) * relCapacity D E + ENNReal.ofReal (C / T) := by
  refine (ma_le_relCapacity_add_localEnergy hn hDb (hφ j) hT one_pos hED).trans ?_
  gcongr
  rw [← ENNReal.ofReal_toReal ((hφ j).localEnergy_ne_top zero_le_one),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hT.le _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.rpow_neg_one, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right (hC j) hT.le

/-- **Lebesgue tails of `ℰ₀` functions**: on a bounded open `D ⊆ B̄(0, ρ)`, for `φ` locally
bounded psh with boundary values `0`, `cₙ · vol({φ < -t}) ≤ 2ⁿ⁺ᵖ ρ²ⁿ t^{-(n+p)} e_p(φ)`
(`cₙ = n!/πⁿ`; the tail bound for `μ = cₙ dV ≤ (ddᶜ|z|²)ⁿ`). -/
theorem volume_sublevel_le_localEnergy (hn : 0 < n) {D : Opens (ComplexModel n)}
    (hDb : Bornology.IsBounded (D : Set (ComplexModel n))) {ρ : ℝ}
    (hρ : ∀ z ∈ D, ‖z‖ ≤ ρ) {φ : ComplexModel n → ℝ} (hφ : IsLocallyBoundedPshOn D φ)
    (hbd : ∀ ζ ∈ frontier (D : Set (ComplexModel n)),
      Tendsto φ (𝓝[(D : Set (ComplexModel n))] ζ) (𝓝 0)) {p t : ℝ} (hp : 0 < p) (ht : 0 < t) :
    ENNReal.ofReal (SGPT.NPP.LogConcavityDinew.mongeAmpereConst n) *
        volume {z | z ∈ D ∧ φ z < -t} ≤
      ENNReal.ofReal (2 ^ ((n : ℝ) + p) * (ρ ^ 2) ^ n * t ^ (-((n : ℝ) + p))) *
        localEnergy D p φ hφ := by
  set W : ComplexModel n → ℝ := fun z => (fun _ => (0 : ℝ)) z + 1 * (‖z‖ ^ 2 - 0) with hWdef
  have hW : IsLocallyBoundedPshOn D W := by
    have := isLocallyBoundedPshOn_linComb (isLocallyBoundedPshOn_zero D)
      (isLocallyBoundedPshOn_zero D) (Ω := D) (a := 0) (b := 0) (c := 1) le_rfl le_rfl
      zero_le_one
    convert this using 1
    funext z
    simp [hWdef]
  have hsum := ma_add_normSq_ge hn (isLocallyBoundedPshOn_zero D) one_pos 0 hW
  rw [one_pow, mul_one] at hsum
  have hμ : (ENNReal.ofReal (SGPT.NPP.LogConcavityDinew.mongeAmpereConst n) •
      volume.restrict (D : Set (ComplexModel n))).restrict D ≤
        canonicalBedfordTaylorMeasure D W hW := by
    rw [Measure.restrict_smul, Measure.restrict_restrict D.isOpen.measurableSet, inter_self]
    exact le_trans (Measure.le_add_left le_rfl) hsum
  have hWb : ∀ z ∈ D, 0 ≤ W z ∧ W z ≤ 0 + ρ ^ 2 := by
    intro z hz
    have h1 := hρ z hz
    simp only [hWdef, sub_zero, one_mul, zero_add]
    exact ⟨sq_nonneg _, pow_le_pow_left₀ (norm_nonneg z) h1 2⟩
  have := measure_sublevel_le_localEnergy hn hDb hφ hbd hW (sq_nonneg ρ) hWb hμ hp ht
  rw [Measure.smul_apply, Measure.restrict_apply' D.isOpen.measurableSet, smul_eq_mul] at this
  have hset : {z | z ∈ D ∧ φ z < -t} ∩ (D : Set (ComplexModel n)) = {z | z ∈ D ∧ φ z < -t} :=
    inter_eq_left.mpr fun z hz => hz.1
  rwa [hset] at this

end SGPT.Envelopes.MADirichlet
