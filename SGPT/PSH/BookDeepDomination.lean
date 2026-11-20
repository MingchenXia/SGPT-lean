import SGPT.Foundations.Analysis.Pending.BedfordTaylorLocalComparison
import SGPT.Foundations.Analysis.Pending.BedfordTaylorCompactMassEquality
import SGPT.Foundations.Analysis.Pending.BoundedPairMaxLocality
import SGPT.Foundations.Analysis.Pending.BedfordTaylorSlotAdd
import SGPT.Foundations.Analysis.Pending.BedfordTaylorIncreasingStepP
import SGPT.Foundations.Analysis.Pending.BedfordTaylorCapacity
import SGPT.PSH.Basic

/-!
# The local comparison and domination principles (`prop:dom_prin_loc`)

Source: `prop:dom_prin_loc` of the chapter *Plurisubharmonic functions* (Guedj–Zeriahi,
Cor. 3.31): let `Ω ⊆ ℂⁿ` be a bounded domain and `φ, ψ ∈ PSH(Ω)` locally bounded with

1. `liminf_{Ω ∋ w → z} (ψ(w) - φ(w)) ≥ 0` for every `z ∈ ∂Ω`;
2. `φ ≤ ψ` almost everywhere with respect to `(ddᶜψ)ⁿ`.

Then `φ ≤ ψ`.

The Monge–Ampère measure `(ddᶜψ)ⁿ` of a locally bounded psh function is the Bedford–Taylor
limit `SGPT.Foundations.Analysis.Pending.BedfordTaylor.IsBTLimit` (unique, and existing for every
locally bounded psh function).

We first prove the **comparison principle** for locally bounded (not necessarily continuous)
psh functions (`measure_lt_le_of_boundary`): if `liminf (u - v) ≥ 0` at `∂Ω`, then
`(ddᶜv)ⁿ{u < v} ≤ (ddᶜu)ⁿ{u < v}`. For `δ > 0` the set `{u + δ < v}` lies in a compact `K ⊆ Ω`;
`w = max(u + δ, v)` agrees with `u + δ` off `K`, so `w` and `u` have the same mass on a
neighbourhood `V ⋐ Ω` of `K` (local Stokes, `BedfordTaylor.measure_eq_of_eqOn_compl`), while
`(ddᶜw)ⁿ = (ddᶜu)ⁿ` on `{v < u + δ}` and `(ddᶜw)ⁿ = (ddᶜv)ⁿ` on `{u + δ < v}` (plurifine
locality of maxima, `BoundedPairMaxLocality.restrict_eq_of_bounded_pair_max`); comparing the
masses gives `(ddᶜv)ⁿ{u + δ < v} ≤ (ddᶜu)ⁿ{u < v}`, and `δ ↓ 0` finishes.

For the domination principle let `φ_ε = φ + ε(|z|² - M) ≤ φ` with `|z|² < M` on `Ω`. The
comparison principle and (2) give `(ddᶜφ_ε)ⁿ{ψ < φ_ε} = 0`; since
`(ddᶜφ_ε)ⁿ ≥ εⁿ (ddᶜ|z|²)ⁿ = εⁿ n!/πⁿ · Lebesgue` (slot additivity), `φ_ε ≤ ψ` almost
everywhere, hence everywhere on `Ω`; let `ε → 0`.

Main declarations:

* `SGPT.PSH.BookDeepDomination.measure_lt_le_of_boundary` — comparison principle;
* `SGPT.PSH.BookDeepDomination.le_of_isBTLimit_add` — `(ddᶜ(φ + ρ))ⁿ ≥ (ddᶜρ)ⁿ`;
* `SGPT.PSH.BookDeepDomination.le_on_of_domination` — domination, real-valued form;
* `SGPT.PSH.BookDeepDomination.domination_principle` — `prop:dom_prin_loc`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.PSH.BookDeepDomination

open Set Filter MeasureTheory TopologicalSpace Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open MongeAmpere BedfordTaylor
open scoped Topology ENNReal ComplexOrder

variable {n : ℕ}

/-! ### Closure properties and measurability -/

theorem isLocallyBoundedPshOn_add {Ω : Opens (ComplexModel n)} {f g : ComplexModel n → ℝ}
    (hf : IsLocallyBoundedPshOn Ω f) (hg : IsLocallyBoundedPshOn Ω g) :
    IsLocallyBoundedPshOn Ω fun z => f z + g z := by
  refine ⟨?_, fun z hz => ?_⟩
  · simpa only [EReal.coe_add] using hf.1.add hg.1
  · obtain ⟨V, hzV, hVΩ, C, hC⟩ := hf.2 z hz
    obtain ⟨V', hzV', -, C', hC'⟩ := hg.2 z hz
    refine ⟨V ⊓ V', ⟨hzV, hzV'⟩, inf_le_left.trans hVΩ, C + C', fun y hy => ?_⟩
    exact (abs_add_le _ _).trans (add_le_add (hC y hy.1) (hC' y hy.2))

theorem upperSemicontinuousAt_of_isLocallyBoundedPshOn {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u) {z : ComplexModel n}
    (hz : z ∈ Ω) : UpperSemicontinuousAt u z := by
  intro c hc
  have h := (hu.1 z hz).upperSemicontinuousAt (c : EReal) (EReal.coe_lt_coe_iff.mpr hc)
  filter_upwards [h] with y hy
  exact EReal.coe_lt_coe_iff.mp hy

theorem upperSemicontinuous_restrict {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) : UpperSemicontinuous fun z : Ω => u z := by
  intro z c hc
  exact (continuous_subtype_val.tendsto z).eventually
    (upperSemicontinuousAt_of_isLocallyBoundedPshOn hu z.2 c hc)

theorem measurableSet_add_lt_add {Ω : Opens (ComplexModel n)} {f g : ComplexModel n → ℝ}
    (hf : IsLocallyBoundedPshOn Ω f) (hg : IsLocallyBoundedPshOn Ω g) (a b : ℝ) :
    MeasurableSet {z | z ∈ Ω ∧ f z + a < g z + b} := by
  have hfm : Measurable fun z : Ω => f z + a :=
    (upperSemicontinuous_restrict hf).measurable.add_const a
  have hgm : Measurable fun z : Ω => g z + b :=
    (upperSemicontinuous_restrict hg).measurable.add_const b
  have hset : {z | z ∈ Ω ∧ f z + a < g z + b} =
      Subtype.val '' {z : Ω | f z + a < g z + b} := by
    ext z
    constructor
    · rintro ⟨hz, h⟩
      exact ⟨⟨z, hz⟩, h, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
  rw [hset]
  exact MeasurableSet.subtype_image Ω.isOpen.measurableSet (measurableSet_lt hfm hgm)

/-! ### The comparison principle for locally bounded psh functions -/

/-- **Core of the comparison principle.** If `{u + δ < v}` lies in a compact `K ⊆ Ω`, then
`(ddᶜv)ⁿ {u + δ < v} ≤ (ddᶜu)ⁿ {u < v}`. -/
theorem measure_add_lt_le_of_subset_compact (hn : 0 < n) {Ω : Opens (ComplexModel n)}
    {u v : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn Ω v)
    {μu μv : Measure (ComplexModel n)} (hμu : IsBTLimit Ω (fun _ => u) μu)
    (hμv : IsBTLimit Ω (fun _ => v) μv) {δ : ℝ} (hδ : 0 < δ) {K : Set (ComplexModel n)}
    (hKc : IsCompact K) (hKΩ : K ⊆ Ω) (hAK : {z | z ∈ Ω ∧ u z + δ < v z} ⊆ K) :
    μv {z | z ∈ Ω ∧ u z + δ < v z} ≤ μu {z | z ∈ Ω ∧ u z < v z} := by
  classical
  have hall : ∀ P : Prop, (∀ _ : Fin n, P) ↔ P := fun P => ⟨fun h => h ⟨0, hn⟩, fun h _ => h⟩
  set A : Set (ComplexModel n) := {z | z ∈ Ω ∧ u z + δ < v z} with hAdef
  set B : Set (ComplexModel n) := {z | z ∈ Ω ∧ v z < u z + δ} with hBdef
  -- an open `V ⋐ Ω` around `K`
  obtain ⟨V, hVo, hKV, hVΩ, hVc⟩ := exists_open_between_and_isCompact_closure hKc Ω.isOpen hKΩ
  set V' : Opens (ComplexModel n) := ⟨V, hVo⟩ with hV'def
  have hVrc : RelativelyCompactIn V' Ω := ⟨hVc, hVΩ⟩
  have hVsub : V ⊆ Ω := subset_closure.trans hVΩ
  have hVfin : μu V < ⊤ := (measure_mono subset_closure).trans_lt (hμu.2.1 _ hVc hVΩ)
  -- the maximum `w = max(u + δ, v)`
  set w : ComplexModel n → ℝ := fun z => max (u z + δ) (v z) with hwdef
  have hw : IsLocallyBoundedPshOn Ω w :=
    BedfordTaylor.IsLocallyBoundedPshOn.max (BedfordTaylor.IsLocallyBoundedPshOn.add_const hu δ) hv
  obtain ⟨μw, hμw⟩ := exists_isBTLimit_of_isLocallyBoundedPshOn (u := fun _ : Fin n => w)
    fun _ => hw
  have hμuδ := hμu.add_const_diag δ
  have hmass : μw V = μu V :=
    measure_eq_of_eqOn_compl hw (BedfordTaylor.IsLocallyBoundedPshOn.add_const hu δ) hVrc hKc hKV
      (fun z hzΩ hzK => max_eq_left (not_lt.mp fun h => hzK (hAK ⟨hzΩ, h⟩))) hμw hμuδ
  have hloc1 := BoundedPairMaxLocality.restrict_eq_of_bounded_pair_max
    (u := fun _ => fun z => u z + δ) (w := fun _ => w) (g := fun _ => v) hμuδ hμw
    (fun _ => hv) (fun _ z _ => rfl)
  have hloc2 := BoundedPairMaxLocality.restrict_eq_of_bounded_pair_max
    (u := fun _ => v) (w := fun _ => w) (g := fun _ => fun z => u z + δ) hμv hμw
    (fun _ => BedfordTaylor.IsLocallyBoundedPshOn.add_const hu δ) (fun _ z _ => max_comm _ _)
  simp only [hall] at hloc1 hloc2
  have hA : MeasurableSet A := by
    have h := measurableSet_add_lt_add hu hv δ 0
    simp only [add_zero] at h
    exact h
  have hB : MeasurableSet B := by
    have h := measurableSet_add_lt_add hv hu 0 δ
    simp only [add_zero] at h
    exact h
  have e1 : μv A = μw A := by
    have h := congrArg (fun μ : Measure (ComplexModel n) => μ A) hloc2
    simp only [Measure.restrict_apply hA] at h
    rw [← hAdef, inter_self] at h
    exact h.symm
  have e2 : μw (V ∩ B) = μu (V ∩ B) := by
    have h := congrArg (fun μ : Measure (ComplexModel n) => μ V) hloc1
    simp only [Measure.restrict_apply hVo.measurableSet] at h
    exact h
  have hsplitw : μw (V ∩ B) + μw (V \ B) = μw V := measure_inter_add_sdiff V hB
  have hsplitu : μu (V ∩ B) + μu (V \ B) = μu V := measure_inter_add_sdiff V hB
  have hAVB : A ⊆ V \ B := fun z hz => ⟨hKV (hAK hz), fun hzB => by linarith [hz.2, hzB.2]⟩
  have hVB : V \ B ⊆ {z | z ∈ Ω ∧ u z < v z} := by
    rintro z ⟨hzV, hzB⟩
    refine ⟨hVsub hzV, ?_⟩
    have : ¬ v z < u z + δ := fun h => hzB ⟨hVsub hzV, h⟩
    linarith [not_lt.mp this]
  have hfin : μu (V ∩ B) ≠ ⊤ := ((measure_mono inter_subset_left).trans_lt hVfin).ne
  calc μv A = μw A := e1
    _ ≤ μw (V \ B) := measure_mono hAVB
    _ ≤ μu (V \ B) := by
        have h : μu (V ∩ B) + μw (V \ B) = μu (V ∩ B) + μu (V \ B) := by
          rw [← e2, hsplitw, hmass, e2, hsplitu]
        exact ((ENNReal.add_right_inj hfin).mp h).le
    _ ≤ μu {z | z ∈ Ω ∧ u z < v z} := measure_mono hVB

/-- Letting `δ ↓ 0` in the core estimate. -/
theorem measure_lt_le_of_forall_add {Ω : Opens (ComplexModel n)} {u v : ComplexModel n → ℝ}
    {μu μv : Measure (ComplexModel n)}
    (hkey : ∀ δ : ℝ, 0 < δ → μv {z | z ∈ Ω ∧ u z + δ < v z} ≤ μu {z | z ∈ Ω ∧ u z < v z}) :
    μv {z | z ∈ Ω ∧ u z < v z} ≤ μu {z | z ∈ Ω ∧ u z < v z} := by
  -- let `δ ↓ 0`
  set A : ℕ → Set (ComplexModel n) := fun k => {z | z ∈ Ω ∧ u z + 1 / ((k : ℝ) + 1) < v z}
    with hAdef
  have hU : {z | z ∈ Ω ∧ u z < v z} = ⋃ k, A k := by
    ext z
    simp only [hAdef, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨hz, h⟩
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
      exact ⟨k, hz, by linarith⟩
    · rintro ⟨k, hz, h⟩
      exact ⟨hz, by have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
                    linarith⟩
  have hmono : Monotone A := by
    intro k l hkl z hz
    refine ⟨hz.1, lt_of_le_of_lt ?_ hz.2⟩
    have : 1 / ((l : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hkl 1)
    linarith
  calc μv {z | z ∈ Ω ∧ u z < v z} = μv (⋃ k, A k) := by rw [← hU]
    _ = ⨆ k, μv (A k) := hmono.measure_iUnion
    _ ≤ μu {z | z ∈ Ω ∧ u z < v z} := iSup_le fun k => hkey _ (by positivity)


/-- **Comparison principle**, compact form: if `{u < v}` lies in a compact subset of `Ω`, then
`(ddᶜv)ⁿ {u < v} ≤ (ddᶜu)ⁿ {u < v}`. -/
theorem measure_lt_le_of_subset_compact (hn : 0 < n) {Ω : Opens (ComplexModel n)}
    {u v : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn Ω v)
    {μu μv : Measure (ComplexModel n)} (hμu : IsBTLimit Ω (fun _ => u) μu)
    (hμv : IsBTLimit Ω (fun _ => v) μv) {K : Set (ComplexModel n)} (hKc : IsCompact K)
    (hKΩ : K ⊆ Ω) (hK : {z | z ∈ Ω ∧ u z < v z} ⊆ K) :
    μv {z | z ∈ Ω ∧ u z < v z} ≤ μu {z | z ∈ Ω ∧ u z < v z} :=
  measure_lt_le_of_forall_add fun δ hδ =>
    measure_add_lt_le_of_subset_compact hn hu hv hμu hμv hδ hKc hKΩ
      fun z hz => hK ⟨hz.1, by linarith [hz.2]⟩

/-- **Comparison principle** (Bedford–Taylor; Błocki, Thm. 2.2.6) for locally bounded psh
functions on a bounded open set: if `v - u` has nonpositive upper limits at the boundary, then
`(ddᶜv)ⁿ {u < v} ≤ (ddᶜu)ⁿ {u < v}`. -/
theorem measure_lt_le_of_boundary (hn : 0 < n) {Ω : Opens (ComplexModel n)}
    (hΩ : Bornology.IsBounded (Ω : Set (ComplexModel n))) {u v : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn Ω v)
    (hbd : ∀ ζ ∈ frontier (Ω : Set (ComplexModel n)), ∀ δ > 0,
      ∀ᶠ z in 𝓝[(Ω : Set (ComplexModel n))] ζ, v z - u z < δ)
    {μu μv : Measure (ComplexModel n)} (hμu : IsBTLimit Ω (fun _ => u) μu)
    (hμv : IsBTLimit Ω (fun _ => v) μv) :
    μv {z | z ∈ Ω ∧ u z < v z} ≤ μu {z | z ∈ Ω ∧ u z < v z} := by
  classical
  refine measure_lt_le_of_forall_add fun δ hδ => ?_
  -- a compact `K ⊆ Ω` containing `{u + δ < v}`
  have hW : ∀ ζ ∈ frontier (Ω : Set (ComplexModel n)), ∃ W : Set (ComplexModel n),
      IsOpen W ∧ ζ ∈ W ∧ ∀ z ∈ W, z ∈ Ω → v z - u z < δ := by
    intro ζ hζ
    have h := hbd ζ hζ δ hδ
    rw [eventually_nhdsWithin_iff] at h
    obtain ⟨W, hWs, hWo, hζW⟩ := _root_.mem_nhds_iff.mp h
    exact ⟨W, hWo, hζW, fun z hz hzΩ => hWs hz hzΩ⟩
  choose W hWo hζW hWP using hW
  set N : Set (ComplexModel n) := ⋃ ζ, ⋃ (h : ζ ∈ frontier (Ω : Set (ComplexModel n))), W ζ h
    with hNdef
  have hNo : IsOpen N := isOpen_iUnion fun ζ => isOpen_iUnion fun h => hWo ζ h
  set K : Set (ComplexModel n) := closure (Ω : Set (ComplexModel n)) \ N with hKdef
  have hKc : IsCompact K :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_closure.sdiff hNo)
      (hΩ.closure.subset sdiff_subset)
  have hKΩ : K ⊆ Ω := by
    rintro z ⟨hzc, hzN⟩
    by_contra hzΩ
    have hzf : z ∈ frontier (Ω : Set (ComplexModel n)) := by
      refine ⟨hzc, ?_⟩
      rwa [Ω.isOpen.interior_eq]
    exact hzN (mem_iUnion₂.mpr ⟨z, hzf, hζW z hzf⟩)
  refine measure_add_lt_le_of_subset_compact hn hu hv hμu hμv hδ hKc hKΩ ?_
  rintro z ⟨hzΩ, hz⟩
  refine ⟨subset_closure hzΩ, fun hzN => ?_⟩
  obtain ⟨ζ, hζ, hzW⟩ := mem_iUnion₂.mp hzN
  have := hWP ζ hζ z hzW hzΩ
  linarith

/-! ### Superadditivity -/

/-- `(ddᶜ(φ + ρ))ⁿ ≥ (ddᶜρ)ⁿ` for locally bounded psh `φ, ρ`, by slot additivity. -/
theorem le_of_isBTLimit_add {Ω : Opens (ComplexModel n)} {φ ρ : ComplexModel n → ℝ}
    (hφ : IsLocallyBoundedPshOn Ω φ) (hρ : IsLocallyBoundedPshOn Ω ρ)
    {μ ν : Measure (ComplexModel n)} (hμ : IsBTLimit Ω (fun _ => fun z => φ z + ρ z) μ)
    (hν : IsBTLimit Ω (fun _ => ρ) ν) : ν ≤ μ := by
  classical
  set T : ℕ → Fin n → ComplexModel n → ℝ :=
    fun k i => if i.val < k then fun z => φ z + ρ z else ρ with hTdef
  have hTb : ∀ k i, IsLocallyBoundedPshOn Ω (T k i) := by
    intro k i
    simp only [hTdef]
    split_ifs
    · exact isLocallyBoundedPshOn_add hφ hρ
    · exact hρ
  have key : ∀ k, k ≤ n → ∀ μk : Measure (ComplexModel n), IsBTLimit Ω (T k) μk → ν ≤ μk := by
    intro k
    induction k with
    | zero =>
      intro _ μk hμk
      have h0 : T 0 = fun _ => ρ := by
        funext i
        simp [hTdef]
      rw [h0] at hμk
      exact (hν.unique hμk).le
    | succ k ih =>
      intro hk μk hμk
      set i₀ : Fin n := ⟨k, hk⟩ with hi₀
      have hT1 : T (k + 1) = Function.update (T k) i₀ fun z => φ z + ρ z := by
        funext i
        by_cases hi : i = i₀
        · rw [hi, Function.update_self]
          show (if (i₀ : ℕ) < k + 1 then (fun z => φ z + ρ z) else ρ) = _
          rw [if_pos (by simp [hi₀])]
        · rw [Function.update_of_ne hi]
          have hik : i.val ≠ k := fun h => hi (Fin.ext h)
          simp only [hTdef]
          by_cases hlt : i.val < k
          · simp [hlt, Nat.lt_succ_of_lt hlt]
          · have hlt' : ¬ i.val < k + 1 := by omega
            simp [hlt, hlt']
      have hT0 : Function.update (T k) i₀ ρ = T k := by
        funext i
        by_cases hi : i = i₀
        · rw [hi, Function.update_self]
          show ρ = if (i₀ : ℕ) < k then (fun z => φ z + ρ z) else ρ
          rw [if_neg (by simp [hi₀])]
        · rw [Function.update_of_ne hi]
      obtain ⟨μa, hμa⟩ := exists_isBTLimit_of_isLocallyBoundedPshOn
        (u := Function.update (T k) i₀ φ) fun i => by
          by_cases hi : i = i₀
          · subst hi
            simpa using hφ
          · rw [Function.update_of_ne hi]
            exact hTb k i
      obtain ⟨μb, hμb⟩ := exists_isBTLimit_of_isLocallyBoundedPshOn (u := T k) (hTb k)
      rw [hT1] at hμk
      have hsum := hμk.add_slot i₀ hμa (by rw [hT0]; exact hμb)
      rw [hsum]
      exact Measure.le_add_left (ih (Nat.le_of_succ_le hk) μb hμb)
  have hTn : T n = fun _ => fun z => φ z + ρ z := by
    funext i
    simp [hTdef, i.isLt]
  exact key n le_rfl μ (by rw [hTn]; exact hμ)

theorem isLocallyBoundedPshOn_mul_normSq (Ω : Opens (ComplexModel n)) {ε : ℝ} (hε : 0 < ε) :
    IsLocallyBoundedPshOn Ω fun z => ε * ‖z‖ ^ 2 := by
  refine ⟨?_, fun z hz => ?_⟩
  · have h := ((discPshOn_norm_sq (Ω : Set (ComplexModel n))).const_mul hε).plurisubharmonicOn
      Ω.isOpen
    simpa only [EReal.coe_mul, EReal.coe_pow] using h
  · refine ⟨Ω ⊓ ⟨ball z 1, isOpen_ball⟩, ⟨hz, mem_ball_self one_pos⟩, inf_le_left,
      ε * (‖z‖ + 1) ^ 2, fun y hy => ?_⟩
    have hy1 : ‖y‖ ≤ ‖z‖ + 1 := by
      have h := hy.2
      change dist y z < 1 at h
      rw [dist_eq_norm] at h
      have := norm_le_insert' y z
      linarith [norm_sub_norm_le y z]
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hy1 2) hε.le

/-- `(ddᶜ(ε|z|²))ⁿ = εⁿ n!/πⁿ · Lebesgue` on `Ω`. -/
theorem isBTLimit_mul_normSq (Ω : Opens (ComplexModel n)) {ε : ℝ} (hε : 0 ≤ ε) :
    IsBTLimit Ω (fun _ => fun z => ε * ‖z‖ ^ 2)
      ((ENNReal.ofReal ε ^ n * ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n)) •
        volume.restrict (Ω : Set (ComplexModel n))) := by
  have hb : IsLocallyBoundedPshOn Ω fun z : ComplexModel n => ‖z‖ ^ 2 := by
    simpa only [one_mul] using isLocallyBoundedPshOn_mul_normSq Ω one_pos
  obtain ⟨μ₀, hμ₀⟩ := exists_isBTLimit_of_isLocallyBoundedPshOn
    (u := fun _ : Fin n => fun z : ComplexModel n => ‖z‖ ^ 2) fun _ => hb
  have hd := hμ₀.eq_densityMeasure fun _ =>
    ⟨(contDiff_norm_sq ℝ).contDiffOn, fun z _ => by
      rw [complexHessian_norm_sq]; exact Matrix.PosSemidef.one⟩
  have hden : densityMeasure Ω (fun _ : Fin n => fun z : ComplexModel n => ‖z‖ ^ 2) =
      ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n) •
        volume.restrict (Ω : Set (ComplexModel n)) := by
    unfold densityMeasure
    simp only [MixedMongeAmpere.mixedDensity_diagonal, smoothDensity_norm_sq]
    rw [withDensity_const]
  have h := hμ₀.const_mul_all hε
  rw [hd, hden, smul_smul] at h
  exact h

/-! ### The domination principle -/

/-- **Domination principle**, real-valued form: for locally bounded psh `φ, ψ` on a bounded open
`Ω ⊆ ℂⁿ` (`n ≥ 1`) with `φ - ψ` having nonpositive upper limits at `∂Ω` and `φ ≤ ψ` almost
everywhere for `(ddᶜψ)ⁿ`, one has `φ ≤ ψ` on `Ω`. -/
theorem le_on_of_domination (hn : 0 < n) {Ω : Opens (ComplexModel n)}
    (hΩ : Bornology.IsBounded (Ω : Set (ComplexModel n))) {φ ψ : ComplexModel n → ℝ}
    (hφ : IsLocallyBoundedPshOn Ω φ) (hψ : IsLocallyBoundedPshOn Ω ψ)
    (h1 : ∀ ζ ∈ frontier (Ω : Set (ComplexModel n)), ∀ δ > 0,
      ∀ᶠ z in 𝓝[(Ω : Set (ComplexModel n))] ζ, φ z - ψ z < δ)
    {μ : Measure (ComplexModel n)} (hμ : IsBTLimit Ω (fun _ => ψ) μ)
    (h2 : ∀ᵐ z ∂μ, φ z ≤ ψ z) : ∀ z ∈ Ω, φ z ≤ ψ z := by
  obtain ⟨R, hR⟩ := hΩ.subset_closedBall 0
  set M : ℝ := R ^ 2 + 1 with hMdef
  have hM : ∀ z ∈ Ω, ‖z‖ ^ 2 < M := by
    intro z hz
    have h := hR hz
    rw [mem_closedBall, dist_zero_right] at h
    have hR0 : 0 ≤ R := (norm_nonneg z).trans h
    nlinarith [norm_nonneg z]
  have hε : ∀ ε : ℝ, 0 < ε → ∀ z ∈ Ω, φ z + ε * (‖z‖ ^ 2 - M) ≤ ψ z := by
    intro ε hε
    set φ' : ComplexModel n → ℝ := fun z => φ z + -(ε * M) with hφ'def
    set φε : ComplexModel n → ℝ := fun z => φ' z + ε * ‖z‖ ^ 2 with hφεdef
    have hφεeq : ∀ z, φε z = φ z + ε * (‖z‖ ^ 2 - M) := by intro z; simp only [hφεdef, hφ'def]; ring
    have hφ'b : IsLocallyBoundedPshOn Ω φ' := BedfordTaylor.IsLocallyBoundedPshOn.add_const hφ _
    have hρb := isLocallyBoundedPshOn_mul_normSq Ω hε
    have hφεb : IsLocallyBoundedPshOn Ω φε := isLocallyBoundedPshOn_add hφ'b hρb
    obtain ⟨με, hμε⟩ := exists_isBTLimit_of_isLocallyBoundedPshOn (u := fun _ : Fin n => φε)
      fun _ => hφεb
    -- the comparison principle for `ψ` and `φ_ε`
    have hbd : ∀ ζ ∈ frontier (Ω : Set (ComplexModel n)), ∀ δ > 0,
        ∀ᶠ z in 𝓝[(Ω : Set (ComplexModel n))] ζ, φε z - ψ z < δ := by
      intro ζ hζ δ hδ
      filter_upwards [h1 ζ hζ δ hδ, self_mem_nhdsWithin] with z hz hzΩ
      have hneg : ε * (‖z‖ ^ 2 - M) < 0 :=
        mul_neg_of_pos_of_neg hε (by linarith [hM z hzΩ])
      rw [hφεeq]
      linarith
    have hcomp := measure_lt_le_of_boundary hn hΩ hψ hφεb hbd hμ hμε
    set S : Set (ComplexModel n) := {z | z ∈ Ω ∧ ψ z < φε z} with hSdef
    have hS0 : μ S = 0 := by
      apply measure_mono_null _ (ae_iff.mp h2)
      rintro z ⟨hzΩ, hz⟩ hle
      have hneg : ε * (‖z‖ ^ 2 - M) < 0 :=
        mul_neg_of_pos_of_neg hε (by linarith [hM z hzΩ])
      rw [hφεeq] at hz
      linarith
    have hSε : με S = 0 := le_antisymm (hcomp.trans hS0.le) bot_le
    -- Lebesgue-null by the lower bound `(ddᶜφ_ε)ⁿ ≥ εⁿ (ddᶜ|z|²)ⁿ`
    have hlow := le_of_isBTLimit_add hφ'b hρb hμε (isBTLimit_mul_normSq Ω hε.le)
    have hvol : volume.restrict (Ω : Set (ComplexModel n)) S = 0 := by
      have h := hlow S
      rw [hSε, Measure.smul_apply, nonpos_iff_eq_zero, smul_eq_mul, mul_eq_zero] at h
      rcases h with h | h
      · exfalso
        rw [mul_eq_zero] at h
        rcases h with h | h
        · exact (pow_ne_zero n (ENNReal.ofReal_pos.mpr hε).ne') h
        · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne' h
      · exact h
    -- hence `φ_ε ≤ ψ` almost everywhere, and everywhere on `Ω`
    have hae : (fun z => ((max (φε z) (ψ z) : ℝ) : EReal)) =ᵐ[volume.restrict (Ω : Set _)]
        fun z => ((ψ z : ℝ) : EReal) := by
      have hnot : ∀ᵐ z ∂volume.restrict (Ω : Set (ComplexModel n)), z ∉ S :=
        measure_eq_zero_iff_ae_notMem.mp hvol
      filter_upwards [hnot, ae_restrict_mem Ω.isOpen.measurableSet] with z hz hzΩ
      have : φε z ≤ ψ z := not_lt.mp fun h => hz ⟨hzΩ, h⟩
      rw [max_eq_right this]
    have heq := PlurisubharmonicOn.eqOn_of_ae_eq
      (BedfordTaylor.IsLocallyBoundedPshOn.max hφεb hψ).1 hψ.1 Ω.isOpen volume hae
    intro z hz
    have h := heq hz
    simp only [EReal.coe_eq_coe_iff] at h
    rw [← hφεeq]
    exact (max_eq_right_iff.mp h)
  intro z hz
  have hMz : 0 < M - ‖z‖ ^ 2 := by linarith [hM z hz]
  refine le_of_forall_pos_le_add fun η hη => ?_
  have h := hε (η / (M - ‖z‖ ^ 2)) (div_pos hη hMz) z hz
  have hcalc : η / (M - ‖z‖ ^ 2) * (‖z‖ ^ 2 - M) = -η := by
    field_simp
    ring
  rw [hcalc] at h
  linarith

/-! ### `prop:dom_prin_loc` for extended-real psh functions -/

/-- A locally bounded `φ ∈ PSH(Ω)` is real-valued on `Ω`, and its real part is a locally bounded
psh function in the sense of the Bedford–Taylor theory. -/
theorem isLocallyBoundedPshOn_toReal {Ω : Opens (ComplexModel n)} {φ : ComplexModel n → EReal}
    (hφ : SGPT.PSH.PSHOn φ Ω)
    (hφb : ∀ z ∈ Ω, ∃ U ∈ 𝓝 z, ∃ C : ℝ, ∀ w ∈ U, ((-C : ℝ) : EReal) ≤ φ w ∧ φ w ≤ C) :
    IsLocallyBoundedPshOn Ω (fun z => (φ z).toReal) ∧
      ∀ z ∈ Ω, (((φ z).toReal : ℝ) : EReal) = φ z := by
  have hfin : ∀ z ∈ Ω, (((φ z).toReal : ℝ) : EReal) = φ z := by
    intro z hz
    obtain ⟨U, hU, C, hC⟩ := hφb z hz
    obtain ⟨h1, h2⟩ := hC z (mem_of_mem_nhds hU)
    exact EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top C) h2)
      (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h1)
  refine ⟨⟨fun z hz => ?_, fun z hz => ?_⟩, hfin⟩
  · refine ((hφ.disc.plurisubharmonicOn Ω.isOpen) z hz).congr ?_
    filter_upwards [Ω.isOpen.mem_nhds hz] with w hw
    exact (hfin w hw).symm
  · obtain ⟨U, hU, C, hC⟩ := hφb z hz
    obtain ⟨V, hVU, hVo, hzV⟩ := _root_.mem_nhds_iff.mp hU
    refine ⟨Ω ⊓ ⟨V, hVo⟩, ⟨hz, hzV⟩, inf_le_left, C, fun w hw => ?_⟩
    obtain ⟨h1, h2⟩ := hC w (hVU hw.2)
    rw [← hfin w hw.1] at h1 h2
    exact abs_le.mpr ⟨EReal.coe_le_coe_iff.mp h1, EReal.coe_le_coe_iff.mp h2⟩

/-- **`prop:dom_prin_loc`** (local domination principle). Let `Ω ⊆ ℂⁿ` be a bounded open set and
`φ, ψ ∈ PSH(Ω)` locally bounded. Assume

1. `liminf_{Ω ∋ w → z} (ψ(w) - φ(w)) ≥ 0` for every `z ∈ ∂Ω`;
2. `φ ≤ ψ` almost everywhere with respect to `(ddᶜψ)ⁿ`, the Bedford–Taylor Monge–Ampère measure
   of the (real-valued) locally bounded psh function `ψ`.

Then `φ ≤ ψ` on `Ω`. -/
theorem domination_principle {Ω : Opens (ComplexModel n)}
    (hΩ : Bornology.IsBounded (Ω : Set (ComplexModel n))) {φ ψ : ComplexModel n → EReal}
    (hφ : SGPT.PSH.PSHOn φ Ω) (hψ : SGPT.PSH.PSHOn ψ Ω)
    (hφb : ∀ z ∈ Ω, ∃ U ∈ 𝓝 z, ∃ C : ℝ, ∀ w ∈ U, ((-C : ℝ) : EReal) ≤ φ w ∧ φ w ≤ C)
    (hψb : ∀ z ∈ Ω, ∃ U ∈ 𝓝 z, ∃ C : ℝ, ∀ w ∈ U, ((-C : ℝ) : EReal) ≤ ψ w ∧ ψ w ≤ C)
    (h1 : ∀ z ∈ frontier (Ω : Set (ComplexModel n)),
      0 ≤ liminf (fun w => ψ w - φ w) (𝓝[(Ω : Set (ComplexModel n))] z))
    {μ : Measure (ComplexModel n)} (hμ : IsBTLimit Ω (fun _ => fun z => (ψ z).toReal) μ)
    (h2 : ∀ᵐ z ∂μ, φ z ≤ ψ z) : ∀ z ∈ Ω, φ z ≤ ψ z := by
  obtain ⟨hφr, hφe⟩ := isLocallyBoundedPshOn_toReal hφ hφb
  obtain ⟨hψr, hψe⟩ := isLocallyBoundedPshOn_toReal hψ hψb
  have hΩae : ∀ᵐ z ∂μ, z ∈ Ω := by
    rw [ae_iff]
    exact hμ.1
  have h2' : ∀ᵐ z ∂μ, (φ z).toReal ≤ (ψ z).toReal := by
    filter_upwards [h2, hΩae] with z hz hzΩ
    rw [← hφe z hzΩ, ← hψe z hzΩ] at hz
    exact EReal.coe_le_coe_iff.mp hz
  suffices hreal : ∀ z ∈ Ω, (φ z).toReal ≤ (ψ z).toReal by
    intro z hz
    rw [← hφe z hz, ← hψe z hz]
    exact EReal.coe_le_coe_iff.mpr (hreal z hz)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- dimension zero: `(ddᶜψ)⁰` is Lebesgue measure on the point
    intro z hz
    have hsub : ∀ w : ComplexModel 0, w = z := fun w => by
      ext i
      exact i.elim0
    have hd := hμ.eq_densityMeasure fun _ =>
      ⟨by
        have hc : (fun w => (ψ w).toReal) = fun _ => (ψ z).toReal := by
          funext w; rw [hsub w]
        rw [hc]
        exact contDiffOn_const,
      fun w _ => by
        rw [Subsingleton.elim (complexHessian (fun w => (ψ w).toReal) w) 1]
        exact Matrix.PosSemidef.one⟩
    have hpos : μ {z} ≠ 0 := by
      rw [hd, densityMeasure, withDensity_apply _ (measurableSet_singleton z)]
      simp only [MixedMongeAmpere.mixedDensity_diagonal, smoothDensity, Nat.factorial_zero,
        Nat.cast_one, pow_zero, div_one, Matrix.det_isEmpty, Complex.one_re, mul_one,
        ENNReal.ofReal_one, lintegral_const, one_mul]
      rw [Measure.restrict_apply MeasurableSet.univ, univ_inter,
        Measure.restrict_apply (measurableSet_singleton z), Set.singleton_inter_of_mem hz]
      have huniv : ({z} : Set (ComplexModel 0)) = univ :=
        eq_univ_of_forall fun w => mem_singleton_iff.mpr (hsub w)
      rw [huniv]
      exact Measure.measure_univ_ne_zero.mpr (NeZero.ne _)
    by_contra hlt
    apply hpos
    apply measure_mono_null _ (ae_iff.mp h2')
    intro w hw
    rw [mem_singleton_iff.mp hw]
    exact hlt
  · refine le_on_of_domination hn hΩ hφr hψr ?_ hμ h2'
    intro ζ hζ δ hδ
    have hlt : ((-δ : ℝ) : EReal) < liminf (fun w => ψ w - φ w) (𝓝[(Ω : Set _)] ζ) :=
      (EReal.coe_lt_coe_iff.mpr (by linarith : -δ < 0)).trans_le (by simpa using h1 ζ hζ)
    filter_upwards [eventually_lt_of_lt_liminf hlt, self_mem_nhdsWithin] with w hw hwΩ
    rw [← hφe w hwΩ, ← hψe w hwΩ, ← EReal.coe_sub, EReal.coe_lt_coe_iff] at hw
    linarith

/-! ### Uniqueness of the balayage (`prop:BT_balayage`, uniqueness and `ψ ≥ φ`) -/

theorem isLocallyBoundedPshOn_mono {Ω Ω' : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hΩ' : Ω' ≤ Ω) : IsLocallyBoundedPshOn Ω' u := by
  refine ⟨hu.1.mono hΩ', fun z hz => ?_⟩
  obtain ⟨V, hzV, hVΩ, C, hC⟩ := hu.2 z (hΩ' hz)
  exact ⟨V ⊓ Ω', ⟨hzV, hz⟩, inf_le_right, C, fun w hw => hC w hw.1⟩

/-- If `ψ` is locally bounded psh on `Ω`, `(ddᶜψ)ⁿ` puts no mass on an open `D` with compact
closure in `Ω`, and `φ ≤ ψ` off `D` for a locally bounded psh `φ`, then `φ ≤ ψ` on `Ω`. -/
theorem le_of_le_off_of_measure_eq_zero (hn : 0 < n) {Ω : Opens (ComplexModel n)}
    {D : Set (ComplexModel n)} (hDc : IsCompact (closure D)) (hDΩ : closure D ⊆ Ω)
    {φ ψ : ComplexModel n → ℝ} (hφ : IsLocallyBoundedPshOn Ω φ) (hψ : IsLocallyBoundedPshOn Ω ψ)
    (hoff : ∀ z ∈ Ω, z ∉ D → φ z ≤ ψ z) {μ : Measure (ComplexModel n)}
    (hμ : IsBTLimit Ω (fun _ => ψ) μ) (hzero : μ D = 0) : ∀ z ∈ Ω, φ z ≤ ψ z := by
  -- a bounded open `Ω' ⊆ Ω` containing `closure D`
  obtain ⟨R, hR⟩ := hDc.isBounded.subset_closedBall 0
  set Ω' : Opens (ComplexModel n) := Ω ⊓ ⟨ball 0 (R + 1), isOpen_ball⟩ with hΩ'def
  have hΩ'Ω : Ω' ≤ Ω := inf_le_left
  have hDΩ' : closure D ⊆ Ω' := fun z hz => ⟨hDΩ hz, by
    have h := hR hz
    rw [mem_closedBall] at h
    exact mem_ball.mpr (by linarith)⟩
  have hφ' := isLocallyBoundedPshOn_mono hφ hΩ'Ω
  have hψ' := isLocallyBoundedPshOn_mono hψ hΩ'Ω
  have hμ' := hμ.restrict_opens hΩ'Ω
  set M : ℝ := (R + 1) ^ 2 + 1 with hMdef
  have hM : ∀ z ∈ Ω', ‖z‖ ^ 2 < M := by
    intro z hz
    have h := hz.2
    change dist z 0 < R + 1 at h
    rw [dist_zero_right] at h
    nlinarith [norm_nonneg z]
  have hε : ∀ ε : ℝ, 0 < ε → ∀ z ∈ Ω', φ z + ε * (‖z‖ ^ 2 - M) ≤ ψ z := by
    intro ε hε
    set φ'' : ComplexModel n → ℝ := fun z => φ z + -(ε * M) with hφ''def
    set φε : ComplexModel n → ℝ := fun z => φ'' z + ε * ‖z‖ ^ 2 with hφεdef
    have hφεeq : ∀ z, φε z = φ z + ε * (‖z‖ ^ 2 - M) := by
      intro z; simp only [hφεdef, hφ''def]; ring
    have hφ''b : IsLocallyBoundedPshOn Ω' φ'' :=
      BedfordTaylor.IsLocallyBoundedPshOn.add_const hφ' _
    have hρb := isLocallyBoundedPshOn_mul_normSq Ω' hε
    have hφεb : IsLocallyBoundedPshOn Ω' φε := isLocallyBoundedPshOn_add hφ''b hρb
    obtain ⟨με, hμε⟩ := exists_isBTLimit_of_isLocallyBoundedPshOn (u := fun _ : Fin n => φε)
      fun _ => hφεb
    set S : Set (ComplexModel n) := {z | z ∈ Ω' ∧ ψ z < φε z} with hSdef
    have hSD : S ⊆ D := by
      rintro z ⟨hzΩ', hz⟩
      by_contra hzD
      have hneg : ε * (‖z‖ ^ 2 - M) < 0 :=
        mul_neg_of_pos_of_neg hε (by linarith [hM z hzΩ'])
      have := hoff z (hΩ'Ω hzΩ') hzD
      rw [hφεeq] at hz
      linarith
    have hcomp := measure_lt_le_of_subset_compact hn hψ' hφεb hμ' hμε hDc hDΩ'
      (hSD.trans subset_closure)
    have hS0 : μ.restrict Ω' S = 0 := by
      rw [Measure.restrict_apply' Ω'.isOpen.measurableSet]
      exact measure_mono_null (fun z hz => hSD hz.1) hzero
    have hSε : με S = 0 := le_antisymm (hcomp.trans hS0.le) bot_le
    have hlow := le_of_isBTLimit_add hφ''b hρb hμε (isBTLimit_mul_normSq Ω' hε.le)
    have hvol : volume.restrict (Ω' : Set (ComplexModel n)) S = 0 := by
      have h := hlow S
      rw [hSε, Measure.smul_apply, nonpos_iff_eq_zero, smul_eq_mul, mul_eq_zero] at h
      rcases h with h | h
      · exfalso
        rw [mul_eq_zero] at h
        rcases h with h | h
        · exact (pow_ne_zero n (ENNReal.ofReal_pos.mpr hε).ne') h
        · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne' h
      · exact h
    have hae : (fun z => ((max (φε z) (ψ z) : ℝ) : EReal)) =ᵐ[volume.restrict (Ω' : Set _)]
        fun z => ((ψ z : ℝ) : EReal) := by
      have hnot : ∀ᵐ z ∂volume.restrict (Ω' : Set (ComplexModel n)), z ∉ S :=
        measure_eq_zero_iff_ae_notMem.mp hvol
      filter_upwards [hnot, ae_restrict_mem Ω'.isOpen.measurableSet] with z hz hzΩ
      have : φε z ≤ ψ z := not_lt.mp fun h => hz ⟨hzΩ, h⟩
      rw [max_eq_right this]
    have heq := PlurisubharmonicOn.eqOn_of_ae_eq
      (BedfordTaylor.IsLocallyBoundedPshOn.max hφεb hψ').1 hψ'.1 Ω'.isOpen volume hae
    intro z hz
    have h := heq hz
    simp only [EReal.coe_eq_coe_iff] at h
    rw [← hφεeq]
    exact (max_eq_right_iff.mp h)
  intro z hz
  by_cases hzD : z ∈ D
  · have hzΩ' : z ∈ Ω' := hDΩ' (subset_closure hzD)
    have hMz : 0 < M - ‖z‖ ^ 2 := by linarith [hM z hzΩ']
    refine le_of_forall_pos_le_add fun η hη => ?_
    have h := hε (η / (M - ‖z‖ ^ 2)) (div_pos hη hMz) z hzΩ'
    have hcalc : η / (M - ‖z‖ ^ 2) * (‖z‖ ^ 2 - M) = -η := by
      field_simp
      ring
    rw [hcalc] at h
    linarith
  · exact hoff z hz hzD

/-- **`prop:BT_balayage`, the uniqueness clause.** Let `D` be open with compact closure in `Ω`
and `φ` locally bounded psh on `Ω`. Two locally bounded psh functions `ψ₁, ψ₂` on `Ω` with
`(ddᶜψᵢ)ⁿ = 0` on `D` and `ψᵢ = φ` on `Ω \ D` coincide. (No pseudoconvexity of `D` is needed.) -/
theorem balayage_unique (hn : 0 < n) {Ω : Opens (ComplexModel n)} {D : Set (ComplexModel n)}
    (hDc : IsCompact (closure D)) (hDΩ : closure D ⊆ Ω) {φ ψ₁ ψ₂ : ComplexModel n → ℝ}
    (hψ₁ : IsLocallyBoundedPshOn Ω ψ₁) (hψ₂ : IsLocallyBoundedPshOn Ω ψ₂)
    (he₁ : ∀ z ∈ Ω, z ∉ D → ψ₁ z = φ z) (he₂ : ∀ z ∈ Ω, z ∉ D → ψ₂ z = φ z)
    {μ₁ μ₂ : Measure (ComplexModel n)} (hμ₁ : IsBTLimit Ω (fun _ => ψ₁) μ₁)
    (hμ₂ : IsBTLimit Ω (fun _ => ψ₂) μ₂) (hz₁ : μ₁ D = 0) (hz₂ : μ₂ D = 0) :
    ∀ z ∈ Ω, ψ₁ z = ψ₂ z := by
  intro z hz
  apply le_antisymm
  · exact le_of_le_off_of_measure_eq_zero hn hDc hDΩ hψ₁ hψ₂
      (fun w hw hwD => by rw [he₁ w hw hwD, he₂ w hw hwD]) hμ₂ hz₂ z hz
  · exact le_of_le_off_of_measure_eq_zero hn hDc hDΩ hψ₂ hψ₁
      (fun w hw hwD => by rw [he₁ w hw hwD, he₂ w hw hwD]) hμ₁ hz₁ z hz

/-- **`prop:BT_balayage`, the clause `ψ ≥ φ`.** Every locally bounded psh `ψ` on `Ω` with
`(ddᶜψ)ⁿ = 0` on `D` and `ψ = φ` on `Ω \ D` satisfies `ψ ≥ φ`. -/
theorem le_balayage (hn : 0 < n) {Ω : Opens (ComplexModel n)} {D : Set (ComplexModel n)}
    (hDc : IsCompact (closure D)) (hDΩ : closure D ⊆ Ω) {φ ψ : ComplexModel n → ℝ}
    (hφ : IsLocallyBoundedPshOn Ω φ) (hψ : IsLocallyBoundedPshOn Ω ψ)
    (he : ∀ z ∈ Ω, z ∉ D → ψ z = φ z) {μ : Measure (ComplexModel n)}
    (hμ : IsBTLimit Ω (fun _ => ψ) μ) (hzero : μ D = 0) : ∀ z ∈ Ω, φ z ≤ ψ z :=
  le_of_le_off_of_measure_eq_zero hn hDc hDΩ hφ hψ (fun w hw hwD => (he w hw hwD).ge) hμ hzero

end SGPT.PSH.BookDeepDomination
