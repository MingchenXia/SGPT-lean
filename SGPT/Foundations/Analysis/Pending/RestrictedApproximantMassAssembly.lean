import SGPT.Foundations.Analysis.Pending.RestrictedVolumeModelMass
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison
import SGPT.Foundations.Analysis.Pending.UniformLelongBound
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantMass
import SGPT.Foundations.Analysis.Pending.MultiplierIdealWeightLowerBound
import SGPT.Foundations.Analysis.Pending.TraceUPartRouteF
import SGPT.Foundations.Analysis.Pending.MinimalSingularityLelongVanishing

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Route F, `F-b` assembled: the restricted approximant masses are bounded below by `h`

Plan §8 of `scratch/tn23-envelopes-qea-plan-0117.md`; blueprint `pc:f-restricted-mass`,
`pc:f-ideal-shift`, `pc:f-approximant-bound` (human decision I-0796, D0 = route F).  Let `X` be compact
connected Kähler, `{θ}` big, `V ⊆ X` a closed connected submanifold of dimension `k` with
`h = ⟨{θ}^k⟩_{X|V} > 0`, and `Φ_j` a quasi-equisingular approximation of `V_θ` of global type
`(2^{-j}, 𝓘(2^jV_θ))` with errors `ε_j > 0` and restrictions `φ_j = Φ_j|_V ∈ PSH(V, γ + ε_jω_V)`.  Then

    b_j = ∫_V ⟨(γ + ε_jω_V)_{φ_j}^k⟩ ≥ h   for every j       (`restrictedApproximantMassBound`).

* On `X` (TN-CLASSICAL's probe `scratch/offlib/tncl_ideal_shift_0130.lean`, run 0130, taken in here
  by agreement, I-0813 C-0004/C-0005): `𝓘((q+1)V_{ε_i}) ⊆ 𝓘(qV_θ)` for large `i` (P3 =
  `UniformLelongBound.exists_multiplierIdeal_le_of_convexComb_le` with P2), hence
  `((q+1)/q)·V_{ε_i} ≤ Φ_j + C` (P4b), `q = 2^j` (`eventually_multiplierIdeal_le`,
  `eventually_moreSingularOn`).
* On `V`, per level: `h ≤ h_{ε_i}` (P1, `RestrictedVolumeModelMass`) and `h_{ε_i} ≤ b_j + t K` with
  `t = aε_i + A/q` (P5, `RestrictedApproximantComparison`); letting `i → ∞`, `h ≤ b_j + (A/2^j)K`.
* `b_j` is antitone (`antitone_restrictedApproximantMass`: background and singularity monotonicity),
  so `h ≤ b_j + (A/2^{j'})K` for all `j' ≥ j`, and `h ≤ b_j`.

With the wiring `TraceUPartRouteF.positiveCurrentInput_of_restrictedApproximantMassBound`:
`positiveCurrentInput_of_numericalRestrictedVolume_pos` discharges Copy-4 `sec:positive-current`
under the standing hypotheses of `PositiveCurrentInputInterface.ct22Copy4_positiveCurrentInput`.

This module contains no `sorry`; `restrictedApproximantMassBound` and the lemmas above it are
axiom-clean.  `positiveCurrentInput_of_numericalRestrictedVolume_pos` reaches one named input, the
Boucksom bigness criterion `UniformAmbientVolumeBigness.isBigClass_of_hasUniformAmbientMassLowerBound`
(already a root of the main theorem; used by `lem:domination` in `DominationBigRestriction`).
-/

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.RestrictedApproximantMassAssembly

noncomputable section

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.HolomorphicIdealSheaves
  FirstPass.GlobalAnalyticSingularities FirstPass.QuasiEquisingularApproximation
  FirstPass.BlowupSequences FirstPass.NumericalRestrictedVolume
  SubmanifoldChartedSpace RestrictedApproximantMass ThetaPshConvexCombination DiagonalMass
  RestrictedVolumeModelMass

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-! ### On `X`: the ideal shift and the approximant bound (TN-CLASSICAL's probe, run 0130) -/

section Ambient

variable [MeasurableSpace X] [BorelSpace X]

/-- **`pc:f-ideal-shift`**: `𝓘((q+1)V_{θ+ε_jω}) ⊆ 𝓘(qV_θ)` for all large `j` (P3 with `θ₂ = θ + ω`
and P2 with `a = max 2 t₀⁻¹`).  From TN-CLASSICAL's probe (run 0130). -/
theorem eventually_multiplierIdeal_le (hn : 0 < n) [CompactSpace X] [ConnectedSpace X]
    (omega : KahlerBackground n X) {θ : ClosedRealOneOneForm n X}
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hV : IsThetaPshPotential θ.val (thetaPshSupremum θ.val))
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hanti : Antitone ε) (hlim : Tendsto ε atTop (𝓝 0))
    (hVj : ∀ j, IsThetaPshPotential (θ + ε j • omega.form).val
      (thetaPshSupremum (θ + ε j • omega.form).val)) {q : ℝ} (hq : 0 < q) :
    ∀ᶠ j in atTop, (multiplierIdeal (n := n) (q + 1)
      (thetaPshSupremum (θ + ε j • omega.form).val)).Le
        (multiplierIdeal (n := n) q (thetaPshSupremum θ.val)) := by
  obtain ⟨t₀, ht₀, hP3⟩ :=
    UniformLelongBound.exists_multiplierIdeal_le_of_convexComb_le hn omega (θ + omega.form) hq
  set a : ℝ := max 2 t₀⁻¹ with hadef
  have ha : 1 < a := lt_of_lt_of_le one_lt_two (le_max_left _ _)
  have hainv : a⁻¹ ≤ t₀ := by
    have := inv_anti₀ (inv_pos.mpr ht₀) (le_max_right 2 t₀⁻¹)
    rwa [inv_inv] at this
  have h2 := eventually_exists_convexComb_le_thetaPshSupremum hn omega hbig hV hε hanti hlim hVj ha
  have h1 : ∀ᶠ j in atTop, ε j ≤ 1 := hlim.eventually (ge_mem_nhds one_pos)
  filter_upwards [h1, h2] with j hj1 hj
  obtain ⟨w, hw, hconv⟩ := hj
  have hw' : IsThetaPshPotential (θ + omega.form).val w := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hw
      (KahlerDomination.isSemipositive_smul omega.isSemipositive (sub_nonneg.mpr hj1))
    have heq : θ + ε j • omega.form + (1 - ε j) • omega.form = θ + omega.form := by
      rw [add_assoc, ← add_smul, add_sub_cancel, one_smul]
    rwa [heq] at h
  refine hP3 a⁻¹ (inv_pos.mpr (lt_trans one_pos ha)) hainv (hVj j).1.quasiPlurisubharmonic hw'
    hV.1.quasiPlurisubharmonic fun x => ?_
  have := hconv x
  rw [convexComb_apply] at this
  rwa [add_comm]

/-- **`pc:f-approximant-bound` on `X`**: for `Φ` of type `(2^{-j}, 𝓘(2^jV_θ))`,
`((2^j+1)/2^j)·V_{θ+ε_iω} ≤ Φ + C` for all large `i` (the ideal shift and P4b).  From TN-CLASSICAL's
probe (run 0130). -/
theorem eventually_moreSingularOn (hn : 0 < n) [CompactSpace X] [ConnectedSpace X]
    (omega : KahlerBackground n X) {θ : ClosedRealOneOneForm n X}
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hV : IsThetaPshPotential θ.val (thetaPshSupremum θ.val))
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hanti : Antitone ε) (hlim : Tendsto ε atTop (𝓝 0))
    (hVj : ∀ j, IsThetaPshPotential (θ + ε j • omega.form).val
      (thetaPshSupremum (θ + ε j • omega.form).val)) (j : ℕ) {Φ : X → EReal}
    (hΦ : HasAnalyticSingularitiesOfType (n := n) Φ (((2 ^ j : ℕ) : ℚ)⁻¹)
      (multiplierIdeal (n := n) ((2 ^ j : ℕ) : ℝ) (thetaPshSupremum θ.val))) :
    ∀ᶠ i in atTop, MoreSingularOn (fun x => (((((2 ^ j + 1 : ℕ) : ℝ) / (2 ^ j : ℕ) : ℝ)) : EReal) *
      thetaPshSupremum (θ + ε i • omega.form).val x) Φ univ := by
  have hq : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  filter_upwards [eventually_multiplierIdeal_le hn omega hbig hV hε hanti hlim hVj hq] with i hi
  refine MultiplierIdealWeightLowerBound.moreSingularOn_smul_of_multiplierIdeal_le hn (hVj i)
    (pow_pos two_pos j) hΦ ?_
  have hcast : (((2 ^ j + 1 : ℕ) : ℝ)) = ((2 ^ j : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  exact hi

end Ambient

/-! ### The assembly -/

/-- **`b_j` is antitone**: `b_{j'} ≤ ∫(γ + ε_jω_V)_{φ_{j'}}^k ≤ b_j` for `j ≤ j'` (background, then
singularity monotonicity, `φ_{j'} ≤ φ_j`). -/
theorem antitone_restrictedApproximantMass {k : ℕ} {Z : Type*} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel k) Z] [IsComplexManifold k Z] [MeasurableSpace Z] [BorelSpace Z]
    [CompactSpace Z] (omegaZ : KahlerBackground k Z) (γ : ClosedRealOneOneForm k Z)
    {ε : ℕ → ℝ} (hanti : Antitone ε) {φ : ℕ → Z → EReal} (hφanti : ∀ x, Antitone fun j => φ j x)
    (hφ : ∀ j, IsThetaPshPotential (γ + ε j • omegaZ.form).val (φ j)) :
    Antitone fun j => diagonalPotentialMass (γ + ε j • omegaZ.form) (φ j) (hφ j) := by
  intro j j' hjj'
  have hle : ε j' ≤ ε j := hanti hjj'
  have hφ' : IsThetaPshPotential (γ + ε j • omegaZ.form).val (φ j') := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive (hφ j')
      (KahlerDomination.isSemipositive_smul omegaZ.isSemipositive (sub_nonneg.mpr hle))
    rwa [show γ + ε j' • omegaZ.form + (ε j - ε j') • omegaZ.form = γ + ε j • omegaZ.form by
      module] at h
  calc diagonalPotentialMass (γ + ε j' • omegaZ.form) (φ j') (hφ j')
      ≤ diagonalPotentialMass (γ + ε j • omegaZ.form) (φ j') hφ' :=
        TraceFreeLimit.diagonalPotentialMeasure_le_of_le omegaZ hle (hφ j') hφ' univ
    _ ≤ diagonalPotentialMass (γ + ε j • omegaZ.form) (φ j) (hφ j) :=
        diagonalPotentialMass_mono_of_kahler omegaZ hφ' (hφ j)
          ⟨0, fun x _ => by rw [EReal.coe_zero, add_zero]; exact hφanti x hjj'⟩

/-- **Route F, `F-b`: `b_j ≥ h` for every `j`**, hence `RestrictedApproximantMassBound` (with the
constant `h = ⟨{θ}^k⟩_{X|V} > 0`). -/
theorem restrictedApproximantMassBound (hn : 0 < n) [CompactSpace X] [ConnectedSpace X]
    (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim)
    (hvol : 0 < numericalRestrictedVolume omega (RealBottChern.ofRepresentative θ) V) :
    TraceUPartRouteF.RestrictedApproximantMassBound omega θ V hV := by
  set hk := le_of_isClosedConnectedSubmanifold hV
  let := chartedSpace hk hV.2.2
  have := isComplexManifold_chartedSpace hk hV.2.2
  let : MeasurableSpace V.carrier := borel _
  have : BorelSpace V.carrier := ⟨rfl⟩
  have : CompactSpace V.carrier := SubmanifoldMassCalculus.compactSpace_of_isClosed hV.1
  have : Nonempty V.carrier := hV.2.1.nonempty.to_subtype
  have : Nonempty X := ⟨(Classical.choice (inferInstance : Nonempty V.carrier)).1⟩
  let : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  intro ε Φ hqea hεpos htype hφ
  set ωV := SubmanifoldKahlerRestriction.kahlerBackground hk hV.2.2 omega with hωV
  set γ := ClosedRealOneOneForm.pullback (contMDiff_val hk hV.2.2) θ with hγ
  set h := numericalRestrictedVolume omega (RealBottChern.ofRepresentative θ) V with hhdef
  have hanti := hqea.error_antitone
  have hlim := hqea.error_tendsto
  -- `V_θ` and the `V_{θ+ε_iω}` are potentials on `X`
  have hVθ : IsThetaPshPotential θ.val (thetaPshSupremum θ.val) :=
    MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum θ hbig
  have hVj : ∀ i, IsThetaPshPotential (θ + ε i • omega.form).val
      (thetaPshSupremum (θ + ε i • omega.form).val) := fun i =>
    thetaPshSupremum_isThetaPshPotential _ (θ + ε i • omega.form).2.1 (θ + ε i • omega.form).2.2
      (isThetaPshPotential_thetaPshSupremum_add omega hVθ (hεpos i).le).1.hasSmoothLocalPotentials
      ⟨_, isThetaPshPotential_thetaPshSupremum_add omega hVθ (hεpos i).le⟩
  -- the model potentials on `V` and P1
  have hmodel : ∀ i, IsThetaPshPotential (γ + ε i • ωV.form).val
      (restrictedModel θ omega.form (ε i) (W := V.carrier)) := fun i =>
    isThetaPshPotential_restrictedModel omega θ V hV
      (ε := ⟨ε i, hεpos i⟩)
      (Classical.choice (nonempty_presentation_of_pos omega θ V hvol ⟨ε i, hεpos i⟩))
  have hP1 : ∀ i, h ≤ diagonalPotentialMass (γ + ε i • ωV.form)
      (restrictedModel θ omega.form (ε i) (W := V.carrier)) (hmodel i) := fun i =>
    numericalRestrictedVolume_le_restrictedModelMass omega θ V hV (hεpos i) (hmodel i)
  -- P5 on `V`
  obtain ⟨A, hA, K, hK, hP5⟩ :=
    RestrictedApproximantComparison.exists_diagonalPotentialMass_le_of_smul_moreSingular ωV γ
  -- the restricted approximant masses
  set b : ℕ → ℝ≥0∞ := fun j => diagonalPotentialMass (γ + ε j • ωV.form)
    (fun x : V.carrier => Φ j x.1) (hφ j) with hbdef
  have hb : Antitone b := antitone_restrictedApproximantMass ωV γ hanti
    (fun x => hqea.decreasesPointwise.1 x.1) hφ
  -- one level
  have hlevel : ∀ j', ε j' ≤ 1 → A / 2 ^ j' < 1 →
      h ≤ b j' + ENNReal.ofReal (A / 2 ^ j') * K := by
    intro j' hε1 hA1
    set a : ℝ := ((2 ^ j' + 1 : ℕ) : ℝ) / ((2 ^ j' : ℕ) : ℝ) with hadef
    have hq : (0 : ℝ) < ((2 ^ j' : ℕ) : ℝ) := by positivity
    have ha_eq : a = 1 + 1 / 2 ^ j' := by
      rw [hadef]; push_cast; field_simp
    have ha1 : 1 ≤ a := by
      rw [ha_eq]
      have : (0 : ℝ) ≤ 1 / 2 ^ j' := by positivity
      linarith
    have hasub : (a - 1) * A = A / 2 ^ j' := by rw [ha_eq]; ring
    have hev := eventually_moreSingularOn hn omega hbig hVθ hεpos hanti hlim hVj j' (htype j')
    have hev2 : ∀ᶠ i in atTop, a * ε i + (a - 1) * A ≤ 1 := by
      have hT : Tendsto (fun i => a * ε i + (a - 1) * A) atTop (𝓝 (a * 0 + (a - 1) * A)) :=
        (hlim.const_mul a).add_const _
      rw [mul_zero, zero_add, hasub] at hT
      exact (hT.eventually (ge_mem_nhds hA1)).mono fun i hi => by rwa [hasub]
    have hbound : ∀ᶠ i in atTop, h ≤ b j' + ENNReal.ofReal (a * ε i + (a - 1) * A) * K := by
      filter_upwards [hev, hev2] with i hi hi2
      have hmore : MoreSingularOn
          (fun x : V.carrier => (a : EReal) * restrictedModel θ omega.form (ε i) (W := V.carrier) x)
          (fun x : V.carrier => Φ j' x.1) univ := by
        obtain ⟨C, hC⟩ := hi
        exact ⟨C, fun x _ => hC x.1 (mem_univ _)⟩
      exact (hP1 i).trans (hP5 a (ε i) (ε j') ha1 (hεpos i) (hεpos j') hε1 hi2 (hmodel i) (hφ j')
        hmore)
    have hT : Tendsto (fun i => b j' + ENNReal.ofReal (a * ε i + (a - 1) * A) * K) atTop
        (𝓝 (b j' + ENNReal.ofReal (a * 0 + (a - 1) * A) * K)) := by
      refine tendsto_const_nhds.add (ENNReal.Tendsto.mul_const ?_ (Or.inr hK.ne))
      exact ENNReal.tendsto_ofReal ((hlim.const_mul a).add_const _)
    have := ge_of_tendsto hT hbound
    rwa [mul_zero, zero_add, hasub] at this
  -- closing
  refine ⟨h, hvol, fun j => ?_⟩
  have hε1 : ∀ᶠ j' in atTop, ε j' ≤ 1 := hlim.eventually (ge_mem_nhds one_pos)
  have hpow : Tendsto (fun j' : ℕ => A / 2 ^ j') atTop (𝓝 0) := by
    have h2 : Tendsto (fun j' : ℕ => ((1 : ℝ) / 2) ^ j') atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have := h2.const_mul A
    rw [mul_zero] at this
    refine this.congr fun j' => ?_
    rw [one_div, inv_pow, div_eq_mul_inv]
  have hA1 : ∀ᶠ j' in atTop, A / 2 ^ j' < 1 := hpow.eventually (gt_mem_nhds one_pos)
  have hev3 : ∀ᶠ j' in atTop, h ≤ b j + ENNReal.ofReal (A / 2 ^ j') * K := by
    filter_upwards [eventually_ge_atTop j, hε1, hA1] with j' hjj' h1 h2
    exact (hlevel j' h1 h2).trans (by gcongr; exact hb hjj')
  have hT3 : Tendsto (fun j' : ℕ => b j + ENNReal.ofReal (A / 2 ^ j') * K) atTop
      (𝓝 (b j + ENNReal.ofReal 0 * K)) :=
    tendsto_const_nhds.add (ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hpow)
      (Or.inr hK.ne))
  have := ge_of_tendsto hT3 hev3
  rwa [ENNReal.ofReal_zero, zero_mul, add_zero] at this

/-- **Copy-4 `sec:positive-current` along route F**: under the standing hypotheses of
`PositiveCurrentInputInterface.ct22Copy4_positiveCurrentInput` (`{θ}` big, `0 < dim V < n`,
`V ⊄ E_nn(α)`, `⟨α^{dim V}⟩_{X|V} > 0`), `PositiveCurrentInput` holds. -/
theorem positiveCurrentInput_of_numericalRestrictedVolume_pos [CompactSpace X] [ConnectedSpace X]
    (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) (hdim_pos : 0 < V.dim)
    (hdim_lt : V.dim < n)
    (hnonNef : ¬ V.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ))
    (hvol : 0 < numericalRestrictedVolume omega (RealBottChern.ofRepresentative θ) V) :
    Copy4TraceInputReduction.PositiveCurrentInput omega θ V hV :=
  TraceUPartRouteF.positiveCurrentInput_of_restrictedApproximantMassBound omega θ hbig V hV hdim_pos
    hdim_lt hnonNef
    (restrictedApproximantMassBound (hdim_pos.trans hdim_lt) omega θ hbig V hV hvol)

end

end SGPT.Foundations.Analysis.Pending.RestrictedApproximantMassAssembly
