import SGPT.Foundations.Analysis.Pending.TraceUPartRouteF
import SGPT.Foundations.Analysis.Pending.KahlerVolumePositive

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Route F, `F-b`: the masses of the restricted approximants are bounded below

Plan `scratch/tn23-envelopes-qea-plan-0117.md` §5.2 (F1 → T1) and §8; human decision I-0796 (D0 = route F).
Target: `TraceUPartRouteF.RestrictedApproximantMassBound`.  This module collects its steps.

## P2 (ambient side): DDNL Lemma 4.3 with a vanishing weight

On a compact connected Kähler manifold `X` with `{θ}` big:

* `diagonalPotentialMass_pos_of_sub_smul`: a potential of `θ - δω`, `δ > 0`, has positive mass in
  `θ` (slot by slot, `(θ, u₀) = (θ - δω, u₀) + δ(ω, 0)`, down to `δ^n ∫ω^n > 0`); hence
  `vol(θ) = ∫θ_{V_θ}^n > 0` (`diagonalPotentialMass_thetaPshSupremum_pos_of_isBigClass`).
* `tendsto_volume_add_smul`: `vol(θ + ε_jω) → vol(θ)` for `ε_j ↓ 0` — DX24 Prop. 2.1
  (`TraceFreeLimit.tendsto_diagonalPotentialMass_traceFreeLimit`) for the model potentials
  `V_{θ+ε_jω}`, whose decreasing limit is `V_θ`.
* `eventually_exists_convexComb_le_thetaPshSupremum`: for every weight `a > 1`, eventually in `j`
  there is `w ∈ PSH(X, θ + ε_jω)` with `a⁻¹w + (1 - a⁻¹)V_{θ+ε_jω} ≤ V_θ` (DDNL Lemma 4.3 = Xia SGPT
  Lemma 2.4.4, big-class form, the weight `a` being admissible for large `j` because
  `∫(θ + ε_jω)_{V_θ}^n` and `vol(θ + ε_jω)` both tend to `vol(θ) > 0`).
-/

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.RestrictedApproximantMass

noncomputable section

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus DiagonalMass
  GlobalNonPluripolar GlobalSlotLinear GlobalDiagonalScaling AmbientMassBackgroundMonotone
  ThetaPshConvexCombination ConvexCombEnvelopeMass

/-! ### Positive volume of a big class -/

section Volume

variable {k : ℕ} {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [ChartedSpace (ComplexModel k) Z] [IsComplexManifold k Z] [CompactSpace Z]

/-- **A potential of `θ - δω` has positive mass in `θ`**: slot by slot,
`(θ, u₀) = 1·(θ - δω, u₀) + δ·(ω, 0)` (slot linearity), so `∫θ_{u₀}^k ≥ δ^k ∫ω^k > 0`. -/
theorem diagonalPotentialMass_pos_of_sub_smul [Nonempty Z] (omega : KahlerBackground k Z)
    {θ : ClosedRealOneOneForm k Z} {δ : ℝ} (hδ : 0 < δ) {u₀ : Z → EReal}
    (hu₀ : IsThetaPshPotential (θ - δ • omega.form).val u₀)
    (hu : IsThetaPshPotential θ.val u₀) : 0 < diagonalPotentialMass θ u₀ hu := by
  classical
  have h0ω : IsThetaPshPotential omega.form.val (fun _ : Z => (0 : EReal)) :=
    ⟨(LocalPotentials.thetaPlurisubharmonic_zero_iff _).mpr omega.isSemipositive,
      fun x _ _ hx => ⟨x, hx, EReal.zero_ne_bot⟩⟩
  set T : Finset (Fin k) → Fin k → ClosedRealOneOneForm k Z :=
    fun s i => if i ∈ s then omega.form else θ with hT
  set x : Finset (Fin k) → Fin k → Z → EReal :=
    fun s i => if i ∈ s then (fun _ => (0 : EReal)) else u₀ with hx
  have hpot : ∀ s i, IsThetaPshPotential (T s i).val (x s i) := by
    intro s i
    by_cases hi : i ∈ s
    · simpa [hT, hx, hi] using h0ω
    · simpa [hT, hx, hi] using hu
  have key : ∀ s : Finset (Fin k),
      ENNReal.ofReal (δ ^ s.card) * globalMixedMeasure (T s) (x s) (fun i => (hpot s i).1) univ ≤
        globalMixedMeasure (T ∅) (x ∅) (fun i => (hpot ∅ i).1) univ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i₀ s hi₀ ih =>
        have hθi₀ : T s i₀ = (1 : ℝ) • (θ - δ • omega.form) + δ • omega.form := by
          simp only [hT, hi₀, if_false]
          module
        have hTα : Function.update (T s) i₀ (θ - δ • omega.form) = Function.update (T s) i₀
            (θ - δ • omega.form) := rfl
        have hTβ : Function.update (T s) i₀ omega.form = T (insert i₀ s) := by
          funext j
          by_cases hj : j = i₀
          · subst hj; simp [hT]
          · simp [hT, Finset.mem_insert, hj]
        have hxβ : Function.update (x s) i₀ (fun _ => (0 : EReal)) = x (insert i₀ s) := by
          funext j
          by_cases hj : j = i₀
          · subst hj; simp [hx]
          · simp [hx, Finset.mem_insert, hj]
        have hcomb : Function.update (x s) i₀
            (fun p => ((1 : ℝ) : EReal) * u₀ p + ((δ : ℝ) : EReal) * (0 : EReal)) = x s := by
          funext j
          by_cases hj : j = i₀
          · subst hj; funext p; simp [hx, hi₀]
          · simp [Function.update_of_ne hj]
        have hc : ∀ i, ThetaPlurisubharmonic (T s i).val (Function.update (x s) i₀
            (fun p => ((1 : ℝ) : EReal) * u₀ p + ((δ : ℝ) : EReal) * (0 : EReal)) i) := by
          rw [hcomb]; exact fun i => (hpot s i).1
        have hapot : ∀ i, IsThetaPshPotential
            (Function.update (T s) i₀ (θ - δ • omega.form) i).val
            (Function.update (x s) i₀ u₀ i) := by
          intro i
          by_cases hi : i = i₀
          · subst hi; simpa using hu₀
          · simpa [Function.update_of_ne hi] using hpot s i
        have hb : ∀ i, ThetaPlurisubharmonic (Function.update (T s) i₀ omega.form i).val
            (Function.update (x s) i₀ (fun _ => (0 : EReal)) i) := by
          rw [hTβ, hxβ]; exact fun i => (hpot (insert i₀ s) i).1
        have hkey := globalMixedMeasure_update_add_smul (θ := T s) i₀ (α := θ - δ • omega.form)
          (β := omega.form) (s := 1) (r := δ) one_pos hδ hθi₀ (x := x s) (a := u₀)
          (b := fun _ => (0 : EReal)) hc (fun i => (hapot i).1) hb
          (globalMixedMeasure_pole_null_of_nondegenerate hb hu₀) (by simp)
        have hlow : ENNReal.ofReal δ * globalMixedMeasure (T (insert i₀ s)) (x (insert i₀ s))
            (fun i => (hpot (insert i₀ s) i).1) univ ≤
            globalMixedMeasure (T s) (x s) (fun i => (hpot s i).1) univ := by
          have h1 := congrArg (fun μ : Measure Z => μ univ) hkey
          simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul] at h1
          rw [globalMixedMeasure_congr_tuples rfl hcomb.symm _ hc, h1,
            globalMixedMeasure_congr_tuples hTβ.symm hxβ.symm (fun i => (hpot (insert i₀ s) i).1)
              hb]
          exact le_add_self
        calc ENNReal.ofReal (δ ^ (insert i₀ s).card) * globalMixedMeasure (T (insert i₀ s))
              (x (insert i₀ s)) (fun i => (hpot (insert i₀ s) i).1) univ
            = ENNReal.ofReal (δ ^ s.card) * (ENNReal.ofReal δ * globalMixedMeasure
                (T (insert i₀ s)) (x (insert i₀ s)) (fun i => (hpot (insert i₀ s) i).1) univ) := by
              rw [Finset.card_insert_of_notMem hi₀, pow_succ, ENNReal.ofReal_mul (by positivity),
                mul_assoc]
          _ ≤ ENNReal.ofReal (δ ^ s.card) *
                globalMixedMeasure (T s) (x s) (fun i => (hpot s i).1) univ := by gcongr
          _ ≤ _ := ih
  have huniv := key Finset.univ
  have hTu : T Finset.univ = fun _ => omega.form := by funext j; simp [hT]
  have hxu : x Finset.univ = fun _ => (fun _ => (0 : EReal)) := by funext j; simp [hx]
  have hT0 : T ∅ = fun _ => θ := by funext j; simp [hT]
  have hx0 : x ∅ = fun _ => u₀ := by funext j; simp [hx]
  rw [globalMixedMeasure_congr_tuples hTu hxu _ (fun _ => (PluripolarCapacityDichotomy.isThetaPshPotential_zero omega).1),
    globalMixedMeasure_congr_tuples hT0 hx0 _ (fun _ => hu.1)] at huniv
  have hvol := KahlerVolumePositive.diagonalPotentialMass_zero_pos omega
  refine lt_of_lt_of_le ?_ huniv
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (by positivity)).ne' hvol.ne'

/-- **A big class has positive volume**: `∫θ_{V_θ}^k > 0` (a Kähler current `θ + ddᶜu₀ ≥ δ₀ω` and
`u₀ - sup u₀ ≤ V_θ`). -/
theorem diagonalPotentialMass_thetaPshSupremum_pos_of_isBigClass [Nonempty Z]
    (omega : KahlerBackground k Z) (θ : ClosedRealOneOneForm k Z)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hV : IsThetaPshPotential θ.val (thetaPshSupremum θ.val)) :
    0 < diagonalPotentialMass θ (thetaPshSupremum θ.val) hV := by
  obtain ⟨δ₀, hδ₀, u₀, hu₀⟩ :=
    DivisorialDomination.exists_isThetaPshPotential_sub_smul_of_isBigClass omega θ hbig
  have hu : IsThetaPshPotential θ.val u₀ := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hu₀
      (KahlerDomination.isSemipositive_smul omega.isSemipositive hδ₀.le)
    rwa [sub_add_cancel] at h
  obtain ⟨C, hC⟩ := hu.exists_global_upper_bound
  have hle : (fun x => u₀ x - (C : EReal)) ≤ thetaPshSupremum θ.val :=
    le_thetaPshSupremum (hu.sub_const C) (sub_const_nonpositive_of_le hC)
  refine lt_of_lt_of_le (diagonalPotentialMass_pos_of_sub_smul omega hδ₀ hu₀ hu) ?_
  refine diagonalPotentialMass_mono_of_kahler omega hu hV ⟨C, fun x _ => ?_⟩
  have h := hle x
  simp only at h
  calc u₀ x = u₀ x - (C : EReal) + (C : EReal) := by
        rw [sub_eq_add_neg, add_assoc, ← EReal.coe_neg, ← EReal.coe_add, neg_add_cancel,
          EReal.coe_zero, add_zero]
    _ ≤ thetaPshSupremum θ.val x + (C : EReal) := add_le_add h le_rfl

end Volume

/-! ### P2: volume continuity and DDNL Lemma 4.3 with a vanishing weight -/

section Ambient

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X] [Nonempty X]

open TraceFreeLimit

/-- `V_θ ≤ V_{θ+η}` for a semipositive `η`. -/
theorem thetaPshSupremum_le_add {θ η : ClosedRealOneOneForm n X} (hη : η.val.IsSemipositive) :
    thetaPshSupremum θ.val ≤ thetaPshSupremum (θ + η).val :=
  sSup_le_sSup fun _ hw => ⟨LocalPotentials.isThetaPshPotential_add_of_semipositive hw.1 hη, hw.2⟩

/-- `V_θ` is a potential of `θ + εω` for `ε ≥ 0`. -/
theorem isThetaPshPotential_thetaPshSupremum_add (omega : KahlerBackground n X)
    {θ : ClosedRealOneOneForm n X} (hV : IsThetaPshPotential θ.val (thetaPshSupremum θ.val))
    {ε : ℝ} (hε : 0 ≤ ε) : IsThetaPshPotential (θ + ε • omega.form).val (thetaPshSupremum θ.val) :=
  LocalPotentials.isThetaPshPotential_add_of_semipositive hV
    (KahlerDomination.isSemipositive_smul omega.isSemipositive hε)

/-- **`vol(θ + ε_jω) → vol(θ)`** for `ε_j ↓ 0`, `ε_j > 0`: DX24 Prop. 2.1 for the model potentials
`V_{θ+ε_jω}` (`P_{θ+ε_jω}[V_{θ+ε_jω}] ≥ V_θ`), whose trace-free limit is `V_θ`. -/
theorem tendsto_volume_add_smul (hn : 0 < n) [ConnectedSpace X] (omega : KahlerBackground n X)
    {θ : ClosedRealOneOneForm n X} (hV : IsThetaPshPotential θ.val (thetaPshSupremum θ.val))
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hanti : Antitone ε) (hlim : Tendsto ε atTop (𝓝 0))
    (hVj : ∀ j, IsThetaPshPotential (θ + ε j • omega.form).val
      (thetaPshSupremum (θ + ε j • omega.form).val)) :
    Tendsto (fun j => diagonalPotentialMass (θ + ε j • omega.form)
      (thetaPshSupremum (θ + ε j • omega.form).val) (hVj j)) atTop
      (𝓝 (diagonalPotentialMass θ (thetaPshSupremum θ.val) hV)) := by
  have hφanti : ∀ x, Antitone fun j => thetaPshSupremum (θ + ε j • omega.form).val x := by
    intro x i j hij
    have h := thetaPshSupremum_le_add (θ := θ + ε j • omega.form) (η := (ε i - ε j) • omega.form)
      (KahlerDomination.isSemipositive_smul omega.isSemipositive (sub_nonneg.2 (hanti hij))) x
    rwa [show θ + ε j • omega.form + (ε i - ε j) • omega.form = θ + ε i • omega.form by
      module] at h
  have hT := tendsto_diagonalPotentialMass_traceFreeLimit hn omega hε hanti hlim hVj hφanti
  -- the trace-free limit of the `V_{θ+ε_jω}` is `V_θ`
  have hu := isThetaPshPotential_traceFreeLimit omega hanti hlim hVj hφanti
  have heq : traceFreeLimit θ omega.form ε (fun j => thetaPshSupremum (θ + ε j • omega.form).val) =
      thetaPshSupremum θ.val := by
    refine le_antisymm ?_ ?_
    · refine le_thetaPshSupremum hu fun x => ?_
      exact (traceFreeLimit_le θ omega.form ε _ 0 x).trans (singularityEnvelope_le_zero _ _ x)
    · intro x
      refine le_iInf fun j => ?_
      refine le_singularityEnvelope (isThetaPshPotential_thetaPshSupremum_add omega hV (hε j).le)
        (thetaPshSupremum_le_zero θ.val) (MoreSingularOn.of_le fun y _ => ?_) x
      have h := thetaPshSupremum_le_add (θ := θ) (η := ε j • omega.form)
        (KahlerDomination.isSemipositive_smul omega.isSemipositive (hε j).le) y
      exact h
  have hmass : ∀ (f : X → EReal) (hf : IsThetaPshPotential θ.val f), f = thetaPshSupremum θ.val →
      diagonalPotentialMass θ f hf = diagonalPotentialMass θ (thetaPshSupremum θ.val) hV := by
    rintro f hf rfl
    rfl
  rwa [hmass _ _ heq] at hT

/-- **P2: DDNL Lemma 4.3 with a vanishing perturbation.**  For `{θ}` big, `ε_j ↓ 0` (`ε_j > 0`)
and any weight `a > 1`, for all large `j` there is `w ∈ PSH(X, θ + ε_jω)` with
`a⁻¹w + (1 - a⁻¹)V_{θ+ε_jω} ≤ V_θ`. -/
theorem eventually_exists_convexComb_le_thetaPshSupremum (hn : 0 < n) [ConnectedSpace X]
    (omega : KahlerBackground n X) {θ : ClosedRealOneOneForm n X}
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hV : IsThetaPshPotential θ.val (thetaPshSupremum θ.val))
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hanti : Antitone ε) (hlim : Tendsto ε atTop (𝓝 0))
    (hVj : ∀ j, IsThetaPshPotential (θ + ε j • omega.form).val
      (thetaPshSupremum (θ + ε j • omega.form).val)) {a : ℝ} (ha : 1 < a) :
    ∀ᶠ j in atTop, ∃ w : X → EReal, IsThetaPshPotential (θ + ε j • omega.form).val w ∧
      convexComb a⁻¹ w (thetaPshSupremum (θ + ε j • omega.form).val) ≤ thetaPshSupremum θ.val := by
  set L := diagonalPotentialMass θ (thetaPshSupremum θ.val) hV with hLdef
  have hL : 0 < L := diagonalPotentialMass_thetaPshSupremum_pos_of_isBigClass omega θ hbig hV
  have hLtop : L ≠ ⊤ := (DiagonalMeasureRegularity.diagonalPotentialMeasure_lt_top omega θ hV univ).ne
  have hVθj := fun j => isThetaPshPotential_thetaPshSupremum_add omega hV (hε j).le
  have hlow : ∀ j, L ≤ diagonalPotentialMass (θ + ε j • omega.form) (thetaPshSupremum θ.val)
      (hVθj j) := fun j =>
    diagonalPotentialMass_le_add_smul omega.isSemipositive (hε j) hV (hVθj j)
  have hvol := tendsto_volume_add_smul hn omega hV hε hanti hlim hVj
  filter_upwards [PositiveCurrentRooftop.eventually_isAdmissibleWeight (n := n) hL hLtop hlow hvol
    ha] with j hadm
  have hbigj : IsBigClass (RealBottChern.ofRepresentative (θ + ε j • omega.form)) :=
    PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential omega θ hV (hε j)
  have hle : thetaPshSupremum θ.val ≤ thetaPshSupremum (θ + ε j • omega.form).val :=
    thetaPshSupremum_le_add (KahlerDomination.isSemipositive_smul omega.isSemipositive (hε j).le)
  exact PositiveCurrentRooftop.exists_thetaPsh_convexCombBarrier_of_isBigClass omega
    (θ + ε j • omega.form) hbigj (hVθj j) (hVj j) hle ((hL.trans_le (hlow j))) hadm

end Ambient

end

end SGPT.Foundations.Analysis.Pending.RestrictedApproximantMass
