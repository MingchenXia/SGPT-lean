import SGPT.Foundations.Analysis.Pending.MixedMass
import SGPT.Foundations.Analysis.Pending.AmbientMassBackgroundMonotone
import SGPT.Foundations.Analysis.Pending.NefMixedMass
import SGPT.Foundations.Analysis.Pending.MixedMassClassInvariance
import SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Bounded potentials in nef classes: the mixed non-pluripolar mass is the slot integral

Source: Copy-4, `lem:domination`, Step 2 (`pc:domination-intersection` (1)); Boucksom, proof of
Theorem 4.8 (`bou02-volume:4.8`, the masses of the residual nef part after the resolution); the
mixed version of "the non-pluripolar mass of a bounded potential is the cohomological top power".

Let `M` be a compact complex manifold of dimension `N > 0` with a Kähler form `ω`, `θ₀, …, θ_{N-1}`
smooth closed real `(1,1)`-forms, each NEF with respect to `ω`, and `uᵢ` bounded `θᵢ`-psh
potentials.  Then (`globalMixedMass_toReal_eq_slotIntegral`)
`∫_M ⟨(θ₀ + ddᶜu₀) ∧ ⋯ ∧ (θ_{N-1} + ddᶜu_{N-1})⟩ = ∫_M θ₀ ∧ ⋯ ∧ θ_{N-1}`.

## Proof

For `ε > 0` nefness gives smooth `fᵢ` with `θᵢ + εω + ddᶜfᵢ ≥ 0`.  In the classes `θᵢ + εω` the
potentials `uᵢ` and `fᵢ` are both bounded, so the masses agree (`MixedMass.globalMixedMass_eq_of_sameSingularityType`);
the smooth representatives give the slot integral (change of representative, class invariance).
Letting `ε → 0`:
* the measure does not decrease when the backgrounds grow (`AmbientMassBackgroundMonotone`, here for
  any set of slots: `globalMixedMeasure_le_of_add_smul_on`), so the mass is `≤` the slot integral;
* one-slot linearity (`GlobalSlotLinear`) gives the exact increment
  `μ(θ + εω in slot j) = μ(θ) + ε μ(ω in slot j, potential 0)` (`globalMixedMeasure_update_add_smul_eq`),
  hence `μ(θ + εω) ≤ μ(θ) + ε K` for `ε ≤ 1` (`exists_globalMixedMass_add_smul_le`), so the mass is
  `≥` the slot integral.

Sorry-free.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.NefBoundedMixedMass

noncomputable section

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar MixedMass NefMixedMass
  IntegrationCurrent ManifoldTubePositivity BoundedGlobalProduct AmbientMassBackgroundMonotone

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M]

/-- A nonnegative multiple of a semipositive form is semipositive. -/
theorem isSemipositive_smul {γ : ClosedRealOneOneForm N M} (hγ : γ.val.IsSemipositive) {c : ℝ}
    (hc : 0 ≤ c) : (c • γ).val.IsSemipositive := fun e z hz v => by
  have h := hγ e z hz v
  simp only [ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  exact mul_nonneg hc h

/-- Adding a semipositive form keeps a potential plurisubharmonic. -/
theorem thetaPlurisubharmonic_add_of_isSemipositive {θ γ : ClosedRealOneOneForm N M}
    {u : M → EReal} (hu : ThetaPlurisubharmonic θ.val u) (hγ : γ.val.IsSemipositive) :
    ThetaPlurisubharmonic (θ + γ).val u := by
  have h := SGPT.Foundations.Analysis.FirstPass.LocalPotentials.thetaPlurisubharmonic_add hu
    ((Pending.LocalPotentials.thetaPlurisubharmonic_zero_iff γ).mpr hγ)
  simpa only [add_zero] using h

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-! ### One slot, exactly -/

/-- **One-slot increment.**  Enlarging the background of slot `j` by `c • γ` (`c > 0`, `γ`
semipositive) adds exactly `c` times the measure with `γ` and the potential `0` in slot `j`. -/
theorem globalMixedMeasure_update_add_smul_eq {θ : Fin N → ClosedRealOneOneForm N M}
    {u : Fin N → M → EReal} (j : Fin N) {γ : ClosedRealOneOneForm N M} {c : ℝ} (hc : 0 < c)
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i))
    (hnd : IsThetaPshPotential (θ j).val (u j))
    (hu' : ∀ i, ThetaPlurisubharmonic (Function.update θ j (θ j + c • γ) i).val (u i))
    (h0 : ∀ i, ThetaPlurisubharmonic (Function.update θ j γ i).val
      (Function.update u j (fun _ => (0 : EReal)) i)) :
    globalMixedMeasure (Function.update θ j (θ j + c • γ)) u hu' =
      globalMixedMeasure θ u hu + ENNReal.ofReal c •
        globalMixedMeasure (Function.update θ j γ) (Function.update u j (fun _ => (0 : EReal)))
          h0 := by
  classical
  set θ' := Function.update θ j (θ j + c • γ) with hθ'
  have hrestθ : Function.update θ' j (θ j) = θ := by
    rw [hθ', Function.update_idem, Function.update_eq_self]
  have hθ'γ : Function.update θ' j γ = Function.update θ j γ := by
    rw [hθ', Function.update_idem]
  have hrestu : Function.update u j (u j) = u := Function.update_eq_self _ _
  have hcomb : Function.update u j
      (fun p => ((1 : ℝ) : EReal) * u j p + ((c : ℝ) : EReal) * (0 : EReal)) = u := by
    funext i
    by_cases hi : i = j
    · subst hi; funext p; simp
    · simp [Function.update_of_ne hi]
  have ha : ∀ i, ThetaPlurisubharmonic ((Function.update θ' j (θ j)) i).val
      ((Function.update u j (u j)) i) := by
    rw [hrestθ, hrestu]; exact hu
  have hb : ∀ i, ThetaPlurisubharmonic ((Function.update θ' j γ) i).val
      ((Function.update u j (fun _ : M => (0 : EReal))) i) := by
    rw [hθ'γ]; exact h0
  have hcc : ∀ i, ThetaPlurisubharmonic (θ' i).val
      ((Function.update u j
        (fun p => ((1 : ℝ) : EReal) * u j p + ((c : ℝ) : EReal) * (0 : EReal))) i) := by
    rw [hcomb]; exact hu'
  have hkey := GlobalSlotLinear.globalMixedMeasure_update_add_smul (θ := θ') j (α := θ j)
      (β := γ) (s := 1) (r := c) one_pos hc (by rw [hθ']; simp) (x := u) (a := u j)
      (b := fun _ : M => (0 : EReal)) hcc ha hb
      (GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate hb hnd) (by simp)
  rw [ENNReal.ofReal_one, one_smul] at hkey
  calc globalMixedMeasure θ' u hu'
      = globalMixedMeasure θ' (Function.update u j
          (fun p => ((1 : ℝ) : EReal) * u j p + ((c : ℝ) : EReal) * (0 : EReal))) hcc :=
        globalMixedMeasure_congr_tuples rfl hcomb.symm hu' hcc
    _ = _ := hkey
    _ = globalMixedMeasure θ u hu + ENNReal.ofReal c • globalMixedMeasure
          (Function.update θ j γ) (Function.update u j (fun _ => (0 : EReal))) h0 := by
        rw [globalMixedMeasure_congr_tuples hrestθ hrestu ha hu,
          globalMixedMeasure_congr_tuples hθ'γ rfl hb h0]

/-! ### Several slots: monotonicity -/

/-- **Enlarging the backgrounds of the slots in `S`** by `c • γ` (`c > 0`, `γ` semipositive) does
not decrease the global mixed measure. -/
theorem globalMixedMeasure_le_of_add_smul_on {θ θ' : Fin N → ClosedRealOneOneForm N M}
    {u : Fin N → M → EReal} (S : Finset (Fin N)) {γ : ClosedRealOneOneForm N M}
    (hγ : γ.val.IsSemipositive) {c : ℝ} (hc : 0 < c)
    (hθ' : ∀ i, θ' i = if i ∈ S then θ i + c • γ else θ i)
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i))
    (hnd : ∀ i ∈ S, IsThetaPshPotential (θ i).val (u i))
    (hu' : ∀ i, ThetaPlurisubharmonic (θ' i).val (u i)) :
    globalMixedMeasure θ u hu ≤ globalMixedMeasure θ' u hu' := by
  classical
  set T : Finset (Fin N) → Fin N → ClosedRealOneOneForm N M :=
    fun s i => if i ∈ s then θ i + c • γ else θ i with hT
  have hTpsh : ∀ s i, ThetaPlurisubharmonic (T s i).val (u i) := by
    intro s i
    by_cases hi : i ∈ s
    · simp only [hT, if_pos hi]
      exact thetaPlurisubharmonic_add_of_isSemipositive (hu i) (isSemipositive_smul hγ hc.le)
    · simp only [hT, if_neg hi]
      exact hu i
  have key : ∀ s : Finset (Fin N), s ⊆ S →
      globalMixedMeasure (T ∅) u (hTpsh ∅) ≤ globalMixedMeasure (T s) u (hTpsh s) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; exact le_rfl
    | insert j s hj ih =>
        intro hsub
        refine (ih ((Finset.subset_insert j s).trans hsub)).trans ?_
        have hTs : T s j = θ j := by simp [hT, hj]
        have hupd : T (insert j s) = Function.update (T s) j (T s j + c • γ) := by
          funext i
          by_cases hi : i = j
          · subst hi; simp [hT, hj]
          · simp [hT, Finset.mem_insert, hi]
        exact globalMixedMeasure_le_of_eq_update_add_smul j hγ hc hupd (hTpsh s)
          (by rw [hTs]; exact hnd j (hsub (Finset.mem_insert_self j s))) (hTpsh (insert j s))
  have hempty : T ∅ = θ := by funext i; simp [hT]
  have hS : T S = θ' := by funext i; rw [hθ' i]
  calc globalMixedMeasure θ u hu = globalMixedMeasure (T ∅) u (hTpsh ∅) :=
        globalMixedMeasure_congr_tuples hempty.symm rfl _ _
    _ ≤ globalMixedMeasure (T S) u (hTpsh S) := key S subset_rfl
    _ = globalMixedMeasure θ' u hu' := globalMixedMeasure_congr_tuples hS rfl _ _

/-! ### Several slots: the increment is `O(ε)` -/

/-- The family `θᵢ + εω` on the slots of `S`, `θᵢ` elsewhere. -/
def bumpOn (w : KahlerBackground N M) (θ : Fin N → ClosedRealOneOneForm N M) (S : Finset (Fin N))
    (ε : ℝ) : Fin N → ClosedRealOneOneForm N M :=
  fun i => if i ∈ S then θ i + ε • w.form else θ i

theorem thetaPlurisubharmonic_bumpOn (w : KahlerBackground N M)
    {θ : Fin N → ClosedRealOneOneForm N M} {u : Fin N → M → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) (S : Finset (Fin N)) {ε : ℝ} (hε : 0 ≤ ε)
    (i : Fin N) : ThetaPlurisubharmonic (bumpOn w θ S ε i).val (u i) := by
  classical
  unfold bumpOn
  split_ifs
  · exact thetaPlurisubharmonic_add_of_isSemipositive (hu i) (isSemipositive_smul w.isSemipositive hε)
  · exact hu i

/-- **The increment is linear in `ε`**: there is `K < ∞` with
`μ(θ + εω on S) ≤ μ(θ) + ε K` for `0 < ε ≤ 1`. -/
theorem exists_globalMixedMass_bumpOn_le (w : KahlerBackground N M)
    {θ : Fin N → ClosedRealOneOneForm N M} {u : Fin N → M → EReal}
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i)) (S : Finset (Fin N)) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ ε : ℝ, (hε : 0 < ε) → ε ≤ 1 →
      globalMixedMass (bumpOn w θ S ε) u
          (thetaPlurisubharmonic_bumpOn w (fun i => (hu i).1) S hε.le) ≤
        globalMixedMass θ u (fun i => (hu i).1) + ENNReal.ofReal ε * K := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨0, ENNReal.zero_lt_top, fun ε hε _ => ?_⟩
      have h : bumpOn w θ ∅ ε = θ := by funext i; simp [bumpOn]
      rw [mul_zero, add_zero]
      exact (congrArg (fun μ : Measure M => μ univ)
        (globalMixedMeasure_congr_tuples h rfl _ (fun i => (hu i).1))).le
  | insert j S hj ih =>
      obtain ⟨K, hK, hle⟩ := ih
      -- the measure with `ω` and the potential `0` in slot `j`, at `ε = 1`
      have h0 : ∀ ε : ℝ, 0 ≤ ε → ∀ i, ThetaPlurisubharmonic
          (Function.update (bumpOn w θ S ε) j w.form i).val
          (Function.update u j (fun _ => (0 : EReal)) i) := by
        intro ε hε i
        by_cases hi : i = j
        · subst hi
          simp only [Function.update_self]
          exact (Pending.LocalPotentials.thetaPlurisubharmonic_zero_iff w.form).mpr
            w.isSemipositive
        · simp only [Function.update_of_ne hi]
          exact thetaPlurisubharmonic_bumpOn w (fun i => (hu i).1) S hε i
      set E : ℝ → ℝ≥0∞ := fun ε => if hε : 0 ≤ ε then
        globalMixedMass (Function.update (bumpOn w θ S ε) j w.form)
          (Function.update u j (fun _ => (0 : EReal))) (h0 ε hε) else 0 with hEdef
      have hE1 : E 1 < ⊤ := by
        simp only [hEdef, dif_pos zero_le_one]
        exact globalMixedMass_lt_top w _
      have hEmono : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → E ε ≤ E 1 := by
        intro ε hε hε1
        rcases eq_or_lt_of_le hε1 with h1 | h1
        · rw [h1]
        simp only [hEdef, dif_pos hε.le, dif_pos zero_le_one]
        refine Measure.le_iff'.mp
          (globalMixedMeasure_le_of_add_smul_on S w.isSemipositive (sub_pos.mpr h1) ?_ _ ?_ _) univ
        · intro i
          by_cases hiS : i ∈ S
          · have hij : i ≠ j := fun h => hj (h ▸ hiS)
            simp only [Function.update_of_ne hij, if_pos hiS, bumpOn]
            apply ClosedRealOneOneForm.ext
            intro e z
            simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul]
            module
          · simp only [if_neg hiS]
            by_cases hij : i = j
            · subst hij; simp only [Function.update_self]
            · simp only [Function.update_of_ne hij, bumpOn, if_neg hiS]
        · intro i hiS
          have hij : i ≠ j := fun h => hj (h ▸ hiS)
          simp only [Function.update_of_ne hij]
          exact ⟨thetaPlurisubharmonic_bumpOn w (fun i => (hu i).1) S hε.le i, (hu i).2⟩
      refine ⟨K + E 1, ENNReal.add_lt_top.mpr ⟨hK, hE1⟩, fun ε hε hε1 => ?_⟩
      have hupd : bumpOn w θ (insert j S) ε =
          Function.update (bumpOn w θ S ε) j (bumpOn w θ S ε j + ε • w.form) := by
        funext i
        by_cases hi : i = j
        · subst hi; simp [bumpOn, hj]
        · simp [bumpOn, Finset.mem_insert, hi]
      have hjθ : bumpOn w θ S ε j = θ j := by simp [bumpOn, hj]
      have hstep := globalMixedMeasure_update_add_smul_eq (θ := bumpOn w θ S ε) (u := u) j
        (γ := w.form) hε (thetaPlurisubharmonic_bumpOn w (fun i => (hu i).1) S hε.le)
        (by rw [hjθ]; exact hu j)
        (by rw [← hupd]; exact thetaPlurisubharmonic_bumpOn w (fun i => (hu i).1) _ hε.le)
        (h0 ε hε.le)
      have hEε : globalMixedMeasure (Function.update (bumpOn w θ S ε) j w.form)
          (Function.update u j (fun _ => (0 : EReal))) (h0 ε hε.le) univ = E ε := by
        simp only [hEdef, dif_pos hε.le]; rfl
      calc globalMixedMass (bumpOn w θ (insert j S) ε) u _
          = globalMixedMeasure (Function.update (bumpOn w θ S ε) j
              (bumpOn w θ S ε j + ε • w.form)) u _ univ :=
            congrArg (fun μ : Measure M => μ univ) (globalMixedMeasure_congr_tuples hupd rfl _ _)
        _ = globalMixedMass (bumpOn w θ S ε) u _ + ENNReal.ofReal ε * E ε := by
            rw [hstep, Measure.add_apply, Measure.smul_apply, smul_eq_mul, hEε]; rfl
        _ ≤ (globalMixedMass θ u (fun i => (hu i).1) + ENNReal.ofReal ε * K) +
              ENNReal.ofReal ε * E 1 := by
            gcongr
            · exact hle ε hε hε1
            · exact hEmono ε hε hε1
        _ = globalMixedMass θ u (fun i => (hu i).1) + ENNReal.ofReal ε * (K + E 1) := by
            rw [mul_add, add_assoc]

/-! ### The smooth comparison at `ε > 0` -/

/-- **At `ε > 0`**: for nef slots and bounded potentials, the total mixed mass in the classes
`θᵢ + εω` is the slot integral. -/
theorem globalMixedMass_add_smul_toReal (hN : 0 < N) (w : KahlerBackground N M)
    {θ : Fin N → ClosedRealOneOneForm N M} (hnef : ∀ i, NefWithRespectTo w (θ i))
    {u : Fin N → M → EReal} (hu : ∀ i, IsThetaPshPotential (θ i).val (u i))
    (hb : ∀ i, IsBoundedPotential (u i)) {ε : ℝ} (hε : 0 < ε)
    (hu' : ∀ i, ThetaPlurisubharmonic (θ i + ε • w.form).val (u i)) :
    (globalMixedMass (fun i => θ i + ε • w.form) u hu').toReal =
      slotIntegral w (fun i => θ i + ε • w.form) := by
  choose f hf hsemi using fun i => exists_isSemipositive_of_nef (hnef i) hε
  have hfpsh : ∀ i, ThetaPlurisubharmonic (θ i + ε • w.form).val (fun x => (f i x : EReal)) := by
    intro i
    refine (Pending.LocalPotentials.thetaPlurisubharmonic_smooth_iff _ (f i) (hf i)).mpr ?_
    intro e z hz v
    have h := hsemi i e z hz v
    simpa only [ClosedRealOneOneForm.coeff_add, ddcClosedForm_coeff,
      ContinuousAlternatingMap.add_apply] using h
  have hfpot : ∀ i, IsThetaPshPotential (θ i + ε • w.form).val (fun x => (f i x : EReal)) :=
    fun i => ⟨hfpsh i, fun x _ _ hxU => ⟨x, hxU, EReal.coe_ne_bot _⟩⟩
  have hupot : ∀ i, IsThetaPshPotential (θ i + ε • w.form).val (u i) := fun i => ⟨hu' i, (hu i).2⟩
  have hsame : ∀ i, SameSingularityTypeOn (u i) (fun x => (f i x : EReal)) univ := by
    intro i
    obtain ⟨a, b, hab⟩ := hb i
    obtain ⟨m, hm⟩ := isCompact_univ.exists_bound_of_continuousOn
      (CurrentTraceMeasure.chartSmooth_continuous (hf i)).continuousOn
    have hm' : ∀ x, -m ≤ f i x ∧ f i x ≤ m := fun x => abs_le.mp (by
      simpa [Real.norm_eq_abs] using hm x (mem_univ x))
    constructor
    · refine ⟨b + m, fun x _ => ?_⟩
      calc u i x ≤ (b : EReal) := (hab x).2
        _ ≤ ((f i x + (b + m) : ℝ) : EReal) :=
            EReal.coe_le_coe_iff.mpr (by linarith [(hm' x).1])
        _ = (f i x : EReal) + ((b + m : ℝ) : EReal) := EReal.coe_add _ _
    · refine ⟨m - a, fun x _ => ?_⟩
      calc (f i x : EReal) ≤ ((a + (m - a) : ℝ) : EReal) :=
            EReal.coe_le_coe_iff.mpr (by linarith [(hm' x).2])
        _ = (a : EReal) + ((m - a : ℝ) : EReal) := EReal.coe_add _ _
        _ ≤ u i x + ((m - a : ℝ) : EReal) := add_le_add_left (hab x).1 _
  have h1 := globalMixedMass_eq_of_sameSingularityType hN w hupot hfpot hsame
  have h2 := globalMixedMass_changeRepresentative (θ := fun i => θ i + ε • w.form)
    (η := fun i => θ i + ε • w.form + ddcClosedForm (f i) (hf i)) (f := f) hf
    (fun i e z _ => by simp only [ClosedRealOneOneForm.coeff_add, ddcClosedForm_coeff]) hfpsh
  have hzero : (fun i x => ((f i x : ℝ) : EReal) - ((f i x : ℝ) : EReal)) =
      fun (_ : Fin N) (_ : M) => (0 : EReal) := by
    funext i x
    rw [← EReal.coe_sub, sub_self, EReal.coe_zero]
  have hη0 : ∀ i, ThetaPlurisubharmonic (θ i + ε • w.form + ddcClosedForm (f i) (hf i)).val
      (fun _ => (0 : EReal)) := fun i =>
    (Pending.LocalPotentials.thetaPlurisubharmonic_zero_iff _).mpr (hsemi i)
  have h3 : globalMixedMass (fun i => θ i + ε • w.form + ddcClosedForm (f i) (hf i))
      (fun i x => ((f i x : ℝ) : EReal) - ((f i x : ℝ) : EReal))
        (fun i => GlobalPotentialTransforms.thetaPlurisubharmonic_sub_smooth (hf i)
          (fun e z _ => by simp only [ClosedRealOneOneForm.coeff_add, ddcClosedForm_coeff])
          (hfpsh i)) =
      globalMixedMass (fun i => θ i + ε • w.form + ddcClosedForm (f i) (hf i))
        (fun _ _ => (0 : EReal)) hη0 :=
    congrArg (fun μ : Measure M => μ univ) (globalMixedMeasure_congr_tuples rfl hzero _ _)
  have h4 := MixedMassClassInvariance.globalMixedMeasure_real_univ_eq_integral w
    (fun i => θ i + ε • w.form + ddcClosedForm (f i) (hf i)) hη0
  rw [h1, ← h2, h3, ← slotIntegral_add_ddc w (fun i => θ i + ε • w.form) f hf]
  exact h4

/-! ### The limit -/

/-- **Bounded potentials in nef classes** (mixed form of `pc:domination-intersection` (1)): on a
compact complex manifold of dimension `N > 0` with a Kähler form `ω`, if every `θᵢ` is nef and every
`uᵢ` is a bounded `θᵢ`-psh potential, then
`∫ ⟨(θ₀ + ddᶜu₀) ∧ ⋯ ∧ (θ_{N-1} + ddᶜu_{N-1})⟩ = ∫ θ₀ ∧ ⋯ ∧ θ_{N-1}`. -/
theorem globalMixedMass_toReal_eq_slotIntegral (hN : 0 < N) (w : KahlerBackground N M)
    {θ : Fin N → ClosedRealOneOneForm N M} (hnef : ∀ i, NefWithRespectTo w (θ i))
    {u : Fin N → M → EReal} (hu : ∀ i, IsThetaPshPotential (θ i).val (u i))
    (hb : ∀ i, IsBoundedPotential (u i)) :
    (globalMixedMass θ u (fun i => (hu i).1)).toReal = slotIntegral w θ := by
  classical
  set m := (globalMixedMass θ u (fun i => (hu i).1)).toReal with hmdef
  obtain ⟨K, hK, hle⟩ := exists_globalMixedMass_bumpOn_le w hu Finset.univ
  have hbump : ∀ ε, bumpOn w θ Finset.univ ε = fun i => θ i + ε • w.form := by
    intro ε; funext i; simp [bumpOn]
  have hpsh : ∀ ε : ℝ, 0 ≤ ε → ∀ i, ThetaPlurisubharmonic (θ i + ε • w.form).val (u i) :=
    fun ε hε i => thetaPlurisubharmonic_add_of_isSemipositive (hu i).1
      (isSemipositive_smul w.isSemipositive hε)
  -- lower and upper bounds at `ε > 0`
  have hlow : ∀ ε : ℝ, 0 < ε → m ≤ slotIntegral w (fun i => θ i + ε • w.form) := by
    intro ε hε
    rw [← globalMixedMass_add_smul_toReal hN w hnef hu hb hε (hpsh ε hε.le)]
    exact ENNReal.toReal_mono (globalMixedMass_lt_top w _).ne
      (Measure.le_iff'.mp (globalMixedMeasure_le_of_add_smul_on Finset.univ w.isSemipositive hε
        (by simp) _ (fun i _ => hu i) _) univ)
  have hupp : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      slotIntegral w (fun i => θ i + ε • w.form) ≤ m + ε * K.toReal := by
    intro ε hε hε1
    rw [← globalMixedMass_add_smul_toReal hN w hnef hu hb hε (hpsh ε hε.le)]
    have h := hle ε hε hε1
    have hθε : globalMixedMass (fun i => θ i + ε • w.form) u (hpsh ε hε.le) =
        globalMixedMass (bumpOn w θ Finset.univ ε) u
          (thetaPlurisubharmonic_bumpOn w (fun i => (hu i).1) Finset.univ hε.le) :=
      congrArg (fun μ : Measure M => μ univ)
        (globalMixedMeasure_congr_tuples (hbump ε).symm rfl _ _)
    rw [hθε]
    have hfin : globalMixedMass θ u (fun i => (hu i).1) + ENNReal.ofReal ε * K ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨(globalMixedMass_lt_top w _).ne,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK.ne⟩
    refine (ENNReal.toReal_mono hfin h).trans ?_
    rw [ENNReal.toReal_add (globalMixedMass_lt_top w _).ne
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK.ne), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hε.le]
  -- the slot integrals converge as `ε → 0⁺`
  have hcont := (continuous_slotIntegral_add_smul w θ fun _ => w.form).continuousWithinAt
    (s := Ioi (0 : ℝ)) (x := 0)
  have hcont' : Tendsto (fun t : ℝ => slotIntegral w fun i => θ i + t • w.form) (𝓝[>] 0)
      (𝓝 (slotIntegral w θ)) := by
    simpa only [zero_smul, add_zero] using hcont.tendsto
  apply le_antisymm
  · refine ge_of_tendsto hcont' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hlow ε hε
  · have hlim : Tendsto (fun ε : ℝ => m + ε * K.toReal) (𝓝[>] 0) (𝓝 m) := by
      have : Tendsto (fun ε : ℝ => m + ε * K.toReal) (𝓝 0) (𝓝 (m + 0 * K.toReal)) :=
        (continuous_const.add (continuous_id.mul continuous_const)).tendsto 0
      rw [zero_mul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto_of_tendsto hcont' hlim ?_
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε hε1
    exact hupp ε hε hε1.2.le

end

end SGPT.Foundations.Analysis.Pending.NefBoundedMixedMass
