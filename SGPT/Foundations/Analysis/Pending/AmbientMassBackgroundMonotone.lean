import SGPT.Foundations.Analysis.Pending.GlobalSlotLinear
import SGPT.Foundations.Analysis.Pending.DiagonalMass
import SGPT.Foundations.Analysis.Pending.LocalPotentials

set_option autoImplicit false

/-!
# The global non-pluripolar mass is monotone in the background form

Fix a theta-PSH potential `u` and enlarge the background by a semipositive
closed real `(1,1)`-form: replace `θ` by `θ + c • γ` with `c > 0` and
`γ` semipositive.  Then the global mixed non-pluripolar measure does not
decrease.

The proof needs no new analysis.  `GlobalSlotLinear` already proves *positive
linearity in one slot*, in the form which also splits the background form of
that slot: if `θ i₀ = s • α + r • β` and the potentials in slot `i₀` are
`a`, `b` and `s a + r b`, then the measures add.  Taking `b = 0` and `s = 1`,
`r = c` gives `1 * a + c * 0 = a`, so the *same* potential tuple appears on both
sides while the background of slot `i₀` grows by `c • γ`, and the extra summand
`c • (measure with `0` in slot `i₀`)` is a genuine measure.  Dropping it is the
inequality.  Iterating over the slots of a diagonal tuple gives
`diagonalPotentialMass` monotonicity, which is what the perturbed
full-space ambient envelopes need at two different errors.

The two pole hypotheses of the linearity theorem are discharged, not assumed:
the potential `0` never takes the value `⊥`, and the poles of `u` are null for
every global mixed measure once `u` is locally nondegenerate
(`GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate`).  This
is exactly where `IsThetaPshPotential` rather than bare `ThetaPlurisubharmonic`
is needed: for `u ≡ -∞` the statement would compare two zero measures, but the
linearity input is not available.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.AmbientMassBackgroundMonotone

open FirstPass FirstPass.PositiveClasses
open GlobalNonPluripolar GlobalSlotLinear GlobalDiagonalScaling DiagonalMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [BorelSpace M] in
/-- Both tuple arguments of the global mixed measure are congruent; the
`ThetaPlurisubharmonic` proof argument is irrelevant. -/
theorem globalMixedMeasure_congr_tuples {θ θ' : Fin n → ClosedRealOneOneForm n M}
    {u u' : Fin n → M → EReal} (hθ : θ = θ') (hu : u = u')
    (h : ∀ i, ThetaPlurisubharmonic (θ i).val (u i))
    (h' : ∀ i, ThetaPlurisubharmonic (θ' i).val (u' i)) :
    globalMixedMeasure θ u h = globalMixedMeasure θ' u' h' := by
  subst hθ
  subst hu
  rfl

/-- **One slot.**  Enlarging the background of a single slot by `c • γ`, with
`c > 0` and `γ` semipositive, does not decrease the global mixed measure.  The
potential tuple is unchanged. -/
theorem globalMixedMeasure_le_of_eq_update_add_smul
    {θ θ' : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal} (i₀ : Fin n)
    {γ : ClosedRealOneOneForm n M} (hγ : γ.val.IsSemipositive) {c : ℝ} (hc : 0 < c)
    (hθ' : θ' = Function.update θ i₀ (θ i₀ + c • γ))
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i))
    (hnd : IsThetaPshPotential (θ i₀).val (u i₀))
    (hu' : ∀ i, ThetaPlurisubharmonic (θ' i).val (u i)) :
    globalMixedMeasure θ u hu ≤ globalMixedMeasure θ' u hu' := by
  classical
  have hθ'ne : ∀ i, i ≠ i₀ → θ' i = θ i := by
    intro i hi
    rw [hθ', Function.update_of_ne hi]
  -- the zero potential is `γ`-PSH because `γ` is semipositive
  have h0 : ThetaPlurisubharmonic γ.val (fun _ : M => (0 : EReal)) :=
    (LocalPotentials.thetaPlurisubharmonic_zero_iff γ).mpr hγ
  -- restoring slot `i₀` recovers the original background and potential tuples
  have hrestθ : Function.update θ' i₀ (θ i₀) = θ := by
    funext i
    by_cases hi : i = i₀
    · subst hi; simp
    · rw [Function.update_of_ne hi, hθ'ne i hi]
  have hrestu : Function.update u i₀ (u i₀) = u := Function.update_eq_self _ _
  -- the combined potential in slot `i₀` is again `u i₀`
  have hcomb : Function.update u i₀
      (fun p => ((1 : ℝ) : EReal) * u i₀ p + ((c : ℝ) : EReal) * (0 : EReal)) = u := by
    funext i
    by_cases hi : i = i₀
    · subst hi; funext p; simp
    · simp [Function.update_of_ne hi]
  have hb : ∀ i, ThetaPlurisubharmonic ((Function.update θ' i₀ γ) i).val
      ((Function.update u i₀ (fun _ : M => (0 : EReal))) i) := by
    intro i
    by_cases hi : i = i₀
    · subst hi; simpa using h0
    · rw [Function.update_of_ne hi, Function.update_of_ne hi, hθ'ne i hi]
      exact hu i
  have ha : ∀ i, ThetaPlurisubharmonic ((Function.update θ' i₀ (θ i₀)) i).val
      ((Function.update u i₀ (u i₀)) i) := by
    rw [hrestθ, hrestu]; exact hu
  have hcc : ∀ i, ThetaPlurisubharmonic (θ' i).val
      ((Function.update u i₀
        (fun p => ((1 : ℝ) : EReal) * u i₀ p + ((c : ℝ) : EReal) * (0 : EReal))) i) := by
    rw [hcomb]; exact hu'
  have hkey := globalMixedMeasure_update_add_smul (θ := θ') i₀ (α := θ i₀) (β := γ)
      (s := 1) (r := c) one_pos hc (by rw [hθ']; simp) (x := u) (a := u i₀)
      (b := fun _ : M => (0 : EReal)) hcc ha hb
      (globalMixedMeasure_pole_null_of_nondegenerate hb hnd) (by simp)
  calc globalMixedMeasure θ u hu
      = globalMixedMeasure (Function.update θ' i₀ (θ i₀))
          (Function.update u i₀ (u i₀)) ha :=
        globalMixedMeasure_congr_tuples hrestθ.symm hrestu.symm hu ha
    _ ≤ ENNReal.ofReal 1 • globalMixedMeasure (Function.update θ' i₀ (θ i₀))
            (Function.update u i₀ (u i₀)) ha +
          ENNReal.ofReal c • globalMixedMeasure (Function.update θ' i₀ γ)
            (Function.update u i₀ (fun _ : M => (0 : EReal))) hb := by
        simp only [ENNReal.ofReal_one, one_smul]
        exact Measure.le_add_right le_rfl
    _ = globalMixedMeasure θ' (Function.update u i₀
          (fun p => ((1 : ℝ) : EReal) * u i₀ p + ((c : ℝ) : EReal) * (0 : EReal))) hcc :=
        hkey.symm
    _ = globalMixedMeasure θ' u hu' :=
        globalMixedMeasure_congr_tuples rfl hcomb hcc hu'

/-- **All slots at once.**  For a diagonal tuple, enlarging the background by
`c • γ` with `c > 0` and `γ` semipositive does not decrease the global mixed
measure.  This is the one-slot statement iterated over the `n` slots. -/
theorem globalMixedMeasure_diagonal_le_add_smul
    {a γ : ClosedRealOneOneForm n M} (hγ : γ.val.IsSemipositive) {c : ℝ} (hc : 0 < c)
    {u : M → EReal} (hu : IsThetaPshPotential a.val u)
    (hu' : ThetaPlurisubharmonic (a + c • γ).val u) :
    globalMixedMeasure (fun _ : Fin n => a) (fun _ => u) (fun _ => hu.1) ≤
      globalMixedMeasure (fun _ : Fin n => a + c • γ) (fun _ => u) (fun _ => hu') := by
  classical
  set T : Finset (Fin n) → Fin n → ClosedRealOneOneForm n M :=
    fun s i => if i ∈ s then a + c • γ else a with hT
  have hTpsh : ∀ s i, ThetaPlurisubharmonic (T s i).val u := by
    intro s i
    by_cases hi : i ∈ s
    · simpa [hT, hi] using hu'
    · simpa [hT, hi] using hu.1
  have key : ∀ s : Finset (Fin n),
      globalMixedMeasure (T ∅) (fun _ => u) (fun i => hTpsh ∅ i) ≤
        globalMixedMeasure (T s) (fun _ => u) (fun i => hTpsh s i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact le_rfl
    | insert i₀ s hi₀ ih =>
        refine ih.trans ?_
        have hTs : T s i₀ = a := by simp [hT, hi₀]
        have hupd : T (insert i₀ s) = Function.update (T s) i₀ (T s i₀ + c • γ) := by
          funext j
          by_cases hj : j = i₀
          · subst hj; simp [hT, hi₀]
          · simp [hT, Finset.mem_insert, hj]
        exact globalMixedMeasure_le_of_eq_update_add_smul i₀ hγ hc hupd
          (fun i => hTpsh s i) (by rw [hTs]; exact hu) (fun i => hTpsh (insert i₀ s) i)
  have hempty : T ∅ = fun _ : Fin n => a := by funext j; simp [hT]
  have huniv : T Finset.univ = fun _ : Fin n => a + c • γ := by funext j; simp [hT]
  calc globalMixedMeasure (fun _ : Fin n => a) (fun _ => u) (fun _ => hu.1)
      = globalMixedMeasure (T ∅) (fun _ => u) (fun i => hTpsh ∅ i) :=
        globalMixedMeasure_congr_tuples hempty.symm rfl _ _
    _ ≤ globalMixedMeasure (T Finset.univ) (fun _ => u) (fun i => hTpsh Finset.univ i) :=
        key Finset.univ
    _ = globalMixedMeasure (fun _ : Fin n => a + c • γ) (fun _ => u) (fun _ => hu') :=
        globalMixedMeasure_congr_tuples huniv rfl _ _

/-- **The diagonal non-pluripolar mass is nondecreasing in the background.** -/
theorem diagonalPotentialMass_le_add_smul
    {a γ : ClosedRealOneOneForm n M} (hγ : γ.val.IsSemipositive) {c : ℝ} (hc : 0 < c)
    {u : M → EReal} (hu : IsThetaPshPotential a.val u)
    (hu' : IsThetaPshPotential (a + c • γ).val u) :
    diagonalPotentialMass a u hu ≤ diagonalPotentialMass (a + c • γ) u hu' :=
  globalMixedMeasure_diagonal_le_add_smul hγ hc hu hu'.1 _

end

end SGPT.Foundations.Analysis.Pending.AmbientMassBackgroundMonotone
