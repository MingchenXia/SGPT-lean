import SGPT.Foundations.Analysis.Pending.BoundedIntegrationByParts
import SGPT.Foundations.Analysis.Pending.NefBoundedMixedMass
import SGPT.Foundations.Analysis.Pending.GlobalMixedMassMonotone
import SGPT.Foundations.Analysis.Pending.ModificationMassInvariance
import SGPT.Foundations.Analysis.Pending.ProductTestForms

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Intersection numbers on a compact Kähler manifold: bounded potentials, pseudoeffective slots and blowups

Source: Copy-4, `lem:domination`, Step 2 (blueprint `pc:domination-intersection`). For smooth closed
real `(1,1)`-forms `θ₀, …, θ_{N-1}` on a compact complex manifold `M` of dimension `N` with a Kähler
form `ω`, the intersection number of their classes is the slot integral
`slotIntegral w θ = ∫_M θ₀ ∧ ⋯ ∧ θ_{N-1}` (`NefMixedMass.slotIntegral`, normalized as the
non-pluripolar masses).

## Main results

* `nefWithRespectTo_of_isBoundedPotential` — **a class with a bounded potential is nef**: if `u` is
  a bounded `θ`-psh function, then for every `ε > 0` there is a smooth `h` with
  `θ + εω + ddᶜh ≥ 0`. Demailly's decreasing regularization of a bounded potential with curvature
  loss `ω / (k + 1)` (`BoundedIntegrationByParts.exists_antitone_chartSmooth`) gives `h`.
* `globalMixedMass_toReal_eq_slotIntegral_of_isBoundedPotential` — `pc:domination-intersection` (1),
  mixed and in every dimension: for arbitrary closed real `(1,1)`-forms `θᵢ` and bounded `θᵢ`-psh
  `uᵢ`, `∫ ⟨(θ₀ + ddᶜu₀) ∧ ⋯ ∧ (θ_{N-1} + ddᶜu_{N-1})⟩ = ∫ θ₀ ∧ ⋯ ∧ θ_{N-1}`. For `N > 0` this
  is `NefBoundedMixedMass.globalMixedMass_toReal_eq_slotIntegral` with the nefness above; for
  `N = 0` both sides are the mass of the measure of the empty tuple.
* `slotIntegral_nonneg_of_pseudoeffective` — `pc:domination-intersection` (2): if one slot is
  pseudoeffective (it carries a `θ`-psh potential) and every other slot is nef, the slot integral
  is `≥ 0`.
* `slotIntegral_pullback_of_isBlowupSequence` — `pc:domination-intersection` (3): intersection
  numbers do not change under pullback along a finite sequence of blowups with smooth centres.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.DominationIntersectionNumbers

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar MixedMass NefMixedMass
  BoundedGlobalProduct

noncomputable section

section Nef

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M]

/-- **A class with a bounded potential is nef.** If `u` is a bounded `θ`-psh function on a
compact Kähler manifold, then `θ` is nef: Demailly's decreasing regularization of `u` consists of
chart-smooth `(θ + ω / (k + 1))`-psh functions, and `ω / (k + 1) ≤ εω` for `k` large. -/
theorem nefWithRespectTo_of_isBoundedPotential [CompactSpace M] (w : KahlerBackground N M)
    {θ : ClosedRealOneOneForm N M} {u : M → EReal} (hu : ThetaPlurisubharmonic θ.val u)
    (hb : IsBoundedPotential u) : NefWithRespectTo w θ := by
  obtain ⟨uk, hsm, hpsh, -, -⟩ := BoundedIntegrationByParts.exists_antitone_chartSmooth w θ hu hb
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  refine ⟨uk k, hsm k, fun e z hz v => ?_⟩
  have h1 := (LocalPotentials.thetaPlurisubharmonic_smooth_iff
    (θ + (1 / ((k : ℝ) + 1)) • w.form) (uk k) (hsm k)).mp (hpsh k) e z hz v
  have h2 := w.isSemipositive e z hz v
  simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul] at h1 ⊢
  have hk0 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  nlinarith

end Nef

/-! ### (1) Bounded potentials -/

section Mass

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- A bounded `θ`-psh function is a `θ`-psh potential: it is nowhere `-∞`. -/
theorem isThetaPshPotential_of_isBoundedPotential {θ : SmoothRealForm N M 2} {u : M → EReal}
    (hu : ThetaPlurisubharmonic θ u) (hb : IsBoundedPotential u) : IsThetaPshPotential θ u := by
  obtain ⟨a, b, hab⟩ := hb
  exact ⟨hu, fun x _ _ hxU => ⟨x, hxU, ne_bot_of_le_ne_bot (EReal.coe_ne_bot a) (hab x).1⟩⟩

/-- **The total mixed mass of bounded potentials is the intersection number**
(`pc:domination-intersection` (1), mixed form, every dimension). On a compact complex manifold of
dimension `N` with a Kähler form, for arbitrary closed real `(1,1)`-forms `θᵢ` and bounded `θᵢ`-psh
functions `uᵢ`,
`∫ ⟨(θ₀ + ddᶜu₀) ∧ ⋯ ∧ (θ_{N-1} + ddᶜu_{N-1})⟩ = ∫ θ₀ ∧ ⋯ ∧ θ_{N-1}`.
No positivity of the forms is assumed: a bounded potential makes its class nef
(`nefWithRespectTo_of_isBoundedPotential`). -/
theorem globalMixedMass_toReal_eq_slotIntegral_of_isBoundedPotential (w : KahlerBackground N M)
    {θ : Fin N → ClosedRealOneOneForm N M} {u : Fin N → M → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) (hb : ∀ i, IsBoundedPotential (u i)) :
    (globalMixedMass θ u hu).toReal = slotIntegral w θ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h0 : ∀ i, ThetaPlurisubharmonic (θ i).val (fun _ => (0 : EReal)) := fun i => i.elim0
    have e : globalMixedMeasure θ u hu = globalMixedMeasure θ (fun _ _ => 0) h0 :=
      UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple (Subsingleton.elim _ _) _ _
    rw [globalMixedMass, e, ← measureReal_def]
    exact MixedMassClassInvariance.globalMixedMeasure_real_univ_eq_integral w θ h0
  · exact NefBoundedMixedMass.globalMixedMass_toReal_eq_slotIntegral hN w
      (fun i => nefWithRespectTo_of_isBoundedPotential w (hu i) (hb i))
      (fun i => isThetaPshPotential_of_isBoundedPotential (hu i) (hb i)) hb

/-- **`pc:domination-intersection` (1), as stated**: if `α` is a smooth closed real `(1,1)`-form and
`b` a bounded `α`-psh function on a compact Kähler manifold of dimension `N`, then
`∫ ⟨α_b^N⟩ = {α}^N = ∫ α^N`. -/
theorem diagonalMass_toReal_eq_slotIntegral_of_isBoundedPotential (w : KahlerBackground N M)
    {α : ClosedRealOneOneForm N M} {b : M → EReal} (hb : ThetaPlurisubharmonic α.val b)
    (hbb : IsBoundedPotential b) :
    (globalMixedMass (fun _ => α) (fun _ => b) (fun _ => hb)).toReal =
      slotIntegral w (fun _ => α) :=
  globalMixedMass_toReal_eq_slotIntegral_of_isBoundedPotential w (fun _ => hb) (fun _ => hbb)

end Mass

/-! ### (2) A pseudoeffective slot against nef slots -/

section Pseudoeffective

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

open MixedMassClassInvariance IntegrationCurrent TopDegreeDensity

/-- **Slot integrals are affine in one slot**:
`∫ ⋯ ∧ (a + c b) ∧ ⋯ = ∫ ⋯ ∧ a ∧ ⋯ + c ∫ ⋯ ∧ b ∧ ⋯`. -/
theorem slotIntegral_update_add_smul (w : KahlerBackground N M)
    (θ : Fin N → ClosedRealOneOneForm N M) (j : Fin N) (a b : ClosedRealOneOneForm N M) (c : ℝ) :
    slotIntegral w (Function.update θ j (a + c • b)) =
      slotIntegral w (Function.update θ j a) + c * slotIntegral w (Function.update θ j b) := by
  have hpt : ∀ x, topRatio w.form.val (slotForm (Function.update θ j (a + c • b))) x =
      topRatio w.form.val (slotForm (Function.update θ j a)) x +
        c * topRatio w.form.val (slotForm (Function.update θ j b)) x := by
    intro x
    simp only [topRatio, chartRatio]
    rw [topDensity_slotForm_coeff, topDensity_slotForm_coeff, topDensity_slotForm_coeff,
      update_coeff, update_coeff, update_coeff, ← MongeAmpere.actualMixedTopDensityMultilinear_apply,
      ← MongeAmpere.actualMixedTopDensityMultilinear_apply,
      ← MongeAmpere.actualMixedTopDensityMultilinear_apply, ClosedRealOneOneForm.coeff_add,
      ClosedRealOneOneForm.coeff_smul, MultilinearMap.map_update_add,
      MultilinearMap.map_update_smul, smul_eq_mul, add_div, mul_div_assoc]
  rw [slotIntegral, integral_congr_ae (Eventually.of_forall hpt),
    integral_add (NefMixedMass.integrable_topRatio w _)
      ((NefMixedMass.integrable_topRatio w _).const_mul c),
    integral_const_mul]
  rfl

/-- A `θ`-psh function on a compact manifold is bounded above: it is more singular than `0`. -/
theorem moreSingularOn_zero {θ : SmoothRealForm N M 2} {u : M → EReal}
    (hu : ThetaPlurisubharmonic θ u) : MoreSingularOn u (fun _ => ((0 : ℝ) : EReal)) univ := by
  rcases isEmpty_or_nonempty M with hM | hM
  · exact ⟨0, fun x => isEmptyElim x⟩
  obtain ⟨y, -, hmax⟩ := (hu.quasiPlurisubharmonic.upperSemicontinuous.upperSemicontinuousOn
    univ).exists_isMaxOn univ_nonempty isCompact_univ
  refine ⟨(u y).toReal, fun x _ => ?_⟩
  rw [EReal.coe_zero, zero_add]
  exact (hmax (mem_univ x)).trans (EReal.le_coe_toReal (hu.quasiPlurisubharmonic.ne_top y))

/-- **A pseudoeffective slot against semipositive slots.** If the slot `j` carries a
`θ_j`-psh potential and every other slot is semipositive, then `∫ θ₀ ∧ ⋯ ∧ θ_{N-1} ≥ 0`.

Choose `A > 0` with `θ_j + Aω` semipositive. In the classes `θ_j + Aω` the potential `u` is more
singular than `0`, so its mixed mass is at most that of `0`, the slot integral
(`globalMixedMass_mono_of_isThetaPshPotential`). Both sides are affine in `A` with the same slope
`∫ ⋯ ∧ ω ∧ ⋯` (one-slot linearity of the measure and of the slot integral), so the mixed mass of
`u` in the class `θ_j` is at most `∫ θ₀ ∧ ⋯ ∧ θ_{N-1}`, which is therefore `≥ 0`. -/
theorem slotIntegral_nonneg_of_pseudoeffective_of_semipositive (w : KahlerBackground N M)
    {Θ : Fin N → ClosedRealOneOneForm N M} (j : Fin N) {u : M → EReal}
    (hu : IsThetaPshPotential (Θ j).val u) (hsemi : ∀ i, i ≠ j → (Θ i).val.IsSemipositive) :
    0 ≤ slotIntegral w Θ := by
  classical
  obtain ⟨A, hA, hAsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul w (Θ j)
  set Θ' := Function.update Θ j (Θ j + A • w.form) with hΘ'
  set v : Fin N → M → EReal := Function.update (fun _ _ => (0 : EReal)) j u with hv
  have hsemi' : ∀ i, (Θ' i).val.IsSemipositive := by
    intro i
    by_cases hij : i = j
    · subst hij; simpa [hΘ'] using hAsemi
    · simpa [hΘ', Function.update_of_ne hij] using hsemi i hij
  have hωsemi : ∀ i, (Function.update Θ j w.form i).val.IsSemipositive := by
    intro i
    by_cases hij : i = j
    · subst hij; simpa using w.isSemipositive
    · simpa [Function.update_of_ne hij] using hsemi i hij
  have hvpot : ∀ i, IsThetaPshPotential (Θ' i).val (v i) := by
    intro i
    by_cases hij : i = j
    · subst hij
      simp only [hΘ', hv, Function.update_self]
      exact ⟨NefBoundedMixedMass.thetaPlurisubharmonic_add_of_isSemipositive hu.1
        (NefBoundedMixedMass.isSemipositive_smul w.isSemipositive hA.le), hu.2⟩
    · simp only [hv, Function.update_of_ne hij]
      exact (LocalPotentials.isThetaPshPotential_zero_iff _).mpr (hsemi' i)
  have h0pot : ∀ i, IsThetaPshPotential (Θ' i).val (fun _ => (0 : EReal)) :=
    fun i => (LocalPotentials.isThetaPshPotential_zero_iff _).mpr (hsemi' i)
  have hmono := GlobalMixedMassMonotone.globalMixedMass_mono_of_isThetaPshPotential w hvpot h0pot
    (fun i => by
      by_cases hij : i = j
      · subst hij; simpa [hv] using moreSingularOn_zero hu.1
      · simp only [hv, Function.update_of_ne hij]
        exact ⟨0, fun x _ => by simp⟩)
  have hvΘ : ∀ i, ThetaPlurisubharmonic (Θ i).val (v i) := by
    intro i
    by_cases hij : i = j
    · subst hij; simpa [hv] using hu.1
    · simp only [hv, Function.update_of_ne hij]
      exact (LocalPotentials.isThetaPshPotential_zero_iff _).mpr (hsemi i hij) |>.1
  have hv0 : Function.update v j (fun _ => (0 : EReal)) = fun _ _ => (0 : EReal) := by
    funext i
    by_cases hij : i = j
    · subst hij; simp
    · simp [hv, Function.update_of_ne hij]
  have hω0 : ∀ i, ThetaPlurisubharmonic (Function.update Θ j w.form i).val
      (Function.update v j (fun _ => (0 : EReal)) i) := by
    intro i
    rw [hv0]
    exact ((LocalPotentials.isThetaPshPotential_zero_iff _).mpr (hωsemi i)).1
  have hlin := NefBoundedMixedMass.globalMixedMeasure_update_add_smul_eq j hA hvΘ
    (by simpa [hv] using hu) (fun i => (hvpot i).1) hω0
  -- the three masses as real numbers
  have hfin1 := globalMixedMeasure_apply_lt_top w hvΘ univ
  have hfin2 := globalMixedMeasure_apply_lt_top w hω0 univ
  have hfin3 := globalMixedMeasure_apply_lt_top w (fun i => (h0pot i).1) univ
  have hmass : (globalMixedMass Θ' v fun i => (hvpot i).1).toReal =
      (globalMixedMass Θ v hvΘ).toReal + A * (globalMixedMass (Function.update Θ j w.form)
        (Function.update v j fun _ => (0 : EReal)) hω0).toReal := by
    simp only [globalMixedMass]
    rw [hlin, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      ENNReal.toReal_add hfin1.ne (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin2.ne),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hA.le]
  have hω_eq : (globalMixedMass (Function.update Θ j w.form)
      (Function.update v j fun _ => (0 : EReal)) hω0).toReal =
      slotIntegral w (Function.update Θ j w.form) := by
    have h0' : ∀ i, ThetaPlurisubharmonic (Function.update Θ j w.form i).val
        (fun _ => (0 : EReal)) := fun i =>
      ((LocalPotentials.isThetaPshPotential_zero_iff _).mpr (hωsemi i)).1
    rw [globalMixedMass, UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple hv0 hω0 h0',
      ← measureReal_def]
    exact globalMixedMeasure_real_univ_eq_integral w _ h0'
  have h0_eq : (globalMixedMass Θ' (fun _ _ => (0 : EReal)) fun i => (h0pot i).1).toReal =
      slotIntegral w Θ' := by
    rw [globalMixedMass, ← measureReal_def]
    exact globalMixedMeasure_real_univ_eq_integral w _ _
  have hslot : slotIntegral w Θ' = slotIntegral w Θ + A * slotIntegral w (Function.update Θ j w.form) := by
    have h := slotIntegral_update_add_smul w Θ j (Θ j) w.form A
    rwa [Function.update_eq_self] at h
  have hle : (globalMixedMass Θ' v fun i => (hvpot i).1).toReal ≤
      (globalMixedMass Θ' (fun _ _ => (0 : EReal)) fun i => (h0pot i).1).toReal :=
    ENNReal.toReal_mono hfin3.ne hmono
  rw [hmass, hω_eq, h0_eq, hslot] at hle
  have hnn : 0 ≤ (globalMixedMass Θ v hvΘ).toReal := ENNReal.toReal_nonneg
  linarith

/-- The `ddᶜ` of the zero function is the zero form. -/
theorem ddcClosedForm_zero (h : ChartSmooth (n := N) (fun _ : M => (0 : ℝ))) :
    ManifoldTubePositivity.ddcClosedForm (fun _ : M => (0 : ℝ)) h = 0 := by
  refine ClosedRealOneOneForm.ext fun e z => ?_
  rw [ManifoldTubePositivity.ddcClosedForm_coeff, FirstPass.smoothDDC_zero z]
  rfl

/-- **`pc:domination-intersection` (2), as stated**: on a compact Kähler manifold, if the class of
the slot `j` is pseudoeffective and the classes of all other slots are nef, then
`∫ θ₀ ∧ ⋯ ∧ θ_{N-1} ≥ 0`. For `t > 0` each nef slot `θᵢ + tω` has a semipositive representative
`θᵢ + tω + ddᶜfᵢ`; the slot integral does not see the `ddᶜfᵢ`
(`slotIntegral_add_ddc`), the previous theorem applies, and `t → 0`. -/
theorem slotIntegral_nonneg_of_pseudoeffective (w : KahlerBackground N M)
    {θ : Fin N → ClosedRealOneOneForm N M} (j : Fin N) (hP : PseudoeffectiveViaPotentials (θ j))
    (hnef : ∀ i, i ≠ j → NefWithRespectTo w (θ i)) : 0 ≤ slotIntegral w θ := by
  classical
  obtain ⟨u, hu⟩ := hP
  set B : Fin N → ClosedRealOneOneForm N M := fun i => if i = j then 0 else w.form with hB
  have hpos : ∀ t : ℝ, 0 < t → 0 ≤ slotIntegral w (fun i => θ i + t • B i) := by
    intro t ht
    have hex : ∀ i, ∃ (f : M → ℝ) (hf : ChartSmooth (n := N) f), i ≠ j →
        (θ i + t • w.form + ManifoldTubePositivity.ddcClosedForm f hf).val.IsSemipositive := by
      intro i
      by_cases hij : i = j
      · exact ⟨fun _ => 0, fun _ => contDiffOn_const, fun h => absurd hij h⟩
      · obtain ⟨f, hf, hs⟩ := exists_isSemipositive_of_nef (hnef i hij) ht
        exact ⟨f, hf, fun _ => hs⟩
    choose f hf hfs using hex
    set F : Fin N → M → ℝ := fun i => if i = j then fun _ => 0 else f i with hF
    have hFs : ∀ i, ChartSmooth (n := N) (F i) := by
      intro i
      by_cases hij : i = j
      · simp only [hF, if_pos hij]; exact fun _ => contDiffOn_const
      · simp only [hF, if_neg hij]; exact hf i
    rw [← slotIntegral_add_ddc w (fun i => θ i + t • B i) F hFs]
    refine slotIntegral_nonneg_of_pseudoeffective_of_semipositive w j (u := u) ?_ ?_
    · have hj : θ j + t • B j + ManifoldTubePositivity.ddcClosedForm (F j) (hFs j) = θ j := by
        have hFj : F j = fun _ => 0 := by simp [hF]
        have hBj : B j = 0 := by simp [hB]
        have e0 : ManifoldTubePositivity.ddcClosedForm (F j) (hFs j) = 0 := by
          refine ClosedRealOneOneForm.ext fun e z => ?_
          rw [ManifoldTubePositivity.ddcClosedForm_coeff, hFj, FirstPass.smoothDDC_zero z]
          rfl
        rw [e0, hBj, smul_zero, add_zero, add_zero]
      simpa only [hj] using hu
    · intro i hij
      have hFi : F i = f i := by simp [hF, hij]
      have hBi : B i = w.form := by simp [hB, hij]
      have e1 : θ i + t • B i + ManifoldTubePositivity.ddcClosedForm (F i) (hFs i) =
          θ i + t • w.form + ManifoldTubePositivity.ddcClosedForm (f i) (hf i) := by
        ext e z
        simp only [ClosedRealOneOneForm.coeff_add, ManifoldTubePositivity.ddcClosedForm_coeff,
          hFi, hBi]
      rw [e1]
      exact hfs i hij
  have hcont := (continuous_slotIntegral_add_smul w θ B).continuousWithinAt
    (s := Ioi (0 : ℝ)) (x := 0)
  have h0 : slotIntegral w (fun i => θ i + (0 : ℝ) • B i) = slotIntegral w θ := by
    simp only [zero_smul, add_zero]
  rw [← h0]
  refine ge_of_tendsto hcont ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hpos t ht

end Pseudoeffective

/-! ### (3) Pullback along a sequence of blowups -/

section Pullback

universe u

variable {N : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel N) X]
  [IsComplexManifold N X] [mX : MeasurableSpace X] [bX : BorelSpace X] [CompactSpace X]

open ModificationMassInvariance BlowupSequences

/-- **Mixed masses are invariant under pullback along a blowup sequence** (Xia SGPT Prop. 2.4.2 for
blowup sequences, mixed form): `∫_Y ⟨⋀ᵢ (π^*θᵢ)_{uᵢ∘π}⟩ = ∫_X ⟨⋀ᵢ (θᵢ)_{uᵢ}⟩`, for any Borel structure
on `Y`. Induction over the sequence, as `diagonalPotentialMass_pullback_of_isBlowupSequence`, from
the one-blowup case `globalMixedMeasure_univ_pullback_of_isBlowupAlong`. -/
theorem globalMixedMeasure_univ_pullback_of_isBlowupSequence {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel N) Y] [IsComplexManifold N Y] {π : Y → X}
    (hπ : IsBlowupSequence N X Y π) (θ : Fin N → ClosedRealOneOneForm N X)
    {v : Fin N → X → EReal} (hv : ∀ i, ThetaPlurisubharmonic (θ i).val (v i)) :
    ∀ [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
      (hv' : ∀ i, ThetaPlurisubharmonic (pullbackTuple hπ.contMDiff θ i).val
        (fun y => v i (π y))),
      globalMixedMeasure (pullbackTuple hπ.contMDiff θ) (fun i y => v i (π y)) hv' univ =
        globalMixedMeasure θ v hv univ := by
  induction hπ with
  | refl =>
      intro mY bY cY hv'
      have hm : mY = mX := bY.measurable_eq.trans bX.measurable_eq.symm
      subst hm
      exact congrArg (fun μ : Measure X => μ univ)
        (globalMixedMeasure_congr_geometricallyEq
          (fun i => SmoothRealForm.pullback_id_geometricallyEq (θ i).val) hv' hv)
  | @step Y' Z' _ _ _ _ _ _ f C g hf hg ih =>
      intro mZ bZ cZ hv'
      let : MeasurableSpace Y' := borel Y'
      have : BorelSpace Y' := ⟨rfl⟩
      have hYc := StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hf
      have : CompactSpace Y' := hYc.1
      have hw : ∀ i, ThetaPlurisubharmonic (pullbackTuple hf.contMDiff θ i).val
          (fun y => v i (f y)) := fun i =>
        GlobalPotentialPullback.thetaPlurisubharmonic_comp hf.contMDiff (hv i)
      have hw' : ∀ i, ThetaPlurisubharmonic
          (pullbackTuple hg.contMDiff (pullbackTuple hf.contMDiff θ) i).val
          (fun z => v i (f (g z))) := fun i =>
        GlobalPotentialPullback.thetaPlurisubharmonic_comp hg.contMDiff (hw i)
      calc globalMixedMeasure _ _ hv' univ
          = globalMixedMeasure (pullbackTuple hg.contMDiff (pullbackTuple hf.contMDiff θ))
              (fun i z => v i (f (g z))) hw' univ :=
            congrArg (fun μ : Measure Z' => μ univ)
              (globalMixedMeasure_congr_geometricallyEq (fun i =>
                SmoothRealForm.pullback_comp_geometricallyEq hf.contMDiff hg.contMDiff (θ i).val)
                hv' hw')
        _ = globalMixedMeasure (pullbackTuple hf.contMDiff θ) (fun i y => v i (f y)) hw univ :=
            globalMixedMeasure_univ_pullback_of_isBlowupAlong hg hw hw'
        _ = globalMixedMeasure θ v hv univ := ih hw

/-- Pullback of closed real `(1,1)`-forms is linear. -/
theorem pullback_add_smul {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
    [IsComplexManifold N Y] {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel N) ∞ π)
    (a b : ClosedRealOneOneForm N X) (c : ℝ) :
    ClosedRealOneOneForm.pullback hπ (a + c • b) =
      ClosedRealOneOneForm.pullback hπ a + c • ClosedRealOneOneForm.pullback hπ b :=
  Subtype.ext (by
    rw [ClosedRealOneOneForm.pullback_val]
    exact (ProductTestForms.pullback_add hπ a.val (c • b.val)).trans
      (congrArg _ (ProductTestForms.pullback_smul hπ c b.val)))

/-- **`pc:domination-intersection` (3), as stated: intersection numbers are invariant under
pullback along a finite sequence of blowups with smooth centres.** For compact Kähler manifolds `X`
and `Y` (backgrounds `w`, `w'`), a blowup sequence `π : Y → X` and smooth closed real `(1,1)`-forms
`θᵢ` on `X`, `∫_Y π^*θ₀ ∧ ⋯ ∧ π^*θ_{N-1} = ∫_X θ₀ ∧ ⋯ ∧ θ_{N-1}`.

With `A > 0` such that every `θᵢ + Aω` is semipositive, `θᵢ = (θᵢ + Aω) + (-A)ω`; the slot
integrals expand multilinearly (`slotIntegral_add_smul_eq_sum`) into slot integrals of semipositive
forms, which are mixed masses of the potentials `0` (`globalMixedMeasure_real_univ_eq_integral`), and
those are invariant under pullback (`globalMixedMeasure_univ_pullback_of_isBlowupSequence`). -/
theorem slotIntegral_pullback_of_isBlowupSequence {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel N) Y] [IsComplexManifold N Y] [MeasurableSpace Y] [BorelSpace Y]
    [CompactSpace Y] {π : Y → X} (hπ : IsBlowupSequence N X Y π) (w : KahlerBackground N X)
    (w' : KahlerBackground N Y) (θ : Fin N → ClosedRealOneOneForm N X) :
    slotIntegral w' (fun i => ClosedRealOneOneForm.pullback hπ.contMDiff (θ i)) =
      slotIntegral w θ := by
  classical
  obtain ⟨A, hA, hsemi⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul w θ
  set P : Fin N → ClosedRealOneOneForm N X := fun i => θ i + A • w.form with hP
  have hθP : θ = fun i => P i + (-A) • w.form := by
    funext i
    simp only [hP, add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]
  have hθP' : (fun i => ClosedRealOneOneForm.pullback hπ.contMDiff (θ i)) = fun i =>
      ClosedRealOneOneForm.pullback hπ.contMDiff (P i) +
        (-A) • ClosedRealOneOneForm.pullback hπ.contMDiff w.form := by
    funext i
    rw [← pullback_add_smul, hP]
    congr 1
    simp only [add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]
  -- each semipositive piece is pullback invariant
  have hpiece : ∀ s : Finset (Fin N),
      slotIntegral w' (s.piecewise (fun i => ClosedRealOneOneForm.pullback hπ.contMDiff (P i))
        fun _ => ClosedRealOneOneForm.pullback hπ.contMDiff w.form) =
      slotIntegral w (s.piecewise P fun _ => w.form) := by
    intro s
    have hsX : ∀ i, ((s.piecewise P fun _ => w.form) i).val.IsSemipositive := by
      intro i
      by_cases hi : i ∈ s
      · rw [Finset.piecewise_eq_of_mem _ _ _ hi]; exact hsemi i
      · rw [Finset.piecewise_eq_of_notMem _ _ _ hi]; exact w.isSemipositive
    have h0X : ∀ i, ThetaPlurisubharmonic ((s.piecewise P fun _ => w.form) i).val
        (fun _ => (0 : EReal)) := fun i =>
      ((LocalPotentials.isThetaPshPotential_zero_iff _).mpr (hsX i)).1
    have hpb : (s.piecewise (fun i => ClosedRealOneOneForm.pullback hπ.contMDiff (P i))
        fun _ => ClosedRealOneOneForm.pullback hπ.contMDiff w.form) =
        pullbackTuple hπ.contMDiff (s.piecewise P fun _ => w.form) := by
      funext i
      by_cases hi : i ∈ s
      · simp only [pullbackTuple, Finset.piecewise_eq_of_mem _ _ _ hi]
      · simp only [pullbackTuple, Finset.piecewise_eq_of_notMem _ _ _ hi]
    have h0Y : ∀ i, ThetaPlurisubharmonic (pullbackTuple hπ.contMDiff
        (s.piecewise P fun _ => w.form) i).val (fun y => (fun _ => (0 : EReal)) (π y)) :=
      fun i => GlobalPotentialPullback.thetaPlurisubharmonic_comp hπ.contMDiff (h0X i)
    rw [hpb, slotIntegral, slotIntegral,
      ← MixedMassClassInvariance.globalMixedMeasure_real_univ_eq_integral w' _ h0Y,
      ← MixedMassClassInvariance.globalMixedMeasure_real_univ_eq_integral w _ h0X,
      measureReal_def, measureReal_def,
      globalMixedMeasure_univ_pullback_of_isBlowupSequence hπ _ h0X h0Y]
  rw [hθP', hθP, slotIntegral_add_smul_eq_sum, slotIntegral_add_smul_eq_sum]
  exact Finset.sum_congr rfl fun s _ => by rw [hpiece]

end Pullback

end

end SGPT.Foundations.Analysis.Pending.DominationIntersectionNumbers
