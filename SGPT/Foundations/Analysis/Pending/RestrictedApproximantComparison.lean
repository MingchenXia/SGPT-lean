import SGPT.Foundations.Analysis.Pending.TraceFreeLimit
import SGPT.Foundations.Analysis.Pending.GlobalMultilinearExpansion
import SGPT.Foundations.Analysis.Pending.UniformPerturbedKahlerLowerBound

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Route F, `F-b` step P5: comparing the restricted approximant masses with `h_ε`

Plan §8 of `scratch/tn23-envelopes-qea-plan-0117.md` (human decision I-0796, D0 = route F).  On a
compact complex manifold `Z` of dimension `k` with a Kähler form `ω` and a closed real
`(1,1)`-form `γ` (in the application: `Z = V`, `γ = θ|_V`), let `v` be a `(γ + εω)`-psh potential
(`v = V_{θ+εω}|_V`) and `Φ` a `(γ + ε'ω)`-psh potential (`Φ = Φ_q|_V`, the restricted Demailly
approximant) with `a·v ≤ Φ + C` for some `a ≥ 1` (`a = (q+1)/q`, from P4b).  Then

    ∫(γ + εω)_v^k ≤ ∫(γ + ε'ω)_Φ^k + t·K,     t = aε + (a - 1)A,

with `A ≥ 0` (`γ ≤ Aω`) and `K < ∞` depending only on `(Z, ω, γ)`
(`exists_diagonalPotentialMass_le_of_smul_moreSingular`).  Proof, in the common class
`B = γ + (ε' + t)ω`:

* homogeneity `∫(a·β)_{a·v}^k = a^k ∫β_v^k` (`diagonalPotentialMass_smul`, from the multilinear
  expansion `GlobalMultilinearExpansion.globalMixedMeasure_diagonal_sumPot`), and `a^k ≥ 1`;
* background monotonicity: `B - a(γ + εω) = ε'ω + (a - 1)(Aω - γ) ≥ 0`;
* monotonicity in the singularity type (`a·v ≤ Φ + C`) in the class `B`;
* a UNIFORM Lipschitz bound for the mass in the background
  (`exists_diagonalPotentialMass_add_smul_le_uniform`, the upgrade of
  `TraceFreeLimit.exists_diagonalPotentialMass_add_smul_le`): the slot terms `(ω, 0)`, `(θ + ε ω, u)`
  are bounded, by background monotonicity and mixed monotonicity in the potentials, by the
  masses of the smooth tuples `(ω, 0)`, `(Cω, 0)` — independent of `θ` and `u` as long as
  `θ + ω ≤ Cω`.

Sorry-free.
-/

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal

namespace SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison

noncomputable section

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus DiagonalMass
  GlobalNonPluripolar GlobalSlotLinear GlobalDiagonalScaling AmbientMassBackgroundMonotone
  TraceFreeLimit

variable {k : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]
  [IsComplexManifold k Z]

/-- A positive multiple of a `θ`-psh potential is an `(c • θ)`-psh potential. -/
theorem isThetaPshPotential_smul {θ : ClosedRealOneOneForm k Z} {u : Z → EReal}
    (hu : IsThetaPshPotential θ.val u) {c : ℝ} (hc : 0 < c) :
    IsThetaPshPotential (c • θ).val (fun x => (c : EReal) * u x) := by
  refine ⟨GlobalMultilinearExpansion.thetaPlurisubharmonic_smul hc hu.1, fun x U hU hxU => ?_⟩
  obtain ⟨y, hyU, hy⟩ := hu.2 x U hU hxU
  refine ⟨y, hyU, ?_⟩
  show (c : EReal) * u y ≠ ⊥
  induction h : u y using EReal.rec with
  | bot => exact absurd h hy
  | top => rw [EReal.coe_mul_top_of_pos hc]; exact top_ne_bot
  | coe r => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _

variable [MeasurableSpace Z] [BorelSpace Z] [CompactSpace Z]

/-- **Homogeneity of the non-pluripolar mass**: `∫(c θ)_{c u}^k = c^k ∫θ_u^k` for `c > 0`. -/
theorem diagonalPotentialMass_smul {θ : ClosedRealOneOneForm k Z} {u : Z → EReal}
    (hu : IsThetaPshPotential θ.val u) {c : ℝ} (hc : 0 < c)
    (hcu : IsThetaPshPotential (c • θ).val (fun x => (c : EReal) * u x)) :
    diagonalPotentialMass (c • θ) (fun x => (c : EReal) * u x) hcu =
      ENNReal.ofReal (c ^ k) * diagonalPotentialMass θ u hu := by
  classical
  have hq : IsGlobalQuasiPshPotential (n := k) u := ⟨hu.1.quasiPlurisubharmonic, hu.2⟩
  have h := GlobalMultilinearExpansion.globalMixedMeasure_diagonal_sumPot (ι := Unit)
    (T := {()}) (Finset.singleton_nonempty _) (w := fun _ => c) (fun _ => hc)
    (α := fun _ => θ) (f := fun _ => u) (fun _ => hu.1) (fun _ => hq)
  have hform : GlobalMultilinearExpansion.sumForm ({()} : Finset Unit) (fun _ => c)
      (fun _ => θ) = c • θ := GlobalMultilinearExpansion.sumForm_singleton _ _ _
  have hpot : GlobalMultilinearExpansion.sumPot ({()} : Finset Unit) (fun _ => c)
      (fun _ => u) = fun x => (c : EReal) * u x :=
    GlobalMultilinearExpansion.sumPot_singleton _ _ _
  have hpi : Fintype.piFinset (fun _ : Fin k => ({()} : Finset Unit)) = {fun _ => ()} :=
    Fintype.piFinset_singleton _
  rw [hpi, Finset.sum_singleton, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  have h' := congrArg (fun μ : Measure Z => μ univ) h
  simp only [Measure.smul_apply, smul_eq_mul] at h'
  unfold diagonalPotentialMass diagonalPotentialMeasure
  rw [globalMixedMeasure_congr_tuples (θ' := fun _ => GlobalMultilinearExpansion.sumForm
      ({()} : Finset Unit) (fun _ => c) (fun _ => θ))
    (u' := fun _ => GlobalMultilinearExpansion.sumPot ({()} : Finset Unit) (fun _ => c)
      (fun _ => u)) (by rw [hform]) (by rw [hpot]) _
      (fun _ => GlobalMultilinearExpansion.thetaPlurisubharmonic_sumPot
        (Finset.singleton_nonempty _) (fun _ => hc) (fun _ => hu.1)), h']

/-- **A uniform Lipschitz bound for the mass in the background.**  For `C ≥ 0` there is `K < ∞`
such that for every closed real `(1,1)`-form `θ` with `θ + ω ≤ Cω`, every `θ`-psh potential `u` and
`0 < ε ≤ 1`, `∫(θ + εω)_u^k ≤ ∫θ_u^k + εK`.  The constant is the sum of the masses of the smooth
tuples `(ω, 0)` in slot `i`, `(Cω, 0)` elsewhere: upgrade of
`TraceFreeLimit.exists_diagonalPotentialMass_add_smul_le`, whose constant depends on `u`. -/
theorem exists_diagonalPotentialMass_add_smul_le_uniform (omega : KahlerBackground k Z)
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ θ : ClosedRealOneOneForm k Z,
      (C • omega.form - (θ + omega.form)).val.IsSemipositive →
      ∀ {u : Z → EReal} (hu : IsThetaPshPotential θ.val u) (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ hu' : IsThetaPshPotential (θ + ε • omega.form).val u,
        diagonalPotentialMass (θ + ε • omega.form) u hu' ≤
          diagonalPotentialMass θ u hu + ENNReal.ofReal ε * K := by
  classical
  have h0ω : IsThetaPshPotential omega.form.val (fun _ : Z => (0 : EReal)) :=
    ⟨(LocalPotentials.thetaPlurisubharmonic_zero_iff _).mpr omega.isSemipositive,
      fun x _ _ hx => ⟨x, hx, EReal.zero_ne_bot⟩⟩
  have hCsemi : (C • omega.form).val.IsSemipositive :=
    KahlerDomination.isSemipositive_smul omega.isSemipositive hC
  have h0C : IsThetaPshPotential (C • omega.form).val (fun _ : Z => (0 : EReal)) :=
    ⟨(LocalPotentials.thetaPlurisubharmonic_zero_iff _).mpr hCsemi,
      fun x _ _ hx => ⟨x, hx, EReal.zero_ne_bot⟩⟩
  -- the reference tuples `R_i`: `(ω, 0)` in slot `i`, `(Cω, 0)` elsewhere
  set R : Fin k → Fin k → ClosedRealOneOneForm k Z :=
    fun i => Function.update (fun _ => C • omega.form) i omega.form with hR
  have hRpot : ∀ i j, IsThetaPshPotential (R i j).val (fun _ : Z => (0 : EReal)) := by
    intro i j
    by_cases hj : j = i
    · subst hj; simpa [hR] using h0ω
    · simpa [hR, Function.update_of_ne hj] using h0C
  set K : ℝ≥0∞ := ∑ i, globalMixedMeasure (R i) (fun _ _ => (0 : EReal))
    (fun j => (hRpot i j).1) univ with hK
  refine ⟨K, ?_, fun θ hθC u hu ε hε hε1 hu' => ?_⟩
  · exact ENNReal.sum_lt_top.2 fun i _ => globalMixedMeasure_apply_lt_top omega _ univ
  -- `u` is bounded above, hence more singular than `0`
  have hu0 : MoreSingularOn u (fun _ : Z => (0 : EReal)) univ := by
    rcases isEmpty_or_nonempty Z with hZ | hZ
    · exact ⟨0, fun x _ => isEmptyElim x⟩
    · obtain ⟨C₀, hC₀⟩ := hu.exists_global_upper_bound
      exact ⟨C₀, fun x _ => by simpa using hC₀ x⟩
  -- the tuples `T s`: `θ + εω` in the slots of `s`, `θ` elsewhere, potential `u` everywhere
  set T : Finset (Fin k) → Fin k → ClosedRealOneOneForm k Z :=
    fun s i => if i ∈ s then θ + ε • omega.form else θ with hT
  have hTpot : ∀ s i, IsThetaPshPotential (T s i).val u := by
    intro s i
    by_cases hi : i ∈ s
    · simpa [hT, hi] using hu'
    · simpa [hT, hi] using hu
  -- `Cω - T s j` is semipositive
  have hCT : ∀ s j, (C • omega.form - T s j).val.IsSemipositive := by
    intro s j
    by_cases hj : j ∈ s
    · have h1 : C • omega.form - (θ + ε • omega.form) =
          (C • omega.form - (θ + omega.form)) + (1 - ε) • omega.form := by module
      simp only [hT, hj, if_true, h1]
      exact UniformPerturbedKahlerLowerBound.isSemipositive_add hθC
        (KahlerDomination.isSemipositive_smul omega.isSemipositive (by linarith))
    · have h1 : C • omega.form - θ = (C • omega.form - (θ + omega.form)) + (1 : ℝ) • omega.form := by
        module
      simp only [hT, hj, if_false, h1]
      exact UniformPerturbedKahlerLowerBound.isSemipositive_add hθC
        (KahlerDomination.isSemipositive_smul omega.isSemipositive zero_le_one)
  have key : ∀ s : Finset (Fin k),
      globalMixedMeasure (T s) (fun _ => u) (fun i => (hTpot s i).1) univ ≤
        globalMixedMeasure (T ∅) (fun _ => u) (fun i => (hTpot ∅ i).1) univ +
          ENNReal.ofReal ε * ∑ i ∈ s, globalMixedMeasure (R i) (fun _ _ => (0 : EReal))
            (fun j => (hRpot i j).1) univ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i₀ s hi₀ ih =>
        -- slot linearity in slot `i₀`: `(θ + εω, u) = 1·(θ, u) + ε·(ω, 0)`
        have hθi₀ : T (insert i₀ s) i₀ = (1 : ℝ) • θ + ε • omega.form := by simp [hT]
        have hrest : Function.update (T (insert i₀ s)) i₀ θ = T s := by
          funext j
          by_cases hj : j = i₀
          · subst hj; simp [hT, hi₀]
          · simp [hT, Finset.mem_insert, hj]
        have hcomb : Function.update (fun _ : Fin k => u) i₀
            (fun p => ((1 : ℝ) : EReal) * u p + ((ε : ℝ) : EReal) * (0 : EReal)) =
            fun _ => u := by
          funext j
          by_cases hj : j = i₀
          · subst hj; funext p; simp
          · simp [Function.update_of_ne hj]
        have hc : ∀ i, ThetaPlurisubharmonic (T (insert i₀ s) i).val
            (Function.update (fun _ : Fin k => u) i₀
              (fun p => ((1 : ℝ) : EReal) * u p + ((ε : ℝ) : EReal) * (0 : EReal)) i) := by
          rw [hcomb]; exact fun i => (hTpot (insert i₀ s) i).1
        have ha : ∀ i, ThetaPlurisubharmonic (Function.update (T (insert i₀ s)) i₀ θ i).val
            (Function.update (fun _ : Fin k => u) i₀ u i) := by
          rw [hrest, Function.update_eq_self]; exact fun i => (hTpot s i).1
        have hbpot : ∀ i, IsThetaPshPotential
            (Function.update (T (insert i₀ s)) i₀ omega.form i).val
            (Function.update (fun _ : Fin k => u) i₀ (fun _ => (0 : EReal)) i) := by
          intro i
          by_cases hi : i = i₀
          · subst hi; simpa using h0ω
          · simpa [Function.update_of_ne hi] using hTpot (insert i₀ s) i
        have hb : ∀ i, ThetaPlurisubharmonic
            (Function.update (T (insert i₀ s)) i₀ omega.form i).val
            (Function.update (fun _ : Fin k => u) i₀ (fun _ => (0 : EReal)) i) :=
          fun i => (hbpot i).1
        have hkey := globalMixedMeasure_update_add_smul (θ := T (insert i₀ s)) i₀ (α := θ)
          (β := omega.form) (s := 1) (r := ε) one_pos hε hθi₀ (x := fun _ => u) (a := u)
          (b := fun _ => (0 : EReal)) hc ha hb
          (globalMixedMeasure_pole_null_of_nondegenerate hb hu) (by simp)
        -- the `(ω, 0)`-term is at most `K_{i₀}`: background monotonicity, then `u ≤ 0 + C₀`
        set B : Fin k → ClosedRealOneOneForm k Z :=
          Function.update (T (insert i₀ s)) i₀ omega.form with hB
        set σ : Fin k → ClosedRealOneOneForm k Z :=
          Function.update (fun j => C • omega.form - T (insert i₀ s) j) i₀ 0 with hσdef
        have hσ : ∀ j, (σ j).val.IsSemipositive := by
          intro j
          by_cases hj : j = i₀
          · subst hj
            simpa [hσdef] using
              KahlerDomination.isSemipositive_smul omega.isSemipositive (le_refl (0 : ℝ))
          · simp only [hσdef, Function.update_of_ne hj]
            exact hCT (insert i₀ s) j
        have hBσ : (fun j => B j + σ j) = R i₀ := by
          funext j
          by_cases hj : j = i₀
          · subst hj; simp [hB, hσdef, hR]
          · simp [hB, hσdef, hR, Function.update_of_ne hj]
        have hRu : ∀ j, IsThetaPshPotential (R i₀ j).val
            (Function.update (fun _ : Fin k => u) i₀ (fun _ => (0 : EReal)) j) := by
          intro j
          rw [← congrFun hBσ j]
          exact LocalPotentials.isThetaPshPotential_add_of_semipositive (hbpot j) (hσ j)
        have hmonoB := globalMixedMeasure_le_of_add_semipositive hσ hbpot
          (fun j => by rw [congrFun hBσ j]; exact (hRu j).1)
        have hBle : globalMixedMeasure B
            (Function.update (fun _ : Fin k => u) i₀ (fun _ => (0 : EReal))) hb univ ≤
            globalMixedMeasure (R i₀) (fun _ _ => (0 : EReal)) (fun j => (hRpot i₀ j).1) univ := by
          calc globalMixedMeasure B
                (Function.update (fun _ : Fin k => u) i₀ (fun _ => (0 : EReal))) hb univ
              ≤ globalMixedMeasure (fun j => B j + σ j)
                  (Function.update (fun _ : Fin k => u) i₀ (fun _ => (0 : EReal)))
                  (fun j => by rw [congrFun hBσ j]; exact (hRu j).1) univ :=
                hmonoB univ
            _ = globalMixedMeasure (R i₀)
                  (Function.update (fun _ : Fin k => u) i₀ (fun _ => (0 : EReal)))
                  (fun j => (hRu j).1) univ := by
                rw [globalMixedMeasure_congr_tuples hBσ rfl _ (fun j => (hRu j).1)]
            _ ≤ globalMixedMeasure (R i₀) (fun _ _ => (0 : EReal))
                  (fun j => (hRpot i₀ j).1) univ := by
                refine MassFromBoundedDifference.globalMixedMeasure_univ_le_of_moreSingular
                  hRu (hRpot i₀) (fun j => ?_)
                  fun _ _ ha hb _ ht hab hba =>
                    (MixedMassBoundedDifference.globalMixedMeasure_univ_eq_of_le_add omega ha hb
                      ht hab hba).le
                by_cases hj : j = i₀
                · subst hj
                  exact ⟨0, fun x _ => by simp⟩
                · simpa [Function.update_of_ne hj] using hu0
        -- assemble
        have hstep : globalMixedMeasure (T (insert i₀ s)) (fun _ => u)
            (fun i => (hTpot (insert i₀ s) i).1) univ =
            globalMixedMeasure (T s) (fun _ => u) (fun i => (hTpot s i).1) univ +
              ENNReal.ofReal ε * globalMixedMeasure B
                (Function.update (fun _ : Fin k => u) i₀ (fun _ => (0 : EReal))) hb univ := by
          have h1 := congrArg (fun μ : Measure Z => μ univ) hkey
          simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, ENNReal.ofReal_one,
            one_mul] at h1
          rw [globalMixedMeasure_congr_tuples rfl hcomb.symm _ hc, h1,
            globalMixedMeasure_congr_tuples hrest (Function.update_eq_self _ _) ha
              (fun i => (hTpot s i).1)]
        rw [hstep, Finset.sum_insert hi₀, mul_add]
        calc globalMixedMeasure (T s) (fun _ => u) (fun i => (hTpot s i).1) univ +
              ENNReal.ofReal ε * globalMixedMeasure B
                (Function.update (fun _ : Fin k => u) i₀ (fun _ => (0 : EReal))) hb univ
            ≤ (globalMixedMeasure (T ∅) (fun _ => u) (fun i => (hTpot ∅ i).1) univ +
                ENNReal.ofReal ε * ∑ i ∈ s, globalMixedMeasure (R i) (fun _ _ => (0 : EReal))
                  (fun j => (hRpot i j).1) univ) +
              ENNReal.ofReal ε * globalMixedMeasure (R i₀) (fun _ _ => (0 : EReal))
                (fun j => (hRpot i₀ j).1) univ :=
              add_le_add ih (by gcongr)
          _ = _ := by ring
  have hempty : T ∅ = fun _ => θ := by funext j; simp [hT]
  have huniv : T Finset.univ = fun _ => θ + ε • omega.form := by funext j; simp [hT]
  have hfin := key Finset.univ
  rw [globalMixedMeasure_congr_tuples huniv rfl _ (fun _ => hu'.1),
    globalMixedMeasure_congr_tuples hempty rfl _ (fun _ => hu.1)] at hfin
  exact hfin

/-- **Route F, `F-b` step P5 (mass comparison).**  There are `A ≥ 0` and `K < ∞`, depending only
on `(Z, ω, γ)`, such that: whenever `a ≥ 1`, `ε > 0`, `0 < ε' ≤ 1`, `t := aε + (a - 1)A ≤ 1`, `v` is a
`(γ + εω)`-psh potential, `Φ` a `(γ + ε'ω)`-psh potential and `a·v ≤ Φ + C`, then
`∫(γ + εω)_v^k ≤ ∫(γ + ε'ω)_Φ^k + tK`. -/
theorem exists_diagonalPotentialMass_le_of_smul_moreSingular (omega : KahlerBackground k Z)
    (γ : ClosedRealOneOneForm k Z) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ a ε ε' : ℝ, 1 ≤ a → 0 < ε → 0 < ε' → ε' ≤ 1 →
      a * ε + (a - 1) * A ≤ 1 → ∀ {v Φ : Z → EReal}
      (hv : IsThetaPshPotential (γ + ε • omega.form).val v)
      (hΦ : IsThetaPshPotential (γ + ε' • omega.form).val Φ),
      MoreSingularOn (fun x => (a : EReal) * v x) Φ univ →
      diagonalPotentialMass (γ + ε • omega.form) v hv ≤
        diagonalPotentialMass (γ + ε' • omega.form) Φ hΦ +
          ENNReal.ofReal (a * ε + (a - 1) * A) * K := by
  obtain ⟨A, hA, hAγ⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omega (-γ)
  obtain ⟨K, hK, hLip⟩ := exists_diagonalPotentialMass_add_smul_le_uniform omega
    (C := A + 2) (by linarith)
  refine ⟨A, hA.le, K, hK, fun a ε ε' ha hε hε' hε'1 ht v Φ hv hΦ hmore => ?_⟩
  set t : ℝ := a * ε + (a - 1) * A with htdef
  have ha0 : 0 < a := by linarith
  have ht0 : 0 < t := by
    have h1 : 0 < a * ε := mul_pos ha0 hε
    have h2 : 0 ≤ (a - 1) * A := mul_nonneg (by linarith) hA.le
    linarith
  -- the common class `B = γ + ε'ω + tω`
  have hΦB : IsThetaPshPotential (γ + ε' • omega.form + t • omega.form).val Φ :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hΦ
      (KahlerDomination.isSemipositive_smul omega.isSemipositive ht0.le)
  have hav := isThetaPshPotential_smul hv ha0
  set D : ClosedRealOneOneForm k Z := ε' • omega.form + (a - 1) • (-γ + A • omega.form) with hD
  have hDsemi : D.val.IsSemipositive :=
    UniformPerturbedKahlerLowerBound.isSemipositive_add
      (KahlerDomination.isSemipositive_smul omega.isSemipositive hε'.le)
      (KahlerDomination.isSemipositive_smul hAγ (by linarith))
  have hBD : a • (γ + ε • omega.form) + (1 : ℝ) • D = γ + ε' • omega.form + t • omega.form := by
    rw [hD, htdef]; module
  have havD : IsThetaPshPotential (a • (γ + ε • omega.form) + (1 : ℝ) • D).val
      (fun x => (a : EReal) * v x) :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hav
      (KahlerDomination.isSemipositive_smul hDsemi zero_le_one)
  have havB : IsThetaPshPotential (γ + ε' • omega.form + t • omega.form).val
      (fun x => (a : EReal) * v x) := by rw [← hBD]; exact havD
  -- step 1: homogeneity, `a^k ≥ 1`
  have h1 : diagonalPotentialMass (γ + ε • omega.form) v hv ≤
      diagonalPotentialMass (a • (γ + ε • omega.form)) (fun x => (a : EReal) * v x) hav := by
    rw [diagonalPotentialMass_smul hv ha0 hav]
    have hak : 1 ≤ ENNReal.ofReal (a ^ k) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (one_le_pow₀ ha)
    calc diagonalPotentialMass (γ + ε • omega.form) v hv
        = 1 * diagonalPotentialMass (γ + ε • omega.form) v hv := (one_mul _).symm
      _ ≤ _ := by gcongr
  -- step 2: background monotonicity `a(γ + εω) ≤ B`
  have h2 : diagonalPotentialMass (a • (γ + ε • omega.form)) (fun x => (a : EReal) * v x) hav ≤
      diagonalPotentialMass (γ + ε' • omega.form + t • omega.form)
        (fun x => (a : EReal) * v x) havB := by
    calc diagonalPotentialMass (a • (γ + ε • omega.form)) (fun x => (a : EReal) * v x) hav
        ≤ diagonalPotentialMass (a • (γ + ε • omega.form) + (1 : ℝ) • D)
            (fun x => (a : EReal) * v x) havD :=
          diagonalPotentialMass_le_add_smul hDsemi one_pos hav havD
      _ = _ := DivisorialDomination.diagonalPotentialMass_congr hBD havD havB
  -- step 3: monotonicity in the singularity type in the class `B`
  have h3 : diagonalPotentialMass (γ + ε' • omega.form + t • omega.form)
        (fun x => (a : EReal) * v x) havB ≤
      diagonalPotentialMass (γ + ε' • omega.form + t • omega.form) Φ hΦB :=
    diagonalPotentialMass_mono_of_kahler omega havB hΦB hmore
  -- step 4: the uniform Lipschitz bound, `θ = γ + ε'ω`, `θ + ω ≤ (A + 2)ω`
  have hθC : ((A + 2) • omega.form - (γ + ε' • omega.form + omega.form)).val.IsSemipositive := by
    have e : (A + 2) • omega.form - (γ + ε' • omega.form + omega.form) =
        (-γ + A • omega.form) + (1 - ε') • omega.form := by module
    rw [e]
    exact UniformPerturbedKahlerLowerBound.isSemipositive_add hAγ
      (KahlerDomination.isSemipositive_smul omega.isSemipositive (by linarith))
  have h4 := hLip (γ + ε' • omega.form) hθC hΦ t ht0 ht hΦB
  exact h1.trans (h2.trans (h3.trans h4))

end

end SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison
