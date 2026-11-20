import SGPT.Foundations.Analysis.Pending.BoucksomResolutionAssembly
import SGPT.Foundations.Analysis.Pending.NefCoreKahlerCurrent
import SGPT.Foundations.Analysis.Pending.CoordinateWedgeFamilyPairing
import SGPT.Foundations.Analysis.Pending.NefBoundedMixedMass
import SGPT.Foundations.Analysis.Pending.DivisorMixedMass
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple
import SGPT.Foundations.Analysis.FirstPass.ThetaPshCompactBounds

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Boucksom 4.8: the resolution step, PROVED from `RelativePrincipalization.exists_factorizationData`

Source: Boucksom, proof of Theorem 4.8 (`bou02-volume:4.8`, the resolution of the singularities of a
current with analytic singularities and its residual nef part, `bou02-volume:2.4`); Copy-4
`lem:residual-nef`.  Blueprint `bou:resolved-nef-part`.  Human decision I-0902 item 3 (F2 = (B)): the
resolution step may use the Hironaka-type named statement
`RelativePrincipalization.exists_factorizationData` AS GIVEN (never widened, never restated).

`resolutionStep` proves `BoucksomResolutionAssembly.ResolutionStep ω` on a compact CONNECTED complex
manifold of dimension `n > 0`.  Given a `β`-psh potential `ψ` of global analytic type and `C` with
`Cω - β ≥ 0`:

* the resolution: TN23's `DominationResidualMass.exists_logResolution_mass` (which calls
  `exists_factorizationData` with `W` a point off the poles of `ψ`) gives a blowup sequence
  `ρ : Y → X`, `Y` compact connected Kähler (`ω'`), a metered effective `ℚ`-divisor `F` with
  `ψ ∘ ρ = ψ_F + b` off `Supp F`, `b` bounded and `(ρ^*β - Θ_F)`-psh, the residual form
  `b_F := ρ^*β - Θ_F` NEF, and `∫ ⟨(b_F)_bⁿ⟩ = ∫ ⟨β_ψⁿ⟩`;
* (2) `∫ ⟨β_ψⁿ⟩ = ∫ ⟨(b_F)_bⁿ⟩ = ∫_Y b_Fⁿ` (bounded potential in a nef class,
  `NefBoundedMixedMass.globalMixedMass_toReal_eq_slotIntegral`);
* (3) for `i ≤ n`, with `m = ρ^*ω`: `∫ b_Fⁱ ∧ mⁿ⁻ⁱ = ∫ ⟨(b_F)_bⁱ ∧ mⁿ⁻ⁱ⟩` (same lemma)
  `= ∫ ⟨(ρ^*β)_{ψ∘ρ}ⁱ ∧ mⁿ⁻ⁱ⟩` (off the divisor, `DivisorMixedMass`)
  `≤ ∫ ⟨(C m)_{ψ∘ρ}ⁱ ∧ mⁿ⁻ⁱ⟩` (the backgrounds grow by `ρ^*(Cω - β) ≥ 0`)
  `≤ ∫ (C m)ⁱ ∧ mⁿ⁻ⁱ` (`ψ ∘ ρ` is more singular than `0`, `MixedMass.globalMixedMass_mono`)
  `= Cⁱ ∫_Y mⁿ = Cⁱ ∫_X ωⁿ` (modification invariance); here `C ≥ 0` is forced by the hypotheses
  (`nonneg_of_isThetaPshPotential`);
* (4) the transfer: a `(b_F - ρ^*γ)`-psh `v` gives the `ρ^*(β - γ)`-psh `v + ψ_F`.

Sorry-free; the Hironaka statement (`RelativePrincipalization.exists_factorizationData`,
proved in place from the canonical resolution invariant) enters only through `exists_logResolution_mass`.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.BoucksomResolutionStep

noncomputable section

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.BlowupSequences
  FirstPass.GlobalAnalyticSingularities FirstPass.HolomorphicIdealSheaves GlobalNonPluripolar
  MixedMass NefMixedMass IntegrationCurrent BoundedGlobalProduct NefBoundedMixedMass
  DivisorMixedMass ResidualNefReduction BoucksomResolutionAssembly AmbientMassBackgroundMonotone
  MixedMassClassInvariance FirstPass.MongeAmpere

/-! ### Algebra of forms -/

section Forms

variable {k n : ℕ} {V M : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V] [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

open scoped Manifold ContDiff in
/-- Pull-back of forms commutes with subtraction. -/
theorem pullback_sub {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a c : ClosedRealOneOneForm n M) :
    ClosedRealOneOneForm.pullback hf (a - c) =
      ClosedRealOneOneForm.pullback hf a - ClosedRealOneOneForm.pullback hf c := by
  have h1 : a - c = a + (-1 : ℝ) • c := by module
  rw [h1, NefCoreKahlerCurrent.pullback_add_smul]
  module

end Forms

/-! ### Mixed slot integrals with scaled slots -/

section Slots

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Scaling the first `i` slots by `C` multiplies the slot integral by `C^{min N i}`. -/
theorem slotIntegral_smul_prefix (w : KahlerBackground N M) (a : ClosedRealOneOneForm N M) (C : ℝ)
    (i : ℕ) :
    slotIntegral w (fun j : Fin N => if (j : ℕ) < i then C • a else a) =
      C ^ (min N i) * slotIntegral w (fun _ => a) := by
  classical
  set S : Finset (Fin N) := Finset.univ.filter fun j : Fin N => (j : ℕ) < i with hS
  have hcard : S.card = min N i := Fin.card_filter_val_lt
  have hpt : ∀ x, topRatio w.form.val
      (slotForm fun j : Fin N => if (j : ℕ) < i then C • a else a) x =
        C ^ (min N i) * topRatio w.form.val (slotForm fun _ => a) x := by
    intro x
    simp only [topRatio, chartRatio]
    rw [MixedMassClassInvariance.topDensity_slotForm_coeff,
      MixedMassClassInvariance.topDensity_slotForm_coeff]
    have h := (actualMixedTopDensityMultilinear (n := N)).map_piecewise_smul (fun _ => C)
      (fun _ => a.val.coeff (complexChartAt (n := N) x) ((complexChartAt (n := N) x).val x)) S
    simp only [actualMixedTopDensityMultilinear_apply, smul_eq_mul, Finset.prod_const,
      hcard] at h
    have hA : actualMixedTopDensity (fun j : Fin N =>
        (if (j : ℕ) < i then C • a else a).val.coeff (complexChartAt (n := N) x)
          ((complexChartAt (n := N) x).val x)) =
        C ^ (min N i) * actualMixedTopDensity (fun _ : Fin N =>
          a.val.coeff (complexChartAt (n := N) x) ((complexChartAt (n := N) x).val x)) := by
      rw [← h]
      congr 1
      funext j
      by_cases hj : (j : ℕ) < i
      · rw [if_pos hj, Finset.piecewise_eq_of_mem _ _ _ (by simp [hS, hj])]
        rfl
      · rw [if_neg hj, Finset.piecewise_eq_of_notMem _ _ _ (by simp [hS, hj])]
    rw [hA, mul_div_assoc]
  rw [slotIntegral, slotIntegral]
  simp_rw [hpt]
  exact integral_const_mul _ _

end Slots

/-! ### `C ≥ 0` -/

section Nonneg

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X] [Nonempty X]

/-- **The constant `C` of the resolution step is nonnegative**: in positive dimension, if `{β}`
carries a `β`-psh potential and `Cω - β ≥ 0`, then `C ≥ 0`.  Otherwise `ψ` would be psh for the zero
form `(C + |C|) ω`, so the mass of `(0, ψ)` would vanish (it is at most that of `(0, 0)`), while one
slot at a time `0 = Cω + |C| ω` gives the lower bound `|C|ⁿ ∫ ωⁿ > 0`. -/
theorem nonneg_of_isThetaPshPotential (hn : 0 < n) (ω : KahlerBackground n X)
    {β : ClosedRealOneOneForm n X} {ψ : X → EReal} (hψ : IsThetaPshPotential β.val ψ) {C : ℝ}
    (hC : (C • ω.form - β).val.IsSemipositive) : 0 ≤ C := by
  classical
  by_contra hneg
  have hneg' : C < 0 := lt_of_not_ge hneg
  set c : ℝ := -C with hcdef
  have hc : 0 < c := by linarith
  have hCeq : C • ω.form = β + (C • ω.form - β) := by abel
  have hψC : IsThetaPshPotential (C • ω.form).val ψ :=
    ⟨by rw [hCeq]; exact thetaPlurisubharmonic_add_of_isSemipositive hψ.1 hC, hψ.2⟩
  have hzero : C • ω.form + c • ω.form = (0 : ℝ) • ω.form := by
    rw [← add_smul, hcdef, add_neg_cancel]
  have hzsemi : (C • ω.form + c • ω.form).val.IsSemipositive := by
    rw [hzero]; exact isSemipositive_smul ω.isSemipositive le_rfl
  have hψ0 : ThetaPlurisubharmonic (C • ω.form + c • ω.form).val ψ :=
    thetaPlurisubharmonic_add_of_isSemipositive hψC.1 (isSemipositive_smul ω.isSemipositive hc.le)
  have hω0 : ThetaPlurisubharmonic ω.form.val (fun _ => (0 : EReal)) :=
    (Pending.LocalPotentials.thetaPlurisubharmonic_zero_iff ω.form).mpr ω.isSemipositive
  -- the families: `(0, ψ)` on `T`, `(ω, 0)` elsewhere
  set fam : Finset (Fin n) → Fin n → ClosedRealOneOneForm n X :=
    fun T i => if i ∈ T then C • ω.form + c • ω.form else ω.form with hfam
  set pots : Finset (Fin n) → Fin n → X → EReal :=
    fun T i => if i ∈ T then ψ else fun _ => (0 : EReal) with hpots
  have hpsh : ∀ T i, ThetaPlurisubharmonic (fam T i).val (pots T i) := by
    intro T i
    by_cases hi : i ∈ T
    · simp only [hfam, hpots, if_pos hi]; exact hψ0
    · simp only [hfam, hpots, if_neg hi]; exact hω0
  set V := globalMixedMeasure (fam ∅) (pots ∅) (hpsh ∅) univ with hVdef
  have key : ∀ T : Finset (Fin n), ENNReal.ofReal c ^ T.card * V ≤
      globalMixedMeasure (fam T) (pots T) (hpsh T) univ := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp [hVdef]
    | insert j T hj ih =>
        set θ := Function.update (fam T) j (C • ω.form) with hθdef
        set u := Function.update (pots T) j ψ with hudef
        have hθu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i) := by
          intro i
          by_cases hi : i = j
          · subst hi; simp only [hθdef, hudef, Function.update_self]; exact hψC.1
          · simp only [hθdef, hudef, Function.update_of_ne hi]; exact hpsh T i
        have hupd : fam (insert j T) = Function.update θ j (θ j + c • ω.form) := by
          funext i
          by_cases hi : i = j
          · subst hi; simp [hfam, hθdef]
          · simp [hfam, hθdef, hi]
        have hupu : pots (insert j T) = u := by
          funext i
          by_cases hi : i = j
          · subst hi; simp [hpots, hudef]
          · simp [hpots, hudef, hi]
        have hTj : fam T j = ω.form := by simp [hfam, hj]
        have hTj' : pots T j = fun _ => (0 : EReal) := by simp [hpots, hj]
        have hback : Function.update θ j ω.form = fam T := by
          rw [hθdef, Function.update_idem, ← hTj, Function.update_eq_self]
        have hbacku : Function.update u j (fun _ => (0 : EReal)) = pots T := by
          rw [hudef, Function.update_idem, ← hTj', Function.update_eq_self]
        have h0 : ∀ i, ThetaPlurisubharmonic (Function.update θ j ω.form i).val
            (Function.update u j (fun _ => (0 : EReal)) i) := by
          rw [hback, hbacku]; exact hpsh T
        have hstep := globalMixedMeasure_update_add_smul_eq (θ := θ) (u := u) j (γ := ω.form) hc
          hθu (by simp only [hθdef, hudef, Function.update_self]; exact hψC)
          (by rw [← hupd, ← hupu]; exact hpsh (insert j T)) h0
        calc ENNReal.ofReal c ^ (insert j T).card * V
            = ENNReal.ofReal c * (ENNReal.ofReal c ^ T.card * V) := by
              rw [Finset.card_insert_of_notMem hj, pow_succ]; ring
          _ ≤ ENNReal.ofReal c * globalMixedMeasure (fam T) (pots T) (hpsh T) univ := by gcongr
          _ = ENNReal.ofReal c * globalMixedMeasure (Function.update θ j ω.form)
                (Function.update u j (fun _ => (0 : EReal))) h0 univ := by
              rw [globalMixedMeasure_congr_tuples hback hbacku h0 (hpsh T)]
          _ ≤ globalMixedMeasure θ u hθu univ + ENNReal.ofReal c • globalMixedMeasure
                (Function.update θ j ω.form) (Function.update u j (fun _ => (0 : EReal))) h0 univ :=
              by rw [smul_eq_mul]; exact le_add_self
          _ = globalMixedMeasure (Function.update θ j (θ j + c • ω.form)) u _ univ := by
              rw [hstep, Measure.add_apply, Measure.smul_apply]
          _ = globalMixedMeasure (fam (insert j T)) (pots (insert j T)) (hpsh _) univ := by
              rw [globalMixedMeasure_congr_tuples hupd.symm hupu.symm _ (hpsh _)]
  -- the full family has total mass `0`
  have hfull : globalMixedMeasure (fam Finset.univ) (pots Finset.univ) (hpsh _) univ = 0 := by
    obtain ⟨M₀, hM₀⟩ := hψ.exists_global_upper_bound
    have hpot1 : ∀ i, IsThetaPshPotential (fam Finset.univ i).val (pots Finset.univ i) := by
      intro i
      simp only [hfam, hpots, Finset.mem_univ, if_true]
      exact ⟨hψ0, hψ.2⟩
    have hpot0 : ∀ i, IsThetaPshPotential (fam Finset.univ i).val (fun _ => (0 : EReal)) := by
      intro i
      simp only [hfam, Finset.mem_univ, if_true]
      exact (Pending.LocalPotentials.isThetaPshPotential_zero_iff _).mpr hzsemi
    have hmono := globalMixedMass_mono hn ω hpot1 hpot0 (fun i => by
      simp only [hpots, Finset.mem_univ, if_true]
      exact ⟨M₀, fun x _ => by simpa using hM₀ x⟩)
    have hsm := MixedMassClassInvariance.globalMixedMeasure_real_univ_eq_integral ω
      (fam Finset.univ) (fun i => (hpot0 i).1)
    have hslot : slotIntegral ω (fam Finset.univ) = 0 := by
      have h := slotIntegral_smul_prefix ω ω.form 0 n
      have hfe : (fun j : Fin n => if (j : ℕ) < n then (0 : ℝ) • ω.form else ω.form) =
          fam Finset.univ := by
        funext j
        simp only [hfam, Finset.mem_univ, if_true, if_pos j.isLt, hzero]
      rw [hfe, min_self, zero_pow hn.ne', zero_mul] at h
      exact h
    have hz : globalMixedMeasure (fam Finset.univ) (fun _ _ => (0 : EReal))
        (fun i => (hpot0 i).1) univ = 0 := by
      have hr : (globalMixedMeasure (fam Finset.univ) (fun _ _ => (0 : EReal))
          (fun i => (hpot0 i).1)).real univ = 0 := by
        rw [hsm]; exact hslot
      rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at hr
      exact hr.resolve_right (globalMixedMass_lt_top ω _).ne
    exact le_antisymm (hmono.trans_eq hz) bot_le
  -- the empty family is the Kähler volume
  have hV : V ≠ 0 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hpos := NefCoreKahlerCurrent.kahlerVolume_real_univ_pos ω
    have hVe : V = kahlerVolume ω univ := by
      rw [hVdef]
      exact congrArg (fun μ : Measure X => μ univ)
        (globalMixedMeasure_congr_tuples (by funext i; simp [hfam])
          (by funext i; simp [hpots]) (hpsh ∅) (fun _ => hω0))
    rw [hVe]
    exact (ENNReal.toReal_pos_iff.mp (by rwa [measureReal_def] at hpos)).1.ne'
  have h := key Finset.univ
  rw [hfull, nonpos_iff_eq_zero, mul_eq_zero] at h
  rcases h with h | h
  · exact absurd ((pow_eq_zero_iff (Finset.card_ne_zero.mpr
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩))).mp h) (ENNReal.ofReal_pos.mpr hc).ne'
  · exact hV h

end Nonneg

/-! ### The resolution step -/

section Resolution

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X] [ConnectedSpace X]

/-- **Boucksom's resolution step** (`bou:resolved-nef-part`, `bou02-volume:4.8`), PROVED on a compact
connected complex manifold of positive dimension from `RelativePrincipalization.exists_factorizationData`
as given (through TN23's `DominationResidualMass.exists_logResolution_mass`; human decision I-0902
item 3): the residual form `ρ^*β - Θ_F` of the resolution is nef, its top power is the non-pluripolar
mass of `ψ`, its mixed integrals against `ρ^*ω` are at most `Cⁱ ∫ ωⁿ`, and potentials transfer by
adding the weight of `F`. -/
theorem resolutionStep (hn : 0 < n) (ω : KahlerBackground n X) : ResolutionStep ω := by
  classical
  intro β ψ hψ hψa _ C hC
  obtain ⟨c, 𝔞, htype⟩ := hψa
  obtain ⟨Z, tZ, cZ, mZ, ρ, hρ, hcpt, hconn, ⟨ω'⟩, hpot, F, L, b, hb, hblow, hbupp, hboff, hnef,
    hmass⟩ := DominationResidualMass.exists_logResolution_mass hn ω β hψ htype
  let _ : MeasurableSpace Z := borel Z
  have _ : BorelSpace Z := ⟨rfl⟩
  set bF : ClosedRealOneOneForm n Z :=
    ClosedRealOneOneForm.pullback hρ.contMDiff β - F.curvature with hbFdef
  set m : ClosedRealOneOneForm n Z := ClosedRealOneOneForm.pullback hρ.contMDiff ω.form with hmdef
  have hC0 : 0 ≤ C := nonneg_of_isThetaPshPotential hn ω hψ hC
  have hbB : IsBoundedPotential b := ⟨-L.bound, L.bound, fun y => ⟨hblow y, hbupp y⟩⟩
  have hmsemi : m.val.IsSemipositive :=
    ClosedRealOneOneForm.pullback_isSemipositive hρ.contMDiff ω.isSemipositive
  have hmnef : NefWithRespectTo ω' m := nefWithRespectTo_of_isSemipositive hmsemi
  have hm0 : IsThetaPshPotential m.val (fun _ => (0 : EReal)) :=
    (Pending.LocalPotentials.isThetaPshPotential_zero_iff m).mpr hmsemi
  have h0bdd : IsBoundedPotential (fun _ : Z => (0 : EReal)) := ⟨0, 0, fun _ => ⟨le_rfl, le_rfl⟩⟩
  have hFnd : LocallyNondegenerate F.weight := by
    intro y U hU hyU
    obtain ⟨y', hy'U, hy'⟩ := hpot.2 y U hU hyU
    refine ⟨y', hy'U, fun hbot => hy' ?_⟩
    change ψ (ρ y') = ⊥
    rw [L.weight_add y', hbot, EReal.bot_add]
  have hψρ : ∀ y, y ∉ F.support → ψ (ρ y) = F.weight y + b y := fun y hy =>
    (L.weight_add y).trans (by rw [hboff y hy])
  -- `∫_Y mⁿ = ∫_X ωⁿ`
  have hvol : slotIntegral ω' (fun _ => m) = (kahlerVolume ω).real univ := by
    have h1 := MixedMassClassInvariance.globalMixedMeasure_real_univ_eq_integral ω' (fun _ => m)
      (fun _ => hm0.1)
    have h2 := ModificationMassInvariance.diagonalPotentialMass_pullback_of_isBlowupSequence hρ
      ω.form ((Pending.LocalPotentials.isThetaPshPotential_zero_iff ω.form).mpr ω.isSemipositive)
      hm0
    calc slotIntegral ω' (fun _ => m)
        = (globalMixedMeasure (fun _ => m) (fun _ _ => (0 : EReal)) (fun _ => hm0.1)).real univ :=
          h1.symm
      _ = (DiagonalMass.diagonalPotentialMass m (fun _ => 0) hm0).toReal := rfl
      _ = (DiagonalMass.diagonalPotentialMass ω.form (fun _ => 0)
            ((Pending.LocalPotentials.isThetaPshPotential_zero_iff ω.form).mpr
              ω.isSemipositive)).toReal := by rw [h2]
      _ = (kahlerVolume ω).real univ := rfl
  refine ⟨Z, tZ, cZ, mZ, borel Z, ⟨rfl⟩, hcpt, ρ, hρ, ω', bF, hnef ω', ?_, ?_, ?_⟩
  · -- (2) `∫ ⟨β_ψⁿ⟩ = ∫ ⟨(b_F)_bⁿ⟩ = ∫ b_Fⁿ`
    have hA := globalMixedMass_toReal_eq_slotIntegral hn ω' (θ := fun _ => bF)
      (fun _ => hnef ω') (u := fun _ => b) (fun _ => hb) (fun _ => hbB)
    rw [← hmass]
    change globalMixedMass (fun _ => bF) (fun _ => b) (fun _ => hb.1) ≤ _
    rw [← hA, ENNReal.ofReal_toReal (globalMixedMass_lt_top ω' _).ne]
  · -- (3) the mixed bounds
    intro i hi
    set S : Finset (Fin n) := Finset.univ.filter fun j : Fin n => (j : ℕ) < i with hS
    have hmemS : ∀ j : Fin n, j ∈ S ↔ (j : ℕ) < i := fun j => by simp [hS]
    set θ : Fin n → ClosedRealOneOneForm n Z := fun j => if (j : ℕ) < i then bF else m with hθ
    set θb : Fin n → ClosedRealOneOneForm n Z :=
      fun j => if (j : ℕ) < i then ClosedRealOneOneForm.pullback hρ.contMDiff β else m with hθb
    set θC : Fin n → ClosedRealOneOneForm n Z := fun j => if (j : ℕ) < i then C • m else m
      with hθC
    set u : Fin n → Z → EReal := fun j => if (j : ℕ) < i then b else fun _ => 0 with hu
    set w : Fin n → Z → EReal :=
      fun j => if (j : ℕ) < i then (fun y => ψ (ρ y)) else fun _ => 0 with hw
    have hθu : ∀ j, IsThetaPshPotential (θ j).val (u j) := fun j => by
      by_cases hj : (j : ℕ) < i
      · simp only [hθ, hu, if_pos hj]; exact hb
      · simp only [hθ, hu, if_neg hj]; exact hm0
    have hθnef : ∀ j, NefWithRespectTo ω' (θ j) := fun j => by
      by_cases hj : (j : ℕ) < i
      · simp only [hθ, if_pos hj]; exact hnef ω'
      · simp only [hθ, if_neg hj]; exact hmnef
    have hubdd : ∀ j, IsBoundedPotential (u j) := fun j => by
      by_cases hj : (j : ℕ) < i
      · simp only [hu, if_pos hj]; exact hbB
      · simp only [hu, if_neg hj]; exact h0bdd
    have hθbw : ∀ j, IsThetaPshPotential (θb j).val (w j) := fun j => by
      by_cases hj : (j : ℕ) < i
      · simp only [hθb, hw, if_pos hj]; exact hpot
      · simp only [hθb, hw, if_neg hj]; exact hm0
    -- step 1: the slot integral is the mixed mass of the bounded potentials
    have h1 := globalMixedMass_toReal_eq_slotIntegral hn ω' hθnef hθu hubdd
    -- step 2: off the divisor
    have hsub : subCurvatureOn θb F S = θ := by
      funext j
      by_cases hj : (j : ℕ) < i
      · have hjS : j ∈ S := (hmemS j).mpr hj
        simp only [subCurvatureOn, hθb, hθ, if_pos hjS, if_pos hj, hbFdef]
      · have hjS : j ∉ S := fun h => hj ((hmemS j).mp h)
        simp only [subCurvatureOn, hθb, hθ, if_neg hjS, if_neg hj]
    have hu' : ∀ j, ThetaPlurisubharmonic (subCurvatureOn θb F S j).val (u j) := by
      rw [hsub]; exact fun j => (hθu j).1
    have heq : ∀ j x, x ∉ F.support → w j x = if j ∈ S then F.weight x + u j x else u j x := by
      intro j x hx
      by_cases hj : (j : ℕ) < i
      · rw [if_pos ((hmemS j).mpr hj)]
        simp only [hw, hu, if_pos hj]
        exact hψρ x hx
      · rw [if_neg (fun h => hj ((hmemS j).mp h))]
        simp only [hw, hu, if_neg hj]
    have h2 := globalMixedMeasure_univ_subCurvatureOn_eq θb F S hu' (fun j => (hθbw j).1) heq hFnd
    -- step 3: the backgrounds grow by `ρ^*(Cω - β) ≥ 0`
    have hγ : (ClosedRealOneOneForm.pullback hρ.contMDiff (C • ω.form - β)).val.IsSemipositive :=
      ClosedRealOneOneForm.pullback_isSemipositive hρ.contMDiff hC
    have hCm : C • m = ClosedRealOneOneForm.pullback hρ.contMDiff β +
        (1 : ℝ) • ClosedRealOneOneForm.pullback hρ.contMDiff (C • ω.form - β) := by
      rw [pullback_sub, BoucksomResolutionAssembly.pullback_smul]
      module
    have hθC' : ∀ j, θC j = if j ∈ S then θb j + (1 : ℝ) •
        ClosedRealOneOneForm.pullback hρ.contMDiff (C • ω.form - β) else θb j := by
      intro j
      by_cases hj : (j : ℕ) < i
      · rw [if_pos ((hmemS j).mpr hj)]
        simp only [hθC, hθb, if_pos hj]
        exact hCm
      · rw [if_neg (fun h => hj ((hmemS j).mp h))]
        simp only [hθC, hθb, if_neg hj]
    have hθCw : ∀ j, IsThetaPshPotential (θC j).val (w j) := fun j => by
      rw [hθC' j]
      by_cases hjS : j ∈ S
      · rw [if_pos hjS]
        exact ⟨thetaPlurisubharmonic_add_of_isSemipositive (hθbw j).1
          (isSemipositive_smul hγ zero_le_one), (hθbw j).2⟩
      · rw [if_neg hjS]
        exact hθbw j
    have h3 := globalMixedMeasure_le_of_add_smul_on S hγ one_pos hθC' (fun j => (hθbw j).1)
      (fun j _ => hθbw j) (fun j => (hθCw j).1)
    -- step 4: `ψ ∘ ρ` is more singular than `0`
    have hθC0 : ∀ j, IsThetaPshPotential (θC j).val (fun _ => (0 : EReal)) := fun j => by
      by_cases hj : (j : ℕ) < i
      · simp only [hθC, if_pos hj]
        exact (Pending.LocalPotentials.isThetaPshPotential_zero_iff _).mpr
          (isSemipositive_smul hmsemi hC0)
      · simp only [hθC, if_neg hj]; exact hm0
    obtain ⟨M₀, hM₀⟩ := hψ.exists_global_upper_bound
    have hmore : ∀ j, MoreSingularOn (w j) (fun _ => (0 : EReal)) univ := fun j => by
      by_cases hj : (j : ℕ) < i
      · simp only [hw, if_pos hj]
        exact ⟨M₀, fun y _ => by simpa using hM₀ (ρ y)⟩
      · simp only [hw, if_neg hj]
        exact MoreSingularOn.of_le (fun _ _ => le_rfl)
    have h4 := globalMixedMass_mono hn ω' hθCw hθC0 hmore
    -- step 5: the smooth family
    have h5 := MixedMassClassInvariance.globalMixedMeasure_real_univ_eq_integral ω' θC
      (fun j => (hθC0 j).1)
    -- step 6: scaling
    have h6 := slotIntegral_smul_prefix ω' m C i
    rw [min_eq_right hi] at h6
    have hfin := globalMixedMass_lt_top ω' (fun j => (hθC0 j).1)
    show slotIntegral ω' θ ≤ _
    calc slotIntegral ω' θ = (globalMixedMass θ u (fun j => (hθu j).1)).toReal := h1.symm
      _ = (globalMixedMass θb w (fun j => (hθbw j).1)).toReal := by
          congr 1
          show globalMixedMeasure θ u _ univ = globalMixedMeasure θb w _ univ
          exact (congrArg (fun μ : Measure Z => μ univ)
            (globalMixedMeasure_congr_tuples hsub.symm rfl _ hu')).trans h2
      _ ≤ (globalMixedMass θC w (fun j => (hθCw j).1)).toReal :=
          ENNReal.toReal_mono (globalMixedMass_lt_top ω' _).ne (Measure.le_iff'.mp h3 univ)
      _ ≤ (globalMixedMass θC (fun _ _ => (0 : EReal)) (fun j => (hθC0 j).1)).toReal :=
          ENNReal.toReal_mono hfin.ne h4
      _ = slotIntegral ω' θC := h5
      _ = C ^ i * slotIntegral ω' (fun _ => m) := h6
      _ = C ^ i * (kahlerVolume ω).real univ := by rw [hvol]
  · -- (4) the transfer: add the weight of `F`
    intro γ v hv
    have hform : bF - ClosedRealOneOneForm.pullback hρ.contMDiff γ + F.curvature =
        ClosedRealOneOneForm.pullback hρ.contMDiff (β - γ) := by
      rw [pullback_sub, hbFdef]; abel
    have hpsh : ThetaPlurisubharmonic (ClosedRealOneOneForm.pullback hρ.contMDiff (β - γ)).val
        (fun y => v y + F.weight y) := by
      have h := SGPT.Foundations.Analysis.FirstPass.LocalPotentials.thetaPlurisubharmonic_add hv.1
        (MeteredDivisorPositivity.thetaPlurisubharmonic_weight F)
      rwa [hform] at h
    refine ⟨fun y => v y + F.weight y, hpsh, ?_⟩
    apply ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot hpsh
    have hopen : IsOpen F.supportᶜ :=
      (ResidualNef.isComplexAnalyticSubset_support F).isClosed.isOpen_compl
    obtain ⟨x, hx⟩ : ∃ x, x ∈ F.supportᶜ := by
      by_contra hcon
      push Not at hcon
      exact L.support_ne_univ hpot.2 (Set.eq_univ_of_forall fun x => by
        simpa using hcon x)
    obtain ⟨y, hyU, hvy⟩ := hv.2 x F.supportᶜ hopen hx
    exact ⟨y, fun h => (EReal.add_eq_bot_iff.mp h).elim hvy hyU⟩

end Resolution

end

end SGPT.Foundations.Analysis.Pending.BoucksomResolutionStep
