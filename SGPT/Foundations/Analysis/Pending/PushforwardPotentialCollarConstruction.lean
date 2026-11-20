import SGPT.Foundations.Analysis.Pending.DemaillyAlgebraicApproximationInterface
import SGPT.Foundations.Analysis.Pending.ThetaPshSmoothLocus
import SGPT.Foundations.Analysis.Pending.RegularizedMaxOffPoleCollarGluing
import SGPT.Foundations.Analysis.Pending.CompactCollarCutoff
import SGPT.Foundations.Analysis.Pending.PotentialPatchDensityComparison
import SGPT.Foundations.Analysis.Pending.AnalyticGluingProof
import SGPT.Foundations.Analysis.Pending.SmoothPotentialDomination
import SGPT.Foundations.Analysis.Pending.RestrictedMassFiniteness

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-!
# CT22, Lemma 4.3, Step 3: the collar construction

This module proves the analytic step of Collins--Tosatti 2022, Lemma 4.3, from the
single classical input
`Pending.DemaillyAlgebraicApproximation.exists_algebraicApproximation`
(`bou02-volume:2.6`, Demailly 1992) and nothing else.

## The construction

`Λ = ε - ε₀ > 0`.  Demailly's theorem gives `ψ_k ↓ ψ` with analytic singularities
and `α + ddᶜψ_k ≥ -δ_kω`, `δ_k → 0`, where `α = θ + ε₀ω`.  Let `U` be the smooth
locus of `ψ` (`Pending.ThetaPshSmoothLocus`), exhausted by compacta `K_m` with
collars `K_m ⊆ W_m`, `closure W_m ⊆ V_m`, `closure V_m ⊆ U` compact
(`Pending.CollarExhaustionDini`).  For each `m` take the collar cut-off `ρ_m` with
`ddᶜρ_m ≥ -C_mω` (`Pending.CompactCollarCutoff`), put `s_m = Λ/(2C_m)`, and choose
`k_m` with `δ_{k_m} ≤ Λ/2` and `sup_{closure V_m}(ψ_{k_m} - ψ) < s_m/4` — the
latter by Dini, which is legitimate because `ψ` and every `ψ_k` are continuous real
functions on `closure V_m`.  The glued potential is
```
  w_m = M_{s_m/4}(ψ - (-s_mρ_m),  ψ_{k_m} - s_m/2)   on V_m,
  w_m = ψ_{k_m} - s_m/2                              off V_m.
```
The GLOBAL branch carries the constant downward shift `-s_m/2`.  Without it
`ψ_{k_m} ≥ ψ` everywhere, so no regularized maximum against `ψ` could ever select
`ψ`, and the construction would be empty.

On the collar `V_m \ W_m` one has `ρ_m = -1`, so the local branch is `ψ - s_m` and
falls `3s_m/4` below the global one: the glue IS the global branch there, which is
what makes `w_m` globally defined with analytic singularities.  On a neighbourhood
of `K_m` one has `ρ_m = 0` and `ψ_{k_m} - ψ < s_m/4`, so the global branch falls
below the local one and the glue IS `ψ`.  The transition region carries no claim.

The positivity budget is the entire role of the strict gap `ε₀ < ε`: the cut-off
costs `s_mC_m ≤ Λ/2` and Demailly's loss costs `δ_{k_m} ≤ Λ/2`.

## Relation to the sorry it replaces

`Pending.PushforwardPotentialRegularizationInterface` states this theorem with a
`sorry`; that module is outside this lane's write set, so the proof is given here
under a different name and the one-line reroute is proposed by inbox item.
-/

open Set Filter
open scoped Topology ContDiff ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.PushforwardPotentialCollarConstruction

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.NumericalRestrictedVolumeScaffold FirstPass.NumericalRestrictedVolume
  FirstPass.AdmissibleCurrentFormPositivity
open SGPT.Foundations.Analysis.Pending.DemaillyAlgebraicApproximation
open SGPT.Foundations.Analysis.Pending.ThetaPshSmoothLocus
open SGPT.Foundations.Analysis.Pending.ThetaPshContinuityLocus
open SGPT.Foundations.Analysis.Pending.CompactCollarCutoff
open SGPT.Foundations.Analysis.Pending.CollarExhaustionDini
open SGPT.Foundations.Analysis.Pending.RegularizedMaxEReal
open SGPT.Foundations.Analysis.Pending.RegularizedMaxCollarGluing
open SGPT.Foundations.Analysis.Pending.RegularizedMaxOffPoleCollarGluing
open SGPT.Foundations.Analysis.Pending.RegularizedMaxSmoothAnalyticType
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Foundations.Analysis.Pending.PotentialPatchDensityComparison
open SGPT.Foundations.Analysis.Pending.ThetaCapacityDecreasingConvergence
open SGPT.Foundations.Analysis.Pending.AnalyticGluingProof
open SGPT.Foundations.Analysis.Pending.SmoothPotentialDomination
open SGPT.Foundations.Analysis.Pending.RestrictedMassFiniteness
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialTransforms
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.RegularPatchNeighborhood
open SGPT.Foundations.Analysis.Pending.ExceptionalPushforwardDensity

noncomputable section

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-! ## Background monotonicity of the global theta-PSH predicates -/

theorem thetaPlurisubharmonicOn_univ_iff {θ : SmoothRealForm n Y 2} {v : Y → EReal} :
    ThetaPlurisubharmonicOn θ v univ ↔ ThetaPlurisubharmonic θ v :=
  ⟨fun h e z hz => h e z hz (mem_univ _), fun h e z hz _ => h e z hz⟩

theorem thetaPlurisubharmonic_add_of_semipositive {a b : ClosedRealOneOneForm n Y}
    {v : Y → EReal} (hv : ThetaPlurisubharmonic a.val v) (hb : b.val.IsSemipositive) :
    ThetaPlurisubharmonic (a + b).val v :=
  thetaPlurisubharmonicOn_univ_iff.mp
    (thetaPlurisubharmonicOn_add_of_semipositive
      (thetaPlurisubharmonicOn_univ_iff.mpr hv) hb)

/-- **Enlarging the background.**  A `θ`-PSH potential is `θ'`-PSH whenever
`θ' - θ` is semipositive. -/
theorem isThetaPshPotential_mono {a b : ClosedRealOneOneForm n Y} {v : Y → EReal}
    (hv : IsThetaPshPotential a.val v) (hb : (b - a).val.IsSemipositive) :
    IsThetaPshPotential b.val v := by
  have h := thetaPlurisubharmonic_add_of_semipositive hv.1 hb
  rw [show a + (b - a) = b from by abel] at h
  exact ⟨h, hv.2⟩

theorem ThetaPlurisubharmonic.onSet {θ : SmoothRealForm n Y 2} {v : Y → EReal}
    (h : ThetaPlurisubharmonic θ v) (Ω : Set Y) : ThetaPlurisubharmonicOn θ v Ω :=
  fun e z hz _ => h e z hz

theorem thetaPlurisubharmonicOn_mono {a b : ClosedRealOneOneForm n Y} {v : Y → EReal}
    {Ω : Set Y} (hv : ThetaPlurisubharmonicOn a.val v Ω)
    (hb : (b - a).val.IsSemipositive) : ThetaPlurisubharmonicOn b.val v Ω := by
  have h := thetaPlurisubharmonicOn_add_of_semipositive hv hb
  rwa [show a + (b - a) = b from by abel] at h


/-! ## The construction -/

variable [CompactSpace Y]

/-- **CT22, Lemma 4.3, Step 3.**  Demailly's approximation, a collar cut-off, a
constant downward shift of the global branch and a regularized-max glue produce
`ε`-admissible presentations along `W` that keep the poles of `ψ` and recover its
smooth-locus densities. -/
theorem exists_regularization_of_thetaPshPotential
    (theta : ClosedRealOneOneForm n Y) (omega : KahlerBackground n Y)
    (W : ClosedIrreducibleAnalyticSubvariety n Y)
    (eps0 eps : PositiveError) (hgap : (eps0 : ℝ) < (eps : ℝ))
    (psi : Y → EReal)
    (hpsi : IsThetaPshPotential (theta + (eps0 : ℝ) • omega.form).val psi)
    (hW : ¬ W.carrier ⊆ poleSet psi) :
    ∃ p : ℕ → AdmissibleRestrictedCurrentPresentation omega
        (RealBottChern.ofRepresentative theta) W eps,
      (∀ y ∉ poleSet psi, ∀ m, y ∉ poleSet (p m).potential) ∧
      ∀ (P : RegularPatch W) (v : ComplexModel W.dim), v ∈ P.parameterDomain →
        P.toManifold v ∉ poleSet psi →
        (∀ᶠ y in 𝓝 (P.coordinateParametrization v),
          ContDiffAt ℝ ∞
            (fun y' => (psi ((complexChartAt (n := n) P.center).val.symm y')).toReal) y) →
        ENNReal.ofReal (potentialPatchDensity
            (theta + (eps0 : ℝ) • omega.form) psi P v)
          ≤ liminf (fun m => ENNReal.ofReal (patchDensity (p m) P v)) atTop := by
  classical
  set alpha : ClosedRealOneOneForm n Y := theta + (eps0 : ℝ) • omega.form with halpha
  set Th : ClosedRealOneOneForm n Y := theta + (eps : ℝ) • omega.form with hTh
  set Lam : ℝ := (eps : ℝ) - (eps0 : ℝ) with hLamdef
  have hLpos : 0 < Lam := by rw [hLamdef]; linarith
  have homegasemi : omega.form.val.IsSemipositive := omega.isSemipositive
  -- `Th - alpha - A omega = (Lam - A) omega`, and it is semipositive for `A <= Lam`
  have hdiff : ∀ A : ℝ, 0 ≤ Lam - A →
      (Th - (alpha + A • omega.form)).val.IsSemipositive := by
    intro A hA
    have hform : Th - (alpha + A • omega.form) = (Lam - A) • omega.form := by
      rw [hTh, halpha, hLamdef]; module
    rw [hform]
    exact KahlerDomination.isSemipositive_smul homegasemi hA
  -- Demailly's approximation
  obtain ⟨psiSeq, delta, hsing, hanti, hinf, hdelta0, hdeltaT, hpshk⟩ :=
    exists_algebraicApproximation omega alpha psi hpsi
  have hle : ∀ k x, psi x ≤ psiSeq k x := fun k x => le_of_iInf_eq hinf k x
  have hpole : ∀ k, poleSet (psiSeq k) ⊆ poleSet psi := fun k =>
    poleSet_subset_of_iInf_eq hinf k
  have hknetop : ∀ k x, psiSeq k x ≠ ⊤ := fun k x =>
    (hpshk k).1.quasiPlurisubharmonic.ne_top x
  have hpsinetop : ∀ x, psi x ≠ ⊤ := hpsi.1.quasiPlurisubharmonic.ne_top
  -- the smooth locus and its nested exhaustion
  set U : Set Y := smoothLocus (n := n) psi with hUdef
  have hUopen : IsOpen U := isOpen_smoothLocus psi
  have hUfin : ∀ x ∈ U, psi x ≠ ⊥ := fun _ hx => ne_bot_of_mem_smoothLocus hx
  obtain ⟨K, Wc, Vc, hKc, hKmono, hKunion, hWopen, hVopen, hKW, hWV, hVU, hVcomp⟩ :=
    hUopen.exists_nested_collar_exhaustion
  have hKV : ∀ m, K m ⊆ Vc m := fun m => (hKW m).trans (subset_closure.trans (hWV m))
  have hVUsub : ∀ m, Vc m ⊆ U := fun m => subset_closure.trans (hVU m)
  have hkne : ∀ (m : ℕ), ∀ x ∈ closure (Vc m), ∀ k, psiSeq k x ≠ ⊥ := by
    intro m x hx k hbot
    exact hUfin x (hVU m hx) (le_bot_iff.mp (hbot ▸ hle k x))
  -- Dini on each `closure (Vc m)`
  have hdini : ∀ (m : ℕ) (t : ℝ), 0 < t → ∃ N : ℕ, ∀ k, N ≤ k → ∀ x ∈ closure (Vc m),
      (psiSeq k x).toReal < (psi x).toReal + t := by
    intro m t ht
    refine exists_forall_lt_add_of_antitone_of_continuousOn (hVcomp m) (fun k => ?_) (fun x hx =>
      (continuousAt_toReal_of_mem_smoothLocus (hVU m hx)).continuousWithinAt) ?_ ?_ ht
    · exact continuousOn_toReal_of_hasManifoldAnalyticSingularitiesSmoothOffPole (hsing k)
        fun x hx => hkne m x hx k
    · intro x hx j k hjk
      exact EReal.toReal_le_toReal (hanti x hjk) (hkne m x hx k) (hknetop j x)
    · intro x hx
      exact (EReal.tendsto_toReal (hpsinetop x) (hUfin x (hVU m hx))).comp
        (tendsto_of_antitone_of_iInf_eq hanti hinf x)
  -- one presentation per stage
  have hstep : ∀ m : ℕ, ∃ q : AdmissibleRestrictedCurrentPresentation omega
        (RealBottChern.ofRepresentative theta) W eps,
      q.representative = theta ∧ poleSet q.potential ⊆ poleSet psi ∧
      ∀ x ∈ K m, q.potential =ᶠ[𝓝 x] psi := by
    intro m
    obtain ⟨rho, hrho, hrlow, hrup, ⟨Nb, hNopen, hKN, hrhoN⟩, hrhoOff, C, hC, hsemiC⟩ :=
      exists_chartSmooth_collar_ddc_lower omega (hKc m) (hWopen m) (hKW m)
    set sc : ℝ := Lam / (2 * C) with hscdef
    have hspos : 0 < sc := by rw [hscdef]; positivity
    have hsC : sc * C = Lam / 2 := by rw [hscdef]; field_simp
    have hq4 : (0 : ℝ) < sc / 4 := by positivity
    -- the index of the approximant
    obtain ⟨N1, hN1⟩ := eventually_atTop.mp
      (hdeltaT (gt_mem_nhds (show (0 : ℝ) < Lam / 2 by linarith)))
    obtain ⟨N2, hN2⟩ := hdini m (sc / 4) hq4
    set kk : ℕ := max N1 N2 with hkk
    have hdk : delta kk ≤ Lam / 2 := (hN1 kk (le_max_left _ _)).le
    have hDini : ∀ x ∈ closure (Vc m), (psiSeq kk x).toReal < (psi x).toReal + sc / 4 :=
      hN2 kk (le_max_right _ _)
    -- the two branches
    set vv : Y → ℝ := fun x => (-sc) * rho x with hvv
    have hvsm : ChartSmooth (n := n) vv := fun e => contDiffOn_const.mul (hrho e)
    set fb : Y → EReal := fun x => psi x + ((sc * rho x : ℝ) : EReal) with hfb
    set gb : Y → EReal := fun x => psiSeq kk x + ((-(sc / 2) : ℝ) : EReal) with hgb
    have hfbapp : ∀ x, fb x = psi x + ((sc * rho x : ℝ) : EReal) := fun _ => rfl
    have hgbapp : ∀ x, gb x = psiSeq kk x + ((-(sc / 2) : ℝ) : EReal) := fun _ => rfl
    have hvvapp : ∀ x, vv x = (-sc) * rho x := fun _ => rfl
    have hfbsub : fb = fun x => psi x - ((vv x : ℝ) : EReal) := by
      funext x
      rw [hfbapp, hvvapp, show ((-sc) * rho x : ℝ) = -(sc * rho x) by ring, EReal.coe_neg,
        sub_eq_add_neg, neg_neg]
    have hgbsub : gb = fun x => psiSeq kk x - ((sc / 2 : ℝ) : EReal) := by
      funext x
      rw [hgbapp, EReal.coe_neg, sub_eq_add_neg]
    have hfbnetop : ∀ x, fb x ≠ ⊤ := fun x => by
      rw [hfbapp]; exact EReal.add_ne_top (hpsinetop x) (EReal.coe_ne_top _)
    have hgbnetop : ∀ x, gb x ≠ ⊤ := fun x => by
      rw [hgbapp]; exact EReal.add_ne_top (hknetop kk x) (EReal.coe_ne_top _)
    -- the collar gap: off the inner core the cut-off is `-1`
    have hgapcollar : ∀ x ∈ Vc m \ Wc m, fb x + ((sc / 4 : ℝ) : EReal) ≤ gb x := by
      intro x hx
      have hr : rho x = -1 := hrhoOff x hx.2
      have harith : sc * rho x + sc / 4 = -(3 * sc / 4) := by rw [hr]; ring
      have h1 : fb x + ((sc / 4 : ℝ) : EReal) = psi x + ((-(3 * sc / 4) : ℝ) : EReal) := by
        rw [hfbapp, add_assoc, ← EReal.coe_add, harith]
      rw [h1, hgbapp]
      exact add_le_add (hle kk x) (EReal.coe_le_coe_iff.mpr (by linarith))
    -- the glued potential
    set wb : Y → EReal := eregularizedMaxGlued (Vc m) (sc / 4) fb gb with hwb
    -- positivity
    have hgbpsh : IsThetaPshPotential Th.val gb := by
      have h1 : IsThetaPshPotential Th.val (psiSeq kk) :=
        isThetaPshPotential_mono (hpshk kk) (hdiff (delta kk) (by linarith))
      rw [hgbsub]
      refine ⟨thetaPlurisubharmonic_sub_const h1.1 (sc / 2), ?_⟩
      intro x V hV hxV
      obtain ⟨y, hy, hyne⟩ := h1.2 x V hV hxV
      refine ⟨y, hy, ?_⟩
      show psiSeq kk y - ((sc / 2 : ℝ) : EReal) ≠ ⊥
      rw [sub_eq_add_neg, ← EReal.coe_neg]
      exact EReal.add_ne_bot_iff.mpr ⟨hyne, EReal.coe_ne_bot _⟩
    have hfbpsh : ThetaPlurisubharmonicOn Th.val fb (Vc m) := by
      have h0 : ThetaPlurisubharmonic (alpha + ddcClosedForm vv hvsm).val
          (fun x => psi x - ((vv x : ℝ) : EReal)) := by
        refine thetaPlurisubharmonic_sub_smooth hvsm (fun e z _ => ?_) hpsi.1
        simp [ClosedRealOneOneForm.coeff_add, ddcClosedForm_coeff]
      rw [← hfbsub] at h0
      refine thetaPlurisubharmonicOn_mono (ThetaPlurisubharmonic.onSet h0 (Vc m)) ?_
      -- `Th - alpha - ddc vv = Lam omega + s ddc rho >= (Lam/2) omega >= 0`
      have hform : Th - (alpha + ddcClosedForm vv hvsm)
          = Lam • omega.form + (-1 : ℝ) • ddcClosedForm vv hvsm := by
        rw [hTh, halpha, hLamdef]; module
      rw [hform]
      intro e z hz u
      have hddc : (ddcClosedForm vv hvsm).val.coeff e z ![u, Complex.I • u]
          = (-sc) * (ddcClosedForm rho hrho).val.coeff e z ![u, Complex.I • u] :=
        ddcClosedForm_const_mul_coeff hrho (-sc) hvsm e hz u
      have hlow := hsemiC e z hz u
      have homg := homegasemi e z hz u
      simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
        ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
        smul_eq_mul] at hlow ⊢
      rw [hddc]
      nlinarith [mul_le_mul_of_nonneg_left hlow hspos.le]
    have hwbpsh : IsThetaPshPotential Th.val wb :=
      isThetaPshPotential_eregularizedMaxGlued hq4 (hVopen m) (hWV m) hgapcollar
        hfbpsh hgbpsh
    -- analytic singularities
    have hwbsing : HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) wb := by
      refine hasManifoldAnalyticSingularitiesSmoothOffPole_eregularizedMaxGlued hq4
        (hVopen m) (hWV m) hgapcollar hgbnetop ?_ ?_
      · rw [hgbsub]
        exact hasManifoldAnalyticSingularitiesSmoothOffPole_sub (hsing kk)
          (fun _ => contDiffOn_const)
      · intro e z hz hzV
        obtain ⟨g0, hg0, heq0⟩ := hVUsub m hzV e z hz rfl
        refine ⟨fun y => g0 y + sc * rho (e.val.symm y), ?_, ?_⟩
        · filter_upwards [hg0, e.val.open_target.mem_nhds hz] with y hy hyt
          exact hy.add (contDiffAt_const.mul
            ((hrho e).contDiffAt (e.val.open_target.mem_nhds hyt)))
        · filter_upwards [heq0] with y hy
          show psi (e.val.symm y) + ((sc * rho (e.val.symm y) : ℝ) : EReal) = _
          rw [show psi (e.val.symm y) = chartFunction psi e y from rfl, hy, ← EReal.coe_add]
    -- the pole set does not grow
    have hwbpole : poleSet wb ⊆ poleSet psi := by
      intro x hx
      rw [mem_poleSet] at hx ⊢
      by_cases hxV : x ∈ Vc m
      · rw [hwb, eregularizedMaxGlued_of_mem hxV] at hx
        have hfbot : fb x = ⊥ :=
          le_bot_iff.mp (hx ▸ (le_max_right (gb x) (fb x)).trans
            (max_le_eregularizedMax hq4 (hgbnetop x) (hfbnetop x)))
        by_contra hne
        rw [hfb] at hfbot
        exact (EReal.add_ne_bot_iff.mpr ⟨hne, EReal.coe_ne_bot _⟩) hfbot
      · rw [hwb, eregularizedMaxGlued_of_not_mem hxV, hgb] at hx
        by_cases hne : psiSeq kk x = ⊥
        · exact hpole kk hne
        · exact absurd hx (EReal.add_ne_bot_iff.mpr ⟨hne, EReal.coe_ne_bot _⟩)
    refine ⟨⟨theta, rfl, wb, hwbpsh, hwbsing, fun hc => hW (hc.trans hwbpole)⟩, rfl, hwbpole, ?_⟩
    -- the germ on the core
    intro x hx
    have hxV : x ∈ Vc m := hKV m hx
    have hxN : x ∈ Nb := hKN hx
    have hopen : IsOpen (Nb ∩ Vc m) := hNopen.inter (hVopen m)
    filter_upwards [hopen.mem_nhds ⟨hxN, hxV⟩] with y hy
    have hr0 : rho y = 0 := hrhoN y hy.1
    have hfby : fb y = psi y := by
      rw [hfbapp, hr0]
      norm_num
    have hycl : y ∈ closure (Vc m) := subset_closure hy.2
    have hyfin : psi y ≠ ⊥ := hUfin y (hVU m hycl)
    have hykfin : psiSeq kk y ≠ ⊥ := hkne m y hycl kk
    have hgapy : gb y + ((sc / 4 : ℝ) : EReal) ≤ fb y := by
      have hb : ((psiSeq kk y).toReal : EReal) = psiSeq kk y :=
        EReal.coe_toReal (hknetop kk y) hykfin
      have ha : ((psi y).toReal : EReal) = psi y := EReal.coe_toReal (hpsinetop y) hyfin
      have hlt := hDini y hycl
      rw [hgbapp, hfby, ← ha, ← hb, ← EReal.coe_add, ← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (by linarith)
    show wb y = psi y
    rw [hwb, eregularizedMaxGlued_of_mem hy.2,
      eregularizedMax_eq_right_of_gap hq4 hgapy (hfbnetop y), hfby]
  choose q hqrep hqpole hqgerm using hstep
  refine ⟨q, fun y hy m hmem => hy (hqpole m hmem), ?_⟩
  intro P vp hv hnotpole hsm
  set e : ComplexChart n Y := complexChartAt (n := n) P.center with he
  set z : ComplexModel n := P.coordinateParametrization vp with hzdef
  have hzt : z ∈ e.val.target :=
    P.source_subset (RegularPatchNeighborhood.RegularPatch.coordinateParametrization_mem_source P hv)
  have hx0 : e.val.symm z = P.toManifold vp := rfl
  have hmemU : e.val.symm z ∈ U := mem_smoothLocus_of_eventually_contDiffAt hpsi e hzt hsm
  obtain ⟨g0, hg0, heq0⟩ := hmemU e z hzt rfl
  obtain ⟨m0, hm0⟩ : ∃ m0, e.val.symm z ∈ K m0 := by
    rw [hUdef] at hmemU
    have : e.val.symm z ∈ ⋃ m, K m := by rw [hKunion]; exact hmemU
    exact mem_iUnion.mp this
  have htoReal : (fun y => (psi (e.val.symm y)).toReal) =ᶠ[𝓝 z] g0 := by
    filter_upwards [heq0] with y hy
    show (chartFunction psi e y).toReal = g0 y
    rw [hy]
    exact EReal.toReal_coe _
  refine ofReal_potentialPatchDensity_le_liminf_of_eventually_germ (a := alpha) (psi := psi)
    q P hv hzt (hsm.self_of_nhds.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) ?_ ?_ ?_
  · -- semipositivity of the limit coordinate form
    intro uu
    have hsemi := semipositive_add_smoothDDC_of_thetaPlurisubharmonic hpsi.1 e hzt hg0 heq0 uu
    have hcongr : smoothDDC (fun y => (psi (e.val.symm y)).toReal) z = smoothDDC g0 z :=
      smoothDDC_congr htoReal
    simp only [potentialCoordinateForm, ContinuousAlternatingMap.add_apply, ← he, ← hzdef,
      hcongr]
    exact hsemi
  · -- the germ of the glued potential is the germ of `psi`, eventually
    filter_upwards [eventually_ge_atTop m0] with m hm
    have hmem : e.val.symm z ∈ K m := hKmono hm hm0
    have hgermY : (q m).potential =ᶠ[𝓝 (e.val.symm z)] psi := hqgerm m _ hmem
    have hchart : (fun y => (q m).potential (e.val.symm y)) =ᶠ[𝓝 z]
        fun y => psi (e.val.symm y) := hgermY.comp_tendsto (e.val.continuousAt_symm hzt)
    filter_upwards [hchart] with y hy
    rw [hy]
  · -- the perturbed representative dominates `alpha`
    filter_upwards with m
    intro uu
    have hrep : perturbedRepresentative (q m) = Th := by
      rw [hTh]
      show (q m).representative + (eps : ℝ) • omega.form = theta + (eps : ℝ) • omega.form
      rw [hqrep m]
    have hform : Th = alpha + Lam • omega.form := by rw [hTh, halpha, hLamdef]; module
    have homg := homegasemi e z hzt uu
    rw [hrep, hform]
    simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    nlinarith

end

end SGPT.Foundations.Analysis.Pending.PushforwardPotentialCollarConstruction
