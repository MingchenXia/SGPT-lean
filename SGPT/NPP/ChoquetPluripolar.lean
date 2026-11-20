import SGPT.NPP.ChoquetCapacitability
import SGPT.NPP.PluripolarCapacity
import SGPT.Foundations.Analysis.Pending.NegligibleSetsPluripolarProof
import SGPT.Foundations.Analysis.Pending.ChoquetRegularization
import SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit
import SGPT.Foundations.Analysis.Pending.ThetaPshAntitoneSupNondegenerate
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple
import SGPT.Foundations.Analysis.FirstPass.ThetaPshComparison

/-!
# Borel sets of capacity zero are pluripolar

Source `thm:pp_cap` (`chapter_npp.tex`): on a compact Kähler manifold `X` and for `θ` a closed
smooth real `(1,1)`-form in a big class, a **Borel** set `A ⊆ X` is pluripolar iff
`Cap_θ(A) = 0`.  The implication pluripolar ⇒ capacity zero and the converse for closed and
`F_σ` sets are in `SGPT.NPP.PluripolarCapacity`; this file proves the converse for every Borel
set (`locallyPluripolar_of_measurableSet_of_sourceThetaCapacity_eq_zero`), and hence the full
equivalence (`locallyPluripolar_iff_sourceThetaCapacity_eq_zero`).

## The route

The missing ingredient was a Choquet capacity whose null sets are the pluripolar sets.  We use
the *extremal height* of the global (Siciak) extremal function of a set `E ⊆ X`,

  `h(E) = sup_X V_E = sup {sup_X u | u ω-psh, u ≤ 0 on E}`   (`extremalHeight`),

for a Kähler form `ω` (`h(E) ∈ [0, ∞]`, antitone in `E`; `E` is pluripolar iff `h(E) = ∞`).
`exp(-h)` is, up to normalization, the Alexander–Taylor capacity.

* **Continuity along increasing sequences** (`iInf_extremalHeight_le_iUnion`): if `E_j ↑ E`,
  then `h(E) = lim h(E_j)`.  For `t < inf_j h(E_j)` let `W_j` be the regularized upper envelope
  of the competitors for `E_j` bounded by `t + 1`; by Choquet's lemma and Bedford–Taylor's
  theorem on negligible sets (TN `NegligibleSetsPluripolarProof.outerCapacityZero_negligible`),
  `W_j ≤ 0` on `E_j` off a set of outer capacity zero.  The `W_j` decrease to an `ω`-psh `W ≥ 0`
  with `sup W ≥ t` (compactness), and `W ≤ 0` on `E` off a set `N` of outer capacity zero.  `N`
  lies in the pole set of an `ω`-psh `ψ ≤ 0` (TN step C1), and the competitors `(1-ε) W + ε ψ`
  for `E` give `W ≤ h(E)` off the poles of `ψ`, hence everywhere
  (`ThetaPlurisubharmonic.le_of_quasiEverywhere_le`), so `h(E) ≥ t`.
* **Outer regularity at pluripolar sets** (`exists_isOpen_lt_extremalHeight`): a set of outer
  capacity zero lies in the open sets `{ψ < -c}`, on which `ψ + c` is a competitor.
* **Height `∞` ⇒ pluripolar** (`manifoldLocallyPluripolar_of_extremalHeight_eq_top`): the
  regularized envelopes of the sup-normalized competitors `≤ -N` on `A` decrease, each touching
  `0`; their limit is a genuine `ω`-psh potential (compactness of normalized `ω`-psh functions and
  the identity principle) which is `-∞` on `A` off a set of outer capacity zero.

Choquet's capacitability theorem for the antitone set function `h`
(`SGPT.NPP.Choquet.exists_isCompact_subset_forall_isOpen_gt_of_antitone`) then shows: if `A` is
analytic (e.g. Borel) and every compact subset of `A` is pluripolar, then `h(A) = ∞`, i.e. `A` is
pluripolar.  For a Borel set of capacity zero every compact subset has capacity zero and is
pluripolar by the closed case.

This replaces the reference [GZ17, Theorem 4.40] of the source; no Josefson theorem is used.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.ChoquetPluripolar

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ThetaCapacity
open SGPT.Foundations.Analysis.Pending.PluripolarCapacityZero
open SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The competitors of the global extremal function of `E`: `ω`-psh potentials which are
`≤ 0` on `E`. -/
def extremalCompetitors (ω : KahlerBackground n M) (E : Set M) : Set (M → EReal) :=
  {u | IsThetaPshPotential ω.form.val u ∧ ∀ x ∈ E, u x ≤ 0}

/-- The extremal height `h(E) = sup_X V_E` of `E`: the supremum over `X` of the global (Siciak)
extremal function `V_E = sup {u | u ω-psh, u ≤ 0 on E}`. -/
def extremalHeight (ω : KahlerBackground n M) (E : Set M) : EReal :=
  ⨆ u ∈ extremalCompetitors ω E, ⨆ x, u x

/-- Every value of a competitor is at most the extremal height. -/
theorem le_extremalHeight (ω : KahlerBackground n M) {E : Set M} {u : M → EReal}
    (hu : u ∈ extremalCompetitors ω E) (x : M) : u x ≤ extremalHeight ω E :=
  le_iSup₂_of_le (f := fun u (_ : u ∈ extremalCompetitors ω E) => ⨆ x, u x) u hu (le_iSup u x)

/-- The extremal height is antitone. -/
theorem extremalHeight_antitone (ω : KahlerBackground n M) : Antitone (extremalHeight ω) := by
  intro E F hEF
  refine iSup₂_le fun u hu => ?_
  exact iSup_le fun x => le_extremalHeight ω ⟨hu.1, fun y hy => hu.2 y (hEF hy)⟩ x

/-- The potential `0` is a competitor of every set. -/
theorem zero_mem_extremalCompetitors (ω : KahlerBackground n M) (E : Set M) :
    (fun _ => (0 : EReal)) ∈ extremalCompetitors ω E :=
  ⟨isThetaPshPotential_zero ω, fun _ _ => le_rfl⟩

/-- On a nonempty manifold the extremal height is nonnegative. -/
theorem zero_le_extremalHeight [Nonempty M] (ω : KahlerBackground n M) (E : Set M) :
    0 ≤ extremalHeight ω E :=
  le_extremalHeight ω (zero_mem_extremalCompetitors ω E) (Classical.arbitrary M)

/-- A `θ`-psh potential on a compact manifold attains its supremum, at a real value if it
exceeds a real number somewhere. -/
theorem exists_max_coe [CompactSpace M] {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hu : IsThetaPshPotential θ u) {x : M} {a : EReal} (hx : a < u x) :
    ∃ xm : M, ∃ m : ℝ, u xm = (m : EReal) ∧ a < (m : EReal) ∧ ∀ y, u y ≤ (m : EReal) := by
  obtain ⟨xm, -, hxm⟩ :=
    (hu.1.quasiPlurisubharmonic.upperSemicontinuous.upperSemicontinuousOn univ).exists_isMaxOn
      ⟨x, mem_univ x⟩ isCompact_univ
  have hax : a < u xm := hx.trans_le (hxm (mem_univ x))
  have hne_top : u xm ≠ ⊤ := hu.1.quasiPlurisubharmonic.ne_top xm
  refine ⟨xm, (u xm).toReal, (EReal.coe_toReal hne_top (ne_bot_of_gt hax)).symm, ?_, ?_⟩
  · rwa [EReal.coe_toReal hne_top (ne_bot_of_gt hax)]
  · intro y
    rw [EReal.coe_toReal hne_top (ne_bot_of_gt hax)]
    exact hxm (mem_univ y)

section Compact

variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **Regularized upper envelopes.**  For a nonempty family `F` of `Ω`-psh potentials bounded
above by one real constant, the regularized supremum `(sup F)^*` is `Ω`-psh, and it differs from
`sup F` only on a set of outer capacity zero (Choquet's lemma and Bedford–Taylor's theorem on
negligible sets). -/
theorem envelope_spec (hn : 0 < n) (Ω : KahlerBackground n M) {F : Set (M → EReal)}
    (hF : F.Nonempty) (hFpsh : ∀ u ∈ F, IsThetaPshPotential Ω.form.val u) {C : ℝ}
    (hFC : ∀ u ∈ F, ∀ x, u x ≤ (C : EReal)) :
    IsThetaPshPotential Ω.form.val (uscRegularization (sSup F)) ∧
      OuterCapacityZero Ω {x | sSup F x < uscRegularization (sSup F) x} := by
  obtain ⟨s, hsF, hs⟩ := exists_seq_uscRegularization_iSup_eq hF
  refine ⟨?_, ?_⟩
  · rw [← hs]
    exact NegligibleSetsPluripolarProof.isThetaPshPotential_uscRegularization_iSup_of_le
      (fun k => hFpsh _ (hsF k)) (fun k x => hFC _ (hsF k) x)
  · refine NegligibleSetsPluripolarProof.OuterCapacityZero.mono
      (NegligibleSetsPluripolarProof.outerCapacityZero_negligible hn Ω
        (fun k => hFpsh _ (hsF k)) (fun k x => hFC _ (hsF k) x)) ?_
    intro x hx
    have hx' : sSup F x < uscRegularization (sSup F) x := hx
    show (⨆ j, s j) x < uscRegularization (⨆ j, s j) x
    rw [hs]
    refine lt_of_le_of_lt ?_ hx'
    exact (iSup_le fun k => le_sSup (hsF k) : (⨆ j, s j) ≤ sSup F) x

/-- **The extremal height is continuous along increasing sequences**: if `E_j ↑ E` then
`h(E) ≥ inf_j h(E_j)` (hence `h(E) = lim_j h(E_j)`), on a compact connected Kähler manifold of
positive dimension. -/
theorem iInf_extremalHeight_le_iUnion (hn : 0 < n) [ConnectedSpace M] (ω : KahlerBackground n M)
    {E : ℕ → Set M} (hE : Monotone E) :
    ⨅ j, extremalHeight ω (E j) ≤ extremalHeight ω (⋃ j, E j) := by
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · have hbot : ∀ S : Set M, extremalHeight ω S = ⊥ := fun S => by
      refine le_antisymm (iSup₂_le fun u _ => ?_) bot_le
      exact iSup_le fun x => (IsEmpty.false x).elim
    simp [hbot]
  by_contra hcon
  push Not at hcon
  obtain ⟨t, ht1, ht2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
  have h0 := isThetaPshPotential_zero ω
  have ht0 : (0 : ℝ) ≤ t := by
    have := (zero_le_extremalHeight ω (⋃ j, E j)).trans ht1.le
    exact_mod_cast this
  -- the truncated families of competitors and their envelopes
  set F : ℕ → Set (M → EReal) := fun j => {u | IsThetaPshPotential ω.form.val u ∧
    (∀ x ∈ E j, u x ≤ 0) ∧ ∀ x, u x ≤ ((t + 1 : ℝ) : EReal)} with hFdef
  have hF0 : ∀ j, (fun _ => (0 : EReal)) ∈ F j := fun j =>
    ⟨h0, fun _ _ => le_rfl, fun _ => show (0 : EReal) ≤ ((t + 1 : ℝ) : EReal) by
      exact_mod_cast (by linarith : (0 : ℝ) ≤ t + 1)⟩
  have hspec := fun j => envelope_spec hn ω ⟨_, hF0 j⟩ (fun u (hu : u ∈ F j) => hu.1)
    (fun u (hu : u ∈ F j) => hu.2.2)
  set W : ℕ → M → EReal := fun j => uscRegularization (sSup (F j)) with hWdef
  have hWpsh : ∀ j, IsThetaPshPotential ω.form.val (W j) := fun j => (hspec j).1
  have hWanti : ∀ x, Antitone fun j => W j x := by
    intro x j k hjk
    refine uscRegularization_mono (sSup_le_sSup ?_) x
    intro u hu
    exact ⟨hu.1, fun y hy => hu.2.1 y (hE hjk hy), hu.2.2⟩
  have hW0 : ∀ j x, 0 ≤ W j x := fun j x =>
    ((le_sSup (hF0 j) : (fun _ => (0 : EReal)) ≤ sSup (F j)) x).trans (le_uscRegularization _ x)
  have hWle : ∀ j x, W j x ≤ ((t + 1 : ℝ) : EReal) := by
    intro j x
    refine uscRegularization_le (g := fun _ => ((t + 1 : ℝ) : EReal)) upperSemicontinuous_const
      ?_ x
    intro y
    simp only [sSup_apply]
    exact iSup_le fun f => f.2.2.2 y
  have hWE : ∀ j, ∀ y ∈ E j, sSup (F j) y ≤ 0 := by
    intro j y hy
    simp only [sSup_apply]
    exact iSup_le fun f => f.2.2.1 y hy
  -- each envelope exceeds `t` somewhere
  have hWlarge : ∀ j, ∃ x, (t : EReal) < W j x := by
    intro j
    have hlt : (t : EReal) < extremalHeight ω (E j) := ht2.trans_le (iInf_le _ j)
    obtain ⟨u, hu, hut⟩ := lt_biSup_iff.mp hlt
    obtain ⟨x, hx⟩ := lt_iSup_iff.mp hut
    obtain ⟨xm, m, hum, htm, hmax⟩ := exists_max_coe hu.1 hx
    have htm' : t < m := EReal.coe_lt_coe_iff.mp htm
    set d : ℝ := max 0 (m - (t + 1)) with hd
    have hd0 : 0 ≤ d := le_max_left _ _
    have hvF : (fun y => u y + ((-d : ℝ) : EReal)) ∈ F j := by
      refine ⟨hu.1.add_const (-d), fun y hy => ?_, fun y => ?_⟩
      · have h1 : u y ≤ 0 := hu.2 y hy
        have h2 : ((-d : ℝ) : EReal) ≤ 0 := by exact_mod_cast (by linarith : -d ≤ 0)
        simpa using add_le_add h1 h2
      · calc u y + ((-d : ℝ) : EReal) ≤ (m : EReal) + ((-d : ℝ) : EReal) :=
              add_le_add (hmax y) le_rfl
          _ = ((m + -d : ℝ) : EReal) := by rw [EReal.coe_add]
          _ ≤ ((t + 1 : ℝ) : EReal) := by
              exact_mod_cast (by have := le_max_right 0 (m - (t + 1)); linarith)
    refine ⟨xm, ?_⟩
    calc (t : EReal) < ((m + -d : ℝ) : EReal) := by
          refine EReal.coe_lt_coe_iff.mpr ?_
          rcases le_total 0 (m - (t + 1)) with h | h
          · rw [hd, max_eq_right h]; linarith
          · rw [hd, max_eq_left h]; linarith
      _ = u xm + ((-d : ℝ) : EReal) := by rw [hum, EReal.coe_add]
      _ ≤ sSup (F j) xm := (le_sSup hvF : (fun y => u y + ((-d : ℝ) : EReal)) ≤ sSup (F j)) xm
      _ ≤ W j xm := le_uscRegularization _ xm
  -- a common point where the limit is `≥ t` (compactness)
  have hC : (⋂ j, {x | (t : EReal) ≤ W j x}).Nonempty := by
    refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _
      (fun j x hx => le_trans hx (hWanti x (Nat.le_succ j))) (fun j => ?_)
      (isCompact_univ.of_isClosed_subset
        ((upperSemicontinuous_uscRegularization _).isClosed_preimage (t : EReal))
        (subset_univ _))
      (fun j => (upperSemicontinuous_uscRegularization _).isClosed_preimage (t : EReal))
    obtain ⟨x, hx⟩ := hWlarge j
    exact ⟨x, hx.le⟩
  obtain ⟨x₀, hx₀⟩ := hC
  -- the decreasing limit
  set V : M → EReal := fun x => ⨅ j, W j x with hVdef
  have hVpsh : ThetaPlurisubharmonic ω.form.val V :=
    ThetaPshDecreasingLimit.thetaPlurisubharmonic_iInf_of_antitone (fun j => (hWpsh j).1) hWanti
  have hV0 : ∀ x, 0 ≤ V x := fun x => le_iInf fun j => hW0 j x
  have hVle : ∀ x, V x ≤ ((t + 1 : ℝ) : EReal) := fun x => (iInf_le _ 0).trans (hWle 0 x)
  have hVP : IsThetaPshPotential ω.form.val V :=
    ⟨hVpsh, fun x _ _ hx => ⟨x, hx, ne_bot_of_le_ne_bot EReal.zero_ne_bot (hV0 x)⟩⟩
  have hVx₀ : (t : EReal) ≤ V x₀ := le_iInf fun j => mem_iInter.mp hx₀ j
  -- the exceptional set and a potential with poles on it
  set Neg : ℕ → Set M := fun j => {x | sSup (F j) x < W j x} with hNegdef
  have hNeg : OuterCapacityZero ω (⋃ j, Neg j) :=
    PluripolarOuterCapacity.OuterCapacityZero.iUnion fun j => (hspec j).2
  obtain ⟨ψ, hψ, hψN⟩ :=
    KahlerVolumePositive.exists_isThetaPshPotential_poles_of_outerCapacityZero' hn ω hNeg
  obtain ⟨y₀, -, hy₀⟩ := hψ.2 (Classical.arbitrary M) univ isOpen_univ (mem_univ _)
  obtain ⟨-, b, -, -, hψb⟩ := exists_max_coe hψ (bot_lt_iff_ne_bot.mpr hy₀)
  set ψ' : M → EReal := fun x => ψ x + ((-b : ℝ) : EReal) with hψ'def
  have hψ'P : IsThetaPshPotential ω.form.val ψ' := hψ.add_const (-b)
  have hψ'0 : ∀ x, ψ' x ≤ 0 := by
    intro x
    calc ψ x + ((-b : ℝ) : EReal) ≤ (b : EReal) + ((-b : ℝ) : EReal) := add_le_add (hψb x) le_rfl
      _ = 0 := by rw [← EReal.coe_add]; simp
  have hψ'N : ∀ x ∈ ⋃ j, Neg j, ψ' x = ⊥ := by
    intro x hx
    simp only [hψ'def, hψN x hx, EReal.bot_add]
  -- the height of the union is a real number `r < t`
  have hr0 := zero_le_extremalHeight ω (⋃ j, E j)
  have hrtop : extremalHeight ω (⋃ j, E j) ≠ ⊤ := ne_top_of_lt ht1
  set r : ℝ := (extremalHeight ω (⋃ j, E j)).toReal with hrdef
  have hr : extremalHeight ω (⋃ j, E j) = (r : EReal) :=
    (EReal.coe_toReal hrtop (ne_bot_of_le_ne_bot EReal.zero_ne_bot hr0)).symm
  have hrt : r < t := by rw [hr] at ht1; exact_mod_cast ht1
  have hr0' : 0 ≤ r := by rw [hr] at hr0; exact_mod_cast hr0
  -- off the poles of `ψ'`, the limit is below the height of the union
  have hkey : ∀ x, ψ' x ≠ ⊥ → V x ≤ (r : EReal) := by
    intro x hx
    have hVxtop : V x ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) (hVle x)
    have hVxbot : V x ≠ ⊥ := ne_bot_of_le_ne_bot EReal.zero_ne_bot (hV0 x)
    have hψxtop : ψ' x ≠ ⊤ := ne_top_of_le_ne_top EReal.zero_ne_top (hψ'0 x)
    set a : ℝ := (V x).toReal with ha
    set p : ℝ := (ψ' x).toReal with hp
    have hVa : V x = (a : EReal) := (EReal.coe_toReal hVxtop hVxbot).symm
    have hψp : ψ' x = (p : EReal) := (EReal.coe_toReal hψxtop hx).symm
    have ha0 : 0 ≤ a := by have := hV0 x; rw [hVa] at this; exact_mod_cast this
    have hp0 : p ≤ 0 := by have := hψ'0 x; rw [hψp] at this; exact_mod_cast this
    -- the competitors `(1-ε) V + ε ψ'`
    have hcomp : ∀ ε : ℝ, 0 < ε → ε < 1 → (1 - ε) * a + ε * p ≤ r := by
      intro ε hε0 hε1
      set w := ThetaPshConvexCombination.convexComb (1 - ε) V ψ' with hw
      have hwP : IsThetaPshPotential ω.form.val w :=
        ThetaPshConvexCombination.isThetaPshPotential_convexComb hVP hψ'P (by linarith)
          (by linarith)
      have hε' : (1 - (1 - ε) : ℝ) = ε := by ring
      have hwmem : w ∈ extremalCompetitors ω (⋃ j, E j) := by
        refine ⟨hwP, fun y hy => ?_⟩
        obtain ⟨j, hyj⟩ := mem_iUnion.mp hy
        rw [hw, ThetaPshConvexCombination.convexComb_apply, hε']
        by_cases hyN : y ∈ Neg j
        · have hψy : ψ' y = ⊥ := hψ'N y (mem_iUnion.mpr ⟨j, hyN⟩)
          rw [hψy, EReal.coe_mul_bot_of_pos hε0, EReal.add_bot]
          exact bot_le
        · have hyW : W j y ≤ sSup (F j) y := not_lt.mp hyN
          have hVy : V y ≤ 0 := (iInf_le _ j).trans (hyW.trans (hWE j y hyj))
          have hVy0 : V y = 0 := le_antisymm hVy (hV0 y)
          rw [hVy0, mul_zero, zero_add]
          exact EReal.mul_nonpos_iff.mpr (Or.inl ⟨EReal.coe_nonneg.mpr hε0.le, hψ'0 y⟩)
      have hwx := le_extremalHeight ω hwmem x
      rw [hw, ThetaPshConvexCombination.convexComb_apply, hε', hVa, hψp, hr,
        ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at hwx
      exact_mod_cast hwx
    -- let `ε → 0`
    rw [hVa]
    refine EReal.coe_le_coe_iff.mpr ?_
    by_contra har
    push Not at har
    set ε : ℝ := (a - r) / (2 * (a - p) + 1) with hεdef
    have hden : 0 < 2 * (a - p) + 1 := by linarith
    have hε0 : 0 < ε := div_pos (by linarith) hden
    have hεle : ε * (2 * (a - p) + 1) = a - r := div_mul_cancel₀ _ hden.ne'
    have hε1 : ε < 1 := by
      rw [div_lt_one hden]; linarith
    have := hcomp ε hε0 hε1
    nlinarith
  -- hence `V ≤ r` everywhere, contradicting `V x₀ ≥ t > r`
  have hconst : ThetaPlurisubharmonic ω.form.val (fun _ => (r : EReal)) := by
    simpa using (h0.add_const r).1
  have hqe : QuasiEverywhere (n := n) (fun x => V x ≤ (fun _ => (r : EReal)) x) := by
    refine (quasiPsh_poles_manifoldLocallyPluripolar hψ'P.quasiPshPotential).mono ?_
    intro x hx
    by_contra hne
    exact hx (hkey x hne)
  have hle := ThetaPlurisubharmonic.le_of_quasiEverywhere_le hVpsh hconst hqe x₀
  have : (t : EReal) ≤ (r : EReal) := hVx₀.trans hle
  exact absurd (EReal.coe_le_coe_iff.mp this) (not_le.mpr hrt)

/-- **Outer regularity at pluripolar sets.**  A set of outer capacity zero lies in open sets of
arbitrarily large extremal height. -/
theorem exists_isOpen_lt_extremalHeight (hn : 0 < n) [ConnectedSpace M] [Nonempty M]
    (ω : KahlerBackground n M) {K : Set M} (hK : OuterCapacityZero ω K) (T : ℝ) :
    ∃ U, IsOpen U ∧ K ⊆ U ∧ (T : EReal) < extremalHeight ω U := by
  obtain ⟨ψ, hψ, hψK⟩ :=
    KahlerVolumePositive.exists_isThetaPshPotential_poles_of_outerCapacityZero' hn ω hK
  obtain ⟨y, -, hy⟩ := hψ.2 (Classical.arbitrary M) univ isOpen_univ (mem_univ _)
  have hytop : ψ y ≠ ⊤ := hψ.1.quasiPlurisubharmonic.ne_top y
  set a : ℝ := (ψ y).toReal with ha
  have hψa : ψ y = (a : EReal) := (EReal.coe_toReal hytop hy).symm
  set c : ℝ := a - T - 1 with hc
  refine ⟨{x | ψ x < (c : EReal)},
    hψ.1.quasiPlurisubharmonic.upperSemicontinuous.isOpen_preimage (c : EReal),
    fun x hx => by
      show ψ x < (c : EReal)
      rw [hψK x hx]
      exact EReal.bot_lt_coe c, ?_⟩
  have hmem : (fun x => ψ x + ((-c : ℝ) : EReal)) ∈
      extremalCompetitors ω {x | ψ x < (c : EReal)} := by
    refine ⟨hψ.add_const (-c), fun x (hx : ψ x < (c : EReal)) => ?_⟩
    show ψ x + ((-c : ℝ) : EReal) ≤ 0
    have h1 := EReal.add_lt_add_right_coe hx (-c)
    rw [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] at h1
    exact h1.le
  calc (T : EReal) < ((a + -c : ℝ) : EReal) := EReal.coe_lt_coe_iff.mpr (by linarith)
    _ = ψ y + ((-c : ℝ) : EReal) := by rw [hψa, EReal.coe_add]
    _ ≤ extremalHeight ω {x | ψ x < (c : EReal)} := le_extremalHeight ω hmem y

/-- **Infinite extremal height forces pluripolarity.**  On a compact connected Kähler manifold of
positive dimension, a set `A` with `h(A) = ∞` is pluripolar. -/
theorem manifoldLocallyPluripolar_of_extremalHeight_eq_top (hn : 0 < n) [ConnectedSpace M]
    (ω : KahlerBackground n M) {A : Set M} (hA : extremalHeight ω A = ⊤) :
    ManifoldLocallyPluripolar (n := n) A := by
  classical
  -- the families of sup-normalized competitors which are `≤ -N` on `A`
  set F : ℕ → Set (M → EReal) := fun N => {v | IsThetaPshPotential ω.form.val v ∧
    (∀ x, v x ≤ 0) ∧ ∀ x ∈ A, v x ≤ ((-(N : ℝ) : ℝ) : EReal)} with hFdef
  have hFtouch : ∀ N : ℕ, ∃ v ∈ F N, ∃ x, v x = 0 := by
    intro N
    have hlt : ((N : ℝ) : EReal) < extremalHeight ω A := by rw [hA]; exact EReal.coe_lt_top _
    obtain ⟨u, hu, hut⟩ := lt_biSup_iff.mp hlt
    obtain ⟨x, hx⟩ := lt_iSup_iff.mp hut
    obtain ⟨xm, m, hum, hNm, hmax⟩ := exists_max_coe hu.1 hx
    have hNm' : (N : ℝ) < m := EReal.coe_lt_coe_iff.mp hNm
    refine ⟨fun y => u y + ((-m : ℝ) : EReal), ⟨hu.1.add_const (-m), fun y => ?_, fun y hy => ?_⟩,
      xm, ?_⟩
    · calc u y + ((-m : ℝ) : EReal) ≤ (m : EReal) + ((-m : ℝ) : EReal) :=
            add_le_add (hmax y) le_rfl
        _ = 0 := by rw [← EReal.coe_add]; simp
    · calc u y + ((-m : ℝ) : EReal) ≤ 0 + ((-m : ℝ) : EReal) := add_le_add (hu.2 y hy) le_rfl
        _ ≤ ((-(N : ℝ) : ℝ) : EReal) := by
            rw [zero_add]; exact_mod_cast (by linarith : -m ≤ -(N : ℝ))
    · show u xm + ((-m : ℝ) : EReal) = 0
      rw [hum, ← EReal.coe_add]; simp
  have hFne : ∀ N, (F N).Nonempty := fun N => by
    obtain ⟨v, hv, -⟩ := hFtouch N
    exact ⟨v, hv⟩
  have hspec := fun N => envelope_spec hn ω (hFne N) (fun v (hv : v ∈ F N) => hv.1)
    (C := 0) (fun v (hv : v ∈ F N) x => by simpa using hv.2.1 x)
  set W : ℕ → M → EReal := fun N => uscRegularization (sSup (F N)) with hWdef
  have hWpsh : ∀ N, IsThetaPshPotential ω.form.val (W N) := fun N => (hspec N).1
  have hWanti : ∀ x, Antitone fun N => W N x := by
    intro x N N' hNN'
    refine uscRegularization_mono (sSup_le_sSup ?_) x
    intro v hv
    refine ⟨hv.1, hv.2.1, fun y hy => (hv.2.2 y hy).trans ?_⟩
    have : (N : ℝ) ≤ N' := by exact_mod_cast hNN'
    exact_mod_cast (by linarith : -(N' : ℝ) ≤ -(N : ℝ))
  have hWtouch : ∀ N, ∃ x, ((-(0 : ℝ) : ℝ) : EReal) ≤ W N x := by
    intro N
    obtain ⟨v, hv, x, hvx⟩ := hFtouch N
    refine ⟨x, ?_⟩
    calc ((-(0 : ℝ) : ℝ) : EReal) = v x := by rw [hvx]; simp
      _ ≤ sSup (F N) x := (le_sSup hv : v ≤ sSup (F N)) x
      _ ≤ W N x := le_uscRegularization _ x
  obtain ⟨x₀, hx₀⟩ :=
    ThetaPshAntitoneSupNondegenerate.exists_ne_bot_iInf_of_forall_exists_le hWpsh hWanti hWtouch
  set V : M → EReal := fun x => ⨅ N, W N x with hVdef
  have hVpsh : ThetaPlurisubharmonic ω.form.val V :=
    ThetaPshDecreasingLimit.thetaPlurisubharmonic_iInf_of_antitone (fun N => (hWpsh N).1) hWanti
  have hVP : IsThetaPshPotential ω.form.val V :=
    ThetaPshIdentityPrinciple.isThetaPshPotential_of_exists_ne_bot hVpsh ⟨x₀, hx₀⟩
  -- the exceptional sets
  set Neg : ℕ → Set M := fun N => {x | sSup (F N) x < W N x} with hNegdef
  set S : ℕ → Set M := fun k => Nat.casesOn k {x | V x = ⊥} (fun N => Neg N) with hSdef
  have hS : OuterCapacityZero ω (⋃ k, S k) := by
    refine PluripolarOuterCapacity.OuterCapacityZero.iUnion fun k => ?_
    cases k with
    | zero =>
      exact PluripolarOuterCapacity.outerCapacityZero_of_manifoldLocallyPluripolar ω
        (quasiPsh_poles_manifoldLocallyPluripolar hVP.quasiPshPotential)
    | succ N => exact (hspec N).2
  refine (KahlerVolumePositive.manifoldLocallyPluripolar_of_outerCapacityZero' hn ω hS).mono ?_
  intro x hxA
  by_cases hxN : ∃ N, x ∈ Neg N
  · obtain ⟨N, hN⟩ := hxN
    exact mem_iUnion.mpr ⟨N + 1, hN⟩
  · push Not at hxN
    refine mem_iUnion.mpr ⟨0, ?_⟩
    show V x = ⊥
    rw [EReal.eq_bot_iff_forall_lt]
    intro y
    obtain ⟨N, hN⟩ := exists_nat_gt (-y)
    have hWx : W N x ≤ ((-(N : ℝ) : ℝ) : EReal) := by
      refine (not_lt.mp (hxN N)).trans ?_
      simp only [sSup_apply]
      exact iSup_le fun v => v.2.2.2 x hxA
    calc V x ≤ W N x := iInf_le _ N
      _ ≤ ((-(N : ℝ) : ℝ) : EReal) := hWx
      _ < (y : EReal) := EReal.coe_lt_coe_iff.mpr (by linarith)

/-- **Choquet's theorem for pluripolar sets.**  On a compact connected Kähler manifold of
positive dimension, an analytic (e.g. Borel) set all of whose compact subsets are pluripolar is
pluripolar. -/
theorem manifoldLocallyPluripolar_of_analyticSet (hn : 0 < n) [ConnectedSpace M]
    (ω : KahlerBackground n M) {A : Set M} (hA : AnalyticSet A)
    (hK : ∀ K, IsCompact K → K ⊆ A → ManifoldLocallyPluripolar (n := n) K) :
    ManifoldLocallyPluripolar (n := n) A := by
  rcases isEmpty_or_nonempty M with hM | hM
  · exact manifoldLocallyPluripolar_empty.mono fun x _ => (IsEmpty.false x).elim
  refine manifoldLocallyPluripolar_of_extremalHeight_eq_top hn ω ?_
  by_contra hne
  obtain ⟨T, hAT, -⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_top_iff_ne_top.mpr hne)
  obtain ⟨K, hKc, hKA, hKU⟩ := Choquet.exists_isCompact_subset_forall_isOpen_gt_of_antitone
    (extremalHeight ω) (extremalHeight_antitone ω)
    (fun E hE => iInf_extremalHeight_le_iUnion hn ω hE) hA hAT
  obtain ⟨U, hU, hKU', hTU⟩ := exists_isOpen_lt_extremalHeight hn ω
    (PluripolarOuterCapacity.outerCapacityZero_of_manifoldLocallyPluripolar ω (hK K hKc hKA)) T
  exact lt_asymm (hKU U hU hKU') hTU

/-- A compact complex manifold is a Polish space. -/
theorem polishSpace_of_compact (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] :
    PolishSpace M := by
  have := DiagonalMeasureRegularity.metrizableSpace_of_isComplexManifold n M
  let _ : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  have : CompleteSpace M := complete_of_compact
  infer_instance

/-- **Borel sets of Kähler capacity zero are pluripolar**, on a compact connected Kähler
manifold (every dimension). -/
theorem manifoldLocallyPluripolar_of_measurableSet_of_kahlerCapacity_eq_zero_connected
    [ConnectedSpace M] (ω : KahlerBackground n M) {A : Set M} (hA : MeasurableSet A)
    (h0 : thetaCapacity ω.form (fun _ => 0) A = 0) :
    ManifoldLocallyPluripolar (n := n) A := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hAe : A = ∅ := by
      by_contra hne
      obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr hne
      have hz := isThetaPshPotential_zero ω
      have hle := diagonalPotentialMeasure_le_thetaCapacity hz (le_refl _)
        (fun x => by simp) A
      rw [h0] at hle
      have hcount := (ZeroDimensionalGlobalMixedMass.global_empty_mixed_measure_eq_count
        (M := M) (fun _ => ω.form) (fun _ => fun _ => (0 : EReal)) (fun _ => hz.1)).1
      have hdiag : DiagonalMass.diagonalPotentialMeasure ω.form (fun _ => (0 : EReal)) hz =
          Measure.count := hcount
      rw [hdiag, Measure.count_apply hA] at hle
      have h1 : (1 : ℕ∞) ≤ A.encard := Set.one_le_encard_iff_nonempty.mpr ⟨x, hx⟩
      have h2 : ((A.encard : ℕ∞) : ℝ≥0∞) = 0 := le_antisymm hle zero_le
      have h3 : A.encard = 0 := by exact_mod_cast h2
      rw [h3] at h1
      exact absurd h1 (by norm_num)
    rw [hAe]
    exact manifoldLocallyPluripolar_empty
  · have := polishSpace_of_compact n M
    refine manifoldLocallyPluripolar_of_analyticSet hn ω hA.analyticSet fun K hK hKA => ?_
    exact SGPT.NPP.manifoldLocallyPluripolar_of_isClosed_of_kahlerCapacity_eq_zero_connected ω
      hK.isClosed (le_antisymm (h0 ▸ thetaCapacity_mono hKA) zero_le)

end Compact

end SGPT.NPP.ChoquetPluripolar

namespace SGPT.NPP

open Set MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open ThetaCapacity OpensRestriction OpensRestrictionMeasure
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- On a compact Kähler manifold (not necessarily connected, any dimension), a **Borel** set of
Kähler capacity zero is pluripolar in the source sense (`def:pluripolarsets`). -/
theorem locallyPluripolar_of_measurableSet_of_kahlerCapacity_eq_zero
    (ω : KahlerBackground n M) {A : Set M} (hA : MeasurableSet A)
    (h0 : thetaCapacity ω.form (fun _ => 0) A = 0) :
    (ofFixedModel n M).LocallyPluripolar A := by
  classical
  let _ : LocallyConnectedSpace M := OpensRestrictionMeasure.locallyConnectedSpace n M
  have hcomp : ∀ x : M,
      (ofFixedModel n M).LocallyPluripolar (A ∩ (componentOpens x : Set M)) := by
    intro x
    let U := componentOpens x
    have hU : IsClopen (U : Set M) := isClopen_componentOpens x
    have hAU : MeasurableSet ((Subtype.val : U → M) ⁻¹' A) := measurable_subtype_coe hA
    have hcapU := ActualClopenCapacityRestriction.thetaCapacity_restrict_le
      (n := n) (M := M) ω U hU hA
    change thetaCapacity (restrictKahler U ω).form (fun _ => 0)
      ((Subtype.val : U → M) ⁻¹' A) ≤ thetaCapacity ω.form (fun _ => 0) A at hcapU
    rw [h0] at hcapU
    have h0U : thetaCapacity (restrictKahler U ω).form (fun _ => 0)
        ((Subtype.val : U → M) ⁻¹' A) = 0 := le_antisymm hcapU zero_le
    have hpolU :=
      ChoquetPluripolar.manifoldLocallyPluripolar_of_measurableSet_of_kahlerCapacity_eq_zero_connected
        (M := U) (restrictKahler U ω) hAU h0U
    have himg := manifoldLocallyPluripolar_image_val (n := n) hU hpolU
    have hset : (Subtype.val '' ((Subtype.val : U → M) ⁻¹' A) : Set M) =
        A ∩ (U : Set M) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨hz, z.2⟩
      · rintro ⟨hyA, hyU⟩
        exact ⟨⟨y, hyU⟩, hyA, rfl⟩
    rw [hset] at himg
    exact source_locallyPluripolar_of_manifold himg
  intro x
  let U := componentOpens x
  have hUo : IsOpen (U : Set M) := U.isOpen
  obtain ⟨W, hW, hxW, w, hw, hpole⟩ := hcomp x x
  refine ⟨W ∩ U, hW.inter hUo, ⟨hxW, mem_componentOpens x⟩, w,
    hw.mono_open hW (hW.inter hUo) inter_subset_left, ?_⟩
  rintro y ⟨hyA, hyW, hyU⟩
  exact hpole y ⟨⟨hyA, hyU⟩, hyW⟩

/-- **Source `thm:pp_cap`, (2) ⇒ (1), for every Borel set**: on a compact Kähler manifold, with
`θ` a closed smooth real `(1,1)`-form in a big class, a Borel set `A` with `Cap_θ(A) = 0` is
pluripolar. -/
theorem locallyPluripolar_of_measurableSet_of_sourceThetaCapacity_eq_zero
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {A : Set M} (hA : MeasurableSet A) (h0 : sourceThetaCapacity θ A = 0) :
    (ofFixedModel n M).LocallyPluripolar A :=
  locallyPluripolar_of_measurableSet_of_kahlerCapacity_eq_zero ω hA
    (kahlerCapacity_eq_zero_of_source_capacity_eq_zero ω θ hbig hA h0)

/-- **Source `thm:pp_cap`**: on a compact Kähler manifold, with `θ` a closed smooth real
`(1,1)`-form in a big class, a Borel set `A ⊆ X` is pluripolar iff `Cap_θ(A) = 0`. -/
theorem locallyPluripolar_iff_sourceThetaCapacity_eq_zero
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {A : Set M} (hA : MeasurableSet A) :
    (ofFixedModel n M).LocallyPluripolar A ↔ sourceThetaCapacity θ A = 0 :=
  ⟨sourceThetaCapacity_eq_zero_of_locallyPluripolar θ,
    locallyPluripolar_of_measurableSet_of_sourceThetaCapacity_eq_zero ω θ hbig hA⟩

end SGPT.NPP
