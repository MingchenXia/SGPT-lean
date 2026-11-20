import SGPT.Foundations.Analysis.Pending.PluripolarOuterCapacity
import SGPT.Foundations.Analysis.Pending.ClosedNullOuterCapacity
import SGPT.Foundations.Analysis.Pending.NegligibleSetNotCharged
import SGPT.Foundations.Analysis.Pending.ThetaCapacityQuasiContinuity
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.IEnvelopeStrongOpenness

set_option autoImplicit false

/-!
# Negligible sets are pluripolar (step C5 of I-0510)

**Bedford--Taylor's theorem** (Bedford--Taylor 1982, Thm 7.1; Guedj--Zeriahi 2005, §5): on a
compact connected Kähler manifold, for a sequence `u_j` of `θ`-PSH potentials bounded above by one
real constant, the negligible set `{(sup_j u_j)^* > sup_j u_j}` is `ManifoldLocallyPluripolar`.
This is the predicate `RooftopObstacleQuasiEverywhere.NegligibleSetsPluripolar`, input (b) of
Xia's (2.20) (`negligibleSetsPluripolar`).

*Proof.*
1. `θ ≤ Aω` for some `A > 0` (`KahlerDomination`), so the `u_j` are `Aω`-PSH; work with the
   Kähler form `Ω = Aω` and its capacity `Cap_Ω`.
2. Truncation: the negligible set of `(u_j)` lies in the union over `k` of those of the bounded
   families `max(u_j, -k)`, and running maxima make each family increasing.
3. Bounded increasing `v_j` (`outerCapacityZero_negligible_of_monotone`): by quasi-continuity
   (`ThetaCapacityQuasiContinuity.exists_isOpen_thetaCapacity_lt_continuousOn_compl`, applied to
   `V^*` and every `v_j`) there is an open `G` of small capacity off which all are continuous; the
   negligible set off `G` is the countable union of the CLOSED sets
   `F_m = {x ∉ G | v_j + 1/(m+1) ≤ V^* for all j}`; bounded potentials do not charge them
   (`NegligibleSetNotCharged`), so they have outer capacity zero
   (`ClosedNullOuterCapacity.outerCapacityZero_of_isClosed`).  Hence the negligible set has outer
   capacity zero.
4. Outer capacity zero ⇒ pluripolar (step C1 without the volume hypothesis,
   `KahlerVolumePositive.manifoldLocallyPluripolar_of_outerCapacityZero'`).  In dimension `0` the
   manifold is discrete and the negligible set is empty.
-/

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace SGPT.Foundations.Analysis.Pending.NegligibleSetsPluripolarProof

noncomputable section

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ThetaCapacity
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
open SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy
open SGPT.Foundations.Analysis.Pending.PluripolarCapacityZero
open SGPT.Foundations.Analysis.Pending.KahlerVolumePositive
open SGPT.Foundations.Analysis.Pending.PluripolarOuterCapacity
open SGPT.Foundations.Analysis.Pending.RooftopObstacleQuasiEverywhere

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The regularized supremum of a sequence of `θ`-PSH potentials bounded above by one real
constant is `θ`-PSH. -/
theorem isThetaPshPotential_uscRegularization_iSup_of_le {θ : SmoothRealForm n M 2}
    {v : ℕ → M → EReal} (hv : ∀ j, IsThetaPshPotential θ (v j)) {b : ℝ}
    (hb : ∀ j x, v j x ≤ (b : EReal)) :
    IsThetaPshPotential θ (uscRegularization (⨆ j, v j)) := by
  set v' : ℕ → M → EReal := fun j x => v j x + ((-b : ℝ) : EReal) with hv'def
  have hv' : ∀ j, IsThetaPshPotential θ (v' j) := fun j => (hv j).add_const (-b)
  have hv'0 : ∀ j, v' j ≤ 0 := fun j x => by
    simp only [hv'def]
    calc v j x + ((-b : ℝ) : EReal) ≤ (b : EReal) + ((-b : ℝ) : EReal) := add_le_add (hb j x) le_rfl
      _ = 0 := by rw [← EReal.coe_add]; simp
  have hpsh := thetaPlurisubharmonic_uscRegularization_sSup (θ := θ) (F := range v')
    (hv 0).1.hasSmoothLocalPotentials ⟨v' 0, mem_range_self 0⟩
    (by rintro _ ⟨j, rfl⟩; exact hv' j) (by rintro _ ⟨j, rfl⟩; exact hv'0 j)
  rw [sSup_range] at hpsh
  have hsup : (⨆ j, v' j) = fun x => (⨆ j, v j) x + ((-b : ℝ) : EReal) := by
    funext x
    simp only [iSup_apply, hv'def]
    exact (NegligibleSetNotCharged.iSup_add_coe _ _).symm
  rw [hsup, uscRegularization_add_coe_const] at hpsh
  have hnd : LocallyNondegenerate (uscRegularization (⨆ j, v j)) := by
    refine (hv 0).2.mono fun x => ?_
    exact (le_iSup (fun j => v j x) 0).trans (by rw [← iSup_apply]; exact le_uscRegularization _ x)
  have hfin : IsThetaPshPotential θ
      (fun x => uscRegularization (⨆ j, v j) x + ((-b : ℝ) : EReal)) :=
    ⟨hpsh, fun x U hU hx => by
      obtain ⟨y, hy, hne⟩ := hnd x U hU hx
      refine ⟨y, hy, fun h => ?_⟩
      rcases EReal.add_eq_bot_iff.mp h with h' | h'
      · exact hne h'
      · exact EReal.coe_ne_bot _ h'⟩
  have := hfin.add_const b
  convert this using 1
  funext x
  rw [add_assoc, ← EReal.coe_add]
  simp

/-- In dimension `0` the negligible set of any family is empty: the manifold is discrete. -/
theorem uscRegularization_le_of_dim_zero {N : Type*} [TopologicalSpace N]
    [ChartedSpace (ComplexModel 0) N] (f : N → EReal) (x : N) :
    uscRegularization f x ≤ f x := by
  set e := chartAt (ComplexModel 0) x
  have hsrc : e.source ⊆ {x} := by
    intro y hy
    have hx : x ∈ e.source := mem_chart_source (ComplexModel 0) x
    have heq : e y = e x := by
      ext i
      exact i.elim0
    exact e.injOn hy hx heq
  have hnhds : ({x} : Set N) ∈ 𝓝 x :=
    Filter.mem_of_superset (e.open_source.mem_nhds (mem_chart_source (ComplexModel 0) x)) hsrc
  refine (uscRegularization_le_localSup f hnhds).trans ?_
  exact iSup_le fun y => iSup_le fun hy => by rw [mem_singleton_iff.mp hy]

theorem OuterCapacityZero.mono [CompactSpace M] [MeasurableSpace M]
    {omega : KahlerBackground n M} {E F : Set M} (hE : OuterCapacityZero omega E)
    (hFE : F ⊆ E) : OuterCapacityZero omega F := fun ε hε => by
  obtain ⟨G, hG, hEG, hcap⟩ := hE ε hε
  exact ⟨G, hG, hFE.trans hEG, hcap⟩

section Compact

variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **Bounded increasing case.**  The negligible set of an increasing, uniformly bounded sequence
of `Ω`-PSH potentials has outer capacity zero. -/
theorem outerCapacityZero_negligible_of_monotone (hn : 0 < n) (Ω : KahlerBackground n M)
    {v : ℕ → M → EReal} (hv : ∀ j, IsThetaPshPotential Ω.form.val (v j)) {a b : ℝ}
    (hvb : ∀ j x, (a : EReal) ≤ v j x ∧ v j x ≤ (b : EReal)) (hmono : Monotone v) :
    OuterCapacityZero Ω {x | (⨆ j, v j) x < uscRegularization (⨆ j, v j) x} := by
  classical
  set θ : ClosedRealOneOneForm n M := Ω.form with hθ
  set Vs : M → EReal := uscRegularization (⨆ j, v j) with hVsdef
  have hV : IsThetaPshPotential θ.val Vs :=
    isThetaPshPotential_uscRegularization_iSup_of_le hv (fun j x => (hvb j x).2)
  have hsupv : ∀ x, (⨆ j, v j) x = ⨆ j, v j x := fun x => iSup_apply
  have hle_sup : ∀ j x, v j x ≤ (⨆ j, v j) x := fun j x => by
    rw [hsupv]; exact le_iSup (fun j => v j x) j
  have hsup_le : ∀ x, (⨆ j, v j) x ≤ Vs x := fun x => le_uscRegularization _ x
  have hVle : ∀ x, Vs x ≤ (b : EReal) := fun x =>
    uscRegularization_le (g := fun _ => (b : EReal)) upperSemicontinuous_const
      (fun y => by rw [hsupv]; exact iSup_le fun j => (hvb j y).2) x
  have hVge : ∀ x, (a : EReal) ≤ Vs x := fun x =>
    (hvb 0 x).1.trans ((hle_sup 0 x).trans (hsup_le x))
  have hvfin : ∀ k y, v k y ≠ ⊤ ∧ v k y ≠ ⊥ := fun k y =>
    ⟨ne_top_of_le_ne_top (EReal.coe_ne_top b) (hvb k y).2,
      ne_bot_of_le_ne_bot (EReal.coe_ne_bot a) (hvb k y).1⟩
  have hVfin : ∀ y, Vs y ≠ ⊤ ∧ Vs y ≠ ⊥ := fun y =>
    ⟨ne_top_of_le_ne_top (EReal.coe_ne_top b) (hVle y),
      ne_bot_of_le_ne_bot (EReal.coe_ne_bot a) (hVge y)⟩
  set N : Set M := {x | (⨆ j, v j) x < Vs x} with hNdef
  have hNnull : ∀ (w : M → EReal) (hw : IsThetaPshPotential θ.val w),
      IsBoundedPotential w → diagonalPotentialMeasure θ w hw N = 0 := fun w hw hwb =>
    NegligibleSetNotCharged.diagonalPotentialMeasure_negligible_eq_zero hw hwb hv hvb hmono hV
  intro ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  -- quasi-continuity of `V^*` and of every `v_j` off one open set of small capacity
  set F : ℕ → M → EReal := fun i => Nat.casesOn i Vs (fun j => v j) with hFdef
  have hF : ∀ i, IsThetaPshPotential θ.val (F i) ∧ IsBoundedPotential (F i) := by
    intro i
    cases i with
    | zero => exact ⟨hV, a, b, fun x => ⟨hVge x, hVle x⟩⟩
    | succ j => exact ⟨hv j, a, b, hvb j⟩
  obtain ⟨ε', hε'pos, hε'sum⟩ := ENNReal.exists_pos_sum_of_countable hε2.ne' ℕ
  choose G hGo hGcap hGcont using fun i =>
    ThetaCapacityQuasiContinuity.exists_isOpen_thetaCapacity_lt_continuousOn_compl
      (hF i).1 (hF i).2 (V := fun _ => 0) (c := 0) (d := 0) le_rfl (fun _ => by simp)
      (eps := (ε' i : ℝ)) (by exact_mod_cast hε'pos i)
  set G0 : Set M := ⋃ i, G i with hG0def
  have hG0o : IsOpen G0 := isOpen_iUnion hGo
  have hG0cap : thetaCapacity θ (fun _ => 0) G0 < ε / 2 := by
    calc thetaCapacity θ (fun _ => 0) G0 ≤ ∑' i, thetaCapacity θ (fun _ => 0) (G i) :=
          thetaCapacity_iUnion_le _ _ _
      _ ≤ ∑' i, (ε' i : ℝ≥0∞) := ENNReal.tsum_le_tsum fun i => by
          have := (hGcap i).le
          rwa [ENNReal.ofReal_coe_nnreal] at this
      _ < ε / 2 := hε'sum
  have hcont : ∀ i, ContinuousOn (fun y => (F i y).toReal) G0ᶜ := fun i =>
    (hGcont i).mono (compl_subset_compl.mpr (subset_iUnion G i))
  have hcV : ContinuousOn (fun y => (Vs y).toReal) G0ᶜ := hcont 0
  have hcv : ∀ j, ContinuousOn (fun y => (v j y).toReal) G0ᶜ := fun j => hcont (j + 1)
  -- the closed pieces of the negligible set
  set Fm : ℕ → Set M := fun m => ⋂ j, {x | x ∈ G0ᶜ ∧
    (v j x).toReal + 1 / ((m : ℝ) + 1) ≤ (Vs x).toReal} with hFmdef
  have hFmc : ∀ m, IsClosed (Fm m) := fun m => isClosed_iInter fun j =>
    hG0o.isClosed_compl.isClosed_le ((hcv j).add continuousOn_const) hcV
  have hFmN : ∀ m, Fm m ⊆ N := by
    intro m x hx
    have hx' : ∀ j, (v j x).toReal + 1 / ((m : ℝ) + 1) ≤ (Vs x).toReal := fun j =>
      (mem_iInter.mp hx j).2
    have hδ : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    show (⨆ j, v j) x < Vs x
    rw [hsupv]
    calc ⨆ j, v j x ≤ (((Vs x).toReal - 1 / ((m : ℝ) + 1) : ℝ) : EReal) := iSup_le fun j => by
          rw [← EReal.coe_toReal (hvfin j x).1 (hvfin j x).2]
          exact EReal.coe_le_coe_iff.mpr (by linarith [hx' j])
      _ < ((Vs x).toReal : EReal) := EReal.coe_lt_coe_iff.mpr (by linarith)
      _ = Vs x := EReal.coe_toReal (hVfin x).1 (hVfin x).2
  have hFmoc : ∀ m, OuterCapacityZero Ω (Fm m) := fun m =>
    ClosedNullOuterCapacity.outerCapacityZero_of_isClosed hn Ω (hFmc m)
      fun w hw hwb => measure_mono_null (hFmN m) (hNnull w hw hwb)
  obtain ⟨O, hOo, hFO, hOcap⟩ := OuterCapacityZero.iUnion hFmoc (ε / 2) hε2
  refine ⟨G0 ∪ O, hG0o.union hOo, fun x hx => ?_, ?_⟩
  · by_cases hxG : x ∈ G0
    · exact Or.inl hxG
    · right
      have hxN : (⨆ j, v j) x < Vs x := hx
      have hsfin : (⨆ j, v j) x ≠ ⊤ ∧ (⨆ j, v j) x ≠ ⊥ :=
        ⟨ne_top_of_le_ne_top (hVfin x).1 (hsup_le x),
          ne_bot_of_le_ne_bot (hvfin 0 x).2 (hle_sup 0 x)⟩
      have hlt : ((⨆ j, v j) x).toReal < (Vs x).toReal := by
        have h := hxN
        rw [← EReal.coe_toReal hsfin.1 hsfin.2, ← EReal.coe_toReal (hVfin x).1 (hVfin x).2] at h
        exact EReal.coe_lt_coe_iff.mp h
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
      refine hFO (mem_iUnion.mpr ⟨m, mem_iInter.mpr fun j => ⟨hxG, ?_⟩⟩)
      have hk : (v j x).toReal ≤ ((⨆ j, v j) x).toReal :=
        EReal.toReal_le_toReal (hle_sup j x) (hvfin j x).2 hsfin.1
      linarith
  · calc thetaCapacity θ (fun _ => 0) (G0 ∪ O)
        ≤ thetaCapacity θ (fun _ => 0) G0 + thetaCapacity θ (fun _ => 0) O :=
          thetaCapacity_union_le _ _ _ _
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hG0cap hOcap
      _ = ε := ENNReal.add_halves ε

omit [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- A finite running maximum of `θ`-PSH potentials is `θ`-PSH. -/
theorem isThetaPshPotential_runningMax {θ : SmoothRealForm n M 2} {s : ℕ → M → EReal}
    (hs : ∀ j, IsThetaPshPotential θ (s j)) : ∀ k, IsThetaPshPotential θ (runningMax s k)
  | 0 => hs 0
  | k + 1 => IsThetaPshPotential.max (isThetaPshPotential_runningMax hs k) (hs (k + 1))

/-- **The negligible set of a sequence of `Ω`-PSH potentials bounded above has outer capacity
zero.** -/
theorem outerCapacityZero_negligible (hn : 0 < n) (Ω : KahlerBackground n M)
    {u : ℕ → M → EReal} (hu : ∀ j, IsThetaPshPotential Ω.form.val (u j)) {C : ℝ}
    (huC : ∀ j x, u j x ≤ (C : EReal)) :
    OuterCapacityZero Ω {x | (⨆ j, u j) x < uscRegularization (⨆ j, u j) x} := by
  classical
  set θ : ClosedRealOneOneForm n M := Ω.form with hθ
  have h0 := isThetaPshPotential_zero Ω
  -- the truncated families and their running maxima
  set w : ℕ → ℕ → M → EReal := fun k j x => max (u j x) (((-(k : ℝ)) : ℝ) : EReal) with hwdef
  have hconst : ∀ k : ℕ, IsThetaPshPotential θ.val (fun _ => (((-(k : ℝ)) : ℝ) : EReal)) :=
    fun k => by simpa only [zero_add] using h0.add_const (-(k : ℝ))
  have hw : ∀ k j, IsThetaPshPotential θ.val (w k j) := fun k j => IsThetaPshPotential.max (hu j) (hconst k)
  set v : ℕ → ℕ → M → EReal := fun k => runningMax (w k) with hvdef
  have hv : ∀ k j, IsThetaPshPotential θ.val (v k j) := fun k =>
    isThetaPshPotential_runningMax (hw k)
  have hvb : ∀ (k j : ℕ) (x : M), (((-(k : ℝ)) : ℝ) : EReal) ≤ v k j x ∧
      v k j x ≤ ((max C (-(k : ℝ)) : ℝ) : EReal) := by
    intro k j x
    refine ⟨(le_max_right _ _).trans (le_runningMax (w k) 0 x |>.trans ?_), ?_⟩
    · exact runningMax_monotone (w k) (Nat.zero_le j) x
    · refine runningMax_apply_le (s := w k) (x := x) (fun i => ?_) j
      exact max_le ((huC i x).trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _)))
        (EReal.coe_le_coe_iff.mpr (le_max_right _ _))
  have hvmono : ∀ k, Monotone (v k) := fun k => runningMax_monotone (w k)
  have hsupvw : ∀ k, (⨆ j, v k j) = ⨆ j, w k j := fun k => by
    funext x
    simp only [iSup_apply, hvdef]
    exact iSup_runningMax (w k) x
  have hk : ∀ k, OuterCapacityZero Ω
      {x | (⨆ j, w k j) x < uscRegularization (⨆ j, w k j) x} := fun k => by
    have := outerCapacityZero_negligible_of_monotone hn Ω (hv k) (hvb k) (hvmono k)
    rwa [hsupvw k] at this
  refine OuterCapacityZero.mono (OuterCapacityZero.iUnion hk) fun x hx => ?_
  have hx' : (⨆ j, u j) x < uscRegularization (⨆ j, u j) x := hx
  have hSbot : uscRegularization (⨆ j, u j) x ≠ ⊥ := ne_bot_of_gt hx'
  have hStop : uscRegularization (⨆ j, u j) x ≠ ⊤ := by
    refine ne_top_of_le_ne_top (EReal.coe_ne_top C) ?_
    exact uscRegularization_le (g := fun _ => (C : EReal)) upperSemicontinuous_const
      (fun y => by rw [iSup_apply]; exact iSup_le fun j => huC j y) x
  obtain ⟨k, hk'⟩ := exists_nat_gt (-(uscRegularization (⨆ j, u j) x).toReal)
  refine mem_iUnion.mpr ⟨k, ?_⟩
  show (⨆ j, w k j) x < uscRegularization (⨆ j, w k j) x
  have hkS : (((-(k : ℝ)) : ℝ) : EReal) < uscRegularization (⨆ j, u j) x := by
    rw [← EReal.coe_toReal hStop hSbot]
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  have hmono_reg : uscRegularization (⨆ j, u j) x ≤ uscRegularization (⨆ j, w k j) x :=
    uscRegularization_mono (fun y => by
      simp only [iSup_apply]
      exact iSup_mono fun j => le_max_left _ _) x
  refine lt_of_lt_of_le ?_ hmono_reg
  have hwsup : (⨆ j, w k j) x = max ((⨆ j, u j) x) (((-(k : ℝ)) : ℝ) : EReal) := by
    simp only [iSup_apply, hwdef]
    refine le_antisymm (iSup_le fun j => max_le_max (le_iSup (fun j => u j x) j) le_rfl)
      (max_le (iSup_mono fun j => le_max_left _ _) (le_iSup_of_le 0 (le_max_right _ _)))
  rw [hwsup]
  exact max_lt hx' hkS

end Compact

/-- **Bedford--Taylor: negligible sets are pluripolar** — the predicate
`RooftopObstacleQuasiEverywhere.NegligibleSetsPluripolar θ` holds for every smooth closed real
`(1,1)`-form `θ` on a compact connected Kähler manifold (every dimension; no measurable
structure in the statement).  Input (b) of Xia's (2.20). -/
theorem negligibleSetsPluripolar [CompactSpace M] [ConnectedSpace M]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M) :
    NegligibleSetsPluripolar theta.val := by
  intro u C hu huC
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine manifoldLocallyPluripolar_empty.mono fun x hx => ?_
    exact hx (uscRegularization_le_of_dim_zero _ x)
  · borelize M
    obtain ⟨A, hA, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omega (-theta)
    set Ω : KahlerBackground n M := KahlerBackground.smul hA omega with hΩ
    have hz : ThetaPlurisubharmonic (-theta + A • omega.form).val (fun _ => 0) :=
      ((LocalPotentials.isThetaPshPotential_zero_iff _).mpr hsemi).1
    have hform : theta + (-theta + A • omega.form) = Ω.form := by
      rw [hΩ, KahlerBackground.smul_form]
      abel
    have hu' : ∀ j, IsThetaPshPotential Ω.form.val (u j) := fun j => by
      have := LocalPotentials.isThetaPshPotential_add_of_zero (hu j) hz
      rwa [hform] at this
    have h := outerCapacityZero_negligible hn Ω hu' huC
    refine (manifoldLocallyPluripolar_of_outerCapacityZero' hn Ω h).mono fun x hx => ?_
    exact not_le.mp hx

end

end SGPT.Foundations.Analysis.Pending.NegligibleSetsPluripolarProof
