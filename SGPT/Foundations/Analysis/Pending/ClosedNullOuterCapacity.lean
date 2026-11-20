import SGPT.Foundations.Analysis.Pending.PluripolarCapacityZero
import SGPT.Foundations.Analysis.Pending.ThetaCapacitySublevel
import SGPT.Foundations.Analysis.Pending.IncreasingLimitOpenMeasure

set_option autoImplicit false

/-!
# A closed set not charged by bounded potentials has outer capacity zero (step C4a of I-0510)

On a compact Kähler manifold `(M, ω)` of positive dimension, let `F` be a closed set such that
`(ω + ddᶜw)ⁿ(F) = 0` for every bounded `ω`-PSH potential `w` (equivalently `Cap_ω(F) = 0`).
Then `F` has *outer* capacity zero (`outerCapacityZero_of_isClosed`): for every `ε > 0` there is
an open `G ⊇ F` with `Cap_ω(G) < ε`.  This is the outer regularity of the Monge--Ampère capacity
at closed null sets (Bedford--Taylor 1982, §6; Guedj--Zeriahi 2005, §3), proved here without
the relative extremal function.

*Proof.*  Fix `t > 1` with `(1 - (1 - 1/t)ⁿ) ∫ωⁿ < ε/2` and put `S = 3t`.  With cut-offs
`g_l = max(0, 1 - (l+1) d(·, F))` (continuous, `= 1` on `F`, decreasing in `l`, supported in
`C_l = {d(·, F) ≤ 1/(l+1)}`) let `u_l = P_ω(-S g_l)` be the envelopes of the continuous
obstacles; they increase in `l`, `-S ≤ u_l ≤ -S g_l`, and their regularized limit `U` is a
bounded `ω`-PSH potential, so `(ω + ddᶜU)ⁿ(F) = 0` and hence `(ω + ddᶜU)ⁿ(C_m)` is small for some
`m`.  All these potentials are bounded, so they have the same total mass `∫ωⁿ`; the open-set
semicontinuity along increasing sequences
(`IncreasingLimitOpenMeasure.diagonalPotentialMeasure_isOpen_le_liminf`, applied to `M ∖ C_m`)
then makes `(ω + ddᶜu_l)ⁿ(C_m)` small for some `l ≥ m`.  By the comparison principle
(`ThetaCapacitySublevel.diagonalPotentialMeasure_lt_le`, against the constant `-t`) and the
contact concentration of continuous-obstacle envelopes, `ωⁿ{u_l < -t}` is at most that
measure, and the Guedj--Zeriahi sublevel estimate (`ThetaCapacitySublevel.thetaCapacity_sublevel_le`)
gives `Cap_ω{u_l < -2t} < ε`.  The open set `{u_l < -2t}` contains `F`, where `u_l ≤ -S = -3t`.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.ClosedNullOuterCapacity

noncomputable section

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ThetaCapacity
open SGPT.Foundations.Analysis.Pending.ThetaCapacitySublevel
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
open SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy
open SGPT.Foundations.Analysis.Pending.PluripolarCapacityZero

/-- The tolerance `1 - (1 - 1/t)ⁿ` can be made arbitrarily small. -/
theorem exists_one_lt_sublevel_tolerance (n : ℕ) {vol ε : ℝ≥0∞} (hvol : vol ≠ ⊤) (hε : 0 < ε) :
    ∃ t : ℝ, 1 < t ∧ ENNReal.ofReal (1 - (1 - t⁻¹) ^ n) * vol < ε := by
  have h1 : Tendsto (fun k : ℕ => ((k : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  have h2 : Tendsto (fun k : ℕ => 1 - (1 - ((k : ℝ) + 2)⁻¹) ^ n) atTop (𝓝 0) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub h1).pow n
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  have h3 : Tendsto (fun k : ℕ => ENNReal.ofReal (1 - (1 - ((k : ℝ) + 2)⁻¹) ^ n) * vol) atTop
      (𝓝 0) := by
    have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h2) (Or.inr hvol)
    simpa using this
  obtain ⟨k, hk⟩ := (h3.eventually (gt_mem_nhds hε)).exists
  exact ⟨(k : ℝ) + 2, by linarith [Nat.cast_nonneg (α := ℝ) k], hk⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **Outer regularity at closed null sets.**  A closed set that carries no Monge--Ampère mass
of any bounded `ω`-PSH potential has outer capacity zero. -/
theorem outerCapacityZero_of_isClosed (hn : 0 < n) (omega : KahlerBackground n M)
    {F : Set M} (hF : IsClosed F)
    (hF0 : ∀ (w : M → EReal) (hw : IsThetaPshPotential omega.form.val w),
      IsBoundedPotential w → diagonalPotentialMeasure omega.form w hw F = 0) :
    OuterCapacityZero omega F := by
  classical
  intro ε hε
  rcases F.eq_empty_or_nonempty with rfl | hFne
  · exact ⟨∅, isOpen_empty, subset_rfl, by simpa using hε⟩
  have : Nonempty M := ⟨hFne.some⟩
  have := DiagonalMeasureRegularity.metrizableSpace_of_isComplexManifold n M
  let _ : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  set θ : ClosedRealOneOneForm n M := omega.form with hθ
  have h0 := isThetaPshPotential_zero omega
  have hbig := isBigClass_kahler omega
  set vol : ℝ≥0∞ := diagonalPotentialMass θ (fun _ => 0) h0 with hvoldef
  have hvolfin : vol ≠ ⊤ :=
    (GlobalNonPluripolar.globalMixedMeasure_apply_lt_top omega (fun _ : Fin n => h0.1) _).ne
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨t, ht1, htε⟩ := exists_one_lt_sublevel_tolerance n hvolfin hε2
  have ht0 : 0 < t := lt_trans zero_lt_one ht1
  set S : ℝ := 3 * t with hSdef
  have hS : 0 < S := by positivity
  -- the cut-offs
  set g : ℕ → M → ℝ := fun l x => max 0 (1 - ((l : ℝ) + 1) * infDist x F) with hgdef
  have hgc : ∀ l, Continuous (g l) := fun l =>
    continuous_const.max (continuous_const.sub (continuous_const.mul (continuous_infDist_pt _)))
  have hg0 : ∀ l x, 0 ≤ g l x := fun l x => le_max_left _ _
  have hg1 : ∀ l x, g l x ≤ 1 := fun l x => max_le zero_le_one (by
    have : 0 ≤ ((l : ℝ) + 1) * infDist x F := mul_nonneg (by positivity) infDist_nonneg
    linarith)
  have hgF : ∀ l x, x ∈ F → g l x = 1 := fun l x hx => by
    simp [hgdef, infDist_zero_of_mem hx]
  have hganti : ∀ x, Antitone fun l => g l x := by
    intro x l l' hll'
    refine max_le_max le_rfl (sub_le_sub_left (mul_le_mul_of_nonneg_right ?_ infDist_nonneg) _)
    have : (l : ℝ) ≤ l' := by exact_mod_cast hll'
    linarith
  have hgpos : ∀ l x, 0 < g l x → infDist x F ≤ 1 / ((l : ℝ) + 1) := by
    intro l x hx
    have hpos : 0 < 1 - ((l : ℝ) + 1) * infDist x F := by
      by_contra h
      push Not at h
      have : g l x = 0 := max_eq_left h
      linarith
    rw [le_div_iff₀ (by positivity)]
    linarith
  -- the obstacles and their envelopes
  set f : ℕ → M → ℝ := fun l x => -S * g l x with hfdef
  have hfc : ∀ l, Continuous (f l) := fun l => continuous_const.mul (hgc l)
  have hfS : ∀ l x, -S ≤ f l x := fun l x => by
    simp only [hfdef]; nlinarith [hg1 l x]
  have hfmono : ∀ x, Monotone fun l => f l x := fun x l l' hll' => by
    simp only [hfdef]
    nlinarith [hganti x hll']
  have hfF : ∀ l x, x ∈ F → f l x = -S := fun l x hx => by simp [hfdef, hgF l x hx]
  set u : ℕ → M → EReal := fun l => rooftopEnvelope θ.val (fun x => (f l x : EReal)) with hudef
  have hu : ∀ l, IsThetaPshPotential θ.val (u l) := fun l =>
    ContinuousObstacleEnvelopeContact.isThetaPshPotential_rooftopEnvelope_of_continuous
      hn θ hbig (hfc l)
  have hule : ∀ l x, u l x ≤ (f l x : EReal) := fun l x =>
    ContinuousObstacleEnvelopeContact.rooftopEnvelope_le_of_continuous (hfc l)
      (ContinuousObstacleEnvelopeContact.rooftopCompetitors_nonempty_of_isBigClass hn θ hbig
        (hfc l)) (hu l).1 x
  have huge : ∀ l x, ((-S : ℝ) : EReal) ≤ u l x := by
    intro l
    have hc : IsThetaPshPotential θ.val
        (fun x => (fun _ => (0 : EReal)) x + ((-S : ℝ) : EReal)) := h0.add_const (-S)
    have := le_rooftopEnvelope hc (quasiEverywhere_of_forall fun x => by
      simp only [zero_add]
      exact EReal.coe_le_coe_iff.mpr (hfS l x))
    intro x
    simpa only [zero_add] using this x
  have hu0 : ∀ l, u l ≤ fun _ => 0 := fun l x =>
    (hule l x).trans (EReal.coe_nonpos.mpr (by
      simp only [hfdef]; nlinarith [hg0 l x]))
  have humono : Monotone u := fun l l' hll' x =>
    rooftopEnvelope_mono (fun y => EReal.coe_le_coe_iff.mpr (hfmono y hll')) x
  -- the regularized limit
  set U : M → EReal := uscRegularization (⨆ l, u l) with hUdef
  have hUpsh : ThetaPlurisubharmonic θ.val U := by
    have h := thetaPlurisubharmonic_uscRegularization_sSup (θ := θ.val) (F := range u)
      (hu 0).1.hasSmoothLocalPotentials ⟨u 0, mem_range_self 0⟩
      (by rintro _ ⟨l, rfl⟩; exact hu l) (by rintro _ ⟨l, rfl⟩; exact hu0 l)
    rwa [sSup_range] at h
  have hUge : ∀ x, ((-S : ℝ) : EReal) ≤ U x := fun x =>
    (huge 0 x).trans ((le_iSup (fun l => u l x) 0).trans (by
      rw [← iSup_apply]; exact le_uscRegularization _ x))
  have hUle : ∀ x, U x ≤ 0 := fun x =>
    uscRegularization_le (g := fun _ => (0 : EReal)) upperSemicontinuous_const
      (iSup_le hu0) x
  have hU : IsThetaPshPotential θ.val U :=
    ⟨hUpsh, fun x V _ hx => ⟨x, hx, ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hUge x)⟩⟩
  have hUb : IsBoundedPotential U := ⟨-S, 0, fun x => ⟨hUge x, by simpa using hUle x⟩⟩
  have hUF : diagonalPotentialMeasure θ U hU F = 0 := hF0 U hU hUb
  -- all the potentials carry the full mass
  have hmassU : diagonalPotentialMass θ U hU = vol :=
    diagonalPotentialMass_eq_of_le_add omega θ hU h0 (c₁ := S) (c₂ := 0)
      (fun x => by simpa only [zero_add] using hUge x)
      (fun x => by simpa only [zero_add, EReal.coe_zero] using hUle x)
  have hmassu : ∀ l, diagonalPotentialMass θ (u l) (hu l) = vol := fun l =>
    diagonalPotentialMass_eq_of_le_add omega θ (hu l) h0 (c₁ := S) (c₂ := 0)
      (fun x => by simpa only [zero_add] using huge l x)
      (fun x => by simpa only [zero_add, EReal.coe_zero] using hu0 l x)
  -- the closed neighbourhoods of `F`
  set C : ℕ → Set M := fun m => {x | infDist x F ≤ 1 / ((m : ℝ) + 1)} with hCdef
  have hCc : ∀ m, IsClosed (C m) := fun m =>
    isClosed_le (continuous_infDist_pt _) continuous_const
  have hCanti : Antitone C := by
    intro m m' hmm' x hx
    have hx' : infDist x F ≤ 1 / ((m' : ℝ) + 1) := hx
    show infDist x F ≤ 1 / ((m : ℝ) + 1)
    refine hx'.trans ?_
    have : (m : ℝ) ≤ m' := by exact_mod_cast hmm'
    gcongr
  have hCinter : ⋂ m, C m = F := by
    ext x
    simp only [mem_iInter]
    constructor
    · intro hx
      replace hx : ∀ m : ℕ, infDist x F ≤ 1 / ((m : ℝ) + 1) := hx
      rw [← hF.closure_eq, mem_closure_iff_infDist_zero hFne]
      refine le_antisymm (le_of_forall_pos_le_add fun δ hδ => ?_) infDist_nonneg
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
      have := hx m
      rw [zero_add]
      linarith
    · intro hx m
      show infDist x F ≤ 1 / ((m : ℝ) + 1)
      rw [infDist_zero_of_mem hx]
      positivity
  have hCsub : ∀ l x, 0 < g l x → x ∈ C l := fun l x hx => hgpos l x hx
  -- (ii) `θⁿ_U (C_m)` is small for some `m`
  have hε8 : 0 < ε / 8 := ENNReal.div_pos hε.ne' (by norm_num)
  have hlimC : Tendsto (fun m => diagonalPotentialMeasure θ U hU (C m)) atTop
      (𝓝 (diagonalPotentialMeasure θ U hU (⋂ m, C m))) :=
    tendsto_measure_iInter_atTop (fun m => (hCc m).measurableSet.nullMeasurableSet) hCanti
      ⟨0, (GlobalNonPluripolar.globalMixedMeasure_apply_lt_top omega
        (fun _ : Fin n => hU.1) _).ne⟩
  rw [hCinter, hUF] at hlimC
  obtain ⟨m, hm⟩ := (hlimC.eventually (gt_mem_nhds hε8)).exists
  -- (iii) `θⁿ_{u_l} (C_m)` is small for some `l ≥ m`
  have hε4 : ε / 8 ≤ ε / 4 := ENNReal.div_le_div_left (by norm_num) _
  obtain ⟨l, hlm, hl⟩ : ∃ l, m ≤ l ∧ diagonalPotentialMeasure θ (u l) (hu l) (C m) < ε / 4 := by
    by_contra hcon
    push Not at hcon
    have hO : IsOpen (C m)ᶜ := (hCc m).isOpen_compl
    have hlim := IncreasingLimitOpenMeasure.diagonalPotentialMeasure_isOpen_le_liminf u hu
      humono hU hO
    have hfin : ∀ (w : M → EReal) (hw : IsThetaPshPotential θ.val w) (E : Set M),
        diagonalPotentialMeasure θ w hw E ≠ ⊤ := fun w hw E =>
      (GlobalNonPluripolar.globalMixedMeasure_apply_lt_top omega (fun _ : Fin n => hw.1) E).ne
    have hcompl : ∀ l, diagonalPotentialMeasure θ (u l) (hu l) (C m)ᶜ =
        vol - diagonalPotentialMeasure θ (u l) (hu l) (C m) := fun l => by
      rw [measure_compl (μ := diagonalPotentialMeasure θ (u l) (hu l)) (hCc m).measurableSet
        (hfin _ _ _), ← hmassu l]
      rfl
    have hUcompl : diagonalPotentialMeasure θ U hU (C m)ᶜ =
        vol - diagonalPotentialMeasure θ U hU (C m) := by
      rw [measure_compl (μ := diagonalPotentialMeasure θ U hU) (hCc m).measurableSet
        (hfin _ _ _), ← hmassU]
      rfl
    have hle : liminf (fun l => diagonalPotentialMeasure θ (u l) (hu l) (C m)ᶜ) atTop ≤
        vol - ε / 4 := by
      refine liminf_le_of_frequently_le' ((eventually_ge_atTop m).mono fun l hl => ?_).frequently
      rw [hcompl l]
      exact tsub_le_tsub_left (hcon l hl) vol
    have hvolle : ∀ (w : M → EReal) (hw : IsThetaPshPotential θ.val w),
        diagonalPotentialMass θ w hw = vol → ∀ E, diagonalPotentialMeasure θ w hw E ≤ vol :=
      fun w hw hmass E => hmass ▸ measure_mono (subset_univ E)
    have hε4vol : ε / 4 ≤ vol := (hcon m le_rfl).trans (hvolle _ _ (hmassu m) _)
    have hkey : vol - diagonalPotentialMeasure θ U hU (C m) ≤ vol - ε / 4 := by
      rw [← hUcompl]
      exact hlim.trans hle
    have := (ENNReal.sub_le_sub_iff_left hε4vol hvolfin).mp hkey
    exact absurd (hm.trans_le hε4) (not_lt.mpr this)
  -- (iv) the volume of `{u_l < -t}` is small
  have hb : IsThetaPshPotential θ.val
      (fun x => (fun _ => (0 : EReal)) x + ((-t : ℝ) : EReal)) := h0.add_const (-t)
  have hba : MoreSingularOn (fun x => (fun _ => (0 : EReal)) x + ((-t : ℝ) : EReal)) (u l)
      univ := by
    refine ⟨S, fun x _ => ?_⟩
    calc (fun _ => (0 : EReal)) x + ((-t : ℝ) : EReal) = ((-t : ℝ) : EReal) := zero_add _
      _ ≤ ((-S : ℝ) : EReal) + (S : EReal) := by
          rw [← EReal.coe_add]
          exact EReal.coe_le_coe_iff.mpr (by linarith)
      _ ≤ u l x + (S : EReal) := add_le_add (huge l x) le_rfl
  have hcomp := diagonalPotentialMeasure_lt_le omega (hu l) hb hba
  have hMA0 := DiagonalMeasureRegularity.diagonalPotentialMeasure_add_const θ h0 (-t) hb
  have hsub1 : {x | u l x < (fun _ => (0 : EReal)) x + ((-t : ℝ) : EReal)} ⊆
      {x | u l x < (f l x : EReal)} ∪ C m := by
    intro x hx
    by_cases h : u l x < (f l x : EReal)
    · exact Or.inl h
    · right
      push Not at h
      have hx' : u l x < ((-t : ℝ) : EReal) := by simpa using hx
      have hf : f l x < -t := EReal.coe_lt_coe_iff.mp (lt_of_le_of_lt h hx')
      have hgl : 0 < g l x := by
        simp only [hfdef] at hf
        nlinarith [hg0 l x]
      exact hCanti hlm (hCsub l x hgl)
  have hcontact :=
    ContinuousObstacleEnvelopeContact.diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_continuous
      hn θ hbig (hfc l) (hu l)
  have hsmall : diagonalPotentialMeasure θ (fun _ => 0) h0
      {x | u l x < (fun _ => (0 : EReal)) x + ((-t : ℝ) : EReal)} < ε / 4 := by
    calc diagonalPotentialMeasure θ (fun _ => 0) h0
          {x | u l x < (fun _ => (0 : EReal)) x + ((-t : ℝ) : EReal)}
        = diagonalPotentialMeasure θ _ hb
            {x | u l x < (fun _ => (0 : EReal)) x + ((-t : ℝ) : EReal)} := by rw [hMA0]
      _ ≤ diagonalPotentialMeasure θ (u l) (hu l)
            {x | u l x < (fun _ => (0 : EReal)) x + ((-t : ℝ) : EReal)} := hcomp
      _ ≤ diagonalPotentialMeasure θ (u l) (hu l) ({x | u l x < (f l x : EReal)} ∪ C m) :=
          measure_mono hsub1
      _ ≤ diagonalPotentialMeasure θ (u l) (hu l) {x | u l x < (f l x : EReal)} +
            diagonalPotentialMeasure θ (u l) (hu l) (C m) := measure_union_le _ _
      _ = diagonalPotentialMeasure θ (u l) (hu l) (C m) := by
          rw [show diagonalPotentialMeasure θ (u l) (hu l) {x | u l x < (f l x : EReal)} = 0
            from hcontact, zero_add]
      _ < ε / 4 := hl
  -- (v) the sublevel estimate and (vi) the open set
  have hcap := thetaCapacity_sublevel_le omega h0 (hu l) (hu0 l) ht1
  refine ⟨{x | u l x < (fun _ => (0 : EReal)) x + ((-(2 * t) : ℝ) : EReal)}, ?_, ?_, ?_⟩
  · exact upperSemicontinuous_iff_isOpen_preimage.mp
      (upperSemicontinuous_rooftopEnvelope θ.val _) _
  · intro x hx
    show u l x < (fun _ => (0 : EReal)) x + ((-(2 * t) : ℝ) : EReal)
    rw [zero_add]
    refine lt_of_le_of_lt (hule l x) ?_
    rw [hfF l x hx]
    exact EReal.coe_lt_coe_iff.mpr (by simp only [hSdef]; linarith)
  · calc thetaCapacity θ (fun _ => 0)
          {x | u l x < (fun _ => (0 : EReal)) x + ((-(2 * t) : ℝ) : EReal)}
        ≤ ENNReal.ofReal (1 - (1 - t⁻¹) ^ n) * vol +
            diagonalPotentialMeasure θ (fun _ => 0) h0
              {x | u l x < (fun _ => (0 : EReal)) x + ((-t : ℝ) : EReal)} := hcap
      _ < ε / 2 + ε / 4 := ENNReal.add_lt_add htε hsmall
      _ ≤ ε / 2 + ε / 2 := add_le_add le_rfl (ENNReal.div_le_div_left (by norm_num) _)
      _ = ε := ENNReal.add_halves ε

end

end SGPT.Foundations.Analysis.Pending.ClosedNullOuterCapacity
