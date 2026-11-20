import SGPT.Foundations.Analysis.Pending.DiagonalMeasureDecreasingPortmanteau
import SGPT.Foundations.Analysis.Pending.ThetaCapacityLocalDecreasingConvergence

set_option autoImplicit false

/-!
# The local step of Xia's Theorem 2.4.4

This is the analytic core of Xia's Theorem 2.4.4 (`xia-sgpt:page-0081`),
assembled on one slot chart out of the four ingredients the workspace now has:

1. the **open-set portmanteau** for `theta^n` along a decreasing sequence
   (`Pending.DiagonalMeasureDecreasingPortmanteau`);
2. **Theorem 2.3.3**, convergence in capacity of a decreasing sequence
   (`Pending.ThetaCapacityLocalDecreasingConvergence`);
3. the **domination of the measure by the capacity**
   (`Pending.ThetaCapacity.diagonalPotentialMeasure_le_thetaCapacity_of_bounds`);
4. **quasi-continuity** of the limit potential and of the obstacle, which is
   Theorem 2.3.2, entering through the hypothesis `hqc`.  For the potential `w`
   that is `ThetaCapacityLocalQuasiContinuity.exists_isOpen_thetaCapacity_lt_continuousOn_of_boundedOn`
   directly; for the obstacle it is NOT, since that theorem needs a `theta`-PSH
   potential and the Section 3.1 obstacle `min {phi, psi}` is not one --
   `Pending.ThetaCapacityMinQuasiContinuity` supplies the minimum, and the
   common small open set for the pair.

The shape of the argument is Xia's, including his device at (2.27): the set
`S = O ∩ {w + delta < f}` on which one wants to conclude is not open, so it is
enlarged to an open `W` whose difference `W \ S` has small capacity, the
portmanteau is applied to `W`, and the difference is paid for by the capacity
bound.

What replaces Xia's Step 2 here is the decreasing family itself.  His `f_j` come
from Tietze on the small-capacity complements of a quasi-continuous `f`; the
obstacles `g k` below are only required to decrease with `theta^n_{u_k}` carried
by `{u_k = g_k}`, which for an upper semicontinuous obstacle is supplied by the
continuous majorants of `Pending.RooftopUscObstacleApproximation` together with
the continuous case of Theorem 2.4.4.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.RooftopLocalConcentration

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.GlobalSlotStokes
open SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
open SGPT.Foundations.Analysis.Pending.ThetaCapacity
open SGPT.Foundations.Analysis.Pending.ThetaCapacityChart
open SGPT.Foundations.Analysis.Pending.ThetaCapacityLocalDecreasingConvergence
open SGPT.Foundations.Analysis.Pending.DiagonalMeasureDecreasingPortmanteau

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-! ### Xia's enlargement (2.27) -/

/-- **A relatively open subset of `K \ A` sits inside an open set whose
difference with it is contained in `A`.**  This is the set-theoretic content of
Xia's construction after (2.27): `W = (U ∪ A) ∩ O`. -/
theorem exists_isOpen_superset_sdiff_subset {X : Type*} [TopologicalSpace X]
    {K A O S U : Set X} (hA : IsOpen A) (hO : IsOpen O) (hU : IsOpen U)
    (hUS : U ∩ (K \ A) = S ∩ (K \ A)) (hSO : S ⊆ O) (hOK : O ⊆ K) :
    ∃ W : Set X, IsOpen W ∧ S ⊆ W ∧ W ⊆ O ∧ W \ S ⊆ A := by
  refine ⟨(U ∪ A) ∩ O, (hU.union hA).inter hO, fun x hx => ⟨?_, hSO hx⟩, inter_subset_right, ?_⟩
  · by_cases hxA : x ∈ A
    · exact Or.inr hxA
    · refine Or.inl ?_
      have hmem : x ∈ S ∩ (K \ A) := ⟨hx, hOK (hSO hx), hxA⟩
      exact (hUS ▸ hmem : x ∈ U ∩ (K \ A)).1
  · rintro x ⟨⟨hxUA, hxO⟩, hxS⟩
    by_cases hxA : x ∈ A
    · exact hxA
    · exfalso
      rcases hxUA with hxU | hxA'
      · have hmem : x ∈ U ∩ (K \ A) := ⟨hxU, hOK hxO, hxA⟩
        exact hxS ((hUS ▸ hmem : x ∈ S ∩ (K \ A)).1)
      · exact hxA hxA'

/-! ### The local concentration theorem -/

variable {theta : ClosedRealOneOneForm n M} {e : ComplexChart n M}
  {D : Opens (ComplexModel n)} {hD : (D : Set (ComplexModel n)) ⊆ e.val.target}
  {rho : ComplexModel n → ℝ} {hrho : IsSmoothLocalPotential theta.val e D rho}

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- **The strict comparison of two functions continuous on `T` is relatively
open in `T`.**  Both functions are finite on `T`, so the `EReal` comparison
`w + delta < f` is the real one between the `toReal` values. -/
theorem exists_isOpen_inter_eq_lt_add {w f : M → EReal} {T : Set M}
    (hwb : ∀ x ∈ T, w x ≠ ⊥ ∧ w x ≠ ⊤) (hfb : ∀ x ∈ T, f x ≠ ⊥ ∧ f x ≠ ⊤)
    (hcw : ContinuousOn (fun y => (w y).toReal) T)
    (hcf : ContinuousOn (fun y => (f y).toReal) T)
    (delta : ℝ) :
    ∃ U : Set M, IsOpen U ∧
      U ∩ T = {x : M | w x + (delta : EReal) < f x} ∩ T := by
  have hcont : ContinuousOn (fun y => (f y).toReal - (w y).toReal) T := hcf.sub hcw
  obtain ⟨U, hUopen, hUeq⟩ :=
    (continuousOn_iff'.mp hcont) (Ioi delta) isOpen_Ioi
  refine ⟨U, hUopen, ?_⟩
  have hpt : ∀ x ∈ T,
      (w x + (delta : EReal) < f x ↔ delta < (f x).toReal - (w x).toReal) := by
    intro x hx
    obtain ⟨hwb1, hwb2⟩ := hwb x hx
    obtain ⟨hfb1, hfb2⟩ := hfb x hx
    have hw' : ((w x).toReal : EReal) = w x := EReal.coe_toReal hwb2 hwb1
    have hf' : ((f x).toReal : EReal) = f x := EReal.coe_toReal hfb2 hfb1
    constructor
    · intro h
      rw [← hw', ← hf', ← EReal.coe_add, EReal.coe_lt_coe_iff] at h
      linarith
    · intro h
      rw [← hw', ← hf', ← EReal.coe_add, EReal.coe_lt_coe_iff]
      linarith
  ext x
  constructor
  · rintro ⟨hxU, hxT⟩
    have hmem : x ∈ (fun y => (f y).toReal - (w y).toReal) ⁻¹' (Ioi delta) ∩ T := by
      rw [hUeq]; exact ⟨hxU, hxT⟩
    exact ⟨(hpt x hxT).mpr hmem.1, hxT⟩
  · rintro ⟨hxlt, hxT⟩
    have hmem : x ∈ (fun y => (f y).toReal - (w y).toReal) ⁻¹' (Ioi delta) ∩ T :=
      ⟨(hpt x hxT).mp hxlt, hxT⟩
    rw [hUeq] at hmem
    exact ⟨hmem.1, hxT⟩

/-- **The local step of Xia's Theorem 2.4.4.**  Let `u_k` decrease to `w`, all
of them bounded on a slot-chart source together with the capacity reference `V`
and the obstacle `f`; let the obstacles `g k` dominate `f` and carry the
measures of `u_k` on their contact sets **inside `O`**; let `V - C <= u_k <= V` globally.  Then
on every open `O` whose closure lies in the slot-chart source, and on which `w`
and `f` are quasi-continuous for `Cap_theta(-, V)`,

  `theta^n_w (O ∩ {w + delta < f}) = 0`   for every `delta > 0`.

The proof is Xia's, on `xia-sgpt:page-0081`: the set is enlarged to an open `W`
whose difference has capacity less than `eps` (his (2.27)); the portmanteau
inequality is applied to `W`; the measures `theta^n_{u_k}` of the set itself
tend to `0`, because there `u_k` either stays strictly below its own obstacle
(a null set for `theta^n_{u_k}` inside `O`) or exceeds `w + delta` (a set of capacity
tending to `0`, by Theorem 2.3.3); and the difference is paid for by
`C^n eps`. -/
theorem diagonalPotentialMeasure_inter_lt_add_eq_zero
    {V w f : M → EReal} {u : ℕ → M → EReal} {g : ℕ → M → ℝ}
    (hu : ∀ k, IsThetaPshPotential theta.val (u k))
    (hw : IsThetaPshPotential theta.val w)
    (hV : IsThetaPshPotential theta.val V)
    (hub : ∀ k, IsBoundedPotentialOn (u k)
      ((diagSlotChart theta e D hD rho hrho).source : Set M))
    (hwb : IsBoundedPotentialOn w
      ((diagSlotChart theta e D hD rho hrho).source : Set M))
    (hVb : IsBoundedPotentialOn V
      ((diagSlotChart theta e D hD rho hrho).source : Set M))
    (hfb : IsBoundedPotentialOn f
      ((diagSlotChart theta e D hD rho hrho).source : Set M))
    {L : ℝ} (hL : ∀ z ∈ (D : Set (ComplexModel n)), |rho z| ≤ L)
    (hanti : ∀ x, Antitone fun k => u k x)
    (hlim : ∀ x, Tendsto (fun k => u k x) atTop (𝓝 (w x)))
    {C : ℝ} (hC : 1 ≤ C) (hleV : ∀ k, u k ≤ V)
    (hlbV : ∀ k x, V x ≤ u k x + (C : EReal))
    (hukg : ∀ k x, u k x ≤ ((g k x : ℝ) : EReal))
    (hfg : ∀ k x, f x ≤ ((g k x : ℝ) : EReal))
    {O : Set M} (hO : IsOpen O)
    (hOS : closure O ⊆ ((diagSlotChart theta e D hD rho hrho).source : Set M))
    (hcontact : ∀ k, diagonalPotentialMeasure theta (u k) (hu k)
      (O ∩ {x : M | u k x < ((g k x : ℝ) : EReal)}) = 0)
    (hqc : ∀ eps : ℝ, 0 < eps → ∃ A : Set M, IsOpen A ∧
      thetaCapacity theta V A < ENNReal.ofReal eps ∧
      ContinuousOn (fun y => (w y).toReal) (closure O \ A) ∧
      ContinuousOn (fun y => (f y).toReal) (closure O \ A))
    {delta : ℝ} (hdelta : 0 < delta) :
    diagonalPotentialMeasure theta w hw
      (O ∩ {x : M | w x + (delta : EReal) < f x}) = 0 := by
  classical
  set Sc : Set M := ((diagSlotChart theta e D hD rho hrho).source : Set M) with hSc
  set K : Set M := closure O with hK
  have hKc : IsCompact K := isClosed_closure.isCompact
  have hOK : O ⊆ K := subset_closure
  set Sset : Set M := O ∩ {x : M | w x + (delta : EReal) < f x} with hSset
  have hSO : Sset ⊆ O := inter_subset_left
  -- the uniform domination of the measures by the capacity
  have hdom : ∀ (k : ℕ) (E : Set M), diagonalPotentialMeasure theta (u k) (hu k) E ≤
      ENNReal.ofReal (C ^ n) * thetaCapacity theta V E := fun k E =>
    diagonalPotentialMeasure_le_thetaCapacity_of_bounds hV (hu k) hC (hleV k) (hlbV k) E
  -- Theorem 2.3.3: the capacity of the bad set tends to zero
  have hcap0 : Tendsto (fun k => thetaCapacity theta V
      (K ∩ {x : M | w x + (delta : EReal) < u k x})) atTop (𝓝 0) :=
    tendsto_thetaCapacity_of_antitone_of_boundedOn
      (diagSlotChart theta e D hD rho hrho).source.isOpen hVb hKc hOS hu hub hw hwb
      hanti hlim hdelta
  have hcap0' : Tendsto (fun k => ENNReal.ofReal (C ^ n) * thetaCapacity theta V
      (K ∩ {x : M | w x + (delta : EReal) < u k x})) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (C ^ n)) hcap0
      (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  -- the measures of the target set along the sequence tend to zero
  have hsplit : ∀ k : ℕ, Sset ⊆ (O ∩ {x : M | u k x < ((g k x : ℝ) : EReal)}) ∪
      (K ∩ {x : M | w x + (delta : EReal) < u k x}) := by
    intro k x hx
    rcases lt_or_eq_of_le (hukg k x) with hlt | heq
    · exact Or.inl ⟨hx.1, hlt⟩
    · refine Or.inr ⟨hOK hx.1, ?_⟩
      exact lt_of_lt_of_le hx.2 (heq ▸ hfg k x)
  have hSk : ∀ k : ℕ, diagonalPotentialMeasure theta (u k) (hu k) Sset ≤
      ENNReal.ofReal (C ^ n) * thetaCapacity theta V
        (K ∩ {x : M | w x + (delta : EReal) < u k x}) := by
    intro k
    calc diagonalPotentialMeasure theta (u k) (hu k) Sset
        ≤ diagonalPotentialMeasure theta (u k) (hu k)
            ((O ∩ {x : M | u k x < ((g k x : ℝ) : EReal)}) ∪
              (K ∩ {x : M | w x + (delta : EReal) < u k x})) := measure_mono (hsplit k)
      _ ≤ diagonalPotentialMeasure theta (u k) (hu k)
            (O ∩ {x : M | u k x < ((g k x : ℝ) : EReal)}) +
          diagonalPotentialMeasure theta (u k) (hu k)
            (K ∩ {x : M | w x + (delta : EReal) < u k x}) := measure_union_le _ _
      _ = diagonalPotentialMeasure theta (u k) (hu k)
            (K ∩ {x : M | w x + (delta : EReal) < u k x}) := by rw [hcontact k, zero_add]
      _ ≤ _ := hdom k _
  have hto0 : Tendsto (fun k => diagonalPotentialMeasure theta (u k) (hu k) Sset)
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hcap0'
      (fun _ => zero_le) hSk
  -- the `eps`-estimate
  have key : ∀ eps : ℝ, 0 < eps →
      diagonalPotentialMeasure theta w hw Sset ≤
        ENNReal.ofReal (C ^ n) * ENNReal.ofReal eps := by
    intro eps heps
    obtain ⟨A, hAopen, hAcap, hcw, hcf⟩ := hqc eps heps
    have hKA : closure O \ A ⊆ Sc := fun x hx => hOS hx.1
    obtain ⟨U0, hU0open, hU0eq⟩ := exists_isOpen_inter_eq_lt_add
      (w := w) (f := f) (T := closure O \ A)
      (fun x hx => ⟨hwb.ne_bot (hKA hx), hwb.ne_top (hKA hx)⟩)
      (fun x hx => ⟨hfb.ne_bot (hKA hx), hfb.ne_top (hKA hx)⟩) hcw hcf delta
    have hUeq : (U0 ∩ O) ∩ (K \ A) = Sset ∩ (K \ A) := by
      rw [hSset, hK]
      ext x
      constructor
      · rintro ⟨⟨hxU, hxO⟩, hxKA⟩
        have : x ∈ {y : M | w y + (delta : EReal) < f y} ∩ (closure O \ A) := by
          rw [← hU0eq]; exact ⟨hxU, hxKA⟩
        exact ⟨⟨hxO, this.1⟩, hxKA⟩
      · rintro ⟨⟨hxO, hxlt⟩, hxKA⟩
        have : x ∈ U0 ∩ (closure O \ A) := by
          rw [hU0eq]; exact ⟨hxlt, hxKA⟩
        exact ⟨⟨this.1, hxO⟩, hxKA⟩
    obtain ⟨W, hWopen, hSW, hWO, hWdiff⟩ :=
      exists_isOpen_superset_sdiff_subset hAopen hO (hU0open.inter hO) hUeq hSO hOK
    have hWS : W ⊆ Sc := fun x hx => hOS (hOK (hWO hx))
    -- portmanteau on `W`
    have hport : diagonalPotentialMeasure theta w hw W ≤
        liminf (fun k => diagonalPotentialMeasure theta (u k) (hu k) W) atTop :=
      diagonalPotentialMeasure_le_liminf_of_antitone (hrho := hrho) hu hw hub hwb hL
        hanti hlim hWopen hWS
    have hWbound : ∀ k : ℕ, diagonalPotentialMeasure theta (u k) (hu k) W ≤
        diagonalPotentialMeasure theta (u k) (hu k) Sset +
          ENNReal.ofReal (C ^ n) * ENNReal.ofReal eps := by
      intro k
      have hsub : W ⊆ Sset ∪ (W \ Sset) := fun x hx => by
        by_cases hxS : x ∈ Sset
        · exact Or.inl hxS
        · exact Or.inr ⟨hx, hxS⟩
      calc diagonalPotentialMeasure theta (u k) (hu k) W
          ≤ diagonalPotentialMeasure theta (u k) (hu k) (Sset ∪ (W \ Sset)) :=
            measure_mono hsub
        _ ≤ diagonalPotentialMeasure theta (u k) (hu k) Sset +
            diagonalPotentialMeasure theta (u k) (hu k) (W \ Sset) := measure_union_le _ _
        _ ≤ diagonalPotentialMeasure theta (u k) (hu k) Sset +
            ENNReal.ofReal (C ^ n) * ENNReal.ofReal eps := by
              refine add_le_add le_rfl ((hdom k _).trans ?_)
              have hcaple : thetaCapacity theta V (W \ Sset) ≤ ENNReal.ofReal eps :=
                (thetaCapacity_mono hWdiff).trans hAcap.le
              exact mul_le_mul' le_rfl hcaple
    have hlimsum : Tendsto (fun k => diagonalPotentialMeasure theta (u k) (hu k) Sset +
        ENNReal.ofReal (C ^ n) * ENNReal.ofReal eps) atTop
        (𝓝 (ENNReal.ofReal (C ^ n) * ENNReal.ofReal eps)) := by
      have := hto0.add (tendsto_const_nhds
        (x := ENNReal.ofReal (C ^ n) * ENNReal.ofReal eps) (f := atTop (α := ℕ)))
      simpa using this
    calc diagonalPotentialMeasure theta w hw Sset
        ≤ diagonalPotentialMeasure theta w hw W := measure_mono hSW
      _ ≤ liminf (fun k => diagonalPotentialMeasure theta (u k) (hu k) W) atTop := hport
      _ ≤ liminf (fun k => diagonalPotentialMeasure theta (u k) (hu k) Sset +
            ENNReal.ofReal (C ^ n) * ENNReal.ofReal eps) atTop :=
          liminf_le_liminf (Eventually.of_forall hWbound)
      _ = ENNReal.ofReal (C ^ n) * ENNReal.ofReal eps := hlimsum.liminf_eq
  -- let `eps` tend to zero
  refine le_antisymm ?_ zero_le
  have h1 : Tendsto (fun m : ℕ => ENNReal.ofReal (1 / ((m : ℝ) + 1))) atTop (𝓝 0) := by
    have hc := (ENNReal.continuous_ofReal.tendsto 0).comp
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [Function.comp_def] using hc
  have hseq : Tendsto (fun m : ℕ => ENNReal.ofReal (C ^ n) *
      ENNReal.ofReal (1 / ((m : ℝ) + 1))) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (C ^ n)) h1
      (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  refine ge_of_tendsto hseq (Eventually.of_forall fun m => ?_)
  exact key _ (by positivity)


/-! ### From the local statement to the global one -/

/-- **A measure that vanishes near every point of `S` outside a null set
vanishes on `S`.**  This is mathlib's `measure_null_of_locally_null` (second
countability makes the covering countable) with the exceptional null set `Z`
added: in Xia's argument `Z` is `nK({theta})` together with the poles, where the
local hypotheses of `diagonalPotentialMeasure_inter_lt_add_eq_zero` fail. -/
theorem measure_eq_zero_of_forall_exists_isOpen {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [SecondCountableTopology X] {mu : Measure X} {S Z : Set X}
    (hZ : mu Z = 0)
    (hloc : ∀ x ∈ S \ Z, ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ mu (O ∩ S) = 0) :
    mu S = 0 := by
  have hTnull : mu (S \ Z) = 0 := by
    refine measure_null_of_locally_null (S \ Z) fun x hx => ?_
    obtain ⟨O, hOopen, hxO, hOnull⟩ := hloc x hx
    refine ⟨(S \ Z) ∩ O, inter_mem_nhdsWithin _ (hOopen.mem_nhds hxO), ?_⟩
    refine measure_mono_null (fun y hy => ?_) hOnull
    exact ⟨hy.2, hy.1.1⟩
  have hsub : S ⊆ (S \ Z) ∪ Z := fun x hx => by
    by_cases hxZ : x ∈ Z
    · exact Or.inr hxZ
    · exact Or.inl ⟨hx, hxZ⟩
  exact measure_mono_null hsub (measure_union_null hTnull hZ)

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- **The strict inequality set is a countable union of the `delta`-shifted
ones, off the poles.** -/
theorem lt_subset_union_iUnion_add (w f : M → EReal) :
    {x : M | w x < f x} ⊆ {x : M | w x = ⊥} ∪
      ⋃ m : ℕ, {x : M | w x + ((1 / ((m : ℝ) + 1) : ℝ) : EReal) < f x} := by
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx
  by_cases hbot : w x = ⊥
  · exact Or.inl hbot
  refine Or.inr ?_
  have htop : w x ≠ ⊤ := ne_top_of_lt hx
  obtain ⟨r, hr⟩ : ∃ r : ℝ, w x = (r : EReal) :=
    ⟨(w x).toReal, (EReal.coe_toReal htop hbot).symm⟩
  rcases eq_or_ne (f x) ⊤ with hftop | hftop
  · refine mem_iUnion.mpr ⟨0, ?_⟩
    show w x + _ < f x
    rw [hftop, hr, ← EReal.coe_add]
    exact EReal.coe_lt_top _
  have hfbot : f x ≠ ⊥ := by
    intro h
    rw [h] at hx
    exact absurd (le_bot_iff.mp hx.le) hbot
  obtain ⟨s, hs⟩ : ∃ s : ℝ, f x = (s : EReal) :=
    ⟨(f x).toReal, (EReal.coe_toReal hftop hfbot).symm⟩
  have hrs : r < s := by
    rw [hr, hs, EReal.coe_lt_coe_iff] at hx; exact hx
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / (s - r))
  have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hlt : 1 / ((m : ℝ) + 1) < s - r := by
    have hsr : 0 < s - r := by linarith
    rw [div_lt_iff₀ hmpos]
    rw [div_lt_iff₀ hsr] at hm
    nlinarith
  refine mem_iUnion.mpr ⟨m, ?_⟩
  show w x + _ < f x
  rw [hr, hs, ← EReal.coe_add, EReal.coe_lt_coe_iff]
  linarith

end

end SGPT.Foundations.Analysis.Pending.RooftopLocalConcentration
