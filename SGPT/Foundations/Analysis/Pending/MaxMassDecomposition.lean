import SGPT.Foundations.Analysis.Pending.IncreasingLimitOpenMeasure
import SGPT.Foundations.Analysis.Pending.GlobalMaxLocality
import SGPT.Foundations.Analysis.Pending.DiagonalMeasureRegularity
import SGPT.Foundations.Analysis.Pending.IEnvelopeStrongOpenness

set_option autoImplicit false

/-!
# Xia's Lemma 2.4.2: the mass of a maximum dominates the two contact pieces

For `u, v` in `PSH(X, theta)` whose maximum is again a genuine potential,
Xia, SGPT, Lemma 2.4.2 (`xia-sgpt:page-0076`, inequality (2.17)) states

  `theta^n_{u v v} >= 1_{u >= v} theta^n_u + 1_{u < v} theta^n_v`.

The two *strict* pieces are plurifine locality, which this workspace has
globally (`GlobalMaxLocality.globalMixedMeasure_restrict_max_eq`); the whole
content of the lemma is that the contact set `{u = v}` may be attached to
either side.

The source proof truncates at `V_theta - k`, shifts by `t > 0`, and lets
`t -> 0+` using the *decreasing* convergence theorem (Xia's Theorem 2.4.2),
which this workspace does not have.  The proof below avoids it: it shifts
*downwards* instead, so that

  `gamma_j := max (u - c_j) v`,   `c_j = 1 / (j + 1)`,

is an **increasing** sequence with pointwise supremum `max u v`, already upper
semicontinuous, so no regularization is needed.  The increasing semicontinuity
inequality on open sets (Xia's Corollary 2.4.1 in measure form,
`IncreasingLimitOpenMeasure.diagonalPotentialMeasure_isOpen_le_liminf`) then
gives, because every `gamma_j` has the *same* total mass as `max u v`
(bounded difference, monotonicity theorem), the dual bound on closed sets

  `limsup_j theta^n_{gamma_j}(C) <= theta^n_{max u v}(C)`,

and no truncation at `V_theta - k` is needed at any point: locality is applied
to the unbounded potentials directly.  Inner regularity of a finite Borel
measure on a compact metrizable manifold transports the closed-set inequality
to all Borel sets.

The hypothesis `hmax` carried by the statements below is not an extra
assumption: it is unconditionally supplied by
`Pending.IsThetaPshPotential.max hu hv`.  It is named because the measure
`diagonalPotentialMeasure theta (fun x => max (u x) (v x)) hmax` needs a proof
term in the statement itself, exactly as `hw` is named in
`Pending.RooftopMassDecomposition`; proof irrelevance makes the choice of
witness immaterial.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.MaxMassDecomposition

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.DiagonalMeasureRegularity
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar

noncomputable section

/-! ## The downward-shifted increasing family (pointwise) -/

section Pointwise

variable {M : Type*}

/-- The shifts `1 / (j + 1)`, decreasing to `0`. -/
def shift (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)

theorem shift_pos (j : ℕ) : 0 < shift j := by
  unfold shift; positivity

theorem shift_antitone : Antitone shift := fun j k h => by
  unfold shift
  gcongr

theorem tendsto_shift : Tendsto shift atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- The `j`-th downward shift of `u`. -/
def shiftPot (u : M → EReal) (j : ℕ) : M → EReal :=
  fun x => u x + ((-(shift j) : ℝ) : EReal)

theorem shiftPot_apply (u : M → EReal) (j : ℕ) (x : M) :
    shiftPot u j x = u x + ((-(shift j) : ℝ) : EReal) := rfl

theorem shiftPot_le (u : M → EReal) (j : ℕ) (x : M) : shiftPot u j x ≤ u x := by
  calc shiftPot u j x ≤ u x + ((0 : ℝ) : EReal) :=
        add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (by linarith [shift_pos j]))
    _ = u x := by simp

theorem shiftPot_mono (u : M → EReal) : Monotone (shiftPot u) := fun j k hjk x =>
  add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (by simpa using shift_antitone hjk))

/-- `max (u - 1/(j+1)) v`: an increasing sequence of potentials with pointwise
supremum `max u v`. -/
def shifted (u v : M → EReal) (j : ℕ) : M → EReal :=
  fun x => max (shiftPot u j x) (v x)

theorem shifted_monotone (u v : M → EReal) : Monotone (shifted u v) := by
  intro j k hjk x
  refine max_le_max ?_ le_rfl
  exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (by simpa using shift_antitone hjk))

theorem shifted_le_max (u v : M → EReal) (j : ℕ) (x : M) :
    shifted u v j x ≤ max (u x) (v x) := by
  refine max_le_max ?_ le_rfl
  calc u x + ((-(shift j) : ℝ) : EReal) ≤ u x + ((0 : ℝ) : EReal) :=
        add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (by linarith [shift_pos j]))
    _ = u x := by simp

theorem max_le_shifted_add (u v : M → EReal) (j : ℕ) (x : M) :
    max (u x) (v x) ≤ shifted u v j x + ((shift j : ℝ) : EReal) := by
  have h1 : u x ≤ shifted u v j x + ((shift j : ℝ) : EReal) := by
    have hle : u x + ((-(shift j) : ℝ) : EReal) ≤ shifted u v j x := le_max_left _ _
    calc u x = (u x + ((-(shift j) : ℝ) : EReal)) + ((shift j : ℝ) : EReal) := by
          rw [add_assoc, ← EReal.coe_add]; simp
      _ ≤ shifted u v j x + ((shift j : ℝ) : EReal) := add_le_add hle le_rfl
  have h2 : v x ≤ shifted u v j x + ((shift j : ℝ) : EReal) := by
    have hle : v x ≤ shifted u v j x := le_max_right _ _
    calc v x ≤ shifted u v j x := hle
      _ = shifted u v j x + ((0 : ℝ) : EReal) := by simp
      _ ≤ shifted u v j x + ((shift j : ℝ) : EReal) :=
          add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (shift_pos j).le)
  exact max_le h1 h2

/-- The pointwise supremum of the shifted family is the maximum itself. -/
theorem iSup_shifted (u v : M → EReal) (hu : ∀ x, u x ≠ ⊤) (x : M) :
    (⨆ j, shifted u v j x) = max (u x) (v x) := by
  refine le_antisymm (iSup_le fun j => shifted_le_max u v j x) ?_
  refine max_le ?_ (le_iSup_of_le 0 (le_max_right _ _))
  rcases eq_or_ne (u x) ⊥ with hb | hb
  · rw [hb]; exact bot_le
  · lift u x to ℝ using ⟨hu x, hb⟩ with a ha
    have hbound : ∀ j : ℕ, ((a - shift j : ℝ) : EReal) ≤ ⨆ j, shifted u v j x := by
      intro j
      refine le_iSup_of_le j (le_trans (le_of_eq ?_) (le_max_left _ _))
      rw [shiftPot_apply, ← ha, ← EReal.coe_add]
      congr 1
    have htend : Tendsto (fun j : ℕ => ((a - shift j : ℝ) : EReal)) atTop
        (𝓝 ((a : ℝ) : EReal)) := by
      refine EReal.tendsto_coe.mpr ?_
      simpa using tendsto_const_nhds.sub tendsto_shift
    exact le_of_tendsto htend (Eventually.of_forall hbound)

end Pointwise

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-! ## Diagonal forms of the two global inputs -/

omit [BorelSpace M] in
theorem diagonalPotentialMeasure_congr {theta : ClosedRealOneOneForm n M}
    {f g : M → EReal} (hf : IsThetaPshPotential theta.val f)
    (hg : IsThetaPshPotential theta.val g) (h : f = g) :
    diagonalPotentialMeasure theta f hf = diagonalPotentialMeasure theta g hg := by
  subst h
  exact diagonalPotentialMeasure_proof_independent hf hg

/-- **Plurifine locality, diagonal form.**  The non-pluripolar Monge--Ampere
measure of `max (u, v)` agrees with that of `u` on `{v < u}`.  In dimension
zero the tuple condition `forall i : Fin n, v < u` is vacuous, so the global
statement degenerates to equality of the two measures; both cases are covered
here, and no positivity of the dimension is assumed. -/
theorem diagonalPotentialMeasure_restrict_max_eq
    (theta : ClosedRealOneOneForm n M) {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (hv : IsThetaPshPotential theta.val v)
    (hmax : IsThetaPshPotential theta.val (fun x => max (u x) (v x))) :
    (diagonalPotentialMeasure theta (fun x => max (u x) (v x)) hmax).restrict
        {x : M | v x < u x} =
      (diagonalPotentialMeasure theta u hu).restrict {x : M | v x < u x} := by
  have h := GlobalMaxLocality.globalMixedMeasure_restrict_max_eq
    (θ := fun _ : Fin n => theta) (u := fun _ : Fin n => u) (w := fun _ : Fin n => v)
    (fun _ => hu.1) (fun _ => hv.1) (fun _ => hmax.1)
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    have huniv : {x : M | ∀ _ : Fin 0, v x < u x} = univ :=
      eq_univ_iff_forall.2 fun x i => i.elim0
    rw [huniv, Measure.restrict_univ, Measure.restrict_univ] at h
    have heq : diagonalPotentialMeasure theta (fun x => max (u x) (v x)) hmax =
        diagonalPotentialMeasure theta u hu := h
    rw [heq]
  · have hset : {x : M | ∀ _ : Fin n, v x < u x} = {x : M | v x < u x} := by
      ext x
      exact ⟨fun h => h ⟨0, hn⟩, fun h _ => h⟩
    rw [hset] at h
    exact h

/-- In dimension zero every diagonal non-pluripolar measure is the same
measure: the empty mixed product does not see the potential.  This is the
degenerate case the dimension hypothesis usually excludes, isolated here so
that the statements below need no positivity assumption. -/
theorem diagonalPotentialMeasure_eq_of_dim_zero (h0 : n = 0)
    (theta : ClosedRealOneOneForm n M) {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (hv : IsThetaPshPotential theta.val v) :
    diagonalPotentialMeasure theta u hu = diagonalPotentialMeasure theta v hv := by
  have hmax : IsThetaPshPotential theta.val (fun x => max (u x) (v x)) :=
    SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max hu hv
  have hmax' : IsThetaPshPotential theta.val (fun x => max (v x) (u x)) :=
    SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max hv hu
  have key : ∀ (p q : M → EReal) (hp : IsThetaPshPotential theta.val p)
      (hq : IsThetaPshPotential theta.val q)
      (hpq : IsThetaPshPotential theta.val (fun x => max (p x) (q x))),
      diagonalPotentialMeasure theta (fun x => max (p x) (q x)) hpq =
        diagonalPotentialMeasure theta p hp := by
    intro p q hp hq hpq
    have h := GlobalMaxLocality.globalMixedMeasure_restrict_max_eq
      (θ := fun _ : Fin n => theta) (u := fun _ : Fin n => p) (w := fun _ : Fin n => q)
      (fun _ => hp.1) (fun _ => hq.1) (fun _ => hpq.1)
    subst h0
    have huniv : {x : M | ∀ _ : Fin 0, q x < p x} = univ :=
      eq_univ_iff_forall.2 fun x i => i.elim0
    rw [huniv, Measure.restrict_univ, Measure.restrict_univ] at h
    exact h
  have hfun : (fun x : M => max (v x) (u x)) = fun x : M => max (u x) (v x) := by
    funext x
    exact max_comm _ _
  calc diagonalPotentialMeasure theta u hu
      = diagonalPotentialMeasure theta (fun x => max (u x) (v x)) hmax :=
        (key u v hu hv hmax).symm
    _ = diagonalPotentialMeasure theta (fun x => max (v x) (u x)) hmax' := by
        rw [diagonalPotentialMeasure_congr hmax' hmax hfun]
    _ = diagonalPotentialMeasure theta v hv := key v u hv hu hmax'

omit [CompactSpace M] in
/-- The strict comparison set of two `theta`-PSH potentials is Borel. -/
theorem measurableSet_potential_lt {theta : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (hv : IsThetaPshPotential theta.val v) :
    MeasurableSet {x : M | v x < u x} :=
  measurableSet_lt hv.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
    hu.1.quasiPlurisubharmonic.upperSemicontinuous.measurable

omit [CompactSpace M] in
/-- The non-strict comparison set of two `theta`-PSH potentials is Borel. -/
theorem measurableSet_potential_le {theta : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (hv : IsThetaPshPotential theta.val v) :
    MeasurableSet {x : M | u x ≤ v x} :=
  measurableSet_le hu.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
    hv.1.quasiPlurisubharmonic.upperSemicontinuous.measurable

/-! ## The shifted family as potentials -/

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem isThetaPshPotential_shifted {theta : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (hv : IsThetaPshPotential theta.val v)
    (j : ℕ) : IsThetaPshPotential theta.val (shifted u v j) :=
  SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max (hu.add_const _) hv

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The maximum of two `theta`-PSH potentials is already upper semicontinuous,
so the pointwise supremum of the shifted family needs no regularization. -/
theorem uscRegularization_iSup_shifted {theta : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (hv : IsThetaPshPotential theta.val v) :
    uscRegularization (⨆ j, shifted u v j) = fun x => max (u x) (v x) := by
  have hfun : (⨆ j, shifted u v j) = fun x : M => max (u x) (v x) := by
    funext x
    rw [iSup_apply]
    exact iSup_shifted u v (fun y => hu.1.quasiPlurisubharmonic.ne_top y) x
  rw [hfun]
  refine uscRegularization_eq ?_
  exact hu.1.quasiPlurisubharmonic.upperSemicontinuous.sup
    hv.1.quasiPlurisubharmonic.upperSemicontinuous

/-- Every member of the shifted family has the same total non-pluripolar mass
as the maximum: the two differ by at most the constant `shift j`, so the
monotonicity theorem applies in both directions. -/
theorem diagonalPotentialMass_shifted (hn : 0 < n) (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (hv : IsThetaPshPotential theta.val v)
    (hmax : IsThetaPshPotential theta.val (fun x => max (u x) (v x))) (j : ℕ) :
    diagonalPotentialMeasure theta (shifted u v j)
        (isThetaPshPotential_shifted hu hv j) univ =
      diagonalPotentialMeasure theta (fun x => max (u x) (v x)) hmax univ :=
  MixedMass.globalMixedMass_eq_of_sameSingularityType hn omega
    (θ := fun _ : Fin n => theta) (u := fun _ : Fin n => shifted u v j)
    (v := fun _ : Fin n => fun x => max (u x) (v x))
    (fun _ => isThetaPshPotential_shifted hu hv j) (fun _ => hmax)
    (fun _ => ⟨MoreSingularOn.of_le (fun x _ => shifted_le_max u v j x),
      ⟨shift j, fun x _ => max_le_shifted_add u v j x⟩⟩)

/-! ## The dual (closed-set) semicontinuity bound -/

/-- **Upper semicontinuity of the mass of a closed set along the shifted
family.**  The increasing-limit inequality of Xia's Corollary 2.4.1 bounds the
limit measure from above on *open* sets; because every member of the family
carries the *same* finite total mass as the limit, complementation turns it
into the bound this proof needs, on *closed* sets. -/
theorem limsup_closed_le (hn : 0 < n) (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (hv : IsThetaPshPotential theta.val v)
    (hmax : IsThetaPshPotential theta.val (fun x => max (u x) (v x)))
    {C : Set M} (hC : IsClosed C) :
    limsup (fun j => diagonalPotentialMeasure theta (shifted u v j)
        (isThetaPshPotential_shifted hu hv j) C) atTop ≤
      diagonalPotentialMeasure theta (fun x => max (u x) (v x)) hmax C := by
  set mu := diagonalPotentialMeasure theta (fun x => max (u x) (v x)) hmax with hmu
  set nu := fun j => diagonalPotentialMeasure theta (shifted u v j)
    (isThetaPshPotential_shifted hu hv j) with hnu
  set V := mu univ with hV
  have hVtop : V ≠ ⊤ := (diagonalPotentialMeasure_lt_top omega theta hmax univ).ne
  have hCm : MeasurableSet C := hC.measurableSet
  -- every member of the family has total mass `V`
  have hmass : ∀ j, nu j univ = V := fun j =>
    diagonalPotentialMass_shifted hn omega hu hv hmax j
  -- the increasing-limit inequality on the open complement
  have hU : IsThetaPshPotential theta.val (uscRegularization (⨆ j, shifted u v j)) := by
    rw [uscRegularization_iSup_shifted hu hv]; exact hmax
  have htransport : ∀ (f : M → EReal) (hf : IsThetaPshPotential theta.val f),
      f = (fun x => max (u x) (v x)) →
      diagonalPotentialMeasure theta f hf = mu := by
    rintro f hf rfl
    exact diagonalPotentialMeasure_proof_independent hf hmax
  have hopen : mu Cᶜ ≤ liminf (fun j => nu j Cᶜ) atTop := by
    have h := IncreasingLimitOpenMeasure.diagonalPotentialMeasure_isOpen_le_liminf
      (theta := theta) (shifted u v) (isThetaPshPotential_shifted hu hv)
      (shifted_monotone u v) hU (G := Cᶜ) hC.isOpen_compl
    rwa [htransport _ hU (uscRegularization_iSup_shifted hu hv)] at h
  -- complementation
  have hsplit : ∀ j, nu j C = V - nu j Cᶜ := fun j =>
    ENNReal.eq_sub_of_add_eq
      (ne_top_of_le_ne_top hVtop
        ((measure_mono (subset_univ _)).trans (le_of_eq (hmass j))))
      ((measure_add_measure_compl hCm).trans (hmass j))
  have hmuC : mu C = V - mu Cᶜ :=
    ENNReal.eq_sub_of_add_eq
      (ne_top_of_le_ne_top hVtop (measure_mono (subset_univ _)))
      (measure_add_measure_compl hCm)
  calc limsup (fun j => nu j C) atTop = limsup (fun j => V - nu j Cᶜ) atTop := by
        simp only [hsplit]
    _ = V - liminf (fun j => nu j Cᶜ) atTop := ENNReal.limsup_const_sub atTop _ hVtop
    _ ≤ V - mu Cᶜ := tsub_le_tsub_left hopen V
    _ = mu C := hmuC.symm

/-! ## Evaluated forms of locality -/

/-- Locality, evaluated: on the part of a measurable set where `q < p`, the
measure of `max (p, q)` is the measure of `p`. -/
theorem measure_inter_lt_left (theta : ClosedRealOneOneForm n M)
    {p q : M → EReal} (hp : IsThetaPshPotential theta.val p)
    (hq : IsThetaPshPotential theta.val q)
    (hpq : IsThetaPshPotential theta.val (fun x => max (p x) (q x)))
    {s : Set M} (hs : MeasurableSet s) :
    diagonalPotentialMeasure theta (fun x => max (p x) (q x)) hpq
        (s ∩ {x : M | q x < p x}) =
      diagonalPotentialMeasure theta p hp (s ∩ {x : M | q x < p x}) := by
  have h := diagonalPotentialMeasure_restrict_max_eq theta hp hq hpq
  have h' := congrArg (fun mu : Measure M => mu s) h
  simpa only [Measure.restrict_apply hs] using h'

/-- Locality, evaluated, on the other side. -/
theorem measure_inter_lt_right (theta : ClosedRealOneOneForm n M)
    {p q : M → EReal} (hp : IsThetaPshPotential theta.val p)
    (hq : IsThetaPshPotential theta.val q)
    (hpq : IsThetaPshPotential theta.val (fun x => max (p x) (q x)))
    {s : Set M} (hs : MeasurableSet s) :
    diagonalPotentialMeasure theta (fun x => max (p x) (q x)) hpq
        (s ∩ {x : M | p x < q x}) =
      diagonalPotentialMeasure theta q hq (s ∩ {x : M | p x < q x}) := by
  have hfun : (fun x : M => max (q x) (p x)) = fun x : M => max (p x) (q x) := by
    funext x
    exact max_comm _ _
  have hqp : IsThetaPshPotential theta.val (fun x => max (q x) (p x)) := by
    rw [hfun]; exact hpq
  have h := measure_inter_lt_left theta hq hp hqp hs
  rw [diagonalPotentialMeasure_congr hqp hpq hfun] at h
  exact h

/-! ## Xia's Lemma 2.4.2 -/

/-- The closed-set case of (2.17). -/
theorem measure_closed_ge (hn : 0 < n) (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (hv : IsThetaPshPotential theta.val v)
    (hmax : IsThetaPshPotential theta.val (fun x => max (u x) (v x)))
    {C : Set M} (hC : IsClosed C) :
    diagonalPotentialMeasure theta u hu (C ∩ {x : M | v x < u x}) +
        diagonalPotentialMeasure theta v hv (C ∩ {x : M | u x ≤ v x}) ≤
      diagonalPotentialMeasure theta (fun x => max (u x) (v x)) hmax C := by
  classical
  have hCm : MeasurableSet C := hC.measurableSet
  have hus_psh : ∀ j, IsThetaPshPotential theta.val (shiftPot u j) :=
    fun j => hu.add_const _
  have hmax_j : ∀ j, IsThetaPshPotential theta.val (fun x => max (shiftPot u j x) (v x)) :=
    fun j => isThetaPshPotential_shifted hu hv j
  have husmeas : ∀ j, diagonalPotentialMeasure theta (shiftPot u j) (hus_psh j) =
      diagonalPotentialMeasure theta u hu :=
    fun j => diagonalPotentialMeasure_add_const theta hu _ (hus_psh j)
  -- the per-stage lower bound, from plurifine locality
  have hlow : ∀ j, diagonalPotentialMeasure theta u hu
        (C ∩ {x : M | v x < shiftPot u j x}) +
      diagonalPotentialMeasure theta v hv (C ∩ {x : M | shiftPot u j x < v x}) ≤
      diagonalPotentialMeasure theta (shifted u v j)
        (isThetaPshPotential_shifted hu hv j) C := by
    intro j
    have h1 : diagonalPotentialMeasure theta (shifted u v j)
        (isThetaPshPotential_shifted hu hv j) (C ∩ {x : M | v x < shiftPot u j x}) =
        diagonalPotentialMeasure theta u hu (C ∩ {x : M | v x < shiftPot u j x}) := by
      rw [← husmeas j]
      exact measure_inter_lt_left theta (hus_psh j) hv (hmax_j j) hCm
    have h2 : diagonalPotentialMeasure theta (shifted u v j)
        (isThetaPshPotential_shifted hu hv j) (C ∩ {x : M | shiftPot u j x < v x}) =
        diagonalPotentialMeasure theta v hv (C ∩ {x : M | shiftPot u j x < v x}) :=
      measure_inter_lt_right theta (hus_psh j) hv (hmax_j j) hCm
    have hdisj : Disjoint (C ∩ {x : M | v x < shiftPot u j x})
        (C ∩ {x : M | shiftPot u j x < v x}) := by
      refine Set.disjoint_left.mpr fun x hx hx' => ?_
      have h1 : v x < shiftPot u j x := hx.2
      have h2 : shiftPot u j x < v x := hx'.2
      exact absurd (h1.trans h2) (lt_irrefl _)
    rw [← h1, ← h2, ← measure_union hdisj
      (hCm.inter (measurableSet_potential_lt hv (hus_psh j)))]
    refine measure_mono ?_
    rintro x (hx | hx) <;> exact hx.1
  -- `{u ≤ v}` sits inside every strict set `{shiftPot u j < v}`, up to the poles of `v`
  have hpole : diagonalPotentialMeasure theta v hv {x : M | v x = ⊥} = 0 :=
    GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate
      (fun _ : Fin n => hv.1) hv
  have hBsub : ∀ j, C ∩ {x : M | u x ≤ v x} ⊆
      (C ∩ {x : M | shiftPot u j x < v x}) ∪ {x : M | v x = ⊥} := by
    intro j x hx
    rcases eq_or_ne (v x) ⊥ with hb | hb
    · exact Or.inr hb
    · refine Or.inl ⟨hx.1, ?_⟩
      show shiftPot u j x < v x
      have hle : u x ≤ v x := hx.2
      rcases eq_or_ne (u x) ⊥ with hub | hub
      · have hbot : shiftPot u j x = ⊥ := by rw [shiftPot_apply, hub, EReal.bot_add]
        rw [hbot]
        exact Ne.bot_lt hb
      · refine lt_of_lt_of_le ?_ hle
        rw [shiftPot_apply]
        lift u x to ℝ using ⟨hu.1.quasiPlurisubharmonic.ne_top x, hub⟩ with a ha
        rw [← EReal.coe_add]
        exact EReal.coe_lt_coe_iff.mpr (by linarith [shift_pos j])
  have hBle : ∀ j, diagonalPotentialMeasure theta v hv (C ∩ {x : M | u x ≤ v x}) ≤
      diagonalPotentialMeasure theta v hv (C ∩ {x : M | shiftPot u j x < v x}) := by
    intro j
    calc diagonalPotentialMeasure theta v hv (C ∩ {x : M | u x ≤ v x})
        ≤ diagonalPotentialMeasure theta v hv
            ((C ∩ {x : M | shiftPot u j x < v x}) ∪ {x : M | v x = ⊥}) :=
          measure_mono (hBsub j)
      _ ≤ diagonalPotentialMeasure theta v hv (C ∩ {x : M | shiftPot u j x < v x}) +
            diagonalPotentialMeasure theta v hv {x : M | v x = ⊥} := measure_union_le _ _
      _ = diagonalPotentialMeasure theta v hv
            (C ∩ {x : M | shiftPot u j x < v x}) := by rw [hpole, add_zero]
  -- the sets increase
  have hAmono : Monotone (fun j => C ∩ {x : M | v x < shiftPot u j x}) := by
    intro j k hjk x hx
    exact ⟨hx.1, lt_of_lt_of_le hx.2 (shiftPot_mono u hjk x)⟩
  -- each stage bound survives the limit
  have hstage : ∀ m, diagonalPotentialMeasure theta u hu
        (C ∩ {x : M | v x < shiftPot u m x}) +
      diagonalPotentialMeasure theta v hv (C ∩ {x : M | u x ≤ v x}) ≤
      diagonalPotentialMeasure theta (fun x => max (u x) (v x)) hmax C := by
    intro m
    refine le_trans ?_ (limsup_closed_le hn omega hu hv hmax hC)
    refine Filter.le_limsup_of_frequently_le
      (Filter.Eventually.frequently ((Filter.eventually_ge_atTop m).mono fun j hj => ?_))
    exact le_trans (add_le_add (measure_mono (hAmono hj)) (hBle j)) (hlow j)
  -- and they exhaust `{v < u}`
  have hexh : (⋃ m, C ∩ {x : M | v x < shiftPot u m x}) = C ∩ {x : M | v x < u x} := by
    ext x
    simp only [mem_iUnion, mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨m, hxC, hxm⟩
      exact ⟨hxC, lt_of_lt_of_le hxm (shiftPot_le u m x)⟩
    · rintro ⟨hxC, hxlt⟩
      have hub : u x ≠ ⊥ := fun h => absurd (h ▸ hxlt) (by simp)
      rcases eq_or_ne (v x) ⊥ with hb | hb
      · refine ⟨0, hxC, ?_⟩
        rw [hb, shiftPot_apply]
        refine Ne.bot_lt ?_
        lift u x to ℝ using ⟨hu.1.quasiPlurisubharmonic.ne_top x, hub⟩ with a ha
        rw [← EReal.coe_add]
        exact EReal.coe_ne_bot _
      · lift u x to ℝ using ⟨hu.1.quasiPlurisubharmonic.ne_top x, hub⟩ with a ha
        lift v x to ℝ using ⟨hv.1.quasiPlurisubharmonic.ne_top x, hb⟩ with b hbb
        have hba : b < a := by exact_mod_cast hxlt
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.mpr hba)
        refine ⟨m, hxC, ?_⟩
        rw [shiftPot_apply, ← ha, ← EReal.coe_add]
        refine EReal.coe_lt_coe_iff.mpr ?_
        have hs : shift m < a - b := by simpa [shift] using hm
        linarith
  have hsup : diagonalPotentialMeasure theta u hu (C ∩ {x : M | v x < u x}) ≤
      ⨆ m, diagonalPotentialMeasure theta u hu (C ∩ {x : M | v x < shiftPot u m x}) := by
    rw [← hexh]
    exact le_of_tendsto (MeasureTheory.tendsto_measure_iUnion_atTop hAmono)
      (Eventually.of_forall fun m => le_iSup _ m)
  calc diagonalPotentialMeasure theta u hu (C ∩ {x : M | v x < u x}) +
        diagonalPotentialMeasure theta v hv (C ∩ {x : M | u x ≤ v x})
      ≤ (⨆ m, diagonalPotentialMeasure theta u hu
            (C ∩ {x : M | v x < shiftPot u m x})) +
          diagonalPotentialMeasure theta v hv (C ∩ {x : M | u x ≤ v x}) :=
        add_le_add hsup le_rfl
    _ = ⨆ m, (diagonalPotentialMeasure theta u hu
            (C ∩ {x : M | v x < shiftPot u m x}) +
          diagonalPotentialMeasure theta v hv (C ∩ {x : M | u x ≤ v x})) :=
        ENNReal.iSup_add _
    _ ≤ _ := iSup_le hstage

/-- The positive-dimensional case of (2.17). -/
theorem measure_max_ge_of_pos (hn : 0 < n) (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (hv : IsThetaPshPotential theta.val v)
    (hmax : IsThetaPshPotential theta.val (fun x => max (u x) (v x)))
    {E : Set M} (hE : MeasurableSet E) :
    diagonalPotentialMeasure theta u hu (E ∩ {x : M | v x < u x}) +
        diagonalPotentialMeasure theta v hv (E ∩ {x : M | u x ≤ v x}) ≤
      diagonalPotentialMeasure theta (fun x => max (u x) (v x)) hmax E := by
  classical
  let _ := pseudoMetrizableSpace_of_isComplexManifold n M
  set nu : Measure M :=
    (diagonalPotentialMeasure theta u hu).restrict {x : M | v x < u x} +
      (diagonalPotentialMeasure theta v hv).restrict {x : M | u x ≤ v x} with hnu
  have hval : ∀ s : Set M, MeasurableSet s →
      nu s = diagonalPotentialMeasure theta u hu (s ∩ {x : M | v x < u x}) +
        diagonalPotentialMeasure theta v hv (s ∩ {x : M | u x ≤ v x}) := by
    intro s hs
    simp only [hnu, Measure.coe_add, Pi.add_apply, Measure.restrict_apply hs]
  have : IsFiniteMeasure nu := by
    refine ⟨?_⟩
    rw [hval univ MeasurableSet.univ]
    exact ENNReal.add_lt_top.2
      ⟨diagonalPotentialMeasure_lt_top omega theta hu _,
        diagonalPotentialMeasure_lt_top omega theta hv _⟩
  rw [← hval E hE]
  refine le_of_forall_lt fun r hr => ?_
  obtain ⟨C, hCE, hCclosed, hrC⟩ :=
    Measure.WeaklyRegular.innerRegular_measurable (μ := nu) ⟨hE, measure_ne_top _ _⟩ r hr
  calc r < nu C := hrC
    _ ≤ diagonalPotentialMeasure theta (fun x => max (u x) (v x)) hmax C := by
        rw [hval C hCclosed.measurableSet]
        exact measure_closed_ge hn omega hu hv hmax hCclosed
    _ ≤ diagonalPotentialMeasure theta (fun x => max (u x) (v x)) hmax E :=
        measure_mono hCE

/-- **Xia, SGPT, Lemma 2.4.2, inequality (2.17).**  For `u, v` in
`PSH(X, theta)` whose maximum is again a genuine potential,

  `theta^n_{max(u,v)} >= 1_{v < u} theta^n_u + 1_{u <= v} theta^n_v`

as measures.  The contact set `{u = v}` is attached here to `v`; the form with
it attached to `u` is `measure_max_ge'` below, obtained by exchanging the two
potentials.  No truncation at `V_theta - k` is used, the maximum is not assumed
bounded, and the dimension is not assumed positive. -/
theorem measure_max_ge (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (hv : IsThetaPshPotential theta.val v)
    (hmax : IsThetaPshPotential theta.val (fun x => max (u x) (v x)))
    {E : Set M} (hE : MeasurableSet E) :
    diagonalPotentialMeasure theta u hu (E ∩ {x : M | v x < u x}) +
        diagonalPotentialMeasure theta v hv (E ∩ {x : M | u x ≤ v x}) ≤
      diagonalPotentialMeasure theta (fun x => max (u x) (v x)) hmax E := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · rw [diagonalPotentialMeasure_eq_of_dim_zero h0 theta hu hmax,
      diagonalPotentialMeasure_eq_of_dim_zero h0 theta hv hmax]
    have hdisj : Disjoint (E ∩ {x : M | v x < u x}) (E ∩ {x : M | u x ≤ v x}) := by
      refine Set.disjoint_left.mpr fun x hx hx' => ?_
      have h1 : v x < u x := hx.2
      have h2 : u x ≤ v x := hx'.2
      exact absurd (h1.trans_le h2) (lt_irrefl _)
    have hunion : (E ∩ {x : M | v x < u x}) ∪ (E ∩ {x : M | u x ≤ v x}) = E := by
      ext x
      simp only [mem_union, mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro (hx | hx) <;> exact hx.1
      · intro hx
        rcases lt_or_ge (v x) (u x) with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, h⟩
    rw [← measure_union hdisj (hE.inter (measurableSet_potential_le hu hv)), hunion]
  · exact measure_max_ge_of_pos hn omega hu hv hmax hE

/-- **Xia's (2.17) in the orientation of the source**, with the contact set
attached to `u`. -/
theorem measure_max_ge' (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (hv : IsThetaPshPotential theta.val v)
    (hmax : IsThetaPshPotential theta.val (fun x => max (u x) (v x)))
    {E : Set M} (hE : MeasurableSet E) :
    diagonalPotentialMeasure theta u hu (E ∩ {x : M | v x ≤ u x}) +
        diagonalPotentialMeasure theta v hv (E ∩ {x : M | u x < v x}) ≤
      diagonalPotentialMeasure theta (fun x => max (u x) (v x)) hmax E := by
  have hfun : (fun x : M => max (v x) (u x)) = fun x : M => max (u x) (v x) := by
    funext x
    exact max_comm _ _
  have hmax' : IsThetaPshPotential theta.val (fun x => max (v x) (u x)) := by
    rw [hfun]; exact hmax
  have h := measure_max_ge omega hv hu hmax' hE
  rw [diagonalPotentialMeasure_congr hmax' hmax hfun] at h
  exact le_trans (le_of_eq (add_comm _ _)) h

/-- **The contact comparison of Lemma 2.4.2.**  For `u <= v` the two
non-pluripolar measures are ordered on the contact set `{u = v}`. -/
theorem contact_measure_le (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (hv : IsThetaPshPotential theta.val v)
    (hle : u ≤ v) {E : Set M} (hE : MeasurableSet E) :
    diagonalPotentialMeasure theta u hu (E ∩ {x : M | u x = v x}) ≤
      diagonalPotentialMeasure theta v hv (E ∩ {x : M | u x = v x}) := by
  classical
  have hfun : (fun x : M => max (u x) (v x)) = v := by
    funext x
    exact max_eq_right (hle x)
  have hmax : IsThetaPshPotential theta.val (fun x => max (u x) (v x)) := by
    rw [hfun]; exact hv
  have hcontact : {x : M | v x ≤ u x} = {x : M | u x = v x} := by
    ext x
    exact ⟨fun h => le_antisymm (hle x) h, fun h => le_of_eq h.symm⟩
  have h := measure_max_ge' omega hu hv hmax hE
  rw [diagonalPotentialMeasure_congr hmax hv hfun, hcontact] at h
  -- split `E` along the contact set
  have hsplit : diagonalPotentialMeasure theta v hv E =
      diagonalPotentialMeasure theta v hv (E ∩ {x : M | u x = v x}) +
        diagonalPotentialMeasure theta v hv (E ∩ {x : M | u x < v x}) := by
    have hdisj : Disjoint (E ∩ {x : M | u x = v x}) (E ∩ {x : M | u x < v x}) := by
      refine Set.disjoint_left.mpr fun x hx hx' => ?_
      have h1 : u x = v x := hx.2
      have h2 : u x < v x := hx'.2
      exact absurd h1 (ne_of_lt h2)
    have hunion : (E ∩ {x : M | u x = v x}) ∪ (E ∩ {x : M | u x < v x}) = E := by
      ext x
      simp only [mem_union, mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro (hx | hx) <;> exact hx.1
      · intro hx
        rcases lt_or_eq_of_le (hle x) with h | h
        · exact Or.inr ⟨hx, h⟩
        · exact Or.inl ⟨hx, h⟩
    conv_lhs => rw [← hunion]
    exact measure_union hdisj (hE.inter (measurableSet_potential_lt hv hu))
  rw [hsplit] at h
  have hfin : diagonalPotentialMeasure theta v hv (E ∩ {x : M | u x < v x}) ≠ ⊤ :=
    (diagonalPotentialMeasure_lt_top omega theta hv _).ne
  exact (ENNReal.add_le_add_iff_right hfin).1 h

end

end SGPT.Foundations.Analysis.Pending.MaxMassDecomposition
