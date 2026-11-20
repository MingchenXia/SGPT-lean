import SGPT.Foundations.Analysis.Pending.RooftopMassDecomposition
import SGPT.Foundations.Analysis.Pending.IncreasingLimitOpenMeasure
import SGPT.Foundations.Analysis.FirstPass.FiniteTranslation
import SGPT.Foundations.Analysis.Pending.RooftopFeasibility
import SGPT.Foundations.Analysis.Pending.GlobalSlotComparison

set_option autoImplicit false

/-!
# Xia's Corollary 3.1.1 from Lemma 3.1.1

Let `u, v ∈ PSH(X, θ)` and let `η = sup*_{C > 0} (v + C) ∧ u` be the regularized
limit of the shifted rooftop family, `P_θ[v](u)` in Xia's notation.
**Corollary 3.1.1** (`xia-sgpt:page-0101`) is

  `θ^n_η ≤ 1_{η = u} θ^n_u`.

This file carries out the source proof from the single named interface
`Pending.RooftopMassDecomposition` (Lemma 3.1.1):

* Lemma 3.1.1 applied to `(v + C) ∧ u` bounds `θ^n_{(v+C) ∧ u}` by
  `1_{(v+C)∧u = u} θ^n_u + 1_{(v+C)∧u = v+C} θ^n_{v+C}`.  The first contact set
  is inside `{η = u}` because `(v+C)∧u ≤ η ≤ u`, and the second is inside
  `{v + C ≤ u}` because `(v+C)∧u ≤ u`.
* `θ^n_{v+C} = θ^n_v` (constant translation invariance), so the second term is
  one fixed finite measure evaluated on the decreasing family
  `{v + C ≤ u}`, whose intersection over `C ∈ ℕ` is contained in the pole set
  `{v = -∞}`; the non-pluripolar measure does not charge it, so the term tends
  to `0`.  This is Xia's "dominated convergence" step.
* The semicontinuity theorem Corollary 2.4.1 in its measure form on open sets
  (`Pending.IncreasingLimitOpenMeasure`) gives
  `θ^n_η G ≤ liminf_C θ^n_{(v+C)∧u} G` for every open `G`.
* Outer regularity of both sides (`Pending.DiagonalMeasureRegularity`) turns the
  resulting inequality on open sets into the inequality on all sets.

The family hypothesis `hw` is the one the consumers of Corollary 3.1.1 already
carry (`ShiftedRooftopContact.shiftedRooftopLimit_eq_of_mass`,
`RelativeFullMass`): every member of the shifted rooftop family is a genuine
`theta`-PSH potential.  That every member lies below the ceiling `u` is not a
hypothesis: it follows from `u`, `v` being `theta`-PSH
(`FirstPass.rooftopEnvelope_min_add_const_le_obstacles`).
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.ShiftedRooftopContactProof

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.DiagonalMeasureRegularity
open SGPT.Foundations.Analysis.Pending.IncreasingLimitOpenMeasure
open SGPT.Foundations.Analysis.Pending.RooftopMassDecomposition
open SGPT.Foundations.Analysis.Pending.ShiftedRooftopLimit

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The decreasing family `{v + j ≤ u}` exhausts only the pole set of `v`: if
`v x` is finite the inequality fails for large `j`, because `u` never takes the
value `⊤`. -/
theorem iInter_setOf_add_nat_le_subset_poles {theta : SmoothRealForm n M 2}
    {u v : M → EReal} (hu : ThetaPlurisubharmonic theta u) :
    (⋂ j : ℕ, {x | v x + ((j : ℝ) : EReal) ≤ u x}) ⊆ {x | v x = ⊥} := by
  intro x hx
  simp only [mem_iInter, mem_ofPred_eq] at hx
  by_contra hvx
  have hut : u x ≠ ⊤ := hu.quasiPlurisubharmonic.ne_top x
  -- `v x` cannot be `⊤`
  have hvt : v x ≠ ⊤ := by
    intro h
    exact hut (top_le_iff.mp (by simpa [h] using hx 0))
  lift v x to ℝ using ⟨hvt, hvx⟩ with a ha
  -- `u x` cannot be `⊥`
  have hub : u x ≠ ⊥ := by
    intro h
    have := hx 0
    rw [h] at this
    simp at this
  lift u x to ℝ using ⟨hut, hub⟩ with b hb
  obtain ⟨j, hj⟩ := exists_nat_gt (b - a)
  have := hx j
  rw [← EReal.coe_add, EReal.coe_le_coe_iff] at this
  linarith


/-- **Xia, Corollary 3.1.1 on open sets.**  `theta^n_eta G ≤ theta^n_u (G ∩ {eta = u})`
for every open `G`, where `eta = sup*_{C} (v + C) ∧ u`. -/
theorem diagonalPotentialMeasure_shiftedRooftopLimit_isOpen_le_contact [ConnectedSpace M]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u)
    (hv : IsThetaPshPotential theta.val v)
    (c : ℕ → ℝ) (hcmono : Monotone c) (hcex : ∀ k : ℕ, ∃ j : ℕ, (k : ℝ) ≤ c j)
    (hlim : shiftedRooftopLimit theta u v =
      uscRegularization (⨆ j : ℕ, shiftedRooftop theta u v (c j)))
    (hw : ∀ j : ℕ, IsThetaPshPotential theta.val (shiftedRooftop theta u v (c j)))
    (heta : IsThetaPshPotential theta.val (shiftedRooftopLimit theta u v))
    {G : Set M} (hG : IsOpen G) :
    diagonalPotentialMeasure theta (shiftedRooftopLimit theta u v) heta G ≤
      diagonalPotentialMeasure theta u hu
        (G ∩ {x | shiftedRooftopLimit theta u v x = u x}) := by
  classical
  have hle : ∀ C : ℝ, shiftedRooftop theta u v C ≤ u := fun C =>
    (rooftopEnvelope_min_add_const_le_obstacles hu.1 hv.1 C).1
  have hWmono : Monotone (fun j : ℕ => shiftedRooftop theta u v (c j)) :=
    fun j k hjk => shiftedRooftop_monotone theta u v (hcmono hjk)
  have hetale : shiftedRooftopLimit theta u v ≤ u := shiftedRooftopLimit_le theta hu hle
  set cst : ℝ≥0∞ := diagonalPotentialMeasure theta u hu
      (G ∩ {x | shiftedRooftopLimit theta u v x = u x}) with hcstdef
  set A : ℕ → Set M := fun j => G ∩ {x | v x + ((c j : ℝ) : EReal) ≤ u x} with hAdef
  -- Step 1: the semicontinuity theorem in measure form on the open set `G`.
  have hetalim : IsThetaPshPotential theta.val
      (uscRegularization (⨆ j : ℕ, shiftedRooftop theta u v (c j))) := hlim ▸ heta
  have hstepA : diagonalPotentialMeasure theta (shiftedRooftopLimit theta u v) heta G ≤
      liminf (fun j : ℕ => diagonalPotentialMeasure theta
        (shiftedRooftop theta u v (c j)) (hw j) G) atTop := by
    have hmeas : diagonalPotentialMeasure theta (shiftedRooftopLimit theta u v) heta =
        diagonalPotentialMeasure theta
          (uscRegularization (⨆ j : ℕ, shiftedRooftop theta u v (c j))) hetalim := by
      exact GlobalDiagonalScaling.globalMixedMeasure_congr rfl (funext fun _ => hlim)
        (fun _ => heta.1) (fun _ => hetalim.1)
    rw [hmeas]
    exact diagonalPotentialMeasure_isOpen_le_liminf
      (fun j : ℕ => shiftedRooftop theta u v (c j)) hw hWmono hetalim hG
  -- Step 2: Lemma 3.1.1 for each member of the family.
  have hstepB : ∀ j : ℕ, diagonalPotentialMeasure theta
      (shiftedRooftop theta u v (c j)) (hw j) G ≤
      diagonalPotentialMeasure theta v hv (A j) + cst := by
    intro j
    have hvj : IsThetaPshPotential theta.val (fun x => v x + ((c j : ℝ) : EReal)) :=
      hv.add_const (c j)
    have key := diagonalPotentialMeasure_rooftopEnvelope_min_le omega theta hu hvj
      (hw j) G
    refine key.trans ?_
    rw [add_comm]
    refine add_le_add ?_ ?_
    · rw [diagonalPotentialMeasure_add_const theta hv (c j) hvj]
      refine measure_mono fun x hx => ⟨hx.1, ?_⟩
      have h0 : rooftopEnvelope theta.val
          (fun y => min (u y) (v y + ((c j : ℝ) : EReal))) x ≤ u x := hle (c j) x
      rw [hx.2] at h0
      exact h0
    · refine measure_mono fun x hx => ⟨hx.1, ?_⟩
      have h1 : shiftedRooftop theta u v (c j) x ≤ shiftedRooftopLimit theta u v x := by
        rw [hlim]
        exact (le_iSup (fun k : ℕ => shiftedRooftop theta u v (c k)) j x).trans
          (le_uscRegularization _ x)
      have hx2 : shiftedRooftop theta u v (c j) x = u x := hx.2
      rw [hx2] at h1
      exact le_antisymm (hetale x) h1
  -- Step 3: the `theta^n_v` term tends to zero.
  have hAmeas : ∀ j : ℕ, MeasurableSet (A j) := by
    intro j
    refine hG.measurableSet.inter (measurableSet_le ?_ (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hu.1))
    exact (Monotone.measurable (f := fun y : EReal => y + ((c j : ℝ) : EReal))
      (fun _ _ h => add_le_add h le_rfl)).comp (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hv.1)
  have hAanti : Antitone A := by
    intro j k hjk x hx
    refine ⟨hx.1, ?_⟩
    have h2 : v x + ((c j : ℝ) : EReal) ≤ v x + ((c k : ℝ) : EReal) :=
      add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (hcmono hjk))
    exact le_trans h2 hx.2
  have hnull : diagonalPotentialMeasure theta v hv (⋂ j, A j) = 0 := by
    refine measure_mono_null ?_
      (GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate
        (θ := fun _ : Fin n => theta) (u := fun _ => v) (fun _ => hv.1) hv)
    refine subset_trans ?_ (iInter_setOf_add_nat_le_subset_poles (v := v) hu.1)
    refine subset_iInter fun k => ?_
    obtain ⟨j, hj⟩ := hcex k
    refine (iInter_subset A j).trans ?_
    intro x hx
    exact le_trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hj)) hx.2
  have htend : Tendsto (fun j => diagonalPotentialMeasure theta v hv (A j)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := diagonalPotentialMeasure theta v hv)
      (fun j => (hAmeas j).nullMeasurableSet) hAanti
      ⟨0, (diagonalPotentialMeasure_lt_top omega theta hv (A 0)).ne⟩
    rwa [hnull] at h
  have htend2 : Tendsto (fun j => diagonalPotentialMeasure theta v hv (A j) + cst)
      atTop (𝓝 cst) := by
    simpa using htend.add (tendsto_const_nhds (x := cst) (f := (atTop : Filter ℕ)))
  -- Step 4: assemble.
  refine hstepA.trans ((liminf_le_liminf (Eventually.of_forall hstepB)).trans ?_)
  exact le_of_eq htend2.liminf_eq

/-- **Xia, Corollary 3.1.1** (`xia-sgpt:page-0101`), on arbitrary sets:
`theta^n_eta ≤ 1_{eta = u} theta^n_u` for `eta = sup*_{C > 0} (v + C) ∧ u`.
Proved from the open-set form by outer regularity of both measures. -/
theorem diagonalPotentialMeasure_shiftedRooftopLimit_le_contact_of_seq [ConnectedSpace M]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u)
    (hv : IsThetaPshPotential theta.val v)
    (c : ℕ → ℝ) (hcmono : Monotone c) (hcex : ∀ k : ℕ, ∃ j : ℕ, (k : ℝ) ≤ c j)
    (hlim : shiftedRooftopLimit theta u v =
      uscRegularization (⨆ j : ℕ, shiftedRooftop theta u v (c j)))
    (hw : ∀ j : ℕ, IsThetaPshPotential theta.val (shiftedRooftop theta u v (c j)))
    (heta : IsThetaPshPotential theta.val (shiftedRooftopLimit theta u v))
    (B : Set M) :
    diagonalPotentialMeasure theta (shiftedRooftopLimit theta u v) heta B ≤
      diagonalPotentialMeasure theta u hu
        (B ∩ {x | shiftedRooftopLimit theta u v x = u x}) := by
  classical
  have hCmeas : MeasurableSet {x | shiftedRooftopLimit theta u v x = u x} := by
    have hset : {x | shiftedRooftopLimit theta u v x = u x} =
        {x | shiftedRooftopLimit theta u v x ≤ u x} ∩
          {x | u x ≤ shiftedRooftopLimit theta u v x} := by
      ext x
      exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩
    rw [hset]
    exact (measurableSet_le (GlobalSlotComparison.ThetaPlurisubharmonic.measurable heta.1)
        (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hu.1)).inter
      (measurableSet_le (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hu.1)
        (GlobalSlotComparison.ThetaPlurisubharmonic.measurable heta.1))
  set nu' : Measure M := (diagonalPotentialMeasure theta u hu).restrict
    {x | shiftedRooftopLimit theta u v x = u x} with hnu'
  have hnu'apply : ∀ S : Set M, nu' S = diagonalPotentialMeasure theta u hu
      (S ∩ {x | shiftedRooftopLimit theta u v x = u x}) := fun S =>
    Measure.restrict_apply' hCmeas
  have : IsFiniteMeasure nu' := by
    refine ⟨?_⟩
    rw [hnu'apply]
    exact diagonalPotentialMeasure_lt_top omega theta hu _
  let _ := pseudoMetrizableSpace_of_isComplexManifold n M
  have : nu'.OuterRegular := inferInstance
  rw [← hnu'apply B, Set.measure_eq_iInf_isOpen B nu']
  refine le_iInf fun G => le_iInf fun hBG => le_iInf fun hGopen => ?_
  refine le_trans (measure_mono hBG) ?_
  rw [hnu'apply]
  exact diagonalPotentialMeasure_shiftedRooftopLimit_isOpen_le_contact omega theta
    hu hv c hcmono hcex hlim hw heta hGopen

/-- Corollary 3.1.1 for a family whose every member is a genuine potential
below the ceiling: the special case of the sequence `C = 0, 1, 2, ...`. -/
theorem diagonalPotentialMeasure_shiftedRooftopLimit_le_contact_of_family [ConnectedSpace M]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u)
    (hv : IsThetaPshPotential theta.val v)
    (hw : ∀ C : ℝ, IsThetaPshPotential theta.val (shiftedRooftop theta u v C))
    (heta : IsThetaPshPotential theta.val (shiftedRooftopLimit theta u v))
    (B : Set M) :
    diagonalPotentialMeasure theta (shiftedRooftopLimit theta u v) heta B ≤
      diagonalPotentialMeasure theta u hu
        (B ∩ {x | shiftedRooftopLimit theta u v x = u x}) :=
  diagonalPotentialMeasure_shiftedRooftopLimit_le_contact_of_seq omega theta hu hv
    (fun j : ℕ => (j : ℝ)) Nat.mono_cast (fun k => ⟨k, le_rfl⟩) rfl
    (fun j => hw ((j : ℕ) : ℝ)) heta B

/-- The null form of Corollary 3.1.1: the measure of `eta` gives no mass to the
set where `eta` is strictly below its ceiling. -/
theorem diagonalPotentialMeasure_shiftedRooftopLimit_lt_eq_zero_of_family [ConnectedSpace M]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u)
    (hv : IsThetaPshPotential theta.val v)
    (hw : ∀ C : ℝ, IsThetaPshPotential theta.val (shiftedRooftop theta u v C))
    (heta : IsThetaPshPotential theta.val (shiftedRooftopLimit theta u v)) :
    diagonalPotentialMeasure theta (shiftedRooftopLimit theta u v) heta
      {x | shiftedRooftopLimit theta u v x < u x} = 0 := by
  have hbound := diagonalPotentialMeasure_shiftedRooftopLimit_le_contact_of_family
    omega theta hu hv hw heta {x | shiftedRooftopLimit theta u v x < u x}
  have hempty : {x | shiftedRooftopLimit theta u v x < u x} ∩
      {x | shiftedRooftopLimit theta u v x = u x} = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro hlt heq
    exact absurd heq (ne_of_lt hlt)
  rw [hempty] at hbound
  simpa using hbound


omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- **The feasibility gap is closed by the limit itself.**  If the regularized
limit `eta` is a genuine potential then it is not identically `-∞`, so some
shifted rooftop has a competitor; and the competitor sets increase with the
translation, so all later ones do too. -/
theorem exists_rooftopCompetitors_nonempty_of_limit [Nonempty M]
    (theta : ClosedRealOneOneForm n M) {u v : M → EReal}
    (heta : IsThetaPshPotential theta.val (shiftedRooftopLimit theta u v)) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j →
      (rooftopCompetitors theta.val
        (fun x => min (u x) (v x + ((j : ℝ) : EReal)))).Nonempty := by
  by_cases h : ∃ j₀ : ℕ, (rooftopCompetitors theta.val
      (fun x => min (u x) (v x + ((j₀ : ℝ) : EReal)))).Nonempty
  · obtain ⟨j₀, hj₀⟩ := h
    refine ⟨j₀, fun j hj => hj₀.mono (rooftopCompetitors_mono fun x => ?_)⟩
    exact min_le_min le_rfl (add_le_add le_rfl
      (EReal.coe_le_coe_iff.mpr (by exact_mod_cast hj)))
  · exfalso
    simp only [not_exists, Set.not_nonempty_iff_eq_empty] at h
    have hbot : ∀ j : ℕ, shiftedRooftop theta u v (j : ℝ) = ⊥ := fun j =>
      rooftopEnvelope_of_empty (h j)
    have hsup : (⨆ j : ℕ, shiftedRooftop theta u v (j : ℝ)) = (⊥ : M → EReal) := by
      funext x
      simp only [iSup_apply, hbot]
      simp
    have hetabot : shiftedRooftopLimit theta u v = (⊥ : M → EReal) := by
      rw [shiftedRooftopLimit, hsup]
      exact uscRegularization_const ⊥
    obtain ⟨y, -, hy⟩ := heta.2 (Classical.arbitrary M) univ isOpen_univ (mem_univ _)
    exact hy (congrFun hetabot y)

omit [MeasurableSpace M] [BorelSpace M] in
/-- The tail of the shifted rooftop family consists of genuine `theta`-PSH
potentials, from the nondegeneracy of the limit alone. -/
theorem exists_isThetaPshPotential_shiftedRooftop_tail [Nonempty M]
    (theta : ClosedRealOneOneForm n M) {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u)
    (heta : IsThetaPshPotential theta.val (shiftedRooftopLimit theta u v)) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j →
      IsThetaPshPotential theta.val (shiftedRooftop theta u v (j : ℝ)) := by
  obtain ⟨j₀, hj₀⟩ := exists_rooftopCompetitors_nonempty_of_limit theta heta
  refine ⟨j₀, fun j hj => ?_⟩
  exact isThetaPshPotential_rooftop_of_nonempty (hj₀ j hj)
    (rooftopCompetitors_min_add_const_uniformlyBoundedAbove theta u v hu ((j : ℝ)))

/-- **Xia, Corollary 3.1.1** (`xia-sgpt:page-0101`) with no family hypotheses:
`theta^n_eta ≤ 1_{eta = u} theta^n_u` for `eta = sup*_{C > 0} (v + C) ∧ u`,
assuming only that `u`, `v` and `eta` are genuine `theta`-PSH potentials.  The
one fact that the sequence form takes as a hypothesis -- that the members are
genuine potentials -- is supplied here by
`exists_isThetaPshPotential_shiftedRooftop_tail`; that they lie below `u` is
derived inside the sequence form from
`FirstPass.rooftopEnvelope_min_add_const_le_obstacles`. -/
theorem diagonalPotentialMeasure_shiftedRooftopLimit_le_contact_of_potential [ConnectedSpace M]
    [Nonempty M] (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u)
    (hv : IsThetaPshPotential theta.val v)
    (heta : IsThetaPshPotential theta.val (shiftedRooftopLimit theta u v))
    (B : Set M) :
    diagonalPotentialMeasure theta (shiftedRooftopLimit theta u v) heta B ≤
      diagonalPotentialMeasure theta u hu
        (B ∩ {x | shiftedRooftopLimit theta u v x = u x}) := by
  classical
  obtain ⟨j₀, hj₀⟩ := exists_isThetaPshPotential_shiftedRooftop_tail theta hu heta
  have hWmono : Monotone (fun j : ℕ => shiftedRooftop theta u v (j : ℝ)) :=
    fun j k hjk => shiftedRooftop_monotone theta u v (Nat.mono_cast hjk)
  have hsupeq : (⨆ j : ℕ, shiftedRooftop theta u v ((j : ℝ))) =
      ⨆ j : ℕ, shiftedRooftop theta u v (((j₀ + j : ℕ) : ℝ)) := by
    refine le_antisymm (iSup_le fun j => ?_) (iSup_le fun j => ?_)
    · exact le_trans (hWmono (Nat.le_add_left j j₀))
        (le_iSup (fun k : ℕ => shiftedRooftop theta u v (((j₀ + k : ℕ) : ℝ))) j)
    · exact le_iSup (fun k : ℕ => shiftedRooftop theta u v ((k : ℝ))) (j₀ + j)
  have hlim : shiftedRooftopLimit theta u v =
      uscRegularization (⨆ j : ℕ, shiftedRooftop theta u v (((j₀ + j : ℕ) : ℝ))) := by
    rw [shiftedRooftopLimit, hsupeq]
  exact diagonalPotentialMeasure_shiftedRooftopLimit_le_contact_of_seq omega theta
    hu hv (fun j : ℕ => ((j₀ + j : ℕ) : ℝ))
    (fun a b h => Nat.mono_cast (Nat.add_le_add_left h j₀))
    (fun k => ⟨k, Nat.mono_cast (Nat.le_add_left k j₀)⟩)
    hlim (fun j => hj₀ (j₀ + j) (Nat.le_add_right j₀ j)) heta B


end

end SGPT.Foundations.Analysis.Pending.ShiftedRooftopContactProof
