import SGPT.Foundations.Analysis.Pending.RooftopContactConcentration
import SGPT.Foundations.Analysis.Pending.ShiftedRooftopContactProof

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Xia's contact theorems for a BIG class, without the non-big branch

`Pending.RooftopMinConcentration` proves Xia SGPT Theorem 2.4.4 at the obstacle `min {φ, ψ}` by a
bigness dichotomy; its non-big branch uses `NonBigPotentialMass`, i.e. the named Boucksom input
`BoucksomNonBigSupremumMass` (not a root of the main cone).  The chain built on it —
Xia Lemma 3.1.1 (`RooftopContactConcentration.diagonalPotentialMeasure_rooftopEnvelope_min_le`) and
Xia Corollary 3.1.1 (`ShiftedRooftopContactProof`) — therefore reaches that input even for big
classes.  This module repeats the chain verbatim with a hypothesis `IsBigClass {θ}` in place of the
dichotomy, so that for big classes no named input is used.  Statements are those of the originals
plus `0 < n` and the bigness hypothesis; proofs are the originals with the big branch taken.

Consumer: `TraceFreeLimit` (route F, DX24 Prop. 2.1: contact of model envelopes in the big classes
`γ + ε_jω`).  Sorry-free.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.RooftopContactBigClass

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.DiagonalMeasureRegularity
open SGPT.Foundations.Analysis.Pending.MaxMassDecomposition
open SGPT.Foundations.Analysis.Pending.RooftopEnvelopeNormalization
open SGPT.Foundations.Analysis.Pending.RooftopTruncatedObstacleConcentration
open SGPT.Foundations.Analysis.Pending.RooftopTruncationConcentration
open SGPT.Foundations.Analysis.Pending.IncreasingLimitOpenMeasure
open SGPT.Foundations.Analysis.Pending.RooftopMassDecomposition
open SGPT.Foundations.Analysis.Pending.ShiftedRooftopLimit

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- **Xia SGPT Theorem 2.4.4 at `min {φ, ψ}`, big class** (`RooftopMinConcentration`, big branch). -/
theorem rooftopEnvelope_min_noncontact_eq_zero_of_isBigClass
    (hn : 0 < n) (theta : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (hw : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (phi x) (psi x)))) :
    diagonalPotentialMeasure theta
        (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))) hw
      {x | rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x ≠ phi x ∧
        rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x ≠ psi x} = 0 := by
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · rw [Set.eq_empty_of_isEmpty
      {x : M | rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x ≠ phi x ∧
        rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x ≠ psi x}]
    exact measure_empty
  have hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val) :=
    SGPT.Foundations.Analysis.Pending.thetaPshSupremum_isThetaPshPotential theta.val
      theta.2.1 theta.2.2 hphi.1.hasSmoothLocalPotentials ⟨_, hphi⟩
  -- the rooftop lies below both obstacles
  have hbelow : rooftopEnvelope theta.val (fun x => min (phi x) (psi x)) ≤ phi ∧
      rooftopEnvelope theta.val (fun x => min (phi x) (psi x)) ≤ psi := by
    have hfun : (fun x : M => min (phi x) (psi x + ((0 : ℝ) : EReal))) =
        fun x : M => min (phi x) (psi x) := by
      funext x; simp
    have h := rooftopEnvelope_min_add_const_le_obstacles hphi.1 hpsi.1 0
    rw [hfun] at h
    exact ⟨h.1, fun x => by simpa using h.2 x⟩
  -- the non-contact set is the strict sublevel set of the obstacle
  have hset : {x : M | rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x ≠ phi x ∧
      rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x ≠ psi x} =
      {x : M | rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x <
        min (phi x) (psi x)} := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact lt_min (lt_of_le_of_ne (hbelow.1 x) h1) (lt_of_le_of_ne (hbelow.2 x) h2)
    · intro h
      change rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x <
        min (phi x) (psi x) at h
      exact ⟨(lt_min_iff.mp h).1.ne, (lt_min_iff.mp h).2.ne⟩
  rw [hset]
  -- Step 1.1: normalise both potentials by one common constant
  obtain ⟨Aphi, hAphi⟩ := hphi.exists_global_upper_bound
  obtain ⟨Apsi, hApsi⟩ := hpsi.exists_global_upper_bound
  have hphiA : ∀ x, phi x ≤ ((max Aphi Apsi : ℝ) : EReal) := fun x =>
    (hAphi x).trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _))
  have hpsiA : ∀ x, psi x ≤ ((max Aphi Apsi : ℝ) : EReal) := fun x =>
    (hApsi x).trans (EReal.coe_le_coe_iff.mpr (le_max_right _ _))
  set A : ℝ := max Aphi Apsi with hAdef
  have hshift0 : ∀ {v : M → EReal}, (∀ x, v x ≤ (A : EReal)) →
      ∀ x, v x + ((-A : ℝ) : EReal) ≤ 0 := by
    intro v hv x
    calc v x + ((-A : ℝ) : EReal) ≤ (A : EReal) + ((-A : ℝ) : EReal) :=
          add_le_add (hv x) le_rfl
      _ = 0 := by rw [← EReal.coe_add, add_neg_cancel, EReal.coe_zero]
  have hphi'pot : IsThetaPshPotential theta.val (fun x => phi x + ((-A : ℝ) : EReal)) :=
    hphi.add_const _
  have hpsi'pot : IsThetaPshPotential theta.val (fun x => psi x + ((-A : ℝ) : EReal)) :=
    hpsi.add_const _
  have hphi'0 : ∀ x, phi x + ((-A : ℝ) : EReal) ≤ 0 := hshift0 hphiA
  have hpsi'0 : ∀ x, psi x + ((-A : ℝ) : EReal) ≤ 0 := hshift0 hpsiA
  -- the shift commutes with the minimum
  have hmin : (fun x : M => min (phi x + ((-A : ℝ) : EReal)) (psi x + ((-A : ℝ) : EReal))) =
      fun x : M => min (phi x) (psi x) + ((-A : ℝ) : EReal) := by
    funext x
    exact (Monotone.map_min (f := fun t : EReal => t + ((-A : ℝ) : EReal))
      (fun a b h => add_le_add h le_rfl)).symm
  -- the shift commutes with the envelope
  have henv : rooftopEnvelope theta.val
      (fun x => min (phi x + ((-A : ℝ) : EReal)) (psi x + ((-A : ℝ) : EReal))) =
      fun x => rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x +
        ((-A : ℝ) : EReal) := by
    rw [hmin]
    exact rooftopEnvelope_add_const theta.val (fun y => min (phi y) (psi y)) (-A)
  have hwshift : IsThetaPshPotential theta.val
      (fun x => rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x +
        ((-A : ℝ) : EReal)) := hw.add_const _
  have hw' : IsThetaPshPotential theta.val (rooftopEnvelope theta.val
      (fun x => min (phi x + ((-A : ℝ) : EReal)) (psi x + ((-A : ℝ) : EReal)))) := by
    rw [henv]; exact hwshift
  -- Theorem 2.4.4 for the normalised obstacle
  have hzero := diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_nonpos hn hbig hV
    (upperSemicontinuous_min hphi'pot.1.quasiPlurisubharmonic.upperSemicontinuous
      hpsi'pot.1.quasiPlurisubharmonic.upperSemicontinuous)
    (fun x => (min_le_left _ _).trans (hphi'0 x))
    (RooftopMinConcentration.refTruncationsQuasiContinuous_min hphi'pot hpsi'pot hV hphi'0 hpsi'0) hw'
  -- transport the measure back
  have hmeaseq : diagonalPotentialMeasure theta (rooftopEnvelope theta.val
        (fun x => min (phi x + ((-A : ℝ) : EReal)) (psi x + ((-A : ℝ) : EReal)))) hw' =
      diagonalPotentialMeasure theta
        (rooftopEnvelope theta.val (fun y => min (phi y) (psi y))) hw := by
    rw [diagonalPotentialMeasure_congr hw' hwshift henv]
    exact diagonalPotentialMeasure_add_const theta hw (-A) hwshift
  -- transport the set back
  have hseteq : {y : M | rooftopEnvelope theta.val
        (fun x => min (phi x + ((-A : ℝ) : EReal)) (psi x + ((-A : ℝ) : EReal))) y <
        min (phi y + ((-A : ℝ) : EReal)) (psi y + ((-A : ℝ) : EReal))} =
      {x : M | rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x <
        min (phi x) (psi x)} := by
    ext y
    show rooftopEnvelope theta.val
        (fun x => min (phi x + ((-A : ℝ) : EReal)) (psi x + ((-A : ℝ) : EReal))) y <
        min (phi y + ((-A : ℝ) : EReal)) (psi y + ((-A : ℝ) : EReal)) ↔ _
    rw [congrFun henv y, congrFun hmin y]
    exact RooftopMinConcentration.add_coe_lt_add_coe_iff (-A)
  rw [← hmeaseq, ← hseteq]
  exact hzero

/-- **Xia SGPT Lemma 3.1.1, inequality (3.2), big class** (`RooftopContactConcentration`). -/
theorem rooftopEnvelope_min_le_of_isBigClass (hn : 0 < n)
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (hw : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))))
    (B : Set M) :
    diagonalPotentialMeasure theta
        (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))) hw B ≤
      diagonalPotentialMeasure theta phi hphi
          (B ∩ {x | rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x
            = phi x}) +
        diagonalPotentialMeasure theta psi hpsi
          (B ∩ {x | rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x
            = psi x}) := by
  classical
  set w := rooftopEnvelope theta.val (fun x => min (phi x) (psi x)) with hwdef
  obtain ⟨hwphi, hwpsi⟩ := RooftopContactConcentration.rooftopEnvelope_min_le_obstacles hphi.1 hpsi.1
  have hzero := rooftopEnvelope_min_noncontact_eq_zero_of_isBigClass hn theta hbig hphi hpsi hw
  have hsub : B ⊆ (B ∩ {x : M | w x = phi x}) ∪
      ((B ∩ {x : M | w x = psi x}) ∪ {x : M | w x ≠ phi x ∧ w x ≠ psi x}) := by
    intro x hx
    by_cases h1 : w x = phi x
    · exact Or.inl ⟨hx, h1⟩
    · by_cases h2 : w x = psi x
      · exact Or.inr (Or.inl ⟨hx, h2⟩)
      · exact Or.inr (Or.inr ⟨h1, h2⟩)
  calc diagonalPotentialMeasure theta w hw B
      ≤ diagonalPotentialMeasure theta w hw ((B ∩ {x : M | w x = phi x}) ∪
          ((B ∩ {x : M | w x = psi x}) ∪
            {x : M | w x ≠ phi x ∧ w x ≠ psi x})) := measure_mono hsub
    _ ≤ diagonalPotentialMeasure theta w hw (B ∩ {x : M | w x = phi x}) +
          diagonalPotentialMeasure theta w hw ((B ∩ {x : M | w x = psi x}) ∪
            {x : M | w x ≠ phi x ∧ w x ≠ psi x}) := measure_union_le _ _
    _ ≤ diagonalPotentialMeasure theta w hw (B ∩ {x : M | w x = phi x}) +
          (diagonalPotentialMeasure theta w hw (B ∩ {x : M | w x = psi x}) +
            diagonalPotentialMeasure theta w hw
              {x : M | w x ≠ phi x ∧ w x ≠ psi x}) :=
        add_le_add le_rfl (measure_union_le _ _)
    _ = diagonalPotentialMeasure theta w hw (B ∩ {x : M | w x = phi x}) +
          diagonalPotentialMeasure theta w hw (B ∩ {x : M | w x = psi x}) := by
        rw [hzero, add_zero]
    _ ≤ diagonalPotentialMeasure theta phi hphi (B ∩ {x : M | w x = phi x}) +
          diagonalPotentialMeasure theta psi hpsi (B ∩ {x : M | w x = psi x}) :=
        add_le_add
          (RooftopContactConcentration.measure_le_of_subset_contact omega theta hw hphi hwphi _
            fun x hx => hx.2)
          (RooftopContactConcentration.measure_le_of_subset_contact omega theta hw hpsi hwpsi _
            fun x hx => hx.2)

/-- **Xia Corollary 3.1.1 on open sets, big class** (`ShiftedRooftopContactProof`). -/
theorem shiftedRooftopLimit_isOpen_le_contact_of_isBigClass (hn : 0 < n)
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
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
    have key := rooftopEnvelope_min_le_of_isBigClass hn omega theta hbig hu hvj
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
    refine subset_trans ?_ (ShiftedRooftopContactProof.iInter_setOf_add_nat_le_subset_poles (v := v) hu.1)
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

/-- **Xia Corollary 3.1.1 on arbitrary sets, big class** (`ShiftedRooftopContactProof`). -/
theorem shiftedRooftopLimit_le_contact_of_seq_of_isBigClass (hn : 0 < n)
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
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
  exact shiftedRooftopLimit_isOpen_le_contact_of_isBigClass hn omega theta hbig
    hu hv c hcmono hcex hlim hw heta hGopen

/-- **Xia Corollary 3.1.1 with no family hypotheses, big class** (`ShiftedRooftopContactProof`). -/
theorem shiftedRooftopLimit_le_contact_of_potential_of_isBigClass
    [Nonempty M] (hn : 0 < n) (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u)
    (hv : IsThetaPshPotential theta.val v)
    (heta : IsThetaPshPotential theta.val (shiftedRooftopLimit theta u v))
    (B : Set M) :
    diagonalPotentialMeasure theta (shiftedRooftopLimit theta u v) heta B ≤
      diagonalPotentialMeasure theta u hu
        (B ∩ {x | shiftedRooftopLimit theta u v x = u x}) := by
  classical
  obtain ⟨j₀, hj₀⟩ := ShiftedRooftopContactProof.exists_isThetaPshPotential_shiftedRooftop_tail theta hu heta
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
  exact shiftedRooftopLimit_le_contact_of_seq_of_isBigClass hn omega theta hbig
    hu hv (fun j : ℕ => ((j₀ + j : ℕ) : ℝ))
    (fun a b h => Nat.mono_cast (Nat.add_le_add_left h j₀))
    (fun k => ⟨k, Nat.mono_cast (Nat.le_add_left k j₀)⟩)
    hlim (fun j => hj₀ (j₀ + j) (Nat.le_add_right j₀ j)) heta B

end

end SGPT.Foundations.Analysis.Pending.RooftopContactBigClass
