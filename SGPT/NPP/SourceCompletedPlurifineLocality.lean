import SGPT.Foundations.Analysis.Pending.BorelPlurifineOpenCountableNormalizedSuperlevelCover
import SGPT.NPP.NonPluripolarCurrent3Currents
import SGPT.NPP.NonPluripolarCurrent4BoundedManifold
import SGPT.NPP.NonPluripolarClosedManifold
import Mathlib.MeasureTheory.Measure.NullMeasurable

/-! Full remaining original prop:npp1/eq:ppp1 non-Borel clause.
Source69360cfd chapter_npp151–162. Original arbitrary fine-open F is
retained in every coefficient/test integral. Completion/nullness produced
internally, genuine original all-degree NPP current objects unchanged.
Uses accepted EVERY-original-chart coefficient equality interface; no new
global compatible PositiveCurrent multiplier packaging claimed.
Canonical private consolidation of EXACT checked proof bodies. -/

-- BEGIN CHECKED COMPONENT FineOpenCore
set_option autoImplicit false

/-!
# Actual arbitrary fine-open core, no Borel premise

The genuine ORIGINAL arbitrary plurifine-open set produces a countable
Borel core. The actual possibly NON-Borel remainder has zero OUTER literal
relative capacity on every ordinary smaller domain. Full blueprint preceded
code. Reuses the genuine proved normalized-cover argument: its ONLY Borel
use was to assert measurability of the remainder, unused by capacity proof.
-/

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.NPP.CompletedPlurifineDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor

variable {n : ℕ}

private theorem exists_increasing_sequence {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] {H : Set (X → ℝ)} (hne : H.Nonempty)
    (hmax : ∀ a ∈ H, ∀ b ∈ H, (fun x ↦ max (a x) (b x)) ∈ H) :
    ∃ g : ℕ → X → ℝ, (∀ k, g k ∈ H) ∧
      (∀ x, Monotone (fun k ↦ g k x)) ∧
      uscRegularization (fun x ↦ ⨆ k, (g k x : EReal)) =
        uscRegularization (sSup ((fun h : X → ℝ ↦ fun x ↦ (h x : EReal)) '' H)) := by
  classical
  obtain ⟨s, hs, hseq⟩ := exists_seq_uscRegularization_iSup_eq (hne.image
    (fun h : X → ℝ ↦ fun x ↦ (h x : EReal)))
  have hrep : ∀ k, ∃ a ∈ H, (fun x ↦ (a x : EReal)) = s k := hs
  choose a ha he using hrep
  let g : ℕ → X → ℝ := fun k x ↦ (runningMax s k x).toReal
  have hh : ∀ k, g k ∈ H ∧ (fun x ↦ (g k x : EReal)) = runningMax s k := by
    intro k
    induction k with
    | zero =>
      have h0 : g 0 = a 0 := by
        funext x
        simp only [g, runningMax, ← he 0, EReal.toReal_coe]
      constructor
      · rw [h0]
        exact ha 0
      · rw [h0]
        exact he 0
    | succ k ih =>
      have hm : (fun x ↦ ((max (g k x) (a (k + 1) x) : ℝ) : EReal)) =
          runningMax s (k + 1) := by
        funext x
        change ((max (g k x) (a (k + 1) x) : ℝ) : EReal) =
          max (runningMax s k x) (s (k + 1) x)
        rw [← congrFun ih.2 x, ← congrFun (he (k + 1)) x]
        exact EReal.coe_strictMono.monotone.map_max
      have hstep : g (k + 1) = fun x ↦ max (g k x) (a (k + 1) x) := by
        funext x
        dsimp only [g]
        rw [← congrFun hm x, EReal.toReal_coe]
      constructor
      · rw [hstep]
        exact hmax (g k) ih.1 (a (k + 1)) (ha (k + 1))
      · rw [hstep]
        exact hm
  refine ⟨g, fun k ↦ (hh k).1, ?_, ?_⟩
  · intro x k l hkl
    apply EReal.coe_le_coe_iff.mp
    rw [congrFun (hh k).2 x, congrFun (hh l).2 x]
    exact runningMax_monotone s hkl x
  · have hsup : (fun x ↦ ⨆ k, (g k x : EReal)) = ⨆ k, s k := by
      ext x
      rw [iSup_apply]
      calc
        (⨆ k, (g k x : EReal)) = ⨆ k, runningMax s k x :=
          iSup_congr fun k ↦ congrFun (hh k).2 x
        _ = _ := iSup_runningMax s x
    rw [hsup]
    exact hseq

/-- The ORIGINAL arbitrary fine-open set internally produces countably many
genuine normalized patches and an all-subdomain capacity-zero remainder. -/
theorem exists_countable_normalized_cover
    {Ω : Opens (ComplexModel n)} {F : Set (ComplexModel n)}
    (hFΩ : F ⊆ (Ω : Set (ComplexModel n)))
    (hFine : IsOpen[PlurifinePshTopology.topology Ω] (Subtype.val ⁻¹' F)) :
    ∃ (B : ℕ → Opens (ComplexModel n)) (g : ℕ → ℕ → ComplexModel n → ℝ),
      (∀ j, B j ≤ Ω) ∧
      (∀ j k, PlurisubharmonicOn (fun x ↦ (g j k x : EReal)) Ω) ∧
      (∀ j, ∀ x ∈ Ω, Monotone (fun k ↦ g j k x)) ∧
      (∀ j k x, x ∈ B j → -1 ≤ g j k x ∧ g j k x ≤ 1) ∧
      (∀ j k, {x | x ∈ B j ∧ 0 < g j k x} ⊆ F ∧
        MeasurableSet {x | x ∈ B j ∧ 0 < g j k x} ∧
        IsOpen[PlurifinePshTopology.topology Ω]
          (Subtype.val ⁻¹' {x | x ∈ B j ∧ 0 < g j k x})) ∧
      ∀ (D : Opens (ComplexModel n)), D ≤ Ω →
        relCapacity D ((F \ ⋃ j, ⋃ k, {x | x ∈ B j ∧ 0 < g j k x}) ∩
          (D : Set (ComplexModel n))) = 0 := by
  classical
  obtain ⟨b, hbasis⟩ := TopologicalSpace.exists_seq_basis Ω
  let B : ℕ → Opens (ComplexModel n) := fun j ↦
    ⟨Subtype.val '' b j,
      Ω.isOpen.isOpenMap_subtype_val _ (hbasis.isOpen (mem_range_self j))⟩
  have hBΩ (j : ℕ) : B j ≤ Ω := by
    rintro x ⟨y, hy, rfl⟩
    exact y.2
  let H : ℕ → Set (ComplexModel n → ℝ) := fun j ↦
    {h | PlurisubharmonicOn (fun x ↦ (h x : EReal)) Ω ∧
      (∀ x ∈ B j, -1 ≤ h x ∧ h x ≤ 1) ∧
      {x | x ∈ B j ∧ 0 < h x} ⊆ F}
  have hne (j : ℕ) : (H j).Nonempty := by
    refine ⟨fun _ ↦ -1, ?_, ?_, ?_⟩
    · exact fun x _ ↦ plurisubharmonicAt_const ((-1 : ℝ) : EReal)
        (EReal.coe_ne_top (-1)) x
    · intro x hx
      norm_num
    · rintro x ⟨hx, hp⟩
      norm_num at hp
  have hmax (j : ℕ) : ∀ a ∈ H j, ∀ c ∈ H j,
      (fun x ↦ max (a x) (c x)) ∈ H j := by
    rintro a ⟨hpa, hba, hFa⟩ c ⟨hpc, hbc, hFc⟩
    refine ⟨?_, ?_, ?_⟩
    · convert hpa.max hpc using 1
      funext x
      exact EReal.coe_strictMono.monotone.map_max
    · intro x hx
      exact ⟨(hba x hx).1.trans (le_max_left _ _),
        max_le (hba x hx).2 (hbc x hx).2⟩
    · rintro x ⟨hx, hp⟩
      rcases lt_max_iff.mp hp with ha | hc
      · exact hFa ⟨hx, ha⟩
      · exact hFc ⟨hx, hc⟩
  have hpoint : ∀ x ∈ F, ∃ j, x ∈ B j ∧ ∃ h ∈ H j, h x = 1 / 2 := by
    intro x hx
    obtain ⟨O, h, hO, hxO, hpsh, hvalue, hlo, hup, _hfo, hsub⟩ :=
      PlurifineSingleSuperlevelNeighborhoods.exists_bounded_single_superlevel
        hFine (show (⟨x, hFΩ hx⟩ : Ω) ∈ Subtype.val ⁻¹' F from hx)
    obtain ⟨v, ⟨j, rfl⟩, hxv, hvO⟩ := hbasis.exists_subset_of_mem_open hxO hO
    refine ⟨j, ⟨⟨x, hFΩ hx⟩, hxv, rfl⟩, h, ?_, hvalue⟩
    refine ⟨hpsh, ?_, ?_⟩
    · rintro z ⟨w, hw, rfl⟩
      exact ⟨hlo w.val w.2, hup w (hvO hw)⟩
    · rintro z ⟨⟨w, hw, rfl⟩, hp⟩
      exact hsub ⟨hvO hw, hp⟩
  have hseq : ∀ j, ∃ g : ℕ → ComplexModel n → ℝ,
      (∀ k, g k ∈ H j) ∧ (∀ x, Monotone (fun k ↦ g k x)) ∧
      uscRegularization (fun x ↦ ⨆ k, (g k x : EReal)) =
        uscRegularization (sSup ((fun h : ComplexModel n → ℝ ↦
          fun x ↦ (h x : EReal)) '' H j)) :=
    fun j ↦ exists_increasing_sequence (hne j) (hmax j)
  choose g hgmem hgmono hgeq using hseq
  let p : ℕ → ComplexModel n → EReal := fun j x ↦ ⨆ k, (g j k x : EReal)
  let Q : ℕ → ComplexModel n → EReal := fun j ↦ uscRegularization (p j)
  let G : ℕ → ℕ → Set (ComplexModel n) := fun j k ↦ {x | x ∈ B j ∧ 0 < g j k x}
  let E : Set (ComplexModel n) := F \ ⋃ j, ⋃ k, G j k
  let N : ℕ → Set (ComplexModel n) := fun j ↦ {x | x ∈ B j ∧ p j x < Q j x}
  have hgap (j : ℕ) (D : Opens (ComplexModel n)) (hDB : D ≤ B j) :
      relCapacity D {x | x ∈ D ∧ p j x < Q j x} = 0 :=
    (RegularizedIncreasingPshGapCapacityZero.regularized_isIncApprox_and_relCapacity_gap_eq_zero
      (hBΩ j) (g j) (fun k ↦ (hgmem j k).1) (fun x _ ↦ hgmono j x)
      (fun k ↦ (hgmem j k).2.1)).2.2.2 D hDB
  have hG (j k : ℕ) : G j k ⊆ F ∧ MeasurableSet (G j k) ∧
      IsOpen[PlurifinePshTopology.topology Ω] (Subtype.val ⁻¹' G j k) := by
    refine ⟨(hgmem j k).2.2, ?_, ?_⟩
    · simpa only [G, ← EReal.coe_zero, EReal.coe_lt_coe_iff] using
        PlurifineStrictSuperlevelCover.measurableSet_psh_superlevel
          ((hgmem j k).1.mono (hBΩ j)) 0
    · let : TopologicalSpace Ω := PlurifinePshTopology.topology Ω
      change IsOpen[PlurifinePshTopology.topology Ω]
        ((Subtype.val ⁻¹' (B j : Set (ComplexModel n))) ∩
          {z : Ω | 0 < g j k z.val})
      exact (PlurifineEuclideanComparison.isOpen_euclidean (B j).isOpen).inter
        (PlurifinePshTopology.isOpen_realPsh_superlevel (hgmem j k).1 0)
  have hEN : E ⊆ ⋃ j, N j := by
    rintro x ⟨hxF, hxP⟩
    obtain ⟨j, hxB, h, hh, hvalue⟩ := hpoint x hxF
    have hgzero : ∀ k, g j k x ≤ 0 := by
      intro k
      apply le_of_not_gt
      intro hp
      exact hxP (mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨k, ⟨hxB, hp⟩⟩⟩)
    have hpzero : p j x ≤ (0 : EReal) :=
      iSup_le fun k ↦ EReal.coe_le_coe_iff.mpr (hgzero k)
    have hhQ : (h x : EReal) ≤ Q j x := by
      calc
        (h x : EReal) ≤ sSup ((fun h : ComplexModel n → ℝ ↦
            fun x ↦ (h x : EReal)) '' H j) x :=
          le_sSup (show (fun x ↦ (h x : EReal)) ∈
            (fun h : ComplexModel n → ℝ ↦ fun x ↦ (h x : EReal)) '' H j from
              ⟨h, hh, rfl⟩) x
        _ ≤ uscRegularization (sSup ((fun h : ComplexModel n → ℝ ↦
            fun x ↦ (h x : EReal)) '' H j)) x := le_uscRegularization _ x
        _ = Q j x := (congrFun (hgeq j) x).symm
    have hpos : (0 : EReal) < (h x : EReal) := by
      rw [hvalue]
      exact EReal.coe_lt_coe_iff.mpr (by norm_num : (0 : ℝ) < 1 / 2)
    exact mem_iUnion.mpr ⟨j, hxB, hpzero.trans_lt (hpos.trans_le hhQ)⟩
  refine ⟨B, g, hBΩ, fun j k ↦ (hgmem j k).1, fun j x _ ↦ hgmono j x,
    fun j k ↦ (hgmem j k).2.1, hG, ?_⟩
  intro D _hDΩ
  refine le_antisymm (relCapacity_le_of_forall ?_) bot_le
  intro w hw hb
  let μ := Pending.MongeAmpere.canonicalBedfordTaylorMeasure D w hw
  have hμ : IsBTLimit D (fun _ ↦ w) μ := isBTLimit_canonicalBedfordTaylorMeasure hw
  have hz (j : ℕ) : μ (N j ∩ (D : Set (ComplexModel n))) = 0 := by
    have hset : N j ∩ (D : Set (ComplexModel n)) =
        {x | x ∈ B j ⊓ D ∧ p j x < Q j x} := by
      ext x
      change ((x ∈ B j ∧ p j x < Q j x) ∧ x ∈ D) ↔
        ((x ∈ B j ∧ x ∈ D) ∧ p j x < Q j x)
      tauto
    have hc : relCapacity (B j ⊓ D) (N j ∩ (D : Set (ComplexModel n))) = 0 := by
      rw [hset]
      exact hgap j (B j ⊓ D) inf_le_left
    have hbound : ∀ i : Fin n, ∀ x ∈ B j ⊓ D, |w x| ≤ (1 : ℝ) := by
      intro i x hx
      exact abs_le.mpr ⟨(hb x hx.2).1, (hb x hx.2).2.trans (by norm_num)⟩
    have hNU : N j ∩ (D : Set (ComplexModel n)) ⊆
        (B j ⊓ D : Opens (ComplexModel n)) := fun x hx ↦ ⟨hx.1.1, hx.2⟩
    refine le_antisymm ((hμ.le_relCapacity_of_abs_le (fun _ ↦ hw) inf_le_right
      (by norm_num : (0 : ℝ) < 1) hbound hNU).trans ?_) bot_le
    rw [hc, mul_zero]
  have hunion : μ (⋃ j, N j ∩ (D : Set (ComplexModel n))) = 0 := measure_iUnion_null hz
  have hsub : E ∩ (D : Set (ComplexModel n)) ⊆
      ⋃ j, N j ∩ (D : Set (ComplexModel n)) := by
    rintro x ⟨hxE, hxD⟩
    obtain ⟨j, hxj⟩ := mem_iUnion.mp (hEN hxE)
    exact mem_iUnion.mpr ⟨j, hxj, hxD⟩
  exact (measure_mono hsub).trans hunion.le

/-- The actual ORIGINAL fine-open set has a single Borel fine-open core
with zero OUTER-capacity remainder on EVERY original smaller domain. -/
theorem exists_borel_fine_core
    {Ω : Opens (ComplexModel n)} {F : Set (ComplexModel n)}
    (hFΩ : F ⊆ (Ω : Set (ComplexModel n)))
    (hFine : IsOpen[PlurifinePshTopology.topology Ω] (Subtype.val ⁻¹' F)) :
    ∃ G : Set (ComplexModel n), G ⊆ F ∧ MeasurableSet G ∧
      IsOpen[PlurifinePshTopology.topology Ω] (Subtype.val ⁻¹' G) ∧
      ∀ (D : Opens (ComplexModel n)), D ≤ Ω →
        relCapacity D ((F \ G) ∩ (D : Set (ComplexModel n))) = 0 := by
  obtain ⟨B,g,hB,hg,hmono,hbounds,hG,hcap⟩ :=
    exists_countable_normalized_cover hFΩ hFine
  refine ⟨⋃ j, ⋃ k, {x | x ∈ B j ∧ 0 < g j k x}, ?_, ?_, ?_, hcap⟩
  · exact iUnion_subset fun j => iUnion_subset fun k => (hG j k).1
  · exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun k => (hG j k).2.1
  · let : TopologicalSpace Ω := PlurifinePshTopology.topology Ω
    simp only [preimage_iUnion]
    exact isOpen_iUnion fun j => isOpen_iUnion fun k => (hG j k).2.2

end SGPT.NPP.CompletedPlurifineDraft
end -- anonymous noncomputable section
-- END CHECKED COMPONENT FineOpenCore

-- BEGIN CHECKED COMPONENT FineCoreTrace
/-! Actual all-degree NPP trace gives zero OUTER mass to the internally
produced arbitrary fine-open remainder. No Borel/nullness certificate. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
namespace SGPT.NPP.CompletedPlurifineDraft
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.NPP.NonPluripolarCurrent
variable {n : ℕ}

theorem mixedMeasure_eq_zero_of_all_subdomain_capacity
    {Ω : Opens (ComplexModel n)} {E : Set (ComplexModel n)}
    (hEΩ : E ⊆ (Ω : Set (ComplexModel n)))
    (hcap : ∀ D : Opens (ComplexModel n), D ≤ Ω →
      relCapacity D (E ∩ (D : Set (ComplexModel n))) = 0)
    {u : Fin n → ComplexModel n → ℝ} (hu : IsLocallyBoundedMixedPshOn Ω u)
    {μ : Measure (ComplexModel n)} (hμspec : IsLocalMixedBedfordTaylorMeasure Ω u μ) :
    μ E = 0 := by
  classical
  have hμ : IsBTLimit Ω u μ := IsLocalMixedBedfordTaylorMeasure.isBTLimit hμspec
  obtain ⟨U, -, hUrc, hUabs⟩ := exists_exhaustion Ω
  have hUΩ (m : ℕ) : U m ≤ Ω := subset_closure.trans (hUrc m).2
  have hnull (m : ℕ) : μ (E ∩ (U m : Set (ComplexModel n))) = 0 := by
    choose C hC using fun i : Fin n ↦
      BedfordTaylor.IsLocallyBoundedPshOn.exists_abs_le (hu i) (hUrc m).1 (hUrc m).2
    let M : ℝ := 1 + ∑ i : Fin n, |C i|
    have hsum : 0 ≤ ∑ i : Fin n, |C i| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    have hM : 0 < M := by dsimp only [M]; linarith
    have hbound (i : Fin n) (z : ComplexModel n) (hz : z ∈ U m) : |u i z| ≤ M := by
      have hi : |C i| ≤ ∑ j : Fin n, |C j| :=
        Finset.single_le_sum (f := fun j : Fin n ↦ |C j|)
          (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ i)
      calc
        |u i z| ≤ C i := hC i z (subset_closure hz)
        _ ≤ |C i| := le_abs_self _
        _ ≤ ∑ j : Fin n, |C j| := hi
        _ ≤ M := by dsimp only [M]; linarith
    have hle := hμ.le_relCapacity_of_abs_le hu (hUΩ m) hM hbound
      (E := E ∩ (U m : Set (ComplexModel n))) inter_subset_right
    rw [hcap (U m) (hUΩ m), mul_zero] at hle
    exact le_antisymm hle bot_le
  have hcover : E ⊆ ⋃ m, E ∩ (U m : Set (ComplexModel n)) := by
    intro x hx
    obtain ⟨m, hm⟩ := hUabs {x} isCompact_singleton
      (singleton_subset_iff.mpr (hEΩ hx))
    exact mem_iUnion.mpr ⟨m, hx, hm (mem_singleton x)⟩
  have hzero : μ (⋃ m, E ∩ (U m : Set (ComplexModel n))) = 0 :=
    measure_iUnion_null hnull
  exact le_antisymm ((measure_mono hcover).trans_eq hzero) bot_le

/-- EVERY original arbitrary-degree locally bounded BT current has
zero true trace OUTER mass on the actual capacity-null remainder. -/
theorem bt_trace_eq_zero_of_all_subdomain_capacity
    {p q : ℕ} (hqp : q+p=n) {Ω : Opens (ComplexModel n)}
    {E : Set (ComplexModel n)} (hEΩ : E ⊆ (Ω : Set (ComplexModel n)))
    (hcap : ∀ D : Opens (ComplexModel n), D ≤ Ω →
      relCapacity D (E ∩ (D : Set (ComplexModel n))) = 0)
    {u : Fin p → ComplexModel n → ℝ} (hu : ∀ i, IsLocallyBoundedPshOn Ω (u i)) :
    (isPositive_btProduct p q u (oneCurrentOf (U := Ω) hqp)
      (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) hu).1.traceMeasure E = 0 := by
  subst hqp
  rw [traceMeasure_btProduct_eq hu]
  let huTop : IsLocallyBoundedMixedPshOn Ω
      (Fin.append (fun _ : Fin q => BedfordTaylorTopDegree.quadPot (kahlerForm (q+p))) u) :=
    BedfordTaylorTopDegree.isLocallyBoundedPshOn_append
      (fun _ => BedfordTaylorTopDegree.isLocallyBoundedPshOn_quadPot
        isSemipositiveOneOne_kahlerForm Ω) hu
  exact mixedMeasure_eq_zero_of_all_subdomain_capacity hEΩ hcap huTop
    (LocalBedfordTaylorCanonicalTraceMeasure.isLocalMixedBedfordTaylorMeasure_recursiveMixedTraceMeasure huTop)

/-- EVERY original well-defined NPP current gives zero OUTER trace mass
to the same actual capacity-null remainder, in EVERY original degree. -/
theorem npp_trace_eq_zero_of_all_subdomain_capacity
    {p q : ℕ} (hqp : q+p=n) {Ω : Opens (ComplexModel n)}
    {E : Set (ComplexModel n)} (hEΩ : E ⊆ (Ω : Set (ComplexModel n)))
    (hcap : ∀ D : Opens (ComplexModel n), D ≤ Ω →
      relCapacity D (E ∩ (D : Set (ComplexModel n))) = 0)
    {φ : Fin p → ComplexModel n → EReal} (hφ : ∀ i, PlurisubharmonicOn (φ i) Ω)
    (hW : IsWellDefinedOn hqp Ω φ) :
    (isPositive_nonPluripolarProduct hqp hφ hW).traceMeasure E = 0 := by
  let hF := isTruncationFamily hqp hφ
  have hm := (isWellDefinedOn_iff hqp hφ).mp hW
  have e : (isPositive_nonPluripolarProduct hqp hφ hW).traceMeasure =
      (hF.isPositive_glue hm).traceMeasure :=
    traceMeasure_congr _ _ (nonPluripolarProduct_eq hqp hφ)
  rw [e,hF.traceMeasure_glue hm]
  exact hF.glueMeasure_eq_zero fun k =>
    bt_trace_eq_zero_of_all_subdomain_capacity hqp hEΩ hcap
      (fun i => truncationReal_isLocallyBoundedPshOn (hφ i) k)

end SGPT.NPP.CompletedPlurifineDraft
end -- anonymous noncomputable section
-- END CHECKED COMPONENT FineCoreTrace

-- BEGIN CHECKED COMPONENT CompletedCurrentRestriction
/-! Actual completed coefficient restriction, using genuine trace densities
and the actual Borel measurable hull. Exact test formula retains the
ORIGINAL potentially non-Borel set. No output equality certificate. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal
namespace SGPT.NPP.CompletedPlurifineDraft
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.NPP.NonPluripolarCurrent
open SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan
variable {n q : ℕ} {U : Opens (ComplexModel n)}

/-- Actual completed restriction of ALL coefficient measures of the
ORIGINAL positive current. It is used with completion measurability, which
is proved internally for the original source fine-open sets below. -/
def completedRestriction (T : LocalProductCurrent n U q) (hT : IsPositive T)
    (F : Set (ComplexModel n)) : LocalProductCurrent n U q :=
  mulBorel T ((toMeasurable hT.traceMeasure F).indicator fun _ => (1 : ℝ))

/-- Exact coefficient/test formula on the ORIGINAL possibly NON-Borel set;
all coefficient measures are actually restricted in their completion. -/
theorem completedRestriction_apply {T : LocalProductCurrent n U q} (hT : IsPositive T)
    {F : Set (ComplexModel n)} (hF : NullMeasurableSet F hT.traceMeasure)
    (γ : formSpan n q) (η : 𝓓(U,ℝ)) :
    completedRestriction T hT F γ η =
      ∫ x, η x*((F.indicator fun _ => (1 : ℝ)) x*hT.density γ x) ∂hT.traceMeasure := by
  rw [completedRestriction,mulBorel_apply hT
    (measurable_const.indicator (measurableSet_toMeasurable _ _))
    (isLocallyBoundedOn_indicator_one _)]
  apply integral_congr_ae
  filter_upwards [indicator_ae_eq_of_ae_eq_set (f := fun _ => (1 : ℝ)) hF.toMeasurable_ae_eq] with x hx
  rw [hx]

/-- Independence of the actual hull: completed restriction agrees with
ANY genuine Borel core equal to the ORIGINAL set trace-almost everywhere. -/
theorem completedRestriction_eq_mulBorel_of_ae
    {T : LocalProductCurrent n U q} (hT : IsPositive T)
    {F G : Set (ComplexModel n)} (hG : MeasurableSet G)
    (hFG : F =ᵐ[hT.traceMeasure] G) :
    completedRestriction T hT F = mulBorel T (G.indicator fun _ => (1 : ℝ)) := by
  have hF : NullMeasurableSet F hT.traceMeasure := hG.nullMeasurableSet.congr hFG.symm
  ext γ η
  rw [completedRestriction_apply hT hF,mulBorel_apply hT
    (measurable_const.indicator hG) (isLocallyBoundedOn_indicator_one _)]
  apply integral_congr_ae
  filter_upwards [indicator_ae_eq_of_ae_eq_set (f := fun _ => (1 : ℝ)) hFG] with x hx
  rw [hx]

/-- On original Borel sets this is EXACTLY the unchanged native restriction. -/
theorem completedRestriction_eq_mulBorel
    {T : LocalProductCurrent n U q} (hT : IsPositive T)
    {F : Set (ComplexModel n)} (hF : MeasurableSet F) :
    completedRestriction T hT F = mulBorel T (F.indicator fun _ => (1 : ℝ)) :=
  completedRestriction_eq_mulBorel_of_ae hT hF Filter.EventuallyEq.rfl

/-- A produced Borel core with actual zero OUTER remainder retains the
original set almost everywhere, without a source Borel premise. -/
theorem ae_eq_borel_core_of_null_difference
    {μ : Measure (ComplexModel n)} {F G : Set (ComplexModel n)}
    (hGF : G ⊆ F) (hnull : μ (F \ G)=0) : F =ᵐ[μ] G := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx
  exact propext ⟨fun hf => by_contra fun hg => hx ⟨hf,hg⟩,fun hg => hGF hg⟩

end SGPT.NPP.CompletedPlurifineDraft
end -- anonymous noncomputable section
-- END CHECKED COMPONENT CompletedCurrentRestriction

-- BEGIN CHECKED COMPONENT NonBorelLocality
/-! Full remaining original prop:npp1 clause: arbitrary ORIGINAL
plurifine-open sets, with actual completed restriction of ALL original
current coefficients. No Borel/nullness/completion certificate premise. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal Manifold
namespace SGPT.NPP.CompletedPlurifineDraft
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.NPP.NonPluripolarCurrent

/-- Original eq:ppp1 in a chart, with NO Borel hypothesis on the ORIGINAL
fine-open set. Both completion measurabilities and the equality of ALL
completed coefficient restrictions are genuinely produced internally. -/
theorem nonBorel_npp_locality
    {n p q : ℕ} (hqp : q+p=n) {U : Opens (ComplexModel n)}
    {φ ψ : Fin p → ComplexModel n → EReal}
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U) (hψ : ∀ i, PlurisubharmonicOn (ψ i) U)
    (hWφ : IsWellDefinedOn hqp U φ) (hWψ : IsWellDefinedOn hqp U ψ)
    {F : Set (ComplexModel n)} (hFU : F ⊆ (U : Set (ComplexModel n)))
    (hFine : IsOpen[SGPT.PSH.domainPlurifineTopology U] (Subtype.val ⁻¹' F))
    (heq : ∀ i, EqOn (φ i) (ψ i) F) :
    NullMeasurableSet F (isPositive_nonPluripolarProduct hqp hφ hWφ).traceMeasure ∧
    NullMeasurableSet F (isPositive_nonPluripolarProduct hqp hψ hWψ).traceMeasure ∧
    completedRestriction (NonPluripolarCurrent.nonPluripolarProduct hqp U φ) (isPositive_nonPluripolarProduct hqp hφ hWφ) F =
      completedRestriction (NonPluripolarCurrent.nonPluripolarProduct hqp U ψ) (isPositive_nonPluripolarProduct hqp hψ hWψ) F := by
  obtain ⟨G,hGF,hGm,hGfine,hcap⟩ := exists_borel_fine_core hFU hFine
  have hnullφ := npp_trace_eq_zero_of_all_subdomain_capacity hqp (sdiff_subset.trans hFU) hcap hφ hWφ
  have hnullψ := npp_trace_eq_zero_of_all_subdomain_capacity hqp (sdiff_subset.trans hFU) hcap hψ hWψ
  have hFGφ := ae_eq_borel_core_of_null_difference hGF hnullφ
  have hFGψ := ae_eq_borel_core_of_null_difference hGF hnullψ
  refine ⟨hGm.nullMeasurableSet.congr hFGφ.symm,hGm.nullMeasurableSet.congr hFGψ.symm,?_⟩
  rw [completedRestriction_eq_mulBorel_of_ae _ hGm hFGφ,
    completedRestriction_eq_mulBorel_of_ae _ hGm hFGψ]
  exact mulBorel_nonPluripolarProduct_eq_of_eqOn_plurifineOpen hqp hφ hψ hWφ hWψ
    (hGF.trans hFU) hGm hGfine (fun i => (heq i).mono hGF)

/-- Full original manifold eq:ppp1, in EVERY original chart, for an
arbitrary original plurifine-open set. The actual original NPP current
objects/coefficient restrictions are retained, with no Borel premise. -/
theorem sourceNonBorelNppLocality
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {p q : ℕ} (hqp : q+p=n) {φ ψ : Fin p → M → EReal}
    (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i))
    (hψ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (ψ i))
    (hWφ : IsNonPluripolarWellDefined hqp φ) (hWψ : IsNonPluripolarWellDefined hqp ψ)
    {F : Set M}
    (hFine : IsOpen[(SGPT.PSH.VariableComplexAtlas.ofFixedModel n M).plurifineTopology] F)
    (heq : ∀ i, EqOn (φ i) (ψ i) F) (e : ComplexChart n M) :
    completedRestriction ((SGPT.NPP.nonPluripolarProduct hqp φ hφ hWφ).inChart e)
      ((SGPT.NPP.nonPluripolarProduct hqp φ hφ hWφ).isPositive e)
      (e.val.target ∩ e.val.symm ⁻¹' F) =
    completedRestriction ((SGPT.NPP.nonPluripolarProduct hqp ψ hψ hWψ).inChart e)
      ((SGPT.NPP.nonPluripolarProduct hqp ψ hψ hWψ).isPositive e)
      (e.val.target ∩ e.val.symm ⁻¹' F) := by
  have hfine := (SGPT.PSH.VariableComplexAtlas.isOpen_plurifine_iff _ F).mp hFine e
  have hset : (Subtype.val ⁻¹' (e.val.target ∩ e.val.symm ⁻¹' F) : Set (chartTarget e)) =
      (SGPT.PSH.VariableComplexAtlas.ofFixedModel n M).chartInverse e ⁻¹' F := by
    ext z
    exact ⟨fun h => h.2,fun h => ⟨z.2,h⟩⟩
  have hlocalFine : IsOpen[SGPT.PSH.domainPlurifineTopology (chartTarget e)]
      (Subtype.val ⁻¹' (e.val.target ∩ e.val.symm ⁻¹' F)) := by
    rw [hset]
    exact hfine
  exact (nonBorel_npp_locality hqp (chartPlurisubharmonicOn hφ e) (chartPlurisubharmonicOn hψ e)
    (hWφ e) (hWψ e) inter_subset_left hlocalFine (fun i z hz => heq i hz.2)).2.2

end SGPT.NPP.CompletedPlurifineDraft
end -- anonymous noncomputable section
-- END CHECKED COMPONENT NonBorelLocality

-- BEGIN CHECKED COMPONENT NonBorelReadback
/-! Exact original-set coefficient/test readback from ONLY original source
inputs. Completion measurability is produced internally, not a premise. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal Manifold
namespace SGPT.NPP.CompletedPlurifineDraft
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

/-- Source-facing actual restriction/test formula over the ORIGINAL
possibly NON-Borel F, with NO supplied completion/nullness certificate. -/
theorem sourceNonBorelNppRestriction_apply
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {p q : ℕ} (hqp : q+p=n) {φ : Fin p → M → EReal}
    (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i))
    (hW : IsNonPluripolarWellDefined hqp φ) {F : Set M}
    (hFine : IsOpen[(SGPT.PSH.VariableComplexAtlas.ofFixedModel n M).plurifineTopology] F)
    (e : ComplexChart n M) (γ : formSpan n q) (η : 𝓓(chartTarget e,ℝ)) :
    completedRestriction ((SGPT.NPP.nonPluripolarProduct hqp φ hφ hW).inChart e)
      ((SGPT.NPP.nonPluripolarProduct hqp φ hφ hW).isPositive e)
      (e.val.target ∩ e.val.symm ⁻¹' F) γ η =
    ∫ z, η z*(((e.val.target ∩ e.val.symm ⁻¹' F).indicator fun _ => (1 : ℝ)) z*
      ((SGPT.NPP.nonPluripolarProduct hqp φ hφ hW).isPositive e).density γ z)
      ∂((SGPT.NPP.nonPluripolarProduct hqp φ hφ hW).isPositive e).traceMeasure := by
  have hfine := (SGPT.PSH.VariableComplexAtlas.isOpen_plurifine_iff _ F).mp hFine e
  have hset : (Subtype.val ⁻¹' (e.val.target ∩ e.val.symm ⁻¹' F) : Set (chartTarget e)) =
      (SGPT.PSH.VariableComplexAtlas.ofFixedModel n M).chartInverse e ⁻¹' F := by
    ext z
    exact ⟨fun h => h.2,fun h => ⟨z.2,h⟩⟩
  have hlocalFine : IsOpen[SGPT.PSH.domainPlurifineTopology (chartTarget e)]
      (Subtype.val ⁻¹' (e.val.target ∩ e.val.symm ⁻¹' F)) := by
    rw [hset]
    exact hfine
  have hnull := (nonBorel_npp_locality hqp (chartPlurisubharmonicOn hφ e)
    (chartPlurisubharmonicOn hφ e) (hW e) (hW e) inter_subset_left hlocalFine
    (fun i z _ => rfl)).1
  exact completedRestriction_apply _ hnull γ η

end SGPT.NPP.CompletedPlurifineDraft
end -- anonymous noncomputable section
-- END CHECKED COMPONENT NonBorelReadback
