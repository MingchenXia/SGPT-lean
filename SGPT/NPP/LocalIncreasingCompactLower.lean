import SGPT.NPP.LocalIncreasingTestMeasureNull
import SGPT.NPP.LocalIncreasingRegularization
import SGPT.NPP.CompactLowerGapTopological
import SGPT.Foundations.Analysis.Pending.ClosedNullOuterCapacity

/-!
The true finite-stage compact lower gap for original increasing local PSH
sequences. This implements nodes fixed-gap-cover and sequence-lower of
compact-lower-gap.tex. Original functions, local backgrounds and chartwise
Lebesgue convergence are the inputs; the compact null set and its small
open cover are produced internally.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.LocalIncreasingCapacityDraft

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open ThetaCapacity
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- One actual open exceptional set simultaneously regularizes a countable
family of original local quasi-PSH functions, at an arbitrary capacity budget. -/
theorem exists_simultaneous_local_quasicontinuity
    (ω : KahlerBackground n M) (U : Opens M) (f : ℕ → M → EReal)
    (hf : ∀ j, IsLocalQuasiPshOn (n := n) (U : Set M) (f j))
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ G : Set M, IsOpen G ∧ thetaCapacity ω.form (fun _ => 0) G < η ∧
      (∀ j x, x ∈ (U : Set M) \ G → f j x ≠ ⊥) ∧
      ∀ j, ContinuousOn (fun x => (f j x).toReal) ((U : Set M) \ G) := by
  classical
  obtain ⟨ε', hε'pos, hsum⟩ := ENNReal.exists_pos_sum_of_countable hη.ne' ℕ
  choose G hGo hGc hGf hGcont using fun j : ℕ =>
    exists_isOpen_kahlerCapacity_lt_on_open ω U.isOpen (hf j)
      (η := (ε' j : ℝ≥0∞)) (by exact_mod_cast hε'pos j)
  refine ⟨⋃ j, G j, isOpen_iUnion hGo, ?_, ?_, ?_⟩
  · calc thetaCapacity ω.form (fun _ => 0) (⋃ j, G j)
        ≤ ∑' j, thetaCapacity ω.form (fun _ => 0) (G j) := thetaCapacity_iUnion_le _ _ _
      _ ≤ ∑' j, (ε' j : ℝ≥0∞) := ENNReal.tsum_le_tsum fun j => by
          exact (hGc j).le
      _ < η := hsum
  · intro j x hx
    exact hGf j x ⟨hx.1, fun h => hx.2 (mem_iUnion.mpr ⟨j, h⟩)⟩
  · intro j
    exact (hGcont j).mono fun x hx =>
      ⟨hx.1, fun h => hx.2 (mem_iUnion.mpr ⟨j, h⟩)⟩

/-- Positive-dimensional compact lower-gap convergence, with the original
local PSH functions and their actual chartwise almost-everywhere limit. -/
theorem tendsto_kahlerCapacity_compact_lowerGap_of_monotone_sequence_pos
    (hn : 0 < n) (ω : KahlerBackground n M)
    (α : AtlasClosedRealOneOneForm (ofFixedModel n M)) (U : Opens M)
    {u : ℕ → M → EReal} {v : M → EReal}
    (hu : ∀ j, (ofFixedModel n M).IsThetaPSHOn α (u j) U)
    (hv : (ofFixedModel n M).IsThetaPSHOn α v U)
    (hm : ∀ x ∈ (U : Set M), Monotone fun j => u j x)
    (hae : NetChartTendstoAEOn (n := n) U u v)
    {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun j => thetaCapacity ω.form (fun _ => 0)
      (K ∩ sourceCapacityLowerGap U (fun x => u j x.1) (fun x => v x.1) δ))
      atTop (𝓝 0) := by
  classical
  let a : ℕ → M → EReal | 0 => v | j + 1 => u j
  have hav : IsLocalQuasiPshOn (n := n) (U : Set M) v :=
    isLocalQuasiPshOn_of_isThetaPSHOn U.isOpen hv
  have hau : ∀ j, IsLocalQuasiPshOn (n := n) (U : Set M) (u j) :=
    fun j => isLocalQuasiPshOn_of_isThetaPSHOn U.isOpen (hu j)
  have ha : ∀ j, IsLocalQuasiPshOn (n := n) (U : Set M) (a j) := by
    intro j; cases j with | zero => exact hav | succ j => exact hau j
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε2 : (0 : ℝ≥0∞) < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨G, hGo, hGc, hGf, hGcont⟩ :=
    exists_simultaneous_local_quasicontinuity ω U a ha hε2
  let L : Set M := K ∩ Gᶜ
  have hL : IsCompact L := hK.inter_right hGo.isClosed_compl
  have hLU : L ⊆ (U : Set M) \ G := fun x hx => ⟨hKU hx.1, hx.2⟩
  have hvcont : ContinuousOn (fun x => (v x).toReal) L := (hGcont 0).mono hLU
  have hucont : ∀ j, ContinuousOn (fun x => (u j x).toReal) L :=
    fun j => (hGcont (j + 1)).mono hLU
  have hufin : ∀ j x, x ∈ L → ((u j x).toReal : EReal) = u j x :=
    fun j x hx => EReal.coe_toReal ((hau j).ne_top (hKU hx.1)) (hGf (j + 1) x (hLU hx))
  have hvfin : ∀ x ∈ L, ((v x).toReal : EReal) = v x :=
    fun x hx => EReal.coe_toReal (hav.ne_top (hKU hx.1)) (hGf 0 x (hLU hx))
  let C : Set M := {x | x ∈ L ∧ ∀ j, (u j x).toReal + δ / 2 ≤ (v x).toReal}
  have hC : IsCompact C := isCompact_fixed_persistent_gap hL hucont hvcont (δ / 2)
  have hCU : C ⊆ U := fun x hx => hKU hx.1.1
  have hCgap : ∀ x ∈ C, (⨆ j, u j x) < v x := by
    intro x hx
    have hb : (⨆ j, u j x) ≤ (((v x).toReal - δ / 2 : ℝ) : EReal) := by
      apply iSup_le
      intro j
      rw [← hufin j x hx.1, EReal.coe_le_coe_iff]
      linarith [hx.2 j]
    refine hb.trans_lt ?_
    have hr : (v x).toReal - δ / 2 < (v x).toReal := by linarith
    exact (EReal.coe_lt_coe_iff.mpr hr).trans_eq (hvfin x hx.1)
  have hCouter := ClosedNullOuterCapacity.outerCapacityZero_of_isClosed hn ω hC.isClosed
    (fun w hw hwb => bounded_test_measure_compact_deficit_eq_zero ω α U hu hv hm hae
      hw hwb hC hCU hCgap)
  obtain ⟨H, hHo, hCH, hHc⟩ := hCouter (ε / 2) hε2
  have hmreal : ∀ x ∈ L, Monotone fun j => (u j x).toReal := by
    intro x hx i j hij
    apply EReal.coe_le_coe_iff.mp
    rw [hufin i x hx, hufin j x hx]
    exact hm x (hKU hx.1) hij
  obtain ⟨N, hN⟩ := exists_eventually_lowerGap_subset_of_fixed_persistent_cover
    hL hHo hucont hvcont hmreal hδ (fun x hx hp => hCH ⟨hx, hp⟩)
  filter_upwards [eventually_ge_atTop N] with j hj
  have hsub : K ∩ sourceCapacityLowerGap U (fun x => u j x.1) (fun x => v x.1) δ ⊆ G ∪ H := by
    rintro x ⟨hxK, ⟨y, hy, rfl⟩⟩
    by_cases hyG : y.1 ∈ G
    · exact Or.inl hyG
    · refine Or.inr (hN j hj y.1 ⟨hxK, hyG⟩ ?_)
      have hgap : u j y.1 < v y.1 - (δ : EReal) := hy
      rw [← hufin j y.1 ⟨hxK, hyG⟩, ← hvfin y.1 ⟨hxK, hyG⟩,
        ← EReal.coe_sub, EReal.coe_lt_coe_iff] at hgap
      exact hgap
  calc thetaCapacity ω.form (fun _ => 0)
        (K ∩ sourceCapacityLowerGap U (fun x => u j x.1) (fun x => v x.1) δ)
      ≤ thetaCapacity ω.form (fun _ => 0) (G ∪ H) := thetaCapacity_mono hsub
    _ ≤ thetaCapacity ω.form (fun _ => 0) G + thetaCapacity ω.form (fun _ => 0) H :=
      thetaCapacity_union_le _ _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hGc.le hHc.le
    _ = ε := ENNReal.add_halves ε

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- In dimension zero an actual increasing local PSH sequence converges
pointwise to its actual a.e. limit. Discreteness makes raw and USC suprema
identical; the original functions and all infinite-pole cases are retained. -/
theorem tendsto_pointwise_of_monotone_ae_dim_zero
    (hn : n = 0) (α : AtlasClosedRealOneOneForm (ofFixedModel n M)) (U : Opens M)
    {u : ℕ → M → EReal} {v : M → EReal}
    (hu : ∀ j, (ofFixedModel n M).IsThetaPSHOn α (u j) U)
    (hv : (ofFixedModel n M).IsThetaPSHOn α v U)
    (hm : ∀ x ∈ (U : Set M), Monotone fun j => u j x)
    (hae : NetChartTendstoAEOn (n := n) U u v) :
    ∀ x ∈ (U : Set M), Tendsto (fun j => u j x) atTop (𝓝 (v x)) := by
  subst n
  have hreg := uscRegularization_iSup_eqOn_of_monotone_ae
    (fun j => isLocalQuasiPshOn_of_isThetaPSHOn U.isOpen (hu j))
    (isLocalQuasiPshOn_of_isThetaPSHOn U.isOpen hv) hm hae
  intro x hx
  have hraw : (⨆ j, u j x) = v x := by
    apply le_antisymm
    · have h := le_uscRegularization (⨆ j, u j) x
      rw [hreg hx, iSup_apply] at h
      exact h
    · rw [← hreg hx]
      simpa only [iSup_apply] using
        NegligibleSetsPluripolarProof.uscRegularization_le_of_dim_zero (⨆ j, u j) x
  simpa only [hraw] using tendsto_atTop_iSup (hm x hx)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- A finite original core has eventually empty lower gaps under pointwise
convergence to the actual finite-or-negative-infinite limit. -/
theorem eventually_compact_lowerGap_eq_empty_dim_zero
    (hn : n = 0) (U : Opens M) {u : ℕ → M → EReal} {v : M → EReal}
    (hv : IsLocalQuasiPshOn (n := n) (U : Set M) v)
    (hlim : ∀ x ∈ (U : Set M), Tendsto (fun j => u j x) atTop (𝓝 (v x)))
    {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ j in atTop,
      K ∩ sourceCapacityLowerGap U (fun x => u j x.1) (fun x => v x.1) δ = ∅ := by
  classical
  let : DiscreteTopology M := discreteTopology_iff_isOpen_singleton.mpr
    (fun x => RooftopDimZero.isOpen_singleton_of_dim_zero hn x)
  have hpoint : ∀ x ∈ K, ∀ᶠ j in atTop, ¬ u j x < v x - (δ : EReal) := by
    intro x hx
    by_cases hvb : v x = ⊥
    · exact Eventually.of_forall fun j => by simp [hvb]
    · have hvt := hv.ne_top (hKU hx)
      have hshift : v x - (δ : EReal) < v x := by
        rw [← EReal.coe_toReal hvt hvb, ← EReal.coe_sub, EReal.coe_lt_coe_iff]
        linarith
      filter_upwards [(hlim x (hKU hx)).eventually (lt_mem_nhds hshift)] with j hj
      exact not_lt_of_gt hj
  filter_upwards [hK.finite_of_discrete.eventually_all.mpr hpoint] with j hj
  apply eq_empty_iff_forall_notMem.mpr
  rintro _ ⟨hx, ⟨x, hgap, rfl⟩⟩
  exact hj x.1 hx hgap

/-- The compact lower-gap theorem in every natural dimension. The zero
branch has eventually empty gaps; the positive branch uses the genuine
relative Bedford--Taylor producer and compact closed-null outer capacity. -/
theorem tendsto_kahlerCapacity_compact_lowerGap_of_monotone_sequence
    (ω : KahlerBackground n M)
    (α : AtlasClosedRealOneOneForm (ofFixedModel n M)) (U : Opens M)
    {u : ℕ → M → EReal} {v : M → EReal}
    (hu : ∀ j, (ofFixedModel n M).IsThetaPSHOn α (u j) U)
    (hv : (ofFixedModel n M).IsThetaPSHOn α v U)
    (hm : ∀ x ∈ (U : Set M), Monotone fun j => u j x)
    (hae : NetChartTendstoAEOn (n := n) U u v)
    {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun j => thetaCapacity ω.form (fun _ => 0)
      (K ∩ sourceCapacityLowerGap U (fun x => u j x.1) (fun x => v x.1) δ))
      atTop (𝓝 0) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have hp := tendsto_pointwise_of_monotone_ae_dim_zero hn α U hu hv hm hae
    have he := eventually_compact_lowerGap_eq_empty_dim_zero hn U
      (isLocalQuasiPshOn_of_isThetaPSHOn U.isOpen hv) hp hK hKU hδ
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [he] with j hj
    rw [hj, thetaCapacity_empty]
  · exact tendsto_kahlerCapacity_compact_lowerGap_of_monotone_sequence_pos
      hn ω α U hu hv hm hae hK hKU hδ

end SGPT.NPP.LocalIncreasingCapacityDraft
