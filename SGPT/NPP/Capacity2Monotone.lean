import SGPT.NPP.Capacity2QuasiContinuity
import SGPT.NPP.CapacityConvergenceMonotone
import SGPT.PSH.SourceCapacityConvergence
import SGPT.Foundations.Analysis.Pending.ChoquetRegularization
import SGPT.Foundations.Analysis.Pending.NegligibleSetsPluripolarProof

/-!
# Monotone nets of `θ`-psh functions on `X` converge in capacity

Source `prop:mono_psh_cap` (chapter `chapter_npp.tex`, section `sec:qc`): a net
`(φ_i)_{i ∈ I}` in `PSH(U, θ)` with limit `φ ∈ PSH(U, θ)` converges to `φ` in capacity
(`def:conv_cap`) if (1) it decreases to `φ`, or (2) it increases and converges almost
everywhere to `φ`.

For a general open `U` clause (1) is false (source erratum E09, Lean-checked in
`MonotoneCapacityCounterexample`).  This file proves both clauses for `U = X`, for arbitrary
directed nets, with the capacity `Cap_θ` of any big form `θ`:

* (1) `sourceMonoPshCap_decreasing`: by quasi-continuity of `φ` (`ex:psh_qc`), off an open set
  `G` of small capacity `φ` is finite and continuous on the compact set `X \ G`; a Dini
  argument for nets (upper semicontinuity of `φ_i`, finite subcover, directedness) shows that
  the upper gaps `{φ_i > φ + δ}` lie in `G` eventually;
* (2) `sourceMonoPshCap_increasing` (`X` connected): Choquet's lemma gives indices `j_k`,
  which may be taken increasing, with `(sup_k φ_{j_k})^* = φ`; Bedford--Taylor's theorem on
  negligible sets makes `φ_{j_k} → φ` almost everywhere, so the sequence converges in Kähler
  capacity (lane S30, `tendsto_capacity_gap_of_monotone_ae`), and the lower gaps of `φ_i`,
  `i ≥ j_k`, lie in those of `φ_{j_k}` up to a pluripolar set.  Kähler capacity controls
  `Cap_θ` (`exists_source_capacity_control_by_kahler`).
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open ThetaCapacity
open SGPT.PSH.VariableComplexAtlas SGPT.NPP.CapacityConvergence

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Almost-everywhere convergence of a net on `X`: Lebesgue-almost everywhere in every
chart (null sets of a manifold are measured by the Lebesgue measures of its charts). -/
def NetChartTendstoAE {I : Type*} [Preorder I] (u : I → M → EReal) (v : M → EReal) : Prop :=
  ∀ e : ComplexChart n M, ∀ᵐ z ∂volume.restrict e.val.target,
    Tendsto (fun i => u i (e.val.symm z)) atTop (𝓝 (v (e.val.symm z)))

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **Source `prop:mono_psh_cap` (1), `U = X`.**  A decreasing net of `θ`-psh functions on `X`
with `θ`-psh limit `φ₀` converges to `φ₀` in capacity (`def:conv_cap`, `Cap_θ`, `θ` big). -/
theorem sourceMonoPshCap_decreasing (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] {φ : I → M → EReal} {φ₀ : M → EReal}
    (hφ : ∀ i, (ofFixedModel n M).IsThetaPSH θ (φ i))
    (hφ₀ : (ofFixedModel n M).IsThetaPSH θ φ₀)
    (hanti : ∀ x, Antitone fun i => φ i x)
    (hlim : ∀ x, Tendsto (fun i => φ i x) atTop (𝓝 (φ₀ x))) :
    SourceNetConvergesInCapacity θ ⊤ (fun i (x : (⊤ : Opens M)) => φ i x.1)
      (fun x => φ₀ x.1) := by
  have hφm : ∀ i, Measurable (φ i) := fun i =>
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp (hφ i)).1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hφ₀m : Measurable φ₀ :=
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp hφ₀).1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  refine ⟨fun i => (hφm i).comp measurable_subtype_coe, hφ₀m.comp measurable_subtype_coe,
    fun δ hδ => ⟨?_, ?_⟩⟩
  · rcases isEmpty_or_nonempty I with hI | hI
    · rw [Filter.filter_eq_bot_of_isEmpty (atTop : Filter I)]
      exact tendsto_bot
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    rcases eq_or_ne ε ⊤ with rfl | htop
    · exact Eventually.of_forall fun _ => le_top
    have hr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
    have hq := ((isThetaPSH_iff_nativeThetaPotential θ φ₀).mp hφ₀).quasiPshPotential
    obtain ⟨G, hGo, hGc, hGf, hGcont⟩ :=
      exists_isOpen_sourceCapacity_le_finite_continuousOn ω θ hbig hq hr
    have hK : IsCompact Gᶜ := hGo.isClosed_compl.isCompact
    -- for each point of the compact set, a neighbourhood and an index
    have hloc : ∀ x ∈ Gᶜ, ∃ (i : I) (W : Set M), IsOpen W ∧ x ∈ W ∧
        ∀ y ∈ W ∩ Gᶜ, φ i y < (((φ₀ y).toReal + δ : ℝ) : EReal) := by
      intro x hx
      have hfx : φ₀ x = ((φ₀ x).toReal : EReal) :=
        (EReal.coe_toReal (hφ₀.1 x) (hGf x hx)).symm
      have hev : ∀ᶠ i in atTop, φ i x < (((φ₀ x).toReal + δ / 2 : ℝ) : EReal) := by
        apply (hlim x).eventually (gt_mem_nhds _)
        conv_lhs => rw [hfx]
        rw [EReal.coe_lt_coe_iff]
        linarith
      obtain ⟨i, hi⟩ := hev.exists
      have husc := ((isThetaPSH_iff_nativeThetaPotential θ _).mp
        (hφ i)).1.quasiPlurisubharmonic.upperSemicontinuous x _ hi
      obtain ⟨W₂, hW₂s, hW₂o, hxW₂⟩ := mem_nhds_iff.mp husc
      have hcw : ContinuousWithinAt (fun y => (φ₀ y).toReal) Gᶜ x := hGcont x hx
      have hball := hcw.preimage_mem_nhdsWithin (Metric.ball_mem_nhds _ (half_pos hδ))
      obtain ⟨W₁, hW₁o, hxW₁, hW₁s⟩ := mem_nhdsWithin.mp hball
      refine ⟨i, W₁ ∩ W₂, hW₁o.inter hW₂o, ⟨hxW₁, hxW₂⟩, fun y hy => ?_⟩
      have h1 : φ i y < (((φ₀ x).toReal + δ / 2 : ℝ) : EReal) := hW₂s hy.1.2
      have h2 : dist (φ₀ y).toReal (φ₀ x).toReal < δ / 2 := hW₁s ⟨hy.1.1, hy.2⟩
      rw [Real.dist_eq, abs_lt] at h2
      refine h1.trans_le (EReal.coe_le_coe_iff.mpr ?_)
      linarith
    choose! idx W hWo hxW hWlt using hloc
    obtain ⟨t, htcover⟩ := hK.elim_nhds_subcover' (fun x hx => W x)
      (fun x hx => (hWo x hx).mem_nhds (hxW x hx))
    classical
    obtain ⟨i₀, hi₀⟩ := Finset.exists_le (t.image fun x => idx x.1)
    filter_upwards [eventually_ge_atTop i₀] with i hi
    refine (sourceThetaCapacity_mono θ ?_).trans (hGc.trans_eq (ENNReal.ofReal_toReal htop))
    rintro _ ⟨y, hy, rfl⟩
    by_contra hyG
    obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (htcover hyG)
    have hle : idx x.1 ≤ i := (hi₀ _ (Finset.mem_image_of_mem _ hxt)).trans hi
    have hlt := hWlt x.1 x.2 y.1 ⟨hyx, hyG⟩
    have hy' : φ₀ y.1 + (δ : EReal) < φ i y.1 := hy
    have hfy : φ₀ y.1 = ((φ₀ y.1).toReal : EReal) :=
      (EReal.coe_toReal (hφ₀.1 y.1) (hGf y.1 hyG)).symm
    rw [hfy, ← EReal.coe_add] at hy'
    exact absurd ((hanti y.1 hle).trans_lt hlt) (not_lt.mpr hy'.le)
  · have hempty : ∀ i, sourceCapacityLowerGap (⊤ : Opens M) (fun x => φ i x.1)
        (fun x => φ₀ x.1) δ = ∅ := by
      intro i
      apply eq_empty_iff_forall_notMem.mpr
      rintro _ ⟨y, hy, rfl⟩
      have h1 : φ i y.1 < φ₀ y.1 - (δ : EReal) := hy
      rcases isEmpty_or_nonempty I with hI | hI
      · exact isEmptyElim i
      have h2 : φ₀ y.1 ≤ φ i y.1 := (hanti y.1).le_of_tendsto (hlim y.1) i
      have h3 : φ₀ y.1 - (δ : EReal) ≤ φ₀ y.1 :=
        (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot δ)) (Or.inl (EReal.coe_ne_top δ))).mpr
          (le_add_of_nonneg_right (EReal.coe_nonneg.mpr hδ.le))
      exact absurd (h1.trans_le (h3.trans h2)) (lt_irrefl _)
    simp only [hempty, sourceThetaCapacity_empty]
    exact tendsto_const_nhds

/-- A cofinal-from-below increasing sequence of indices dominating a given sequence. -/
theorem exists_monotone_dominating {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)]
    (idx : ℕ → I) : ∃ j : ℕ → I, Monotone j ∧ ∀ k, idx k ≤ j k := by
  let step : ℕ → I → I := fun k a => Classical.choose (exists_ge_ge a (idx (k + 1)))
  have hstep : ∀ k a, a ≤ step k a ∧ idx (k + 1) ≤ step k a := fun k a =>
    Classical.choose_spec (exists_ge_ge a (idx (k + 1)))
  let j : ℕ → I := fun k => Nat.rec (idx 0) (fun k a => step k a) k
  refine ⟨j, monotone_nat_of_le_succ fun k => (hstep k (j k)).1, fun k => ?_⟩
  cases k with
  | zero => exact le_rfl
  | succ k => exact (hstep k (j k)).2

variable [ConnectedSpace M]

/-- **Source `prop:mono_psh_cap` (2), `U = X`** (`X` connected).  An increasing net of
`θ`-psh functions on `X` converging almost everywhere to a `θ`-psh `φ₀` converges to `φ₀` in
capacity (`def:conv_cap`, `Cap_θ`, `θ` big). -/
theorem sourceMonoPshCap_increasing (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] {φ : I → M → EReal} {φ₀ : M → EReal}
    (hφ : ∀ i, (ofFixedModel n M).IsThetaPSH θ (φ i))
    (hφ₀ : (ofFixedModel n M).IsThetaPSH θ φ₀)
    (hmono : ∀ x, Monotone fun i => φ i x)
    (hae : NetChartTendstoAE (n := n) φ φ₀) :
    SourceNetConvergesInCapacity θ ⊤ (fun i (x : (⊤ : Opens M)) => φ i x.1)
      (fun x => φ₀ x.1) := by
  have hφN : ∀ i, IsThetaPshPotential (atlasClosedFormToNative θ).val (φ i) := fun i =>
    (isThetaPSH_iff_nativeThetaPotential θ _).mp (hφ i)
  have hφ₀N := (isThetaPSH_iff_nativeThetaPotential θ _).mp hφ₀
  have hφm : ∀ i, Measurable (φ i) := fun i =>
    (hφN i).1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hφ₀m : Measurable φ₀ := hφ₀N.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hle : ∀ i, φ i ≤ φ₀ := fun i => le_of_chartAELE (hφN i).1 hφ₀N.1 fun e => by
    filter_upwards [hae e] with z hz
    exact (hmono _).ge_of_tendsto hz i
  refine ⟨fun i => (hφm i).comp measurable_subtype_coe, hφ₀m.comp measurable_subtype_coe,
    fun δ hδ => ⟨?_, ?_⟩⟩
  · -- the upper gaps are empty
    have hempty : ∀ i, sourceCapacityUpperGap (⊤ : Opens M) (fun x => φ i x.1)
        (fun x => φ₀ x.1) δ = ∅ := by
      intro i
      apply eq_empty_iff_forall_notMem.mpr
      rintro _ ⟨y, hy, rfl⟩
      have h1 : φ₀ y.1 + (δ : EReal) < φ i y.1 := hy
      exact absurd ((le_add_of_nonneg_right (EReal.coe_nonneg.mpr hδ.le)).trans_lt h1)
        (not_lt.mpr (hle i y.1))
    simp only [hempty, sourceThetaCapacity_empty]
    exact tendsto_const_nhds
  rcases isEmpty_or_nonempty I with hI | hI
  · rw [Filter.filter_eq_bot_of_isEmpty (atTop : Filter I)]
    exact tendsto_bot
  rcases isEmpty_or_nonempty M with hM | hM
  · have : ∀ i, sourceCapacityLowerGap (⊤ : Opens M) (fun x => φ i x.1) (fun x => φ₀ x.1) δ = ∅ :=
      fun i => eq_empty_iff_forall_notMem.mpr fun x => isEmptyElim x
    simp only [this, sourceThetaCapacity_empty]
    exact tendsto_const_nhds
  -- Choquet's lemma and a dominating increasing sequence of indices
  have hFne : (range φ).Nonempty := range_nonempty φ
  obtain ⟨s, hsF, hs⟩ := exists_seq_uscRegularization_iSup_eq hFne
  choose idx hidx using hsF
  obtain ⟨j, hjmono, hjdom⟩ := exists_monotone_dominating idx
  set u : ℕ → M → EReal := fun k => φ (j k) with hudef
  have hum : ∀ x, Monotone fun k => u k x := fun x k l hkl => hmono x (hjmono hkl)
  obtain ⟨b, hb⟩ := hφ₀N.exists_global_upper_bound
  have hub : ∀ k x, u k x ≤ (b : EReal) := fun k x => (hle (j k) x).trans (hb x)
  have hw : IsThetaPshPotential (atlasClosedFormToNative θ).val (uscRegularization (⨆ k, u k)) :=
    NegligibleSetsPluripolarProof.isThetaPshPotential_uscRegularization_iSup_of_le
      (fun k => hφN (j k)) hub
  have hreg : uscRegularization (⨆ k, u k) = φ₀ := by
    apply le_antisymm
    · exact FirstPass.uscRegularization_le hφ₀N.1.quasiPlurisubharmonic.upperSemicontinuous
        (fun x => by simpa only [iSup_apply] using iSup_le fun k => hle (j k) x)
    · have hsu : uscRegularization (⨆ k, s k) ≤ uscRegularization (⨆ k, u k) := by
        apply uscRegularization_mono
        intro x
        simp only [iSup_apply]
        exact iSup_le fun k => le_iSup_of_le k (by rw [← hidx k]; exact hmono x (hjdom k))
      refine le_of_chartAELE hφ₀N.1 hw.1 fun e => ?_
      filter_upwards [hae e] with z hz
      refine le_of_tendsto' hz fun i => ?_
      have h1 : φ i (e.val.symm z) ≤ sSup (range φ) (e.val.symm z) := by
        rw [sSup_apply]
        exact le_iSup_of_le ⟨φ i, mem_range_self i⟩ le_rfl
      exact h1.trans ((FirstPass.le_uscRegularization _ _).trans
        (by rw [← hs]; exact hsu _))
  -- almost-everywhere convergence of the sequence
  have hqe := NegligibleSetsPluripolarProof.negligibleSetsPluripolar ω
    (atlasClosedFormToNative θ) u b (fun k => hφN (j k)) hub
  have hseqae : ChartTendstoAE (n := n) u φ₀ := by
    intro e
    filter_upwards [hqe.ae_in_chart e volume] with z hz
    have heq : (⨆ k, u k) (e.val.symm z) = φ₀ (e.val.symm z) := by
      apply le_antisymm
      · simpa only [iSup_apply] using iSup_le fun k => hle (j k) (e.val.symm z)
      · rw [← hreg]; exact hz
    rw [← heq, iSup_apply]
    exact tendsto_atTop_iSup (hum _)
  have hgap := tendsto_capacity_gap_of_monotone_ae ω (fun k => hφN (j k)) hφ₀N hum hseqae
    (δ / 2) (half_pos hδ)
  -- conclusion
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | htop
  · exact Eventually.of_forall fun _ => le_top
  have hr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  obtain ⟨C, hC, hctl⟩ := exists_source_capacity_control_by_kahler ω θ hbig (half_pos hr)
  have hsmall := (ENNReal.tendsto_nhds_zero.mp hgap) (ENNReal.ofReal (ε.toReal / 2 / C))
    (ENNReal.ofReal_pos.mpr (by positivity))
  obtain ⟨k, hk⟩ := hsmall.exists
  have hpole : thetaCapacity ω.form (fun _ => 0) {x | u k x = ⊥} = 0 :=
    thetaCapacity_eq_zero_of_manifoldLocallyPluripolar _
      (quasiPsh_poles_manifoldLocallyPluripolar (hφN (j k)).quasiPshPotential)
  filter_upwards [eventually_ge_atTop (j k)] with i hi
  have hsub : sourceCapacityLowerGap (⊤ : Opens M) (fun x => φ i x.1) (fun x => φ₀ x.1) δ ⊆
      {x | u k x ≠ ⊥ ∧ φ₀ x ≠ ⊥ ∧ δ / 2 < |(u k x).toReal - (φ₀ x).toReal|} ∪
        {x | u k x = ⊥} := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : φ i y.1 < φ₀ y.1 - (δ : EReal) := hy
    have h2 : u k y.1 ≤ φ i y.1 := hmono y.1 hi
    by_cases hub' : u k y.1 = ⊥
    · exact Or.inr hub'
    left
    have hφ₀b : φ₀ y.1 ≠ ⊥ := fun h => by
      rw [h, EReal.bot_sub] at h1
      exact not_lt_bot h1
    have hut : u k y.1 ≠ ⊤ := (hφ (j k)).1 y.1
    have hφ₀t : φ₀ y.1 ≠ ⊤ := hφ₀.1 y.1
    refine ⟨hub', hφ₀b, ?_⟩
    have h3 := h2.trans_lt h1
    rw [← EReal.coe_toReal hut hub', ← EReal.coe_toReal hφ₀t hφ₀b, ← EReal.coe_sub,
      EReal.coe_lt_coe_iff] at h3
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  calc sourceThetaCapacity θ
        (sourceCapacityLowerGap (⊤ : Opens M) (fun x => φ i x.1) (fun x => φ₀ x.1) δ)
      ≤ ENNReal.ofReal (ε.toReal / 2) + ENNReal.ofReal C *
          sourceThetaCapacity (nativeClosedFormToAtlas ω.form)
            (sourceCapacityLowerGap (⊤ : Opens M) (fun x => φ i x.1) (fun x => φ₀ x.1) δ) :=
        hctl _
    _ ≤ ENNReal.ofReal (ε.toReal / 2) + ENNReal.ofReal C * ENNReal.ofReal (ε.toReal / 2 / C) := by
        rw [sourceThetaCapacity_kahler]
        refine add_le_add le_rfl (mul_le_mul' le_rfl ?_)
        calc thetaCapacity ω.form (fun _ => 0)
              (sourceCapacityLowerGap (⊤ : Opens M) (fun x => φ i x.1) (fun x => φ₀ x.1) δ)
            ≤ thetaCapacity ω.form (fun _ => 0)
                ({x | u k x ≠ ⊥ ∧ φ₀ x ≠ ⊥ ∧ δ / 2 < |(u k x).toReal - (φ₀ x).toReal|} ∪
                  {x | u k x = ⊥}) := thetaCapacity_mono hsub
          _ ≤ _ := thetaCapacity_union_le _ _ _ _
          _ ≤ ENNReal.ofReal (ε.toReal / 2 / C) + 0 := add_le_add hk hpole.le
          _ = _ := add_zero _
    _ = ε := by
        rw [← ENNReal.ofReal_mul hC.le, mul_div_cancel₀ _ hC.ne',
          ← ENNReal.ofReal_add (half_pos hr).le (half_pos hr).le, add_halves,
          ENNReal.ofReal_toReal htop]

end SGPT.NPP
