import SGPT.NPP.Capacity2QuasiPshBridge
import SGPT.NPP.Capacity2Monotone

/-!
# Decreasing nets on an open set: convergence in capacity on compact subsets

Source `prop:mono_psh_cap` (1) is false on a general open set `U` with the book's
`def:conv_cap` (erratum E09, Lean-checked in `MonotoneCapacityCounterexample`).  The proposed
repair measures the gap sets after intersection with a compact `K ⊆ U`.  This file proves the
repaired clause (1) for arbitrary directed nets in `PSH(U, θ)` (and, more generally, for locally
quasi-psh functions on `U`): for every compact `K ⊆ U` and `δ > 0`,
`Cap_θ(K ∩ {φ_i > φ + δ}) → 0`, while the lower gaps `{φ_i < φ - δ}` are empty.

Proof: by `ex:psh_qc` on `U` there is an open `G` of small capacity off which `φ` is finite and
continuous on `U`; on the compact set `K \ G` a Dini argument for nets (upper semicontinuity of
`φ_i` on `U`, finite subcover, directedness) shows that `K ∩ {φ_i > φ + δ}` lies in `G`
eventually.
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
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **Repaired `prop:mono_psh_cap` (1), local-quasi-psh form.**  A decreasing net of locally
quasi-psh functions on an open `U` with locally quasi-psh pointwise limit `φ₀` on `U` converges
to `φ₀` in capacity on every compact `K ⊆ U`. -/
theorem tendsto_capacity_compact_upperGap_of_antitone (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (U : Opens M) {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)]
    {φ : I → M → EReal} {φ₀ : M → EReal}
    (hφ : ∀ i, IsLocalQuasiPshOn (n := n) (U : Set M) (φ i))
    (hφ₀ : IsLocalQuasiPshOn (n := n) (U : Set M) φ₀)
    (hanti : ∀ x ∈ (U : Set M), Antitone fun i => φ i x)
    (hlim : ∀ x ∈ (U : Set M), Tendsto (fun i => φ i x) atTop (𝓝 (φ₀ x)))
    {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun i => sourceThetaCapacity θ
      (K ∩ sourceCapacityUpperGap U (fun x => φ i x.1) (fun x => φ₀ x.1) δ)) atTop (𝓝 0) := by
  classical
  rcases isEmpty_or_nonempty I with hI | hI
  · rw [Filter.filter_eq_bot_of_isEmpty (atTop : Filter I)]
    exact tendsto_bot
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | htop
  · exact Eventually.of_forall fun _ => le_top
  have hr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  obtain ⟨C, hC, hctl⟩ := exists_source_capacity_control_by_kahler omega θ hbig (half_pos hr)
  have hη : (0 : ℝ≥0∞) < ENNReal.ofReal (ε.toReal / 2 / C) := ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨G, hGo, hGc, hGf, hGcont⟩ := exists_isOpen_kahlerCapacity_lt_on_open omega U.isOpen hφ₀ hη
  have hGθ : sourceThetaCapacity θ G ≤ ε := by
    calc sourceThetaCapacity θ G
        ≤ ENNReal.ofReal (ε.toReal / 2) + ENNReal.ofReal C *
            sourceThetaCapacity (nativeClosedFormToAtlas omega.form) G := hctl G
      _ ≤ ENNReal.ofReal (ε.toReal / 2) + ENNReal.ofReal C * ENNReal.ofReal (ε.toReal / 2 / C) := by
          rw [sourceThetaCapacity_kahler]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hGc.le zero_le)
      _ = ε := by
          rw [← ENNReal.ofReal_mul hC.le, mul_div_cancel₀ _ hC.ne',
            ← ENNReal.ofReal_add (half_pos hr).le (half_pos hr).le, add_halves,
            ENNReal.ofReal_toReal htop]
  set L : Set M := K ∩ Gᶜ with hLdef
  have hL : IsCompact L := hK.inter_right hGo.isClosed_compl
  have hLU : ∀ x ∈ L, x ∈ (U : Set M) \ G := fun x hx => ⟨hKU hx.1, hx.2⟩
  have hloc : ∀ x ∈ L, ∃ (i : I) (W : Set M), IsOpen W ∧ x ∈ W ∧
      ∀ y ∈ W ∩ L, φ i y < (((φ₀ y).toReal + δ : ℝ) : EReal) := by
    intro x hx
    have hxU := hLU x hx
    have hfx : φ₀ x = ((φ₀ x).toReal : EReal) :=
      (EReal.coe_toReal (hφ₀.ne_top hxU.1) (hGf x hxU)).symm
    have hev : ∀ᶠ i in atTop, φ i x < (((φ₀ x).toReal + δ / 2 : ℝ) : EReal) := by
      apply (hlim x hxU.1).eventually (gt_mem_nhds _)
      conv_lhs => rw [hfx]
      rw [EReal.coe_lt_coe_iff]
      linarith
    obtain ⟨i, hi⟩ := hev.exists
    obtain ⟨W₂, hW₂s, hW₂o, hxW₂⟩ :=
      mem_nhds_iff.mp (((hφ i).upperSemicontinuousAt hxU.1) _ hi)
    have hcw : ContinuousWithinAt (fun y => (φ₀ y).toReal) ((U : Set M) \ G) x := hGcont x hxU
    have hball := (hcw.mono fun y hy => hLU y hy).preimage_mem_nhdsWithin
      (Metric.ball_mem_nhds _ (half_pos hδ))
    obtain ⟨W₁, hW₁o, hxW₁, hW₁s⟩ := mem_nhdsWithin.mp hball
    refine ⟨i, W₁ ∩ W₂, hW₁o.inter hW₂o, ⟨hxW₁, hxW₂⟩, fun y hy => ?_⟩
    have h1 : φ i y < (((φ₀ x).toReal + δ / 2 : ℝ) : EReal) := hW₂s hy.1.2
    have h2 : dist (φ₀ y).toReal (φ₀ x).toReal < δ / 2 := hW₁s ⟨hy.1.1, hy.2⟩
    rw [Real.dist_eq, abs_lt] at h2
    refine h1.trans_le (EReal.coe_le_coe_iff.mpr ?_)
    linarith
  choose! idx W hWo hxW hWlt using hloc
  obtain ⟨t, htcover⟩ := hL.elim_nhds_subcover' (fun x hx => W x)
    (fun x hx => (hWo x hx).mem_nhds (hxW x hx))
  obtain ⟨i₀, hi₀⟩ := Finset.exists_le (t.image fun x => idx x.1)
  filter_upwards [eventually_ge_atTop i₀] with i hi
  refine (sourceThetaCapacity_mono θ ?_).trans hGθ
  rintro y ⟨hyK, ⟨z, hz, rfl⟩⟩
  by_contra hyG
  have hzL : z.1 ∈ L := ⟨hyK, hyG⟩
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (htcover hzL)
  have hle : idx x.1 ≤ i := (hi₀ _ (Finset.mem_image_of_mem _ hxt)).trans hi
  have hlt := hWlt x.1 x.2 z.1 ⟨hyx, hzL⟩
  have hz' : φ₀ z.1 + (δ : EReal) < φ i z.1 := hz
  have hfz : φ₀ z.1 = ((φ₀ z.1).toReal : EReal) :=
    (EReal.coe_toReal (hφ₀.ne_top z.2) (hGf z.1 ⟨z.2, hyG⟩)).symm
  rw [hfz, ← EReal.coe_add] at hz'
  exact absurd ((hanti z.1 z.2 hle).trans_lt hlt) (not_lt.mpr hz'.le)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The lower gaps of a decreasing net above its limit are empty. -/
theorem sourceCapacityLowerGap_eq_empty_of_antitone (U : Opens M) {I : Type*} [Preorder I]
    [IsDirected I (· ≤ ·)] {φ : I → M → EReal} {φ₀ : M → EReal}
    (hanti : ∀ x ∈ (U : Set M), Antitone fun i => φ i x)
    (hlim : ∀ x ∈ (U : Set M), Tendsto (fun i => φ i x) atTop (𝓝 (φ₀ x))) {δ : ℝ}
    (hδ : 0 ≤ δ) (i : I) :
    sourceCapacityLowerGap U (fun x => φ i x.1) (fun x => φ₀ x.1) δ = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro _ ⟨y, hy, rfl⟩
  have h1 : φ i y.1 < φ₀ y.1 - (δ : EReal) := hy
  have h2 : φ₀ y.1 ≤ φ i y.1 := (hanti y.1 y.2).le_of_tendsto (hlim y.1 y.2) i
  have h3 : φ₀ y.1 - (δ : EReal) ≤ φ₀ y.1 :=
    (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot δ)) (Or.inl (EReal.coe_ne_top δ))).mpr
      (le_add_of_nonneg_right (EReal.coe_nonneg.mpr hδ))
  exact absurd (h1.trans_le (h3.trans h2)) (lt_irrefl _)

/-- **Repaired `prop:mono_psh_cap` (1)** (proposed repair of erratum E09): for a decreasing net
`(φ_i)` in `PSH(U, θ')` with limit `φ ∈ PSH(U, θ')` (any closed real smooth `(1,1)`-form `θ'`
on `X`), the gap sets intersected with any compact `K ⊆ U` have `Cap_θ → 0` (`θ` big). -/
theorem sourceMonoPshCap_decreasing_compact (omega : KahlerBackground n M)
    (θ θ' : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (U : Opens M) {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)]
    {φ : I → M → EReal} {φ₀ : M → EReal}
    (hφ : ∀ i, (ofFixedModel n M).IsThetaPSHOn θ' (φ i) U)
    (hφ₀ : (ofFixedModel n M).IsThetaPSHOn θ' φ₀ U)
    (hanti : ∀ x ∈ (U : Set M), Antitone fun i => φ i x)
    (hlim : ∀ x ∈ (U : Set M), Tendsto (fun i => φ i x) atTop (𝓝 (φ₀ x)))
    {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun i => sourceThetaCapacity θ
      (K ∩ sourceCapacityUpperGap U (fun x => φ i x.1) (fun x => φ₀ x.1) δ)) atTop (𝓝 0) ∧
    Tendsto (fun i => sourceThetaCapacity θ
      (K ∩ sourceCapacityLowerGap U (fun x => φ i x.1) (fun x => φ₀ x.1) δ)) atTop (𝓝 0) := by
  refine ⟨tendsto_capacity_compact_upperGap_of_antitone omega θ hbig U
    (fun i => isLocalQuasiPshOn_of_isThetaPSHOn U.isOpen (hφ i))
    (isLocalQuasiPshOn_of_isThetaPSHOn U.isOpen hφ₀) hanti hlim hK hKU hδ, ?_⟩
  simp only [sourceCapacityLowerGap_eq_empty_of_antitone U hanti hlim hδ.le, inter_empty,
    sourceThetaCapacity_empty]
  exact tendsto_const_nhds

end SGPT.NPP
