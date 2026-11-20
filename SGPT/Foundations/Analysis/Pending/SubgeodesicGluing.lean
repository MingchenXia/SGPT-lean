import SGPT.Foundations.Analysis.Pending.SubgeodesicReplacement
import SGPT.Foundations.Analysis.Pending.SubgeodesicChartPotential
import SGPT.Foundations.Analysis.Pending.PshLocalLowerSupports
import SGPT.Foundations.Analysis.Pending.ThetaPshCodimTwoExtension

/-!
# Dominating replacement glues actual subgeodesics

Xia, SGPT Lemma 4.1.1, PDF pages 0152--0153. The replacement is the actual
piecewise curve, with genuine potential slices, chart-strip PSH, and the
original two chart-local L¹ endpoint limits. Joint USC is produced from the
endpoint chord bounds, rather than assumed as an additional gluing premise.
-/

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SubgeodesicGluing

open FirstPass SubgeodesicChartPotential

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

omit [CompactSpace M] in
/-- Inverse affine time pulls the new normalized chart strip back to the
physical replacement strip, using the same local potential as the old curve. -/
theorem plurisubharmonicOn_replacement_branch
    {theta : SmoothRealForm n M 2} {replacement : ℝ → M → EReal}
    (hr : IsSubgeodesicInterior theta replacement)
    (e : ComplexChart n M) {W : Set (ComplexModel n)} {rho : ComplexModel n → ℝ}
    (hrho : IsSmoothLocalPotential theta e W rho) {a b : ℝ} (hab : a < b) :
    PlurisubharmonicOn
      (fun p : ComplexModel n × ℂ =>
        chartFunction (replacement ((p.2.re - a) / (b - a))) e p.1 + (rho p.1 : EReal))
      (W ×ˢ {τ : ℂ | τ.re ∈ Ioo a b}) := by
  have hpull := (plurisubharmonicOn_subgeodesicChartFunction hr e hrho).comp_affine
    (complexTimeReparamLinear (n := n) 0 ((b - a)⁻¹))
    (complexTimeReparamTranslation (n := n) (-a / (b - a)))
  have htime (t : ℝ) : -a / (b - a) + (b - a)⁻¹ * t = (t - a) / (b - a) := by
    ring
  have hmap (p : ComplexModel n × ℂ) :
      (complexTimeReparamTranslation (n := n) (-a / (b - a)) +
        complexTimeReparamLinear (n := n) 0 ((b - a)⁻¹) p).1 = p.1 ∧
      (complexTimeReparamTranslation (n := n) (-a / (b - a)) +
        complexTimeReparamLinear (n := n) 0 ((b - a)⁻¹) p).2.re =
          (p.2.re - a) / (b - a) := by
    constructor
    · change 0 + p.1 = p.1
      exact zero_add _
    · change (((-a / (b - a) : ℝ) : ℂ) +
        (((b - a)⁻¹ - 0 : ℝ) : ℂ) * p.2).re = _
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        sub_zero, zero_mul, htime]
  have hmono : W ×ˢ {τ : ℂ | τ.re ∈ Ioo a b} ⊆
      (fun p => complexTimeReparamTranslation (n := n) (-a / (b - a)) +
        complexTimeReparamLinear (n := n) 0 ((b - a)⁻¹) p) ⁻¹'
          geodesicChartDomain W := by
    intro p hp
    change _ ∈ W ∧ _ ∈ Ioo (0 : ℝ) 1
    rw [(hmap p).1, (hmap p).2]
    exact ⟨hp.1, replacementTime_mem_Ioo hab hp.2⟩
  intro p hp
  refine (hpull.mono hmono p hp).congr (Eventually.of_forall fun q => ?_)
  change chartFunction (replacement _) e _ + (rho _ : EReal) = _
  rw [(hmap q).1, (hmap q).2]

/-- Domination supplies a touching old PSH lower support at each seam.
Actual joint USC supplies the other hypothesis of the local support theorem. -/
theorem isSubgeodesicInterior_replacementCurve
    {theta : SmoothRealForm n M 2} {curve replacement : ℝ → M → EReal}
    {u₀ u₁ : M → EReal} (h : IsSubgeodesicFrom theta curve u₀ u₁)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b)
    (hr : IsSubgeodesicFrom theta replacement
      (closedSubgeodesicSlice curve u₀ u₁ a) (closedSubgeodesicSlice curve u₀ u₁ b))
    (hdom : ∀ t ∈ Ioo a b, curve t ≤ replacement ((t - a) / (b - a))) :
    IsSubgeodesicInterior theta (replacementCurve curve replacement a b) := by
  classical
  constructor
  · intro t ht
    by_cases htab : t ∈ Ioo a b
    · simpa [replacementCurve, htab] using
        hr.interior.thetaPshPotential (replacementTime_mem_Ioo hab htab)
    · simpa [replacementCurve, htab] using h.interior.thetaPshPotential ht
  · intro e z hz
    obtain ⟨W, rho, hzW, hrho, hOld⟩ := h.interior.complexified_psh e hz
    refine ⟨W, rho, hzW, hrho, ?_⟩
    let U := geodesicChartDomain W
    let V := W ×ˢ {τ : ℂ | τ.re ∈ Ioo a b}
    let f := fun p : ComplexModel n × ℂ =>
      chartFunction (replacement ((p.2.re - a) / (b - a))) e p.1 + (rho p.1 : EReal)
    have hU : IsOpen U := isOpen_geodesicChartDomain hrho.1
    have hV : IsOpen V := hrho.1.prod (isOpen_Ioo.preimage Complex.continuous_re)
    have hVU : V ⊆ U := by
      intro p hp
      exact ⟨hp.1, ha.trans_lt hp.2.1, hp.2.2.trans_le hb⟩
    have hNew : PlurisubharmonicOn f V :=
      plurisubharmonicOn_replacement_branch hr.interior e hrho hab
    have husc : UpperSemicontinuousOn
        (subgeodesicChartFunction (replacementCurve curve replacement a b) e rho) U := by
      intro p hp
      have hsymm : ContinuousAt (fun q : ComplexModel n × ℂ => e.val.symm q.1) p :=
        (e.val.continuousAt_symm (hrho.2.1 hp.1)).comp continuousAt_fst
      have hre : ContinuousAt (fun q : ComplexModel n × ℂ => q.2.re) p :=
        Complex.continuous_re.continuousAt.comp continuousAt_snd
      have hcomp : UpperSemicontinuousAt
          (fun q : ComplexModel n × ℂ =>
            replacementCurve curve replacement a b q.2.re (e.val.symm q.1)) p :=
        UpperSemicontinuousAt.comp (g := fun q : ComplexModel n × ℂ =>
          (e.val.symm q.1, q.2.re)) (c := p)
          (upperSemicontinuousAt_replacementCurve h hab hr _ hp.2) (hsymm.prodMk hre)
      have hrhoc : ContinuousAt (fun q : ComplexModel n × ℂ => rho q.1) p :=
        (((hrho.2.2.1 p.1 hp.1).contDiffAt (hrho.1.mem_nhds hp.1)).continuousAt).comp
          continuousAt_fst
      have hadd : UpperSemicontinuousAt
          (subgeodesicChartFunction (replacementCurve curve replacement a b) e rho) p :=
        ThetaPshCodimTwoExtension.upperSemicontinuousAt_add_real hcomp hrhoc
      intro c hc
      exact Filter.Eventually.filter_mono nhdsWithin_le_nhds (hadd c hc)
    apply PshLocalLowerSupports.plurisubharmonicOn_of_local_lower_supports hU husc
    intro p hp
    by_cases hpt : p.2.re ∈ Ioo a b
    · refine ⟨V, hV, ⟨hp.1, hpt⟩, hVU, f, hNew, ?_, ?_⟩
      · simp [f, subgeodesicChartFunction, chartFunction, replacementCurve, hpt]
      · intro q hq
        have hqt : q.2.re ∈ Ioo a b := hq.2
        simp [f, subgeodesicChartFunction, chartFunction, replacementCurve, hqt]
    · refine ⟨U, hU, hp, subset_rfl, subgeodesicChartFunction curve e rho, hOld, ?_, ?_⟩
      · simp [subgeodesicChartFunction, chartFunction, replacementCurve, hpt]
      · intro q _
        by_cases hqt : q.2.re ∈ Ioo a b
        · simpa [subgeodesicChartFunction, chartFunction, replacementCurve, hqt] using
            add_le_add (hdom q.2.re hqt (e.val.symm q.1)) (le_refl (rho q.1 : EReal))
        · simp [subgeodesicChartFunction, chartFunction, replacementCurve, hqt]

omit [CompactSpace M] in
/-- The left endpoint L¹ limit is transported from the branch that meets it. -/
theorem tendsto_left_replacementCurve
    {theta : SmoothRealForm n M 2} {curve replacement : ℝ → M → EReal}
    {u₀ u₁ : M → EReal} (h : IsSubgeodesicFrom theta curve u₀ u₁)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hr : IsSubgeodesicFrom theta replacement
      (closedSubgeodesicSlice curve u₀ u₁ a) (closedSubgeodesicSlice curve u₀ u₁ b)) :
    ManifoldL1LocallyTendsto (n := n) (replacementCurve curve replacement a b)
      (𝓝[>] (0 : ℝ)) u₀ := by
  classical
  by_cases ha0 : a = 0
  · subst a
    have hbpos : 0 < b := hab
    have htime : Tendsto (fun t : ℝ => (t - 0) / (b - 0))
        (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have ht : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
          tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
        simpa using (ht.sub_const 0).div_const (b - 0)
      · filter_upwards [self_mem_nhdsWithin] with t ht
        change 0 < (t - 0) / (b - 0)
        exact div_pos (by simpa using ht) (by simpa using hbpos)
    have hL1 := hr.tendsto_left.comp htime
    apply ManifoldL1LocallyTendsto.congr' (hu := by simpa using hL1)
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (show ∀ᶠ t in 𝓝 (0 : ℝ), t < b from isOpen_Iio.mem_nhds hbpos)]
      with t ht0 htb
    simp [replacementCurve, show t ∈ Ioo (0 : ℝ) b from ⟨ht0, htb⟩]
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    apply ManifoldL1LocallyTendsto.congr' (hu := h.tendsto_left)
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (show ∀ᶠ t in 𝓝 (0 : ℝ), t < a from isOpen_Iio.mem_nhds hapos)] with t ht
    have hnot : t ∉ Ioo a b := fun htI => (not_lt_of_ge ht.le) htI.1
    simp [replacementCurve, hnot]

omit [CompactSpace M] in
/-- The right endpoint L¹ limit is transported from the branch that meets it. -/
theorem tendsto_right_replacementCurve
    {theta : SmoothRealForm n M 2} {curve replacement : ℝ → M → EReal}
    {u₀ u₁ : M → EReal} (h : IsSubgeodesicFrom theta curve u₀ u₁)
    {a b : ℝ} (hb : b ≤ 1) (hab : a < b)
    (hr : IsSubgeodesicFrom theta replacement
      (closedSubgeodesicSlice curve u₀ u₁ a) (closedSubgeodesicSlice curve u₀ u₁ b)) :
    ManifoldL1LocallyTendsto (n := n) (replacementCurve curve replacement a b)
      (𝓝[<] (1 : ℝ)) u₁ := by
  classical
  by_cases hb1 : b = 1
  · subst b
    have hd : 0 < 1 - a := sub_pos.mpr hab
    have htime : Tendsto (fun t : ℝ => (t - a) / (1 - a))
        (𝓝[<] (1 : ℝ)) (𝓝[<] (1 : ℝ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have ht : Tendsto (fun t : ℝ => t) (𝓝[<] (1 : ℝ)) (𝓝 1) :=
          tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
        simpa [ne_of_gt hd] using (ht.sub_const a).div_const (1 - a)
      · filter_upwards [self_mem_nhdsWithin] with t ht
        have ht' : t < 1 := ht
        exact (div_lt_one hd).mpr (by linarith)
    have hL1 := hr.tendsto_right.comp htime
    apply ManifoldL1LocallyTendsto.congr' (hu := by simpa using hL1)
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (show ∀ᶠ t in 𝓝 (1 : ℝ), a < t from isOpen_Ioi.mem_nhds hab)]
      with t ht1 hta
    simp [replacementCurve, show t ∈ Ioo a (1 : ℝ) from ⟨hta, ht1⟩]
  · have hblt : b < 1 := lt_of_le_of_ne hb hb1
    apply ManifoldL1LocallyTendsto.congr' (hu := h.tendsto_right)
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (show ∀ᶠ t in 𝓝 (1 : ℝ), b < t from isOpen_Ioi.mem_nhds hblt)] with t ht
    have hnot : t ∉ Ioo a b := fun htI => (not_lt_of_ge ht.le) htI.2
    simp [replacementCurve, hnot]

/-- **Xia's gluing lemma.** Replace any nondegenerate closed subsegment by
a dominating subgeodesic with the same two closed endpoint slices. The actual
piecewise curve is a subgeodesic from the original endpoints. -/
theorem isSubgeodesicFrom_replacementCurve
    {theta : SmoothRealForm n M 2} {curve replacement : ℝ → M → EReal}
    {u₀ u₁ : M → EReal} (h : IsSubgeodesicFrom theta curve u₀ u₁)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b)
    (hr : IsSubgeodesicFrom theta replacement
      (closedSubgeodesicSlice curve u₀ u₁ a) (closedSubgeodesicSlice curve u₀ u₁ b))
    (hdom : ∀ t ∈ Ioo a b, curve t ≤ replacement ((t - a) / (b - a))) :
    IsSubgeodesicFrom theta (replacementCurve curve replacement a b) u₀ u₁ :=
  ⟨h.left_endpoint, h.right_endpoint,
    isSubgeodesicInterior_replacementCurve h ha hb hab hr hdom,
    tendsto_left_replacementCurve h ha hab hr, tendsto_right_replacementCurve h hb hab hr⟩

end

end SGPT.Foundations.Analysis.Pending.SubgeodesicGluing
