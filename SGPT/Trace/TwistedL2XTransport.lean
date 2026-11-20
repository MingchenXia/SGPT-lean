import SGPT.Trace.TwistedL2XChart

/-!
# Transport of local pieces between charts and frames

Blueprint `claude-tl2-man.tex` (lane TL2-MAN, `claude-tl2-man:transport`).  A local piece is a
smooth coefficient vector field `h` with compact support in `c₀(c₀.source ∩ base e₀)`, written in
the chart `c₀` and the frame `e₀` of `L`.  Its coefficient field in another chart-frame `(c, e)` is

`transpX c₀ e₀ c e h (z) = t_{e₀ e}(x) · D(c ∘ c₀⁻¹)(c₀ x) h(c₀ x)`,  `x = c⁻¹ z`,

(zero where `x` is outside `c₀.source ∩ base e₀`).  The relation `IsTransp c e c' e' u u' z`
(`u' ∘ (c' ∘ c⁻¹) = t_{e e'} · D(c' ∘ c⁻¹) u` near `z`) is the transformation law of coefficient
fields of `L`-valued `(1,0)`-vector fields.  Main results:

* `contDiffOn_transpX`: the transported field is smooth on the chart-frame domain of `(c, e)`;
* `transpX_self`: transport into the piece's own chart-frame is the identity;
* `isTransp_transpX`: transports into two chart-frames are related by `IsTransp` (cocycle rule,
  chain rule for coordinate changes);
* `isTransp_finset_sum`: `IsTransp` is additive.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory
open scoped Topology ContDiff ComplexConjugate Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle TwistedDatum

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] (L : HermitianHolomorphicLineBundle.{0, 0} n X)

open Classical in
/-- The coefficient field, in the chart-frame `(c, e)`, of the local piece `h` written in the
chart-frame `(c₀, e₀)`. -/
def transpX (c₀ : ComplexChart n X) (e₀ : AtlasFrame L) (c : ComplexChart n X) (e : AtlasFrame L)
    (h : ComplexModel n → ComplexModel n) (z : ComplexModel n) : ComplexModel n :=
  if z ∈ ovl c c₀ ∧ c.val.symm z ∈ e₀.val.baseSet then
    frameTrans L e₀ e (c.val.symm z) • fderiv ℂ (chg c₀ c) (chg c c₀ z) (h (chg c c₀ z))
  else 0

/-- `u'` (in `(c', e')`) is the transport of `u` (in `(c, e)`) near `z`. -/
def IsTransp (c : ComplexChart n X) (e : AtlasFrame L) (c' : ComplexChart n X)
    (e' : AtlasFrame L) (u u' : ComplexModel n → ComplexModel n) (z : ComplexModel n) : Prop :=
  (fun y => u' (chg c c' y)) =ᶠ[𝓝 z]
    fun y => frameTrans L e e' (c.val.symm y) • fderiv ℂ (chg c c') y (u y)

variable {L}

theorem isTransp_finset_sum {c c' : ComplexChart n X} {e e' : AtlasFrame L} {ι : Type*}
    (s : Finset ι) {u u' : ι → ComplexModel n → ComplexModel n} {z : ComplexModel n}
    (h : ∀ i ∈ s, IsTransp L c e c' e' (u i) (u' i) z) :
    IsTransp L c e c' e' (fun y => ∑ i ∈ s, u i y) (fun y => ∑ i ∈ s, u' i y) z := by
  have hall : ∀ᶠ y in 𝓝 z, ∀ i ∈ s, u' i (chg c c' y) =
      frameTrans L e e' (c.val.symm y) • fderiv ℂ (chg c c') y (u i y) :=
    (s.eventually_all).mpr fun i hi => h i hi
  filter_upwards [hall] with y hy
  rw [map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl hy

theorem isTransp_congr {c c' : ComplexChart n X} {e e' : AtlasFrame L}
    {u u' v v' : ComplexModel n → ComplexModel n} {z : ComplexModel n}
    (h : IsTransp L c e c' e' u u' z) (hu : u =ᶠ[𝓝 z] v) (hu' : u' =ᶠ[𝓝 (chg c c' z)] v')
    (hz : z ∈ ovl c c') : IsTransp L c e c' e' v v' z := by
  have hcont : ContinuousAt (chg c c') z := (differentiableAt_chg hz).continuousAt
  have hu'' : (fun y => u' (chg c c' y)) =ᶠ[𝓝 z] fun y => v' (chg c c' y) := hcont.eventually hu'
  filter_upwards [h, hu, hu''] with y hy h1 h2
  rw [← h2, hy, h1]

/-! ### Basic properties of the transport -/

section Basic

variable {c₀ c : ComplexChart n X} {e₀ e : AtlasFrame L} {h : ComplexModel n → ComplexModel n}

theorem transpX_of_mem {z : ComplexModel n} (hz : z ∈ ovl c c₀)
    (hzb : c.val.symm z ∈ e₀.val.baseSet) :
    transpX L c₀ e₀ c e h z =
      frameTrans L e₀ e (c.val.symm z) • fderiv ℂ (chg c₀ c) (chg c c₀ z) (h (chg c c₀ z)) := by
  classical
  rw [transpX, if_pos ⟨hz, hzb⟩]

/-- The transport of a piece into its own chart-frame is the piece. -/
theorem transpX_self (hts : tsupport h ⊆ chartFrameDomain L c₀ e₀) :
    transpX L c₀ e₀ c₀ e₀ h = h := by
  classical
  funext z
  by_cases hz : z ∈ ovl c₀ c₀ ∧ c₀.val.symm z ∈ e₀.val.baseSet
  · rw [transpX, if_pos hz, frameTrans_self e₀ hz.2]
    have hzt : chg c₀ c₀ z = z := c₀.val.right_inv hz.1.1
    rw [hzt, fderiv_chg_self hz.1.1, one_smul]
    rfl
  · rw [transpX, if_neg hz]
    refine (image_eq_zero_of_notMem_tsupport fun h' => hz ?_).symm
    have := hts h'
    exact ⟨mem_ovl_self this.1, this.2⟩

theorem isClosed_pieceSupport (hc : HasCompactSupport h) (ht : tsupport h ⊆ c₀.val.target) :
    IsClosed (pieceSupport c₀ h) := by
  rw [pieceSupport, ← c₀.val.symm_image_eq_source_inter_preimage ht]
  exact (hc.isCompact.image_of_continuousOn (c₀.val.continuousOn_symm.mono ht)).isClosed

/-- Away from the support of the piece the transport vanishes near the point. -/
theorem transpX_eventuallyEq_zero (hc : HasCompactSupport h) (ht : tsupport h ⊆ c₀.val.target)
    {z : ComplexModel n} (hz : z ∈ c.val.target) (hx : c.val.symm z ∉ pieceSupport c₀ h) :
    transpX L c₀ e₀ c e h =ᶠ[𝓝 z] 0 := by
  classical
  have hO : IsOpen (c.val.target ∩ c.val.symm ⁻¹' (pieceSupport c₀ h)ᶜ) :=
    c.val.continuousOn_symm.isOpen_inter_preimage c.val.open_target
      (isClosed_pieceSupport hc ht).isOpen_compl
  filter_upwards [hO.mem_nhds ⟨hz, hx⟩] with y hy
  by_cases hc' : y ∈ ovl c c₀ ∧ c.val.symm y ∈ e₀.val.baseSet
  · rw [transpX, if_pos hc']
    have h0 : h (chg c c₀ y) = 0 := by
      refine image_eq_zero_of_notMem_tsupport fun h' => hy.2 ⟨hc'.1.2, h'⟩
    rw [h0, map_zero, smul_zero]
    rfl
  · rw [transpX, if_neg hc']
    rfl

theorem mem_of_mem_pieceSupport (ht : tsupport h ⊆ chartFrameDomain L c₀ e₀) {x : X}
    (hx : x ∈ pieceSupport c₀ h) : x ∈ c₀.val.source ∩ e₀.val.baseSet := by
  have := (ht hx.2).2
  simp only [mem_preimage, c₀.val.left_inv hx.1] at this
  exact ⟨hx.1, this⟩

/-- The formula for the transport near a point of the support. -/
theorem transpX_eventuallyEq_formula {z : ComplexModel n} (hz : z ∈ ovl c c₀)
    (hzb : c.val.symm z ∈ e₀.val.baseSet) :
    transpX L c₀ e₀ c e h =ᶠ[𝓝 z] fun y => frameTrans L e₀ e (c.val.symm y) •
      fderiv ℂ (chg c₀ c) (chg c c₀ y) (h (chg c c₀ y)) := by
  have hO : IsOpen (ovl c c₀ ∩ c.val.symm ⁻¹' e₀.val.baseSet) :=
    (c.val.continuousOn_symm.mono fun _ hy => hy.1).isOpen_inter_preimage
      (isOpen_ovl c c₀) e₀.val.open_baseSet
  filter_upwards [hO.mem_nhds ⟨hz, hzb⟩] with y hy
  exact transpX_of_mem hy.1 hy.2

end Basic

/-! ### Smoothness -/

theorem fderiv_apply_eq_sum (A : ComplexModel n →L[ℂ] ComplexModel n) (u : ComplexModel n) :
    A u = ∑ m, u m • A (coordVec m) := by
  conv_lhs => rw [← eq_sum_coordVec u]
  rw [map_sum]
  exact Finset.sum_congr rfl fun m _ => map_smul _ _ _

theorem differentiableOn_fderiv_chg_comp (c₀ c : ComplexChart n X) (v : ComplexModel n) :
    DifferentiableOn ℂ (fun y => fderiv ℂ (chg c₀ c) (chg c c₀ y) v) (ovl c c₀) := by
  have h1 : DifferentiableOn ℂ (fun w => fderiv ℂ (chg c₀ c) w v) (ovl c₀ c) :=
    differentiableOn_fderiv_apply_of_isOpen (differentiableOn_chg c₀ c) (isOpen_ovl c₀ c) v
  exact h1.comp (differentiableOn_chg c c₀) fun y hy => chg_mem_ovl hy

theorem contDiffOn_transpX {c₀ c : ComplexChart n X} {e₀ e : AtlasFrame L}
    {h : ComplexModel n → ComplexModel n} (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (ht : tsupport h ⊆ chartFrameDomain L c₀ e₀) :
    ContDiffOn ℝ ∞ (transpX L c₀ e₀ c e h) (chartFrameDomain L c e) := by
  have ht' : tsupport h ⊆ c₀.val.target := ht.trans fun _ hz => hz.1
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  by_cases hx : c.val.symm z ∈ pieceSupport c₀ h
  · have hx' := mem_of_mem_pieceSupport ht hx
    have hzo : z ∈ ovl c c₀ := ⟨hz.1, hx'.1⟩
    set S : Set (ComplexModel n) :=
      ovl c c₀ ∩ c.val.symm ⁻¹' (e₀.val.baseSet ∩ e.val.baseSet) with hS
    have hSo : IsOpen S :=
      (c.val.continuousOn_symm.mono fun _ hy => hy.1).isOpen_inter_preimage
        (isOpen_ovl c c₀) (e₀.val.open_baseSet.inter e.val.open_baseSet)
    have hzS : z ∈ S := ⟨hzo, hx'.2, hz.2⟩
    -- the frame transition
    have htr : ContDiffOn ℝ ∞ (fun y => frameTrans L e₀ e (c.val.symm y)) S := by
      refine contDiffOn_real_of_differentiableOn_complex ?_ hSo
      exact (differentiableOn_frameTrans c e₀ e).mono fun y hy => ⟨hy.1.1, hy.2⟩
    have hchg : ContDiffOn ℝ ∞ (chg c c₀) S :=
      (contDiffOn_real_of_differentiableOn_complex (differentiableOn_chg c c₀)
        (isOpen_ovl c c₀)).mono fun y hy => hy.1
    have hhc : ContDiffOn ℝ ∞ (fun y => h (chg c c₀ y)) S := hh.comp_contDiffOn hchg
    have hD : ∀ m, ContDiffOn ℝ ∞ (fun y => fderiv ℂ (chg c₀ c) (chg c c₀ y) (coordVec m)) S :=
      fun m => (contDiffOn_real_of_differentiableOn_complex
        (differentiableOn_fderiv_chg_comp c₀ c (coordVec m)) (isOpen_ovl c c₀)).mono
          fun y hy => hy.1
    have hF : ContDiffOn ℝ ∞ (fun y => frameTrans L e₀ e (c.val.symm y) •
        ∑ m, h (chg c c₀ y) m • fderiv ℂ (chg c₀ c) (chg c c₀ y) (coordVec m)) S := by
      refine htr.smul (ContDiffOn.sum fun m _ => ?_)
      exact (contDiffOn_coord hhc m).smul (hD m)
    refine (hF.contDiffAt (hSo.mem_nhds hzS)).congr_of_eventuallyEq ?_
    filter_upwards [transpX_eventuallyEq_formula (L := L) (e := e) (h := h) hzo hx'.2]
      with y hy
    rw [hy, fderiv_apply_eq_sum]
  · exact contDiffAt_const.congr_of_eventuallyEq
      (transpX_eventuallyEq_zero (e₀ := e₀) (e := e) hc ht' hz.1 hx)

/-! ### The transformation law -/

/-- **Transports into two chart-frames are related by the transformation law.** -/
theorem isTransp_transpX {c₀ c c' : ComplexChart n X} {e₀ e e' : AtlasFrame L}
    {h : ComplexModel n → ComplexModel n} (hc : HasCompactSupport h)
    (ht : tsupport h ⊆ chartFrameDomain L c₀ e₀) {z : ComplexModel n}
    (hz : z ∈ chartFrameDomain L c e) (hz' : c.val.symm z ∈ c'.val.source ∩ e'.val.baseSet) :
    IsTransp L c e c' e' (transpX L c₀ e₀ c e h) (transpX L c₀ e₀ c' e' h) z := by
  have ht' : tsupport h ⊆ c₀.val.target := ht.trans fun _ hz => hz.1
  have hzc' : z ∈ ovl c c' := ⟨hz.1, hz'.1⟩
  by_cases hx : c.val.symm z ∈ pieceSupport c₀ h
  · have hx' := mem_of_mem_pieceSupport ht hx
    have hzo : z ∈ ovl c c₀ := ⟨hz.1, hx'.1⟩
    set S : Set (ComplexModel n) := ovl c c₀ ∩ ovl c c' ∩
      c.val.symm ⁻¹' (e₀.val.baseSet ∩ e.val.baseSet ∩ e'.val.baseSet) with hS
    have hSo : IsOpen S :=
      (c.val.continuousOn_symm.mono fun _ hy => hy.1.1).isOpen_inter_preimage
        ((isOpen_ovl c c₀).inter (isOpen_ovl c c'))
        ((e₀.val.open_baseSet.inter e.val.open_baseSet).inter e'.val.open_baseSet)
    filter_upwards [hSo.mem_nhds ⟨⟨hzo, hzc'⟩, ⟨hx'.2, hz.2⟩, hz'.2⟩] with y hy
    obtain ⟨⟨hy0, hy'⟩, ⟨hb0, hb⟩, hb'⟩ := hy
    have hsymm : c'.val.symm (chg c c' y) = c.val.symm y := symm_chg hy'
    have hy1 : chg c c' y ∈ ovl c' c₀ := ⟨c'.val.map_source hy'.2, by
      simp only [mem_preimage]; rw [hsymm]; exact hy0.2⟩
    have hcomp : chg c' c₀ (chg c c' y) = chg c c₀ y := by
      simp only [chg] at hsymm ⊢; rw [hsymm]
    rw [transpX_of_mem hy1 (by rw [hsymm]; exact hb0), transpX_of_mem hy0 hb0, hsymm, hcomp]
    -- chain rule and frame cocycle
    have hw : chg c c₀ y ∈ ovl c₀ c := chg_mem_ovl hy0
    have hw' : c₀.val.symm (chg c c₀ y) ∈ c'.val.source := by rw [symm_chg hy0]; exact hy'.2
    have hchain := fderiv_chg_comp hw hw'
    rw [chg_chg hy0] at hchain
    rw [hchain, map_smul, smul_smul, ContinuousLinearMap.comp_apply,
      frameTrans_mul e₀ e e' hb0 hb hb', mul_comm (frameTrans L e₀ e _)]
  · have hzero : transpX L c₀ e₀ c e h =ᶠ[𝓝 z] 0 :=
      transpX_eventuallyEq_zero hc ht' hz.1 hx
    have hzero' : transpX L c₀ e₀ c' e' h =ᶠ[𝓝 (chg c c' z)] 0 := by
      refine transpX_eventuallyEq_zero hc ht' (c'.val.map_source hz'.1) ?_
      rw [symm_chg hzc']; exact hx
    have hcont : ContinuousAt (chg c c') z := (differentiableAt_chg hzc').continuousAt
    filter_upwards [hzero, hcont.eventually hzero'] with y hy hy'
    simp only [Pi.zero_apply] at hy hy'
    rw [hy', hy, map_zero, smul_zero]

/-- A piece is the transport of its own transport into another chart-frame. -/
theorem isTransp_piece {c₀ c : ComplexChart n X} {e₀ e : AtlasFrame L}
    {h : ComplexModel n → ComplexModel n} (hc : HasCompactSupport h)
    (ht : tsupport h ⊆ chartFrameDomain L c₀ e₀) {z : ComplexModel n}
    (hz : z ∈ chartFrameDomain L c e) (hz' : c.val.symm z ∈ c₀.val.source ∩ e₀.val.baseSet) :
    IsTransp L c e c₀ e₀ (transpX L c₀ e₀ c e h) h z := by
  have := isTransp_transpX (e' := e₀) hc ht hz hz'
  rwa [transpX_self ht] at this

end SGPT.Trace.TwistedL2
