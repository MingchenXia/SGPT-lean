import SGPT.Currents.AnalyticSupportSlice
import SGPT.Foundations.Analysis.Pending.DivisorIntegrationCurrent
import SGPT.Foundations.Analysis.FirstPass.SubgeodesicChord

/-!
# The support theorem near a regular point of a hypersurface: slicing transversally

Let `u₀` be a unit vector of `V = ℂⁿ` with an orthogonal splitting `V = ℂ u₀ ⊕ ι(W)`
(`SGPT.Foundations.Analysis.Pending.DivisorRegularLocus.Splitting`), and let `Γ` be the holomorphic
graph `{k(w) u₀ + ι w}` of a function `k` over a ball of `W`.  The complex lines
`t ↦ k(w) u₀ + ι w + t u₀` (`graphBase`) meet `Γ` at `t = 0`.

* `ae_good_slices`: for a locally integrable upper semicontinuous function `u` on an open set
  `Ω ⊇` the tube, almost every line carries a locally integrable restriction of `u` which is
  finite almost everywhere.  The tube map `(w, t) ↦ (k(w) + t) u₀ + ι w` is measure preserving
  (a shear followed by the splitting isometry), and Tonelli's theorem applies.
* `exists_log_bound_on_graph`: **the transverse logarithmic decomposition**.  If `u₁ = u₂ + h`
  off a set `G` met by the tube only on `Γ`, with `u₁, u₂` plurisubharmonic and `h`
  pluriharmonic off `G`, then there is a continuous `c` on the base ball with
  `|h(k(w) u₀ + ι w + t u₀) - c(w) log |t|| ≤ C` uniformly.  On almost every line this is the
  one-variable decomposition (`exists_harmonic_of_eq_add`, `abs_sub_le_of_eq_add`); the
  coefficient `c(w) = (2π)⁻¹ ∫ h(⋯ + t u₀) Δχ(t) dt` only involves `h` on an annulus, so it is
  continuous in `w`, and the bound passes to every line by continuity.

This is the geometric part of Xia, *Foundations of pluripotential theory*,
`thm:analytic-order-zero-support`, Step 2 (regular points of codimension one), read through local
potentials instead of measure coefficients.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Laplacian ENNReal

namespace SGPT.Currents.AnalyticSupport

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DivisorRegularLocus

/-! ### Measurability of functions of upper semicontinuous functions -/

theorem measurable_indicator_comp_of_upperSemicontinuousOn {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {u : X → EReal} {U K : Set X}
    (hu : UpperSemicontinuousOn u U) (hK : MeasurableSet K) (hKU : K ⊆ U) {F : EReal → ℝ≥0∞}
    (hF : Measurable F) : Measurable (K.indicator (fun x => F (u x))) := by
  classical
  have hsc : UpperSemicontinuousOn (fun x : K => u x) univ :=
    hu.comp continuous_subtype_val.continuousOn (fun x _ => hKU x.property)
  have hm : Measurable (fun x : K => F (u x)) :=
    hF.comp (upperSemicontinuousOn_univ_iff.mp hsc).measurable
  refine measurable_of_restrict_of_restrict_compl hK ?_ ?_
  · convert hm using 1
    funext x
    simp [Set.domRestrict, x.property]
  · have hzero : Kᶜ.domRestrict (K.indicator (fun x => F (u x))) =
        fun _ : (Kᶜ : Set X) => (0 : ℝ≥0∞) := by
      funext x
      change K.indicator (fun x => F (u x)) (x : X) = 0
      exact Set.indicator_of_notMem x.property _
    rw [hzero]
    exact measurable_const

/-! ### A cut-off with Laplacian supported on an annulus -/

theorem exists_annulus_cutoff {R : ℝ} (hR : 0 < R) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ ball 0 R ∧
      (∀ t, 0 ≤ χ t) ∧ (∀ᶠ t in 𝓝 (0 : ℂ), χ t = 1) ∧
      ∀ t, Δ χ t ≠ 0 → t ∈ closedBall (0 : ℂ) R \ ball 0 (R / 4) := by
  let bump : ContDiffBump (0 : ℂ) := ⟨R / 4, R / 3, by positivity, by linarith⟩
  have hχt : tsupport (bump : ℂ → ℝ) = closedBall 0 (R / 3) := bump.tsupport_eq
  refine ⟨bump, bump.contDiff, bump.hasCompactSupport, ?_, fun t => bump.nonneg, ?_, ?_⟩
  · rw [hχt]; exact closedBall_subset_ball (by linarith)
  · filter_upwards [ball_mem_nhds (0 : ℂ) (show 0 < R / 4 by positivity)] with t ht
    exact bump.one_of_mem_closedBall (ball_subset_closedBall ht)
  · intro t ht
    refine ⟨?_, fun hin => ht ?_⟩
    · by_contra h'
      apply ht
      apply LelongPoincareOneVariable.laplacian_eq_zero_of_notMem_tsupport
      rw [hχt]
      exact fun h'' => h' (closedBall_subset_closedBall (by linarith) h'')
    · have hev : (bump : ℂ → ℝ) =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
        filter_upwards [isOpen_ball.mem_nhds hin] with s hs
        exact bump.one_of_mem_closedBall (ball_subset_closedBall hs)
      have := (InnerProductSpace.laplacian_congr_nhds hev).self_of_nhds
      rw [this]; simp

/-! ### The tube over a graph -/

section Graph

variable {n k : ℕ} {u0 : EuclideanSpace ℂ (Fin n)}
  (S : Splitting u0 (EuclideanSpace ℂ (Fin k)))

local notation "V" => EuclideanSpace ℂ (Fin n)
local notation "W" => EuclideanSpace ℂ (Fin k)

/-- The point of the graph of `kf` over `w`: `kf w • u₀ + ι w`. -/
def graphBase (kf : W → ℂ) (w : W) : V := kf w • u0 + S.ι w

theorem continuousOn_graphBase {kf : W → ℂ} {s : Set W} (hkf : ContinuousOn kf s) :
    ContinuousOn (graphBase S kf) s :=
  (hkf.smul continuousOn_const).add S.ι.continuous.continuousOn

theorem continuousOn_graphLine {kf : W → ℂ} {s : Set W} (hkf : ContinuousOn kf s) :
    ContinuousOn (fun p : W × ℂ => graphBase S kf p.1 + p.2 • u0) (s ×ˢ univ) :=
  ((continuousOn_graphBase S hkf).comp continuousOn_fst (fun p hp => hp.1)).add
    (continuous_snd.smul continuous_const).continuousOn

/-- **Almost every transverse line is a good slice.** -/
theorem ae_good_slices (hu0 : ‖u0‖ = 1) {Ω : Set V} (hΩ : IsOpen Ω) {u : V → EReal}
    (hu : UpperSemicontinuousOn u Ω)
    (hi : LocallyIntegrableOn (fun z => (u z).toReal) Ω volume)
    (hf : ∀ᵐ z ∂volume.restrict Ω, u z ≠ ⊥) {kf : W → ℂ} {w₀ : W} {δ R : ℝ}
    (hkf : ContinuousOn kf (closedBall w₀ δ))
    (hsub : ∀ w ∈ closedBall w₀ δ, ∀ t ∈ closedBall (0 : ℂ) R, graphBase S kf w + t • u0 ∈ Ω) :
    ∀ᵐ w ∂(volume : Measure W), w ∈ closedBall w₀ δ →
      LocallyIntegrableOn (fun t : ℂ => (u (graphBase S kf w + t • u0)).toReal) (ball 0 R)
        volume ∧
      ∀ᵐ t ∂volume.restrict (ball (0 : ℂ) R), u (graphBase S kf w + t • u0) ≠ ⊥ := by
  classical
  set B : Set W := closedBall w₀ δ with hBdef
  set kf' : W → ℂ := B.piecewise kf 0 with hkf'def
  have hkf'm : Measurable kf' :=
    ContinuousOn.measurable_piecewise hkf continuousOn_const isClosed_closedBall.measurableSet
  set Φ : W × ℂ → V := fun p => DivisorIntegrationCurrent.splitMap S (kf' p.1 + p.2, p.1)
    with hΦdef
  have hskew : MeasurePreserving (fun p : W × ℂ => (id p.1, kf' p.1 + p.2))
      ((volume : Measure W).prod (volume : Measure ℂ))
      ((volume : Measure W).prod (volume : Measure ℂ)) :=
    (MeasurePreserving.id volume).skew_product (g := fun w t => kf' w + t)
      ((hkf'm.comp measurable_fst).add measurable_snd)
      (Eventually.of_forall fun w => Measure.IsAddLeftInvariant.map_add_left_eq_self (kf' w))
  have hΦmp : MeasurePreserving Φ ((volume : Measure W).prod (volume : Measure ℂ)) volume :=
    (DivisorIntegrationCurrent.measurePreserving_splitMap hu0 S).comp
      (Measure.measurePreserving_swap.comp hskew)
  have hΦeq : ∀ w ∈ B, ∀ t : ℂ, Φ (w, t) = graphBase S kf w + t • u0 := by
    intro w hw t
    simp only [hΦdef, DivisorIntegrationCurrent.splitMap_apply, hkf'def, Set.piecewise_eq_of_mem _ _ _ hw,
      graphBase, add_smul]
    abel
  -- the compact tube
  set K : Set V := (fun p : W × ℂ => graphBase S kf p.1 + p.2 • u0) '' (B ×ˢ closedBall 0 R)
    with hKdef
  have hKc : IsCompact K :=
    (isCompact_closedBall w₀ δ |>.prod (isCompact_closedBall 0 R)).image_of_continuousOn
      ((continuousOn_graphLine S hkf).mono (prod_mono subset_rfl (subset_univ _)))
  have hKΩ : K ⊆ Ω := by
    rintro _ ⟨p, hp, rfl⟩
    exact hsub p.1 hp.1 p.2 hp.2
  have hKint : IntegrableOn (fun z => (u z).toReal) K volume :=
    hi.integrableOn_compact_subset hKΩ hKc
  set g : V → ℝ≥0∞ := K.indicator (fun z => ‖(u z).toReal‖ₑ) with hgdef
  have hgm : Measurable g :=
    measurable_indicator_comp_of_upperSemicontinuousOn hu hKc.measurableSet hKΩ
      measurable_ereal_toReal.enorm
  have hgint : ∫⁻ z, g z ≠ ⊤ := by
    rw [hgdef, lintegral_indicator hKc.measurableSet]
    exact hKint.2.ne
  have hcomp : ∫⁻ p, g (Φ p) ∂((volume : Measure W).prod (volume : Measure ℂ)) ≠ ⊤ := by
    rw [hΦmp.lintegral_comp hgm]; exact hgint
  rw [lintegral_prod (fun p => g (Φ p)) (hgm.comp hΦmp.measurable).aemeasurable] at hcomp
  have hfin : ∀ᵐ w ∂(volume : Measure W), ∫⁻ t, g (Φ (w, t)) < ⊤ :=
    ae_lt_top' ((hgm.comp hΦmp.measurable).lintegral_prod_right').aemeasurable hcomp
  -- the poles
  set N : Set V := {z | z ∈ Ω ∧ u z = ⊥} with hNdef
  have hN : volume N = 0 := by
    rw [ae_restrict_iff' hΩ.measurableSet] at hf
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hf] with z hz hzN
    exact hz hzN.1 hzN.2
  have hpre : ((volume : Measure W).prod (volume : Measure ℂ)) (Φ ⁻¹' N) = 0 :=
    hΦmp.quasiMeasurePreserving.preimage_null hN
  have hpoles : ∀ᵐ w ∂(volume : Measure W), ∀ᵐ t ∂(volume : Measure ℂ), Φ (w, t) ∉ N :=
    Measure.ae_ae_of_ae_prod (measure_eq_zero_iff_ae_notMem.mp hpre)
  filter_upwards [hfin, hpoles] with w hw1 hw2 hwB
  have hval : ∀ t ∈ closedBall (0 : ℂ) R, g (Φ (w, t)) = ‖(u (graphBase S kf w + t • u0)).toReal‖ₑ := by
    intro t ht
    rw [hΦeq w hwB t, hgdef,
      indicator_of_mem (show graphBase S kf w + t • u0 ∈ K from ⟨(w, t), ⟨hwB, ht⟩, rfl⟩)]
  refine ⟨?_, ?_⟩
  · apply IntegrableOn.locallyIntegrableOn
    refine ⟨?_, ?_⟩
    · have husc : UpperSemicontinuousOn (fun t : ℂ => u (graphBase S kf w + t • u0))
          (ball 0 R) := by
        apply hu.comp ((continuous_const.add (continuous_id.smul continuous_const)).continuousOn)
        intro t ht
        exact hsub w hwB t (ball_subset_closedBall ht)
      exact (measurable_ereal_toReal.comp_aemeasurable
        (FirstPass.UpperSemicontinuousOn.aemeasurable_restrict_of_isOpen husc isOpen_ball)).aestronglyMeasurable
    · change ∫⁻ t in ball (0 : ℂ) R, ‖(u (graphBase S kf w + t • u0)).toReal‖ₑ < ⊤
      calc ∫⁻ t in ball (0 : ℂ) R, ‖(u (graphBase S kf w + t • u0)).toReal‖ₑ
          = ∫⁻ t in ball (0 : ℂ) R, g (Φ (w, t)) := by
            apply setLIntegral_congr_fun measurableSet_ball
            intro t ht
            exact (hval t (ball_subset_closedBall ht)).symm
        _ ≤ ∫⁻ t, g (Φ (w, t)) := setLIntegral_le_lintegral _ _
        _ < ⊤ := hw1
  · filter_upwards [ae_restrict_of_ae hw2, ae_restrict_mem measurableSet_ball] with t ht htB
    have h1 := hΦeq w hwB t
    rw [h1] at ht
    intro hbot
    exact ht ⟨hsub w hwB t (ball_subset_closedBall htB), hbot⟩

/-- **The transverse logarithmic decomposition.**  Let `u₁ = u₂ + h` off `G`, with `u₁, u₂`
plurisubharmonic and locally integrable on `Ω`, and `h` continuous and pluriharmonic on the open
set `Ω \ G`.  Suppose the tube `graphBase kf w + t u₀` (`w ∈ closedBall w₀ δ`, `|t| ≤ R`) lies in
`Ω` and meets `G` only at `t = 0`.  Then there is a continuous `c` with
`|h(graphBase kf w + t u₀) - c(w) log |t|| ≤ C` for `w ∈ ball w₀ δ`, `0 < |t| ≤ R / 2`. -/
theorem exists_log_bound_on_graph (hu0 : ‖u0‖ = 1) {Ω : Set V} (hΩ : IsOpen Ω)
    {u₁ u₂ : V → EReal} (hu₁ : PlurisubharmonicOn u₁ Ω) (hu₂ : PlurisubharmonicOn u₂ Ω)
    (hi₁ : LocallyIntegrableOn (fun z => (u₁ z).toReal) Ω volume)
    (hi₂ : LocallyIntegrableOn (fun z => (u₂ z).toReal) Ω volume)
    (hf₁ : ∀ᵐ z ∂volume.restrict Ω, u₁ z ≠ ⊥) (hf₂ : ∀ᵐ z ∂volume.restrict Ω, u₂ z ≠ ⊥)
    {G : Set V} (hG : IsOpen (Ω \ G)) {h : V → ℝ} (hhc : ContinuousOn h (Ω \ G))
    (hhp : PlurisubharmonicOn (fun z => (h z : EReal)) (Ω \ G))
    (hhn : PlurisubharmonicOn (fun z => ((-h z : ℝ) : EReal)) (Ω \ G))
    (heq : ∀ z ∈ Ω \ G, u₁ z = u₂ z + (h z : EReal))
    {kf : W → ℂ} {w₀ : W} {δ R : ℝ} (hR : 0 < R)
    (hkf : ContinuousOn kf (closedBall w₀ δ))
    (hsub : ∀ w ∈ closedBall w₀ δ, ∀ t ∈ closedBall (0 : ℂ) R, graphBase S kf w + t • u0 ∈ Ω)
    (hoff : ∀ w ∈ closedBall w₀ δ, ∀ t ∈ closedBall (0 : ℂ) R, t ≠ 0 →
      graphBase S kf w + t • u0 ∉ G) :
    ∃ c : W → ℝ, ContinuousOn c (closedBall w₀ δ) ∧ ∃ C : ℝ, ∀ w ∈ ball w₀ δ, ∀ t : ℂ,
      t ≠ 0 → ‖t‖ ≤ R / 2 → |h (graphBase S kf w + t • u0) - c w * Real.log ‖t‖| ≤ C := by
  classical
  obtain ⟨χ, hχs, hχc, hχsub, hχ0, hχ1, hAnn⟩ := exists_annulus_cutoff hR
  set Ann : Set ℂ := closedBall 0 R \ ball 0 (R / 4) with hAnndef
  have hAnn0 : ∀ t ∈ Ann, t ≠ 0 := by
    intro t ht h0; apply ht.2; rw [h0]; exact mem_ball_self (by positivity)
  have hLgood : ∀ w ∈ closedBall w₀ δ, ∀ t ∈ Ann, graphBase S kf w + t • u0 ∈ Ω \ G :=
    fun w hw t ht => ⟨hsub w hw t ht.1, hoff w hw t ht.1 (hAnn0 t ht)⟩
  -- a bound for `h` on the tube over the annulus
  have hQc : IsCompact (closedBall w₀ δ ×ˢ Ann) :=
    (isCompact_closedBall w₀ δ).prod ((isCompact_closedBall 0 R).diff isOpen_ball)
  have hhQ : ContinuousOn (fun p : W × ℂ => h (graphBase S kf p.1 + p.2 • u0))
      (closedBall w₀ δ ×ˢ Ann) :=
    hhc.comp ((continuousOn_graphLine S hkf).mono (prod_mono subset_rfl (subset_univ _)))
      (fun p hp => hLgood p.1 hp.1 p.2 hp.2)
  obtain ⟨M, hM⟩ := hQc.exists_bound_of_continuousOn hhQ
  -- the coefficient
  obtain ⟨c, hcdef⟩ : ∃ c : W → ℝ,
      c = fun w => sliceCoeff (fun t => h (graphBase S kf w + t • u0)) χ := ⟨_, rfl⟩
  have hΔc := LelongPoincareOneVariable.continuous_laplacian hχs
  have hcc : ContinuousOn c (closedBall w₀ δ) := by
    have hint : ContinuousOn (fun w => ∫ t, h (graphBase S kf w + t • u0) * Δ χ t)
        (closedBall w₀ δ) := by
      refine continuousOn_of_dominated
        (F := fun w t => h (graphBase S kf w + t • u0) * Δ χ t)
        (bound := fun t => M * ‖Δ χ t‖) ?_ ?_ ?_ ?_
      · intro w hw
        apply Continuous.aestronglyMeasurable
        rw [continuous_iff_continuousAt]
        intro t
        by_cases ht : t ∈ Ann
        · have hLt := hLgood w hw t ht
          have hc1 : ContinuousAt h (graphBase S kf w + t • u0) :=
            hhc.continuousAt (hG.mem_nhds hLt)
          have hc2 : ContinuousAt (fun t : ℂ => graphBase S kf w + t • u0) t :=
            (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
          have hc3 : ContinuousAt (fun t : ℂ => h (graphBase S kf w + t • u0)) t :=
            ContinuousAt.comp (f := fun t : ℂ => graphBase S kf w + t • u0) hc1 hc2
          exact hc3.mul hΔc.continuousAt
        · have hzero : ∀ s ∉ Ann, Δ χ s = 0 := fun s hs => by
            by_contra h'; exact hs (hAnn s h')
          have hcl : IsClosed Ann := isClosed_closedBall.sdiff isOpen_ball
          have hev : (fun t => h (graphBase S kf w + t • u0) * Δ χ t) =ᶠ[𝓝 t] fun _ => 0 := by
            filter_upwards [hcl.isOpen_compl.mem_nhds ht] with s hs
            rw [hzero s hs, mul_zero]
          exact continuousAt_const.congr hev.symm
      · intro w hw
        refine Eventually.of_forall fun t => ?_
        rw [norm_mul]
        by_cases ht : Δ χ t = 0
        · rw [ht]; simp only [norm_zero, mul_zero, le_refl]
        · have := hM (w, t) ⟨hw, hAnn t ht⟩
          exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
      · exact (hΔc.norm.integrable_of_hasCompactSupport
          (LelongPoincareOneVariable.hasCompactSupport_laplacian hχc).norm).const_mul M
      · refine Eventually.of_forall fun t => ?_
        by_cases ht : Δ χ t = 0
        · simp only [ht, mul_zero]; exact continuousOn_const
        · have hA := hAnn t ht
          refine ContinuousOn.mul ?_ continuousOn_const
          exact hhc.comp ((continuousOn_graphBase S hkf).add continuousOn_const)
            (fun w hw => hLgood w hw t hA)
    rw [hcdef]
    simp only [sliceCoeff]
    exact continuousOn_const.mul hint
  -- a bound for `c`
  obtain ⟨Mc, hMc⟩ := (isCompact_closedBall w₀ δ).exists_bound_of_continuousOn hcc
  set C₀ : ℝ := M + Mc * |Real.log (R / 2)| with hC₀def
  -- good slices
  have hg₁ := ae_good_slices S hu0 hΩ hu₁.upperSemicontinuousOn hi₁ hf₁ hkf hsub
  have hg₂ := ae_good_slices S hu0 hΩ hu₂.upperSemicontinuousOn hi₂ hf₂ hkf hsub
  have hgood : ∀ᵐ w ∂(volume : Measure W), w ∈ closedBall w₀ δ → ∀ t : ℂ, t ≠ 0 →
      ‖t‖ ≤ R / 2 → |h (graphBase S kf w + t • u0) - c w * Real.log ‖t‖| ≤ C₀ := by
    filter_upwards [hg₁, hg₂] with w hw₁ hw₂ hw
    obtain ⟨hl₁, hb₁⟩ := hw₁ hw
    obtain ⟨hl₂, hb₂⟩ := hw₂ hw
    have hballsub : ∀ t ∈ ball (0 : ℂ) R, graphBase S kf w + t • u0 ∈ Ω := fun t ht =>
      hsub w hw t (ball_subset_closedBall ht)
    have hpunct : ∀ t ∈ ball (0 : ℂ) R \ {0}, graphBase S kf w + t • u0 ∈ Ω \ G := fun t ht =>
      ⟨hballsub t ht.1, hoff w hw t (ball_subset_closedBall ht.1) ht.2⟩
    have hpsh : ∀ {u : V → EReal}, PlurisubharmonicOn u Ω →
        PlurisubharmonicOn (fun t : ℂ => u (graphBase S kf w + t • u0)) (ball 0 R) := by
      intro u hu
      have := hu.comp_affine (ContinuousLinearMap.toSpanSingleton ℂ u0) (graphBase S kf w)
      simp only [ContinuousLinearMap.toSpanSingleton_apply] at this
      exact this.mono (fun t ht => hballsub t ht)
    have hpshG : ∀ {u : V → EReal}, PlurisubharmonicOn u (Ω \ G) →
        PlurisubharmonicOn (fun t : ℂ => u (graphBase S kf w + t • u0)) (ball 0 R \ {0}) := by
      intro u hu
      have := hu.comp_affine (ContinuousLinearMap.toSpanSingleton ℂ u0) (graphBase S kf w)
      simp only [ContinuousLinearMap.toSpanSingleton_apply] at this
      exact this.mono (fun t ht => hpunct t ht)
    have hψc : ContinuousOn (fun t : ℂ => h (graphBase S kf w + t • u0)) (ball 0 R \ {0}) :=
      hhc.comp ((continuous_const.add (continuous_id.smul continuous_const)).continuousOn)
        hpunct
    have hC : ∀ t ∈ sphere (0 : ℂ) (R / 2), |h (graphBase S kf w + t • u0) -
        sliceCoeff (fun t => h (graphBase S kf w + t • u0)) χ * Real.log ‖t‖| ≤ C₀ := by
      intro t ht
      have hts : ‖t‖ = R / 2 := by simpa using ht
      have htA : t ∈ Ann :=
        ⟨by rw [mem_closedBall_zero_iff]; linarith, by rw [mem_ball_zero_iff]; linarith⟩
      have h1 := hM (w, t) ⟨hw, htA⟩
      have h2 := hMc w hw
      rw [Real.norm_eq_abs] at h1 h2
      rw [show sliceCoeff (fun t => h (graphBase S kf w + t • u0)) χ = c w by rw [hcdef]]
      calc |h (graphBase S kf w + t • u0) - c w * Real.log ‖t‖|
          ≤ |h (graphBase S kf w + t • u0)| + |c w * Real.log ‖t‖| := abs_sub _ _
        _ = |h (graphBase S kf w + t • u0)| + |c w| * |Real.log (R / 2)| := by
            rw [abs_mul, hts]
        _ ≤ M + Mc * |Real.log (R / 2)| := by gcongr
    have hbd := abs_sub_le_of_eq_add (hpsh hu₁) (hpsh hu₂) hl₁ hl₂ hb₁ hb₂ hψc (hpshG hhp)
      (hpshG hhn) (fun t ht => heq _ (hpunct t ht)) hχs hχc hχsub hχ0 hχ1
      (by positivity : (0 : ℝ) < R / 2) (by linarith) hC
    intro t ht0 htR
    have := hbd t (mem_closedBall_zero_iff.mpr htR) ht0
    rwa [show sliceCoeff (fun t => h (graphBase S kf w + t • u0)) χ = c w by rw [hcdef]] at this
  refine ⟨c, hcc, C₀, fun w hw t ht0 htR => ?_⟩
  by_contra hcon
  push Not at hcon
  set g : W → ℝ := fun w' => |h (graphBase S kf w' + t • u0) - c w' * Real.log ‖t‖| with hgdef
  have htB : t ∈ closedBall (0 : ℂ) R := mem_closedBall_zero_iff.mpr (by linarith)
  have hgc : ContinuousOn g (ball w₀ δ) := by
    have h1 : ContinuousOn (fun w' => h (graphBase S kf w' + t • u0)) (closedBall w₀ δ) :=
      hhc.comp ((continuousOn_graphBase S hkf).add continuousOn_const)
        (fun w' hw' => ⟨hsub w' hw' t htB, hoff w' hw' t htB ht0⟩)
    exact ((h1.sub (hcc.mul continuousOn_const)).abs).mono ball_subset_closedBall
  set U : Set W := ball w₀ δ ∩ g ⁻¹' Ioi C₀ with hUdef
  have hUo : IsOpen U := hgc.isOpen_inter_preimage isOpen_ball isOpen_Ioi
  have hwU : w ∈ U := ⟨hw, hcon⟩
  have hUpos : 0 < volume U := hUo.measure_pos volume ⟨w, hwU⟩
  have hU0 : volume U = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hgood] with w' hw' hw'U
    exact absurd (hw' (ball_subset_closedBall hw'U.1) t ht0 htR) (not_le.mpr hw'U.2)
  exact hUpos.ne' hU0

end Graph

end SGPT.Currents.AnalyticSupport
