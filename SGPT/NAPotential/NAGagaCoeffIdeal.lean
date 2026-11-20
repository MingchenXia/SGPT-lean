import SGPT.NAPotential.NAGagaWeights

/-!
# The complexification `Ψ` and the coefficient ideals of `𝓘(kΨ)`

Source: `chapter_NApotential.tex`, `prop:psiandPhi`, with `lma:istab` and `eq:ImPhiexp`.
Blueprint `claude-na-gaga.tex`, nodes `claude-na-gaga:complexification`,
`claude-na-gaga:coeff`.

For a test curve `Γ` with `Γ_max ≤ 0` its complexification is the function on `X × Δ`

`Ψ(x, δ) = sup_{τ < Γ_max} (Γ_τ(x) - τ log|δ|²) = Γ^*_{-log|δ|²}(x)`,   `δ ≠ 0`

(`complexification`; the source extends it across `X × {0}` by `thm:GRexten`; the multiplier
ideals below do not see the null set `X × {0}`, so every extension is allowed:
`IsComplexificationOf`). `Ψ` is invariant under `δ ↦ e^{iθ}δ`, so (`lma:istab`) the multiplier
ideal `𝓘(kΨ)` at the points of `X × {0}` is `∑_i 𝔞_{k,i} δ^i` with the *coefficient ideals*

`𝔞_{k,i} = {g : g(x) δ^i ∈ 𝓘(kΨ)_{(x,0)}}`   (`coeffIdeal`),

the ideals `𝔞_i` of `eq:ImPhiexp`. The three inclusions proved here identify them with the
multiplier ideals of the slices, up to a shift of the parameter:

* `coeffIdeal_of_multiplierIdeal`: `𝓘(kΓ_τ) ⊆ 𝔞_{k,i}` when `i + kτ > -1`;
* `multiplierIdeal_of_coeffIdeal`: `𝔞_{k,i} ⊆ 𝓘(kΓ_{-(i+1)/k})` when `-(i+1)/k < Γ_max`;
* `eventuallyEq_zero_of_coeffIdeal`: `𝔞_{k,i} = 0` when `i + 1 + kΓ_max ≤ 0`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.NAGaga

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.PSH.VariableComplexAtlas
open ProductComplexManifold
open scoped ProductComplexManifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- **The complexification** `Ψ(x, δ) = Γ^*_{-log|δ|²}(x)` of the Legendre transform `Γ^*` of a
test curve (`def:subgeoray` in the coordinate `t = -log|δ|²`; at `δ = 0` the formula gives the
irrelevant value `Γ^*_0(x)`). -/
def complexification (Γ : SourceTestCurvePredata θ) (p : M × unitDisc) : EReal :=
  sourceTestCurveRawLegendre Γ (-Real.log (‖p.2.val‖ ^ 2)) p.1

/-- `Ψ` is the complexification of `Γ^*` on `X × Δ^*` (any value on `X × {0}`). -/
def IsComplexificationOf (Γ : SourceTestCurvePredata θ) (Ψ : M × unitDisc → EReal) : Prop :=
  ∀ p : M × unitDisc, p.2.val ≠ 0 → Ψ p = complexification Γ p

theorem isComplexificationOf_complexification (Γ : SourceTestCurvePredata θ) :
    IsComplexificationOf Γ (complexification Γ) := fun _ _ => rfl

/-- **The coefficient ideals** `𝔞_{k,i} = {g : g(x) δ^i ∈ 𝓘(kΨ)_{(x,0)}}` of the multiplier ideal
of `kΨ` along `X × {0}` (the ideals of `eq:ImPhiexp`). -/
def coeffIdeal (Ψ : M × unitDisc → EReal) (k i : ℕ) : GermIdeal n M where
  mem x g := HolomorphicAt n g x ∧
    (multiplierIdeal (n := n + 1) (k : ℝ) Ψ).mem (x, discOrigin)
      (fun p => g p.1 * discCoord p.2 ^ i)

/-! ### Chart computations -/

omit [IsComplexManifold n M] in
theorem coord_pow_eval (g : M → ℂ) (i : ℕ) (x : M) (z : ComplexModel n) {w : ComplexModel 1}
    (hw : w ∈ (unitDisc : Set (ComplexModel 1))) :
    (fun p : M × unitDisc => g p.1 * discCoord p.2 ^ i)
        ((chartAt (ComplexModel (n + 1)) (x, discOrigin)).symm (prodL n (z, w))) =
      g ((chartAt (ComplexModel n) x).symm z) * w 0 ^ i := by
  rw [prodChartAt_symm_apply (x, discOrigin) z hw]
  rfl

theorem norm_sq_coord_pow (a : ℂ) (w : ComplexModel 1) (i : ℕ) :
    ‖a * w 0 ^ i‖ ^ 2 = ‖a‖ ^ 2 * ‖w‖ ^ (2 * i) := by
  rw [norm_mul, norm_pow, norm_apply_zero, mul_pow, ← pow_mul, mul_comm i 2]

/-- The density of `|g δ^i|² e^{-kΨ}` at `L(z, w)`, `w ≠ 0`. -/
theorem density_prodL {Γ : SourceTestCurvePredata θ} {Ψ : M × unitDisc → EReal}
    (hΨ : IsComplexificationOf Γ Ψ) (g : M → ℂ) (k i : ℕ) (x : M) (z : ComplexModel n)
    {w : ComplexModel 1} (hw : w ∈ (unitDisc : Set (ComplexModel 1))) (hw0 : w ≠ 0) :
    multiplierDensity (chartFunction Ψ (complexChartAt (n := n + 1) (x, discOrigin))) (k : ℝ)
        (fun z => (fun p : M × unitDisc => g p.1 * discCoord p.2 ^ i)
          ((complexChartAt (n := n + 1) (x, discOrigin)).val.symm z)) (prodL n (z, w)) =
      ENNReal.ofReal (‖g ((chartAt (ComplexModel n) x).symm z)‖ ^ 2) *
        (ENNReal.ofReal (‖w‖ ^ (2 * i)) * multiplierWeight (k : ℝ)
          (sourceTestCurveRawLegendre Γ (-Real.log (‖w‖ ^ 2))
            ((chartAt (ComplexModel n) x).symm z))) := by
  rw [multiplierDensity, complexChartAt_prod_val, coord_pow_eval g i x z hw, chartFunction,
    complexChartAt_prod_val, prodChartAt_symm_apply (x, discOrigin) z hw,
    hΨ _ (by exact hw0), norm_sq_coord_pow, ENNReal.ofReal_mul (by positivity), mul_assoc]
  rfl

/-! ### From `𝔞_{k,i}` to the radial weight -/

/-- **Extraction.** If `g ∈ 𝔞_{k,i}` at `x`, then near `z(x)` in the chart of `x`, `g` is
holomorphic and `|g|² D_{k,i}(·, r)` is integrable for some `0 < r ≤ 1` (Fubini in the product
chart). -/
theorem exists_lintegral_radialWeight_lt_top {Γ : SourceTestCurvePredata θ}
    {Ψ : M × unitDisc → EReal} (hΨ : IsComplexificationOf Γ Ψ) {k i : ℕ} {x : M} {g : M → ℂ}
    (h : (coeffIdeal (n := n) Ψ k i).mem x g) :
    ∃ U₁ : Set (ComplexModel n), IsOpen U₁ ∧ chartAt (ComplexModel n) x x ∈ U₁ ∧
      U₁ ⊆ (chartAt (ComplexModel n) x).target ∧
      DifferentiableOn ℂ (fun z => g ((chartAt (ComplexModel n) x).symm z)) U₁ ∧
      ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
        ∫⁻ z in U₁, ENNReal.ofReal (‖g ((chartAt (ComplexModel n) x).symm z)‖ ^ 2) *
          radialWeight Γ k i ((chartAt (ComplexModel n) x).symm z) r < ⊤ := by
  obtain ⟨-, -, U', hU', hxU', hd', hmeas', hint'⟩ := h.2
  set e := chartAt (ComplexModel n) x with he
  set c := complexChartAt (n := n + 1) (x, discOrigin) with hc
  have hc0 : c.val (x, discOrigin) = prodL n (e x, 0) := rfl
  rw [hc0] at hxU'
  obtain ⟨U₁, hU₁, hxU₁, hU₁t, r, hr0, hr1, hsub⟩ :=
    exists_prod_subset hU' hxU' e.open_target (mem_chart_target _ x)
  have hball : ∀ w ∈ ball (0 : ComplexModel 1) r, w ∈ (unitDisc : Set (ComplexModel 1)) :=
    fun w hw => mem_unitDisc.mpr (lt_of_lt_of_le (mem_ball_zero_iff.mp hw) hr1)
  refine ⟨U₁, hU₁, hxU₁, hU₁t, ?_, r, hr0, hr1, ?_⟩
  · -- slice at a point `w₀ ≠ 0`
    set w₀ : ComplexModel 1 := EuclideanSpace.single 0 ((r / 2 : ℝ) : ℂ) with hw₀
    have hw₀0 : w₀ 0 = ((r / 2 : ℝ) : ℂ) := by simp [hw₀]
    have hw₀ne : w₀ 0 ≠ 0 := by
      rw [hw₀0]; exact Complex.ofReal_ne_zero.mpr (by positivity)
    have hw₀b : w₀ ∈ ball (0 : ComplexModel 1) r := by
      rw [mem_ball_zero_iff, ← norm_apply_zero, hw₀0, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith
    have hdiff : DifferentiableOn ℂ (fun z => (fun p : M × unitDisc => g p.1 * discCoord p.2 ^ i)
        (c.val.symm (prodL n (z, w₀)))) U₁ := by
      refine hd'.comp ((prodL n).differentiable.comp
        (differentiable_id.prodMk (differentiable_const w₀))).differentiableOn ?_
      intro z hz
      exact hsub z hz w₀ hw₀b
    have heq : (fun z => g (e.symm z)) =
        fun z => (fun p : M × unitDisc => g p.1 * discCoord p.2 ^ i)
          (c.val.symm (prodL n (z, w₀))) * ((w₀ 0) ^ i)⁻¹ := by
      funext z
      rw [hc, complexChartAt_prod_val, coord_pow_eval g i x z (hball w₀ hw₀b), mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero i hw₀ne), mul_one]
    rw [heq]
    exact hdiff.mul_const _
  · set S : Set (ComplexModel (n + 1)) := (prodL n).symm ⁻¹' (U₁ ×ˢ ball 0 r) with hS
    have hSU' : S ⊆ U' := by
      intro z hz
      have := hsub _ hz.1 _ hz.2
      rwa [ContinuousLinearEquiv.apply_symm_apply] at this
    set dens := multiplierDensity (chartFunction Ψ c) (k : ℝ)
      (fun z => (fun p : M × unitDisc => g p.1 * discCoord p.2 ^ i) (c.val.symm z)) with hdens
    have hmeasS : AEMeasurable dens (volume.restrict S) :=
      hmeas'.mono_measure (Measure.restrict_mono hSU' le_rfl)
    have hprod := setLIntegral_prodL dens (U₁ ×ˢ ball 0 r)
    rw [setLIntegral_prod _ (by
      rw [← Measure.prod_restrict, Measure.prod_restrict]
      exact aemeasurable_comp_prodL hmeasS)] at hprod
    have hinner : ∀ z ∈ U₁, ∫⁻ w in ball (0 : ComplexModel 1) r, dens (prodL n (z, w)) =
        ENNReal.ofReal (‖g (e.symm z)‖ ^ 2) * radialWeight Γ k i (e.symm z) r := by
      intro z hz
      rw [radialWeight, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply setLIntegral_congr_fun_ae measurableSet_ball
      filter_upwards [Measure.ae_ne volume (0 : ComplexModel 1)] with w hw0 hw
      exact density_prodL hΨ g k i x z (hball w hw) hw0
    rw [setLIntegral_congr_fun hU₁.measurableSet hinner] at hprod
    rw [← hprod]
    exact lt_of_le_of_lt (lintegral_mono_set hSU') hint'

/-! ### The three inclusions -/

/-- **`𝔞_{k,i} ⊆ 𝓘(kΓ_{-(i+1)/k})`** when `-(i+1)/k < Γ_max ≤ 0`. -/
theorem multiplierIdeal_of_coeffIdeal [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
    [ConnectedSpace M] {Γ : SourceTestCurvePredata θ} (hmax : Γ.max ≤ 0)
    {Ψ : M × unitDisc → EReal} (hΨ : IsComplexificationOf Γ Ψ) {k : ℕ} (hk : 0 < k) {i : ℕ}
    (hτ : -((i : ℝ) + 1) / k < Γ.max) {x : M} {g : M → ℂ} (h : (coeffIdeal (n := n) Ψ k i).mem x g) :
    (multiplierIdeal (n := n) (k : ℝ) (Γ.potential ⟨-((i : ℝ) + 1) / k, hτ⟩)).mem x g := by
  obtain ⟨U₁, hU₁, hxU₁, hU₁t, hd, r, hr0, hr1, hint⟩ := exists_lintegral_radialWeight_lt_top hΨ h
  obtain ⟨K, hK, hKle⟩ := exists_multiplierWeight_slice_le_radialWeight Γ hmax hk i hτ hr0 hr1
  set e := chartAt (ComplexModel n) x with he
  set P := Γ.potential ⟨-((i : ℝ) + 1) / k, hτ⟩ with hP
  refine ⟨h.1, Nat.cast_pos.mpr hk, U₁, hU₁, hxU₁, hd, ?_, ?_⟩
  · have hPm : Measurable P :=
      (Γ.native_thetaPSH _).1.quasiPlurisubharmonic.upperSemicontinuous.measurable
    have hsymm : AEMeasurable e.symm (volume.restrict U₁) :=
      (e.continuousOn_symm.mono hU₁t).aemeasurable hU₁.measurableSet
    have hnorm : AEMeasurable (fun z => ENNReal.ofReal (‖g (e.symm z)‖ ^ 2))
        (volume.restrict U₁) :=
      ((hd.continuousOn.aemeasurable hU₁.measurableSet).norm.pow_const 2).ennreal_ofReal
    exact hnorm.mul ((measurable_multiplierWeight (Nat.cast_ne_zero.mpr hk.ne')).comp_aemeasurable
      (hPm.comp_aemeasurable hsymm))
  · calc ∫⁻ z in U₁, multiplierDensity (chartFunction P (complexChartAt (n := n) x)) (k : ℝ)
          (fun z => g ((complexChartAt (n := n) x).val.symm z)) z
        ≤ ∫⁻ z in U₁, K * (ENNReal.ofReal (‖g (e.symm z)‖ ^ 2) *
            radialWeight Γ k i (e.symm z) r) := by
          apply lintegral_mono
          intro z
          change ENNReal.ofReal (‖g (e.symm z)‖ ^ 2) * multiplierWeight (k : ℝ) (P (e.symm z)) ≤ _
          exact (mul_le_mul_of_nonneg_left (hKle _) bot_le).trans (le_of_eq (by ring))
      _ = K * ∫⁻ z in U₁, ENNReal.ofReal (‖g (e.symm z)‖ ^ 2) *
            radialWeight Γ k i (e.symm z) r := lintegral_const_mul' _ _ hK
      _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hK) hint

/-- **`𝔞_{k,i} = 0`** when `i + 1 + kΓ_max ≤ 0`: every `g ∈ 𝔞_{k,i}` vanishes near the point. -/
theorem eventuallyEq_zero_of_coeffIdeal {Γ : SourceTestCurvePredata θ}
    {Ψ : M × unitDisc → EReal} (hΨ : IsComplexificationOf Γ Ψ) {k i : ℕ}
    (hki : (i : ℝ) + 1 + k * Γ.max ≤ 0) {x : M} {g : M → ℂ} (h : (coeffIdeal (n := n) Ψ k i).mem x g) :
    g =ᶠ[𝓝 x] 0 := by
  obtain ⟨U₁, hU₁, hxU₁, hU₁t, hd, r, hr0, hr1, hint⟩ := exists_lintegral_radialWeight_lt_top hΨ h
  set e := chartAt (ComplexModel n) x with he
  simp_rw [radialWeight_eq_top Γ hki _ hr0 hr1] at hint
  have hmeas : AEMeasurable (fun z => ENNReal.ofReal (‖g (e.symm z)‖ ^ 2) * ⊤)
      (volume.restrict U₁) :=
    (((hd.continuousOn.aemeasurable hU₁.measurableSet).norm.pow_const 2).ennreal_ofReal).mul_const _
  have hae : (fun z => g (e.symm z)) =ᵐ[volume.restrict U₁] fun _ => (0 : ℂ) := by
    filter_upwards [ae_lt_top' hmeas hint.ne] with z hz
    by_contra hne
    have hpos : 0 < ENNReal.ofReal (‖g (e.symm z)‖ ^ 2) :=
      ENNReal.ofReal_pos.mpr (pow_pos (norm_pos_iff.mpr hne) 2)
    rw [ENNReal.mul_top hpos.ne'] at hz
    exact lt_irrefl _ hz
  have heq : EqOn (fun z => g (e.symm z)) (fun _ => (0 : ℂ)) U₁ :=
    Measure.eqOn_open_of_ae_eq hae hU₁ hd.continuousOn continuousOn_const
  have hev : ∀ᶠ y in 𝓝 x, y ∈ e.source ∧ e y ∈ U₁ :=
    Filter.Eventually.and (e.open_source.mem_nhds (mem_chart_source _ x))
      (e.continuousAt (mem_chart_source _ x) (hU₁.mem_nhds hxU₁))
  filter_upwards [hev] with y hy
  have h1 := heq hy.2
  simp only at h1
  rw [e.left_inv hy.1] at h1
  exact h1


/-- `L(U₁ × B)` minus the zero section `{δ = 0}` has full measure in `L(U₁ × B)`. -/
theorem volume_preimage_zero_section :
    volume ((prodL n).symm ⁻¹' (univ ×ˢ ({0} : Set (ComplexModel 1)))) = 0 := by
  have hmp := ProductMixedMeasure.measurePreserving_prodModelEquiv n 1
  have h := hmp.measure_preimage_emb (prodL n).toHomeomorph.measurableEmbedding
    ((prodL n).symm ⁻¹' (univ ×ˢ ({0} : Set (ComplexModel 1))))
  have hpre : (prodModelEquiv n 1) ⁻¹' ((prodL n).symm ⁻¹' (univ ×ˢ ({0} : Set _))) =
      univ ×ˢ ({0} : Set (ComplexModel 1)) := by
    ext p; simp [prodL]
  rw [hpre, Measure.prod_prod, measure_singleton, mul_zero] at h
  exact h.symm

/-- **`𝓘(kΓ_τ) ⊆ 𝔞_{k,i}`** when `i + kτ > -1`: from `Ψ(y, w) ≥ Γ_τ(y) - τ log|w|²` and
Fubini, `∫∫ |g|² |w|^{2i} e^{-kΨ} ≤ ∫ |g|² e^{-kΓ_τ} · ∫_{|w|<1} |w|^{2(i + kτ)} < ∞`. -/
theorem coeffIdeal_of_multiplierIdeal [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
    [ConnectedSpace M] (omega : KahlerBackground n M) {Γ : SourceTestCurvePredata θ}
    {Ψ : M × unitDisc → EReal} (hΨ : IsComplexificationOf Γ Ψ) {k : ℕ} (hk : 0 < k)
    (τ : Iio Γ.max) {i : ℕ} (hi : -1 < (i : ℝ) + k * τ.1) {x : M} {g : M → ℂ}
    (h : (multiplierIdeal (n := n) (k : ℝ) (Γ.potential τ)).mem x g) :
    (coeffIdeal (n := n) Ψ k i).mem x g := by
  obtain ⟨hg, hk', U, hU, hxU, hd, hmeas, hint⟩ := h
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  set e := chartAt (ComplexModel n) x with he
  set c := complexChartAt (n := n + 1) (x, discOrigin) with hc
  set U₁ := U ∩ e.target with hU₁def
  have hU₁ : IsOpen U₁ := hU.inter e.open_target
  set B := ball (0 : ComplexModel 1) 1 with hBdef
  set S := (prodL n).symm ⁻¹' (U₁ ×ˢ B) with hSdef
  have hS : IsOpen S := (hU₁.prod isOpen_ball).preimage (prodL n).symm.continuous
  have hB : ∀ w ∈ B, w ∈ (unitDisc : Set (ComplexModel 1)) :=
    fun w hw => mem_unitDisc.mpr (mem_ball_zero_iff.mp hw)
  have hGS : ∀ z ∈ S, (fun p : M × unitDisc => g p.1 * discCoord p.2 ^ i) (c.val.symm z) =
      g (e.symm ((prodL n).symm z).1) * ((prodL n).symm z).2 0 ^ i := by
    intro z hz
    have h1 := coord_pow_eval g i x ((prodL n).symm z).1 (hB _ hz.2)
    rw [Prod.mk.eta, ContinuousLinearEquiv.apply_symm_apply] at h1
    rw [hc, complexChartAt_prod_val]
    exact h1
  have hdS : DifferentiableOn ℂ
      (fun z => (fun p : M × unitDisc => g p.1 * discCoord p.2 ^ i) (c.val.symm z)) S := by
    have h1 : DifferentiableOn ℂ (fun z => g (e.symm ((prodL n).symm z).1)) S :=
      hd.comp (prodL n).symm.differentiable.fst.differentiableOn
        (fun z hz => hz.1.1)
    have h2 : Differentiable ℂ (fun z : ComplexModel (n + 1) => ((prodL n).symm z).2 0) :=
      (EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).differentiable.comp
        (prodL n).symm.differentiable.snd
    exact (h1.mul (h2.pow i).differentiableOn).congr hGS
  have hxS : c.val (x, discOrigin) ∈ S := by
    change (prodL n).symm (prodL n (e x, 0)) ∈ U₁ ×ˢ B
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact ⟨⟨hxU, mem_chart_target _ x⟩, mem_ball_self one_pos⟩
  refine ⟨hg, holomorphicAt_mul_coord_pow hg discOrigin i, hk', S, hS, hxS, hdS, ?_, ?_⟩
  · -- measurability: off the zero section, `Ψ` is the jointly usc Legendre transform
    set S' := S ∩ {z | ((prodL n).symm z).2 ≠ 0} with hS'def
    have hS' : IsOpen S' := hS.inter (isOpen_ne_fun
      (continuous_snd.comp (prodL n).symm.continuous) continuous_const)
    have hSS' : volume.restrict S = volume.restrict S' := by
      apply Measure.restrict_congr_set
      rw [ae_eq_set]
      refine ⟨measure_mono_null ?_ volume_preimage_zero_section,
        measure_mono_null (fun z hz => (hz.2 hz.1.1).elim) measure_empty⟩
      intro z hz
      refine ⟨mem_univ _, ?_⟩
      by_contra hne
      exact hz.2 ⟨hz.1, hne⟩
    set φ : ComplexModel (n + 1) → M × Ioi (0 : ℝ) := fun z =>
      (e.symm ((prodL n).symm z).1,
        ⟨Real.exp (Real.log (-Real.log (‖((prodL n).symm z).2‖ ^ 2))), Real.exp_pos _⟩) with hφ
    have hpos : ∀ z ∈ S', 0 < -Real.log (‖((prodL n).symm z).2‖ ^ 2) := by
      intro z hz
      have h0 : 0 < ‖((prodL n).symm z).2‖ := norm_pos_iff.mpr hz.2
      have h1 : ‖((prodL n).symm z).2‖ < 1 := mem_ball_zero_iff.mp hz.1.2
      have : Real.log (‖((prodL n).symm z).2‖ ^ 2) < 0 :=
        Real.log_neg (by positivity) (by nlinarith)
      linarith
    have hφc : ContinuousOn φ S' := by
      refine ContinuousOn.prodMk ?_ ?_
      · exact e.continuousOn_symm.comp (prodL n).symm.continuous.fst.continuousOn
          (fun z hz => hz.1.1.2)
      · refine (Real.continuous_exp.subtype_mk (fun s => Real.exp_pos s)).comp_continuousOn
          (ContinuousOn.log ?_ fun z hz => (hpos z hz).ne')
        refine (ContinuousOn.log ?_ fun z hz => ?_).neg
        · exact ((continuous_norm.comp (prodL n).symm.continuous.snd).pow 2).continuousOn
        · exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hz.2)
    have hR := Γ.rawLegendre_joint_upperSemicontinuous omega
    have hΨS' : AEMeasurable (fun z => Ψ (c.val.symm z)) (volume.restrict S') := by
      refine (hR.measurable.comp_aemeasurable (hφc.aemeasurable hS'.measurableSet)).congr ?_
      filter_upwards [ae_restrict_mem hS'.measurableSet] with z hz
      have hw := hB _ hz.1.2
      change sourceTestCurveRawLegendre Γ (φ z).2.1 (φ z).1 = Ψ (c.val.symm z)
      conv_rhs => rw [← (prodL n).apply_symm_apply z, ← Prod.mk.eta (p := (prodL n).symm z),
        complexChartAt_prod_val, prodChartAt_symm_apply (x, discOrigin) _ hw]
      rw [hΨ (e.symm ((prodL n).symm z).1, ⟨((prodL n).symm z).2, hw⟩) hz.2, complexification]
      simp only [hφ, Real.exp_log (hpos z hz)]
    have hnorm : AEMeasurable (fun z => ENNReal.ofReal
        (‖(fun p : M × unitDisc => g p.1 * discCoord p.2 ^ i) (c.val.symm z)‖ ^ 2))
        (volume.restrict S) :=
      ((hdS.continuousOn.aemeasurable hS.measurableSet).norm.pow_const 2).ennreal_ofReal
    have hw : AEMeasurable (fun z => multiplierWeight (k : ℝ) (Ψ (c.val.symm z)))
        (volume.restrict S) := by
      rw [hSS']
      exact (measurable_multiplierWeight hkpos.ne').comp_aemeasurable hΨS'
    exact hnorm.mul hw
  · set f : ComplexModel n → ℝ≥0∞ := multiplierDensity
      (chartFunction (Γ.potential τ) (complexChartAt (n := n) x)) (k : ℝ)
      (fun z => g ((complexChartAt (n := n) x).val.symm z)) with hfdef
    set hfun : ComplexModel 1 → ℝ≥0∞ := fun w => ENNReal.ofReal (‖w‖ ^ (2 * ((i : ℝ) + k * τ.1)))
      with hhdef
    rw [hSdef, setLIntegral_prodL]
    calc ∫⁻ p in U₁ ×ˢ B, multiplierDensity (chartFunction Ψ c) (k : ℝ)
          (fun z => (fun p : M × unitDisc => g p.1 * discCoord p.2 ^ i) (c.val.symm z))
          (prodL n p) ∂(volume.prod volume)
        ≤ ∫⁻ p in U₁ ×ˢ B, f p.1 * hfun p.2 ∂(volume.prod volume) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem (hU₁.prod isOpen_ball).measurableSet,
            ae_restrict_of_ae (Measure.quasiMeasurePreserving_snd.ae
              (Measure.ae_ne volume (0 : ComplexModel 1)))] with p hp hp0
          obtain ⟨z, w⟩ := p
          have hw0 : w ≠ 0 := hp0
          have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
          refine (le_of_eq (density_prodL hΨ g k i x z (hB w hp.2) hw0)).trans ?_
          have hwt := multiplierWeight_raw_le Γ hkpos τ (-Real.log (‖w‖ ^ 2)) (e.symm z)
          calc ENNReal.ofReal (‖g (e.symm z)‖ ^ 2) * (ENNReal.ofReal (‖w‖ ^ (2 * i)) *
                multiplierWeight (k : ℝ) (sourceTestCurveRawLegendre Γ (-Real.log (‖w‖ ^ 2))
                  (e.symm z)))
              ≤ ENNReal.ofReal (‖g (e.symm z)‖ ^ 2) * (ENNReal.ofReal (‖w‖ ^ (2 * i)) *
                (multiplierWeight (k : ℝ) (Γ.potential τ (e.symm z)) *
                  ENNReal.ofReal (Real.exp (-(k * (-Real.log (‖w‖ ^ 2) * τ.1)))))) := by
                gcongr
            _ = (ENNReal.ofReal (‖g (e.symm z)‖ ^ 2) *
                  multiplierWeight (k : ℝ) (Γ.potential τ (e.symm z))) *
                ENNReal.ofReal (‖w‖ ^ (2 * i) * Real.exp (-(k * (-Real.log (‖w‖ ^ 2) * τ.1)))) := by
                rw [ENNReal.ofReal_mul (by positivity)]; ring
            _ = f z * hfun w := by
                rw [pow_mul_exp_eq_rpow hwn i (k : ℝ) τ.1]
                rfl
      _ = (∫⁻ z in U₁, f z) * ∫⁻ w in B, hfun w := by
          rw [← Measure.prod_restrict]
          exact lintegral_prod_mul
            (hmeas.mono_measure (Measure.restrict_mono inter_subset_left le_rfl))
            ((continuous_norm.measurable.pow_const _).ennreal_ofReal.aemeasurable)
      _ < ⊤ := ENNReal.mul_lt_top (lt_of_le_of_lt (lintegral_mono_set inter_subset_left) hint)
          (lintegral_ball_rpow_lt_top (by linarith) 1)

end SGPT.NAPotential.NAGaga
