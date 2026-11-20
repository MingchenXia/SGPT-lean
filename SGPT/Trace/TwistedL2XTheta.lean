import SGPT.Trace.TwistedL2XTransport
import SGPT.Trace.TwistedL2DProj

/-!
# Chart invariance of the weighted adjoint `ϑ`

Blueprint `claude-tl2-man.tex` (lane TL2-MAN, `claude-tl2-man:theta`).  For a twisted datum on a
complex manifold, the formal adjoint `ϑ_p u = -∑_j (∂_j u_j - ∂_j p u_j)` of `∂̄` in the local weight
`p = -log |e|²_h + φ - log ρ` of a chart-frame `(c, e)` is invariant:

`ϑ_{p'}(u')(c' x) = t_{e e'}(x) · ϑ_p(u)(c x)`       when `u'` is the transport of `u`.

The proof avoids second derivatives of the coordinate change: `ϑ_p u` is characterized by the
integration-by-parts identity `∫ ϑ_p u · ḡ e^{-p} dλ = ∫ ∑_l u_l \overline{∂_{l̄} g} e^{-p} dλ`
(`integral_dbar_conj_eq`), the right side is chart invariant by the chain rule, and the two charts
are compared through the volume `μ` (`setIntegral_chg`: `e^{-p} dλ = |e|²_h e^{-φ} dμ`), followed by
the fundamental lemma of the calculus of variations.

Main results: `setIntegral_chg`, `isTestFunctionOn_transfX`, `TwistedDatum.chartTheta_transport`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory
open scoped Topology ContDiff ComplexConjugate Manifold ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-! ### Change of variables through the volume -/

theorem chg_image_subset_target {c c' : ComplexChart n X} {K : Set (ComplexModel n)}
    (hKo : K ⊆ ovl c c') : chg c c' '' K ⊆ c'.val.target := by
  rintro _ ⟨y, hy, rfl⟩
  exact c'.val.map_source (hKo hy).2

theorem isCompact_chg_image {c c' : ComplexChart n X} {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKo : K ⊆ ovl c c') : IsCompact (chg c c' '' K) :=
  hK.image_of_continuousOn ((differentiableOn_chg c c').continuousOn.mono hKo)

theorem source_inter_preimage_chg {c c' : ComplexChart n X} {K : Set (ComplexModel n)}
    (hKo : K ⊆ ovl c c') :
    c.val.source ∩ c.val ⁻¹' K = c'.val.source ∩ c'.val ⁻¹' (chg c c' '' K) := by
  ext x
  constructor
  · rintro ⟨hx, hxK⟩
    have hxo : c.val x ∈ ovl c c' := hKo hxK
    have hx' : x ∈ c'.val.source := by
      have := hxo.2
      simp only [mem_preimage, c.val.left_inv hx] at this
      exact this
    exact ⟨hx', c.val x, hxK, chg_chart hx⟩
  · rintro ⟨hx', y, hyK, hy⟩
    have hyo := hKo hyK
    have hx : x = c.val.symm y := by
      rw [← c'.val.left_inv hx', ← hy, symm_chg hyo]
    subst hx
    exact ⟨c.val.map_target hyo.1, by
      simp only [mem_preimage]; rw [c.val.right_inv hyo.1]; exact hyK⟩

section Measure

variable [MeasurableSpace X] [BorelSpace X]

/-- The coordinate change pushes the chart volume of `c` to the chart volume of `c'`. -/
theorem map_chg_withDensity {μ : Measure X} {c c' : ComplexChart n X}
    {ρ ρ' : ComplexModel n → ℝ} (hρ : IsChartDensity μ c ρ) (hρ' : IsChartDensity μ c' ρ')
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKo : K ⊆ ovl c c') :
    Measure.map (chg c c') ((volume.restrict K).withDensity fun z => ENNReal.ofReal (ρ z)) =
      (volume.restrict (chg c c' '' K)).withDensity fun z => ENNReal.ofReal (ρ' z) := by
  have hKt : K ⊆ c.val.target := fun y hy => (hKo hy).1
  have hK' := isCompact_chg_image hK hKo
  have hK't := chg_image_subset_target hKo
  set ν := (volume.restrict K).withDensity fun z => ENNReal.ofReal (ρ z) with hν
  have h1 : Measure.map c.val.symm ν = (μ.restrict c.val.source).restrict (c.val ⁻¹' K) :=
    chartDensity_map_symm_restrict c hρ hK.measurableSet hKt
  have h2 := chartDensity_map_restrict c' hρ' hK'.measurableSet hK't
  have hX : (μ.restrict c.val.source).restrict (c.val ⁻¹' K) =
      (μ.restrict c'.val.source).restrict (c'.val ⁻¹' (chg c c' '' K)) := by
    rw [Measure.restrict_restrict' c.val.open_source.measurableSet,
      Measure.restrict_restrict' c'.val.open_source.measurableSet, inter_comm,
      source_inter_preimage_chg hKo, inter_comm]
  have hsymm : AEMeasurable c.val.symm ν :=
    ((c.val.continuousOn_symm.mono hKt).aemeasurable hK.measurableSet).mono_ac
      (withDensity_absolutelyContinuous _ _)
  have hc' : AEMeasurable c'.val (Measure.map c.val.symm ν) := by
    rw [h1, hX]
    exact (c'.val.continuousOn.aemeasurable c'.val.open_source.measurableSet).restrict
  change Measure.map (c'.val ∘ c.val.symm) ν = _
  rw [← AEMeasurable.map_map_of_aemeasurable hc' hsymm, h1, hX, h2]

theorem integral_withDensity_ofReal_eq {S : Set (ComplexModel n)} (hS : MeasurableSet S)
    {r : ComplexModel n → ℝ} (hr : ContinuousOn r S) (hpos : ∀ z ∈ S, 0 < r z)
    {F : ComplexModel n → ℂ} :
    ∫ y, F y ∂((volume.restrict S).withDensity fun z => ENNReal.ofReal (r z)) =
      ∫ y in S, (r y : ℂ) * F y := by
  have hrm : AEMeasurable (fun z => ENNReal.ofReal (r z)) (volume.restrict S) :=
    (ENNReal.continuous_ofReal.comp_continuousOn hr).aemeasurable hS
  rw [integral_withDensity_eq_integral_toReal_smul₀ hrm
    (Eventually.of_forall fun z => ENNReal.ofReal_lt_top) F]
  refine setIntegral_congr_fun hS fun z hz => ?_
  rw [ENNReal.toReal_ofReal (hpos z hz).le, Complex.real_smul]

/-- **Change of variables through the volume**: `∫_{ψ(K)} ρ' G = ∫_K ρ · G ∘ ψ` for the coordinate
change `ψ = c' ∘ c⁻¹` and the chart densities `ρ, ρ'` of the same volume. -/
theorem setIntegral_chg {μ : Measure X} {c c' : ComplexChart n X} {ρ ρ' : ComplexModel n → ℝ}
    (hρ : IsChartDensity μ c ρ) (hρ' : IsChartDensity μ c' ρ')
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKo : K ⊆ ovl c c') {G : ComplexModel n → ℂ}
    (hG : ContinuousOn G (chg c c' '' K)) :
    ∫ y in chg c c' '' K, (ρ' y : ℂ) * G y = ∫ y in K, (ρ y : ℂ) * G (chg c c' y) := by
  have hKt : K ⊆ c.val.target := fun y hy => (hKo hy).1
  have hK' := isCompact_chg_image hK hKo
  have hK't := chg_image_subset_target hKo
  have hρK : ContinuousOn ρ K := hρ.1.continuousOn.mono hKt
  have hρ'K : ContinuousOn ρ' (chg c c' '' K) := hρ'.1.continuousOn.mono hK't
  have hchgK : ContinuousOn (chg c c') K := (differentiableOn_chg c c').continuousOn.mono hKo
  have hmap := map_chg_withDensity hρ hρ' hK hKo
  have hA : AEMeasurable (chg c c')
      ((volume.restrict K).withDensity fun z => ENNReal.ofReal (ρ z)) :=
    (hchgK.aemeasurable hK.measurableSet).mono_ac (withDensity_absolutelyContinuous _ _)
  have hB : AEStronglyMeasurable G (Measure.map (chg c c')
      ((volume.restrict K).withDensity fun z => ENNReal.ofReal (ρ z))) := by
    rw [hmap]
    exact (hG.aestronglyMeasurable hK'.measurableSet).mono_ac
      (withDensity_absolutelyContinuous _ _)
  rw [← integral_withDensity_ofReal_eq hK'.measurableSet hρ'K
      (fun z hz => hρ'.2.1 z (hK't hz)), ← hmap, integral_map hA hB,
    integral_withDensity_ofReal_eq hK.measurableSet hρK (fun z hz => hρ.2.1 z (hKt hz))]

end Measure

/-! ### Transport of scalar test functions -/

section TestTransport

variable (L : HermitianHolomorphicLineBundle.{0, 0} n X)

open Classical in
/-- The coefficient, in `(c', e')`, of the test section with coefficient `g` in `(c, e)`. -/
def transfX (c : ComplexChart n X) (e : AtlasFrame L) (c' : ComplexChart n X) (e' : AtlasFrame L)
    (g : ComplexModel n → ℂ) (y : ComplexModel n) : ℂ :=
  if y ∈ ovl c' c ∧ c'.val.symm y ∈ e.val.baseSet then
    frameTrans L e e' (c'.val.symm y) * g (chg c' c y)
  else 0

variable {L}

theorem transfX_chg {c c' : ComplexChart n X} {e e' : AtlasFrame L} {g : ComplexModel n → ℂ}
    {y : ComplexModel n} (hy : y ∈ ovl c c') (hyb : c.val.symm y ∈ e.val.baseSet) :
    transfX L c e c' e' g (chg c c' y) = frameTrans L e e' (c.val.symm y) * g y := by
  classical
  have h1 : chg c c' y ∈ ovl c' c := chg_mem_ovl hy
  rw [transfX, if_pos ⟨h1, by rw [symm_chg hy]; exact hyb⟩, symm_chg hy, chg_chg hy]

theorem transfX_chg_eventually {c c' : ComplexChart n X} {e e' : AtlasFrame L}
    {g : ComplexModel n → ℂ} {y : ComplexModel n} (hy : y ∈ ovl c c')
    (hyb : c.val.symm y ∈ e.val.baseSet) :
    (fun x => transfX L c e c' e' g (chg c c' x)) =ᶠ[𝓝 y]
      fun x => frameTrans L e e' (c.val.symm x) * g x := by
  have hO : IsOpen (ovl c c' ∩ c.val.symm ⁻¹' e.val.baseSet) :=
    (c.val.continuousOn_symm.mono fun _ hy => hy.1).isOpen_inter_preimage
      (isOpen_ovl c c') e.val.open_baseSet
  filter_upwards [hO.mem_nhds ⟨hy, hyb⟩] with x hx
  exact transfX_chg hx.1 hx.2

theorem support_transfX_subset {c c' : ComplexChart n X} {e e' : AtlasFrame L}
    (g : ComplexModel n → ℂ) :
    Function.support (transfX L c e c' e' g) ⊆ chg c c' '' Function.support g := by
  classical
  intro y hy
  by_cases hc : y ∈ ovl c' c ∧ c'.val.symm y ∈ e.val.baseSet
  · rw [Function.mem_support, transfX, if_pos hc] at hy
    refine ⟨chg c' c y, right_ne_zero_of_mul hy, chg_chg hc.1⟩
  · rw [Function.mem_support, transfX, if_neg hc] at hy
    exact absurd rfl hy

/-- **The transported test function is a test function** on the chart-frame domain. -/
theorem isTestFunctionOn_transfX {c c' : ComplexChart n X} {e e' : AtlasFrame L}
    {g : ComplexModel n → ℂ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hgs : tsupport g ⊆ ovl c c' ∩ c.val.symm ⁻¹' (e.val.baseSet ∩ e'.val.baseSet)) :
    ContDiff ℝ ∞ (transfX L c e c' e' g) ∧ HasCompactSupport (transfX L c e c' e' g) ∧
      tsupport (transfX L c e c' e' g) ⊆ chg c c' '' tsupport g := by
  have hK : IsCompact (tsupport g) := hgc
  have hKo : tsupport g ⊆ ovl c c' := fun y hy => (hgs hy).1
  have hK' : IsCompact (chg c c' '' tsupport g) := isCompact_chg_image hK hKo
  have hts : tsupport (transfX L c e c' e' g) ⊆ chg c c' '' tsupport g :=
    closure_minimal ((support_transfX_subset g).trans (image_mono subset_closure))
      hK'.isClosed
  refine ⟨?_, HasCompactSupport.of_support_subset_isCompact hK' (subset_closure.trans hts), hts⟩
  rw [contDiff_iff_contDiffAt]
  intro y'
  by_cases hy' : y' ∈ chg c c' '' tsupport g
  · obtain ⟨y, hyK, rfl⟩ := hy'
    obtain ⟨hyo, hyb, hyb'⟩ := hgs hyK
    have hy1 : chg c c' y ∈ ovl c' c := chg_mem_ovl hyo
    have hsy : c'.val.symm (chg c c' y) = c.val.symm y := symm_chg hyo
    set S : Set (ComplexModel n) :=
      ovl c' c ∩ c'.val.symm ⁻¹' (e.val.baseSet ∩ e'.val.baseSet) with hS
    have hSo : IsOpen S :=
      (c'.val.continuousOn_symm.mono fun _ hy => hy.1).isOpen_inter_preimage
        (isOpen_ovl c' c) (e.val.open_baseSet.inter e'.val.open_baseSet)
    have hyS : chg c c' y ∈ S := ⟨hy1, by rw [mem_preimage, hsy]; exact ⟨hyb, hyb'⟩⟩
    have htr : ContDiffOn ℝ ∞ (fun x => frameTrans L e e' (c'.val.symm x)) S :=
      contDiffOn_real_of_differentiableOn_complex
        ((differentiableOn_frameTrans c' e e').mono fun x hx => ⟨hx.1.1, hx.2⟩) hSo
    have hgc' : ContDiffOn ℝ ∞ (fun x => g (chg c' c x)) S :=
      hg.comp_contDiffOn ((contDiffOn_real_of_differentiableOn_complex
        (differentiableOn_chg c' c) (isOpen_ovl c' c)).mono fun x hx => hx.1)
    refine ((htr.mul hgc').contDiffAt (hSo.mem_nhds hyS)).congr_of_eventuallyEq ?_
    filter_upwards [hSo.mem_nhds hyS] with x hx
    classical
    rw [transfX, if_pos ⟨hx.1, hx.2.1⟩]
  · have hev : transfX L c e c' e' g =ᶠ[𝓝 y'] fun _ => 0 := by
      filter_upwards [hK'.isClosed.isOpen_compl.mem_nhds hy'] with x hx
      exact image_eq_zero_of_notMem_tsupport fun h => hx (hts h)
    exact contDiffAt_const.congr_of_eventuallyEq hev

end TestTransport

/-! ### Pointwise identities -/

theorem sum_dbarDir_mul_conj_eq {G : ComplexModel n → ℂ} {y : ComplexModel n}
    (hG : DifferentiableAt ℝ G y) (w : ComplexModel n) :
    ∑ l, dbarDir (coordVec l) G y * conj (w l) = conj (dDir w (fun x => conj (G x)) y) := by
  conv_rhs => rw [← eq_sum_coordVec w]
  rw [dDir_sum_dir, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [dDir_conj hG, map_mul, Complex.conj_conj, mul_comm]

theorem dDir_conj_holo_eq_zero {t : ComplexModel n → ℂ} {y : ComplexModel n}
    (ht : DifferentiableAt ℂ t y) (v : ComplexModel n) :
    dDir v (fun x => conj (t x)) y = 0 := by
  rw [dDir_conj (ht.restrictScalars ℝ), dbarDir_holomorphic ht, map_zero]

/-- The chain-rule identity behind the invariance of the integration-by-parts pairing. -/
theorem sum_dbar_transport {ψ : ComplexModel n → ComplexModel n} {t : ComplexModel n → ℂ}
    {g G : ComplexModel n → ℂ} {y : ComplexModel n} (hψ : DifferentiableAt ℂ ψ y)
    (ht : DifferentiableAt ℂ t y) (hg : DifferentiableAt ℝ g y)
    (hG : DifferentiableAt ℝ G (ψ y)) (hrel : (fun x => G (ψ x)) =ᶠ[𝓝 y] fun x => t x * g x)
    (u : ComplexModel n) :
    ∑ l, dbarDir (coordVec l) G (ψ y) * conj ((t y • fderiv ℂ ψ y u) l) =
      (t y * conj (t y)) * ∑ l, dbarDir (coordVec l) g y * conj (u l) := by
  have hGc : DifferentiableAt ℝ (fun x => conj (G x)) (ψ y) :=
    (Complex.conjCLE.toContinuousLinearMap.differentiableAt).comp _ hG
  have hrel' : (fun x => conj (G (ψ x))) =ᶠ[𝓝 y] fun x => conj (t x) * conj (g x) :=
    hrel.mono fun x hx => by simp only [hx, map_mul]
  have htc : DifferentiableAt ℝ (fun x => conj (t x)) y :=
    (Complex.conjCLE.toContinuousLinearMap.differentiableAt).comp _ (ht.restrictScalars ℝ)
  have hgc : DifferentiableAt ℝ (fun x => conj (g x)) y :=
    (Complex.conjCLE.toContinuousLinearMap.differentiableAt).comp _ hg
  rw [sum_dbarDir_mul_conj_eq hG, sum_dbarDir_mul_conj_eq hg, dDir_smul_dir,
    ← dDir_comp_holo hψ hGc, dDir_congr_of_eventuallyEq hrel', dDir_mul htc hgc,
    dDir_conj_holo_eq_zero ht, zero_mul, zero_add]
  simp only [map_mul, Complex.conj_conj]
  ring

/-! ### The invariance of `ϑ` -/

namespace TwistedDatum

variable [MeasurableSpace X] [BorelSpace X] (T : TwistedDatum n X)

/-- The density of the volume in the chart `c` (chosen once and for all). -/
def ρX (c : ComplexChart n X) : ComplexModel n → ℝ := Classical.choose (T.volume_smooth c)

theorem isChartDensity_ρX (c : ComplexChart n X) : IsChartDensity T.μ c (T.ρX c) :=
  Classical.choose_spec (T.volume_smooth c)

/-- The local weight `p = -log |e|²_h + φ - log ρ` of the chart-frame `(c, e)`. -/
def pX (c : ComplexChart n X) (e : AtlasFrame T.L) : ComplexModel n → ℝ :=
  localWeight T.L c e (T.ρX c) T.φ

/-- The `μ`-density `|e|²_h e^{-φ}` of the chart-frame `(c, e)` in chart coordinates. -/
def wX (c : ComplexChart n X) (e : AtlasFrame T.L) (z : ComplexModel n) : ℝ :=
  frameNormSq T.L e (c.val.symm z) * Real.exp (-T.φ (c.val.symm z))

variable {T}

theorem cweight_pX {c : ComplexChart n X} {e : AtlasFrame T.L} {z : ComplexModel n}
    (hz : z ∈ chartFrameDomain T.L c e) :
    cweight (T.pX c e) z = ((T.ρX c z : ℝ) : ℂ) * ((T.wX c e z : ℝ) : ℂ) := by
  rw [cweight, pX, T.exp_neg_localWeight e (T.isChartDensity_ρX c) hz, wX]
  push_cast
  ring

theorem wX_chg {c c' : ComplexChart n X} {e e' : AtlasFrame T.L} {z : ComplexModel n}
    (hz : z ∈ ovl c c') (hb : c.val.symm z ∈ e.val.baseSet ∩ e'.val.baseSet) :
    T.wX c' e' (chg c c' z) * (frameTrans T.L e e' (c.val.symm z) *
      conj (frameTrans T.L e e' (c.val.symm z))) = T.wX c e z := by
  simp only [wX, symm_chg hz, frameNormSq_eq_frameTrans e e' hb]
  rw [← ofReal_norm_sq_eq_mul_conj]
  push_cast
  ring

theorem contDiffOn_pX (c : ComplexChart n X) (e : AtlasFrame T.L) :
    ContDiffOn ℝ ∞ (T.pX c e) (T.pieceDomain c e) :=
  T.contDiffOn_localWeight e (T.isChartDensity_ρX c)

theorem continuousOn_wX (c : ComplexChart n X) (e : AtlasFrame T.L) :
    ContinuousOn (T.wX c e) (T.pieceDomain c e) := by
  have h1 : ContinuousOn (fun z => frameNormSq T.L e (c.val.symm z)) (T.pieceDomain c e) :=
    ((T.metric_smooth c e).mono fun z hz => hz.1).continuousOn
  have h2 : ContinuousOn (fun z => T.φ (c.val.symm z)) (T.pieceDomain c e) :=
    ((T.φ_smooth c).mono (T.pieceDomain_subset_chartSmooth c e)).continuousOn
  exact h1.mul (Real.continuous_exp.comp_continuousOn h2.neg)

theorem wX_pos {c : ComplexChart n X} {e : AtlasFrame T.L} {z : ComplexModel n}
    (hz : z ∈ chartFrameDomain T.L c e) : 0 < T.wX c e z :=
  mul_pos (frameNormSq_pos e hz.2) (Real.exp_pos _)

theorem dbarDir_eq_zero_of_notMem_tsupport' {f : ComplexModel n → ℂ} {z : ComplexModel n}
    (hz : z ∉ tsupport f) (v : ComplexModel n) : dbarDir v f z = 0 :=
  dbarDir_eq_zero_of_eventuallyEq_zero (notMem_tsupport_iff_eventuallyEq.mp hz)

/-- **The integration-by-parts identity in two charts.**  For a real test function `g` supported
in a set `V` where `u'` is the transport of `u`, the pairings of `ϑ_p u` and of
`t⁻¹ ϑ_{p'} u' ∘ (c' ∘ c⁻¹)` with `g` agree. -/
theorem integral_test_eq {c c' : ComplexChart n X} {e e' : AtlasFrame T.L}
    {A A' : Set (ComplexModel n)} (hA : IsOpen A) (hA' : IsOpen A') (hAd : A ⊆ T.pieceDomain c e)
    (hA'd : A' ⊆ T.pieceDomain c' e')
    {u u' : ComplexModel n → ComplexModel n} (hu : ContDiffOn ℝ ∞ u A)
    (hu' : ContDiffOn ℝ ∞ u' A') {V : Set (ComplexModel n)}
    (hVS : V ⊆ A ∩ ovl c c' ∩ c.val.symm ⁻¹' e'.val.baseSet)
    (hVA' : ∀ y ∈ V, chg c c' y ∈ A')
    (hVrel : ∀ y ∈ V, u' (chg c c' y) =
      frameTrans T.L e e' (c.val.symm y) • fderiv ℂ (chg c c') y (u y))
    (g : ComplexModel n → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hgV : tsupport g ⊆ V) :
    ∫ y, (g y : ℂ) * conj (chartTheta (T.pX c e) u y) * cweight (T.pX c e) y =
      ∫ y, (g y : ℂ) * conj (chartTheta (T.pX c' e') u' (chg c c' y) /
        frameTrans T.L e e' (c.val.symm y)) * cweight (T.pX c e) y := by
  set t : ComplexModel n → ℂ := fun y => frameTrans T.L e e' (c.val.symm y) with ht_def
  set gc : ComplexModel n → ℂ := fun y => (g y : ℂ) with hgc_def
  set K := tsupport gc with hK_def
  have hKg : K ⊆ tsupport g := tsupport_comp_subset Complex.ofReal_zero g
  have hKc : IsCompact K := (hgc.comp_left Complex.ofReal_zero).isCompact
  have hKV : K ⊆ V := hKg.trans hgV
  have hVA : ∀ y ∈ V, y ∈ A := fun y hy => (hVS hy).1.1
  have hVpd : ∀ y ∈ V, y ∈ T.pieceDomain c e := fun y hy => hAd (hVA y hy)
  have hVo' : ∀ y ∈ V, y ∈ ovl c c' := fun y hy => (hVS hy).1.2
  have hVb : ∀ y ∈ V, c.val.symm y ∈ e.val.baseSet ∩ e'.val.baseSet := fun y hy =>
    ⟨(hVpd y hy).1.2, (hVS hy).2⟩
  have hKo : K ⊆ ovl c c' := fun y hy => hVo' y (hKV hy)
  have hgcs : ContDiff ℝ ∞ gc := Complex.ofRealCLM.contDiff.comp hg
  have hgT : IsTestFunctionOn A gc :=
    ⟨hgcs, hgc.comp_left Complex.ofReal_zero, fun y hy => hVA y (hKV hy)⟩
  -- the transported test function
  obtain ⟨hG1, hG2, hG3⟩ := isTestFunctionOn_transfX (L := T.L) (c := c) (c' := c')
    (e := e) (e' := e') hgcs (hgc.comp_left Complex.ofReal_zero)
    (fun y hy => ⟨hKo hy, hVb y (hKV hy)⟩)
  set G' := transfX T.L c e c' e' gc with hG'_def
  set K' := chg c c' '' K with hK'_def
  have hK'A : K' ⊆ A' := by
    rintro _ ⟨y, hy, rfl⟩
    exact hVA' y (hKV hy)
  have hK'pd : K' ⊆ T.pieceDomain c' e' := hK'A.trans hA'd
  have hG'T : IsTestFunctionOn A' G' := ⟨hG1, hG2, hG3.trans hK'A⟩
  have IBP := integral_dbar_conj_eq hA ((T.contDiffOn_pX c e).mono hAd) hu hgT
  have IBP' := integral_dbar_conj_eq hA' ((T.contDiffOn_pX c' e').mono hA'd) hu' hG'T
  have hρ := T.isChartDensity_ρX c
  have hρ' := T.isChartDensity_ρX c'
  -- the two chart-`c'` integrands
  set Ψ1 : ComplexModel n → ℂ := fun y => ((T.wX c' e' y : ℝ) : ℂ) *
    ∑ l, dbarDir (coordVec l) G' y * conj (u' y l) with hΨ1
  set Ψ2 : ComplexModel n → ℂ := fun y => G' y * conj (chartTheta (T.pX c' e') u' y) *
    ((T.wX c' e' y : ℝ) : ℂ) with hΨ2
  have hwc : ContinuousOn (fun y => ((T.wX c' e' y : ℝ) : ℂ)) A' :=
    Complex.continuous_ofReal.comp_continuousOn ((continuousOn_wX c' e').mono hA'd)
  have hΨ1c : ContinuousOn Ψ1 K' := by
    refine (hwc.mul (continuousOn_finsetSum _ fun l _ => ?_)).mono hK'A
    exact ((contDiffOn_dbarDir isOpen_univ hG1.contDiffOn (coordVec l)).continuousOn.mono
      (subset_univ _)).mul
      (Complex.continuous_conj.comp_continuousOn (contDiffOn_coord hu' l).continuousOn)
  have hΨ2c : ContinuousOn Ψ2 K' := by
    refine ((hG1.continuous.continuousOn.mul (Complex.continuous_conj.comp_continuousOn
      (continuousOn_chartTheta' hA' ((T.contDiffOn_pX c' e').mono hA'd) hu'))).mul hwc).mono
      hK'A
  -- chart `c'` integrals as integrals over `K'`
  have e1 : ∫ y, cweight (T.pX c' e') y * ∑ l, dbarDir (coordVec l) G' y * conj (u' y l) =
      ∫ y in K', ((T.ρX c' y : ℝ) : ℂ) * Ψ1 y := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K') fun y hy => ?_]
    · refine setIntegral_congr_fun (isCompact_chg_image hKc hKo).measurableSet fun y hy => ?_
      simp only [hΨ1]
      rw [cweight_pX (hK'pd hy).1]
      ring
    · have hy' : y ∉ tsupport G' := fun h => hy (hG3 h)
      simp [dbarDir_eq_zero_of_notMem_tsupport' hy']
  have e2 : ∫ y, G' y * conj (chartTheta (T.pX c' e') u' y) * cweight (T.pX c' e') y =
      ∫ y in K', ((T.ρX c' y : ℝ) : ℂ) * Ψ2 y := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K') fun y hy => ?_]
    · refine setIntegral_congr_fun (isCompact_chg_image hKc hKo).measurableSet fun y hy => ?_
      simp only [hΨ2]
      rw [cweight_pX (hK'pd hy).1]
      ring
    · have hy' : y ∉ tsupport G' := fun h => hy (hG3 h)
      simp [image_eq_zero_of_notMem_tsupport hy']
  -- pointwise identities on `K`
  have p1 : ∀ y ∈ K, ((T.ρX c y : ℝ) : ℂ) * Ψ1 (chg c c' y) =
      cweight (T.pX c e) y * ∑ l, dbarDir (coordVec l) gc y * conj (u y l) := by
    intro y hy
    have hyV := hKV hy
    have hyo := hVo' y hyV
    have hψ : DifferentiableAt ℂ (chg c c') y := differentiableAt_chg hyo
    have htd : DifferentiableAt ℂ t y :=
      ((differentiableOn_frameTrans c e e').mono fun x hx => hx).differentiableAt
        ((c.val.continuousOn_symm.isOpen_inter_preimage c.val.open_target
          (e.val.open_baseSet.inter e'.val.open_baseSet)).mem_nhds ⟨(hVpd y hyV).1.1, hVb y hyV⟩)
    have hG'd : DifferentiableAt ℝ G' (chg c c' y) :=
      hG1.differentiable (by simp) _
    have hgd : DifferentiableAt ℝ gc y := hgcs.differentiable (by simp) _
    have hrel := transfX_chg_eventually (L := T.L) (e' := e') (g := gc) hyo (hVb y hyV).1
    simp only [hΨ1]
    rw [hVrel y hyV, sum_dbar_transport hψ htd hgd hG'd hrel, cweight_pX (hVpd y hyV).1]
    have hw := wX_chg (T := T) hyo (hVb y hyV)
    rw [← hw]
    push_cast
    ring
  have p2 : ∀ y ∈ K, ((T.ρX c y : ℝ) : ℂ) * Ψ2 (chg c c' y) =
      gc y * conj (chartTheta (T.pX c' e') u' (chg c c' y) / t y) * cweight (T.pX c e) y := by
    intro y hy
    have hyV := hKV hy
    have hyo := hVo' y hyV
    have ht0 : t y ≠ 0 := frameTrans_ne_zero e e' (hVb y hyV)
    have htc0 : conj (t y) ≠ 0 := by simpa using ht0
    simp only [hΨ2]
    rw [hG'_def, transfX_chg hyo (hVb y hyV).1, cweight_pX (hVpd y hyV).1]
    have hw := wX_chg (T := T) hyo (hVb y hyV)
    rw [← hw, map_div₀]
    field_simp
    ring
  -- assemble
  have lhs : ∫ y, cweight (T.pX c e) y * ∑ l, dbarDir (coordVec l) gc y * conj (u y l) =
      ∫ y in K, ((T.ρX c y : ℝ) : ℂ) * Ψ1 (chg c c' y) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) fun y hy => ?_]
    · exact setIntegral_congr_fun hKc.measurableSet fun y hy => (p1 y hy).symm
    · simp [dbarDir_eq_zero_of_notMem_tsupport' hy]
  have rhs : ∫ y, gc y * conj (chartTheta (T.pX c' e') u' (chg c c' y) / t y) *
      cweight (T.pX c e) y = ∫ y in K, ((T.ρX c y : ℝ) : ℂ) * Ψ2 (chg c c' y) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) fun y hy => ?_]
    · exact setIntegral_congr_fun hKc.measurableSet fun y hy => (p2 y hy).symm
    · simp [image_eq_zero_of_notMem_tsupport hy]
  rw [← IBP, lhs, ← setIntegral_chg hρ hρ' hKc hKo hΨ1c, ← e1, IBP', e2,
    setIntegral_chg hρ hρ' hKc hKo hΨ2c, ← rhs]

/-- **Chart invariance of `ϑ`** (`claude-tl2-man:theta`): if `u'` is the transport of `u` from
`(c, e)` to `(c', e')` near `z`, then `ϑ_{p'} u'(c' x) = t_{e e'}(x) ϑ_p u(c x)`. -/
theorem chartTheta_transport {c c' : ComplexChart n X} {e e' : AtlasFrame T.L}
    {A A' : Set (ComplexModel n)} (hA : IsOpen A) (hA' : IsOpen A') (hAd : A ⊆ T.pieceDomain c e)
    (hA'd : A' ⊆ T.pieceDomain c' e')
    {u u' : ComplexModel n → ComplexModel n} (hu : ContDiffOn ℝ ∞ u A)
    (hu' : ContDiffOn ℝ ∞ u' A') {z : ComplexModel n}
    (hz : z ∈ A) (hz' : c.val.symm z ∈ c'.val.source ∩ e'.val.baseSet)
    (hzA' : chg c c' z ∈ A') (hrel : IsTransp T.L c e c' e' u u' z) :
    chartTheta (T.pX c' e') u' (chg c c' z) =
      frameTrans T.L e e' (c.val.symm z) * chartTheta (T.pX c e) u z := by
  set t : ComplexModel n → ℂ := fun y => frameTrans T.L e e' (c.val.symm y) with ht_def
  set S : Set (ComplexModel n) := A ∩ ovl c c' ∩ c.val.symm ⁻¹' e'.val.baseSet with hS
  have hSo : IsOpen S :=
    (c.val.continuousOn_symm.mono fun _ hy => (hAd hy.1).1.1).isOpen_inter_preimage
      (hA.inter (isOpen_ovl c c')) e'.val.open_baseSet
  have hzS : z ∈ S := ⟨⟨hz, (hAd hz).1.1, hz'.1⟩, hz'.2⟩
  have hS' : IsOpen (S ∩ chg c c' ⁻¹' A') :=
    ((differentiableOn_chg c c').continuousOn.mono fun _ hy => hy.1.2).isOpen_inter_preimage
      hSo hA'
  obtain ⟨V, hVsub, hVo, hzV⟩ := mem_nhds_iff.mp (hrel.and (hS'.mem_nhds ⟨hzS, hzA'⟩))
  have hVS : V ⊆ S := fun y hy => (hVsub hy).2.1
  have hVA' : ∀ y ∈ V, chg c c' y ∈ A' := fun y hy => (hVsub hy).2.2
  have hVrel : ∀ y ∈ V, u' (chg c c' y) = t y • fderiv ℂ (chg c c') y (u y) :=
    fun y hy => (hVsub hy).1
  -- basic facts on `V`
  have hVA : ∀ y ∈ V, y ∈ A := fun y hy => (hVS hy).1.1
  have hVpd : ∀ y ∈ V, y ∈ T.pieceDomain c e := fun y hy => hAd (hVA y hy)
  have hVo' : ∀ y ∈ V, y ∈ ovl c c' := fun y hy => (hVS hy).1.2
  have hVb : ∀ y ∈ V, c.val.symm y ∈ e.val.baseSet ∩ e'.val.baseSet := fun y hy =>
    ⟨(hVpd y hy).1.2, (hVS hy).2⟩
  have htV : DifferentiableOn ℂ t V :=
    (differentiableOn_frameTrans c e e').mono fun y hy => ⟨(hVpd y hy).1.1, hVb y hy⟩
  have ht0 : ∀ y ∈ V, t y ≠ 0 := fun y hy => frameTrans_ne_zero e e' (hVb y hy)
  -- the continuous function which must vanish
  set F : ComplexModel n → ℂ := fun y => conj (chartTheta (T.pX c e) u y -
      chartTheta (T.pX c' e') u' (chg c c' y) / t y) * cweight (T.pX c e) y with hF
  have hθc : ContinuousOn (chartTheta (T.pX c e) u) V :=
    (continuousOn_chartTheta' hA ((T.contDiffOn_pX c e).mono hAd) hu).mono hVA
  have hθ'c : ContinuousOn (fun y => chartTheta (T.pX c' e') u' (chg c c' y)) V :=
    (continuousOn_chartTheta' hA' ((T.contDiffOn_pX c' e').mono hA'd) hu').comp
      ((differentiableOn_chg c c').continuousOn.mono hVo') hVA'
  have hFc : ContinuousOn F V := by
    refine (Complex.continuous_conj.comp_continuousOn
      (hθc.sub (hθ'c.div htV.continuousOn ht0))).mul ?_
    exact (continuousOn_cweight (T.contDiffOn_pX c e)).mono hVpd
  -- the integral identity
  have hint : ∀ g : ComplexModel n → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ V → ∫ y, g y • F y = 0 := by
    intro g hg hgc hgV
    have hEq := T.integral_test_eq hA hA' hAd hA'd hu hu' (fun y hy => hVS hy) hVA' hVrel
      g hg hgc hgV
    have hcont : ∀ f : ComplexModel n → ℂ, ContinuousOn f V →
        Integrable (fun y => (g y : ℂ) * conj (f y) * cweight (T.pX c e) y) := by
      intro f hf
      have hcw : ContinuousOn (cweight (T.pX c e)) V :=
        (continuousOn_cweight (T.contDiffOn_pX c e)).mono hVpd
      refine (continuous_of_continuousOn_of_eq_zero hVo
        (((Complex.continuous_ofReal.comp hg.continuous).continuousOn.mul
          (Complex.continuous_conj.comp_continuousOn hf)).mul hcw) (isClosed_tsupport g) hgV
        fun y hy => by simp [image_eq_zero_of_notMem_tsupport hy]).integrable_of_hasCompactSupport
        ?_
      exact (hgc.comp_left Complex.ofReal_zero).mul_right.mul_right
    have hsplit : (fun y => g y • F y) = fun y =>
        (g y : ℂ) * conj (chartTheta (T.pX c e) u y) * cweight (T.pX c e) y -
        (g y : ℂ) * conj (chartTheta (T.pX c' e') u' (chg c c' y) / t y) *
          cweight (T.pX c e) y := by
      funext y
      simp only [hF, map_sub, Complex.real_smul]
      ring
    rw [hsplit, integral_sub (hcont _ hθc)
      (hcont (fun y => chartTheta (T.pX c' e') u' (chg c c' y) / t y)
        (hθ'c.div htV.continuousOn ht0)), hEq, sub_self]
  have hae := hVo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hFc.locallyIntegrableOn hVo.measurableSet) hint
  have hae' : F =ᵐ[volume.restrict V] 0 := by
    rw [EventuallyEq, ae_restrict_iff' hVo.measurableSet]
    exact hae
  have hF0 : F z = 0 := Measure.eqOn_open_of_ae_eq hae' hVo hFc continuousOn_const hzV
  have hcw : cweight (T.pX c e) z ≠ 0 := by
    rw [cweight]; exact_mod_cast (Real.exp_pos _).ne'
  have h1 : chartTheta (T.pX c e) u z -
      chartTheta (T.pX c' e') u' (chg c c' z) / t z = 0 := by
    have := (mul_eq_zero.mp hF0).resolve_right hcw
    rwa [map_eq_zero] at this
  have h2 := sub_eq_zero.mp h1
  change _ = t z * _
  rw [h2]
  field_simp [ht0 z hzV]

end TwistedDatum

end SGPT.Trace.TwistedL2
