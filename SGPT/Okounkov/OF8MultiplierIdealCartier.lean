import SGPT.Okounkov.OF8InftyIdealModification
import SGPT.Okounkov.OkoNSInfty
import SGPT.Okounkov.TranscendentalL2Extension
import SGPT.PSH.BookDeep2LelongBound
import SGPT.NAPotential.BJPrepLelongConvex
import SGPT.Foundations.Analysis.Pending.MultiplierIdealBergmanNadelManifold

/-!
# Multiplier ideals of logarithmic `ℚ`-divisors at integral levels

Source: chapter *The theory of Okounkov bodies*, remark `rmk:DeltaanaW0` (and its uses in
`prop:birinvO`, `prop:suba`, `prop:res`): on a modification `Y` on which `π^*φ` has log
singularities along an effective `ℚ`-divisor `D`, the multiplier ideals of `π^*φ` are
computed by `D`: `𝓘(k π^*φ) = 𝒪_Y(-kD)` whenever `kD` is integral.

If `D = (1/d) F` with `F` an effective (Cartier) divisor and `u` has log singularities along `D`
(book Definition 1.6.2), then locally `d u = log |h|² + O(1)` with `h` a local equation of `F`,
and for every `k ≥ 1`

`𝓘(dk · u) = 𝒪(-kF)`   (`multiplierIdeal_mem_iff_nsmul_ideal`).

`⊇`: `𝒪(-kF) = 𝓘_∞(dk u) ⊆ 𝓘(dk u)` (`SGPT.Okounkov.OF8.nsmul_ideal_mem_iff_inftyIdeal`,
`SGPT.Okounkov.OkoNS.inftyIdeal_le_multiplierIdeal'`). `⊆` is the `L²` Riemann extension
theorem (`SGPT.Okounkov.TranscendentalL2.exists_extension_of_locally_sq_integrable`): if
`∫ |f|² e^{-dk u} < ∞` near `z`, then `f / h^k` is holomorphic off `{h = 0}` with
`|f/h^k|² ≤ C |f|² e^{-dk u}`, hence extends holomorphically, so `f ∈ (h^k)`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.OF8

open Set Filter MeasureTheory Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.PSH
open scoped Topology Manifold ContDiff ENNReal

variable {m : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z]
  [IsComplexManifold (m + 1) Z]

/-- `k · (d · x) = (dk) · x` in `EReal` for natural `d, k`. -/
theorem ereal_natCast_mul_natCast_mul (d k : ℕ) (x : EReal) :
    (k : EReal) * ((d : EReal) * x) = (((d * k : ℕ) : ℝ) : EReal) * x := by
  rw [← mul_assoc]
  congr 1
  rw [mul_comm]
  push_cast
  rfl

omit [IsComplexManifold (m + 1) Z] in
/-- The multiplier ideal with coefficient `c` is the multiplier ideal of `c u` with
coefficient `1`. -/
theorem multiplierIdeal_mem_iff_one {c : ℝ} (hc : 0 < c) (u : Z → EReal) (z : Z) (f : Z → ℂ) :
    (multiplierIdeal (n := m + 1) c u).mem z f ↔
      (multiplierIdeal (n := m + 1) 1 (fun y => (c : EReal) * u y)).mem z f := by
  have hdens : ∀ (e : ComplexChart (m + 1) Z) (g : ComplexModel (m + 1) → ℂ),
      multiplierDensity (chartFunction u e) c g =
        multiplierDensity (chartFunction (fun y => (c : EReal) * u y) e) 1 g := by
    intro e g
    funext w
    simp only [multiplierDensity, multiplierWeight, chartFunction, EReal.coe_one, one_mul]
  constructor
  · rintro ⟨hf, -, U, hU, hzU, hdf, hmeas, hint⟩
    refine ⟨hf, one_pos, U, hU, hzU, hdf, ?_, ?_⟩
    · rw [← hdens]; exact hmeas
    · rw [← hdens]; exact hint
  · rintro ⟨hf, -, U, hU, hzU, hdf, hmeas, hint⟩
    refine ⟨hf, hc, U, hU, hzU, hdf, ?_, ?_⟩
    · rw [hdens]; exact hmeas
    · rw [hdens]; exact hint

/-- Real form of the density comparison: where `h ≠ 0` and `d u = log |h|² + d b`,
`|f / h^k|² = |f|² e^{-dk u} · e^{dk b}`. -/
theorem norm_div_pow_sq_eq {d k : ℕ} (hd : 0 < d) {fz hz : ℂ} (hh : hz ≠ 0) (bz : ℝ) :
    ‖fz / hz ^ k‖ ^ 2 =
      ‖fz‖ ^ 2 * Real.exp (-(((d * k : ℕ) : ℝ) *
        (((1 / (d : ℚ) : ℚ) : ℝ) * Real.log (‖hz‖ ^ 2) + bz))) *
        Real.exp (((d * k : ℕ) : ℝ) * bz) := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hnpos : 0 < ‖hz‖ ^ 2 := by positivity
  have hcoef : ((d * k : ℕ) : ℝ) * ((1 / (d : ℚ) : ℚ) : ℝ) = (k : ℝ) := by
    push_cast
    field_simp
  have hexp : Real.exp (-(((d * k : ℕ) : ℝ) *
      (((1 / (d : ℚ) : ℚ) : ℝ) * Real.log (‖hz‖ ^ 2) + bz))) * Real.exp (((d * k : ℕ) : ℝ) * bz) =
      Real.exp (-((k : ℝ) * Real.log (‖hz‖ ^ 2))) := by
    rw [← Real.exp_add]
    congr 1
    rw [mul_add, ← mul_assoc, hcoef]
    ring
  rw [mul_assoc, hexp, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hnpos, norm_div, norm_pow,
    div_pow]
  have hz0 : ‖hz‖ ≠ 0 := norm_ne_zero_iff.mpr hh
  field_simp
  ring

/-- **`𝓘(dk u) ⊆ 𝒪(-kF)`** by the `L²` Riemann extension theorem (see the module docstring).
Here `h` is a local equation of `F` at `z` on the open set `U₀` (holomorphic, vanishing
identically on no open subset), and `d u = log |h|² + d b` near `z` with `b` bounded. -/
theorem mem_generatorPower_of_mem_multiplierIdeal {d k : ℕ} (hd : 0 < d) (hk : 0 < k) {u : Z → EReal}
    {z : Z} {U₀ : Set Z} (hU₀ : IsOpen U₀) (hzU₀ : z ∈ U₀) {h : Z → ℂ}
    (hhol : MDifferentiableOn 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) h U₀)
    (hdense : ∀ W : Set Z, IsOpen W → W ⊆ U₀ → W.Nonempty → ∃ y ∈ W, h y ≠ 0)
    {b : Z → ℝ} (hb : BoundedRealGermAt b z)
    (hlog : u =ᶠ[𝓝 z] fun y => (((1 / (d : ℚ) : ℚ) : ℝ) : EReal) * logNormSq (h y) + (b y : EReal))
    {f : Z → ℂ} (hf : (multiplierIdeal (n := m + 1) ((d * k : ℕ) : ℝ) u).mem z f) :
    ∃ a : Z → ℂ, HolomorphicAt (m + 1) a z ∧ f =ᶠ[𝓝 z] fun y => a y * h y ^ k := by
  classical
  set c : ℝ := ((d * k : ℕ) : ℝ) with hcdef
  set e := complexChartAt (n := m + 1) z with hedef
  obtain ⟨-, -, U, hU, hzU, hdf, -, hint⟩ := hf
  obtain ⟨C, hC, hbC⟩ := hb
  -- an open neighbourhood `W` of `z` on which everything holds
  obtain ⟨W, hWsub, hWo, hzW⟩ := _root_.mem_nhds_iff.mp
    ((hbC.and hlog).and (hU₀.mem_nhds hzU₀))
  set V : Set (ComplexModel (m + 1)) :=
    (e.val.target ∩ e.val.symm ⁻¹' (W ∩ e.val.source)) ∩ U with hVdef
  have hVo : IsOpen V :=
    (e.val.isOpen_inter_preimage_symm (hWo.inter e.val.open_source)).inter hU
  have hzs : z ∈ e.val.source := mem_complexChartAt_source z
  have hzV : e.val z ∈ V := by
    refine ⟨⟨e.val.map_source hzs, ?_⟩, hzU⟩
    rw [mem_preimage, e.val.left_inv hzs]
    exact ⟨hzW, hzs⟩
  have hVW : ∀ w ∈ V, e.val.symm w ∈ W := fun w hw => hw.1.2.1
  have hVt : ∀ w ∈ V, w ∈ e.val.target := fun w hw => hw.1.1
  set K : ComplexModel (m + 1) → ℂ := fun w => h (e.val.symm w) with hKdef
  have hKd : DifferentiableOn ℂ K V := by
    have h0 := differentiableOn_comp_chartSymm (n := m + 1) z hhol
    exact h0.mono fun w hw => ⟨hVt w hw, (hWsub (hVW w hw)).2⟩
  -- `K` vanishes identically near no point of `V`
  have hkne : ∀ w ∈ V, ¬ ∀ᶠ y in 𝓝 w, K y = 0 := by
    intro w hw hev
    obtain ⟨O, hOsub, hOo, hwO⟩ := _root_.mem_nhds_iff.mp (hev.and (hVo.mem_nhds hw))
    have hOt : O ⊆ e.val.target := fun y hy => hVt y (hOsub hy).2
    have himg : IsOpen (e.val.symm '' O) := e.val.isOpen_image_symm_of_subset_target hOo hOt
    obtain ⟨y, ⟨w', hw'O, rfl⟩, hy⟩ := hdense _ himg
      (by rintro _ ⟨w', hw'O, rfl⟩; exact (hWsub (hVW w' (hOsub hw'O).2)).2)
      ⟨_, w, hwO, rfl⟩
    exact hy (hOsub hw'O).1
  -- the quotient `f / h^k` in the chart
  set Fq : ComplexModel (m + 1) → ℂ := fun w => f (e.val.symm w) / K w ^ k with hFqdef
  have hFq : DifferentiableOn ℂ Fq (V ∩ {w | K w ≠ 0}) := by
    intro w hw
    have h1 : DifferentiableWithinAt ℂ (fun w => f (e.val.symm w)) (V ∩ {w | K w ≠ 0}) w :=
      (hdf w hw.1.2).mono fun y (hy : y ∈ V ∩ {w | K w ≠ 0}) => hy.1.2
    have h2 : DifferentiableWithinAt ℂ (fun w => K w ^ k) (V ∩ {w | K w ≠ 0}) w :=
      ((hKd w hw.1).pow k).mono fun y (hy : y ∈ V ∩ {w | K w ≠ 0}) => hy.1
    have h3 := h1.fun_mul (h2.fun_inv (pow_ne_zero k hw.2))
    simpa [Fq, div_eq_mul_inv] using h3
  -- pointwise comparison with the weighted density
  have hpt : ∀ w ∈ V, ENNReal.ofReal (‖Fq w‖ ^ 2) ≤
      ENNReal.ofReal (Real.exp (c * C)) *
        multiplierDensity (chartFunction u e) c (fun w => f (e.val.symm w)) w := by
    intro w hw
    by_cases hK : K w = 0
    · simp [Fq, hK, zero_pow hk.ne']
    · obtain ⟨⟨hbw, huw⟩, -⟩ := hWsub (hVW w hw)
      have hlogK : logNormSq (h (e.val.symm w)) = (Real.log (‖K w‖ ^ 2) : EReal) :=
        logNormSq_of_ne_zero hK
      have hu' : chartFunction u e w = ((((1 / (d : ℚ) : ℚ) : ℝ) * Real.log (‖K w‖ ^ 2) +
          b (e.val.symm w) : ℝ) : EReal) := by
        change u (e.val.symm w) = _
        rw [huw]
        dsimp only
        rw [hlogK, ← EReal.coe_mul, ← EReal.coe_add]
      rw [multiplierDensity, hu', multiplierWeight_coe, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [norm_div_pow_sq_eq hd hK (b (e.val.symm w))]
      have hexp : Real.exp (c * b (e.val.symm w)) ≤ Real.exp (c * C) := by
        apply Real.exp_le_exp.mpr
        have hc0 : 0 ≤ c := Nat.cast_nonneg _
        exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans hbw) hc0
      have hA : 0 ≤ ‖f (e.val.symm w)‖ ^ 2 * Real.exp (-(c *
          (((1 / (d : ℚ) : ℚ) : ℝ) * Real.log (‖K w‖ ^ 2) + b (e.val.symm w)))) := by positivity
      calc ‖f (e.val.symm w)‖ ^ 2 * Real.exp (-(c *
            (((1 / (d : ℚ) : ℚ) : ℝ) * Real.log (‖K w‖ ^ 2) + b (e.val.symm w)))) *
            Real.exp (c * b (e.val.symm w))
          ≤ ‖f (e.val.symm w)‖ ^ 2 * Real.exp (-(c *
            (((1 / (d : ℚ) : ℚ) : ℝ) * Real.log (‖K w‖ ^ 2) + b (e.val.symm w)))) *
            Real.exp (c * C) := mul_le_mul_of_nonneg_left hexp hA
        _ = _ := by ring
  -- local `L²` bounds on balls in `V`
  have hL2 : ∀ w ∈ V, ∃ r > 0, ball w r ⊆ V ∧
      ∫⁻ y in ball w r, ENNReal.ofReal (‖Fq y‖ ^ 2) ≠ ⊤ := by
    intro w hw
    obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hVo w hw
    refine ⟨r, hr, hrV, ?_⟩
    apply ne_top_of_lt
    calc ∫⁻ y in ball w r, ENNReal.ofReal (‖Fq y‖ ^ 2)
        ≤ ∫⁻ y in ball w r, ENNReal.ofReal (Real.exp (c * C)) *
            multiplierDensity (chartFunction u e) c (fun w => f (e.val.symm w)) y :=
          setLIntegral_mono' measurableSet_ball fun y hy => hpt y (hrV hy)
      _ = ENNReal.ofReal (Real.exp (c * C)) * ∫⁻ y in ball w r,
            multiplierDensity (chartFunction u e) c (fun w => f (e.val.symm w)) y :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Real.exp (c * C)) * ∫⁻ y in U,
            multiplierDensity (chartFunction u e) c (fun w => f (e.val.symm w)) y := by
          exact mul_le_mul' le_rfl (lintegral_mono_set fun y hy => (hrV hy).2)
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint
  obtain ⟨G, hG, hGF⟩ := TranscendentalL2.exists_extension_of_locally_sq_integrable hVo hKd hkne
    hFq hL2
  -- `f ∘ e.symm = G · K^k` on `V`
  have heqV : EqOn (fun w => f (e.val.symm w)) (fun w => G w * K w ^ k) V := by
    have hs : EqOn (fun w => f (e.val.symm w)) (fun w => G w * K w ^ k) (V ∩ {w | K w ≠ 0}) := by
      intro w hw
      change f (e.val.symm w) = G w * K w ^ k
      rw [hGF hw]
      change f (e.val.symm w) = f (e.val.symm w) / K w ^ k * K w ^ k
      rw [div_mul_cancel₀ _ (pow_ne_zero k hw.2)]
    refine hs.of_subset_closure ((hdf.mono fun w hw => hw.2).continuousOn)
      ((hG.mul (hKd.pow k)).continuousOn) inter_subset_left ?_
    intro w hw
    rw [mem_closure_iff_frequently]
    have hfreq : ∃ᶠ y in 𝓝 w, K y ≠ 0 := Filter.not_eventually.mp (hkne w hw)
    exact (hfreq.and_eventually (hVo.mem_nhds hw)).mono fun y hy => ⟨hy.2, hy.1⟩
  -- back on `Z`
  refine ⟨fun y => G (e.val y), ?_, ?_⟩
  · refine MultiplierIdealBergmanNadelManifold.holomorphicAt_comp_chart hzs ?_
    filter_upwards [hVo.mem_nhds hzV] with w hw
    exact (hG w hw).differentiableAt (hVo.mem_nhds hw)
  · have hpre : e.val.source ∩ e.val ⁻¹' V ∈ 𝓝 z :=
      Filter.inter_mem (e.val.open_source.mem_nhds hzs)
        ((e.val.continuousAt hzs).preimage_mem_nhds (hVo.mem_nhds hzV))
    filter_upwards [hpre] with y hy
    have h1 := heqV hy.2
    simp only [hKdef, e.val.left_inv hy.1] at h1
    exact h1

/-- **`𝓘(dk · u) = 𝒪(-kF)`.** If `u` has log singularities along the effective `ℚ`-divisor `D`
(book Definition 1.6.2) and `D = (1/d) F` with `F` an effective divisor, then for every
`k ≥ 1` the multiplier ideal of `dk · u` is the ideal of the divisor `kF`. -/
theorem multiplierIdeal_mem_iff_nsmul_ideal {D : EffectiveGeometricQDivisor (m + 1) Z}
    {u : Z → EReal} (hu : NativeHasLogSingularitiesAlong D u) (F : EffectiveDivisor (m + 1) Z)
    {d : ℕ} (hd : 0 < d)
    (hDF : D = cartierGeometricQDivisor F (1 / (d : ℚ)) (by positivity)) {k : ℕ} (hk : 0 < k)
    (z : Z) (f : Z → ℂ) :
    (multiplierIdeal (n := m + 1) ((d * k : ℕ) : ℝ) u).mem z f ↔ (k • F).ideal.mem z f := by
  obtain ⟨U, hU, hzU, h, hhol, hdense, hgen⟩ := F.isInvertible z
  have hhz : HolomorphicAt (m + 1) h z :=
    InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU hhol hzU
  have hcoeff : ∀ Q, D.coefficient Q = (cartierGeometricPrimeCoefficient F Q : ℚ) / (d : ℚ) := by
    intro Q
    rw [hDF, cartierGeometricQDivisor_coefficient]
    ring
  obtain ⟨b, hb, hlog⟩ :=
    OkoNov16.AttributedGeometricLogReuse.exists_log_germ_of_global_cartier_coefficients
      hu F d hd hcoeff z h hhz (hgen z hzU)
  constructor
  · intro hf
    exact (nsmul_ideal_mem_iff_of_generator F hhz (hgen z hzU) k f).mpr
      ⟨hf.1, mem_generatorPower_of_mem_multiplierIdeal hd hk hU hzU hhol hdense hb hlog hf⟩
  · intro hf
    have h2 := (nsmul_ideal_mem_iff_inftyIdeal hu F hd hDF k z f).mp hf
    obtain ⟨θ', hθ'⟩ := hu.1
    have hQ : ManifoldQuasiPlurisubharmonic (n := m + 1) u :=
      BookDeep2LelongBound.manifoldQuasiPlurisubharmonic_of_isThetaPSH hθ'
    have hcpos : (0 : ℝ) < ((d * k : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hd hk
    have hQ' : ManifoldQuasiPlurisubharmonic (n := m + 1)
        (fun y => ((((d * k : ℕ) : ℝ)) : EReal) * u y) :=
      SGPT.NAPotential.BJPrep.manifoldQuasiPlurisubharmonic_const_mul hQ hcpos
    have hfun : (fun y => (k : EReal) * ((d : EReal) * u y)) =
        fun y => ((((d * k : ℕ) : ℝ)) : EReal) * u y :=
      funext fun y => ereal_natCast_mul_natCast_mul d k (u y)
    rw [hfun] at h2
    exact (multiplierIdeal_mem_iff_one hcpos u z f).mpr
      (OkoNS.inftyIdeal_le_multiplierIdeal' hQ' z f h2)

end SGPT.Okounkov.OF8
