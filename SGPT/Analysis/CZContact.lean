import SGPT.Analysis.CZMeanValue
import SGPT.Okounkov.TranscendentalWNRegDensityPoint
import SGPT.Foundations.Analysis.Pending.SemiconcaveTaylor

/-!
# Second-order contact for functions with bounded Laplacian

Lane C11-REAL (`claude-c11-real`, nodes `c11r:coincide`, `c11r:contact-flat`,
`c11r:contact-second-order`).  The real-analysis core of the first assertion of the book's
`lma:DNTroof` (`references/sgpt-d3f272c3/source/author/chapter_npp.tex`): two functions with
bounded Laplacian, one below the other, **coincide up to second order at almost every point of
their contact set**.

* `CoincideToSecondOrderAt f g x` — `f(x) = g(x)` and `f(x + h) - g(x + h) = o(‖h‖²)`: `f` and
  `g` have the same second-order Taylor expansion at `x`.  If one of them has a second-order
  (Peano) expansion at `x` (TN's `HasPeanoExpansionAt`), so has the other, with the same linear
  and quadratic parts (`CoincideToSecondOrderAt.hasPeanoExpansionAt`).
* `ae_isLittleO_of_nonneg` — **second-order flatness on the zero set**: if `w ≥ 0` is continuous
  on an open `U ⊆ ℂⁿ` with locally bounded distributional Laplacian, then
  `w(x + h) = o(‖h‖²)` at almost every point `x ∈ U` with `w(x) = 0`.
* `ae_coincideToSecondOrderAt_of_le` — the contact form: for `u ≤ f` continuous with locally
  bounded Laplacian, `u` and `f` coincide up to second order at a.e. point of `{u = f}`.
* `hasLocallyBoundedLeviTraceOn_of_complexHessian` — a locally bounded distributional complex
  Hessian (WN-REG's `HasLocallyBoundedComplexHessianOn`) has a locally bounded Laplacian.

## Proof (no Calderón–Zygmund theory, no Stampacchia lemma)

The book obtains the contact statement from `W^{2,1}` regularity, a.e. existence of the
classical Hessian and Stampacchia's lemma.  Here only mean-value inequalities are used
(`SGPT.Analysis.CZMeanValue`).  Let `|Δw| ≤ 4M` near `x` and `Z = {w = 0}`.

1. *Quadratic averages on `Z`*: at `y ∈ Z` the super-mean value inequality gives
   `∫_{B̄(y,s)} w ≤ C s² vol B̄(y, s)`.
2. *Integral flatness at density points* (WN-REG's `eventually_setLIntegral_le_of_density`): at a
   Lebesgue density point `x` of `Z`, `∫_{B̄(x,r)} w = o(r² vol B̄(x, r))`.
3. *Pointwise flatness*: for `y = x + h`, `r = ‖h‖` and a small fixed `δ`, the sub-mean value
   inequality at `y` with radius `δr` gives
   `w(y) ≤ (∫_{B̄(x,2r)} w) / vol B̄(0, δr/2) + (M/n) δ² r² = o(r²) + (M/n) δ² r²`.

Almost every point of `Z` is a density point, which proves the claim.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric Asymptotics
open scoped Topology ContDiff ENNReal

namespace SGPT.Analysis.CZ

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HolomorphicPullback
open SGPT.Foundations.Analysis.Pending.RadialLeviPreimage
open SGPT.Okounkov.TranscendentalWNReg

/-! ### Coincidence up to second order -/

section Coincide

variable {E : Type*} [NormedAddCommGroup E]

/-- **`f` and `g` coincide up to second order at `x`**: `f(x) = g(x)` and
`f(x + h) - g(x + h) = o(‖h‖²)` as `h → 0`. -/
def CoincideToSecondOrderAt (f g : E → ℝ) (x : E) : Prop :=
  f x = g x ∧ (fun h => f (x + h) - g (x + h)) =o[𝓝 0] (fun h => ‖h‖ ^ 2)

theorem CoincideToSecondOrderAt.refl (f : E → ℝ) (x : E) : CoincideToSecondOrderAt f f x :=
  ⟨rfl, by simpa only [sub_self] using isLittleO_zero (fun h : E => ‖h‖ ^ 2) (𝓝 0)⟩

theorem CoincideToSecondOrderAt.symm {f g : E → ℝ} {x : E} (h : CoincideToSecondOrderAt f g x) :
    CoincideToSecondOrderAt g f x := by
  refine ⟨h.1.symm, ?_⟩
  have := h.2.neg_left
  simpa only [neg_sub] using this

theorem CoincideToSecondOrderAt.trans {f g k : E → ℝ} {x : E} (h₁ : CoincideToSecondOrderAt f g x)
    (h₂ : CoincideToSecondOrderAt g k x) : CoincideToSecondOrderAt f k x := by
  refine ⟨h₁.1.trans h₂.1, ?_⟩
  have := h₁.2.add h₂.2
  simpa only [sub_add_sub_cancel] using this

end Coincide

/-- Functions that coincide up to second order have the same second-order Peano expansion. -/
theorem CoincideToSecondOrderAt.hasPeanoExpansionAt {n : ℕ} {f g : ComplexModel n → ℝ}
    {x : ComplexModel n} (h : CoincideToSecondOrderAt f g x)
    {L : ComplexModel n →L[ℝ] ℝ} {A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (hf : SemiconcaveHessian.HasPeanoExpansionAt f x L A) :
    SemiconcaveHessian.HasPeanoExpansionAt g x L A := by
  intro ε hε
  have h2 := isLittleO_iff.mp h.2 (half_pos hε)
  filter_upwards [hf (ε / 2) (half_pos hε), h2] with k hk hk2
  rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ‖k‖ ^ 2), Real.norm_eq_abs] at hk2
  rw [← h.1]
  calc |g (x + k) - f x - L k - A k k / 2|
      = |(f (x + k) - f x - L k - A k k / 2) - (f (x + k) - g (x + k))| := by ring_nf
    _ ≤ |f (x + k) - f x - L k - A k k / 2| + |f (x + k) - g (x + k)| := abs_sub _ _
    _ ≤ ε / 2 * ‖k‖ ^ 2 + ε / 2 * ‖k‖ ^ 2 := add_le_add hk hk2
    _ = ε * ‖k‖ ^ 2 := by ring

variable {n : ℕ}

/-! ### From a bounded complex Hessian to a bounded Laplacian -/

theorem integrable_mul_coordinateLeviTrace {g φ : ComplexModel n → ℝ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hg : ContinuousOn g U) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) : Integrable (fun z => g z * coordinateLeviTrace φ z) := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  exact integrable_mul_of_continuousOn hU hg (continuous_coordinateLeviTrace hφ2)
    (hφc.mono' fun x hx => tsupport_coordinateLeviTrace_subset (subset_tsupport _ hx))
    (tsupport_coordinateLeviTrace_subset.trans hφU)

/-- A locally bounded distributional complex Hessian gives a locally bounded Laplacian. -/
theorem hasLocallyBoundedLeviTraceOn_of_complexHessian {g : ComplexModel n → ℝ}
    {U : Set (ComplexModel n)} (hU : IsOpen U) (hg : ContinuousOn g U)
    (h : HasLocallyBoundedComplexHessianOn g U) : HasLocallyBoundedLeviTraceOn g U := by
  intro K hK hKU
  obtain ⟨C, hC⟩ := h K hK hKU
  refine ⟨n * C, fun φ hφ hφK => ?_⟩
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hφc : HasCompactSupport φ := hK.of_isClosed_subset (isClosed_tsupport _) hφK
  have hint : ∀ j : Fin n, Integrable (fun z => g z * leviForm φ z (coordinateVector j)) := by
    intro j
    have hc : Continuous (fun z => leviForm φ z (coordinateVector j)) :=
      ((continuous_realHessian hφ2 _ _).add (continuous_realHessian hφ2 _ _)).div_const _
    have hsub : Function.support (fun z => leviForm φ z (coordinateVector j)) ⊆ tsupport φ := by
      intro x hx
      by_contra hxs
      apply hx
      have h0 : iteratedFDeriv ℝ 2 φ x = 0 := by
        by_contra hne
        exact hxs (support_iteratedFDeriv_subset (𝕜 := ℝ) (n := 2) (f := φ) hne)
      simp [leviForm, realHessian, h0]
    exact integrable_mul_of_continuousOn hU hg hc (hφc.mono' hsub)
      ((closure_minimal hsub (isClosed_tsupport φ)).trans (hφK.trans hKU))
  have hsum : ∫ z, g z * coordinateLeviTrace φ z =
      ∑ j : Fin n, ∫ z, g z * leviForm φ z (coordinateVector j) := by
    rw [← integral_finsetSum _ fun j _ => hint j]
    congr 1
    funext z
    rw [coordinateLeviTrace, Finset.mul_sum]
  rw [hsum]
  calc |∑ j : Fin n, ∫ z, g z * leviForm φ z (coordinateVector j)|
      ≤ ∑ j : Fin n, |∫ z, g z * leviForm φ z (coordinateVector j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, C * ∫ z, |φ z| := by
        refine Finset.sum_le_sum fun j _ => ?_
        have := hC φ hφ hφK (coordinateVector j)
        rwa [norm_coordinateVector, one_pow, mul_one] at this
    _ = n * C * ∫ z, |φ z| := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The difference of two functions with locally bounded Laplacian has locally bounded
Laplacian. -/
theorem HasLocallyBoundedLeviTraceOn.sub {g₁ g₂ : ComplexModel n → ℝ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hg₁ : ContinuousOn g₁ U) (hg₂ : ContinuousOn g₂ U)
    (h₁ : HasLocallyBoundedLeviTraceOn g₁ U) (h₂ : HasLocallyBoundedLeviTraceOn g₂ U) :
    HasLocallyBoundedLeviTraceOn (fun z => g₁ z - g₂ z) U := by
  intro K hK hKU
  obtain ⟨M₁, hM₁⟩ := h₁ K hK hKU
  obtain ⟨M₂, hM₂⟩ := h₂ K hK hKU
  refine ⟨M₁ + M₂, fun φ hφ hφK => ?_⟩
  have hφc : HasCompactSupport φ := hK.of_isClosed_subset (isClosed_tsupport _) hφK
  have i₁ := integrable_mul_coordinateLeviTrace hU hg₁ hφ hφc (hφK.trans hKU)
  have i₂ := integrable_mul_coordinateLeviTrace hU hg₂ hφ hφc (hφK.trans hKU)
  have hsplit : ∫ z, (g₁ z - g₂ z) * coordinateLeviTrace φ z =
      (∫ z, g₁ z * coordinateLeviTrace φ z) - ∫ z, g₂ z * coordinateLeviTrace φ z := by
    rw [← integral_sub i₁ i₂]
    congr 1
    funext z
    ring
  rw [hsplit, add_mul]
  exact (abs_sub _ _).trans (add_le_add (hM₁ φ hφ hφK) (hM₂ φ hφ hφK))

/-! ### Second-order flatness on the zero set -/

/-- Measure of closed balls in `ℂⁿ` in real form. -/
theorem volume_real_closedBall_eq (x : ComplexModel n) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (closedBall x r) =
      r ^ Module.finrank ℝ (ComplexModel n) * volume.real (ball (0 : ComplexModel n) 1) :=
  Measure.addHaar_real_closedBall volume x hr

/-- **Second-order flatness on the zero set, local form.**  Let `w ≥ 0` be continuous on
`B(c, 8ρ)` with distributional Levi trace between `-M` and `M` there.  Then at almost every
point `x ∈ B(c, ρ)` with `w(x) = 0`, `w(x + h) = o(‖h‖²)`. -/
theorem ae_isLittleO_of_nonneg_ball (hn : 0 < n) {w : ComplexModel n → ℝ} {c : ComplexModel n}
    {ρ M : ℝ} (hρ : 0 < ρ) (hM0 : 0 ≤ M) (hw : ContinuousOn w (ball c (8 * ρ)))
    (hw0 : ∀ z ∈ ball c (8 * ρ), 0 ≤ w z) (hGE : LeviTraceGE w (ball c (8 * ρ)) M)
    (hLE : LeviTraceLE w (ball c (8 * ρ)) M) :
    ∀ᵐ x ∂volume, x ∈ ball c ρ → w x = 0 →
      (fun h => w (x + h)) =o[𝓝 0] (fun h => ‖h‖ ^ 2) := by
  classical
  set V : Set (ComplexModel n) := ball c (8 * ρ) with hVdef
  have hV : IsOpen V := isOpen_ball
  set d : ℕ := Module.finrank ℝ (ComplexModel n) with hd
  set u : ℝ := volume.real (ball (0 : ComplexModel n) 1) with hu
  have hu0 : 0 < u := by
    rw [hu, measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hball : ∀ {y : ComplexModel n} {r t : ℝ}, dist y c ≤ t → r + t < 8 * ρ →
      closedBall y r ⊆ V := by
    intro y r t hy hrt z hz
    rw [mem_closedBall] at hz
    rw [hVdef, mem_ball]
    linarith [dist_triangle z y c]
  -- the zero set inside the closed ball `B̄(c, ρ)`
  set S : Set (ComplexModel n) := closedBall c ρ ∩ w ⁻¹' {0} with hSdef
  have hcV : closedBall c ρ ⊆ V := hball (r := ρ) (t := 0) (by simp) (by linarith)
  have hSc : IsClosed S :=
    (hw.mono hcV).preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton
  have hS : MeasurableSet S := hSc.measurableSet
  -- the measurable nonnegative function used for the flatness lemma
  set B4 : Set (ComplexModel n) := closedBall c (4 * ρ) with hB4
  have hB4V : B4 ⊆ V := hball (r := 4 * ρ) (t := 0) (by simp) (by linarith)
  set G : ComplexModel n → ℝ≥0∞ := fun x => ENNReal.ofReal (B4.piecewise w 0 x) with hGdef
  have hGm : Measurable G :=
    ENNReal.measurable_ofReal.comp ((hw.mono hB4V).measurable_piecewise continuousOn_const
      isClosed_closedBall.measurableSet)
  have hGeq : ∀ x ∈ B4, G x = ENNReal.ofReal (w x) := fun x hx => by
    simp only [hGdef, piecewise_eq_of_mem _ _ _ hx]
  -- integrals of `w` over small balls as lintegrals of `G`
  have hlint : ∀ {y : ComplexModel n} {r : ℝ}, closedBall y r ⊆ B4 →
      ∫⁻ x in closedBall y r, G x = ENNReal.ofReal (∫ x in closedBall y r, w x) := by
    intro y r hsub
    have hint : IntegrableOn w (closedBall y r) :=
      ((hw.mono (hsub.trans hB4V)).integrableOn_compact (isCompact_closedBall y r))
    rw [ofReal_integral_eq_lintegral_ofReal hint]
    · exact setLIntegral_congr_fun measurableSet_closedBall fun x hx => hGeq x (hsub hx)
    · filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
      exact hw0 x (hB4V (hsub hx))
  -- Step 1: quadratic averages at the points of `S`
  set C : ℝ := 4 * M / n * 2 ^ d with hCdef
  have hC0 : 0 ≤ C := by positivity
  have hquad : ∀ y ∈ S, ∀ s : ℝ, 0 < s → s < ρ →
      ∫ x in closedBall y s, w x ≤ C * s ^ 2 * volume.real (closedBall y s) := by
    intro y hy s hs hsρ
    have hyc : dist y c ≤ ρ := hy.1
    have hyw : w y = 0 := hy.2
    have h2s : (0 : ℝ) < 2 * s := by positivity
    have hsub : closedBall y (2 * s) ⊆ V := hball hyc (by linarith)
    have hsup := kernelAverage_sub_le hn hV hw hM0 hLE h2s hsub
    have hlow := setIntegral_div_le_kernelAverage hV hw h2s hsub
      (fun z hz => hw0 z (hsub hz))
    rw [show 2 * s / 2 = s by ring] at hlow
    set A := ∫ z, w z * explicitRadialKernel (2 * s) h2s 0 (z - y) with hA
    have hX0 : 0 ≤ ∫ x in closedBall y s, w x := by
      refine setIntegral_nonneg measurableSet_closedBall fun z hz => hw0 z (hsub ?_)
      exact closedBall_subset_closedBall (by linarith) hz
    have hvb : 0 < volume.real (ball (0 : ComplexModel n) (2 * s)) := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos (measure_ball_pos volume _ h2s).ne' measure_ball_lt_top.ne
    have hvbc : volume.real (ball (0 : ComplexModel n) (2 * s)) ≤
        volume.real (closedBall (0 : ComplexModel n) (2 * s)) :=
      measureReal_mono ball_subset_closedBall measure_closedBall_lt_top.ne
    have hA0 : 0 ≤ A := (div_nonneg hX0 hvb.le).trans hlow
    have hX : ∫ x in closedBall y s, w x ≤ A * volume.real (ball (0 : ComplexModel n) (2 * s)) :=
      (div_le_iff₀ hvb).mp hlow
    have hAle : A ≤ M / n * (2 * s) ^ 2 := by linarith
    rw [volume_real_closedBall_eq _ h2s.le] at hvbc
    rw [volume_real_closedBall_eq _ hs.le]
    calc ∫ x in closedBall y s, w x
        ≤ A * volume.real (ball (0 : ComplexModel n) (2 * s)) := hX
      _ ≤ A * ((2 * s) ^ d * u) := mul_le_mul_of_nonneg_left hvbc hA0
      _ ≤ (M / n * (2 * s) ^ 2) * ((2 * s) ^ d * u) :=
          mul_le_mul_of_nonneg_right hAle (by positivity)
      _ = C * s ^ 2 * (s ^ d * u) := by rw [hCdef, mul_pow, mul_pow]; ring
  -- density points
  have hdens := SGPT.Okounkov.TranscendentalWNReg.DensityPoint.ae_eventually_measure_closedBall_diff_le
    (μ := volume) hS
  rw [ae_restrict_iff' hS] at hdens
  filter_upwards [hdens] with z hz hzB hz0
  have hzS : z ∈ S := ⟨ball_subset_closedBall hzB, hz0⟩
  have hzc : dist z c ≤ ρ := ball_subset_closedBall hzB
  -- Step 2: integral flatness at `z`
  have hsub : ∀ y ∈ S, ∀ s : ℝ, 0 < s → dist y z + s < ρ →
      ∫⁻ x in closedBall y s, G x ≤ ENNReal.ofReal (C * s ^ 2) * volume (closedBall y s) := by
    intro y hy s hs hys
    have hsρ : s < ρ := by linarith [dist_nonneg (x := y) (y := z)]
    have hyc : dist y c ≤ ρ := hy.1
    have hB : closedBall y s ⊆ B4 := by
      intro x hx
      rw [mem_closedBall] at hx ⊢
      linarith [dist_triangle x y c]
    rw [hlint hB, ← ENNReal.ofReal_toReal (measure_closedBall_lt_top (x := y) (r := s)).ne,
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (hquad y hy s hs hsρ)
  have hflat := SGPT.Okounkov.TranscendentalWNReg.DensityPoint.eventually_setLIntegral_le_of_density
    (μ := volume) hGm hS hzS hC0 hρ hsub (hz hzS)
  -- Step 3: pointwise flatness
  rw [isLittleO_iff]
  intro ε hε
  set δ : ℝ := min 1 (ε / (2 * (M / n + 1))) with hδdef
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hMδ : M / n * δ ^ 2 ≤ ε / 2 := by
    have h1 : δ ≤ ε / (2 * (M / n + 1)) := min_le_right _ _
    have h2 : δ ^ 2 ≤ δ := by nlinarith
    have hMn : 0 ≤ M / n := by positivity
    have h3 : M / n * δ ≤ M / n * (ε / (2 * (M / n + 1))) := mul_le_mul_of_nonneg_left h1 hMn
    have h4 : M / n * (ε / (2 * (M / n + 1))) ≤ ε / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    calc M / n * δ ^ 2 ≤ M / n * δ := mul_le_mul_of_nonneg_left h2 hMn
      _ ≤ ε / 2 := h3.trans h4
  set q : ℝ := (4 / δ) ^ d with hqdef
  have hq0 : 0 < q := by positivity
  set ε' : ℝ := ε / (8 * q) with hε'def
  have hε' : 0 < ε' := by positivity
  obtain ⟨r₀, hr₀, hr₀sub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hflat ε' hε')
  have hr₀pos : 0 < r₀ := hr₀
  filter_upwards [ball_mem_nhds (0 : ComplexModel n) (lt_min (half_pos hr₀pos) hρ)] with h hh
  rw [mem_ball, dist_zero_right, lt_min_iff] at hh
  set r : ℝ := ‖h‖ with hrdef
  have hyV : z + h ∈ V := by
    rw [hVdef, mem_ball]
    have : dist (z + h) z = r := by rw [dist_eq_norm, add_sub_cancel_left]
    linarith [dist_triangle (z + h) z c]
  have hwy0 : 0 ≤ w (z + h) := hw0 _ hyV
  rw [Real.norm_eq_abs, abs_of_nonneg hwy0, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rcases (norm_nonneg h).eq_or_lt with hr0 | hrpos
  · have h0 : h = 0 := norm_eq_zero.mp hr0.symm
    rw [h0, add_zero, hz0]
    positivity
  -- the radius `R = δ r`
  set y : ComplexModel n := z + h with hydef
  have hyz : dist y z = r := by rw [hydef, dist_eq_norm, add_sub_cancel_left]
  set R : ℝ := δ * r with hRdef
  have hR : 0 < R := mul_pos hδ0 hrpos
  have hRr : R ≤ r := by rw [hRdef]; nlinarith
  have hyR : closedBall y R ⊆ V := hball (t := ρ + r)
    (by linarith [dist_triangle y z c]) (by linarith)
  have hsubmean := le_kernelAverage_add hn hV hw hM0 hGE hR hyR
  have hcomp := kernelAverage_le_setIntegral_div hV hw hR hyR (fun x hx => hw0 x (hyR hx))
  -- the ball `B̄(z, 2r)`
  have h2r : 2 * r ∈ Ioo 0 r₀ := ⟨by positivity, by linarith⟩
  have hfl := hr₀sub h2r
  have hzB4 : closedBall z (2 * r) ⊆ B4 := by
    intro x hx
    rw [mem_closedBall] at hx ⊢
    linarith [dist_triangle x z c]
  replace hfl : ∫⁻ x in closedBall z (2 * r), G x ≤
      ENNReal.ofReal (ε' * (2 * r) ^ 2) * volume (closedBall z (2 * r)) := hfl
  rw [hlint hzB4, ← ENNReal.ofReal_toReal (measure_closedBall_lt_top (x := z) (r := 2 * r)).ne,
    ← ENNReal.ofReal_mul (by positivity)] at hfl
  have hfl' : ∫ x in closedBall z (2 * r), w x ≤ ε' * (2 * r) ^ 2 *
      volume.real (closedBall z (2 * r)) := by
    have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hfl
    simpa [measureReal_def] using this
  have hyzball : closedBall y R ⊆ closedBall z (2 * r) := by
    intro x hx
    rw [mem_closedBall] at hx ⊢
    linarith [dist_triangle x y z]
  have hmono : ∫ x in closedBall y R, w x ≤ ∫ x in closedBall z (2 * r), w x := by
    refine setIntegral_mono_set ((hw.mono (hzB4.trans hB4V)).integrableOn_compact
      (isCompact_closedBall z _)) ?_ (Eventually.of_forall hyzball)
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    exact hw0 x (hB4V (hzB4 hx))
  have hvs : 0 < volume.real (closedBall (0 : ComplexModel n) (R / 2)) :=
    volume_real_closedBall_pos _ (half_pos hR)
  have hvol : volume.real (closedBall z (2 * r)) =
      q * volume.real (closedBall (0 : ComplexModel n) (R / 2)) := by
    rw [volume_real_closedBall_eq _ (by positivity), volume_real_closedBall_eq _ (by positivity),
      hqdef, ← mul_assoc, ← mul_pow]
    congr 2
    rw [hRdef]
    field_simp
    ring
  have hA : (∫ x in closedBall y R, w x) / volume.real (closedBall (0 : ComplexModel n) (R / 2))
      ≤ ε / 2 * r ^ 2 := by
    rw [div_le_iff₀ hvs]
    calc ∫ x in closedBall y R, w x ≤ ε' * (2 * r) ^ 2 * volume.real (closedBall z (2 * r)) :=
          hmono.trans hfl'
      _ = ε / 2 * r ^ 2 * volume.real (closedBall (0 : ComplexModel n) (R / 2)) := by
          rw [hvol, hε'def]
          field_simp
          ring
  have hquadR : M / n * R ^ 2 ≤ ε / 2 * r ^ 2 := by
    rw [hRdef, mul_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hMδ (sq_nonneg r)
  have : w y ≤ ε * r ^ 2 := by linarith
  simpa [hydef] using this

/-- **Second-order flatness on the zero set.**  Let `w ≥ 0` be continuous on an open `U ⊆ ℂⁿ`
with locally bounded distributional Laplacian.  Then at almost every point `x ∈ U` with
`w(x) = 0`, `w(x + h) = o(‖h‖²)`. -/
theorem ae_isLittleO_of_nonneg {w : ComplexModel n → ℝ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hw : ContinuousOn w U) (hw0 : ∀ z ∈ U, 0 ≤ w z)
    (hL : HasLocallyBoundedLeviTraceOn w U) :
    ∀ᵐ x ∂volume, x ∈ U → w x = 0 →
      (fun h => w (x + h)) =o[𝓝 0] (fun h => ‖h‖ ^ 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine Eventually.of_forall fun x _ hx0 => ?_
    have hconst : (fun h : ComplexModel 0 => w (x + h)) = fun _ => 0 := by
      funext h
      rw [Subsingleton.elim h 0, add_zero, hx0]
    rw [hconst]
    exact isLittleO_zero _ _
  -- local radii
  have hrad : ∀ x : U, ∃ ρ : ℝ, 0 < ρ ∧ closedBall (x : ComplexModel n) (8 * ρ) ⊆ U := by
    intro x
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x x.2
    exact ⟨ε / 16, by positivity, (closedBall_subset_ball (by linarith)).trans hεU⟩
  choose ρ hρ hρU using hrad
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : U => ball (x : ComplexModel n) (ρ x)) fun x => isOpen_ball
  have hloc : ∀ x ∈ T, ∀ᵐ y ∂volume, y ∈ ball (x : ComplexModel n) (ρ x) → w y = 0 →
      (fun h => w (y + h)) =o[𝓝 0] (fun h => ‖h‖ ^ 2) := by
    intro x _
    have hK : IsCompact (closedBall (x : ComplexModel n) (8 * ρ x)) := isCompact_closedBall _ _
    obtain ⟨M, hM0, hGE, hLE⟩ := hL.exists_ge_le hK (hρU x) ball_subset_closedBall
    exact ae_isLittleO_of_nonneg_ball hn (hρ x) hM0
      (hw.mono (ball_subset_closedBall.trans (hρU x)))
      (fun z hz => hw0 z (hρU x (ball_subset_closedBall hz))) hGE hLE
  have hall := (ae_ball_iff hTc).mpr hloc
  filter_upwards [hall] with y hy hyU hy0
  have hmem : y ∈ ⋃ x : U, ball (x : ComplexModel n) (ρ x) :=
    mem_iUnion.mpr ⟨⟨y, hyU⟩, mem_ball_self (hρ _)⟩
  rw [← hTU] at hmem
  obtain ⟨x, hxT, hyx⟩ := mem_iUnion₂.mp hmem
  exact hy x hxT hyx hy0

/-- **Second-order contact.**  Let `u ≤ f` be continuous on an open `U ⊆ ℂⁿ`, each with locally
bounded distributional Laplacian.  Then `u` and `f` coincide up to second order at almost every
point of the contact set `{u = f}`. -/
theorem ae_coincideToSecondOrderAt_of_le {u f : ComplexModel n → ℝ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hu : ContinuousOn u U) (hf : ContinuousOn f U) (hle : ∀ z ∈ U, u z ≤ f z)
    (hLu : HasLocallyBoundedLeviTraceOn u U) (hLf : HasLocallyBoundedLeviTraceOn f U) :
    ∀ᵐ x ∂volume, x ∈ U → u x = f x → CoincideToSecondOrderAt f u x := by
  have hw := ae_isLittleO_of_nonneg hU (hf.sub hu) (fun z hz => sub_nonneg.mpr (hle z hz))
    (HasLocallyBoundedLeviTraceOn.sub hU hf hu hLf hLu)
  filter_upwards [hw] with x hx hxU hxe
  refine ⟨hxe.symm, ?_⟩
  have := hx hxU (by simp [hxe])
  simpa only [Pi.sub_apply] using this

end SGPT.Analysis.CZ
