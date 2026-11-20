import SGPT.Okounkov.TranscendentalWNLegendreApproxSmooth
import SGPT.Okounkov.TranscendentalWNLegendreBoundedTools

/-!
# The locally bounded case on a ball: limits of the smooth identity (package WN-LEG)

Blueprint `claude-tok-wn-leg`, nodes `tok-wn-leg:tight` and `tok-wn-leg:bounded-case` (first
part).  Let `IsBoundedLegendreData (ball z₀ r) u a b C` and let `F_k` be the approximants of
`TranscendentalWNLegendreApproxSmooth` on `D = B'_{2δ₀}` (`δ₀ = min(1/2, r/8)`), which contains
`ball z₀ (3r/4)`.  Write `μ_k`, `μ` for the non-pluripolar measures of `u_k = F_k(z, log |τ|²)`
and `u` on `D × ℂ*`, and `ν_{k,λ}`, `ν_λ` for those of `(û_k)_λ` and `û_λ` on `D`.  For a
continuous compactly supported `0 ≤ φ ≤ 1` with `tsupport φ ⊆ W = ball z₀ (r/8)`:

* `∫ φ dν_{k,λ} → ∫ φ dν_λ` for `λ ∈ (a, b)` and `∫ Φ dμ_k → ∫ Φ dμ` for continuous compactly
  supported `Φ ≥ 0` in `D × ℂ*` (Bedford–Taylor decreasing continuity);
* `ν_{k,λ}(W) ≤ M` uniformly in `k` and `λ` (Chern–Levine–Nirenberg, `exists_cln_bound`);
* `λ ↦ ∫ φ dν_{k,λ}` agrees on `(a, b)` with a Borel function (`exists_measurable_lintegral`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality
  SGPT.Foundations.Analysis.Pending.PshRadialRegularization

variable {N : ℕ}

/-! ### Geometry -/

section Geometry

/-- `δ₀ = min(1/2, r/8)`. -/
def localScale (r : ℝ) : ℝ := min (1 / 2) (r / 8)

theorem localScale_pos {r : ℝ} (hr : 0 < r) : 0 < localScale r :=
  lt_min (by norm_num) (by linarith)

theorem localScale_le_half (r : ℝ) : localScale r ≤ 1 / 2 := min_le_left _ _

theorem localScale_le (r : ℝ) : localScale r ≤ r / 8 := min_le_right _ _

theorem ball_subset_approxDomain {z₀ : ComplexModel N} {r : ℝ} (_hr : 0 < r) :
    ball z₀ (3 * r / 4) ⊆ approxDomain (ball z₀ r) (localScale r) := by
  intro z hz
  rw [mem_ball] at hz
  refine ⟨r - dist z z₀, by linarith [localScale_le r], fun w hw => ?_⟩
  rw [mem_ball] at hw ⊢
  linarith [dist_triangle w z z₀]

theorem closedBall_subset_approxDomain {z₀ : ComplexModel N} {r : ℝ} (hr : 0 < r) :
    closedBall z₀ (2 * (r / 4)) ⊆ approxDomain (ball z₀ r) (localScale r) :=
  (closedBall_subset_ball (by linarith)).trans (ball_subset_approxDomain hr)

theorem ball_eighth_subset_approxDomain {z₀ : ComplexModel N} {r : ℝ} (hr : 0 < r) :
    ball z₀ (r / 8) ⊆ approxDomain (ball z₀ r) (localScale r) :=
  (ball_subset_ball (by linarith)).trans (ball_subset_approxDomain hr)

theorem approxDomain_subset {B : Set (ComplexModel N)} {δ₀ : ℝ} (hδ₀ : 0 ≤ δ₀) :
    (approxDomain B δ₀ : Set (ComplexModel N)) ⊆ B := innerSet_subset (by linarith)

end Geometry

/-! ### The measures of the approximants -/

section Measures

variable {u : ComplexModel N → ℂ → EReal} {a b C : ℝ} {z₀ : ComplexModel N} {r : ℝ}
  {ρ : ComplexModel (N + 1) → ℝ}

theorem isPreconnected_ball' : IsPreconnected (ball z₀ r) := (convex_ball z₀ r).isPreconnected

namespace IsBoundedLegendreData

variable (h : IsBoundedLegendreData (ball z₀ r) u a b C) (hρ : IsRadialKernel ρ) (hr : 0 < r)
include h hρ hr

theorem localData (k : ℕ) :
    IsSmoothLegendreData (approxDomain (ball z₀ r) (localScale r) : Set (ComplexModel N))
      (approxProfile ρ u a b C (localScale r) k) a b :=
  h.isSmoothLegendreData_approxProfile hρ isPreconnected_ball' (localScale_pos hr)
    (localScale_le_half r) (mem_ball_self hr) k

theorem localPsh (k : ℕ) :
    PlurisubharmonicOn (fun p : ComplexModel N × ℂ =>
      logRadialFunction (approxProfile ρ u a b C (localScale r) k) p.1 p.2)
      ((approxDomain (ball z₀ r) (localScale r) : Set (ComplexModel N)) ×ˢ puncturedPlane) :=
  h.plurisubharmonicOn_approxProfile hρ isPreconnected_ball' (localScale_pos hr)
    (localScale_le_half r) (mem_ball_self hr) k

/-- The smooth transforms `(û_k)_λ` as smooth psh functions on `D`. -/
theorem localSmoothTransform (k : ℕ) {lam : ℝ} (hlam : lam ∈ Ioo a b) :
    IsSmoothPshOn (approxDomain (ball z₀ r) (localScale r))
      (fun z => legendreValue (approxProfile ρ u a b C (localScale r) k) z lam) :=
  (h.localData hρ hr k).isSmoothPshOn_legendreValue (h.localPsh hρ hr k) hlam

/-- `ν_{k,λ}` is the bounded Bedford–Taylor measure of the real function `(û_k)_λ`. -/
theorem truncationLimitMeasure_approxTransform (k : ℕ) {lam : ℝ} (hlam : lam ∈ Ioo a b)
    (hf : PlurisubharmonicOn
      (partialLegendre (logRadialFunction (approxProfile ρ u a b C (localScale r) k)) lam)
      (approxDomain (ball z₀ r) (localScale r))) :
    MongeAmpere.truncationLimitMeasure (approxDomain (ball z₀ r) (localScale r))
        (partialLegendre (logRadialFunction (approxProfile ρ u a b C (localScale r) k)) lam) hf =
      MongeAmpere.truncationLimitMeasure (approxDomain (ball z₀ r) (localScale r))
        (fun z => (legendreValue (approxProfile ρ u a b C (localScale r) k) z lam : EReal))
        (h.localSmoothTransform hρ hr k hlam).2.1 :=
  truncationLimitMeasure_congr hf _ fun _ hz => (h.localData hρ hr k).partialLegendre_logRadial_eq
    (D := approxDomain (ball z₀ r) (localScale r)) hz hlam

theorem truncationLimitMeasure_approxTransform_eq_smooth (k : ℕ) {lam : ℝ}
    (hlam : lam ∈ Ioo a b)
    (hf : PlurisubharmonicOn
      (partialLegendre (logRadialFunction (approxProfile ρ u a b C (localScale r) k)) lam)
      (approxDomain (ball z₀ r) (localScale r))) :
    MongeAmpere.truncationLimitMeasure (approxDomain (ball z₀ r) (localScale r))
        (partialLegendre (logRadialFunction (approxProfile ρ u a b C (localScale r) k)) lam) hf =
      smoothMeasure _ _ (h.localSmoothTransform hρ hr k hlam) := by
  rw [h.truncationLimitMeasure_approxTransform hρ hr k hlam hf]
  exact (SGPT.MongeAmpere.truncationLimitMeasure_smooth_sub_const
    (h.localSmoothTransform hρ hr k hlam)).1

/-- The uniform bound `|(û_k)_λ| ≤ max(C, c + (b - a)/2)` on `D`. -/
theorem abs_legendreValue_le (k : ℕ) {lam : ℝ} (hlam : lam ∈ Ioo a b) {z : ComplexModel N}
    (hz : z ∈ approxDomain (ball z₀ r) (localScale r)) :
    |legendreValue (approxProfile ρ u a b C (localScale r) k) z lam| ≤
      max C (approxConst a b C + (b - a) / 2) := by
  have hb := h.legendreValue_approxProfile_bounds hρ isPreconnected_ball'
    (localScale_pos hr) (localScale_le_half r) hz k hlam
  rw [abs_le]
  constructor
  · linarith [le_max_left C (approxConst a b C + (b - a) / 2)]
  · exact hb.2.trans (le_max_right _ _)

/-- **Chern–Levine–Nirenberg, uniformly in `k` and `λ`**: `ν_{k,λ}(ball z₀ (r/8)) ≤ M`. -/
theorem exists_cln_bound : ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ k : ℕ, ∀ lam ∈ Ioo a b,
    ∀ hf : PlurisubharmonicOn
      (partialLegendre (logRadialFunction (approxProfile ρ u a b C (localScale r) k)) lam)
      (approxDomain (ball z₀ r) (localScale r)),
    MongeAmpere.truncationLimitMeasure (approxDomain (ball z₀ r) (localScale r))
      (partialLegendre (logRadialFunction (approxProfile ρ u a b C (localScale r) k)) lam) hf
      (ball z₀ (r / 8)) ≤ M := by
  have hR : 0 < r / 4 := by linarith
  have hz₀ : z₀ ∈ ball z₀ r := mem_ball_self hr
  have hM : 0 ≤ max C (approxConst a b C + (b - a) / 2) :=
    (h.nonneg_C hz₀).trans (le_max_left _ _)
  obtain ⟨Cc, hCc0, hCc⟩ := BedfordTaylor.exists_cln_constant z₀ hR hM
  refine ⟨ENNReal.ofReal (Cc * (volume.restrict (ball z₀ (r / 4))).real univ),
    ENNReal.ofReal_lt_top,
    fun k lam hlam hf => ?_⟩
  set D := approxDomain (ball z₀ r) (localScale r)
  set f := fun z => legendreValue (approxProfile ρ u a b C (localScale r) k) z lam
  have hfs := h.localSmoothTransform hρ hr k hlam
  have hpsd : BedfordTaylor.IsSmoothPsdOn D f := ⟨hfs.1, hfs.2.2⟩
  have hc := hCc D (fun _ => f) (fun _ => 0) 1 (closedBall_subset_approxDomain hr)
    (fun _ => hpsd) (fun _ z hz => h.abs_legendreValue_le hρ hr k hlam
      (closedBall_subset_approxDomain hr hz))
    (BedfordTaylorFibreSlicing.isSmoothPsdOn_const D 0) (fun _ _ => zero_le_one)
  simp only [sub_zero, one_mul, FirstPass.MixedMongeAmpere.mixedDensity_diagonal,
    integral_const, smul_eq_mul, mul_one] at hc
  rw [show r / 4 / 2 = r / 8 by ring] at hc
  rw [h.truncationLimitMeasure_approxTransform_eq_smooth hρ hr k hlam hf, smoothMeasure,
    withDensity_apply _ measurableSet_ball,
    Measure.restrict_restrict_of_subset (ball_eighth_subset_approxDomain hr)]
  have hcont : ContinuousOn (smoothDensity f) (closedBall z₀ (r / 8)) := by
    have := BedfordTaylor.continuousOn_mixedDensity (U := D) (f := fun _ => f) (fun _ => hfs.1)
    rw [show FirstPass.MixedMongeAmpere.mixedDensity (fun _ : Fin N => f) = smoothDensity f from
      funext (FirstPass.MixedMongeAmpere.mixedDensity_diagonal f)] at this
    exact this.mono ((closedBall_subset_closedBall (by linarith)).trans
      (closedBall_subset_approxDomain hr))
  have hint : IntegrableOn (smoothDensity f) (ball z₀ (r / 8)) :=
    (hcont.integrableOn_compact (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_ball).mpr (Eventually.of_forall fun z hz =>
      smoothDensity_nonneg (hfs.2.2 z (ball_eighth_subset_approxDomain hr hz))))]
  exact ENNReal.ofReal_le_ofReal hc

/-! ### Bedford–Taylor convergence on both sides -/

omit hρ hr in
/-- `û_λ` is real and bounded by `C` on `D`. -/
theorem abs_partialLegendre_toReal_le {lam : ℝ} (hlam : lam ∈ Icc a b) {z : ComplexModel N}
    (hz : z ∈ ball z₀ r) : |(partialLegendre u lam z).toReal| ≤ C := by
  have h1 := h.lower lam hlam z hz
  have h2 := h.upper lam hlam z hz
  rw [← EReal.coe_toReal (h.partialLegendre_ne_top_of_mem hz hlam)
    (h.partialLegendre_ne_bot_of_mem hz hlam), EReal.coe_le_coe_iff] at h1 h2
  exact abs_le.mpr ⟨h1, h2⟩

/-- **Right side**: `∫ φ dν_{k,λ} → ∫ φ dν_λ` for `λ ∈ (a, b)`. -/
theorem tendsto_lintegral_approxTransform {lam : ℝ} (hlam : lam ∈ Ioo a b)
    (hû : PlurisubharmonicOn (partialLegendre u lam) (approxDomain (ball z₀ r) (localScale r)))
    (hf : ∀ k, PlurisubharmonicOn
      (partialLegendre (logRadialFunction (approxProfile ρ u a b C (localScale r) k)) lam)
      (approxDomain (ball z₀ r) (localScale r)))
    {φ : ComplexModel N → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ approxDomain (ball z₀ r) (localScale r)) (hφ0 : ∀ z, 0 ≤ φ z) :
    Tendsto (fun k => ∫⁻ z, ENNReal.ofReal (φ z) ∂(MongeAmpere.truncationLimitMeasure
        (approxDomain (ball z₀ r) (localScale r))
        (partialLegendre (logRadialFunction (approxProfile ρ u a b C (localScale r) k)) lam)
        (hf k))) atTop
      (𝓝 (∫⁻ z, ENNReal.ofReal (φ z) ∂(MongeAmpere.truncationLimitMeasure
        (approxDomain (ball z₀ r) (localScale r)) (partialLegendre u lam) hû))) := by
  set D := approxDomain (ball z₀ r) (localScale r)
  have hlamI : lam ∈ Icc a b := ⟨hlam.1.le, hlam.2.le⟩
  have hDB : (D : Set (ComplexModel N)) ⊆ ball z₀ r := approxDomain_subset (localScale_pos hr).le
  set v : ComplexModel N → ℝ := fun z => (partialLegendre u lam z).toReal
  have heq : EqOn (partialLegendre u lam) (fun z => (v z : EReal)) D := fun z hz =>
    (EReal.coe_toReal (h.partialLegendre_ne_top_of_mem (hDB hz) hlamI)
      (h.partialLegendre_ne_bot_of_mem (hDB hz) hlamI)).symm
  have hvp : PlurisubharmonicOn (fun z => (v z : EReal)) D :=
    plurisubharmonicOn_congr_of_eqOn D.isOpen hû heq
  have hv : IsLocallyBoundedPshOn D v :=
    BedfordTaylor.isLocallyBoundedPshOn_of_abs_le hvp fun z hz =>
      h.abs_partialLegendre_toReal_le hlamI (hDB hz)
  have hw : ∀ k, IsLocallyBoundedPshOn D
      (fun z => legendreValue (approxProfile ρ u a b C (localScale r) k) z lam) := fun k =>
    LocalBedfordTaylorDecreasing.isLocallyBoundedPshOn_of_isSmoothPshOn
      (h.localSmoothTransform hρ hr k hlam)
  have e1 : MongeAmpere.truncationLimitMeasure D (partialLegendre u lam) hû =
      MongeAmpere.truncationLimitMeasure D (fun z => (v z : EReal)) hv.1 :=
    truncationLimitMeasure_congr hû hv.1 heq
  rw [e1]
  refine (tendsto_lintegral_truncationLimitMeasure_of_antitone hw hv
    (fun z hz k l hkl => h.legendreValue_approxProfile_anti hρ isPreconnected_ball'
      (localScale_pos hr) (localScale_le_half r) hz hlam hkl)
    (fun z hz => h.tendsto_legendreValue_approxProfile hρ isPreconnected_ball'
      (localScale_pos hr) (localScale_le_half r) hz hlam) hφ hφc hφD hφ0).congr fun k => ?_
  rw [h.truncationLimitMeasure_approxTransform hρ hr k hlam (hf k)]

omit hρ hr in
/-- `|u(z, τ)| ≤ C + max(|a|, |b|) |log |τ|²|` on `B × ℂ*`. -/
theorem abs_toReal_le {z : ComplexModel N} (hz : z ∈ ball z₀ r) {τ : ℂ} (hτ : τ ≠ 0) :
    |(u z τ).toReal| ≤ C + slopeBound a b * |logNormSq τ| := by
  obtain ⟨h1, h2⟩ := h.bounds hz hτ
  have hne : u z τ ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h1
  have hnt : u z τ ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) h2
  rw [← EReal.coe_toReal hnt hne, EReal.coe_le_coe_iff] at h1 h2
  have hm := abs_max_mul_sub_max_mul_le a b (logNormSq τ) 0
  simp only [mul_zero, max_self, sub_zero] at hm
  rw [abs_le] at hm ⊢
  simp only [slopeBound] at *
  constructor <;> linarith [hm.1, hm.2]

/-- **Left side**: `∫ Φ dμ_k → ∫ Φ dμ` for continuous compactly supported `Φ ≥ 0` in `D × ℂ*`. -/
theorem tendsto_lintegral_approxProfile
    (hu : PlurisubharmonicOn (productModelFunction u)
      (puncturedProductOpens (approxDomain (ball z₀ r) (localScale r))))
    (hf : ∀ k, PlurisubharmonicOn
      (productModelFunction (logRadialFunction (approxProfile ρ u a b C (localScale r) k)))
      (puncturedProductOpens (approxDomain (ball z₀ r) (localScale r))))
    {Φ : ComplexModel (N + 1) → ℝ} (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (hΦD : tsupport Φ ⊆ puncturedProductOpens (approxDomain (ball z₀ r) (localScale r)))
    (hΦ0 : ∀ q, 0 ≤ Φ q) :
    Tendsto (fun k => ∫⁻ q, ENNReal.ofReal (Φ q) ∂(MongeAmpere.truncationLimitMeasure
        (puncturedProductOpens (approxDomain (ball z₀ r) (localScale r)))
        (productModelFunction (logRadialFunction (approxProfile ρ u a b C (localScale r) k)))
        (hf k))) atTop
      (𝓝 (∫⁻ q, ENNReal.ofReal (Φ q) ∂(MongeAmpere.truncationLimitMeasure
        (puncturedProductOpens (approxDomain (ball z₀ r) (localScale r)))
        (productModelFunction u) hu))) := by
  set D := approxDomain (ball z₀ r) (localScale r)
  set P := puncturedProductOpens D
  have hDB : (D : Set (ComplexModel N)) ⊆ ball z₀ r := approxDomain_subset (localScale_pos hr).le
  have hmemP : ∀ q ∈ P, (stripModelEquiv N q).1 ∈ D ∧ (stripModelEquiv N q).2 ≠ 0 :=
    fun q hq => hq
  set v : ComplexModel (N + 1) → ℝ := fun q => (productModelFunction u q).toReal
  have heq : EqOn (productModelFunction u) (fun q => (v q : EReal)) P := by
    intro q hq
    obtain ⟨h1, h2⟩ := h.bounds (hDB (hmemP q hq).1) (hmemP q hq).2
    exact (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) h2)
      (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h1)).symm
  have hvp : PlurisubharmonicOn (fun q => (v q : EReal)) P :=
    plurisubharmonicOn_congr_of_eqOn P.isOpen hu heq
  have hg : ContinuousOn (fun q : ComplexModel (N + 1) =>
      C + slopeBound a b * |logNormSq (stripModelEquiv N q).2|) P := by
    intro q hq
    have hc0 : ContinuousAt (fun q : ComplexModel (N + 1) => (stripModelEquiv N q).2) q :=
      (continuous_snd.comp (stripModelEquiv N).continuous).continuousAt
    have hc1 : ContinuousAt (fun q : ComplexModel (N + 1) => logNormSq (stripModelEquiv N q).2) q :=
      ContinuousAt.comp (g := logNormSq) (contDiffAt_logNormSq (hmemP q hq).2).continuousAt hc0
    exact (continuousAt_const.add (continuousAt_const.mul hc1.abs)).continuousWithinAt
  have hv : IsLocallyBoundedPshOn P v :=
    isLocallyBoundedPshOn_of_abs_le_continuousOn hvp hg fun q hq =>
      h.abs_toReal_le (hDB (hmemP q hq).1) (hmemP q hq).2
  have hw : ∀ k, IsLocallyBoundedPshOn P (uTilde (approxProfile ρ u a b C (localScale r) k)) :=
    fun k => LocalBedfordTaylorDecreasing.isLocallyBoundedPshOn_of_isSmoothPshOn
      ((h.localData hρ hr k).isSmoothPshOn_uTilde (h.localPsh hρ hr k))
  have e1 : MongeAmpere.truncationLimitMeasure P (productModelFunction u) hu =
      MongeAmpere.truncationLimitMeasure P (fun q => (v q : EReal)) hv.1 :=
    truncationLimitMeasure_congr hu hv.1 heq
  rw [e1]
  refine tendsto_lintegral_truncationLimitMeasure_of_antitone hw hv
    (fun q hq k l hkl => h.approxProfile_anti hρ isPreconnected_ball' (localScale_pos hr)
      (localScale_le_half r) (hmemP q hq).1 hkl _) (fun q hq => ?_) hΦ hΦc hΦD hΦ0
  have hlim := h.tendsto_approxProfile hρ isPreconnected_ball' (localScale_pos hr)
    (hmemP q hq).1 (logNormSq (stripModelEquiv N q).2)
  rw [expPullback_symm, ← eq_exp_half_logNormSq h.circleInvariant _ (hmemP q hq).2] at hlim
  exact hlim

end IsBoundedLegendreData

end Measures

/-! ### Cutoffs in the `ℂ*` variable -/

section Cutoff

/-- `χ̂_L(y) = max(0, min(1, L + 1 - |y|))`: `1` on `[-L, L]`, `0` off `(-L-1, L+1)`. -/
def logCutoff (L y : ℝ) : ℝ := max 0 (min 1 (L + 1 - |y|))

theorem continuous_logCutoff (L : ℝ) : Continuous (logCutoff L) :=
  continuous_const.max (continuous_const.min (continuous_const.sub continuous_abs))

theorem logCutoff_nonneg (L y : ℝ) : 0 ≤ logCutoff L y := le_max_left _ _

theorem logCutoff_le_one (L y : ℝ) : logCutoff L y ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem logCutoff_eq_one {L y : ℝ} (hy : |y| ≤ L) : logCutoff L y = 1 := by
  unfold logCutoff
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem logCutoff_eq_zero {L y : ℝ} (hy : L + 1 ≤ |y|) : logCutoff L y = 0 := by
  unfold logCutoff
  rw [min_eq_right (by linarith), max_eq_left (by linarith)]

/-- `χ_L(τ) = χ̂_L(log |τ|²)` on `ℂ*`, `0` at `0`. -/
def tauCutoff (L : ℝ) (τ : ℂ) : ℝ := if τ = 0 then 0 else logCutoff L (logNormSq τ)

theorem tauCutoff_of_ne {L : ℝ} {τ : ℂ} (hτ : τ ≠ 0) :
    tauCutoff L τ = logCutoff L (logNormSq τ) := if_neg hτ

theorem tauCutoff_nonneg (L : ℝ) (τ : ℂ) : 0 ≤ tauCutoff L τ := by
  unfold tauCutoff; split_ifs
  · exact le_rfl
  · exact logCutoff_nonneg _ _

theorem tauCutoff_le_one (L : ℝ) (τ : ℂ) : tauCutoff L τ ≤ 1 := by
  unfold tauCutoff; split_ifs
  · exact zero_le_one
  · exact logCutoff_le_one _ _

theorem continuous_tauCutoff (L : ℝ) : Continuous (tauCutoff L) := by
  refine continuous_iff_continuousAt.mpr fun τ => ?_
  by_cases hτ : τ = 0
  · subst hτ
    have hev : tauCutoff L =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
      have hε : 0 < Real.exp (-(L + 1) / 2) := Real.exp_pos _
      filter_upwards [ball_mem_nhds (0 : ℂ) hε] with σ hσ
      by_cases hσ0 : σ = 0
      · simp [tauCutoff, hσ0]
      rw [tauCutoff_of_ne hσ0]
      apply logCutoff_eq_zero
      rw [mem_ball, dist_zero_right] at hσ
      have hpos : 0 < ‖σ‖ := norm_pos_iff.mpr hσ0
      have hlt : ‖σ‖ ^ 2 < Real.exp (-(L + 1)) := by
        have : Real.exp (-(L + 1) / 2) ^ 2 = Real.exp (-(L + 1)) := by
          rw [← Real.exp_nat_mul]; congr 1; ring
        rw [← this]
        exact pow_lt_pow_left₀ hσ hpos.le (by norm_num)
      have hlog : logNormSq σ < -(L + 1) := by
        unfold logNormSq
        rw [Real.log_lt_iff_lt_exp (by positivity)]
        exact hlt
      linarith [neg_le_abs (logNormSq σ)]
    exact (continuousAt_const.congr hev.symm)
  · have hev : tauCutoff L =ᶠ[𝓝 τ] fun σ => logCutoff L (logNormSq σ) := by
      filter_upwards [isOpen_ne.mem_nhds hτ] with σ hσ
      exact tauCutoff_of_ne hσ
    exact ((continuous_logCutoff L).continuousAt.comp
      (contDiffAt_logNormSq hτ).continuousAt).congr hev.symm

/-- The closed annulus `e^{-(L+1)} ≤ |τ|² ≤ e^{L+1}`. -/
def logAnnulus (L : ℝ) : Set ℂ := {τ | Real.exp (-(L + 1)) ≤ ‖τ‖ ^ 2 ∧ ‖τ‖ ^ 2 ≤ Real.exp (L + 1)}

theorem isCompact_logAnnulus (L : ℝ) : IsCompact (logAnnulus L) := by
  refine (isCompact_closedBall (0 : ℂ) (Real.exp (L + 1) + 1)).of_isClosed_subset ?_ ?_
  · exact (isClosed_le continuous_const (continuous_norm.pow 2)).inter
      (isClosed_le (continuous_norm.pow 2) continuous_const)
  · intro τ hτ
    rw [mem_closedBall, dist_zero_right]
    have h1 := hτ.2
    nlinarith [sq_nonneg (‖τ‖ - 1)]

theorem logAnnulus_subset_puncturedPlane (L : ℝ) : logAnnulus L ⊆ puncturedPlane := by
  intro τ hτ h0
  have := hτ.1
  rw [h0, norm_zero] at this
  have := Real.exp_pos (-(L + 1))
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at *
  linarith

theorem tsupport_tauCutoff_subset (L : ℝ) : tsupport (tauCutoff L) ⊆ logAnnulus L := by
  refine closure_minimal (fun τ hτ => ?_) (isCompact_logAnnulus L).isClosed
  rw [Function.mem_support] at hτ
  have hτ0 : τ ≠ 0 := fun h0 => hτ (by simp [tauCutoff, h0])
  rw [tauCutoff_of_ne hτ0] at hτ
  have hlt : |logNormSq τ| < L + 1 := by
    by_contra hge
    exact hτ (logCutoff_eq_zero (not_lt.mp hge))
  have hpos : 0 < ‖τ‖ ^ 2 := by positivity
  rw [abs_lt] at hlt
  unfold logNormSq at hlt
  exact ⟨(Real.lt_log_iff_exp_lt hpos).mp hlt.1 |>.le, (Real.log_lt_iff_lt_exp hpos).mp hlt.2 |>.le⟩

theorem tendsto_tauCutoff {τ : ℂ} (hτ : τ ≠ 0) :
    Tendsto (fun L : ℕ => tauCutoff L τ) atTop (𝓝 1) := by
  obtain ⟨L₀, hL₀⟩ := exists_nat_ge |logNormSq τ|
  refine tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨L₀, fun L hL => ?_⟩)
  show (1 : ℝ) = tauCutoff (L : ℝ) τ
  rw [tauCutoff_of_ne hτ, logCutoff_eq_one (hL₀.trans (by exact_mod_cast hL))]

/-- The product test function `Φ_L(q) = φ(z) χ_L(τ)`. -/
def productCutoff (φ : ComplexModel N → ℝ) (L : ℝ) (q : ComplexModel (N + 1)) : ℝ :=
  φ (stripModelEquiv N q).1 * tauCutoff L (stripModelEquiv N q).2

theorem continuous_productCutoff {φ : ComplexModel N → ℝ} (hφ : Continuous φ) (L : ℝ) :
    Continuous (productCutoff φ L) :=
  (hφ.comp (continuous_fst.comp (stripModelEquiv N).continuous)).mul
    ((continuous_tauCutoff L).comp (continuous_snd.comp (stripModelEquiv N).continuous))

theorem tsupport_productCutoff_subset (φ : ComplexModel N → ℝ) (L : ℝ) :
    tsupport (productCutoff φ L) ⊆ stripModelEquiv N ⁻¹' (tsupport φ ×ˢ logAnnulus L) := by
  refine closure_minimal (fun q hq => ?_) ((isClosed_tsupport φ).prod
    (isCompact_logAnnulus L).isClosed |>.preimage (stripModelEquiv N).continuous)
  rw [Function.mem_support, productCutoff] at hq
  refine ⟨subset_tsupport φ (left_ne_zero_of_mul hq),
    tsupport_tauCutoff_subset L (subset_tsupport _ (right_ne_zero_of_mul hq))⟩

theorem hasCompactSupport_productCutoff {φ : ComplexModel N → ℝ} (hφc : HasCompactSupport φ)
    (L : ℝ) : HasCompactSupport (productCutoff φ L) := by
  have hK : IsCompact (stripModelEquiv N ⁻¹' (tsupport φ ×ˢ logAnnulus L)) := by
    rw [← ContinuousLinearEquiv.image_symm_eq_preimage]
    exact (hφc.isCompact.prod (isCompact_logAnnulus L)).image (stripModelEquiv N).symm.continuous
  exact hK.of_isClosed_subset (isClosed_tsupport _) (tsupport_productCutoff_subset φ L)

theorem tsupport_productCutoff_subset_punctured {φ : ComplexModel N → ℝ}
    {D : Opens (ComplexModel N)} (hφD : tsupport φ ⊆ D) (L : ℝ) :
    tsupport (productCutoff φ L) ⊆ puncturedProductOpens D := fun _ hq =>
  ⟨hφD (tsupport_productCutoff_subset φ L hq).1,
    logAnnulus_subset_puncturedPlane L (tsupport_productCutoff_subset φ L hq).2⟩

theorem productCutoff_nonneg {φ : ComplexModel N → ℝ} (hφ0 : ∀ z, 0 ≤ φ z) (L : ℝ)
    (q : ComplexModel (N + 1)) : 0 ≤ productCutoff φ L q :=
  mul_nonneg (hφ0 _) (tauCutoff_nonneg _ _)

theorem productCutoff_le {φ : ComplexModel N → ℝ} (hφ0 : ∀ z, 0 ≤ φ z) (L : ℝ)
    (q : ComplexModel (N + 1)) : productCutoff φ L q ≤ φ (stripModelEquiv N q).1 :=
  mul_le_of_le_one_right (hφ0 _) (tauCutoff_le_one _ _)

end Cutoff

end SGPT.Okounkov.TranscendentalWN
