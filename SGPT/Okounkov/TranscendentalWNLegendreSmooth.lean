import SGPT.Okounkov.TranscendentalWNLegendreSmoothDensity
import SGPT.MongeAmpere.LocalSmoothDensityBoundedMaxApproximation
import SGPT.Foundations.Analysis.Pending.BedfordTaylorFibreSlicing
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The smooth case of the partial Legendre Monge–Ampère identity (package WN-LEG)

Blueprint `claude-tok-wn-leg`, node `tok-wn-leg:smooth` (WN21 Theorem 3.3, smooth strictly convex
case, Remark 3.4).  Let `IsSmoothLegendreData D F α β` (`F` smooth on `D × ℝ`, `F_yy > 0`,
`∂F/∂y (z, ·) : ℝ → (α, β)` bijective) and let `u(z, τ) = F(z, log |τ|²)` be psh on `D × ℂ*`.
Then

* the partial Legendre transform `û_λ` is `legendreValue F · λ` on `D` for `λ ∈ (α, β)`
  (`partialLegendre_logRadial_eq`);
* for every measurable `g ≥ 0` on `ℂᴺ × ℝ`,

  `∫ g(z, log |τ|²) d MA(u) = (N + 1) ∫_α^β ∫ g(z, Y(z, λ)) d MA(û_λ)(z) dλ`

  (`lintegral_truncationLimitMeasure_logRadial`), where `MA` are TN's non-pluripolar measures
  `truncationLimitMeasure` (here equal to the smooth Monge–Ampère measures) and `Y(z, λ)` is the
  point where `∂F/∂y (z, Y) = λ`.  With `g = 1_E(z)` this is
  `MA(u)(E × ℂ*) = (N + 1) ∫_α^β MA(û_λ)(E) dλ`.

The proof integrates the pointwise identity `smoothDensity_uTilde` in polar coordinates
`τ = r e^{iθ}` (`lintegral_logRadial_polar`: `∫_{ℂ} h(log |τ|²) |τ|⁻² dτ = π ∫_ℝ h`) and
substitutes `λ = ∂F/∂y (z, y)` (`lintegral_image_eq_lintegral_abs_deriv_mul`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality

variable {N : ℕ}

/-! ### Measurability of Hessians -/

section Measurability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E]

theorem measurable_realHessian (u : E → ℝ) (v w : E) :
    Measurable fun x => realHessian u x v w := by
  simp only [realHessian_eq_fderiv]
  have h1 : Measurable fun x => fderiv ℝ (fderiv ℝ u) x v :=
    measurable_fderiv_apply_const ℝ (fderiv ℝ u) v
  exact (ContinuousLinearMap.apply ℝ ℝ w).continuous.measurable.comp h1

end Measurability

/-- The determinant is a measurable function of the entries. -/
theorem measurable_det_of_entries {X : Type*} [MeasurableSpace X] {n : ℕ}
    {M : X → Matrix (Fin n) (Fin n) ℂ} (hM : ∀ j k, Measurable fun x => M x j k) :
    Measurable fun x => (M x).det := by
  have hpi : Measurable fun x => (fun j k => M x j k : Fin n → Fin n → ℂ) :=
    measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun k => hM j k
  have hc : Continuous fun A : Fin n → Fin n → ℂ => (Matrix.of A).det :=
    Continuous.matrix_det (A := fun A : Fin n → Fin n → ℂ => Matrix.of A) continuous_id
  exact hc.measurable.comp hpi

theorem measurable_smoothDensity {n : ℕ} (u : ComplexModel n → ℝ) :
    Measurable (smoothDensity u) := by
  have hH : ∀ j k, Measurable fun z => complexHessian u z j k := by
    intro j k
    simp only [complexHessian]
    have ha := measurable_realHessian u (coordinateVector j) (coordinateVector k)
    have hb := measurable_realHessian u (Complex.I • coordinateVector j)
      (Complex.I • coordinateVector k)
    have hc := measurable_realHessian u (coordinateVector j) (Complex.I • coordinateVector k)
    have hd := measurable_realHessian u (Complex.I • coordinateVector j) (coordinateVector k)
    exact (((Complex.measurable_ofReal.comp (ha.add hb)).div_const 4).add
      ((measurable_const.mul (Complex.measurable_ofReal.comp (hc.sub hd))).div_const 4))
  have hdet : Measurable fun z => (complexHessian u z).det := measurable_det_of_entries hH
  exact measurable_const.mul (Complex.measurable_re.comp hdet)

theorem measurable_schurMatrix_det (F : ComplexModel N × ℝ → ℝ) :
    Measurable fun p => (schurMatrix F p).det := by
  have hS (v v' : ComplexModel N) : Measurable fun p => schurForm F p v v' := by
    simp only [schurForm, partialYY]
    exact (measurable_realHessian F _ _).sub
      (((measurable_realHessian F _ _).mul (measurable_realHessian F _ _)).div
        (measurable_realHessian F _ _))
  refine measurable_det_of_entries fun j k => ?_
  simp only [schurMatrix]
  exact (((Complex.measurable_ofReal.comp ((hS _ _).add (hS _ _))).div_const 4).add
    ((measurable_const.mul (Complex.measurable_ofReal.comp ((hS _ _).sub (hS _ _)))).div_const 4))

theorem measurable_logNormSq : Measurable logNormSq :=
  Real.measurable_log.comp ((continuous_norm.pow 2).measurable)

/-! ### Polar coordinates for functions of `log |τ|²` -/

theorem volume_puncturedPlane_compl : (volume : Measure ℂ) puncturedPlaneᶜ = 0 := by
  have : puncturedPlaneᶜ = ({0} : Set ℂ) := by
    ext τ
    simp [puncturedPlane]
  rw [this, measure_singleton]

/-- `∫_{(0, ∞)} k(r) dr = ∫_ℝ (e^{y/2}/2) k(e^{y/2}) dy`. -/
theorem lintegral_Ioi_eq_exp_half (k : ℝ → ℝ≥0∞) :
    ∫⁻ r in Ioi 0, k r =
      ∫⁻ y, ENNReal.ofReal (Real.exp (y / 2) / 2) * k (Real.exp (y / 2)) := by
  have himage : (fun y : ℝ => Real.exp (y / 2)) '' univ = Ioi 0 := by
    ext r
    simp only [mem_image, mem_univ, true_and, mem_Ioi]
    constructor
    · rintro ⟨y, rfl⟩
      exact Real.exp_pos _
    · intro hr
      exact ⟨2 * Real.log r, by rw [show 2 * Real.log r / 2 = Real.log r by ring,
        Real.exp_log hr]⟩
  have hd : ∀ y ∈ (univ : Set ℝ), HasDerivWithinAt (fun y : ℝ => Real.exp (y / 2))
      (Real.exp (y / 2) / 2) univ y := by
    intro y _
    have h1 : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) y := (hasDerivAt_id y).div_const 2
    have h2 := (Real.hasDerivAt_exp (y / 2)).comp y h1
    exact (h2.congr_deriv (by ring)).hasDerivWithinAt
  have hinj : InjOn (fun y : ℝ => Real.exp (y / 2)) univ := by
    intro a _ b _ hab
    have := Real.exp_injective hab
    linarith
  have h := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ hd hinj k
  rw [himage] at h
  rw [h, Measure.restrict_univ]
  congr 1
  funext y
  rw [abs_of_pos (by positivity)]

/-- **Polar coordinates**: `∫_ℂ h(log |τ|²) |τ|⁻² dτ = π ∫_ℝ h(y) dy`. -/
theorem lintegral_logRadial_polar {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ τ : ℂ, h (logNormSq τ) * ENNReal.ofReal (1 / ‖τ‖ ^ 2) =
      ENNReal.ofReal Real.pi * ∫⁻ y, h y := by
  rw [← Complex.lintegral_comp_polarCoord_symm]
  set k : ℝ → ℝ≥0∞ := fun r => h (Real.log (r ^ 2)) * ENNReal.ofReal (1 / r) with hk
  have hkm : Measurable k :=
    (hh.comp (Real.measurable_log.comp (measurable_id.pow_const 2))).mul
      (ENNReal.measurable_ofReal.comp (measurable_const.div measurable_id))
  have hfun : EqOn (fun p : ℝ × ℝ => ENNReal.ofReal p.1 •
        (h (logNormSq (Complex.polarCoord.symm p)) *
          ENNReal.ofReal (1 / ‖Complex.polarCoord.symm p‖ ^ 2)))
      (fun p => k p.1) polarCoord.target := by
    intro p hp
    have hp1 : 0 < p.1 := hp.1
    simp only [hk, Complex.norm_polarCoord_symm, abs_of_pos hp1, logNormSq, smul_eq_mul]
    rw [mul_comm, mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    field_simp
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hfun]
  rw [show polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi from rfl,
    Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod (fun x : ℝ × ℝ => k x.1) (hkm.comp measurable_fst).aemeasurable]
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioo]
  rw [lintegral_mul_const _ hkm, lintegral_Ioi_eq_exp_half]
  have hint : ∀ y : ℝ, ENNReal.ofReal (Real.exp (y / 2) / 2) * k (Real.exp (y / 2)) =
      ENNReal.ofReal (1 / 2) * h y := by
    intro y
    have hlog : Real.log (Real.exp (y / 2) ^ 2) = y := by
      rw [← Real.exp_nat_mul]
      push_cast
      rw [show (2 : ℝ) * (y / 2) = y by ring, Real.log_exp]
    simp only [hk]
    rw [hlog, mul_comm (h y), ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    field_simp
  simp_rw [hint]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_comm, ← mul_assoc,
    ← ENNReal.ofReal_mul (by linarith [Real.pi_pos])]
  congr 2
  ring

/-! ### Congruence of the non-pluripolar measures -/

section Congr

variable {n : ℕ}

theorem plurisubharmonicOn_congr_of_eqOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u v : E → EReal} {U : Set E} (hU : IsOpen U) (hu : PlurisubharmonicOn u U)
    (huv : EqOn u v U) : PlurisubharmonicOn v U :=
  fun x hx => (hu x hx).congr (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) huv)

theorem isLocalBedfordTaylorMeasure_congr {Ω : Opens (ComplexModel n)}
    {u v : ComplexModel n → ℝ} {μ : Measure (ComplexModel n)}
    (hμ : IsLocalBedfordTaylorMeasure Ω u μ) (huv : EqOn u v Ω) :
    IsLocalBedfordTaylorMeasure Ω v μ := by
  obtain ⟨⟨hpsh, hbd⟩, hc, hfin, happ⟩ := hμ
  refine ⟨⟨plurisubharmonicOn_congr_of_eqOn Ω.isOpen hpsh (fun z hz => by simp [huv hz]),
    fun z hz => ?_⟩, hc, hfin, fun U hU => ?_⟩
  · obtain ⟨V, hzV, hVΩ, C, hC⟩ := hbd z hz
    exact ⟨V, hzV, hVΩ, C, fun w hw => huv (hVΩ hw) ▸ hC w hw⟩
  · have hUΩ : (U : Set (ComplexModel n)) ⊆ Ω := subset_closure.trans hU.2
    have hiff : ∀ f, IsDecreasingApproximation U u f ↔ IsDecreasingApproximation U v f := by
      intro f
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, fun z hz => by rw [← huv (hUΩ hz)]; exact h3 z hz⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, fun z hz => by rw [huv (hUΩ hz)]; exact h3 z hz⟩
    obtain ⟨hex, hall⟩ := happ U hU
    exact ⟨hex.imp fun f hf => (hiff f).mp hf, fun f hf => hall f ((hiff f).mpr hf)⟩

theorem canonicalBedfordTaylorMeasure_congr {Ω : Opens (ComplexModel n)}
    {u v : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u)
    (hv : IsLocallyBoundedPshOn Ω v) (huv : EqOn u v Ω) :
    MongeAmpere.canonicalBedfordTaylorMeasure Ω u hu =
      MongeAmpere.canonicalBedfordTaylorMeasure Ω v hv :=
  (MongeAmpere.canonicalBedfordTaylorMeasure_eq hv (isLocalBedfordTaylorMeasure_congr
    (MongeAmpere.canonicalBedfordTaylorMeasure_spec Ω u hu) huv)).symm

/-- **The non-pluripolar measure only depends on the function on the domain.** -/
theorem truncationLimitMeasure_congr {Ω : Opens (ComplexModel n)}
    {u v : ComplexModel n → EReal} (hu : PlurisubharmonicOn u Ω)
    (hv : PlurisubharmonicOn v Ω) (huv : EqOn u v Ω) :
    MongeAmpere.truncationLimitMeasure Ω u hu = MongeAmpere.truncationLimitMeasure Ω v hv := by
  have hk : ∀ k, MongeAmpere.truncationMeasure Ω u hu k =
      MongeAmpere.truncationMeasure Ω v hv k := by
    intro k
    unfold MongeAmpere.truncationMeasure
    have hloc : strictTruncationLocus Ω u k = strictTruncationLocus Ω v k := by
      ext z
      simp only [strictTruncationLocus, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hz, hlt⟩
        exact ⟨hz, by rwa [← huv hz]⟩
      · rintro ⟨hz, hlt⟩
        exact ⟨hz, by rwa [huv hz]⟩
    rw [hloc, canonicalBedfordTaylorMeasure_congr _ (truncationReal_isLocallyBoundedPshOn hv k)
      (fun z hz => by simp only [truncationReal, truncation, huv hz])]
  refine Measure.ext fun s _ => ?_
  rw [MongeAmpere.truncationLimitMeasure_apply, MongeAmpere.truncationLimitMeasure_apply]
  simp_rw [hk]

end Congr

/-! ### The function `u(z, τ) = F(z, log |τ|²)` and its partial Legendre transforms -/

/-- `u(z, τ) = F(z, log |τ|²)`. -/
def logRadialFunction (F : ComplexModel N × ℝ → ℝ) : ComplexModel N → ℂ → EReal :=
  fun z τ => (F (z, logNormSq τ) : EReal)

theorem isCircleInvariant_logRadialFunction (F : ComplexModel N × ℝ → ℝ) :
    IsCircleInvariant (logRadialFunction F) := by
  intro z τ σ hτσ
  simp only [logRadialFunction, logNormSq, hτσ]

theorem productModelFunction_logRadialFunction (F : ComplexModel N × ℝ → ℝ) :
    productModelFunction (logRadialFunction F) = fun q => (uTilde F q : EReal) := rfl

/-- A function with monotone derivative is minimal at a critical point. -/
theorem le_of_hasDerivAt_of_monotone {g g' : ℝ → ℝ} (hg : ∀ t, HasDerivAt g (g' t) t)
    (hmono : Monotone g') {y₀ : ℝ} (h0 : g' y₀ = 0) (t : ℝ) : g y₀ ≤ g t := by
  have hcont : Continuous g := continuous_iff_continuousAt.mpr fun t => (hg t).continuousAt
  have hdiff : Differentiable ℝ g := fun t => (hg t).differentiableAt
  rcases le_total y₀ t with ht | ht
  · have hm : MonotoneOn g (Ici y₀) :=
      monotoneOn_of_deriv_nonneg (convex_Ici y₀) hcont.continuousOn hdiff.differentiableOn
        (by
          intro x hx
          rw [interior_Ici] at hx
          rw [(hg x).deriv, ← h0]
          exact hmono (le_of_lt hx))
    exact hm (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
  · have ha : AntitoneOn g (Iic y₀) :=
      antitoneOn_of_deriv_nonpos (convex_Iic y₀) hcont.continuousOn hdiff.differentiableOn
        (by
          intro x hx
          rw [interior_Iic] at hx
          rw [(hg x).deriv, ← h0]
          exact hmono (le_of_lt hx))
    exact ha (mem_Iic.mpr ht) (mem_Iic.mpr le_rfl) ht

/-- The Schur density `N!/πᴺ det (schurMatrix F p)`. -/
def schurDensity (F : ComplexModel N × ℝ → ℝ) (p : ComplexModel N × ℝ) : ℝ :=
  (N.factorial : ℝ) / Real.pi ^ N * (schurMatrix F p).det.re

theorem measurable_schurDensity (F : ComplexModel N × ℝ → ℝ) : Measurable (schurDensity F) :=
  measurable_const.mul (Complex.measurable_re.comp (measurable_schurMatrix_det F))

namespace IsSmoothLegendreData

variable {D : Opens (ComplexModel N)} {F : ComplexModel N × ℝ → ℝ} {α β : ℝ}
  (h : IsSmoothLegendreData (D : Set (ComplexModel N)) F α β)
include h

theorem legendreValue_le {z : ComplexModel N} (hz : z ∈ D) {lam : ℝ} (hlam : lam ∈ Ioo α β)
    (t : ℝ) : legendreValue F z lam ≤ F (z, t) - lam * t := by
  have hd : ∀ t, HasDerivAt (fun t => F (z, t) - lam * t) (partialY F (z, t) - lam) t := by
    intro t
    have h1 := (hasDerivAt_slice (h.contDiffAt_two hz t)).sub ((hasDerivAt_id t).const_mul lam)
    exact h1.congr_deriv (by simp)
  have hm : Monotone fun t => partialY F (z, t) - lam := by
    intro a b hab
    have := (h.strictMono_partialY hz).monotone hab
    simp only at this ⊢
    linarith
  have := le_of_hasDerivAt_of_monotone hd hm (y₀ := legendreArg F z lam)
    (by simp only [h.partialY_legendreArg hz hlam, sub_self]) t
  simpa only [legendreValue] using this

/-- **`û_λ = F(z, Y) - λ Y`** on `D` for `λ ∈ (α, β)` (`tok-wn-leg:smooth-family` (2)). -/
theorem partialLegendre_logRadial_eq {z : ComplexModel N} (hz : z ∈ D) {lam : ℝ}
    (hlam : lam ∈ Ioo α β) :
    partialLegendre (logRadialFunction F) lam z = (legendreValue F z lam : EReal) := by
  apply le_antisymm
  · refine (iInf_le _ (⟨Complex.exp ((legendreArg F z lam : ℂ) / 2), Complex.exp_ne_zero _⟩ :
      puncturedPlane)).trans ?_
    simp only [logRadialFunction, logNormSq_exp_half, legendreValue, EReal.coe_sub, le_refl]
  · refine le_iInf fun τ => ?_
    simp only [logRadialFunction]
    rw [← EReal.coe_sub]
    exact EReal.coe_le_coe_iff.mpr (h.legendreValue_le hz hlam _)

theorem smoothDensity_legendreValue {z : ComplexModel N} (hz : z ∈ D) {lam : ℝ}
    (hlam : lam ∈ Ioo α β) :
    smoothDensity (fun z' => legendreValue F z' lam) z = schurDensity F (z, legendreArg F z lam) := by
  rw [smoothDensity, h.complexHessian_legendreValue hz hlam, schurDensity]

theorem smoothDensity_uTilde' {z : ComplexModel N} (hz : z ∈ D) {τ : ℂ} (hτ : τ ≠ 0) :
    smoothDensity (uTilde F) ((stripModelEquiv N).symm (z, τ)) =
      ((N + 1 : ℕ) : ℝ) / Real.pi * (partialYY F (z, logNormSq τ) / ‖τ‖ ^ 2) *
        schurDensity F (z, logNormSq τ) := by
  rw [h.smoothDensity_uTilde hz hτ, h.smoothDensity_legendreValue hz (h.partialY_mem z hz _),
    h.legendreArg_partialY hz]

variable (hpsh : PlurisubharmonicOn (fun p : ComplexModel N × ℂ => logRadialFunction F p.1 p.2)
  ((D : Set (ComplexModel N)) ×ˢ puncturedPlane))
include hpsh

theorem isSmoothPshOn_legendreValue {lam : ℝ} (hlam : lam ∈ Ioo α β) :
    IsSmoothPshOn D (fun z => legendreValue F z lam) := by
  apply isSmoothPshOn_of_psh (h.contDiffOn_legendreValue_slice hlam)
  have := plurisubharmonicOn_partialLegendre h.isOpen hpsh
    (isCircleInvariant_logRadialFunction F) lam
  exact plurisubharmonicOn_congr_of_eqOn h.isOpen this
    fun z hz => h.partialLegendre_logRadial_eq hz hlam

theorem isSmoothPshOn_uTilde : IsSmoothPshOn (puncturedProductOpens D) (uTilde F) :=
  isSmoothPshOn_of_psh (contDiffOn_uTilde h.contDiffOn)
    (plurisubharmonicOn_comp_stripModelEquiv hpsh)

theorem schurDensity_nonneg {z : ComplexModel N} (hz : z ∈ D) (y : ℝ) :
    0 ≤ schurDensity F (z, y) := by
  have hlam := h.partialY_mem z hz y
  have := smoothDensity_nonneg ((h.isSmoothPshOn_legendreValue hpsh hlam).2.2 z hz)
  rwa [h.smoothDensity_legendreValue hz hlam, h.legendreArg_partialY hz] at this

/-- **The smooth identity with explicit densities** (`tok-wn-leg:smooth`). -/
theorem lintegral_puncturedDomain_eq {g : ComplexModel N × ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ q in puncturedDomain (D : Set (ComplexModel N)),
        ENNReal.ofReal (smoothDensity (uTilde F) q) *
          g ((stripModelEquiv N q).1, logNormSq (stripModelEquiv N q).2) =
      ((N + 1 : ℕ) : ℝ≥0∞) * ∫⁻ lam in Ioo α β, ∫⁻ z in (D : Set (ComplexModel N)),
        ENNReal.ofReal (smoothDensity (fun z' => legendreValue F z' lam) z) *
          g (z, legendreArg F z lam) := by
  set G : ComplexModel N × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (schurDensity F p) * g p
    with hG
  have hGm : Measurable G :=
    (ENNReal.measurable_ofReal.comp (measurable_schurDensity F)).mul hg
  -- transport by `stripModelEquiv`
  have hmp := BedfordTaylorFibreSlicing.measurePreserving_stripModelEquiv_symm (n := N)
  have hemb : MeasurableEmbedding (stripModelEquiv N).symm :=
    (stripModelEquiv N).symm.toHomeomorph.measurableEmbedding
  have hpre : (stripModelEquiv N).symm ⁻¹' puncturedDomain (D : Set (ComplexModel N)) =
      (D : Set (ComplexModel N)) ×ˢ puncturedPlane := by
    ext p
    simp [puncturedDomain, puncturedPlane]
  rw [← hmp.setLIntegral_comp_preimage_emb hemb, hpre]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  -- Tonelli
  have hm1 : Measurable fun p : ComplexModel N × ℂ =>
      ENNReal.ofReal (smoothDensity (uTilde F) ((stripModelEquiv N).symm p)) *
        g (p.1, logNormSq p.2) :=
    (ENNReal.measurable_ofReal.comp ((measurable_smoothDensity _).comp
      (stripModelEquiv N).symm.continuous.measurable)).mul
      (hg.comp (measurable_fst.prodMk (measurable_logNormSq.comp measurable_snd)))
  rw [← Measure.prod_restrict, lintegral_prod _ hm1.aemeasurable]
  -- the inner integral: polar coordinates and `λ = ∂F/∂y`
  have hinner : ∀ z ∈ (D : Set (ComplexModel N)),
      ∫⁻ τ in puncturedPlane,
          ENNReal.ofReal (smoothDensity (uTilde F) ((stripModelEquiv N).symm (z, τ))) *
            g (z, logNormSq τ) =
        ((N + 1 : ℕ) : ℝ≥0∞) * ∫⁻ lam in Ioo α β, G (z, legendreArg F z lam) := by
    intro z hz
    set H : ℝ → ℝ≥0∞ := fun y =>
      ENNReal.ofReal (((N + 1 : ℕ) : ℝ) / Real.pi * partialYY F (z, y)) * G (z, y) with hH
    have hHm : Measurable H := by
      have hp : Measurable fun y : ℝ => ((z, y) : ComplexModel N × ℝ) :=
        measurable_const.prodMk measurable_id
      exact (ENNReal.measurable_ofReal.comp (measurable_const.mul
        ((measurable_realHessian F _ _).comp hp))).mul (hGm.comp hp)
    have h1 : ∫⁻ τ in puncturedPlane,
          ENNReal.ofReal (smoothDensity (uTilde F) ((stripModelEquiv N).symm (z, τ))) *
            g (z, logNormSq τ) =
        ∫⁻ τ in puncturedPlane, H (logNormSq τ) * ENNReal.ofReal (1 / ‖τ‖ ^ 2) := by
      apply setLIntegral_congr_fun isOpen_puncturedPlane.measurableSet
      intro τ hτ
      simp only [hH, hG]
      rw [h.smoothDensity_uTilde' hz hτ]
      have hc := h.partialYY_pos z hz (logNormSq τ)
      have hS := h.schurDensity_nonneg hpsh hz (logNormSq τ)
      have hπ := Real.pi_pos
      rw [show ((N + 1 : ℕ) : ℝ) / Real.pi * (partialYY F (z, logNormSq τ) / ‖τ‖ ^ 2) *
          schurDensity F (z, logNormSq τ) =
          ((N + 1 : ℕ) : ℝ) / Real.pi * partialYY F (z, logNormSq τ) *
            schurDensity F (z, logNormSq τ) * (1 / ‖τ‖ ^ 2) by ring,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      ring
    have h2 : ∫⁻ τ in puncturedPlane, H (logNormSq τ) * ENNReal.ofReal (1 / ‖τ‖ ^ 2) =
        ∫⁻ τ, H (logNormSq τ) * ENNReal.ofReal (1 / ‖τ‖ ^ 2) := by
      rw [Measure.restrict_eq_self_of_ae_mem]
      have := compl_mem_ae_iff.mpr volume_puncturedPlane_compl
      rwa [compl_compl] at this
    have h4 : ∫⁻ y, H y = ENNReal.ofReal (((N + 1 : ℕ) : ℝ) / Real.pi) *
        ∫⁻ y, ENNReal.ofReal (partialYY F (z, y)) *
          G (z, legendreArg F z (partialY F (z, y))) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      funext y
      rw [h.legendreArg_partialY hz, hH]
      simp only
      rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
    have h5 : ∫⁻ lam in Ioo α β, G (z, legendreArg F z lam) =
        ∫⁻ y, ENNReal.ofReal (partialYY F (z, y)) *
          G (z, legendreArg F z (partialY F (z, y))) := by
      have himage : (fun y => partialY F (z, y)) '' univ = Ioo α β := by
        ext lam
        constructor
        · rintro ⟨y, -, rfl⟩
          exact h.partialY_mem z hz y
        · intro hlam
          exact ⟨legendreArg F z lam, mem_univ _, h.partialY_legendreArg hz hlam⟩
      have hcv := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
        (fun y _ => (hasDerivAt_partialY_slice (h.contDiffAt_two hz y)).hasDerivWithinAt)
        ((h.strictMono_partialY hz).injective.injOn) (fun lam => G (z, legendreArg F z lam))
      rw [himage, Measure.restrict_univ] at hcv
      rw [hcv]
      congr 1
      funext y
      rw [abs_of_pos (h.partialYY_pos z hz y)]
    rw [h1, h2, lintegral_logRadial_polar hHm, h4, ← h5, ← mul_assoc,
      ← ENNReal.ofReal_mul Real.pi_pos.le]
    congr 1
    rw [show Real.pi * (((N + 1 : ℕ) : ℝ) / Real.pi) = ((N + 1 : ℕ) : ℝ) by
      field_simp [Real.pi_ne_zero]]
    exact ENNReal.ofReal_natCast _
  rw [setLIntegral_congr_fun h.isOpen.measurableSet hinner,
    lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)]
  congr 1
  have hcont : ContinuousOn (fun q : ComplexModel N × ℝ =>
      ((q.1, legendreArg F q.1 q.2) : ComplexModel N × ℝ))
      ((D : Set (ComplexModel N)) ×ˢ Ioo α β) := by
    intro q hq
    have hY := h.contDiffAt_legendreArg hq.1 hq.2
    rw [Prod.mk.eta] at hY
    exact (continuousAt_fst.prodMk hY.continuousAt).continuousWithinAt
  have hae : AEMeasurable (Function.uncurry fun (z : ComplexModel N) (lam : ℝ) =>
      G (z, legendreArg F z lam))
      ((volume.restrict (D : Set (ComplexModel N))).prod (volume.restrict (Ioo α β))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hGm.comp_aemeasurable
      (hcont.aemeasurable (h.isOpen.measurableSet.prod measurableSet_Ioo))
  rw [lintegral_lintegral_swap hae]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro lam hlam
  apply setLIntegral_congr_fun h.isOpen.measurableSet
  intro z hz
  simp only [hG]
  rw [h.smoothDensity_legendreValue hz hlam]

/-- **`tok-wn-leg:smooth`** (WN21 Theorem 3.3, smooth case): for every measurable `g ≥ 0`,
`∫ g(z, log |τ|²) d MA(u) = (N + 1) ∫_α^β ∫ g(z, Y(z, λ)) d MA(û_λ)(z) dλ`, with TN's
non-pluripolar measures `truncationLimitMeasure` of `u(z, τ) = F(z, log |τ|²)` on `D × ℂ*` and of
the partial Legendre transforms `û_λ` on `D`. -/
theorem lintegral_truncationLimitMeasure_logRadial
    (hu : PlurisubharmonicOn (productModelFunction (logRadialFunction F)) (puncturedProductOpens D))
    (hû : ∀ lam : ℝ, PlurisubharmonicOn (partialLegendre (logRadialFunction F) lam) D)
    {g : ComplexModel N × ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ q, g ((stripModelEquiv N q).1, logNormSq (stripModelEquiv N q).2)
        ∂(MongeAmpere.truncationLimitMeasure (puncturedProductOpens D)
          (productModelFunction (logRadialFunction F)) hu) =
      ((N + 1 : ℕ) : ℝ≥0∞) * ∫⁻ lam in Ioo α β, ∫⁻ z, g (z, legendreArg F z lam)
        ∂(MongeAmpere.truncationLimitMeasure D (partialLegendre (logRadialFunction F) lam)
          (hû lam)) := by
  have hU := h.isSmoothPshOn_uTilde hpsh
  have hgm : Measurable fun q : ComplexModel (N + 1) =>
      g ((stripModelEquiv N q).1, logNormSq (stripModelEquiv N q).2) :=
    hg.comp ((measurable_fst.comp (stripModelEquiv N).continuous.measurable).prodMk
      (measurable_logNormSq.comp (measurable_snd.comp (stripModelEquiv N).continuous.measurable)))
  have hL : MongeAmpere.truncationLimitMeasure (puncturedProductOpens D)
      (productModelFunction (logRadialFunction F)) hu = smoothMeasure _ (uTilde F) hU :=
    (SGPT.MongeAmpere.truncationLimitMeasure_smooth_sub_const hU).1
  rw [hL, smoothMeasure, lintegral_withDensity_eq_lintegral_mul _
    (f := fun z => ENNReal.ofReal (smoothDensity (uTilde F) z))
    (measurable_smoothDensity _).ennreal_ofReal hgm]
  simp only [Pi.mul_apply]
  rw [show ((puncturedProductOpens D : Opens (ComplexModel (N + 1))) : Set (ComplexModel (N + 1))) =
    puncturedDomain (D : Set (ComplexModel N)) from rfl, h.lintegral_puncturedDomain_eq hpsh hg]
  congr 1
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro lam hlam
  have hW := h.isSmoothPshOn_legendreValue hpsh hlam
  have hR : MongeAmpere.truncationLimitMeasure D (partialLegendre (logRadialFunction F) lam)
      (hû lam) = smoothMeasure D (fun z => legendreValue F z lam) hW := by
    rw [truncationLimitMeasure_congr (hû lam) hW.2.1
      (fun z hz => h.partialLegendre_logRadial_eq hz hlam)]
    exact (SGPT.MongeAmpere.truncationLimitMeasure_smooth_sub_const hW).1
  have hgz : AEMeasurable (fun z : ComplexModel N => g (z, legendreArg F z lam))
      (volume.restrict (D : Set (ComplexModel N))) := by
    have hc : ContinuousOn (fun z : ComplexModel N => ((z, legendreArg F z lam) :
        ComplexModel N × ℝ)) D := fun z hz =>
      (continuousAt_id.prodMk (h.contDiffAt_legendreArg_slice hz hlam).continuousAt).continuousWithinAt
    exact hg.comp_aemeasurable (hc.aemeasurable h.isOpen.measurableSet)
  simp only
  rw [hR, smoothMeasure, lintegral_withDensity_eq_lintegral_mul₀
    (f := fun z => ENNReal.ofReal (smoothDensity (fun z' => legendreValue F z' lam) z))
    (measurable_smoothDensity _).ennreal_ofReal.aemeasurable hgz]
  rfl

end IsSmoothLegendreData

end SGPT.Okounkov.TranscendentalWN
