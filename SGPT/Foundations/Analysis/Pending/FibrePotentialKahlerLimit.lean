import SGPT.Foundations.Analysis.Pending.SupNormalizedPotentialLimit
import SGPT.Foundations.Analysis.Pending.ProductStokesLevi
import SGPT.Foundations.Analysis.Pending.ContinuousThetaPsh
import SGPT.Foundations.Analysis.Pending.CoordinateWedgeFamilyPairing
import SGPT.Foundations.Analysis.Pending.MixedMassClassInvariance

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The limit of the fibre integrals `p₁_*([X × X] ∧ α_ε^n ∧ p₂^*ω)` is a Kähler current

Source: Demailly--Păun, proof of Theorem 2.12 (`dp04-kahler-cone:2.12`, the paragraph after (2.10));
Boucksom, proof of Theorem 4.8 (`bou02-volume:4.8`).  TN.4 plan, step B6, finding F6 route (i)
(the proof of Boucksom's mass estimate, §1 F6 "STATUS (run 0148)", REMAINING): the ε-level
identity `R_ε = c_ε b_ε + ddᶜv_ε` (`ProductStokesLevi.leviTestIdentity_fibrePushforward`) passes to a
weak limit along the ultrafilter that produces `Θ = lim [X × X] ∧ α_ε^n`, and the lower bound
`Θ ≥ δ [Δ]` turns the limit into a Kähler current.

Let `X` be compact connected of dimension `n = q + 1` with a Kähler form `ω`, `b` a closed real
`(1,1)`-form, `b_ε = b + εω`, and on `X × X` let `α_ε = p₁^*b_ε + p₂^*b_ε + ddᶜg_ε` be semipositive.

* `thetaPlurisubharmonic_fibreV`: the continuous fibre potential `v_ε` of `R_ε` is a `(c_ε b_ε)`-psh
  FUNCTION, `c_ε = n ∫_X b_ε^{n-1} ∧ ω` (the ε-level link + TN23's (b1),
  `ContinuousThetaPsh.thetaPlurisubharmonic_of_continuous_of_isLocallyThetaPshDistribution`).
* `fibreIntegral_add_smul_eq_sum`, `continuous_fibreIntegral_add_smul`: `ε ↦ ∫_X b_ε^q ∧ ω` is a
  polynomial in `ε` (multilinearity of the mixed density), hence continuous.
* `exists_kahlerCurrent_of_tendsto_fibrePushforward` (general backgrounds `b_i`, dominated `c_i b_i`)
  and `exists_kahlerCurrent_of_tendsto_prodForm` (`b_i = b + ε_i ω`, `ε_i → 0`): if
  `[X × X] ∧ α_i^n → Θ` along an ultrafilter and `Θ - δ [Δ] ≥ 0` with `δ > 0`, then
  `{n (∫_X b^{n-1} ∧ ω) · b}` contains a Kähler current with representative
  `n (∫_X b^{n-1} ∧ ω) · b` and lower bound `δ ω`.

Nothing is assumed about `g_ε` beyond chart-smoothness and semipositivity of `α_ε`: in B6 these come
from Yau's theorem (`hYau`, a hypothesis of the nef-core theorem, never an interface here), and
`Θ - δ[Δ] ≥ 0` from TN23's `DiagonalLowerBound`.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.FibrePotentialKahlerLimit

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms PositiveProductCurrents IntegrationCurrent TopDegreeDensity
  SmoothCurrentTraceMeasure SmoothDDCForm ManifoldTubePositivity PositivityLeviLink
  FibrePushforwardProductForm DiagonalFibreIntegration ProductStokesLevi
  SupNormalizedPotentialLimit
open scoped ProductComplexManifold Manifold
open ProductComplexManifold

variable {q : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (q + 1)) X]
  [IsComplexManifold (q + 1) X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-! ### The fibre potential is a `θ`-psh function -/

/-- **The fibre potential of a semipositive `α` is `(c b)`-psh**, `c = (q + 1) ∫_X b^q ∧ ω`. -/
theorem thetaPlurisubharmonic_fibreV (w : KahlerBackground (q + 1) X)
    (b : ClosedRealOneOneForm (q + 1) X) {g : X × X → ℝ}
    (hg : ChartSmooth (n := (q + 1) + (q + 1)) g)
    (hα : ThetaPlurisubharmonic (prodForm b b + ddcClosedForm g hg).val (fun _ => 0)) :
    ThetaPlurisubharmonic ((((q + 1 : ℕ) : ℝ) * fibreIntegral w b w.form.val) • b).val
      fun x => ((fibreV w (prodForm b b) (prodForm b b + ddcClosedForm g hg) g x : ℝ) : EReal) :=
  ContinuousThetaPsh.thetaPlurisubharmonic_of_continuous_of_isLocallyThetaPshDistribution volume
    (continuous_fibreV w _ _ (ChartSmooth.continuous hg))
    (locallyIntegrableOn_fibreV w _ _ (ChartSmooth.continuous hg))
    fun e => isLocallyThetaPshDistribution_fibreV w b hg hα
      (LocalPotentials.closedRealOneOne_hasLocalPotentials _) e

/-! ### Algebra of the smooth currents `[X] ∧ θ` -/

/-- `[X] ∧ (θ₁ + θ₂) = [X] ∧ θ₁ + [X] ∧ θ₂` on test forms. -/
theorem smoothCurrent_add_apply (w : KahlerBackground (q + 1) X)
    (θ₁ θ₂ : ClosedRealOneOneForm (q + 1) X) (η : testSpace (q + 1) X q) :
    smoothCurrent (q := q) (p := 1) w ![θ₁ + θ₂] η =
      smoothCurrent (q := q) (p := 1) w ![θ₁] η + smoothCurrent (q := q) (p := 1) w ![θ₂] η := by
  have h := smoothCurrent_sub_apply w (θ₁ + θ₂) θ₂ η
  rw [add_sub_cancel_right] at h
  linarith

/-! ### The fibre constant is a polynomial in `ε` -/

/-- The slots `b, …, b, ω` (`q` copies of `b`). -/
def baseSlots (w : KahlerBackground (q + 1) X) (b : ClosedRealOneOneForm (q + 1) X) :
    Fin (q + 1) → ClosedRealOneOneForm (q + 1) X :=
  Fin.snoc (fun _ : Fin q => b) w.form

/-- The slots `ω, …, ω, 0` (`q` copies of `ω`). -/
def pertSlots (w : KahlerBackground (q + 1) X) : Fin (q + 1) → ClosedRealOneOneForm (q + 1) X :=
  Fin.snoc (fun _ : Fin q => w.form) 0

theorem topDensity_fibreForm_coeff (w : KahlerBackground (q + 1) X)
    (b : ClosedRealOneOneForm (q + 1) X) (ε : ℝ) (e : ComplexChart (q + 1) X)
    (z : ComplexModel (q + 1)) :
    topDensity ((wedgeTwo (formPow (b + ε • w.form).val q) w.form.val).coeff e z) =
      ∑ s : Finset (Fin (q + 1)), (∏ i, if i ∈ s then (1 : ℝ) else ε) *
        topDensity ((MixedMassClassInvariance.slotForm
          (s.piecewise (baseSlots w b) (pertSlots w))).coeff e z) := by
  classical
  rw [wedgeTwo_coeff, formPow_coeff, formPower_eq_wedgeProd, ← wedgeProd_snoc,
    topDensity_wedgeProd]
  have hsplit : (Fin.snoc (fun _ : Fin q => (b + ε • w.form).val.coeff e z) (w.form.val.coeff e z) :
      Fin (q + 1) → CoordinateRealTwoForm (q + 1)) =
      (fun i => (baseSlots w b i).val.coeff e z) + fun i => ε • (pertSlots w i).val.coeff e z := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [baseSlots, pertSlots]
    · simp [baseSlots, pertSlots, ClosedRealOneOneForm.coeff_add,
        ClosedRealOneOneForm.coeff_smul]
  rw [hsplit, ← actualMixedTopDensityMultilinear_apply, MultilinearMap.map_add_univ]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hpw : s.piecewise (fun i => (baseSlots w b i).val.coeff e z)
      (fun i => ε • (pertSlots w i).val.coeff e z) =
      fun i => (if i ∈ s then (1 : ℝ) else ε) •
        (s.piecewise (baseSlots w b) (pertSlots w) i).val.coeff e z := by
    funext i
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  rw [hpw, MultilinearMap.map_smul_univ, smul_eq_mul,
    MixedMassClassInvariance.topDensity_slotForm_coeff]
  rfl

theorem topRatio_fibreForm (w : KahlerBackground (q + 1) X)
    (b : ClosedRealOneOneForm (q + 1) X) (ε : ℝ) (x : X) :
    topRatio w.form.val (wedgeTwo (formPow (b + ε • w.form).val q) w.form.val) x =
      ∑ s : Finset (Fin (q + 1)), (∏ i, if i ∈ s then (1 : ℝ) else ε) *
        topRatio w.form.val (MixedMassClassInvariance.slotForm
          (s.piecewise (baseSlots w b) (pertSlots w))) x := by
  simp only [topRatio, chartRatio, topDensity_fibreForm_coeff, Finset.sum_div, mul_div_assoc]

/-- **The fibre constant is a polynomial in `ε`**:
`∫_X (b + εω)^q ∧ ω = Σ_s (∏_{i ∉ s} ε) ∫_X (slots of s)`. -/
theorem fibreIntegral_add_smul_eq_sum (w : KahlerBackground (q + 1) X)
    (b : ClosedRealOneOneForm (q + 1) X) (ε : ℝ) :
    fibreIntegral w (b + ε • w.form) w.form.val =
      ∑ s : Finset (Fin (q + 1)), (∏ i, if i ∈ s then (1 : ℝ) else ε) *
        ∫ x, topRatio w.form.val (MixedMassClassInvariance.slotForm
          (s.piecewise (baseSlots w b) (pertSlots w))) x ∂(kahlerVolume w) := by
  classical
  rw [fibreIntegral]
  simp_rw [topRatio_fibreForm]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun s _ => integral_const_mul _ _
  · intro s _
    exact ((continuous_topRatio w.isKahler.1 _).const_mul _).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))

theorem continuous_fibreIntegral_add_smul (w : KahlerBackground (q + 1) X)
    (b : ClosedRealOneOneForm (q + 1) X) :
    Continuous fun ε : ℝ => fibreIntegral w (b + ε • w.form) w.form.val := by
  classical
  simp_rw [fibreIntegral_add_smul_eq_sum]
  refine continuous_finsetSum _ fun s _ => ?_
  exact Continuous.mul (continuous_finsetProd _ fun i _ =>
    continuous_if_const _ (fun _ => continuous_const) fun _ => continuous_id) continuous_const

/-- The backgrounds `c(ε) (b + εω)` converge to `c(0) b` on test forms as `ε → 0`. -/
theorem tendsto_smoothCurrent_fibreConst (w : KahlerBackground (q + 1) X)
    (b : ClosedRealOneOneForm (q + 1) X) {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hε : Tendsto ε l (𝓝 0)) (η : testSpace (q + 1) X q) :
    Tendsto (fun i => smoothCurrent (q := q) (p := 1) w
        ![(((q + 1 : ℕ) : ℝ) * fibreIntegral w (b + ε i • w.form) w.form.val) •
          (b + ε i • w.form)] η) l
      (𝓝 (smoothCurrent (q := q) (p := 1) w
        ![(((q + 1 : ℕ) : ℝ) * fibreIntegral w b w.form.val) • b] η)) := by
  have hc : Tendsto (fun i => ((q + 1 : ℕ) : ℝ) * fibreIntegral w (b + ε i • w.form) w.form.val)
      l (𝓝 (((q + 1 : ℕ) : ℝ) * fibreIntegral w b w.form.val)) := by
    have h := ((continuous_fibreIntegral_add_smul w b).tendsto 0).comp hε
    simp only [zero_smul, add_zero] at h
    exact h.const_mul _
  simp_rw [smoothCurrent_smul_apply, smoothCurrent_add_apply, smoothCurrent_smul_apply]
  have hb : Tendsto (fun i => smoothCurrent (q := q) (p := 1) w ![b] η +
      ε i * smoothCurrent (q := q) (p := 1) w ![w.form] η) l
      (𝓝 (smoothCurrent (q := q) (p := 1) w ![b] η)) := by
    have := (tendsto_const_nhds (x := smoothCurrent (q := q) (p := 1) w ![b] η)).add
      (hε.mul_const (smoothCurrent (q := q) (p := 1) w ![w.form] η))
    simpa only [zero_mul, add_zero] using this
  exact hc.mul hb

/-! ### The limit -/

/-- **The B6 limit, general backgrounds.**  Along an ultrafilter, let
`Θ_i = [X × X] ∧ (p₁^*b_i + p₂^*b_i + ddᶜg_i)^{q+1}` (semipositive `α_i`) converge to `Θ` with
`Θ - δ [Δ] ≥ 0`, `δ > 0`; let the backgrounds `c_i b_i` (`c_i = (q+1) ∫_X b_i^q ∧ ω`) be dominated by
one closed form and converge to `θ` on test forms.  Then `{θ}` contains a Kähler current with
representative `θ` and lower bound `δ ω`. -/
theorem exists_kahlerCurrent_of_tendsto_fibrePushforward [ConnectedSpace X] [Nonempty X]
    (w : KahlerBackground (q + 1) X) {ι : Type*} (U : Ultrafilter ι)
    (b : ι → ClosedRealOneOneForm (q + 1) X) (g : ι → X × X → ℝ)
    (hg : ∀ i, ChartSmooth (n := (q + 1) + (q + 1)) (g i))
    (hα : ∀ i, ThetaPlurisubharmonic (prodForm (b i) (b i) + ddcClosedForm (g i) (hg i)).val
      (fun _ => 0))
    (Θfix : ClosedRealOneOneForm (q + 1) X)
    (hdom : ∀ i, (Θfix - (((q + 1 : ℕ) : ℝ) * fibreIntegral w (b i) w.form.val) • b i).val.IsSemipositive)
    {Θ : ProductCurrent ((q + 1) + (q + 1)) (X × X) (q + 1)}
    (hΘ : ∀ φ, Tendsto (fun i => smoothCurrent (q := q + 1) (p := q + 1) (prodKahlerBackground w w)
      (fun _ => prodForm (b i) (b i) + ddcClosedForm (g i) (hg i)) φ) (U : Filter ι) (𝓝 (Θ φ)))
    (θ : ClosedRealOneOneForm (q + 1) X)
    (hθ : ∀ η, Tendsto (fun i => smoothCurrent (q := q) (p := 1) w
      ![(((q + 1 : ℕ) : ℝ) * fibreIntegral w (b i) w.form.val) • b i] η) (U : Filter ι)
      (𝓝 (smoothCurrent (q := q) (p := 1) w ![θ] η)))
    {δ : ℝ} (hδ : 0 < δ) (hΘδ : IsPositive (Θ - δ • diagonalCurrent w)) :
    ∃ K : NonKahlerLocus.KahlerCurrent (RealBottChern.ofRepresentative θ),
      K.representative = θ ∧ K.lowerBound = KahlerBackground.smul hδ w := by
  set c : ι → ℝ := fun i => ((q + 1 : ℕ) : ℝ) * fibreIntegral w (b i) w.form.val with hcdef
  set v : ι → X → ℝ := fun i =>
    fibreV w (prodForm (b i) (b i)) (prodForm (b i) (b i) + ddcClosedForm (g i) (hg i)) (g i)
    with hvdef
  have hv : ∀ i, Continuous (v i) := fun i =>
    continuous_fibreV w _ _ (ChartSmooth.continuous (hg i))
  -- the positivity `R - δ [X] ∧ ω ≥ 0` of the limit
  have hR : IsPositive (fibrePushforward w.form.2.2 Θ -
      smoothCurrent (q := q) (p := 1) w ![(KahlerBackground.smul hδ w).form]) := by
    have h := isPositive_fibrePushforward_sub w w.form.2.2
      (fun e z hz => isSemipositiveOneOne_of_isHermitian w.isKahler.1 e hz) hΘδ
    have heq : δ • wedge w.form.2.2 (integrationCurrent w) =
        smoothCurrent (q := q) (p := 1) w ![(KahlerBackground.smul hδ w).form] := by
      ext η
      rw [KahlerBackground.smul_form, smoothCurrent_smul_apply, LinearMap.smul_apply,
        smul_eq_mul, ← fibrePushforward_diagonalCurrent w w.form.2.2,
        fibrePushforward_diagonalCurrent_eq_smoothCurrent]
    rwa [heq] at h
  exact exists_kahlerCurrent_of_tendsto_leviTest w U
    (fun i => fibrePushforward w.form.2.2 (smoothCurrent (q := q + 1) (p := q + 1)
      (prodKahlerBackground w w) (fun _ => prodForm (b i) (b i) + ddcClosedForm (g i) (hg i))))
    (fibrePushforward w.form.2.2 Θ) (fun η => tendsto_fibrePushforward_apply w.form.2.2 hΘ η)
    (fun i => c i • b i) θ hθ Θfix hdom v hv
    (fun i => thetaPlurisubharmonic_fibreV w (b i) (hg i) (hα i))
    (fun i => leviTestIdentity_fibrePushforward w (b i) (hg i))
    (KahlerBackground.smul hδ w) hR

/-- **The B6 limit for `b_ε = b + εω`** (dp04 2.12, the limit step).  Along an ultrafilter on which
`ε_i ∈ [0, 1]` tends to `0`, let `Θ_i = [X × X] ∧ (p₁^*b_i + p₂^*b_i + ddᶜg_i)^{q+1}` with
`b_i = b + ε_i ω` and semipositive `α_i` converge to `Θ` with `Θ - δ [Δ] ≥ 0`, `δ > 0`.  Then the
class of `c · b`, `c = (q + 1) ∫_X b^q ∧ ω`, contains a Kähler current with representative `c · b` and
lower bound `δ ω`. -/
theorem exists_kahlerCurrent_of_tendsto_prodForm [ConnectedSpace X] [Nonempty X]
    (w : KahlerBackground (q + 1) X) (b : ClosedRealOneOneForm (q + 1) X) {ι : Type*}
    (U : Ultrafilter ι) (ε : ι → ℝ) (hε : ∀ i, ε i ∈ Icc (0 : ℝ) 1)
    (hε0 : Tendsto ε (U : Filter ι) (𝓝 0)) (g : ι → X × X → ℝ)
    (hg : ∀ i, ChartSmooth (n := (q + 1) + (q + 1)) (g i))
    (hα : ∀ i, ThetaPlurisubharmonic
      (prodForm (b + ε i • w.form) (b + ε i • w.form) + ddcClosedForm (g i) (hg i)).val
      (fun _ => 0))
    {Θ : ProductCurrent ((q + 1) + (q + 1)) (X × X) (q + 1)}
    (hΘ : ∀ φ, Tendsto (fun i => smoothCurrent (q := q + 1) (p := q + 1) (prodKahlerBackground w w)
      (fun _ => prodForm (b + ε i • w.form) (b + ε i • w.form) + ddcClosedForm (g i) (hg i)) φ)
      (U : Filter ι) (𝓝 (Θ φ)))
    {δ : ℝ} (hδ : 0 < δ) (hΘδ : IsPositive (Θ - δ • diagonalCurrent w)) :
    ∃ K : NonKahlerLocus.KahlerCurrent (RealBottChern.ofRepresentative
        ((((q + 1 : ℕ) : ℝ) * fibreIntegral w b w.form.val) • b)),
      K.representative = (((q + 1 : ℕ) : ℝ) * fibreIntegral w b w.form.val) • b ∧
        K.lowerBound = KahlerBackground.smul hδ w := by
  -- a uniform bound on the fibre constants for `ε ∈ [0, 1]`
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (((continuous_fibreIntegral_add_smul w b).const_mul (((q + 1 : ℕ) : ℝ))).continuousOn
      (s := Icc (0 : ℝ) 1))
  obtain ⟨K, hK⟩ := exists_isSemipositive_smul_sub w b C
  refine exists_kahlerCurrent_of_tendsto_fibrePushforward w U (fun i => b + ε i • w.form) g hg hα
    (K • w.form) (fun i => ?_) hΘ _ (tendsto_smoothCurrent_fibreConst w b hε0) hδ hΘδ
  have hci := hC (ε i) (hε i)
  rw [Real.norm_eq_abs] at hci
  exact hK _ _ hci (hε i).1 (hε i).2

end SGPT.Foundations.Analysis.Pending.FibrePotentialKahlerLimit
