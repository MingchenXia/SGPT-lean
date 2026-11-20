import SGPT.Foundations.Analysis.Pending.PositivityLeviLink
import SGPT.Foundations.Analysis.Pending.ThetaPshUniformL1Bound
import SGPT.Foundations.Analysis.Pending.LocalPotentials
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.SmoothDistribution

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Sup-normalized potentials: uniform `L¹` bounds, chart limits and the limit Kähler current

Source: Guedj--Zeriahi, *Degenerate complex Monge--Ampère equations*, Proposition 8.5
(sup-normalized `θ`-psh functions form a relatively compact family in `L¹`); Demailly--Păun, proof
of Theorem 2.12 (`dp04-kahler-cone:2.12`), Boucksom, proof of Theorem 4.8 (`bou02-volume:4.8`):
the potentials `v_ε` of the currents `R_ε = θ_ε + ddᶜv_ε` are normalized by their supremum, have a
weak limit `V`, and `R = lim R_ε = θ + ddᶜV`.  TN.4 plan, step B6, finding F6 route (i), piece (b2)
and the limit (the proof of Boucksom's mass estimate, §1 F6 "STATUS (run 0148)").

Let `M` be a compact **connected** complex manifold.

* `supNormalize v = v - sup v`; for continuous `v` it is `≤ 0` and vanishes somewhere.
* `thetaPlurisubharmonic_of_sub_isSemipositive`: a `θ`-psh function is `Θ`-psh when `Θ - θ ≥ 0`.
* `exists_integral_abs_supNormalize_le` (**the uniform bound**): for a fixed closed real
  `(1,1)`-form `Θ`, a chart `e` and a compact `K ⊆ e.target`, one constant `B` bounds
  `∫_K |supNormalize v ∘ e⁻¹|` for EVERY continuous `θ`-psh `v` and EVERY `θ` with `Θ - θ ≥ 0`
  (`ThetaPshUniformL1Bound.exists_lintegral_compact_le` with level `0`).
* `exists_isSemipositive_smul_sub`: `Θ = Kω` dominates `c (b + εω)` uniformly for `|c| ≤ C`, `0 ≤ ε ≤ 1`.
* `exists_isChartLimit_supNormalize`: along any ultrafilter, the sup-normalized potentials of a
  dominated family have weak limits in every chart.
* `LeviTestIdentity.supNormalize`: the Levi identity is unchanged by the normalization (the Levi
  form of a constant vanishes).
* `exists_kahlerCurrent_of_tendsto_leviTest` (**the limit**): if `P_i → R`, `[X] ∧ θ_i → [X] ∧ θ`,
  the `θ_i` are dominated by one `Θ`, `P_i` satisfies the Levi identity with `θ_i` and continuous
  `θ_i`-psh potentials `v_i`, and `R - [X] ∧ ω_δ ≥ 0`, then `{θ}` contains a Kähler current with
  representative `θ` and lower bound `ω_δ`.

No positivity of the approximating currents and no Monge--Ampère equation is used here; the
`θ_i`-psh property of the potentials is a hypothesis (for the fibre potentials of B6 it follows
from the `ε`-level link `ProductStokesLevi.isLocallyThetaPshDistribution_fibreV`).
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions ENNReal

namespace SGPT.Foundations.Analysis.Pending.SupNormalizedPotentialLimit

open FirstPass FirstPass.PositiveClasses ProductTestForms PositiveProductCurrents
  SmoothCurrentTraceMeasure ThetaPshChartLimitGluing PositivityLeviLink

/-! ### Sup-normalization -/

section Normalize

variable {M : Type*} [TopologicalSpace M]

/-- `v - sup v`. -/
def supNormalize (v : M → ℝ) (x : M) : ℝ :=
  v x - ⨆ y, v y

theorem continuous_supNormalize {v : M → ℝ} (hv : Continuous v) : Continuous (supNormalize v) :=
  hv.sub continuous_const

theorem supNormalize_nonpos [CompactSpace M] {v : M → ℝ} (hv : Continuous v) (x : M) :
    supNormalize v x ≤ 0 := by
  have h : v x ≤ ⨆ y, v y := le_ciSup (isCompact_range hv).bddAbove x
  simp only [supNormalize]
  linarith

theorem exists_supNormalize_eq_zero [CompactSpace M] [Nonempty M] {v : M → ℝ}
    (hv : Continuous v) : ∃ x, supNormalize v x = 0 := by
  obtain ⟨x, hx⟩ := (isCompact_range hv).sSup_mem (range_nonempty v)
  refine ⟨x, ?_⟩
  simp only [supNormalize, iSup]
  rw [hx, sub_self]

end Normalize

/-! ### Domination and the uniform bound -/

section Bound

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Enlarging the background: a `θ`-psh function is `Θ`-psh when `Θ - θ` is semipositive. -/
theorem thetaPlurisubharmonic_of_sub_isSemipositive {θ Θ : ClosedRealOneOneForm n M}
    {u : M → EReal} (hu : ThetaPlurisubharmonic θ.val u) (h : (Θ - θ).val.IsSemipositive) :
    ThetaPlurisubharmonic Θ.val u := by
  have h' := LocalPotentials.thetaPlurisubharmonic_add_of_semipositive hu h
  rwa [show θ + (Θ - θ) = Θ by abel] at h'

/-- Subtracting the supremum preserves `θ`-plurisubharmonicity. -/
theorem thetaPlurisubharmonic_supNormalize {θ : SmoothRealForm n M 2} {v : M → ℝ}
    (hv : ThetaPlurisubharmonic θ fun x => ((v x : ℝ) : EReal)) :
    ThetaPlurisubharmonic θ fun x => ((supNormalize v x : ℝ) : EReal) := by
  have h := GlobalPotentialTransforms.thetaPlurisubharmonic_sub_const hv (⨆ y, v y)
  convert h using 2 with x
  simp only [supNormalize, EReal.coe_sub]

theorem locallyIntegrableOn_comp_symm {v : M → ℝ} (hv : Continuous v) (e : ComplexChart n M) :
    LocallyIntegrableOn (fun z => v (e.val.symm z)) (chartTarget e) volume :=
  (hv.comp_continuousOn e.val.continuousOn_symm).locallyIntegrableOn
    (chartTarget e).isOpen.measurableSet

/-- **The uniform `L¹` bound for sup-normalized potentials** (GZ Prop. 8.5, uniformly in the
background).  For a closed real `(1,1)`-form `Θ`, a chart `e` and a compact `K ⊆ e.target`, one
constant bounds `∫_K |(v - sup v) ∘ e⁻¹|` for every continuous `θ`-psh `v` and every `θ ≤ Θ`. -/
theorem exists_integral_abs_supNormalize_le [CompactSpace M] [ConnectedSpace M] [Nonempty M]
    (Θ : ClosedRealOneOneForm n M) (e : ComplexChart n M) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKe : K ⊆ e.val.target) :
    ∃ B : ℝ, ∀ (θ : ClosedRealOneOneForm n M) (v : M → ℝ), Continuous v →
      ThetaPlurisubharmonic θ.val (fun x => ((v x : ℝ) : EReal)) →
        (Θ - θ).val.IsSemipositive →
          ∫ z in K, |supNormalize v (e.val.symm z)| ≤ B := by
  obtain ⟨B, hB, hbd⟩ := ThetaPshUniformL1Bound.exists_lintegral_compact_le
    (LocalPotentials.closedRealOneOne_hasLocalPotentials Θ) e hK hKe 0
  refine ⟨B.toReal, fun θ v hv hpsh hdom => ?_⟩
  have hu : ThetaPlurisubharmonic Θ.val fun x => ((supNormalize v x : ℝ) : EReal) :=
    thetaPlurisubharmonic_of_sub_isSemipositive (thetaPlurisubharmonic_supNormalize hpsh) hdom
  have hle : ∀ x, ((supNormalize v x : ℝ) : EReal) ≤ 0 := fun x =>
    EReal.coe_nonpos.mpr (supNormalize_nonpos hv x)
  obtain ⟨x₀, hx₀⟩ := exists_supNormalize_eq_zero hv
  have hx₀' : ∃ x₀, (((-0 : ℝ) : ℝ) : EReal) ≤ ((supNormalize v x₀ : ℝ) : EReal) :=
    ⟨x₀, by rw [hx₀]; simp⟩
  have hlin := hbd _ hu hle hx₀'
  have hfun : ∀ y, (-(((supNormalize v (e.val.symm y)) : ℝ) : EReal)).toENNReal =
      ENNReal.ofReal |supNormalize v (e.val.symm y)| := by
    intro y
    rw [← EReal.coe_neg, EReal.real_coe_toENNReal,
      abs_of_nonpos (supNormalize_nonpos hv _)]
  simp_rw [hfun] at hlin
  have hmeas : AEStronglyMeasurable (fun z => |supNormalize v (e.val.symm z)|)
      (volume.restrict K) :=
    (((continuous_supNormalize hv).comp_continuousOn
      (e.val.continuousOn_symm.mono hKe)).abs).aestronglyMeasurable hK.measurableSet
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => abs_nonneg _) hmeas]
  exact ENNReal.toReal_mono hB.ne hlin

/-- **Uniform domination of the scaled backgrounds**: for a closed real `(1,1)`-form `b` and
`C ≥ 0` there is `K` such that `Kω - c (b + εω)` is semipositive for all `|c| ≤ C` and
`0 ≤ ε ≤ 1`. -/
theorem exists_isSemipositive_smul_sub [CompactSpace M]
    (w : KahlerBackground n M) (b : ClosedRealOneOneForm n M) (C : ℝ) :
    ∃ K : ℝ, ∀ c ε : ℝ, |c| ≤ C → 0 ≤ ε → ε ≤ 1 →
      (K • w.form - c • (b + ε • w.form)).val.IsSemipositive := by
  obtain ⟨A, hA, hdom⟩ :=
    KahlerDomination.exists_pos_forall_isSemipositive_add_smul w ![b, -b]
  refine ⟨C * (A + 1), fun c ε hc hε0 hε1 e z hz v => ?_⟩
  have h1 := hdom 0 e z hz v
  have h2 := hdom 1 e z hz v
  have hω : 0 ≤ w.form.val.coeff e z ![v, Complex.I • v] :=
    KahlerDomination.lineValue_nonneg_of_isHermitian w.isKahler.1 e hz v
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
    ClosedRealOneOneForm.coeff_neg, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.neg_apply,
    smul_eq_mul] at h1 h2
  rw [sub_eq_add_neg]
  simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
    ClosedRealOneOneForm.coeff_neg, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.neg_apply, smul_eq_mul]
  set B := b.val.coeff e z ![v, Complex.I • v]
  set W := w.form.val.coeff e z ![v, Complex.I • v]
  have hcB : -(c * B) ≥ -(|c| * (A * W)) := by
    have hBabs : |B| ≤ A * W := abs_le.mpr ⟨by linarith, by linarith⟩
    have := abs_mul c B ▸ (le_abs_self (c * B))
    nlinarith [abs_nonneg c, abs_nonneg B, mul_le_mul_of_nonneg_left hBabs (abs_nonneg c)]
  have hcε : -(c * (ε * W)) ≥ -(|c| * W) := by
    have h3 : |c * ε * W| ≤ |c| * W := by
      rw [abs_mul, abs_mul, abs_of_nonneg hε0, abs_of_nonneg hω]
      nlinarith [mul_nonneg (mul_nonneg (abs_nonneg c) hω) (sub_nonneg.mpr hε1)]
    have := le_abs_self (c * ε * W)
    nlinarith
  nlinarith [abs_nonneg c, mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ (A + 1) * W)]

/-- **Chart limits of the sup-normalized potentials** along any ultrafilter, for a family of
continuous `θ_i`-psh functions with all `θ_i` dominated by one closed `(1,1)`-form. -/
theorem exists_isChartLimit_supNormalize [CompactSpace M] [ConnectedSpace M] [Nonempty M]
    {ι : Type*} (U : Ultrafilter ι) (Θ : ClosedRealOneOneForm n M)
    (θ : ι → ClosedRealOneOneForm n M) (v : ι → M → ℝ) (hv : ∀ i, Continuous (v i))
    (hpsh : ∀ i, ThetaPlurisubharmonic (θ i).val fun x => ((v i x : ℝ) : EReal))
    (hdom : ∀ i, (Θ - θ i).val.IsSemipositive) :
    ∃ T : ∀ e : ComplexChart n M, 𝓓'(chartTarget e, ℝ),
      ∀ e, IsChartLimit volume (U : Filter ι) (fun i => supNormalize (v i)) e (T e) := by
  refine exists_isChartLimit U _ (fun i e => locallyIntegrableOn_comp_symm
    (continuous_supNormalize (hv i)) e) fun e K hK hKe => ?_
  obtain ⟨B, hB⟩ := exists_integral_abs_supNormalize_le Θ e hK hKe
  exact ⟨B, fun i => hB (θ i) (v i) (hv i) (hpsh i) (hdom i)⟩

end Bound

/-! ### The Levi identity does not see constants -/

section Constant

variable {n : ℕ}

/-- The distributional Levi form of a constant vanishes. -/
theorem distributionalLeviCLM_regularDistribution_const {Ω : Opens (ComplexModel n)} (c : ℝ)
    (a : ComplexModel n) :
    distributionalLeviCLM a (regularDistribution volume (fun _ : ComplexModel n => c)
      ((continuous_const : Continuous fun _ : ComplexModel n => c).locallyIntegrable
        |>.locallyIntegrableOn (Ω : Set (ComplexModel n)))) = 0 := by
  rw [distributionalLeviCLM_regularDistribution (contDiff_const : ContDiff ℝ 2 fun _ => c) a]
  ext φ
  simp [regularDistribution_apply]

/-- Subtracting a constant does not change the Levi form of a regular distribution. -/
theorem distributionalLeviCLM_regularDistribution_sub_const {Ω : Opens (ComplexModel n)}
    {f : ComplexModel n → ℝ} (hf : LocallyIntegrableOn f Ω volume) (c : ℝ)
    (hfc : LocallyIntegrableOn (fun z => f z - c) Ω volume) (a : ComplexModel n) :
    distributionalLeviCLM a (regularDistribution volume (fun z => f z - c) hfc) =
      distributionalLeviCLM a (regularDistribution volume f hf) := by
  have hc : LocallyIntegrableOn (fun _ : ComplexModel n => c) Ω volume :=
    (continuous_const : Continuous fun _ : ComplexModel n => c).locallyIntegrable
      |>.locallyIntegrableOn _
  have h := regularDistribution_sub hf hc
  rw [show regularDistribution volume (fun z => f z - c) hfc =
    regularDistribution volume (fun z => f z - c) (hf.sub hc) from rfl, h, map_sub,
    distributionalLeviCLM_regularDistribution_const, sub_zero]

variable {q : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (q + 1)) X]
  [IsComplexManifold (q + 1) X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **The Levi identity is unchanged by the sup-normalization of the potential.** -/
theorem LeviTestIdentity.supNormalize (w : KahlerBackground (q + 1) X)
    {P : ProductCurrent (q + 1) X q} {θ : ClosedRealOneOneForm (q + 1) X} {v : X → ℝ}
    (hv : Continuous v)
    (h : LeviTestIdentity w P θ fun e =>
      regularDistribution volume (fun z => v (e.val.symm z)) (locallyIntegrableOn_comp_symm hv e)) :
    LeviTestIdentity w P θ fun e =>
      regularDistribution volume (fun z => SupNormalizedPotentialLimit.supNormalize v (e.val.symm z))
        (locallyIntegrableOn_comp_symm (continuous_supNormalize hv) e) := by
  intro e ψ φ a ha hφ hψ
  rw [h e ψ φ a ha hφ hψ]
  congr 2
  exact congrArg (fun T => T φ) (distributionalLeviCLM_regularDistribution_sub_const
    (locallyIntegrableOn_comp_symm hv e) _ _ a).symm

end Constant

/-! ### The limit -/

section Limit

variable {q : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (q + 1)) X]
  [IsComplexManifold (q + 1) X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **The limit Kähler current** (F6, piece (b2) and the limit).  Let `P_i` be currents satisfying
the Levi identity with backgrounds `θ_i` and continuous `θ_i`-psh potentials `v_i`, with all `θ_i`
dominated by one closed `(1,1)`-form `Θ`.  If `P_i → R` and `[X] ∧ θ_i → [X] ∧ θ` weakly along an
ultrafilter, and `R - [X] ∧ ω_δ` is positive, then `{θ}` contains a Kähler current with
representative `θ` and lower bound `ω_δ`; its potential represents the chart limits of the
sup-normalized `v_i`. -/
theorem exists_kahlerCurrent_of_tendsto_leviTest [ConnectedSpace X] [Nonempty X]
    (w : KahlerBackground (q + 1) X) {ι : Type*} (U : Ultrafilter ι)
    (P : ι → ProductCurrent (q + 1) X q) (R : ProductCurrent (q + 1) X q)
    (hPR : ∀ η, Tendsto (fun i => P i η) (U : Filter ι) (𝓝 (R η)))
    (θ : ι → ClosedRealOneOneForm (q + 1) X) (θ' : ClosedRealOneOneForm (q + 1) X)
    (hθ : ∀ η, Tendsto (fun i => smoothCurrent (q := q) (p := 1) w ![θ i] η) (U : Filter ι)
      (𝓝 (smoothCurrent (q := q) (p := 1) w ![θ'] η)))
    (Θ : ClosedRealOneOneForm (q + 1) X) (hdom : ∀ i, (Θ - θ i).val.IsSemipositive)
    (v : ι → X → ℝ) (hv : ∀ i, Continuous (v i))
    (hpsh : ∀ i, ThetaPlurisubharmonic (θ i).val fun x => ((v i x : ℝ) : EReal))
    (hlevi : ∀ i, LeviTestIdentity w (P i) (θ i) fun e =>
      regularDistribution volume (fun z => v i (e.val.symm z))
        (locallyIntegrableOn_comp_symm (hv i) e))
    (ωδ : KahlerBackground (q + 1) X)
    (hR : IsPositive (R - smoothCurrent (q := q) (p := 1) w ![ωδ.form])) :
    ∃ K : NonKahlerLocus.KahlerCurrent (RealBottChern.ofRepresentative θ'),
      K.representative = θ' ∧ K.lowerBound = ωδ := by
  obtain ⟨T, hT⟩ := exists_isChartLimit_supNormalize U Θ θ v hv hpsh hdom
  have hRT : LeviTestIdentity w R θ' T :=
    LeviTestIdentity.of_isChartLimit w (fun i => supNormalize (v i))
      (fun i e => locallyIntegrableOn_comp_symm (continuous_supNormalize (hv i)) e) hPR hθ hT
      (Eventually.of_forall fun i => LeviTestIdentity.supNormalize w (hv i) (hlevi i))
  obtain ⟨K, hKrep, hKlow, -⟩ := exists_kahlerCurrent_of_leviTest (fun i => supNormalize (v i)) w θ'
    ωδ hR (LocalPotentials.closedRealOneOne_hasLocalPotentials _) T hT hRT
  exact ⟨K, hKrep, hKlow⟩

end Limit

end SGPT.Foundations.Analysis.Pending.SupNormalizedPotentialLimit
