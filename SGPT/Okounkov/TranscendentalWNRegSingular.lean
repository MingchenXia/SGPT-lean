import SGPT.Okounkov.TranscendentalWNRegEnvelope
import SGPT.Foundations.Analysis.Pending.ThetaPshUniformL1Bound
import SGPT.Foundations.Analysis.Pending.SmoothMax
import SGPT.Foundations.Analysis.Pending.StokesCutoff
import SGPT.Foundations.Analysis.Pending.RelativePreceqClasses
import SGPT.Foundations.Analysis.Pending.GlobalTubeFunction
import SGPT.Foundations.Analysis.FirstPass.FiniteTranslation
import SGPT.Foundations.Analysis.FirstPass.SmoothPshHessian

/-!
# Berman's estimate for obstacles with a singular weight (package WN-REG)

Package WN-REG (`claude-tok-wn-reg`, node `tok-wn-reg:berman-singular`; `tok-wn:berman` of the WN
chapter in the form used in WN21 §7, Lemma 7.5).  Let `(Y, A)` be a compact connected Kähler
manifold, `f` smooth with `ddᶜf ≤ S A`, and `ψ` a quasi-psh weight, `ddᶜψ ≥ -C A`, continuous with
values in `[-∞, ∞)` and smooth where it is finite (e.g. with analytic singularities).  The envelope
`u = P_A(f - ψ)` is real-valued, and on every compact set `K` where `ψ` is finite it is a uniform
limit of smooth `u_j` with `A + ddᶜu_j` Kähler and
`A + ddᶜu_j ≤ ((1 + S + C) Λ e^{a(f - ψ - m)} + ε) A` on `K` (`m ≤ f - ψ`), with the constants
`a, Λ` of `bermanSmoothEnvelopeStatement`.

## Proof (WN21, proof of Theorem 2.5)

* `exists_le_of_quasiEverywhere_le_on_open` (a Hartogs-type bound): an `A`-psh function which is
  `≤ c₀` quasi-everywhere on a fixed nonempty open set is `≤ C(c₀)` everywhere — from TN's uniform
  `L¹` bound for sup-normalized potentials on a Harnack ball (`ThetaPshUniformL1Bound`).
* `smoothedWeight ψ R = -R - 1 + posPart(max(ψ, -R - 3) + R + 1)` (TN's smooth positive part): it is
  chart-smooth, equals `ψ` where `ψ ≥ -R`, is `≤ -R` where `ψ ≤ -R`, dominates `ψ`, and
  `ddᶜ smoothedWeight ≥ -C A` (convexity of `posPart`, `0 ≤ posPart' ≤ 1`).
* For `R` large the competitors of `f - ψ` and `f - smoothedWeight ψ R` coincide (the Hartogs bound
  controls the competitors where `ψ < -R`), so the envelopes coincide, and Berman's estimate for the
  smooth obstacle `f - smoothedWeight ψ R` (with `S + C`) gives the claim; on `K ⊆ {ψ > -R}` the two
  obstacles agree.
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal

namespace SGPT.Okounkov.TranscendentalWNReg

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-! ### Line-bounded approximation on a set -/

/-- **Line-bounded smooth approximation on a set `K`**: `u` is a uniform limit of chart-smooth
`u_j` with `A + ddᶜu_j` Kähler and, for every `ε > 0`, eventually `A + ddᶜu_j ≤ (b(x) + ε)·A` on
every complex line at every point `x ∈ K`. -/
def HasSmoothLineBoundApproximationOn (A : KahlerBackground N Y) (K : Set Y) (u b : Y → ℝ) :
    Prop :=
  ∃ (uj : ℕ → Y → ℝ) (huj : ∀ j, ChartSmooth (n := N) (uj j)),
    TendstoUniformly uj u atTop ∧
    (∀ j, (A.form + ddcClosedForm (uj j) (huj j)).val.IsKahler) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ (e : ComplexChart N Y) (z : ComplexModel N),
      z ∈ e.val.target → e.val.symm z ∈ K → ∀ v : ComplexModel N,
        (A.form + ddcClosedForm (uj j) (huj j)).val.coeff e z ![v, Complex.I • v] ≤
          (b (e.val.symm z) + ε) * A.form.val.coeff e z ![v, Complex.I • v]

theorem HasSmoothLineBoundApproximation.on {A : KahlerBackground N Y} {u b b' : Y → ℝ}
    (h : HasSmoothLineBoundApproximation A u b) {K : Set Y} (hb : ∀ x ∈ K, b x = b' x) :
    HasSmoothLineBoundApproximationOn A K u b' := by
  obtain ⟨uj, huj, hconv, hK, hbd⟩ := h
  refine ⟨uj, huj, hconv, hK, fun ε hε => (hbd ε hε).mono fun j hj e z hz hzK v => ?_⟩
  rw [← hb _ hzK]
  exact hj e z hz v

/-- **`tok-wn-reg:berman-singular`** (WN21 Theorem 2.5, as used in WN21 Lemma 7.5): Berman's
Laplacian estimate for envelopes `P_A(f - ψ)` with a smooth `f` and a quasi-psh weight `ψ` which is
continuous with values in `[-∞, ∞)` and smooth where finite (e.g. with analytic singularities). -/
def BermanSingularEnvelopeStatement : Prop :=
  ∀ (N : ℕ) (Y : Type u) [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
    [IsComplexManifold N Y] [CompactSpace Y] [ConnectedSpace Y] (A : KahlerBackground N Y),
    ∃ a Λ : ℝ, 0 ≤ a ∧ 0 < Λ ∧
      ∀ (f : Y → ℝ) (hf : ChartSmooth (n := N) f) (S : ℝ), 0 ≤ S →
        (∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
          ∀ v : ComplexModel N, (ddcClosedForm f hf).val.coeff e z ![v, Complex.I • v] ≤
            S * A.form.val.coeff e z ![v, Complex.I • v]) →
      ∀ (ψ : Y → EReal) (C : ℝ), 0 ≤ C → IsThetaPshPotential (C • A.form).val ψ →
        Continuous ψ → GlobalTubeFunction.ChartSmoothOn N (fun y => (ψ y).toReal) {y | ψ y ≠ ⊥} →
      ∀ m : ℝ, (∀ y, (m : EReal) ≤ (f y : EReal) - ψ y) →
        (∀ x, rooftopEnvelope A.form.val (fun y => (f y : EReal) - ψ y) x =
          (((rooftopEnvelope A.form.val (fun y => (f y : EReal) - ψ y) x).toReal : ℝ) : EReal)) ∧
        ∀ K : Set Y, IsCompact K → (∀ y ∈ K, ψ y ≠ ⊥) →
          HasSmoothLineBoundApproximationOn A K
            (fun x => (rooftopEnvelope A.form.val (fun y => (f y : EReal) - ψ y) x).toReal)
            (fun x => (1 + S + C) * Λ * Real.exp (a * (f x - (ψ x).toReal - m)))

/-! ### A Hartogs-type bound -/

/-- **Hartogs-type bound.**  On a compact connected manifold, for a closed real `(1,1)`-form `θ`, a
nonempty open set `W` and a level `c₀` there is `C` such that every `θ`-psh `v` with `v ≤ c₀`
quasi-everywhere on `W` satisfies `v ≤ C` everywhere. -/
theorem exists_le_of_quasiEverywhere_le_on_open [CompactSpace Y] [ConnectedSpace Y]
    (θ : ClosedRealOneOneForm N Y) {W : Set Y} (hW : IsOpen W)
    (hWne : W.Nonempty) (c₀ : ℝ) :
    ∃ C : ℝ, ∀ v : Y → EReal, IsThetaPshPotential θ.val v →
      QuasiEverywhere (n := N) (fun x => x ∈ W → v x ≤ (c₀ : EReal)) → ∀ x, v x ≤ (C : EReal) := by
  obtain ⟨x₁, hx₁⟩ := hWne
  set e := complexChartAt (n := N) x₁ with he
  have hx₁e : x₁ ∈ e.val.source := mem_complexChartAt_source x₁
  have hO : IsOpen (e.val.target ∩ e.val.symm ⁻¹' W) := e.val.isOpen_inter_preimage_symm hW
  have hz₁ : e.val x₁ ∈ e.val.target ∩ e.val.symm ⁻¹' W :=
    ⟨e.val.map_source hx₁e, by rw [mem_preimage, e.val.left_inv hx₁e]; exact hx₁⟩
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.mp hO _ hz₁
  have hθ : HasSmoothLocalPotentials θ.val := LocalPotentials.closedRealOneOne_hasLocalPotentials θ
  obtain ⟨H, hHe, hHz, hHr⟩ :=
    ThetaPshUniformL1Bound.exists_harnackBall hθ e (e.val.map_source hx₁e) hε
  have hball : ball H.z H.r ⊆ e.val.target ∩ e.val.symm ⁻¹' W := by
    rw [hHz]
    exact (ball_subset_ball hHr.le).trans hεO
  obtain ⟨B, hBtop, hB⟩ := ThetaPshUniformL1Bound.HarnackBall.exists_lintegral_le hθ H 1
  set c : ℝ≥0∞ := volume (ball H.z H.r) with hc
  have hc0 : c ≠ 0 := (measure_ball_pos volume _ H.r_pos).ne'
  have hctop : c ≠ ⊤ := measure_ball_lt_top.ne
  refine ⟨c₀ + (B / c).toReal, fun v hv hqe x => ?_⟩
  -- the supremum of `v`
  obtain ⟨M₀, hM₀⟩ := RelativePreceqClasses.exists_le_coe_of_isThetaPshPotential hv
  obtain ⟨y₀, -, hy₀⟩ := hv.2 x univ isOpen_univ (mem_univ x)
  set s : EReal := ⨆ y, v y with hs
  have hsle : s ≤ (M₀ : EReal) := iSup_le hM₀
  have hsbot : s ≠ ⊥ := ne_bot_of_le_ne_bot hy₀ (le_iSup v y₀)
  have hstop : s ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top M₀) hsle
  set sr : ℝ := s.toReal with hsr
  have hsreal : s = (sr : EReal) := (EReal.coe_toReal hstop hsbot).symm
  have hvle : ∀ y, v y ≤ (sr : EReal) := fun y => hsreal ▸ le_iSup v y
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, ((sr - 1 : ℝ) : EReal) < v x₀ := by
    have : ((sr - 1 : ℝ) : EReal) < s := by
      rw [hsreal]
      exact EReal.coe_lt_coe_iff.mpr (by linarith)
    exact lt_iSup_iff.mp this
  -- the sup-normalized potential
  set w : Y → EReal := fun y => v y + ((-sr : ℝ) : EReal) with hw
  have hwpsh : IsThetaPshPotential θ.val w := hv.add_const (-sr)
  have hwle : ∀ y, w y ≤ 0 := by
    intro y
    have h := add_le_add (hvle y) (le_refl ((-sr : ℝ) : EReal))
    rwa [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] at h
  have hwx₀ : ((-1 : ℝ) : EReal) ≤ w x₀ := by
    have h := add_le_add hx₀.le (le_refl ((-sr : ℝ) : EReal))
    rw [← EReal.coe_add] at h
    calc ((-1 : ℝ) : EReal) = ((sr - 1 + -sr : ℝ) : EReal) := by congr 1; ring
      _ ≤ _ := h
  have hint := hB w hwpsh.1 hwle ⟨x₀, hwx₀⟩
  -- on the ball, `v ≤ c₀` almost everywhere
  have hae : ∀ᵐ z ∂volume.restrict (ball H.z H.r),
      ENNReal.ofReal (sr - c₀) ≤ (-w (H.e.val.symm z)).toENNReal := by
    have h1 := (hqe.ae_in_chart H.e volume)
    rw [hHe] at h1 ⊢
    have h2 : ∀ᵐ z ∂volume.restrict (ball H.z H.r), e.val.symm z ∈ W → v (e.val.symm z) ≤ c₀ :=
      ae_restrict_of_ae_restrict_of_subset (hball.trans inter_subset_left) h1
    filter_upwards [h2, ae_restrict_mem measurableSet_ball] with z hz hzb
    have hvz := hz (hball hzb).2
    have hwz : w (e.val.symm z) ≤ ((c₀ + -sr : ℝ) : EReal) := by
      rw [EReal.coe_add]
      exact add_le_add hvz le_rfl
    have hneg : ((sr - c₀ : ℝ) : EReal) ≤ -w (e.val.symm z) := by
      have := EReal.neg_le_neg_iff.mpr hwz
      rw [← EReal.coe_neg] at this
      calc ((sr - c₀ : ℝ) : EReal) = ((-(c₀ + -sr) : ℝ) : EReal) := by congr 1; ring
        _ ≤ _ := this
    calc ENNReal.ofReal (sr - c₀) = ((sr - c₀ : ℝ) : EReal).toENNReal := by
          rw [EReal.real_coe_toENNReal]
      _ ≤ _ := EReal.toENNReal_le_toENNReal hneg
  have hlow : ENNReal.ofReal (sr - c₀) * c ≤ B := by
    calc ENNReal.ofReal (sr - c₀) * c = ∫⁻ _z in ball H.z H.r, ENNReal.ofReal (sr - c₀) := by
          rw [setLIntegral_const]
      _ ≤ ∫⁻ z in ball H.z H.r, (-w (H.e.val.symm z)).toENNReal := lintegral_mono_ae hae
      _ ≤ B := hint
  have hdiv : ENNReal.ofReal (sr - c₀) ≤ B / c := (ENNReal.le_div_iff_mul_le (Or.inl hc0)
    (Or.inl hctop)).mpr hlow
  have hreal : sr - c₀ ≤ (B / c).toReal := by
    by_cases hsc : sr - c₀ ≤ 0
    · exact hsc.trans ENNReal.toReal_nonneg
    · exact (ENNReal.ofReal_le_iff_le_toReal (ENNReal.div_ne_top hBtop.ne hc0)).mp hdiv
  calc v x ≤ (sr : EReal) := hvle x
    _ ≤ ((c₀ + (B / c).toReal : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr (by linarith)

/-! ### The smoothed weight -/

section Weight


/-- The smoothed weight `-R - 1 + SmoothMax.posPart(max(ψ, -R - 3) + R + 1)`: equal to `ψ` where `ψ ≥ -R`,
to the constant `-R - 1` where `ψ < -R - 2`. -/
def smoothedWeight (ψ : Y → EReal) (R : ℝ) (y : Y) : ℝ :=
  -R - 1 + SmoothMax.posPart ((max (ψ y) ((-R - 3 : ℝ) : EReal)).toReal + R + 1)

theorem le_smoothPosPart (t : ℝ) : t ≤ SmoothMax.posPart t := by
  rcases le_total 1 t with h | h
  · rw [SmoothMax.posPart_eq_self h]
  · have := SmoothMax.sub_posPart_monotone h
    simp only [SmoothMax.posPart_eq_self le_rfl, sub_self] at this
    linarith

theorem smoothPosPart_le_one {t : ℝ} (ht : t ≤ 1) : SmoothMax.posPart t ≤ 1 := by
  have := SmoothMax.posPart_monotone ht
  rwa [SmoothMax.posPart_eq_self le_rfl] at this

theorem deriv_deriv_smoothPosPart_nonneg (t : ℝ) : 0 ≤ deriv (deriv SmoothMax.posPart) t := by
  rw [SmoothMax.deriv_posPart]
  exact ((SmoothMax.contDiff_trans.differentiable (by simp)) t).hasDerivAt.nonneg_of_monotone SmoothMax.trans_monotone

variable {ψ : Y → EReal} {R : ℝ}

omit [TopologicalSpace Y] in
theorem smoothedWeight_eq_toReal {y : Y} (hψ : ψ y ≠ ⊤) (h : ((-R : ℝ) : EReal) ≤ ψ y) :
    smoothedWeight ψ R y = (ψ y).toReal := by
  have hmax : max (ψ y) ((-R - 3 : ℝ) : EReal) = ψ y :=
    max_eq_left ((EReal.coe_le_coe_iff.mpr (by linarith)).trans h)
  have hbot : ψ y ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h
  have ht : -R ≤ (ψ y).toReal := by
    rw [← EReal.coe_le_coe_iff, EReal.coe_toReal hψ hbot]
    exact h
  simp only [smoothedWeight, hmax]
  rw [SmoothMax.posPart_eq_self (by linarith)]
  ring

omit [TopologicalSpace Y] in
theorem smoothedWeight_le {y : Y} (h : ψ y ≤ ((-R : ℝ) : EReal)) :
    smoothedWeight ψ R y ≤ -R := by
  have hle : max (ψ y) ((-R - 3 : ℝ) : EReal) ≤ ((-R : ℝ) : EReal) :=
    max_le h (EReal.coe_le_coe_iff.mpr (by linarith))
  have hbot : max (ψ y) ((-R - 3 : ℝ) : EReal) ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_max_right _ _)
  have h1 : (max (ψ y) ((-R - 3 : ℝ) : EReal)).toReal ≤ -R := by
    have := EReal.toReal_le_toReal hle hbot (EReal.coe_ne_top _)
    rwa [EReal.toReal_coe] at this
  have := smoothPosPart_le_one (t := (max (ψ y) ((-R - 3 : ℝ) : EReal)).toReal + R + 1) (by linarith)
  simp only [smoothedWeight]
  linarith

omit [TopologicalSpace Y] in
theorem le_smoothedWeight {y : Y} (hψ : ψ y ≠ ⊤) : ψ y ≤ (smoothedWeight ψ R y : EReal) := by
  by_cases hb : ψ y = ⊥
  · rw [hb]
    exact bot_le
  have hmax : (ψ y).toReal ≤ (max (ψ y) ((-R - 3 : ℝ) : EReal)).toReal :=
    EReal.toReal_le_toReal (le_max_left _ _) hb (max_ne_top hψ (EReal.coe_ne_top _) |> fun h => h)
  rw [← EReal.coe_toReal hψ hb, EReal.coe_le_coe_iff]
  have := le_smoothPosPart ((max (ψ y) ((-R - 3 : ℝ) : EReal)).toReal + R + 1)
  simp only [smoothedWeight]
  linarith

omit [TopologicalSpace Y] in
theorem smoothedWeight_eq_const {y : Y} (h : ψ y < ((-R - 2 : ℝ) : EReal)) :
    smoothedWeight ψ R y = -R - 1 := by
  have hle : max (ψ y) ((-R - 3 : ℝ) : EReal) ≤ ((-R - 2 : ℝ) : EReal) :=
    max_le h.le (EReal.coe_le_coe_iff.mpr (by linarith))
  have hbot : max (ψ y) ((-R - 3 : ℝ) : EReal) ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_max_right _ _)
  have h1 : (max (ψ y) ((-R - 3 : ℝ) : EReal)).toReal ≤ -R - 2 := by
    have := EReal.toReal_le_toReal hle hbot (EReal.coe_ne_top _)
    rwa [EReal.toReal_coe] at this
  simp only [smoothedWeight]
  rw [SmoothMax.posPart_eq_zero (by linarith)]
  ring

omit [TopologicalSpace Y] in
theorem smoothedWeight_eq_formula {y : Y} (h : ((-R - 3 : ℝ) : EReal) < ψ y) :
    smoothedWeight ψ R y = -R - 1 + SmoothMax.posPart ((ψ y).toReal + R + 1) := by
  simp only [smoothedWeight, max_eq_left h.le]

variable (hψc : Continuous ψ)
  (hψs : GlobalTubeFunction.ChartSmoothOn N (fun y => (ψ y).toReal) {y | ψ y ≠ ⊥})
include hψc

omit [IsComplexManifold N Y] in
theorem isOpen_chart_lt (e : ComplexChart N Y) (c : ℝ) :
    IsOpen (e.val.target ∩ (fun z => ψ (e.val.symm z)) ⁻¹' Iio (c : EReal)) :=
  (hψc.comp_continuousOn e.val.continuousOn_symm).isOpen_inter_preimage e.val.open_target
    isOpen_Iio

omit [IsComplexManifold N Y] in
theorem isOpen_chart_gt (e : ComplexChart N Y) (c : ℝ) :
    IsOpen (e.val.target ∩ (fun z => ψ (e.val.symm z)) ⁻¹' Ioi (c : EReal)) :=
  (hψc.comp_continuousOn e.val.continuousOn_symm).isOpen_inter_preimage e.val.open_target
    isOpen_Ioi

omit [IsComplexManifold N Y] hψc in
include hψs in
/-- In a chart, on the open set where `ψ > -R - 3`, the smoothed weight is the smooth function
`-R - 1 + SmoothMax.posPart(ψ + R + 1)`. -/
theorem contDiffOn_chart_gt (e : ComplexChart N Y) (R : ℝ) :
    ContDiffOn ℝ ∞ (fun z => -R - 1 + SmoothMax.posPart ((ψ (e.val.symm z)).toReal + R + 1))
      (e.val.target ∩ (fun z => ψ (e.val.symm z)) ⁻¹' Ioi ((-R - 3 : ℝ) : EReal)) := by
  have hsub : e.val.target ∩ (fun z => ψ (e.val.symm z)) ⁻¹' Ioi ((-R - 3 : ℝ) : EReal) ⊆
      e.val.target ∩ e.val.symm ⁻¹' {y | ψ y ≠ ⊥} := fun z hz =>
    ⟨hz.1, ne_bot_of_gt (show ((-R - 3 : ℝ) : EReal) < ψ (e.val.symm z) from hz.2)⟩
  have hφ := ((hψs e).mono hsub).add (contDiffOn_const (c := R + 1))
  have h2 := (contDiffOn_const (c := -R - 1)).add (SmoothMax.contDiff_posPart.comp_contDiffOn hφ)
  refine h2.congr fun z _ => ?_
  simp only [Function.comp_apply, add_assoc]

include hψs in
/-- The smoothed weight is chart-smooth. -/
theorem chartSmooth_smoothedWeight (R : ℝ) : ChartSmooth (n := N) (smoothedWeight ψ R) := by
  intro e
  refine contDiffOn_of_locally_contDiffOn fun z hz => ?_
  by_cases hlt : ψ (e.val.symm z) < ((-R - 2 : ℝ) : EReal)
  · refine ⟨_, isOpen_chart_lt hψc e (-R - 2), ⟨hz, hlt⟩, ?_⟩
    exact (contDiffOn_const (c := -R - 1)).congr fun z' hz' =>
      smoothedWeight_eq_const hz'.2.2
  · have hgt : ((-R - 3 : ℝ) : EReal) < ψ (e.val.symm z) :=
      lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr (by linarith)) (not_lt.mp hlt)
    refine ⟨_, isOpen_chart_gt hψc e (-R - 3), ⟨hz, hgt⟩, ?_⟩
    exact ((contDiffOn_chart_gt hψs e R).mono inter_subset_right).congr fun z' hz' =>
      smoothedWeight_eq_formula hz'.2.2

include hψs in
/-- **`ddᶜ` of the smoothed weight is bounded below**: `ddᶜ smoothedWeight ≥ -C A` on complex lines,
if `ψ` is `C A`-psh. -/
theorem neg_le_ddcClosedForm_smoothedWeight (A : KahlerBackground N Y) {C : ℝ} (hC : 0 ≤ C)
    (hψ : IsThetaPshPotential (C • A.form).val ψ) (R : ℝ) (e : ComplexChart N Y)
    {z : ComplexModel N} (hz : z ∈ e.val.target) (v : ComplexModel N) :
    -(C * A.form.val.coeff e z ![v, Complex.I • v]) ≤
      (ddcClosedForm (smoothedWeight ψ R) (chartSmooth_smoothedWeight hψc hψs R)).val.coeff e z
        ![v, Complex.I • v] := by
  have hA : 0 ≤ A.form.val.coeff e z ![v, Complex.I • v] := A.isSemipositive e z hz v
  have hCA : 0 ≤ C * A.form.val.coeff e z ![v, Complex.I • v] := mul_nonneg hC hA
  rw [ddcClosedForm_coeff]
  by_cases hlt : ψ (e.val.symm z) < ((-R - 2 : ℝ) : EReal)
  · have heq : (fun z' => smoothedWeight ψ R (e.val.symm z')) =ᶠ[𝓝 z] fun _ => -R - 1 := by
      filter_upwards [(isOpen_chart_lt hψc e (-R - 2)).mem_nhds ⟨hz, hlt⟩] with z' hz'
      exact smoothedWeight_eq_const hz'.2
    rw [smoothDDC_congr heq, smoothDDC_complexDiagonal_eq_leviForm contDiffAt_const, leviForm_const,
      zero_div]
    linarith
  · have hgt : ((-R - 3 : ℝ) : EReal) < ψ (e.val.symm z) :=
      lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr (by linarith)) (not_lt.mp hlt)
    set O := e.val.target ∩ (fun z => ψ (e.val.symm z)) ⁻¹' Ioi ((-R - 3 : ℝ) : EReal) with hO
    have hOo : IsOpen O := isOpen_chart_gt hψc e (-R - 3)
    have hzO : z ∈ O := ⟨hz, hgt⟩
    set φ : ComplexModel N → ℝ := fun z' => (ψ (e.val.symm z')).toReal with hφdef
    have hφs : ContDiffOn ℝ ∞ φ O := (hψs e).mono fun z' hz' =>
      ⟨hz'.1, ne_bot_of_gt (show ((-R - 3 : ℝ) : EReal) < ψ (e.val.symm z') from hz'.2)⟩
    have hφ2 : ContDiffAt ℝ 2 φ z :=
      ((hφs z hzO).contDiffAt (hOo.mem_nhds hzO)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have heq : (fun z' => smoothedWeight ψ R (e.val.symm z')) =ᶠ[𝓝 z]
        fun z' => -R - 1 + SmoothMax.posPart (φ z' + R + 1) := by
      filter_upwards [hOo.mem_nhds hzO] with z' hz'
      exact smoothedWeight_eq_formula hz'.2
    have hin2 : ContDiffAt ℝ 2 (fun z' => φ z' + R + 1) z :=
      (hφ2.add contDiffAt_const).add contDiffAt_const
    have hpos2 : ContDiffAt ℝ 2 SmoothMax.posPart (φ z + R + 1) :=
      (SmoothMax.contDiff_posPart.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
    have hcomp2 : ContDiffAt ℝ 2 (fun z' => SmoothMax.posPart (φ z' + R + 1)) z :=
      hpos2.comp (f := fun z' => φ z' + R + 1) z hin2
    have hlevi : leviForm (fun z' => -R - 1 + SmoothMax.posPart (φ z' + R + 1)) z v =
        leviForm (fun z' => SmoothMax.posPart (φ z' + R + 1)) z v := by
      have h := leviForm_add (contDiffAt_const (c := -R - 1)) hcomp2 v
      rw [leviForm_const, zero_add] at h
      exact h
    have hlevi_in : leviForm (fun z' => φ z' + R + 1) z v = leviForm φ z v := by
      have h := leviForm_add hφ2 (contDiffAt_const (c := R + 1)) v
      rw [leviForm_const, add_zero] at h
      have hfun : (fun z' => φ z' + R + 1) = φ + fun _ => R + 1 := by
        funext z'
        simp only [Pi.add_apply]
        ring
      rw [hfun]
      exact h
    have hchain := StokesCutoff.mul_leviForm_le_leviForm_comp hpos2 hin2
      (deriv_deriv_smoothPosPart_nonneg _) v
    rw [hlevi_in, SmoothMax.deriv_posPart] at hchain
    -- the lower bound of the Levi form of `ψ`
    have hφlow : -(Real.pi * (C * A.form.val.coeff e z ![v, Complex.I • v])) ≤ leviForm φ z v := by
      obtain ⟨W, ρ, hzW, hρ, hpsh⟩ := hψ.1 e z hz
      let U : TopologicalSpace.Opens (ComplexModel N) := ⟨W ∩ O, hρ.1.inter hOo⟩
      have hzU : z ∈ U := ⟨hzW, hzO⟩
      have hsU : ContDiffOn ℝ ∞ (fun z' => φ z' + ρ z') U :=
        (hφs.mono inter_subset_right).add (hρ.2.2.1.mono inter_subset_left)
      have hpU : PlurisubharmonicOn (fun z' => ((φ z' + ρ z' : ℝ) : EReal)) U := by
        refine plurisubharmonicOn_congr U.isOpen (hpsh.mono inter_subset_left) fun z' hz' => ?_
        have hz'O : z' ∈ O := hz'.2
        have hne : ψ (e.val.symm z') ≠ ⊥ :=
          ne_bot_of_gt (show ((-R - 3 : ℝ) : EReal) < ψ (e.val.symm z') from hz'O.2)
        have hnt : ψ (e.val.symm z') ≠ ⊤ := hψ.1.quasiPlurisubharmonic.ne_top _
        simp only [chartFunction, hφdef, EReal.coe_add, EReal.coe_toReal hnt hne]
      have h0 := leviForm_nonneg_of_contDiffOn_plurisubharmonicOn hsU hpU hzU v
      have hρ2 : ContDiffAt ℝ 2 ρ z :=
        ((hρ.2.2.1 z hzW).contDiffAt (hρ.1.mem_nhds hzW)).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
      have hsum : leviForm (fun z' => φ z' + ρ z') z v = leviForm φ z v + leviForm ρ z v :=
        leviForm_add hφ2 hρ2 v
      have hρval : leviForm ρ z v = Real.pi * (C * A.form.val.coeff e z ![v, Complex.I • v]) := by
        have h1 := smoothDDC_complexDiagonal_eq_leviForm hρ2 v
        rw [hρ.2.2.2 hzW] at h1
        simp only [ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.smul_apply,
          smul_eq_mul] at h1
        rw [h1]
        field_simp
      linarith
    rw [smoothDDC_congr heq, smoothDDC_complexDiagonal_eq_leviForm
      (contDiffAt_const.add hcomp2), hlevi]
    have ht0 := SmoothMax.trans_nonneg (φ z + R + 1)
    have ht1 := SmoothMax.trans_le_one (φ z + R + 1)
    have hpi := Real.pi_pos
    rw [le_div_iff₀ hpi]
    have hk : 0 ≤ Real.pi * (C * A.form.val.coeff e z ![v, Complex.I • v]) := by positivity
    nlinarith

end Weight

/-! ### Berman's estimate with a singular weight -/

/-- The `ddᶜ` of a difference, on complex lines. -/
theorem ddcClosedForm_sub_coeff {f g : Y → ℝ} (hf : ChartSmooth (n := N) f)
    (hg : ChartSmooth (n := N) g) (hfg : ChartSmooth (n := N) (fun y => f y - g y))
    (e : ComplexChart N Y) {z : ComplexModel N} (hz : z ∈ e.val.target) (v : ComplexModel N) :
    (ddcClosedForm (fun y => f y - g y) hfg).val.coeff e z ![v, Complex.I • v] =
      (ddcClosedForm f hf).val.coeff e z ![v, Complex.I • v] -
        (ddcClosedForm g hg).val.coeff e z ![v, Complex.I • v] := by
  simp only [ddcClosedForm_coeff]
  rw [smoothDDC_sub e.val.open_target (hf e) (hg e) hz]
  rfl

/-- **`tok-wn-reg:berman-singular`**: `BermanSingularEnvelopeStatement`. -/
theorem bermanSingularEnvelopeStatement : BermanSingularEnvelopeStatement.{u} := by
  intro N Y _ _ _ _ _ A
  obtain ⟨a, Λ, ha, hΛ, hB⟩ := bermanSmoothEnvelopeStatement N Y A
  refine ⟨a, Λ, ha, hΛ, fun f hf S hS hfS ψ C hC hψ hψc hψs m hm => ?_⟩
  have hψtop : ∀ y, ψ y ≠ ⊤ := fun y => hψ.1.quasiPlurisubharmonic.ne_top y
  have hfc : Continuous f := ProductTestForms.ChartSmooth.continuous hf
  obtain ⟨xmin, -, hxmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty hfc.continuousOn
  obtain ⟨xmax, -, hxmax⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hfc.continuousOn
  have hfmin : ∀ y, f xmin ≤ f y := fun y => hxmin (mem_univ y)
  have hfmax : ∀ y, f y ≤ f xmax := fun y => hxmax (mem_univ y)
  -- the maximum of `ψ` and the open set where `ψ` is close to it
  obtain ⟨y₀, -, hy₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hψc.continuousOn
  obtain ⟨y₁, -, hy₁⟩ := hψ.2 y₀ univ isOpen_univ (mem_univ y₀)
  have hy₀bot : ψ y₀ ≠ ⊥ := ne_bot_of_le_ne_bot hy₁ (hy₀ (mem_univ y₁))
  set sψ : ℝ := (ψ y₀).toReal with hsψ
  have hψy₀ : ψ y₀ = (sψ : EReal) := (EReal.coe_toReal (hψtop y₀) hy₀bot).symm
  set W : Set Y := {y | ((sψ - 1 : ℝ) : EReal) < ψ y} with hW
  have hWo : IsOpen W := isOpen_lt continuous_const hψc
  have hy₀W : y₀ ∈ W := by
    show ((sψ - 1 : ℝ) : EReal) < ψ y₀
    rw [hψy₀]
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  set c₀ : ℝ := f xmax - sψ + 1 with hc₀
  obtain ⟨Cb, hCb⟩ := exists_le_of_quasiEverywhere_le_on_open A.form hWo ⟨y₀, hy₀W⟩ c₀
  -- every competitor of `f - ψ` is `≤ Cb`
  have hcomp : ∀ v ∈ rooftopCompetitors A.form.val (fun y => (f y : EReal) - ψ y), ∀ x,
      v x ≤ (Cb : EReal) := by
    intro v hv x
    refine hCb v hv.1 (hv.2.mono fun y hy hyW => ?_) x
    have hyW' : ((sψ - 1 : ℝ) : EReal) < ψ y := hyW
    have hne : ψ y ≠ ⊥ := ne_bot_of_gt hyW'
    have hψy : ψ y = ((ψ y).toReal : EReal) := (EReal.coe_toReal (hψtop y) hne).symm
    have hlt : sψ - 1 < (ψ y).toReal := by
      rw [hψy] at hyW'
      exact EReal.coe_lt_coe_iff.mp hyW'
    calc v y ≤ (f y : EReal) - ψ y := hy
      _ = ((f y - (ψ y).toReal : ℝ) : EReal) := by rw [hψy, ← EReal.coe_sub, EReal.toReal_coe]
      _ ≤ (c₀ : EReal) := EReal.coe_le_coe_iff.mpr (by linarith [hfmax y])
  -- the smoothed obstacles
  set F : ℝ → Y → ℝ := fun R y => f y - smoothedWeight ψ R y with hF
  have hFs : ∀ R, ChartSmooth (n := N) (F R) := fun R e =>
    (hf e).sub (chartSmooth_smoothedWeight hψc hψs R e)
  have hFeq : ∀ R y, ((-R : ℝ) : EReal) ≤ ψ y → (F R y : EReal) = (f y : EReal) - ψ y := by
    intro R y hy
    have hne : ψ y ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hy
    simp only [hF, smoothedWeight_eq_toReal (hψtop y) hy]
    rw [EReal.coe_sub, EReal.coe_toReal (hψtop y) hne]
  have hFlow : ∀ R y, ψ y ≤ ((-R : ℝ) : EReal) → f xmin + R ≤ F R y := by
    intro R y hy
    have := smoothedWeight_le (R := R) hy
    simp only [hF]
    linarith [hfmin y]
  -- the envelopes coincide for `R` large
  have henv : ∀ R, Cb - f xmin ≤ R →
      rooftopEnvelope A.form.val (fun y => ((F R y : ℝ) : EReal)) =
        rooftopEnvelope A.form.val (fun y => (f y : EReal) - ψ y) := by
    intro R hR
    have hsets : rooftopCompetitors A.form.val (fun y => ((F R y : ℝ) : EReal)) =
        rooftopCompetitors A.form.val (fun y => (f y : EReal) - ψ y) := by
      ext v
      constructor
      · rintro ⟨hv1, hv2⟩
        refine ⟨hv1, hv2.mono fun y hy => hy.trans ?_⟩
        simp only [hF, EReal.coe_sub]
        exact EReal.sub_le_sub le_rfl (le_smoothedWeight (hψtop y))
      · intro hv
        refine ⟨hv.1, hv.2.mono fun y hy => ?_⟩
        show v y ≤ ((F R y : ℝ) : EReal)
        by_cases hyR : ((-R : ℝ) : EReal) ≤ ψ y
        · rw [hFeq R y hyR]
          exact hy
        · have hle := hFlow R y (not_le.mp hyR).le
          exact (hcomp v hv y).trans (EReal.coe_le_coe_iff.mpr (by linarith))
    simp only [rooftopEnvelope, rooftopSupremum, hsets]
  -- the hypotheses of Berman's smooth estimate
  have hFddc : ∀ R (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      ∀ v : ComplexModel N, (ddcClosedForm (F R) (hFs R)).val.coeff e z ![v, Complex.I • v] ≤
        (S + C) * A.form.val.coeff e z ![v, Complex.I • v] := by
    intro R e z hz v
    have h1 : (ddcClosedForm (F R) (hFs R)).val.coeff e z ![v, Complex.I • v] =
        (ddcClosedForm f hf).val.coeff e z ![v, Complex.I • v] -
          (ddcClosedForm (smoothedWeight ψ R) (chartSmooth_smoothedWeight hψc hψs R)).val.coeff
            e z ![v, Complex.I • v] :=
      ddcClosedForm_sub_coeff hf (chartSmooth_smoothedWeight hψc hψs R) (hFs R) e hz v
    have h2 := neg_le_ddcClosedForm_smoothedWeight hψc hψs A hC hψ R e hz v
    have h3 := hfS e z hz v
    rw [h1]
    linarith
  have hFm : ∀ R, m - f xmin ≤ R → ∀ y, m ≤ F R y := by
    intro R hR y
    by_cases hyR : ((-R : ℝ) : EReal) ≤ ψ y
    · have h := hm y
      rw [← hFeq R y hyR] at h
      exact EReal.coe_le_coe_iff.mp h
    · linarith [hFlow R y (not_le.mp hyR).le]
  have hSC : 0 ≤ S + C := add_nonneg hS hC
  set R₀ : ℝ := max (Cb - f xmin) (m - f xmin) with hR₀
  refine ⟨fun x => ?_, fun K hK hKψ => ?_⟩
  · have h := (hB (F R₀) (hFs R₀) (S + C) hSC (hFddc R₀) m (hFm R₀ (le_max_right _ _))).1 x
    rw [henv R₀ (le_max_left _ _)] at h
    rw [h, EReal.toReal_coe]
  · -- a level below `ψ` on `K`
    obtain ⟨RK, hRK⟩ : ∃ RK : ℝ, ∀ y ∈ K, ((-RK : ℝ) : EReal) ≤ ψ y := by
      rcases K.eq_empty_or_nonempty with hKe | hKne
      · exact ⟨0, fun y hy => by simp [hKe] at hy⟩
      obtain ⟨ymin, hymin, hmin⟩ := hK.exists_isMinOn hKne hψc.continuousOn
      refine ⟨-(ψ ymin).toReal, fun y hy => ?_⟩
      rw [neg_neg, EReal.coe_toReal (hψtop ymin) (hKψ ymin hymin)]
      exact hmin hy
    set R : ℝ := max R₀ RK with hR
    have hR₁ : Cb - f xmin ≤ R := (le_max_left _ _).trans (le_max_left _ _)
    have hR₂ : m - f xmin ≤ R := (le_max_right _ _).trans (le_max_left _ _)
    have hRK' : ∀ y ∈ K, ((-R : ℝ) : EReal) ≤ ψ y := fun y hy =>
      (EReal.coe_le_coe_iff.mpr (neg_le_neg (le_max_right _ _))).trans (hRK y hy)
    have happrox := (hB (F R) (hFs R) (S + C) hSC (hFddc R) m (hFm R hR₂)).2
    have hu : envelopeReal A.form (F R) =
        fun x => (rooftopEnvelope A.form.val (fun y => (f y : EReal) - ψ y) x).toReal := by
      funext x
      rw [envelopeReal, henv R hR₁]
    rw [hu] at happrox
    refine happrox.on fun x hx => ?_
    have hne : ψ x ≠ ⊥ := hKψ x hx
    have hFx : F R x = f x - (ψ x).toReal := by
      simp only [hF, smoothedWeight_eq_toReal (hψtop x) (hRK' x hx)]
    rw [hFx]
    ring_nf

end SGPT.Okounkov.TranscendentalWNReg
