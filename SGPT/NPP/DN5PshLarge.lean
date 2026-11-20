import SGPT.NPP.DN5Bounds
import SGPT.Foundations.Analysis.FirstPass.ERealChordUSC
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshVolumeIntegrability

/-!
# The `psh` clauses at radii bounded away from zero

Lane DN5, `thm:DNT23_C11bar` (`chapter_npp.tex`), via FPT `lem:chern-joint-smoothing`
(`chapters/inputs/q10-big-envelope-regularity.tex`).  For radii `t ∈ [r_L, r₀]`
(`0 < r_L ≤ r₀ < r₁`, `r₁` a uniform radius) the four `psh` clauses of
`SGPT.NPP.DN2.IsJointSmoothing` hold for `H_u = Ψ_u + K t²` as soon as `K` and `C` are large
(depending on `u`, `θ`, `r_L`): the smoothing is smooth there, so its value, its log-radius
derivatives and its joint Levi form are bounded (`SGPT.NPP.DN5Bounds`), while `K t²` makes
`s ↦ H_u(x, eˢ)` increasing and strictly convex and dominates `sup u`, and `C t ≥ C r_L`,
`C t² ≥ C r_L²` absorb the bounded joint Levi form (`psh_large`).

Also: calculus of `s ↦ φ(s) + K e^{2s}` (`deriv_add_sq_exp`), the logarithmic slope as an
`s`-derivative (`logSlope_eq_deriv_exp`), and an upper bound for a `θ`-psh potential
(`exists_le_of_isThetaPshPotential`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace SGPT.NPP.DN5

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending IntegrationCurrent
open SGPT.NPP.DN2

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-! ### One-variable calculus -/

/-- Derivatives of `s ↦ φ(s) + K (eˢ)²`. -/
theorem deriv_add_sq_exp {φ : ℝ → ℝ} {S : Set ℝ} (hS : IsOpen S) (hφ : ContDiffOn ℝ ∞ φ S)
    {s : ℝ} (hs : s ∈ S) (K : ℝ) :
    deriv (fun s => φ s + K * Real.exp s ^ 2) s = deriv φ s + 2 * K * Real.exp s ^ 2 ∧
      deriv (deriv (fun s => φ s + K * Real.exp s ^ 2)) s =
        deriv (deriv φ) s + 4 * K * Real.exp s ^ 2 := by
  have e1 : (fun s => K * Real.exp s ^ 2) = fun s => K * (Real.exp s * Real.exp s) := by
    funext s; ring
  have hq : ∀ s', HasDerivAt (fun s => K * Real.exp s ^ 2) (2 * K * Real.exp s' ^ 2) s' := by
    intro s'
    have h := ((Real.hasDerivAt_exp s').mul (Real.hasDerivAt_exp s')).const_mul K
    rw [e1, show 2 * K * Real.exp s' ^ 2 =
      K * (Real.exp s' * Real.exp s' + Real.exp s' * Real.exp s') by ring]
    exact h
  have hφd : ∀ s' ∈ S, HasDerivAt φ (deriv φ s') s' := fun s' hs' =>
    ((hφ.contDiffAt (hS.mem_nhds hs')).differentiableAt (by simp)).hasDerivAt
  have hd1 : ∀ s' ∈ S, deriv (fun s => φ s + K * Real.exp s ^ 2) s' =
      deriv φ s' + 2 * K * Real.exp s' ^ 2 := fun s' hs' => ((hφd s' hs').add (hq s')).deriv
  refine ⟨hd1 s hs, ?_⟩
  have hev : deriv (fun s => φ s + K * Real.exp s ^ 2) =ᶠ[𝓝 s]
      fun s' => deriv φ s' + 2 * K * Real.exp s' ^ 2 := by
    filter_upwards [hS.mem_nhds hs] with s' hs'
    exact hd1 s' hs'
  rw [hev.deriv_eq]
  have hD : ContDiffOn ℝ ∞ (deriv φ) S := hφ.deriv_of_isOpen hS (by simp)
  have h1 : HasDerivAt (deriv φ) (deriv (deriv φ) s) s :=
    ((hD.contDiffAt (hS.mem_nhds hs)).differentiableAt (by simp)).hasDerivAt
  have h2 : HasDerivAt (fun s' => 2 * K * Real.exp s' ^ 2) (4 * K * Real.exp s ^ 2) s := by
    have h := ((Real.hasDerivAt_exp s).mul (Real.hasDerivAt_exp s)).const_mul (2 * K)
    have e2 : (fun s' => 2 * K * Real.exp s' ^ 2) = fun s' => 2 * K * (Real.exp s' * Real.exp s') := by
      funext s'; ring
    rw [e2, show 4 * K * Real.exp s ^ 2 =
      2 * K * (Real.exp s * Real.exp s + Real.exp s * Real.exp s) by ring]
    exact h
  exact (h1.add h2).deriv

/-- The logarithmic slope `t ∂_t H` is the derivative of `s ↦ H(eˢ)` at `s = log t`. -/
theorem logSlope_eq_deriv_exp {H : Y → ℝ → ℝ} {x : Y} {t : ℝ} (ht : 0 < t)
    (hd : DifferentiableAt ℝ (H x) t) :
    logSlope H x t = deriv (fun s => H x (Real.exp s)) (Real.log t) := by
  have hexp : Real.exp (Real.log t) = t := Real.exp_log ht
  have h1 : HasDerivAt (H x) (deriv (H x) t) (Real.exp (Real.log t)) := by
    rw [hexp]; exact hd.hasDerivAt
  have h2 := h1.comp (Real.log t) (Real.hasDerivAt_exp (Real.log t))
  rw [show (fun s => H x (Real.exp s)) = H x ∘ Real.exp from rfl, h2.deriv, hexp, logSlope,
    mul_comm]

/-- A `θ`-psh potential on a compact manifold is bounded above by a real number. -/
theorem exists_le_of_isThetaPshPotential [CompactSpace Y] {θ : SmoothRealForm N Y 2}
    {u : Y → EReal} (hu : IsThetaPshPotential θ u) : ∃ M : ℝ, ∀ x, u x ≤ (M : EReal) := by
  rcases isEmpty_or_nonempty Y with hY | hY
  · exact ⟨0, fun x => isEmptyElim x⟩
  have husc := hu.1.quasiPlurisubharmonic.upperSemicontinuous
  obtain ⟨a, -, ha⟩ := (husc.upperSemicontinuousOn univ).exists_isMaxOn univ_nonempty
    isCompact_univ
  refine ⟨(u a).toReal, fun x => (ha (mem_univ x)).trans ?_⟩
  exact EReal.le_coe_toReal (hu.1.quasiPlurisubharmonic.ne_top a)

/-! ### The large-radius clauses -/

variable [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

variable {wY : KahlerBackground N Y} {A : FibreAtlas N Y} {r₁ : ℝ}

theorem contDiffOn_smoothing_logRadius (hr : IsUniformRadius wY A r₁) {g : Y → ℝ}
    (hg : Integrable g (kahlerVolume wY)) (x : Y) :
    ContDiffOn ℝ ∞ (fun s => smoothing wY A g x (Real.exp s)) (Iio (Real.log r₁)) := by
  set e := complexChartAt (n := N) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have h := contDiffOn_logRadius hr hg e
  have h2 : ContDiffOn ℝ ∞ (fun s : ℝ => (e.val x, s)) (Iio (Real.log r₁)) :=
    contDiffOn_const.prodMk contDiffOn_id
  refine (h.comp h2 fun s hs => ⟨e.val.map_source hx, hs⟩).congr fun s _ => ?_
  simp only [Function.comp_apply, e.val.left_inv hx]

theorem contDiffOn_smoothing_radius (hr : IsUniformRadius wY A r₁) {g : Y → ℝ}
    (hg : Integrable g (kahlerVolume wY)) (x : Y) :
    ContDiffOn ℝ ∞ (fun t => smoothing wY A g x t) (Ioo 0 r₁) := by
  set e := complexChartAt (n := N) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have h := smoothing_contDiffOn hr hg e
  have h2 : ContDiffOn ℝ ∞ (fun t : ℝ => (e.val x, t)) (Ioo 0 r₁) :=
    contDiffOn_const.prodMk contDiffOn_id
  refine (h.comp h2 fun t ht => ⟨e.val.map_source hx, ht⟩).congr fun t _ => ?_
  simp only [Function.comp_apply, e.val.left_inv hx]

/-- The corrected smoothing in log radius. -/
theorem correctedSmoothing_exp (u : Y → EReal) (K : ℝ) (x : Y) :
    (fun s => correctedSmoothing (smoothing wY A) u K x (Real.exp s)) =
      fun s => smoothing wY A (fun y => (u y).toReal) x (Real.exp s) + K * Real.exp s ^ 2 := rfl

theorem differentiableAt_correctedSmoothing (hr : IsUniformRadius wY A r₁) {u : Y → EReal}
    (hg : Integrable (fun y => (u y).toReal) (kahlerVolume wY)) (K : ℝ) (x : Y) {t : ℝ}
    (ht : 0 < t) (ht₁ : t < r₁) :
    DifferentiableAt ℝ (correctedSmoothing (smoothing wY A) u K x) t := by
  have h := (contDiffOn_smoothing_radius hr hg x).contDiffAt (isOpen_Ioo.mem_nhds ⟨ht, ht₁⟩)
  exact (h.differentiableAt (by simp)).add ((differentiableAt_id.pow 2).const_mul K)

/-- **The `psh` clauses at radii in `[r_L, r₀]`.** -/
theorem psh_large (hr : IsUniformRadius wY A r₁) (θ : ClosedRealOneOneForm N Y) {u : Y → EReal}
    (hu : IsThetaPshPotential θ.val u) {rL r₀ : ℝ} (hrL : 0 < rL) (hLr : rL ≤ r₀)
    (hr₀ : r₀ < r₁) :
    ∃ K₀ C₀ : ℝ, 0 ≤ K₀ ∧ 0 ≤ C₀ ∧ ∀ K C Ac : ℝ, K₀ ≤ K → C₀ ≤ C → 0 ≤ Ac →
      let H := correctedSmoothing (smoothing wY A) u K
      (∀ (x : Y) (t : ℝ), rL ≤ t → t ≤ r₀ → u x ≤ ((H x t : ℝ) : EReal)) ∧
      (∀ (x : Y) (s : ℝ), rL ≤ Real.exp s → Real.exp s ≤ r₀ →
        0 ≤ deriv (fun s => H x (Real.exp s)) s ∧
        0 < deriv (deriv (fun s => H x (Real.exp s))) s) ∧
      (∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target → ∀ w : ℂ,
        rL ≤ ‖w‖ → ‖w‖ ≤ r₀ → 0 ≤ logSlope H (e.val.symm z) ‖w‖ →
        JointLeviLowerBound θ wY H e z w (Ac * logSlope H (e.val.symm z) ‖w‖ + C * ‖w‖) C C) ∧
      (∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target → ∀ (L r : ℝ), 0 ≤ L →
        rL ≤ r → r ≤ r₀ → 0 ≤ logSlope H (e.val.symm z) r → ∀ w : ℂ, ‖w‖ = r →
        JointLeviLowerBound θ wY H e z w
          (Ac * logSlope H (e.val.symm z) r + C * (1 + L) * r ^ 2)
          (C * (1 + L) * r) (C * (1 + L) * r)) := by
  set g : Y → ℝ := fun y => (u y).toReal
  have hg : Integrable g (kahlerVolume wY) :=
    GlobalQuasiPshVolumeIntegrability.integrable_toReal_of_genuine_thetaPsh (kahlerVolume wY)
      (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume wY) θ.val u hu
  obtain ⟨M, hM⟩ := exists_le_of_isThetaPshPotential hu
  obtain ⟨B, hB⟩ := exists_bound_logRadius hr hg hrL hLr hr₀
  obtain ⟨BL, hBL⟩ := exists_bound_leviForm_jointFun hr hg hrL hr₀
  obtain ⟨Bθ, hBθ⟩ := exists_bound_theta wY θ.val
  set B' := |B| + |M| + 1
  set K₀ := B' / rL ^ 2
  set D := |BL| + Real.pi * |Bθ| + 1
  set C₀ := D * (rL⁻¹ + (rL ^ 2)⁻¹ + 1)
  have hrL2 : 0 < rL ^ 2 := by positivity
  have hB' : 0 < B' := by positivity
  have hK₀ : 0 ≤ K₀ := by positivity
  have hD : 0 < D := by positivity
  have hC₀ : 0 ≤ C₀ := by positivity
  refine ⟨K₀, C₀, hK₀, hC₀, fun K C Aa hK hC hA => ?_⟩
  intro H
  have hKrL : B' ≤ K * rL ^ 2 := by
    have : K₀ * rL ^ 2 = B' := by simp only [K₀]; field_simp
    nlinarith
  have hCrL : D ≤ C * rL := by
    have h1 : D * rL⁻¹ ≤ C₀ := by
      simp only [C₀]; nlinarith [inv_pos.mpr hrL, inv_pos.mpr hrL2]
    have h2 : D * rL⁻¹ * rL = D := by field_simp
    nlinarith
  have hCrL2 : D ≤ C * rL ^ 2 := by
    have h1 : D * (rL ^ 2)⁻¹ ≤ C₀ := by
      simp only [C₀]; nlinarith [inv_pos.mpr hrL, inv_pos.mpr hrL2]
    have h2 : D * (rL ^ 2)⁻¹ * rL ^ 2 = D := by field_simp
    nlinarith
  have hC1 : D ≤ C := by
    have : D ≤ C₀ := by simp only [C₀]; nlinarith [inv_pos.mpr hrL, inv_pos.mpr hrL2]
    linarith
  -- the joint Levi form, any potential
  have hlevi : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target → ∀ w : ℂ,
      rL ≤ ‖w‖ → ‖w‖ ≤ r₀ → ∀ (W : Set (ComplexModel N)) (ρ : ComplexModel N → ℝ), z ∈ W →
        IsSmoothLocalPotential θ.val e W ρ → ∀ (v : ComplexModel N) (η : ℂ),
          -(D * chartNormSq wY e z v) - D * ‖η‖ ^ 2 ≤ leviForm (chartJoint H e ρ) (z, w) (v, η) := by
    intro e z hz w hw1 hw2 W ρ hzW hρ v η
    have hw0 : 0 < ‖w‖ := hrL.trans_le hw1
    have hJ : ContDiffAt ℝ 2 (jointFun (smoothing wY A g) e) (z, w) :=
      (contDiffAt_jointFun hr hg hz hw0 (hw2.trans_lt hr₀)).of_le (by norm_cast)
    have hsq : ContDiffAt ℝ 2 (fun p : ComplexModel N × ℂ => K * ‖p.2‖ ^ 2) (z, w) :=
      contDiffAt_const.mul ((contDiff_norm_sq ℝ).contDiffAt.comp (z, w) contDiffAt_snd)
    have hρz : ContDiffAt ℝ 2 ρ z := (hρ.2.2.1.contDiffAt (hρ.1.mem_nhds hzW)).of_le (by norm_cast)
    have hρ1 : ContDiffAt ℝ 2 (fun p : ComplexModel N × ℂ => ρ p.1) (z, w) :=
      hρz.comp (z, w) contDiffAt_fst
    have hsplit : chartJoint H e ρ = (fun p : ComplexModel N × ℂ =>
        jointFun (smoothing wY A g) e p + K * ‖p.2‖ ^ 2) + fun p => ρ p.1 := by
      funext p
      simp only [chartJoint, H, correctedSmoothing, jointFun, Pi.add_apply, g]
    have hsum := leviForm_add (hJ.add hsq) hρ1 (v, η)
    have hsum2 := leviForm_add hJ hsq (v, η)
    rw [hsplit, hsum]
    rw [show leviForm (fun p : ComplexModel N × ℂ =>
        jointFun (smoothing wY A g) e p + K * ‖p.2‖ ^ 2) (z, w) (v, η) =
        leviForm (jointFun (smoothing wY A g) e) (z, w) (v, η) +
          leviForm (fun p : ComplexModel N × ℂ => K * ‖p.2‖ ^ 2) (z, w) (v, η) from hsum2,
      leviForm_comp_fst hρz]
    have hKlevi : leviForm (fun p : ComplexModel N × ℂ => K * ‖p.2‖ ^ 2) (z, w) (v, η) =
        K * ‖η‖ ^ 2 := by
      have h := leviForm_smul (u := fun p : ComplexModel N × ℂ => ‖p.2‖ ^ 2)
        ((contDiff_norm_sq ℝ).contDiffAt.comp (z, w) contDiffAt_snd) K (v, η)
      rw [leviForm_normSq_snd] at h
      exact h
    rw [hKlevi, leviForm_potential hρ hzW]
    have h1 := hBL e z hz w hw1 hw2 v η
    have h2 := hBθ e z hz v
    have hN := chartNormSq_nonneg wY e hz v
    have hKpos : 0 ≤ K := hK₀.trans hK
    have hL1 : -(|BL| * (chartNormSq wY e z v + ‖η‖ ^ 2)) ≤
        leviForm (jointFun (smoothing wY A g) e) (z, w) (v, η) := by
      have := neg_abs_le (leviForm (jointFun (smoothing wY A g) e) (z, w) (v, η))
      have h3 : BL * (chartNormSq wY e z v + ‖η‖ ^ 2) ≤ |BL| * (chartNormSq wY e z v + ‖η‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      linarith
    have hθ1 : -(|Bθ| * chartNormSq wY e z v) ≤ θ.val.coeff e z ![v, Complex.I • v] := by
      have := neg_abs_le (θ.val.coeff e z ![v, Complex.I • v])
      have h3 : Bθ * chartNormSq wY e z v ≤ |Bθ| * chartNormSq wY e z v :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hN
      linarith
    have hη : 0 ≤ ‖η‖ ^ 2 := sq_nonneg _
    have hπθ : -(Real.pi * (|Bθ| * chartNormSq wY e z v)) ≤
        Real.pi * θ.val.coeff e z ![v, Complex.I • v] := by
      have := mul_le_mul_of_nonneg_left hθ1 Real.pi_pos.le
      linarith
    have hKη : 0 ≤ K * ‖η‖ ^ 2 := mul_nonneg hKpos hη
    have hDdef : D = |BL| + Real.pi * |Bθ| + 1 := rfl
    have hπB : 0 ≤ Real.pi * |Bθ| := mul_nonneg Real.pi_pos.le (abs_nonneg Bθ)
    have hD1 : |BL| + Real.pi * |Bθ| ≤ D := by linarith
    have hD2 : |BL| ≤ D := by linarith
    have hDN : (|BL| + Real.pi * |Bθ|) * chartNormSq wY e z v ≤ D * chartNormSq wY e z v :=
      mul_le_mul_of_nonneg_right hD1 hN
    have hDη : |BL| * ‖η‖ ^ 2 ≤ D * ‖η‖ ^ 2 := mul_le_mul_of_nonneg_right hD2 hη
    nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- clause (a)
    intro x t ht1 ht2
    have hs1 : rL ≤ Real.exp (Real.log t) := by rw [Real.exp_log (hrL.trans_le ht1)]; exact ht1
    have hs2 : Real.exp (Real.log t) ≤ r₀ := by rw [Real.exp_log (hrL.trans_le ht1)]; exact ht2
    have hv := (hB x (Real.log t) hs1 hs2).1
    rw [Real.exp_log (hrL.trans_le ht1)] at hv
    refine (hM x).trans ?_
    rw [EReal.coe_le_coe_iff]
    have ht2' : rL ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hrL.le ht1 2
    have hKt : K * rL ^ 2 ≤ K * t ^ 2 := mul_le_mul_of_nonneg_left ht2' (hK₀.trans hK)
    have hvB := neg_abs_le (smoothing wY A g x t)
    change M ≤ smoothing wY A g x t + K * t ^ 2
    have : |smoothing wY A g x t| ≤ |B| := hv.trans (le_abs_self B)
    nlinarith [le_abs_self M]
  · -- clause (b)
    intro x s hs1 hs2
    have hsS : s ∈ Iio (Real.log r₁) := by
      rw [mem_Iio]
      calc s = Real.log (Real.exp s) := (Real.log_exp s).symm
        _ < Real.log r₁ := Real.log_lt_log (Real.exp_pos s) (hs2.trans_lt hr₀)
    obtain ⟨hd1, hd2⟩ := deriv_add_sq_exp isOpen_Iio (contDiffOn_smoothing_logRadius hr hg x)
      hsS K
    have hbs := hB x s hs1 hs2
    have he2 : rL ^ 2 ≤ Real.exp s ^ 2 := pow_le_pow_left₀ hrL.le hs1 2
    have hKe : K * rL ^ 2 ≤ K * Real.exp s ^ 2 := mul_le_mul_of_nonneg_left he2 (hK₀.trans hK)
    have hb1 := neg_abs_le (deriv (fun s => smoothing wY A g x (Real.exp s)) s)
    have hb2 := neg_abs_le (deriv (deriv (fun s => smoothing wY A g x (Real.exp s))) s)
    have hBB : |B| + 1 ≤ B' := by simp only [B']; linarith [abs_nonneg M]
    refine ⟨?_, ?_⟩
    · change 0 ≤ deriv (fun s => smoothing wY A g x (Real.exp s) + K * Real.exp s ^ 2) s
      rw [hd1]
      nlinarith [le_abs_self B]
    · change 0 < deriv (deriv (fun s => smoothing wY A g x (Real.exp s) + K * Real.exp s ^ 2)) s
      rw [hd2]
      nlinarith [le_abs_self B]
  · -- clause (c)
    intro e z hz w hw1 hw2 hlam W ρ hzW hρ v η
    have h := hlevi e z hz w hw1 hw2 W ρ hzW hρ v η
    have hN := chartNormSq_nonneg wY e hz v
    have hCw : D ≤ C * ‖w‖ := hCrL.trans (mul_le_mul_of_nonneg_left hw1 (hC₀.trans hC))
    have hAlam : 0 ≤ Aa * logSlope H (e.val.symm z) ‖w‖ := mul_nonneg hA hlam
    have hCpos : 0 ≤ C := hC₀.trans hC
    have h3 : D * chartNormSq wY e z v ≤ C * ‖w‖ * chartNormSq wY e z v :=
      mul_le_mul_of_nonneg_right hCw hN
    have h4 : D * ‖η‖ ^ 2 ≤ C * ‖η‖ ^ 2 := mul_le_mul_of_nonneg_right hC1 (sq_nonneg _)
    have h5 : 0 ≤ Aa * logSlope H (e.val.symm z) ‖w‖ * chartNormSq wY e z v :=
      mul_nonneg hAlam hN
    have h6 : 0 ≤ C * Real.sqrt (chartNormSq wY e z v) * ‖η‖ := by positivity
    have h7 : (Aa * logSlope H (e.val.symm z) ‖w‖ + C * ‖w‖) * chartNormSq wY e z v =
        Aa * logSlope H (e.val.symm z) ‖w‖ * chartNormSq wY e z v +
          C * ‖w‖ * chartNormSq wY e z v := by ring
    linarith
  · -- clause (d)
    intro e z hz L r hL hr1 hr2 hlam w hw W ρ hzW hρ v η
    have h := hlevi e z hz w (hw ▸ hr1) (hw ▸ hr2) W ρ hzW hρ v η
    have hN := chartNormSq_nonneg wY e hz v
    have hCpos : 0 ≤ C := hC₀.trans hC
    have hr0 : 0 < r := hrL.trans_le hr1
    have hr2' : rL ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hrL.le hr1 2
    have hCLr2 : 0 ≤ C * L * r ^ 2 := mul_nonneg (mul_nonneg hCpos hL) (sq_nonneg r)
    have hCLr : 0 ≤ C * L * r := mul_nonneg (mul_nonneg hCpos hL) hr0.le
    have h1 : D ≤ C * (1 + L) * r ^ 2 := by
      have := hCrL2.trans (mul_le_mul_of_nonneg_left hr2' hCpos)
      have e1 : C * (1 + L) * r ^ 2 = C * r ^ 2 + C * L * r ^ 2 := by ring
      linarith
    have h2 : D ≤ C * (1 + L) * r := by
      have := hCrL.trans (mul_le_mul_of_nonneg_left hr1 hCpos)
      have e1 : C * (1 + L) * r = C * r + C * L * r := by ring
      linarith
    have hAlam : 0 ≤ Aa * logSlope H (e.val.symm z) r := mul_nonneg hA hlam
    have hC3 : 0 ≤ C * (1 + L) * r := by positivity
    have h3 : D * chartNormSq wY e z v ≤ C * (1 + L) * r ^ 2 * chartNormSq wY e z v :=
      mul_le_mul_of_nonneg_right h1 hN
    have h4 : D * ‖η‖ ^ 2 ≤ C * (1 + L) * r * ‖η‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    have h5 : 0 ≤ Aa * logSlope H (e.val.symm z) r * chartNormSq wY e z v := mul_nonneg hAlam hN
    have h6 : 0 ≤ C * (1 + L) * r * Real.sqrt (chartNormSq wY e z v) * ‖η‖ := by positivity
    have h7 : (Aa * logSlope H (e.val.symm z) r + C * (1 + L) * r ^ 2) * chartNormSq wY e z v =
        Aa * logSlope H (e.val.symm z) r * chartNormSq wY e z v +
          C * (1 + L) * r ^ 2 * chartNormSq wY e z v := by ring
    linarith

end SGPT.NPP.DN5
