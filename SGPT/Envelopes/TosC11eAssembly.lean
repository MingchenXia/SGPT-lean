import SGPT.Envelopes.TosC11eLocal
import SGPT.Envelopes.TosC11cAssembly

/-!
# FPT `lem:penalized-real-hessian` and `thm:Tos_C11` for connected `X`

Lane TOS-C11e (`claude-tos-c11e`, nodes `claude-tos-c11e:estimate`, `claude-tos-c11e:tos-c11`).
Source: Xia, *Foundations of pluripotential theory*, `lem:penalized-real-hessian` (after Tosatti
2018 and Chu–Tosatti–Weinkove), and SGPT `thm:Tos_C11`
(`references/sgpt-d3f272c3/source/author/chapter_npp.tex:1202`; the section containing it begins
"Let `X` be a connected compact Kähler manifold").

* `penalizedHessianEstimate_of_pos` — the estimate `TosC11c.PenalizedHessianEstimate A D δ` for
  every compact connected Kähler manifold of positive dimension.  Uniform bounds for the values,
  the gradients and `ddᶜu` (Berman; lanes TOS-C11b/c); the weight
  `w = -(τ/2) log(1 + S - |∇u|²/π) - A u` with `A` from the local estimate; a maximum point `y` of
  `(∇²u(v, v)/g(v, v)) e^{w}` (`TosC11c.exists_max_hessQuot`); Kähler normal coordinates at `y`
  diagonalizing the complex Hessian of the local potential of `A + ddᶜu`
  (`TosC11d.exists_normal_frame`); the local estimate at `y`
  (`max_le_of_frame`); hence `∇²u ≤ Λ g` everywhere, and the chart Hessian bounds on the
  `δ`-thickenings of the pieces (`TosC11d.chart_bounds`).
* `penalizedHessianEstimate_of_eq_zero` — the (trivial) case of dimension `0`.
* `penalizedHessianEstimate` — `TosC11c.PenalizedHessianEstimateStatement`.
* `tosattiChuZhouConnected` — **`thm:Tos_C11`** for connected `X`:
  `TosC11c.TosattiChuZhouConnectedStatement`, via
  `TosC11c.tosattiChuZhouConnected_of_penalizedHessianEstimate`.
-/

set_option autoImplicit false
-- nested spaces of continuous multilinear maps need deeper pending instance synthesis, as in
-- Mathlib's own build configuration
set_option maxSynthPendingDepth 3

noncomputable section

open Filter Set Metric
open scoped Topology ContDiff InnerProductSpace RealInnerProductSpace ComplexConjugate

universe u

namespace SGPT.Envelopes.TosC11e

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Analysis.KahlerNormal
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity SGPT.Okounkov.TranscendentalWNReg
open SGPT.Envelopes.C11Real SGPT.Envelopes.TosC11d

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- The chart data with the pieces replaced by their closed `δ`-thickenings. -/
def thickenData (D : C11ChartData N Y) {δ : ℝ}
    (hδU : ∀ i, cthickening δ (D.piece i) ⊆ (D.chart i).val.target) : C11ChartData N Y where
  card := D.card
  chart := D.chart
  piece := fun i => cthickening δ (D.piece i)
  isCompact_piece := fun i => (D.isCompact_piece i).cthickening
  piece_subset := hδU
  cover := fun x => by
    obtain ⟨i, hi⟩ := D.cover x
    exact ⟨i, image_mono (self_subset_cthickening _) hi⟩

/-- The bound `|-(τ/2) L - c| ≤ (τ/2) L₀ + c₀` for the weight. -/
theorem abs_weight_le {τ L L₀ c c₀ : ℝ} (hτ : 0 ≤ τ) (hL : 0 ≤ L) (hLL : L ≤ L₀)
    (hc : |c| ≤ c₀) : |-(τ / 2) * L - c| ≤ τ / 2 * L₀ + c₀ := by
  have h1 : τ / 2 * L ≤ τ / 2 * L₀ := mul_le_mul_of_nonneg_left hLL (by positivity)
  have h2 : 0 ≤ τ / 2 * L := by positivity
  have h3 := abs_le.mp hc
  rw [abs_le]
  constructor <;> linarith

/-- **FPT `lem:penalized-real-hessian`** for compact connected Kähler manifolds of positive
dimension, in the charts of chart data `D`: `TosC11c.PenalizedHessianEstimate A D δ`. -/
theorem penalizedHessianEstimate_of_pos [CompactSpace Y] [ConnectedSpace Y] (hN : 0 < N)
    (A : KahlerBackground N Y) (D : C11ChartData N Y) {δ : ℝ}
    (hδU : ∀ i, cthickening δ (D.piece i) ⊆ (D.chart i).val.target) :
    TosC11c.PenalizedHessianEstimate A D δ := by
  intro B
  set B' := max B 0 with hB'def
  have hB'0 : 0 ≤ B' := le_max_right _ _
  -- the enlarged chart data and the uniform gradient bound
  set D' := thickenData D hδU with hD'def
  obtain ⟨δ₁, hδ₁, hδ₁U⟩ := TosC11b.C11ChartData.exists_cthickening_subset D'
  have hδ₁U' : ∀ i, cthickening (2 * (δ₁ / 2)) (D'.piece i) ⊆ (D'.chart i).val.target := fun i => by
    rw [show 2 * (δ₁ / 2) = δ₁ by ring]; exact hδ₁U i
  obtain ⟨β₁, hβ₁1, hgradb⟩ :=
    TosC11b.exists_betaSolution_gradient_bound A D' (half_pos hδ₁) hδ₁U'
  obtain ⟨CG, hCG⟩ := hgradb B' B' hB'0
  -- Berman's Laplacian estimate
  obtain ⟨aB, ΛB, β₂, haB, hΛB, -, hlap⟩ := betaSolution_line_le A
  set Λ' := (1 + B') * ΛB * Real.exp (aB * (2 * B' + N * Real.log (1 + B'))) + 1 with hΛ'def
  have hΛ'1 : 1 ≤ Λ' := by
    have : 0 ≤ (1 + B') * ΛB * Real.exp (aB * (2 * B' + N * Real.log (1 + B'))) := by positivity
    linarith
  set C₀ := B' + N * Real.log (1 + B') with hC₀def
  -- metric bounds on the thickened pieces
  have hcb := fun i => chart_bounds A (D.chart i) (D'.isCompact_piece i) (hδU i)
  choose m Mg Mg' hm hMg hMg' hcbi using hcb
  set Smax : ℝ := ∑ i, CG ^ 2 / m i with hSmax
  have hSmax0 : 0 ≤ Smax := Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hm i).le
  set S : ℝ := Smax / Real.pi with hSdef
  have hS0 : 0 ≤ S := div_nonneg hSmax0 Real.pi_pos.le
  -- normal frames
  have hfr := fun j => exists_normal_frame A (D.chart j) (D.isCompact_piece j) (D.piece_subset j)
  choose CAj C2j C3j hCAj hfrj using hfr
  set CA : ℝ := ∑ j, CAj j with hCAdef
  have hCAle : ∀ j, CAj j ≤ CA := fun j =>
    Finset.single_le_sum (f := CAj) (fun j _ => hCAj j) (Finset.mem_univ j)
  have hCA0 : 0 ≤ CA := Finset.sum_nonneg fun j _ => hCAj j
  set C2 : ℝ := ∑ j, |C2j j| with hC2def
  set C3 : ℝ := ∑ j, |C3j j| with hC3def
  have hC2le : ∀ j, C2j j ≤ C2 := fun j => (le_abs_self _).trans
    (Finset.single_le_sum (f := fun j => |C2j j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j))
  have hC3le : ∀ j, C3j j ≤ C3 := fun j => (le_abs_self _).trans
    (Finset.single_le_sum (f := fun j => |C3j j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j))
  have hC20 : 0 ≤ C2 := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hC30 : 0 ≤ C3 := Finset.sum_nonneg fun j _ => abs_nonneg _
  -- the local estimate
  set Cg : ℝ := 2 * N * (2 * N * (Real.pi * (C2 + C3))) with hCgdef
  have hCg0 : 0 ≤ Cg := by positivity
  have hCg2 : 2 * N * (2 * N * (Real.pi * C2)) ≤ Cg := by
    simp only [hCgdef]; gcongr; linarith
  have hCg3 : 2 * N * (2 * N * (Real.pi * C3)) ≤ Cg := by
    simp only [hCgdef]; gcongr; linarith
  set CF : ℝ := B' * CA with hCFdef
  set BF : ℝ := 2 * B' * CA ^ 2 with hBFdef
  obtain ⟨Aℓ, Λℓ, hAℓ, hloc⟩ := exists_localBound (n := N) (Cg := Cg) (R := 1 + Λ') (S := S)
    (CF := CF) (BF := BF) hN hCg0 (by linarith) hS0
  set τ : ℝ := (1 + 2 * CF ^ 2)⁻¹ with hτdef
  have hτ0 : 0 < τ := by positivity
  set W : ℝ := τ / 2 * Real.log (1 + S) + Aℓ * C₀ with hWdef
  set Λ₁ : ℝ := max (Real.pi * Λℓ) 0 * Real.exp W with hΛ₁def
  have hΛ₁0 : 0 ≤ Λ₁ := by positivity
  set Λg : ℝ := Λ₁ * Real.exp W with hΛgdef
  have hΛg0 : 0 ≤ Λg := by positivity
  set C : ℝ := ∑ i, |4 * Real.pi * Mg i + (Λg * Mg i + 3 / 2 * Mg' i * (CG / m i))| with hCdef
  refine ⟨max β₁ (max β₂ 1), C, fun β hβ F hF hFB hFD hFddc U i z hz => ?_⟩
  have hββ₁ : β₁ ≤ β := (le_max_left _ _).trans hβ
  have hββ₂ : β₂ ≤ β := ((le_max_left _ _).trans (le_max_right _ _)).trans hβ
  have hβ1 : 1 ≤ β := ((le_max_right _ _).trans (le_max_right _ _)).trans hβ
  have hβ0 : 0 ≤ β := by linarith
  have hBB' : B ≤ B' := le_max_left _ _
  have hFB' : ∀ y, |F y| ≤ B' := fun y => (hFB y).trans hBB'
  have hFddc' : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      ∀ v : ComplexModel N, (ddcClosedForm F hF).val.coeff e z ![v, Complex.I • v] ≤
        B' * A.form.val.coeff e z ![v, Complex.I • v] := fun e z hz v =>
    (hFddc e z hz v).trans (mul_le_mul_of_nonneg_right hBB'
      (coefficientSemipositive_of_isKahler A.isKahler hz v))
  -- uniform bounds for `u`
  set u := U.u with hudef
  have hu : ChartSmooth (n := N) u := U.smooth
  have hval : ∀ y, |u y| ≤ C₀ := fun y =>
    TosC11b.abs_betaSolution_le hβ1 hF hB'0 hFddc' hFB' U y
  have hgradK : ∀ i, ∀ z ∈ D'.piece i,
      ‖fderiv ℝ (fun w => u ((D.chart i).val.symm w)) z‖ ≤ CG := fun i z hz =>
    hCG β hββ₁ F hF hFB' hFddc' U i z (self_subset_cthickening _ hz)
  have hddc : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      ∀ v : ComplexModel N, |(ddcClosedForm u hu).val.coeff e z ![v, Complex.I • v]| ≤
        Λ' * A.form.val.coeff e z ![v, Complex.I • v] := fun e z hz v =>
    TosC11b.abs_ddc_betaSolution_le haB hΛB hlap hββ₂ hβ1 hF hB'0 hFddc' hFB' U e hz v
  -- the gradient length
  have hsle : ∀ x, TosC11c.gradNormSqFun A u x ≤ Smax := by
    intro x
    obtain ⟨k, z', hz', rfl⟩ := D.cover x
    have hz't := D.piece_subset k hz'
    have hxs : (D.chart k).val.symm z' ∈ (D.chart k).val.source := (D.chart k).val.map_target hz't
    rw [TosC11c.gradNormSqFun_eq A hu (D.chart k) hxs, (D.chart k).val.right_inv hz't]
    have hz'K : z' ∈ D'.piece k := self_subset_cthickening _ hz'
    have h1 := (hcbi k u hu).1 z' hz'K
    have h2 : ‖fderiv ℝ (fun w => u ((D.chart k).val.symm w)) z'‖ ^ 2 ≤ CG ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hgradK k z' hz'K) 2
    have h3 : CG ^ 2 / m k ≤ Smax :=
      Finset.single_le_sum (f := fun i => CG ^ 2 / m i)
        (fun i _ => div_nonneg (sq_nonneg _) (hm i).le) (Finset.mem_univ k)
    exact h1.trans ((div_le_div_of_nonneg_right h2 (hm k).le).trans h3)
  have hs0le : ∀ x, 0 ≤ TosC11c.gradNormSqFun A u x := fun x =>
    TosC11c.gradNormSq_nonneg A u _ ((complexChartAt (n := N) x).val.map_source
      (mem_complexChartAt_source x))
  -- the weight
  set w : Y → ℝ := fun x => -(τ / 2) * Real.log (1 + S - TosC11c.gradNormSqFun A u x / Real.pi) -
    Aℓ * u x with hwdef
  have hlogpos : ∀ x, 1 ≤ 1 + S - TosC11c.gradNormSqFun A u x / Real.pi := fun x => by
    have h1 : TosC11c.gradNormSqFun A u x / Real.pi ≤ S :=
      div_le_div_of_nonneg_right (hsle x) Real.pi_pos.le
    linarith
  have hwc : Continuous w := by
    have hsc := TosC11c.continuous_gradNormSqFun A hu
    have huc : Continuous u := YauUniformEstimate.continuous_of_chartSmooth hu
    have hg : Continuous fun x => 1 + S - TosC11c.gradNormSqFun A u x / Real.pi :=
      continuous_const.sub (hsc.div_const _)
    have hl : Continuous fun x => Real.log (1 + S - TosC11c.gradNormSqFun A u x / Real.pi) :=
      hg.log fun x => ne_of_gt (by linarith [hlogpos x])
    exact (continuous_const.mul hl).sub (continuous_const.mul huc)
  have hwb : ∀ x, |w x| ≤ W := by
    intro x
    have h1 : 0 ≤ Real.log (1 + S - TosC11c.gradNormSqFun A u x / Real.pi) :=
      Real.log_nonneg (hlogpos x)
    have h2 : Real.log (1 + S - TosC11c.gradNormSqFun A u x / Real.pi) ≤ Real.log (1 + S) :=
      Real.log_le_log (by linarith [hlogpos x]) (by
        have := div_nonneg (hs0le x) Real.pi_pos.le; linarith)
    have h4 : |Aℓ * u x| ≤ Aℓ * C₀ := by rw [abs_mul, abs_of_pos hAℓ]; gcongr; exact hval x
    exact abs_weight_le hτ0.le h1 h2 h4
  -- the maximum point
  obtain ⟨y, M, hle, hatt⟩ := TosC11c.exists_max_hessQuot hN A hu hwc
  obtain ⟨j, z₀, hz₀, hyz⟩ := D.cover y
  have hz₀t : z₀ ∈ (D.chart j).val.target := D.piece_subset j hz₀
  have hys : y ∈ (D.chart j).val.source := by rw [← hyz]; exact (D.chart j).val.map_target hz₀t
  have hey : (D.chart j).val y = z₀ := by rw [← hyz]; exact (D.chart j).val.right_inv hz₀t
  -- a local potential of `A` near `z₀` and normal coordinates at `z₀`
  obtain ⟨Wp, ρ, hz₀W, hpot⟩ :=
    LocalPotentials.closedRealOneOne_hasLocalPotentials A.form (D.chart j) z₀ hz₀t
  have hfz : ContDiffOn ℝ ∞ (fun z => ρ z + u ((D.chart j).val.symm z)) Wp :=
    hpot.2.2.1.add ((hu (D.chart j)).mono hpot.2.1)
  have hfz2 : ContDiffAt ℝ 2 (fun z => ρ z + u ((D.chart j).val.symm z)) z₀ :=
    (hfz.contDiffAt (hpot.1.mem_nhds hz₀W)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  obtain ⟨Φ, r, hΦ, hΦ0, hbij, h0, hd, h2, h3, hDΦ, hD2Φ, hdiag⟩ :=
    hfrj j z₀ hz₀ _ (complexHessian_isHermitian hfz2)
  -- the local estimate at the maximum point
  have hM : M ≤ Real.pi * Λℓ * Real.exp (w y) := by
    have hRline : ∀ v : ComplexModel N,
        (ddcClosedForm U.u U.smooth).val.coeff (D.chart j) z₀ ![v, Complex.I • v] ≤
          (1 + Λ' - 1) * A.form.val.coeff (D.chart j) z₀ ![v, Complex.I • v] := fun v => by
      rw [add_sub_cancel_left]; exact (le_abs_self _).trans (hddc _ _ hz₀t v)
    have hs : TosC11c.gradNormSq A U.u (D.chart j) z₀ ≤ Real.pi * S := by
      have h := TosC11c.gradNormSqFun_eq A hu (D.chart j) hys
      rw [hey] at h
      rw [← h, hSdef, mul_div_cancel₀ _ Real.pi_ne_zero]
      exact hsle y
    have hD2Φ' : ∀ v, ‖fderiv ℝ (fderiv ℝ Φ) 0 v v‖ ≤ CA * CA * ‖v‖ ^ 2 := fun v =>
      (hD2Φ v).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul (hCAle j) (hCAle j) (hCAj j) hCA0) (sq_nonneg _))
    obtain ⟨ζ, hζ1, hζM⟩ := hatt (D.chart j) hys
    have h := max_le_of_frame A hβ0 hF U hpot hz₀W hΦ hΦ0 hbij h0 hd hC20 hC30
      (fun p q => (h2 p q).trans (hC2le j)) (fun p q => (h3 p q).trans (hC3le j))
      (hDΦ.trans (hCAle j)) hD2Φ' hdiag hloc hCg2 hCg3 hRline hB'0
      (((hFD j z₀ hz₀).1).trans hBB') (((hFD j z₀ hz₀).2).trans hBB') le_rfl le_rfl hs
      (w := w) (fun x => rfl) (M := M) (fun z hz v hv => hle (D.chart j) z hz v hv)
      ⟨ζ, fun h => by rw [h, norm_zero] at hζ1; exact zero_ne_one hζ1, by
        rw [hyz, ← hey]; exact hζM⟩
    rwa [hyz] at h
  have hMΛ : M ≤ Λ₁ := by
    calc M ≤ Real.pi * Λℓ * Real.exp (w y) := hM
      _ ≤ max (Real.pi * Λℓ) 0 * Real.exp (w y) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      _ ≤ max (Real.pi * Λℓ) 0 * Real.exp W :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (abs_le.mp (hwb y)).2) (le_max_right _ _)
  -- the covariant Hessian quotient is bounded everywhere
  have hq : ∀ i, ∀ z ∈ D'.piece i, ∀ v, v ≠ 0 → TosC11c.hessQuot A u (D.chart i) z v ≤ Λg := by
    intro i z hz v hv
    have h := hle (D.chart i) z (hδU i hz) v hv
    have hx : -w ((D.chart i).val.symm z) ≤ W := by
      linarith [(abs_le.mp (hwb ((D.chart i).val.symm z))).1]
    have h1 : TosC11c.hessQuot A u (D.chart i) z v ≤
        M * Real.exp (-w ((D.chart i).val.symm z)) := by
      have := mul_le_mul_of_nonneg_right h (Real.exp_pos (-w ((D.chart i).val.symm z))).le
      rwa [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at this
    calc TosC11c.hessQuot A u (D.chart i) z v ≤ M * Real.exp (-w ((D.chart i).val.symm z)) := h1
      _ ≤ max M 0 * Real.exp (-w ((D.chart i).val.symm z)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      _ ≤ Λ₁ * Real.exp W :=
          mul_le_mul (max_le hMΛ hΛ₁0) (Real.exp_le_exp.mpr hx) (Real.exp_pos _).le hΛ₁0
  -- the chart Hessian bound
  have hbd := (hcbi i u hu).2 U.isKahler Λg CG hΛg0 (hq i) (hgradK i) z hz
  refine hbd.trans ((le_abs_self _).trans ?_)
  exact Finset.single_le_sum
    (f := fun i => |4 * Real.pi * Mg i + (Λg * Mg i + 3 / 2 * Mg' i * (CG / m i))|)
    (fun i _ => abs_nonneg _) (Finset.mem_univ i)

/-- **FPT `lem:penalized-real-hessian` in dimension `0`**: every chart Hessian vanishes. -/
theorem penalizedHessianEstimate_of_eq_zero (hN : N = 0) (A : KahlerBackground N Y)
    (D : C11ChartData N Y) (δ : ℝ) : TosC11c.PenalizedHessianEstimate A D δ := by
  intro B
  refine ⟨0, 0, fun β _ F hF _ _ _ U i z _ => ?_⟩
  subst hN
  have h : fderiv ℝ (fderiv ℝ (fun z => U.u ((D.chart i).val.symm z))) z = 0 :=
    ContinuousLinearMap.ext fun v => by rw [Subsingleton.elim v 0, map_zero, map_zero]
  rw [h, norm_zero]

/-- **FPT `lem:penalized-real-hessian`** (`TosC11c.PenalizedHessianEstimateStatement`): for every
compact connected Kähler manifold, chart data `D` and `δ > 0` with the closed `δ`-thickenings of the
pieces in the chart targets, the chart Hessians of the solutions of the penalized equations are
bounded uniformly in `β ≥ β₀` and in the obstacles with bounded values, derivatives, Hessians and
`ddᶜ`. -/
theorem penalizedHessianEstimate : TosC11c.PenalizedHessianEstimateStatement.{u} := by
  intro N Y _ _ _ _ _ A D δ _ hδU
  rcases Nat.eq_zero_or_pos N with hN | hN
  · exact penalizedHessianEstimate_of_eq_zero hN A D δ
  · exact penalizedHessianEstimate_of_pos hN A D hδU

/-- **Source `thm:Tos_C11` (Tosatti, Chu–Zhou)** for connected `X` (the book's section containing
`thm:Tos_C11` assumes `X` connected): for a compact connected Kähler manifold with Kähler
background `A` and chart data `D`, and every `B`, there is `C` such that for every
`f ∈ C^{1,1}(X)` with `‖f‖_{C^{1,1}, D} ≤ B`, the envelope `P_A(f)` is real-valued, belongs to
`C^{1,1}(X)` and satisfies `‖P_A(f)‖_{C^{1,1}, D} ≤ C`. -/
theorem tosattiChuZhouConnected : TosC11c.TosattiChuZhouConnectedStatement.{u} :=
  TosC11c.tosattiChuZhouConnected_of_penalizedHessianEstimate penalizedHessianEstimate

end SGPT.Envelopes.TosC11e
