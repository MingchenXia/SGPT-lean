import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Second-order bounds for smooth functions that are even in a fibre variable

Lane DN10, `thm:DNT23_C11bar` (`chapter_npp.tex`), via FPT `lem:chern-joint-smoothing`
(`chapters/inputs/q10-big-envelope-regularity.tex`, Step 5, the paragraph "It remains to subtract
the smoothing of the smooth function `q`").

FPT: "Since `q` is smooth, `Ψ_q(z, w)` is smooth also at `w = 0`, where it equals `q(z)`.  By
rotation invariance, the terms of degree one [...] vanish, so `Ψ_q(z, w) - q(z)` is `|w|²` times a
smooth function of `z`, up to an error `O(|w|³)` whose derivatives lose one power of `|w|` for each
derivative in `w`."  This file proves the abstract statement behind this sentence
(`exists_even_taylor_bounds`): if `E(z, y)` is `C⁴` near `K × {0}` (`K` compact), vanishes on the
zero section and is even in `y`, then, uniformly for `z ∈ K` and small `y`,

* `|E(z, y)| ≤ C |y|²`,
* `|∂_y E(z, y)[b]| ≤ C |y| |b|`,
* `|D²E(z, y)[(a, b), (a, b)]| ≤ C (|y|² |a|² + |y| |a| |b| + |b|²)`.

The proof uses only first-order mean value inequalities along the fibres `{z} × B̄(0, |y|)`: the
`z z`-block of the Hessian vanishes on the zero section and, being even in `y`, has vanishing
`y`-derivative there; the mixed blocks are odd in `y`.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 5

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace SGPT.NPP.DN10

/-! ### Generic helpers -/

section Helpers

variable {X A B : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- Evaluating a differentiable family of linear maps at a fixed vector. -/
theorem hasFDerivAt_apply_const {c : X → A →L[ℝ] B} {c' : X →L[ℝ] A →L[ℝ] B} {x : X}
    (hc : HasFDerivAt c c' x) (a : A) : HasFDerivAt (fun y => c y a) (c'.flip a) x := by
  simpa using hc.clm_apply (hasFDerivAt_const a x)

theorem norm_apply₂_le {C' : Type*} [NormedAddCommGroup C'] [NormedSpace ℝ C']
    (T : X →L[ℝ] A →L[ℝ] C') (x : X) (a : A) : ‖T x a‖ ≤ ‖T‖ * ‖x‖ * ‖a‖ :=
  T.le_opNorm₂ x a

theorem norm_apply₃_le {C' : Type*} [NormedAddCommGroup C'] [NormedSpace ℝ C']
    (T : X →L[ℝ] A →L[ℝ] B →L[ℝ] C') (x : X) (a : A) (b : B) :
    ‖T x a b‖ ≤ ‖T‖ * ‖x‖ * ‖a‖ * ‖b‖ := by
  calc ‖T x a b‖ ≤ ‖T x a‖ * ‖b‖ := (T x a).le_opNorm b
    _ ≤ ‖T‖ * ‖x‖ * ‖a‖ * ‖b‖ := by gcongr; exact T.le_opNorm₂ x a

theorem norm_apply₄_le {C' D : Type*} [NormedAddCommGroup C'] [NormedSpace ℝ C']
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (T : X →L[ℝ] A →L[ℝ] B →L[ℝ] C' →L[ℝ] D) (x : X) (a : A) (b : B) (c : C') :
    ‖T x a b c‖ ≤ ‖T‖ * ‖x‖ * ‖a‖ * ‖b‖ * ‖c‖ := by
  calc ‖T x a b c‖ ≤ ‖T x a b‖ * ‖c‖ := (T x a b).le_opNorm c
    _ ≤ ‖T‖ * ‖x‖ * ‖a‖ * ‖b‖ * ‖c‖ := by gcongr; exact norm_apply₃_le T x a b

theorem abs_add_four_le (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  calc |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
    _ ≤ |a + b| + |c| + |d| := by gcongr; exact abs_add_le _ _
    _ ≤ |a| + |b| + |c| + |d| := by gcongr; exact abs_add_le _ _

/-- The derivative of an even function vanishes at the origin. -/
theorem hasFDerivAt_eq_zero_of_even {φ : X → A} {φ' : X →L[ℝ] A} (hφ : HasFDerivAt φ φ' 0)
    (h : ∀ᶠ y in 𝓝 (0 : X), φ (-y) = φ y) : φ' = 0 := by
  have h0 : HasFDerivAt φ φ' (-(0 : X)) := by simpa using hφ
  have h1 : HasFDerivAt (fun y => φ (-y)) (φ'.comp (-ContinuousLinearMap.id ℝ X)) 0 :=
    h0.comp (0 : X) (hasFDerivAt_id (0 : X)).neg
  have h2 : HasFDerivAt (fun y => φ (-y)) φ' 0 := hφ.congr_of_eventuallyEq h
  have h3 := h1.unique h2
  ext c
  have h4 := congrArg (fun T : X →L[ℝ] A => T c) h3
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply, map_neg] at h4
  simp only [ContinuousLinearMap.zero_apply]
  have : (2 : ℝ) • φ' c = 0 := by rw [two_smul]; nth_rewrite 1 [← h4]; exact neg_add_cancel _
  exact (smul_eq_zero.mp this).resolve_left two_ne_zero

end Helpers

section Fibre

variable {P Q F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `σ(z, y) = (z, -y)`. -/
def flipSnd : (P × Q) →L[ℝ] (P × Q) :=
  (ContinuousLinearMap.id ℝ P).prodMap (-ContinuousLinearMap.id ℝ Q)

@[simp] theorem flipSnd_apply (x : P × Q) : (flipSnd : (P × Q) →L[ℝ] (P × Q)) x = (x.1, -x.2) :=
  rfl

/-- A function vanishing on the zero section near `z` has vanishing `z`-derivative there. -/
theorem hasFDerivAt_inl_eq_zero {G : P × Q → F} {G' : P × Q →L[ℝ] F} {z : P}
    (hG : HasFDerivAt G G' (z, 0)) (h0 : ∀ᶠ z' in 𝓝 z, G (z', 0) = 0) (a : P) :
    G' (a, 0) = 0 := by
  have h1 : HasFDerivAt (fun z' => G (z', 0)) (G'.comp (ContinuousLinearMap.inl ℝ P Q)) z :=
    hG.comp z (ContinuousLinearMap.inl ℝ P Q).hasFDerivAt
  have h2 : HasFDerivAt (fun z' => G (z', 0)) (0 : P →L[ℝ] F) z :=
    (hasFDerivAt_const (0 : F) z).congr_of_eventuallyEq h0
  have h3 := congrArg (fun T : P →L[ℝ] F => T a) (h1.unique h2)
  simpa using h3

/-- **Mean value inequality along a fibre** `{z} × B̄(0, r)`. -/
theorem norm_sub_le_of_fibre {G : P × Q → F} {G' : Q → (P × Q →L[ℝ] F)} {z : P} {r B : ℝ}
    (hB0 : 0 ≤ B) (hG : ∀ y ∈ closedBall (0 : Q) r, HasFDerivAt G (G' y) (z, y))
    (hb : ∀ y ∈ closedBall (0 : Q) r, ∀ c : Q, ‖G' y (0, c)‖ ≤ B * ‖c‖)
    {y : Q} (hy : y ∈ closedBall (0 : Q) r) : ‖G (z, y) - G (z, 0)‖ ≤ B * ‖y‖ := by
  set L : Q →L[ℝ] P × Q := (0 : Q →L[ℝ] P).prod (ContinuousLinearMap.id ℝ Q) with hL
  have hf : ∀ y' ∈ closedBall (0 : Q) r,
      HasFDerivWithinAt (fun y => G (z, y)) ((G' y').comp L) (closedBall (0 : Q) r) y' := by
    intro y' hy'
    have hc : HasFDerivAt (fun y : Q => ((z, y) : P × Q)) L y' :=
      (hasFDerivAt_const z y').prodMk (hasFDerivAt_id y')
    exact ((hG y' hy').comp y' hc).hasFDerivWithinAt
  have hbd : ∀ y' ∈ closedBall (0 : Q) r, ‖(G' y').comp L‖ ≤ B := by
    intro y' hy'
    refine ContinuousLinearMap.opNorm_le_bound _ hB0 fun c => ?_
    simpa [hL] using hb y' hy' c
  have h0 : (0 : Q) ∈ closedBall (0 : Q) r := by
    rw [mem_closedBall, dist_self]; exact (norm_nonneg y).trans (by simpa using hy)
  have := (convex_closedBall (0 : Q) r).norm_image_sub_le_of_norm_hasFDerivWithin_le hf hbd h0 hy
  simpa using this

end Fibre

/-! ### The main estimate -/

section Main

variable {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- **Second-order bounds for an even function vanishing on the zero section.**  Let `E(z, y)` be
`C⁴` on `U × B(0, ρ)`, `E(z, 0) = 0` and `E(z, -y) = E(z, y)`.  Then for a compact `K ⊆ U` and
`ρ' < ρ` there is `C ≥ 0` with, for `z ∈ K` and `|y| ≤ ρ'`:
`|E(z, y)| ≤ C|y|²`, `|∂_y E(z, y)[b]| ≤ C|y||b|` and
`|D²E(z, y)[(a, b), (a, b)]| ≤ C(|y|²|a|² + |y||a||b| + |b|²)`. -/
theorem exists_even_taylor_bounds [ProperSpace Q] {E : P × Q → ℝ} {U K : Set P} {ρ ρ' : ℝ}
    (hU : IsOpen U) (hE : ContDiffOn ℝ 4 E (U ×ˢ ball (0 : Q) ρ))
    (hzero : ∀ z ∈ U, E (z, 0) = 0)
    (heven : ∀ z ∈ U, ∀ y ∈ ball (0 : Q) ρ, E (z, -y) = E (z, y))
    (hK : IsCompact K) (hKU : K ⊆ U) (hρ'0 : 0 ≤ ρ') (hρ' : ρ' < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ y ∈ closedBall (0 : Q) ρ',
      |E (z, y)| ≤ C * ‖y‖ ^ 2 ∧
      (∀ b : Q, |fderiv ℝ E (z, y) (0, b)| ≤ C * ‖y‖ * ‖b‖) ∧
      ∀ (a : P) (b : Q), |fderiv ℝ (fderiv ℝ E) (z, y) (a, b) (a, b)| ≤
        C * (‖y‖ ^ 2 * ‖a‖ ^ 2 + ‖y‖ * ‖a‖ * ‖b‖ + ‖b‖ ^ 2) := by
  set V : Set (P × Q) := U ×ˢ ball (0 : Q) ρ with hVdef
  have hV : IsOpen V := hU.prod isOpen_ball
  set D1 := fderiv ℝ E with hD1def
  set D2 := fderiv ℝ D1 with hD2def
  set D3 := fderiv ℝ D2 with hD3def
  set D4 := fderiv ℝ D3 with hD4def
  have hc1 : ContDiffOn ℝ 3 D1 V := hE.fderiv_of_isOpen hV (by norm_num)
  have hc2 : ContDiffOn ℝ 2 D2 V := hc1.fderiv_of_isOpen hV (by norm_num)
  have hc3 : ContDiffOn ℝ 1 D3 V := hc2.fderiv_of_isOpen hV (by norm_num)
  have hc4 : ContinuousOn D4 V := hc3.continuousOn_fderiv_of_isOpen hV le_rfl
  have hd0 : ∀ x ∈ V, HasFDerivAt E (D1 x) x := fun x hx =>
    ((hE.differentiableOn (by norm_num)) x hx).differentiableAt (hV.mem_nhds hx) |>.hasFDerivAt
  have hd1 : ∀ x ∈ V, HasFDerivAt D1 (D2 x) x := fun x hx =>
    ((hc1.differentiableOn (by norm_num)) x hx).differentiableAt (hV.mem_nhds hx) |>.hasFDerivAt
  have hd2 : ∀ x ∈ V, HasFDerivAt D2 (D3 x) x := fun x hx =>
    ((hc2.differentiableOn (by norm_num)) x hx).differentiableAt (hV.mem_nhds hx) |>.hasFDerivAt
  have hd3 : ∀ x ∈ V, HasFDerivAt D3 (D4 x) x := fun x hx =>
    ((hc3.differentiableOn one_ne_zero) x hx).differentiableAt (hV.mem_nhds hx) |>.hasFDerivAt
  -- the compact set `S = K × B̄(0, ρ')`
  set S : Set (P × Q) := K ×ˢ closedBall (0 : Q) ρ' with hSdef
  have hS : IsCompact S := hK.prod (isCompact_closedBall 0 ρ')
  have hSV : S ⊆ V := prod_mono hKU (closedBall_subset_ball hρ')
  obtain ⟨M₂, hM₂⟩ := hS.exists_bound_of_continuousOn (hc2.continuousOn.mono hSV)
  obtain ⟨M₃, hM₃⟩ := hS.exists_bound_of_continuousOn (hc3.continuousOn.mono hSV)
  obtain ⟨M₄, hM₄⟩ := hS.exists_bound_of_continuousOn (hc4.mono hSV)
  set N₂ := max M₂ 0
  set N₃ := max M₃ 0
  set N₄ := max M₄ 0
  have hN₂ : ∀ x ∈ S, ‖D2 x‖ ≤ N₂ := fun x hx => (hM₂ x hx).trans (le_max_left _ _)
  have hN₃ : ∀ x ∈ S, ‖D3 x‖ ≤ N₃ := fun x hx => (hM₃ x hx).trans (le_max_left _ _)
  have hN₄ : ∀ x ∈ S, ‖D4 x‖ ≤ N₄ := fun x hx => (hM₄ x hx).trans (le_max_left _ _)
  have hN₂0 : 0 ≤ N₂ := le_max_right _ _
  have hN₃0 : 0 ≤ N₃ := le_max_right _ _
  have hN₄0 : 0 ≤ N₄ := le_max_right _ _
  -- membership helpers
  have hmemV : ∀ z ∈ U, ∀ y ∈ ball (0 : Q) ρ, ((z, y) : P × Q) ∈ V := fun z hz y hy => ⟨hz, hy⟩
  have hnegball : ∀ y ∈ ball (0 : Q) ρ, -y ∈ ball (0 : Q) ρ := fun y hy => by
    simpa [mem_ball, dist_zero_right, norm_neg] using hy
  have hσV : ∀ x ∈ V, flipSnd x ∈ V := fun x hx => ⟨hx.1, hnegball _ hx.2⟩
  -- `E ∘ σ = E` on `V`
  have hEσ : ∀ x ∈ V, E (flipSnd x) = E x := fun x hx => by
    obtain ⟨z, y⟩ := x
    exact heven z hx.1 y hx.2
  -- parity of the first derivative
  have hpar1 : ∀ x ∈ V, ∀ u, D1 (flipSnd x) (flipSnd u) = D1 x u := by
    intro x hx u
    have h1 : HasFDerivAt (fun x' => E (flipSnd x')) ((D1 (flipSnd x)).comp flipSnd) x :=
      (hd0 _ (hσV x hx)).comp x (flipSnd : P × Q →L[ℝ] P × Q).hasFDerivAt
    have hev : (fun x' => E (flipSnd x')) =ᶠ[𝓝 x] E :=
      Filter.eventually_of_mem (hV.mem_nhds hx) hEσ
    have h2 : HasFDerivAt (fun x' => E (flipSnd x')) (D1 x) x := (hd0 x hx).congr_of_eventuallyEq hev
    have := congrArg (fun T : P × Q →L[ℝ] ℝ => T u) (h1.unique h2)
    simpa using this
  -- parity of the second derivative
  have hpar2 : ∀ x ∈ V, ∀ u v, D2 (flipSnd x) (flipSnd u) (flipSnd v) = D2 x u v := by
    intro x hx u v
    have h1 : HasFDerivAt (fun x' => D1 (flipSnd x') (flipSnd v))
        (((D2 (flipSnd x)).flip (flipSnd v)).comp flipSnd) x :=
      (hasFDerivAt_apply_const (hd1 _ (hσV x hx)) (flipSnd v)).comp x
        (flipSnd : P × Q →L[ℝ] P × Q).hasFDerivAt
    have hev : (fun x' => D1 (flipSnd x') (flipSnd v)) =ᶠ[𝓝 x] fun x' => D1 x' v :=
      Filter.eventually_of_mem (hV.mem_nhds hx) fun x' hx' => hpar1 x' hx' v
    have h2 : HasFDerivAt (fun x' => D1 (flipSnd x') (flipSnd v)) ((D2 x).flip v) x :=
      (hasFDerivAt_apply_const (hd1 x hx) v).congr_of_eventuallyEq hev
    have := congrArg (fun T : P × Q →L[ℝ] ℝ => T u) (h1.unique h2)
    simpa using this
  have hρ : 0 < ρ := lt_of_le_of_lt hρ'0 hρ'
  have h0ball : (0 : Q) ∈ ball (0 : Q) ρ := mem_ball_self hρ
  have hz0V : ∀ z ∈ U, ((z, 0) : P × Q) ∈ V := fun z hz => hmemV z hz 0 h0ball
  -- the zero section
  have hz1 : ∀ z ∈ U, ∀ a : P, D1 (z, 0) (a, 0) = 0 := by
    intro z hz a
    have h0 : ∀ᶠ z' in 𝓝 z, E (z', 0) = 0 :=
      Filter.eventually_of_mem (hU.mem_nhds hz) hzero
    exact hasFDerivAt_inl_eq_zero (hd0 _ (hz0V z hz)) h0 a
  have hz2 : ∀ z ∈ U, ∀ a a' : P, D2 (z, 0) (a, 0) (a', 0) = 0 := by
    intro z hz a a'
    have h0 : ∀ᶠ z' in 𝓝 z, D1 (z', 0) (a', 0) = 0 :=
      Filter.eventually_of_mem (hU.mem_nhds hz) fun z' hz' => hz1 z' hz' a'
    have := hasFDerivAt_inl_eq_zero (G := fun x => D1 x (a', 0))
      (hasFDerivAt_apply_const (hd1 _ (hz0V z hz)) (a', 0)) h0 a
    simpa using this
  -- parity on the zero section
  have hy1 : ∀ z ∈ U, ∀ b : Q, D1 (z, 0) (0, b) = 0 := by
    intro z hz b
    have h := hpar1 (z, 0) (hz0V z hz) (0, b)
    simp only [flipSnd_apply, neg_zero] at h
    have e : ((0 : P), -b) = -((0 : P), b) := by simp
    rw [e, map_neg] at h
    linarith
  have hy2 : ∀ z ∈ U, ∀ (a : P) (b : Q),
      D2 (z, 0) (a, 0) (0, b) = 0 ∧ D2 (z, 0) (0, b) (a, 0) = 0 := by
    intro z hz a b
    have h1 := hpar2 (z, 0) (hz0V z hz) (a, 0) (0, b)
    have h2 := hpar2 (z, 0) (hz0V z hz) (0, b) (a, 0)
    simp only [flipSnd_apply, neg_zero] at h1 h2
    have e : ((0 : P), -b) = -((0 : P), b) := by simp
    rw [e, map_neg] at h1
    rw [e, map_neg, ContinuousLinearMap.neg_apply] at h2
    constructor <;> linarith
  -- derivatives of evaluations
  have hev2 : ∀ x ∈ V, ∀ u v, HasFDerivAt (fun x => D2 x u v) (((D3 x).flip u).flip v) x :=
    fun x hx u v => hasFDerivAt_apply_const (hasFDerivAt_apply_const (hd2 x hx) u) v
  have hev3 : ∀ x ∈ V, ∀ u v w, HasFDerivAt (fun x => D3 x u v w)
      ((((D4 x).flip u).flip v).flip w) x :=
    fun x hx u v w => hasFDerivAt_apply_const
      (hasFDerivAt_apply_const (hasFDerivAt_apply_const (hd3 x hx) u) v) w
  -- the `y`-derivative of the `zz`-block vanishes on the zero section (evenness)
  have hz3 : ∀ z ∈ U, ∀ (a : P) (c : Q), D3 (z, 0) (0, c) (a, 0) (a, 0) = 0 := by
    intro z hz a c
    set L : Q →L[ℝ] P × Q := (0 : Q →L[ℝ] P).prod (ContinuousLinearMap.id ℝ Q) with hL
    have hφ : HasFDerivAt (fun y : Q => D2 (z, y) (a, 0) (a, 0))
        ((((D3 (z, 0)).flip (a, 0)).flip (a, 0)).comp L) 0 := by
      have hc : HasFDerivAt (fun y : Q => ((z, y) : P × Q)) L 0 :=
        (hasFDerivAt_const z 0).prodMk (hasFDerivAt_id 0)
      exact (hev2 _ (hz0V z hz) (a, 0) (a, 0)).comp (0 : Q) hc
    have heven' : ∀ᶠ y in 𝓝 (0 : Q), D2 (z, -y) (a, 0) (a, 0) = D2 (z, y) (a, 0) (a, 0) := by
      filter_upwards [isOpen_ball.mem_nhds h0ball] with y hy
      have h := hpar2 (z, y) (hmemV z hz y hy) (a, 0) (a, 0)
      simpa only [flipSnd_apply, neg_zero] using h
    have h0 := hasFDerivAt_eq_zero_of_even hφ heven'
    have := congrArg (fun T : Q →L[ℝ] ℝ => T c) h0
    simpa [hL] using this
  -- bounds
  have hpair1 : ∀ a : P, ‖((a, 0) : P × Q)‖ = ‖a‖ := fun a => by simp
  have hpair2 : ∀ b : Q, ‖((0, b) : P × Q)‖ = ‖b‖ := fun b => by simp
  have hball_sub : ∀ {y y' : Q}, y ∈ closedBall (0 : Q) ρ' → y' ∈ closedBall (0 : Q) ‖y‖ →
      y' ∈ closedBall (0 : Q) ρ' := fun {y y'} hy hy' => by
    rw [mem_closedBall, dist_zero_right] at hy hy' ⊢; linarith
  have hyself : ∀ y : Q, y ∈ closedBall (0 : Q) ‖y‖ := fun y => by simp
  -- (B0) first `y`-derivative
  have hB0 : ∀ z ∈ K, ∀ y ∈ closedBall (0 : Q) ρ', ∀ b : Q,
      |D1 (z, y) (0, b)| ≤ N₂ * ‖b‖ * ‖y‖ := by
    intro z hz y hy b
    have h := norm_sub_le_of_fibre (G := fun x => D1 x (0, b))
      (G' := fun y' => (D2 (z, y')).flip (0, b)) (z := z) (r := ρ') (B := N₂ * ‖b‖)
      (mul_nonneg hN₂0 (norm_nonneg b))
      (fun y' hy' => hasFDerivAt_apply_const (hd1 _ (hSV ⟨hz, hy'⟩)) (0, b))
      (fun y' hy' c => by
        simp only [ContinuousLinearMap.flip_apply]
        calc ‖D2 (z, y') (0, c) (0, b)‖ ≤ ‖D2 (z, y')‖ * ‖((0, c) : P × Q)‖ * ‖((0, b) : P × Q)‖ :=
              norm_apply₂_le _ _ _
          _ ≤ N₂ * ‖c‖ * ‖b‖ := by
              rw [hpair2, hpair2]; gcongr; exact hN₂ _ ⟨hz, hy'⟩
          _ = N₂ * ‖b‖ * ‖c‖ := by ring) hy
    simpa [hy1 z (hKU hz) b, Real.norm_eq_abs] using h
  -- (B1) the value
  have hB1 : ∀ z ∈ K, ∀ y ∈ closedBall (0 : Q) ρ', |E (z, y)| ≤ N₂ * ‖y‖ ^ 2 := by
    intro z hz y hy
    have h := norm_sub_le_of_fibre (G := E) (G' := fun y' => D1 (z, y')) (z := z) (r := ‖y‖)
      (B := N₂ * ‖y‖) (mul_nonneg hN₂0 (norm_nonneg y))
      (fun y' hy' => hd0 _ (hSV ⟨hz, hball_sub hy hy'⟩))
      (fun y' hy' c => by
        rw [Real.norm_eq_abs]
        have h1 := hB0 z hz y' (hball_sub hy hy') c
        have h2 : ‖y'‖ ≤ ‖y‖ := by simpa using hy'
        calc |D1 (z, y') (0, c)| ≤ N₂ * ‖c‖ * ‖y'‖ := h1
          _ ≤ N₂ * ‖c‖ * ‖y‖ := by gcongr
          _ = N₂ * ‖y‖ * ‖c‖ := by ring) (hyself y)
    rw [hzero z (hKU hz), sub_zero, Real.norm_eq_abs] at h
    calc |E (z, y)| ≤ N₂ * ‖y‖ * ‖y‖ := h
      _ = N₂ * ‖y‖ ^ 2 := by ring
  -- (B2) the mixed blocks
  have hB2 : ∀ z ∈ K, ∀ y ∈ closedBall (0 : Q) ρ', ∀ u v : P × Q, D2 (z, 0) u v = 0 →
      |D2 (z, y) u v| ≤ N₃ * ‖u‖ * ‖v‖ * ‖y‖ := by
    intro z hz y hy u v h0
    have h := norm_sub_le_of_fibre (G := fun x => D2 x u v)
      (G' := fun y' => ((D3 (z, y')).flip u).flip v) (z := z) (r := ρ')
      (B := N₃ * ‖u‖ * ‖v‖) (by positivity)
      (fun y' hy' => hev2 _ (hSV ⟨hz, hy'⟩) u v)
      (fun y' hy' c => by
        simp only [ContinuousLinearMap.flip_apply]
        calc ‖D3 (z, y') (0, c) u v‖ ≤ ‖D3 (z, y')‖ * ‖((0, c) : P × Q)‖ * ‖u‖ * ‖v‖ :=
              norm_apply₃_le _ _ _ _
          _ ≤ N₃ * ‖c‖ * ‖u‖ * ‖v‖ := by
              rw [hpair2]; gcongr; exact hN₃ _ ⟨hz, hy'⟩
          _ = N₃ * ‖u‖ * ‖v‖ * ‖c‖ := by ring) hy
    simpa [h0, Real.norm_eq_abs] using h
  -- (B4') the `y`-derivative of the `zz`-block
  have hB4' : ∀ z ∈ K, ∀ y ∈ closedBall (0 : Q) ρ', ∀ (a : P) (c : Q),
      |D3 (z, y) (0, c) (a, 0) (a, 0)| ≤ N₄ * ‖c‖ * ‖a‖ ^ 2 * ‖y‖ := by
    intro z hz y hy a c
    have h := norm_sub_le_of_fibre (G := fun x => D3 x (0, c) (a, 0) (a, 0))
      (G' := fun y' => (((D4 (z, y')).flip (0, c)).flip (a, 0)).flip (a, 0)) (z := z)
      (r := ρ') (B := N₄ * ‖c‖ * ‖a‖ ^ 2) (by positivity)
      (fun y' hy' => hev3 _ (hSV ⟨hz, hy'⟩) (0, c) (a, 0) (a, 0))
      (fun y' hy' c' => by
        simp only [ContinuousLinearMap.flip_apply]
        calc ‖D4 (z, y') (0, c') (0, c) (a, 0) (a, 0)‖ ≤
              ‖D4 (z, y')‖ * ‖((0, c') : P × Q)‖ * ‖((0, c) : P × Q)‖ * ‖((a, 0) : P × Q)‖ *
                ‖((a, 0) : P × Q)‖ := norm_apply₄_le _ _ _ _ _
          _ ≤ N₄ * ‖c'‖ * ‖c‖ * ‖a‖ * ‖a‖ := by
              rw [hpair2, hpair2, hpair1]; gcongr; exact hN₄ _ ⟨hz, hy'⟩
          _ = N₄ * ‖c‖ * ‖a‖ ^ 2 * ‖c'‖ := by ring) hy
    simpa [hz3 z (hKU hz) a c, Real.norm_eq_abs] using h
  -- (B4) the `zz`-block
  have hB4 : ∀ z ∈ K, ∀ y ∈ closedBall (0 : Q) ρ', ∀ a : P,
      |D2 (z, y) (a, 0) (a, 0)| ≤ N₄ * ‖a‖ ^ 2 * ‖y‖ ^ 2 := by
    intro z hz y hy a
    have h := norm_sub_le_of_fibre (G := fun x => D2 x (a, 0) (a, 0))
      (G' := fun y' => ((D3 (z, y')).flip (a, 0)).flip (a, 0)) (z := z) (r := ‖y‖)
      (B := N₄ * ‖a‖ ^ 2 * ‖y‖) (by positivity)
      (fun y' hy' => hev2 _ (hSV ⟨hz, hball_sub hy hy'⟩) (a, 0) (a, 0))
      (fun y' hy' c => by
        simp only [ContinuousLinearMap.flip_apply]
        rw [Real.norm_eq_abs]
        have h1 := hB4' z hz y' (hball_sub hy hy') a c
        have h2 : ‖y'‖ ≤ ‖y‖ := by simpa using hy'
        calc |D3 (z, y') (0, c) (a, 0) (a, 0)| ≤ N₄ * ‖c‖ * ‖a‖ ^ 2 * ‖y'‖ := h1
          _ ≤ N₄ * ‖c‖ * ‖a‖ ^ 2 * ‖y‖ := by gcongr
          _ = N₄ * ‖a‖ ^ 2 * ‖y‖ * ‖c‖ := by ring) (hyself y)
    simp only [hz2 z (hKU hz) a a, sub_zero, Real.norm_eq_abs] at h
    calc |D2 (z, y) (a, 0) (a, 0)| ≤ N₄ * ‖a‖ ^ 2 * ‖y‖ * ‖y‖ := h
      _ = N₄ * ‖a‖ ^ 2 * ‖y‖ ^ 2 := by ring
  -- assembly
  refine ⟨N₂ + 2 * N₃ + N₄, by positivity, fun z hz y hy => ⟨?_, ?_, ?_⟩⟩
  · have h := hB1 z hz y hy
    have : N₂ * ‖y‖ ^ 2 ≤ (N₂ + 2 * N₃ + N₄) * ‖y‖ ^ 2 := by
      gcongr; linarith
    linarith
  · intro b
    have h := hB0 z hz y hy b
    have : N₂ * ‖b‖ * ‖y‖ ≤ (N₂ + 2 * N₃ + N₄) * ‖y‖ * ‖b‖ := by
      rw [mul_right_comm]; gcongr; linarith
    linarith
  · intro a b
    have hsplit : D2 (z, y) (a, b) (a, b) = D2 (z, y) (a, 0) (a, 0) + D2 (z, y) (a, 0) (0, b) +
        D2 (z, y) (0, b) (a, 0) + D2 (z, y) (0, b) (0, b) := by
      have e : ((a, b) : P × Q) = (a, 0) + (0, b) := by simp
      rw [e]
      simp only [map_add, ContinuousLinearMap.add_apply]
      ring
    have h1 := hB4 z hz y hy a
    have h2 := hB2 z hz y hy (a, 0) (0, b) (hy2 z (hKU hz) a b).1
    have h3 := hB2 z hz y hy (0, b) (a, 0) (hy2 z (hKU hz) a b).2
    have h4 : |D2 (z, y) (0, b) (0, b)| ≤ N₂ * ‖b‖ ^ 2 := by
      calc |D2 (z, y) (0, b) (0, b)| = ‖D2 (z, y) (0, b) (0, b)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖D2 (z, y)‖ * ‖((0, b) : P × Q)‖ * ‖((0, b) : P × Q)‖ := norm_apply₂_le _ _ _
        _ ≤ N₂ * ‖b‖ * ‖b‖ := by rw [hpair2]; gcongr; exact hN₂ _ ⟨hz, hy⟩
        _ = N₂ * ‖b‖ ^ 2 := by ring
    rw [hpair1, hpair2] at h2 h3
    rw [hsplit]
    have hT1 : 0 ≤ ‖y‖ ^ 2 * ‖a‖ ^ 2 := by positivity
    have hT2 : 0 ≤ ‖y‖ * ‖a‖ * ‖b‖ := by positivity
    have hT3 : 0 ≤ ‖b‖ ^ 2 := by positivity
    have habs := abs_add_four_le (D2 (z, y) (a, 0) (a, 0)) (D2 (z, y) (a, 0) (0, b))
      (D2 (z, y) (0, b) (a, 0)) (D2 (z, y) (0, b) (0, b))
    have e : (N₂ + 2 * N₃ + N₄) * (‖y‖ ^ 2 * ‖a‖ ^ 2 + ‖y‖ * ‖a‖ * ‖b‖ + ‖b‖ ^ 2) -
        (N₄ * ‖a‖ ^ 2 * ‖y‖ ^ 2 + N₃ * ‖a‖ * ‖b‖ * ‖y‖ + N₃ * ‖b‖ * ‖a‖ * ‖y‖ + N₂ * ‖b‖ ^ 2) =
        N₂ * (‖y‖ ^ 2 * ‖a‖ ^ 2 + ‖y‖ * ‖a‖ * ‖b‖) + 2 * N₃ * (‖y‖ ^ 2 * ‖a‖ ^ 2 + ‖b‖ ^ 2) +
          N₄ * (‖y‖ * ‖a‖ * ‖b‖ + ‖b‖ ^ 2) := by ring
    have hpos : 0 ≤ N₂ * (‖y‖ ^ 2 * ‖a‖ ^ 2 + ‖y‖ * ‖a‖ * ‖b‖) +
        2 * N₃ * (‖y‖ ^ 2 * ‖a‖ ^ 2 + ‖b‖ ^ 2) + N₄ * (‖y‖ * ‖a‖ * ‖b‖ + ‖b‖ ^ 2) := by
      positivity
    linarith

end Main

end SGPT.NPP.DN10
