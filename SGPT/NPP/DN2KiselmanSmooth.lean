import SGPT.NPP.DN2KiselmanCalculus
import SGPT.NPP.DN2KiselmanOneDim
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The penalized minimum of FPT `lem:varying-log-radius-minimum` is smooth, with Levi bound

Lane DN2, `thm:DNT23_C11bar`; FPT `lem:varying-log-radius-minimum`
(`chapters/inputs/q10-big-envelope-regularity.tex`, lines 368–413).

Data (`VaryingEndpointData`, all in a domain `D ⊆ ℂⁿ`): a smooth `H(z, s)` on an open set
containing `{s ≤ b(z)}`, with `H_s ≥ 0`, `H_ss > 0`, `H` locally uniformly bounded below, and a
joint Levi bound `(z, ζ) ↦ H(z, Re ζ)` psh-ish at the points with `s ≤ b(z)`, `H_s ≤ c`; smooth
`b` and `Q` with `ddᶜQ ≥ 0` and `ddᶜb ≤ ddᶜQ`.  (FPT's lower bound `-π_D^*Λ` and its
`C_b ω̂` are absorbed in `H` and `Q` through local potentials.)

For `0 < ε ≤ c/4` the penalized minimizer `s_ε(z)` of `H(z, s) - c s - ε log(b(z) - s)` is unique
and smooth (implicit function theorem), and the minimum value `v_ε` satisfies
`ddᶜ(v_ε + c Q) ≥ 0` (FPT: the barrier contributes `≥ -σ ddᶜb` with `σ = ε/(b - s) ≤ c`, and the
Schur complement identity `leviForm_graph_eq_joint`).

## Main results

* `VaryingEndpointData.penMin_spec`, `VaryingEndpointData.contDiffAt_penMin`;
* `VaryingEndpointData.contDiffOn_penValue`;
* `VaryingEndpointData.leviForm_penValue_add_nonneg`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace SGPT.NPP.DN2

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {n : ℕ}

/-- **The data of FPT `lem:varying-log-radius-minimum`** in potential form. -/
structure VaryingEndpointData (D : Set (ComplexModel n)) (O : Set (ComplexModel n × ℝ))
    (H : ComplexModel n × ℝ → ℝ) (b Q : ComplexModel n → ℝ) (c : ℝ) : Prop where
  isOpen_D : IsOpen D
  isOpen_O : IsOpen O
  mem_O : ∀ z ∈ D, ∀ s ≤ b z, (z, s) ∈ O
  smooth_H : ContDiffOn ℝ ∞ H O
  smooth_b : ContDiffOn ℝ ∞ b D
  smooth_Q : ContDiffOn ℝ ∞ Q D
  c_pos : 0 < c
  deriv_nonneg : ∀ z ∈ D, ∀ s ≤ b z, 0 ≤ deriv (fun t => H (z, t)) s
  deriv2_pos : ∀ z ∈ D, ∀ s ≤ b z, 0 < deriv (deriv (fun t => H (z, t))) s
  lower : ∀ z ∈ D, ∃ V ∈ 𝓝 z, ∃ m : ℝ, ∀ y ∈ V, y ∈ D → ∀ s ≤ b y, m ≤ H (y, s)
  levi : ∀ z ∈ D, ∀ s ≤ b z, deriv (fun t => H (z, t)) s ≤ c → ∀ (v : ComplexModel n) (η : ℂ),
    0 ≤ leviForm (fun p : ComplexModel n × ℂ => H (p.1, p.2.re)) (z, (s : ℂ)) (v, η)
  levi_Q : ∀ z ∈ D, ∀ v, 0 ≤ leviForm Q z v
  levi_b : ∀ z ∈ D, ∀ v, leviForm b z v ≤ leviForm Q z v

open Classical in
/-- The penalized minimizer (the unique zero of the derivative of the penalized function). -/
def penMin (H : ComplexModel n × ℝ → ℝ) (b : ComplexModel n → ℝ) (c ε : ℝ)
    (z : ComplexModel n) : ℝ :=
  if h : ∃ s, s < b z ∧ penaltyDeriv (fun t => H (z, t)) (b z) c ε s = 0 then h.choose
  else b z - 1

/-- The penalized minimum value. -/
def penValue (H : ComplexModel n × ℝ → ℝ) (b : ComplexModel n → ℝ) (c ε : ℝ)
    (z : ComplexModel n) : ℝ :=
  penalty (fun t => H (z, t)) (b z) c ε (penMin H b c ε z)

/-- A partial derivative in the last variable is a directional Fréchet derivative. -/
theorem deriv_slice_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E × ℝ → ℝ}
    {z : E} {s : ℝ} (hF : DifferentiableAt ℝ F (z, s)) :
    deriv (fun t => F (z, t)) s = fderiv ℝ F (z, s) ((0 : E), (1 : ℝ)) := by
  have hγ : HasDerivAt (fun t : ℝ => ((z, t) : E × ℝ)) ((0 : E), (1 : ℝ)) s :=
    (hasDerivAt_const s z).prodMk (hasDerivAt_id s)
  exact (hF.hasFDerivAt.comp_hasDerivAt s hγ).deriv

/-- A continuous linear functional has vanishing second derivative. -/
theorem realHessian_clm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : F →L[ℝ] ℝ) (x v w : F) : realHessian (fun p => L p) x v w = 0 := by
  have h : fderiv ℝ (fun p => L p) = fun _ => L := by
    funext p; exact L.fderiv
  rw [realHessian_eq_fderiv, h]
  simp

theorem two_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl 2

namespace VaryingEndpointData

variable {D : Set (ComplexModel n)} {O : Set (ComplexModel n × ℝ)} {H : ComplexModel n × ℝ → ℝ}
  {b Q : ComplexModel n → ℝ} {c : ℝ}

theorem contDiffAt_H (P : VaryingEndpointData D O H b Q c) {p : ComplexModel n × ℝ}
    (hp : p ∈ O) : ContDiffAt ℝ ∞ H p :=
  P.smooth_H.contDiffAt (P.isOpen_O.mem_nhds hp)

theorem contDiffAt_slice (P : VaryingEndpointData D O H b Q c) {z : ComplexModel n} {s : ℝ}
    (hzs : (z, s) ∈ O) : ContDiffAt ℝ ∞ (fun t => H (z, t)) s :=
  (P.contDiffAt_H hzs).comp s (contDiffAt_const.prodMk contDiffAt_id)

theorem differentiableAt_deriv_slice (P : VaryingEndpointData D O H b Q c) {z : ComplexModel n}
    {s : ℝ} (hzs : (z, s) ∈ O) : DifferentiableAt ℝ (deriv fun t => H (z, t)) s := by
  have hopen : IsOpen {t : ℝ | (z, t) ∈ O} :=
    P.isOpen_O.preimage (continuous_const.prodMk continuous_id)
  have hcd : ContDiffOn ℝ ∞ (fun t => H (z, t)) {t : ℝ | (z, t) ∈ O} :=
    P.smooth_H.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun t ht => ht
  have hd : ContDiffOn ℝ ∞ (deriv fun t => H (z, t)) {t : ℝ | (z, t) ∈ O} :=
    hcd.deriv_of_isOpen hopen (by simp)
  exact (hd.contDiffAt (hopen.mem_nhds hzs)).differentiableAt (by simp)

/-- On each fibre the hypotheses of `LogRadiusProfile` hold. -/
theorem exists_profile (P : VaryingEndpointData D O H b Q c) {z : ComplexModel n} (hz : z ∈ D) :
    ∃ m, LogRadiusProfile (fun t => H (z, t)) (b z) c m := by
  obtain ⟨V, hV, m, hm⟩ := P.lower z hz
  exact ⟨m, ⟨P.c_pos, fun s hs => (P.contDiffAt_slice (P.mem_O z hz s hs)).differentiableAt
    (by simp), fun s hs => P.differentiableAt_deriv_slice (P.mem_O z hz s hs),
    P.deriv_nonneg z hz, P.deriv2_pos z hz, fun s hs => hm z (mem_of_mem_nhds hV) hz s hs⟩⟩

theorem penMin_spec (P : VaryingEndpointData D O H b Q c) {z : ComplexModel n} (hz : z ∈ D)
    {ε : ℝ} (hε : 0 < ε) (hεc : ε ≤ c / 4) :
    penMin H b c ε z < b z ∧
      penaltyDeriv (fun t => H (z, t)) (b z) c ε (penMin H b c ε z) = 0 := by
  obtain ⟨m, Pz⟩ := P.exists_profile hz
  have hex := Pz.exists_penaltyDeriv_eq_zero hε hεc
  have hex' : ∃ s, s < b z ∧ penaltyDeriv (fun t => H (z, t)) (b z) c ε s = 0 := by
    obtain ⟨s, hs, h0⟩ := hex; exact ⟨s, hs, h0⟩
  unfold penMin
  rw [dif_pos hex']
  exact hex'.choose_spec

theorem eq_penMin (P : VaryingEndpointData D O H b Q c) {z : ComplexModel n} (hz : z ∈ D)
    {ε : ℝ} (hε : 0 < ε) (hεc : ε ≤ c / 4) {s : ℝ} (hs : s < b z)
    (h0 : penaltyDeriv (fun t => H (z, t)) (b z) c ε s = 0) : s = penMin H b c ε z := by
  obtain ⟨m, Pz⟩ := P.exists_profile hz
  obtain ⟨h1, h2⟩ := P.penMin_spec hz hε hεc
  exact Pz.penaltyDeriv_injOn hε.le (mem_Iio.mpr hs) (mem_Iio.mpr h1) (h0.trans h2.symm)

/-- The penalized minimizer realizes the minimum on `s < b(z)`. -/
theorem isMinOn_penValue (P : VaryingEndpointData D O H b Q c) {z : ComplexModel n}
    (hz : z ∈ D) {ε : ℝ} (hε : 0 < ε) (hεc : ε ≤ c / 4) :
    IsMinOn (penalty (fun t => H (z, t)) (b z) c ε) (Iio (b z)) (penMin H b c ε z) := by
  obtain ⟨m, Pz⟩ := P.exists_profile hz
  obtain ⟨h1, h2⟩ := P.penMin_spec hz hε hεc
  exact Pz.isMinOn_penalty hε.le h1 h2

/-! ### The implicit equation -/

/-- The derivative of the penalized function as a function of `(z, s)`. -/
def critFun (H : ComplexModel n × ℝ → ℝ) (b : ComplexModel n → ℝ) (c ε : ℝ)
    (p : ComplexModel n × ℝ) : ℝ :=
  fderiv ℝ H p ((0 : ComplexModel n), (1 : ℝ)) - c + ε / (b p.1 - p.2)

theorem critFun_eq (P : VaryingEndpointData D O H b Q c) {z : ComplexModel n} {s ε : ℝ}
    (hzs : (z, s) ∈ O) :
    critFun H b c ε (z, s) = penaltyDeriv (fun t => H (z, t)) (b z) c ε s := by
  unfold critFun penaltyDeriv
  rw [deriv_slice_eq ((P.contDiffAt_H hzs).differentiableAt (by simp))]

theorem contDiffAt_critFun (P : VaryingEndpointData D O H b Q c) {z : ComplexModel n} {s ε : ℝ}
    (hz : z ∈ D) (hzs : (z, s) ∈ O) (hsb : s < b z) :
    ContDiffAt ℝ ∞ (critFun H b c ε) (z, s) := by
  have h1 : ContDiffAt ℝ ∞ (fderiv ℝ H) (z, s) :=
    (P.smooth_H.fderiv_of_isOpen P.isOpen_O (by simp)).contDiffAt (P.isOpen_O.mem_nhds hzs)
  have h2 : ContDiffAt ℝ ∞ (fun p : ComplexModel n × ℝ => fderiv ℝ H p ((0 : ComplexModel n),
      (1 : ℝ))) (z, s) := h1.clm_apply contDiffAt_const
  have hb : ContDiffAt ℝ ∞ (fun p : ComplexModel n × ℝ => b p.1) (z, s) :=
    (P.smooth_b.contDiffAt (P.isOpen_D.mem_nhds hz)).comp (z, s) contDiffAt_fst
  have h3 : ContDiffAt ℝ ∞ (fun p : ComplexModel n × ℝ => ε / (b p.1 - p.2)) (z, s) :=
    contDiffAt_const.div (hb.sub contDiffAt_snd) (sub_pos.mpr hsb).ne'
  exact (h2.sub contDiffAt_const).add h3

/-- The slope of `critFun` in `s` is positive at the penalized minimizer. -/
theorem fderiv_critFun_inr_ne_zero (P : VaryingEndpointData D O H b Q c) {z : ComplexModel n}
    {s ε : ℝ} (hz : z ∈ D) (hε : 0 ≤ ε) (hsb : s < b z) :
    fderiv ℝ (critFun H b c ε) (z, s) ((0 : ComplexModel n), (1 : ℝ)) ≠ 0 := by
  have hzs := P.mem_O z hz s hsb.le
  have hdiff : DifferentiableAt ℝ (critFun H b c ε) (z, s) :=
    (P.contDiffAt_critFun hz hzs hsb).differentiableAt (by simp)
  rw [← deriv_slice_eq hdiff]
  -- near `s`, the slice of `critFun` is the explicit penalized derivative
  have hopen : IsOpen {t : ℝ | (z, t) ∈ O ∧ t < b z} :=
    (P.isOpen_O.preimage (continuous_const.prodMk continuous_id)).inter isOpen_Iio
  have hev : (fun t => critFun H b c ε (z, t)) =ᶠ[𝓝 s]
      fun t => deriv (fun t => H (z, t)) t - c + ε / (b z - t) := by
    filter_upwards [hopen.mem_nhds ⟨hzs, hsb⟩] with t ht
    rw [P.critFun_eq ht.1]; rfl
  have hd1 : HasDerivAt (deriv fun t => H (z, t))
      (deriv (deriv fun t => H (z, t)) s) s := (P.differentiableAt_deriv_slice hzs).hasDerivAt
  have hbs : b z - s ≠ 0 := (sub_pos.mpr hsb).ne'
  have hd2 : HasDerivAt (fun t => ε / (b z - t)) ((0 * (b z - s) - ε * (-1)) / (b z - s) ^ 2) s :=
    (hasDerivAt_const s ε).div ((hasDerivAt_id' s).const_sub (b z)) hbs
  have hd : HasDerivAt (fun t => deriv (fun t => H (z, t)) t - c + ε / (b z - t))
      (deriv (deriv fun t => H (z, t)) s + (0 * (b z - s) - ε * (-1)) / (b z - s) ^ 2) s :=
    (hd1.sub_const c).add hd2
  rw [hev.deriv_eq, hd.deriv]
  have hpos := P.deriv2_pos z hz s hsb.le
  have : 0 ≤ (0 * (b z - s) - ε * (-1)) / (b z - s) ^ 2 :=
    div_nonneg (by linarith) (sq_nonneg _)
  linarith

/-- A nonzero continuous linear map `ℝ → ℝ` is invertible. -/
theorem isInvertible_of_apply_one_ne_zero (L : ℝ →L[ℝ] ℝ) (hL : L 1 ≠ 0) : L.IsInvertible := by
  refine ContinuousLinearMap.IsInvertible.of_inverse (g := (L 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    ?_ ?_
  · ext
    change L ((L 1)⁻¹ • (1 : ℝ)) = 1
    rw [L.map_smul, smul_eq_mul, inv_mul_cancel₀ hL]
  · ext
    change (L 1)⁻¹ • L 1 = 1
    rw [smul_eq_mul, inv_mul_cancel₀ hL]

/-- **The penalized minimizer is smooth** (implicit function theorem). -/
theorem contDiffAt_penMin (P : VaryingEndpointData D O H b Q c) {z₀ : ComplexModel n}
    (hz₀ : z₀ ∈ D) {ε : ℝ} (hε : 0 < ε) (hεc : ε ≤ c / 4) :
    ContDiffAt ℝ ∞ (penMin H b c ε) z₀ := by
  obtain ⟨hlt, hcrit⟩ := P.penMin_spec hz₀ hε hεc
  set s₀ := penMin H b c ε z₀ with hs₀
  have hzs : (z₀, s₀) ∈ O := P.mem_O z₀ hz₀ s₀ hlt.le
  have cdf : ContDiffAt ℝ ∞ (critFun H b c ε) (z₀, s₀) := P.contDiffAt_critFun hz₀ hzs hlt
  have hinv : (fderiv ℝ (critFun H b c ε) (z₀, s₀) ∘L
      ContinuousLinearMap.inr ℝ (ComplexModel n) ℝ).IsInvertible := by
    apply isInvertible_of_apply_one_ne_zero
    simpa using P.fderiv_critFun_inr_ne_zero hz₀ hε.le hlt
  set ψ := cdf.implicitFunction (by simp) hinv with hψ
  have hψ₀ : ψ z₀ = s₀ := cdf.implicitFunction_apply_self (by simp) hinv
  have hψc : ContDiffAt ℝ ∞ ψ z₀ := cdf.contDiffAt_implicitFunction (by simp) hinv
  have hψeq : ∀ᶠ z in 𝓝 z₀, critFun H b c ε (z, ψ z) = critFun H b c ε (z₀, s₀) :=
    cdf.eventually_apply_implicitFunction (by simp) hinv
  have hbcont : ContinuousAt b z₀ :=
    (P.smooth_b.contDiffAt (P.isOpen_D.mem_nhds hz₀)).continuousAt
  have hlt' : ∀ᶠ z in 𝓝 z₀, ψ z < b z := by
    have := (hψc.continuousAt.sub hbcont).eventually
      (Iio_mem_nhds (show (ψ - b) z₀ < 0 by simp only [Pi.sub_apply, hψ₀]; linarith))
    filter_upwards [this] with z hz
    simp only [Pi.sub_apply] at hz
    linarith
  have hD : ∀ᶠ z in 𝓝 z₀, z ∈ D := P.isOpen_D.mem_nhds hz₀
  have heq : penMin H b c ε =ᶠ[𝓝 z₀] ψ := by
    filter_upwards [hψeq, hlt', hD] with z hz hzb hzD
    have hzO : (z, ψ z) ∈ O := P.mem_O z hzD (ψ z) hzb.le
    have h0 : penaltyDeriv (fun t => H (z, t)) (b z) c ε (ψ z) = 0 := by
      rw [← P.critFun_eq hzO, hz, P.critFun_eq hzs]; exact hcrit
    exact (P.eq_penMin hzD hε hεc hzb h0).symm
  exact hψc.congr_of_eventuallyEq heq

/-! ### The penalized value function -/

/-- The function `K(z, s) = H(z, s) - c s - ε log(b(z) - s) + c Q(z)`. -/
def penJoint (H : ComplexModel n × ℝ → ℝ) (b Q : ComplexModel n → ℝ) (c ε : ℝ)
    (p : ComplexModel n × ℝ) : ℝ :=
  H p - c * p.2 - ε * Real.log (b p.1 - p.2) + c * Q p.1

theorem contDiffAt_penJoint (P : VaryingEndpointData D O H b Q c) {z : ComplexModel n} {s ε : ℝ}
    (hz : z ∈ D) (hsb : s < b z) : ContDiffAt ℝ ∞ (penJoint H b Q c ε) (z, s) := by
  have hzs := P.mem_O z hz s hsb.le
  have hb : ContDiffAt ℝ ∞ (fun p : ComplexModel n × ℝ => b p.1) (z, s) :=
    (P.smooth_b.contDiffAt (P.isOpen_D.mem_nhds hz)).comp (z, s) contDiffAt_fst
  have hQ : ContDiffAt ℝ ∞ (fun p : ComplexModel n × ℝ => Q p.1) (z, s) :=
    (P.smooth_Q.contDiffAt (P.isOpen_D.mem_nhds hz)).comp (z, s) contDiffAt_fst
  have hlog : ContDiffAt ℝ ∞ (fun p : ComplexModel n × ℝ => Real.log (b p.1 - p.2)) (z, s) :=
    (hb.sub contDiffAt_snd).log (sub_pos.mpr hsb).ne'
  exact (((P.contDiffAt_H hzs).sub (contDiffAt_const.mul contDiffAt_snd)).sub
    (contDiffAt_const.mul hlog)).add (contDiffAt_const.mul hQ)

theorem penValue_add_eq (H : ComplexModel n × ℝ → ℝ) (b Q : ComplexModel n → ℝ) (c ε : ℝ)
    (z : ComplexModel n) :
    penValue H b c ε z + c * Q z = penJoint H b Q c ε (z, penMin H b c ε z) := by
  simp [penValue, penalty, penJoint]

theorem contDiffOn_penValue (P : VaryingEndpointData D O H b Q c) {ε : ℝ} (hε : 0 < ε)
    (hεc : ε ≤ c / 4) : ContDiffOn ℝ ∞ (penValue H b c ε) D := by
  intro z hz
  have hm := P.contDiffAt_penMin hz hε hεc
  have hlt := (P.penMin_spec hz hε hεc).1
  have hK : ContDiffAt ℝ ∞ (fun y => penJoint H b Q c ε (y, penMin H b c ε y)) z := by
    have := (P.contDiffAt_penJoint (ε := ε) hz hlt).comp z (contDiffAt_id.prodMk hm)
    simpa only [Function.comp_def, id] using this
  have hQ : ContDiffAt ℝ ∞ (fun y => c * Q y) z :=
    contDiffAt_const.mul (P.smooth_Q.contDiffAt (P.isOpen_D.mem_nhds hz))
  have : (penValue H b c ε) = fun y => penJoint H b Q c ε (y, penMin H b c ε y) - c * Q y := by
    funext y; rw [← penValue_add_eq]; ring
  rw [this]
  exact (hK.sub hQ).contDiffWithinAt

/-! ### The Levi bound -/

/-- The joint Levi form of `(z, ζ) ↦ K(z, Re ζ)` is nonnegative at the penalized minimizer. -/
theorem leviForm_penJoint_nonneg (P : VaryingEndpointData D O H b Q c) {z : ComplexModel n}
    (hz : z ∈ D) {ε : ℝ} (hε : 0 < ε) (hεc : ε ≤ c / 4) (v : ComplexModel n) (η : ℂ) :
    0 ≤ leviForm (fun p : ComplexModel n × ℂ => penJoint H b Q c ε (p.1, p.2.re))
      (z, (penMin H b c ε z : ℂ)) (v, η) := by
  obtain ⟨hlt, hcrit⟩ := P.penMin_spec hz hε hεc
  set s := penMin H b c ε z with hs
  have hzs := P.mem_O z hz s hlt.le
  set φ := b z - s with hφ
  have hφpos : 0 < φ := sub_pos.mpr hlt
  -- the slope at the minimizer
  have hHs : deriv (fun t => H (z, t)) s = c - ε / φ := by
    unfold penaltyDeriv at hcrit; rw [hφ]; linarith
  have hσ : ε / φ ≤ c := by have := P.deriv_nonneg z hz s hlt.le; linarith
  -- the four pieces, as functions on `ℂⁿ × ℂ`
  set p₀ : ComplexModel n × ℂ := (z, (s : ℂ)) with hp₀
  set gH : ComplexModel n × ℂ → ℝ := fun p => H (p.1, p.2.re) with hgH
  set gl : ComplexModel n × ℂ → ℝ := fun p => -c * p.2.re with hgl
  set gφ : ComplexModel n × ℂ → ℝ := fun p => b p.1 - p.2.re with hgφ
  set θ : ℝ → ℝ := fun t => -ε * Real.log t with hθ
  set gb : ComplexModel n × ℂ → ℝ := fun p => θ (gφ p) with hgb
  set gQ : ComplexModel n × ℂ → ℝ := fun p => c * Q p.1 with hgQ
  have hsplit : (fun p : ComplexModel n × ℂ => penJoint H b Q c ε (p.1, p.2.re)) =
      gH + gl + gb + gQ := by
    funext p
    simp only [penJoint, Pi.add_apply, hgH, hgl, hgb, hgQ, hθ, hgφ]
    ring
  -- smoothness of the pieces at `p₀`
  have hre : ContDiff ℝ ∞ (fun p : ComplexModel n × ℂ => p.2.re) :=
    Complex.reCLM.contDiff.comp contDiff_snd
  have hbz : ContDiffAt ℝ ∞ b z := P.smooth_b.contDiffAt (P.isOpen_D.mem_nhds hz)
  have hQz : ContDiffAt ℝ ∞ Q z := P.smooth_Q.contDiffAt (P.isOpen_D.mem_nhds hz)
  have hgH2 : ContDiffAt ℝ 2 gH p₀ := by
    have : ContDiffAt ℝ ∞ H (reProd p₀) := by simpa [hp₀] using P.contDiffAt_H hzs
    exact (this.comp p₀ (reProd (E := ComplexModel n)).contDiff.contDiffAt).of_le two_le_infty
  have hgl2 : ContDiffAt ℝ 2 gl p₀ :=
    (contDiffAt_const.mul hre.contDiffAt).of_le two_le_infty
  have hgφ2 : ContDiffAt ℝ ∞ gφ p₀ :=
    (hbz.comp p₀ contDiffAt_fst).sub hre.contDiffAt
  have hφval : gφ p₀ = φ := by simp [hgφ, hp₀, hφ]
  have hθ2 : ContDiffAt ℝ ∞ θ (gφ p₀) := by
    rw [hφval]
    exact contDiffAt_const.mul (Real.contDiffAt_log.mpr hφpos.ne')
  have hgb2 : ContDiffAt ℝ 2 gb p₀ := (hθ2.comp p₀ hgφ2).of_le two_le_infty
  have hgQ2 : ContDiffAt ℝ 2 gQ p₀ :=
    (contDiffAt_const.mul (hQz.comp p₀ contDiffAt_fst)).of_le two_le_infty
  have h12 : ContDiffAt ℝ 2 (gH + gl) p₀ := hgH2.add hgl2
  have h123 : ContDiffAt ℝ 2 (gH + gl + gb) p₀ := h12.add hgb2
  rw [hsplit, leviForm_add h123 hgQ2, leviForm_add h12 hgb2, leviForm_add hgH2 hgl2]
  -- piece by piece
  have hσ0' : 0 ≤ ε / φ := by positivity
  have hHc : deriv (fun t => H (z, t)) s ≤ c := by rw [hHs]; linarith
  have hLH : 0 ≤ leviForm gH p₀ (v, η) := P.levi z hz s hlt.le hHc v η
  have hLl : leviForm gl p₀ (v, η) = 0 := by
    have : gl = fun p => ((-c) • (Complex.reCLM.comp
        (ContinuousLinearMap.snd ℝ (ComplexModel n) ℂ))) p := by
      funext p; simp [hgl]
    simp only [leviForm, this, realHessian_clm, add_zero, zero_div]
  have hLQ : leviForm gQ p₀ (v, η) = c * leviForm Q z v := by
    have h := realHessian_comp_clm (ContinuousLinearMap.fst ℝ (ComplexModel n) ℂ)
      (u := fun x => c * Q x) (p := p₀) (by
        simpa [hp₀] using (contDiffAt_const.mul hQz).of_le two_le_infty)
    have hQ2 : ContDiffAt ℝ 2 Q z := hQz.of_le two_le_infty
    have hQs : leviForm (fun x => c * Q x) z v = c * leviForm Q z v :=
      leviForm_smul hQ2 c v
    unfold leviForm at hQs ⊢
    rw [show gQ = fun q => (fun x => c * Q x) ((ContinuousLinearMap.fst ℝ (ComplexModel n) ℂ) q)
      from rfl, h, h]
    simpa [hp₀, Prod.smul_mk] using hQs
  have hLφ : leviForm gφ p₀ (v, η) = leviForm b z v := by
    have hfst := realHessian_comp_clm (ContinuousLinearMap.fst ℝ (ComplexModel n) ℂ)
      (u := b) (p := p₀) (by simpa [hp₀] using hbz.of_le two_le_infty)
    have hsub : gφ = (fun q => b ((ContinuousLinearMap.fst ℝ (ComplexModel n) ℂ) q)) +
        (fun q => ((-1 : ℝ) • (Complex.reCLM.comp
          (ContinuousLinearMap.snd ℝ (ComplexModel n) ℂ))) q) := by
      funext q; simp [hgφ, sub_eq_add_neg]
    have hb2 : ContDiffAt ℝ 2 (fun q => b ((ContinuousLinearMap.fst ℝ (ComplexModel n) ℂ) q))
        p₀ := ((hbz.comp p₀ contDiffAt_fst).of_le two_le_infty)
    have hl2 : ContDiffAt ℝ 2 (fun q => ((-1 : ℝ) • (Complex.reCLM.comp
          (ContinuousLinearMap.snd ℝ (ComplexModel n) ℂ))) q) p₀ :=
      ContinuousLinearMap.contDiff _ |>.contDiffAt
    rw [hsub, leviForm_add hb2 hl2]
    simp only [leviForm, realHessian_clm, hfst, add_zero, zero_div]
    simp [hp₀, Prod.smul_mk]
  have hLb : -(ε / φ) * leviForm b z v ≤ leviForm gb p₀ (v, η) := by
    have hθd : deriv θ (gφ p₀) = -(ε / φ) := by
      rw [hφval, hθ]
      have := ((Real.hasDerivAt_log hφpos.ne').const_mul (-ε)).deriv
      rw [this]; field_simp
    have hθdd : 0 ≤ deriv (deriv θ) (gφ p₀) := by
      rw [hφval]
      have hev : deriv θ =ᶠ[𝓝 φ] fun t => -ε * t⁻¹ := by
        filter_upwards [lt_mem_nhds hφpos] with t ht
        rw [hθ]
        exact ((Real.hasDerivAt_log ht.ne').const_mul (-ε)).deriv
      rw [hev.deriv_eq]
      have := ((hasDerivAt_inv hφpos.ne').const_mul (-ε)).deriv
      rw [this]
      have : 0 ≤ ε * (φ ^ 2)⁻¹ := by positivity
      linarith
    have hcomp := SGPT.Foundations.Analysis.Pending.StokesCutoff.realHessian_comp (θ := θ) (f := gφ) (z := p₀)
      (hθ2.of_le two_le_infty) (hgφ2.of_le two_le_infty)
    have hsq : ∀ a : ComplexModel n × ℂ, 0 ≤ deriv (deriv θ) (gφ p₀) *
        (fderiv ℝ gφ p₀ a * fderiv ℝ gφ p₀ a) := fun a =>
      mul_nonneg hθdd (mul_self_nonneg _)
    have hgb_eq : leviForm gb p₀ (v, η) ≥ deriv θ (gφ p₀) * leviForm gφ p₀ (v, η) := by
      unfold leviForm
      rw [show gb = fun y => θ (gφ y) from rfl, hcomp, hcomp]
      have h1 := hsq (v, η)
      have h2 := hsq (Complex.I • (v, η))
      nlinarith
    rw [hθd, hLφ] at hgb_eq
    linarith
  have hQnn := P.levi_Q z hz v
  have hbQ := P.levi_b z hz v
  have hσ0 : 0 ≤ ε / φ := by positivity
  have hkey : -(ε / φ) * leviForm b z v ≥ -(ε / φ) * leviForm Q z v :=
    by nlinarith
  rw [hLl, hLQ]
  nlinarith

/-- **`ddᶜ(v_ε + c Q) ≥ 0`** at every point of `D`. -/
theorem leviForm_penValue_add_nonneg (P : VaryingEndpointData D O H b Q c) {z₀ : ComplexModel n}
    (hz₀ : z₀ ∈ D) {ε : ℝ} (hε : 0 < ε) (hεc : ε ≤ c / 4) (v : ComplexModel n) :
    0 ≤ leviForm (fun z => penValue H b c ε z + c * Q z) z₀ v := by
  obtain ⟨hlt, hcrit⟩ := P.penMin_spec hz₀ hε hεc
  have hfun : (fun z => penValue H b c ε z + c * Q z) =
      fun z => penJoint H b Q c ε (z, penMin H b c ε z) := by
    funext z; exact penValue_add_eq H b Q c ε z
  have hK2 : ContDiffAt ℝ 2 (penJoint H b Q c ε) (z₀, penMin H b c ε z₀) :=
    (P.contDiffAt_penJoint hz₀ hlt).of_le two_le_infty
  have hD : ∀ᶠ z in 𝓝 z₀, z ∈ D := P.isOpen_D.mem_nhds hz₀
  have hσd : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℝ (penMin H b c ε) z := by
    filter_upwards [hD] with z hz
    exact (P.contDiffAt_penMin hz hε hεc).differentiableAt (by simp)
  have hcrit' : ∀ᶠ z in 𝓝 z₀,
      fderiv ℝ (penJoint H b Q c ε) (z, penMin H b c ε z) ((0 : ComplexModel n), (1 : ℝ)) = 0 := by
    filter_upwards [hD] with z hz
    obtain ⟨hlt, hcr⟩ := P.penMin_spec hz hε hεc
    have hdiff : DifferentiableAt ℝ (penJoint H b Q c ε) (z, penMin H b c ε z) :=
      (P.contDiffAt_penJoint hz hlt).differentiableAt (by simp)
    rw [← deriv_slice_eq hdiff]
    obtain ⟨m, Pz⟩ := P.exists_profile hz
    have hpd := Pz.hasDerivAt_penalty ε hlt
    have hslice : (fun t => penJoint H b Q c ε (z, t)) =
        fun t => penalty (fun t => H (z, t)) (b z) c ε t + c * Q z := by
      funext t; simp [penJoint, penalty]
    rw [hslice, (hpd.add_const (c * Q z)).deriv, hcr]
  rw [hfun, leviForm_graph_eq_joint hK2 hσd hcrit']
  exact P.leviForm_penJoint_nonneg hz₀ hε hεc v _

end VaryingEndpointData

end SGPT.NPP.DN2
