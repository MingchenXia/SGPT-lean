import SGPT.PSH.Basic
import SGPT.Toric.ProjectiveLineFubiniStudy
import SGPT.Foundations.Analysis.Pending.HolomorphicPullback
import SGPT.Foundations.Analysis.Pending.ConvexExhaustion
import SGPT.Foundations.Analysis.FirstPass.PshDiscLocalGlobal
import SGPT.Foundations.Analysis.PshAddition

/-!
# Kiselman's principle as printed is false (`prop:Kis`)

Source `prop:Kis` (chapter `chapter_pshfunctions.tex`, Kiselman's principle): *let
`Ω ⊆ ℂᵐ × ℂⁿ` be a pseudoconvex domain such that every slice `Ω_z = {w : (z, w) ∈ Ω}` has the
form `E + iℝⁿ` with `E ⊆ ℝⁿ` a subset; let `φ ∈ PSH(Ω)` be independent of `Im w`, `Ω'` the
projection of `Ω` to `ℂᵐ` and `ψ(z) = inf_{w ∈ Ω_z} φ(z, w)`; then `ψ ≡ -∞` or `ψ ∈ PSH(Ω')`.*

The book refers to Demailly (*Complex analytic and differential geometry*, Ch. I, Thm. (7.5),
after Kiselman 1978), whose slices are **convex** tubes `ω_z + iℝⁿ`; with arbitrary `E` the
statement fails.  Counterexample (`m = n = 1`):

* `Ω = {(z, w) : Re (z e^{-iw}) < 0}`.  Since `z e^{-iw} = e^{Im w} z e^{-i Re w}`, the slice over
  `z ≠ 0` is `E_z + iℝ` with `E_z = {x : cos (arg z - x) < 0}`, a union of infinitely many
  disjoint open intervals; `Ω_0 = ∅`.  `Ω` is connected: it is the image of the convex set
  `{Re a < 0} × ℂ` under the biholomorphism `(a, w) ↦ (a e^{iw}, w)`.  `Ω` is pseudoconvex:
  `u = ‖(z, w)‖² + Im w - log (-Re (z e^{-iw}))` is a continuous psh exhaustion
  (`-log (-Re ζ)` is convex on `{Re ζ < 0}`, composed with the holomorphic `z e^{-iw}`).
* `φ(z, w) = (arg (-z e^{-iw}) + Re w - π)²`.  On `Ω`, `-z e^{-iw}` lies in the right half-plane,
  so `F = Log (-z e^{-iw}) + iw` is holomorphic and `φ = (Im F - π)²` is psh; it only depends on
  `Re w`.  `Im F - π` is an argument of `z`.
* Hence `ψ(z) = (arg z)²` on `Ω' = ℂ*` (the infimum is attained at `w = arg z + π`).  This is
  not subharmonic: `ψ(-1) = π²` while `ψ < π²` off the negative real axis, so the sub-mean value
  inequality fails on every small circle around `-1`.

Main declarations:

* `IsPseudoconvex` — continuous psh exhaustion (Hörmander, Def. 2.6.8; equivalent to Demailly's
  definition).
* `KiselmanPrinciplePrinted m n` — the printed statement of `prop:Kis`.
* `not_kiselmanPrinciplePrinted` — `¬ KiselmanPrinciplePrinted 1 1`.
-/

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Complex
open scoped Topology Real ENNReal

namespace SGPT.PSH.BookDeep2Kiselman

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending

/-! ### The printed statement -/

/-- **Pseudoconvex open sets**: open sets admitting a continuous plurisubharmonic exhaustion
function `u` (every sublevel set `{u ≤ c}` is compact). -/
def IsPseudoconvex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (kDomain : Set E) : Prop :=
  IsOpen kDomain ∧ ∃ u : E → ℝ, ContinuousOn u kDomain ∧ PlurisubharmonicOn (fun x => (u x : EReal)) kDomain ∧
    ∀ c : ℝ, IsCompact {x | x ∈ kDomain ∧ u x ≤ c}

/-- The slice `Ω_z = {w : (z, w) ∈ Ω}`. -/
def slice {m n : ℕ} (kDomain : Set (ComplexModel m × ComplexModel n)) (z : ComplexModel m) :
    Set (ComplexModel n) :=
  {w | (z, w) ∈ kDomain}

/-- **`prop:Kis` as printed.** For every pseudoconvex domain `Ω ⊆ ℂᵐ × ℂⁿ` whose slices are
`E + iℝⁿ` with `E ⊆ ℝⁿ` arbitrary, and every `φ ∈ PSH(Ω)` independent of `Im w`, the function
`ψ(z) = inf_{w ∈ Ω_z} φ(z, w)` on the projection `Ω'` is `≡ -∞` or in `PSH(Ω')`. -/
def KiselmanPrinciplePrinted (m n : ℕ) : Prop :=
  ∀ kDomain : Set (ComplexModel m × ComplexModel n), IsConnected kDomain → IsPseudoconvex kDomain →
    (∀ z, ∃ E : Set (Fin n → ℝ), slice kDomain z = {w | (fun k => (w k).re) ∈ E}) →
    ∀ kPhi : ComplexModel m × ComplexModel n → EReal, SGPT.PSH.PSHOn kPhi kDomain →
      (∀ z w w', (z, w) ∈ kDomain → (∀ k, (w k).re = (w' k).re) → kPhi (z, w') = kPhi (z, w)) →
      (∀ z ∈ Prod.fst '' kDomain, (⨅ w ∈ slice kDomain z, kPhi (z, w)) = ⊥) ∨
        SGPT.PSH.PSHOn (fun z => ⨅ w ∈ slice kDomain z, kPhi (z, w)) (Prod.fst '' kDomain)

/-- **`prop:Kis`, corrected** (Demailly, Ch. I, Thm. (7.5)): the same statement with **convex**
`E` in every slice `Ω_z = E + iℝⁿ`.  Recorded as a statement only; it is not proved here. -/
def KiselmanPrincipleConvexSlices (m n : ℕ) : Prop :=
  ∀ Ω : Set (ComplexModel m × ComplexModel n), IsConnected Ω → IsPseudoconvex Ω →
    (∀ z, ∃ E : Set (Fin n → ℝ), Convex ℝ E ∧ slice Ω z = {w | (fun k => (w k).re) ∈ E}) →
    ∀ φ : ComplexModel m × ComplexModel n → EReal, SGPT.PSH.PSHOn φ Ω →
      (∀ z w w', (z, w) ∈ Ω → (∀ k, (w k).re = (w' k).re) → φ (z, w') = φ (z, w)) →
      (∀ z ∈ Prod.fst '' Ω, (⨅ w ∈ slice Ω z, φ (z, w)) = ⊥) ∨
        SGPT.PSH.PSHOn (fun z => ⨅ w ∈ slice Ω z, φ (z, w)) (Prod.fst '' Ω)

/-! ### The counterexample on `ℂ²` -/

/-- `G(z, w) = z e^{-iw}` on `ℂ² = ComplexModel 2`. -/
def G (v : ComplexModel 2) : ℂ := v 0 * Complex.exp (-(Complex.I * v 1))

/-- `Ω₂ = {Re (z e^{-iw}) < 0}`. -/
def omega2 : Set (ComplexModel 2) := {v | (G v).re < 0}

theorem differentiable_G : Differentiable ℂ G := by
  have h0 : Differentiable ℂ (fun v : ComplexModel 2 => v 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : ComplexModel 2 →L[ℂ] ℂ).differentiable
  have h1 : Differentiable ℂ (fun v : ComplexModel 2 => v 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : ComplexModel 2 →L[ℂ] ℂ).differentiable
  exact h0.mul ((differentiable_const _ |>.mul h1).neg.cexp)

theorem continuous_G : Continuous G := differentiable_G.continuous

theorem isOpen_omega2 : IsOpen omega2 :=
  isOpen_lt (Complex.continuous_re.comp continuous_G) continuous_const

/-- The half-plane `{Re ζ < 0}` in `ComplexModel 1`. -/
def leftHalf : Set (ComplexModel 1) := {ζ | (SGPT.Toric.projectiveModelEquiv.symm ζ).re < 0}

/-- `ζ ↦ Re ζ` on `ComplexModel 1`, as an `ℝ`-linear map. -/
def reL : ComplexModel 1 →ₗ[ℝ] ℝ :=
  Complex.reLm.comp
    (SGPT.Toric.projectiveModelEquiv.symm.toContinuousLinearMap.restrictScalars ℝ).toLinearMap

/-- `ζ ↦ Im ζ` on `ComplexModel 1`, as an `ℝ`-linear map. -/
def imL : ComplexModel 1 →ₗ[ℝ] ℝ :=
  Complex.imLm.comp
    (SGPT.Toric.projectiveModelEquiv.symm.toContinuousLinearMap.restrictScalars ℝ).toLinearMap

theorem reL_apply (ζ : ComplexModel 1) :
    reL ζ = (SGPT.Toric.projectiveModelEquiv.symm ζ).re := rfl

theorem imL_apply (ζ : ComplexModel 1) :
    imL ζ = (SGPT.Toric.projectiveModelEquiv.symm ζ).im := rfl

/-- `-log (-t)` is convex on `t < 0`. -/
theorem convexOn_neg_log_neg : ConvexOn ℝ (Iio 0) (fun t : ℝ => -Real.log (-t)) := by
  have h := strictConcaveOn_log_Ioi.concaveOn.neg.comp_linearMap (-LinearMap.id : ℝ →ₗ[ℝ] ℝ)
  have hpre : ((-LinearMap.id : ℝ →ₗ[ℝ] ℝ) ⁻¹' Ioi 0) = Iio 0 := by
    ext t
    simp
  rw [hpre] at h
  exact h

/-- `f₀(ζ) = -log (-Re ζ)` on the left half-plane. -/
def f0 (ζ : ComplexModel 1) : ℝ := -Real.log (-(SGPT.Toric.projectiveModelEquiv.symm ζ).re)

theorem plurisubharmonicOn_f0 :
    PlurisubharmonicOn (fun ζ => (f0 ζ : EReal)) leftHalf := by
  have hconv : ConvexOn ℝ (reL ⁻¹' Iio 0) ((fun t : ℝ => -Real.log (-t)) ∘ reL) :=
    convexOn_neg_log_neg.comp_linearMap reL
  have hset : reL ⁻¹' Iio 0 = leftHalf := rfl
  rw [hset] at hconv
  have hcont : Continuous (fun ζ : ComplexModel 1 => (SGPT.Toric.projectiveModelEquiv.symm ζ).re) :=
    Complex.continuous_re.comp SGPT.Toric.projectiveModelEquiv.symm.continuous
  refine plurisubharmonicOn_of_convexOn
    (isOpen_lt hcont continuous_const) hconv ?_
  intro ζ hζ
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.neg
  apply ContinuousAt.log (hcont.neg.continuousAt)
  exact ne_of_gt (neg_pos.mpr hζ)

/-- The exhaustion function `u₂ = ‖v‖² + Im w - log (-Re (z e^{-iw}))`. -/
def u2 (v : ComplexModel 2) : ℝ := ‖v‖ ^ 2 + (v 1).im + -Real.log (-(G v).re)

theorem convexOn_norm_sq_add_im :
    ConvexOn ℝ univ (fun v : ComplexModel 2 => ‖v‖ ^ 2 + (v 1).im) := by
  have h1 : ConvexOn ℝ univ (fun v : ComplexModel 2 => ‖v‖ ^ 2) := by
    exact (convexOn_univ_norm (E := ComplexModel 2)).pow (fun x _ => norm_nonneg x) 2
  have h2 : ConvexOn ℝ univ (fun v : ComplexModel 2 => (v 1).im) :=
    (Complex.imLm.comp ((EuclideanSpace.proj (1 : Fin 2) : ComplexModel 2 →L[ℂ] ℂ).restrictScalars
      ℝ).toLinearMap).convexOn convex_univ
  exact h1.add h2

theorem plurisubharmonicOn_u2 : PlurisubharmonicOn (fun v => (u2 v : EReal)) omega2 := by
  have h1 : PlurisubharmonicOn (fun v : ComplexModel 2 => ((‖v‖ ^ 2 + (v 1).im : ℝ) : EReal))
      omega2 := by
    have := plurisubharmonicOn_of_convexOn isOpen_univ convexOn_norm_sq_add_im
      (by fun_prop)
    exact fun x _ => this x (mem_univ x)
  have h2 : PlurisubharmonicOn
      (fun v : ComplexModel 2 => (f0 (SGPT.Toric.projectiveModelEquiv (G v)) : EReal)) omega2 := by
    refine HolomorphicPullback.plurisubharmonicOn_comp_holomorphic isOpen_omega2 ?_ ?_
      plurisubharmonicOn_f0
    · exact (SGPT.Toric.projectiveModelEquiv.differentiable.comp differentiable_G).differentiableOn
    · intro v hv
      change (SGPT.Toric.projectiveModelEquiv.symm (SGPT.Toric.projectiveModelEquiv (G v))).re < 0
      simpa [omega2] using hv
  have h := h1.add h2
  intro x hx
  obtain ⟨U, hU, hxU, hd⟩ := h x hx
  refine ⟨U, hU, hxU, hd.congr fun y _ => ?_⟩
  simp only [u2, f0, ContinuousLinearEquiv.symm_apply_apply, EReal.coe_add]

theorem continuousOn_u2 : ContinuousOn u2 omega2 := by
  intro v hv
  apply ContinuousAt.continuousWithinAt
  have hre : Continuous (fun v : ComplexModel 2 => (G v).re) :=
    Complex.continuous_re.comp continuous_G
  refine ((continuous_norm.pow 2).add ?_).continuousAt.add ?_
  · exact Complex.continuous_im.comp
      (EuclideanSpace.proj (1 : Fin 2) : ComplexModel 2 →L[ℂ] ℂ).continuous
  · exact (ContinuousAt.log hre.neg.continuousAt (ne_of_gt (neg_pos.mpr hv))).neg

theorem norm_exp_neg_I_mul (w : ℂ) : ‖Complex.exp (-(Complex.I * w))‖ = Real.exp w.im := by
  rw [Complex.norm_exp]
  congr 1
  simp

theorem neg_re_G_le (v : ComplexModel 2) : -(G v).re ≤ ‖v 0‖ * Real.exp (v 1).im := by
  calc -(G v).re ≤ |(G v).re| := neg_le_abs _
    _ ≤ ‖G v‖ := Complex.abs_re_le_norm _
    _ = ‖v 0‖ * Real.exp (v 1).im := by rw [G, norm_mul, norm_exp_neg_I_mul]

theorem norm_coord_le (v : ComplexModel 2) (i : Fin 2) : ‖v i‖ ≤ ‖v‖ :=
  PiLp.norm_apply_le v i

/-- The sublevel sets of `u₂` are compact. -/
theorem isCompact_sublevel_u2 (c : ℝ) : IsCompact {v | v ∈ omega2 ∧ u2 v ≤ c} := by
  set R : ℝ := max 1 (2 * c)
  set δ : ℝ := Real.exp (-(c + R))
  have hδ : 0 < δ := Real.exp_pos _
  have hbound : ∀ v ∈ omega2, u2 v ≤ c → ‖v‖ ≤ R ∧ (G v).re ≤ -δ := by
    intro v hv hu
    have hv' : 0 < -(G v).re := neg_pos.mpr hv
    have hG := neg_re_G_le v
    have h0 : 0 < ‖v 0‖ := by
      by_contra h
      have : ‖v 0‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
      rw [this, zero_mul] at hG
      linarith
    have hlog : Real.log (-(G v).re) ≤ Real.log ‖v 0‖ + (v 1).im := by
      calc Real.log (-(G v).re) ≤ Real.log (‖v 0‖ * Real.exp (v 1).im) :=
            Real.log_le_log hv' hG
        _ = Real.log ‖v 0‖ + (v 1).im := by
            rw [Real.log_mul (ne_of_gt h0) (Real.exp_pos _).ne', Real.log_exp]
    have hlog0 : Real.log ‖v 0‖ ≤ ‖v 0‖ - 1 := Real.log_le_sub_one_of_pos h0
    have hc0 : ‖v 0‖ ≤ ‖v‖ := norm_coord_le v 0
    have him : |(v 1).im| ≤ ‖v‖ := (Complex.abs_im_le_norm _).trans (norm_coord_le v 1)
    have hu' : ‖v‖ ^ 2 + (v 1).im + -Real.log (-(G v).re) ≤ c := hu
    have hnorm : ‖v‖ ^ 2 - ‖v‖ + 1 ≤ c := by linarith
    have hR : ‖v‖ ≤ R := by
      rcases le_or_gt ‖v‖ 1 with h1 | h1
      · exact h1.trans (le_max_left _ _)
      · refine le_trans ?_ (le_max_right _ _)
        nlinarith
    refine ⟨hR, ?_⟩
    have hlow : -(c + R) ≤ Real.log (-(G v).re) := by
      have := abs_le.mp him
      nlinarith [sq_nonneg ‖v‖]
    have := Real.exp_le_exp.mpr hlow
    rw [Real.exp_log hv'] at this
    linarith
  set K : Set (ComplexModel 2) := Metric.closedBall 0 R ∩ {v | (G v).re ≤ -δ}
  have hKc : IsCompact K :=
    (isCompact_closedBall 0 R).inter_right
      (isClosed_le (Complex.continuous_re.comp continuous_G) continuous_const)
  have hKkDomain : K ⊆ omega2 := fun v hv => lt_of_le_of_lt hv.2 (neg_lt_zero.mpr hδ)
  have hclosed : IsClosed (K ∩ u2 ⁻¹' Iic c) :=
    (continuousOn_u2.mono hKkDomain).preimage_isClosed_of_isClosed hKc.isClosed isClosed_Iic
  have heq : {v | v ∈ omega2 ∧ u2 v ≤ c} = K ∩ u2 ⁻¹' Iic c := by
    ext v
    constructor
    · rintro ⟨hv, hu⟩
      obtain ⟨h1, h2⟩ := hbound v hv hu
      exact ⟨⟨mem_closedBall_zero_iff.mpr h1, h2⟩, hu⟩
    · rintro ⟨hv, hu⟩
      exact ⟨hKkDomain hv, hu⟩
  rw [heq]
  exact hKc.of_isClosed_subset hclosed inter_subset_left

/-- `φ₂ = (arg (-z e^{-iw}) + Re w - π)²`, written through the holomorphic logarithm. -/
def phi2 (v : ComplexModel 2) : ℝ := ((Complex.log (-(G v)) + Complex.I * v 1).im - π) ^ 2

/-- `q(ζ) = (Im ζ - π)²`, a convex function on `ComplexModel 1`. -/
def q (ζ : ComplexModel 1) : ℝ := (imL ζ - π) ^ 2

theorem convexOn_q : ConvexOn ℝ univ q := by
  have h1 : ConvexOn ℝ univ (fun ζ : ComplexModel 1 => imL ζ ^ 2) := by
    exact (Even.convexOn_pow (𝕜 := ℝ) (n := 2) even_two).comp_linearMap imL
  have h2 : ConvexOn ℝ univ ((fun ζ : ComplexModel 1 => (-(2 * π)) • imL ζ) + fun _ => π ^ 2) :=
    (((-(2 * π)) • imL).convexOn convex_univ).add (convexOn_const (π ^ 2) convex_univ)
  refine (h1.add h2).congr ?_
  intro ζ _
  simp only [Pi.add_apply, q, smul_eq_mul]
  ring

theorem mem_slitPlane_neg_G {v : ComplexModel 2} (hv : v ∈ omega2) : -(G v) ∈ Complex.slitPlane := by
  have hv' : (G v).re < 0 := hv
  exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using neg_pos.mpr hv'))

theorem plurisubharmonicOn_phi2 : PlurisubharmonicOn (fun v => (phi2 v : EReal)) omega2 := by
  have hq : PlurisubharmonicOn (fun ζ => (q ζ : EReal)) univ :=
    plurisubharmonicOn_of_convexOn isOpen_univ convexOn_q (by unfold q imL; fun_prop)
  have hF : DifferentiableOn ℂ (fun v : ComplexModel 2 => SGPT.Toric.projectiveModelEquiv
      (Complex.log (-(G v)) + Complex.I * v 1)) omega2 := by
    intro v hv
    apply DifferentiableAt.differentiableWithinAt
    apply SGPT.Toric.projectiveModelEquiv.differentiableAt.comp
    refine DifferentiableAt.add ?_ ?_
    · exact ((differentiable_G v).neg).clog (mem_slitPlane_neg_G hv)
    · exact (differentiable_const _).mul
        (EuclideanSpace.proj (1 : Fin 2) : ComplexModel 2 →L[ℂ] ℂ).differentiable v
  have h := HolomorphicPullback.plurisubharmonicOn_comp_holomorphic isOpen_omega2 hF
    (mapsTo_univ _ _) hq
  intro x hx
  obtain ⟨U, hU, hxU, hd⟩ := h x hx
  refine ⟨U, hU, hxU, hd.congr fun y _ => ?_⟩
  simp only [q, imL_apply, phi2, ContinuousLinearEquiv.symm_apply_apply]

/-! ### Transfer to `ℂ × ℂ = ComplexModel 1 × ComplexModel 1` -/

/-- `ℂ × ℂ ≅ ℂ²` as a continuous linear equivalence. -/
def pairEquiv : (ComplexModel 1 × ComplexModel 1) ≃L[ℂ] ComplexModel 2 :=
  (SGPT.Toric.projectiveModelEquiv.symm.prodCongr SGPT.Toric.projectiveModelEquiv.symm).trans
    ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm.trans (EuclideanSpace.equiv (Fin 2) ℂ).symm)

@[simp] theorem pairEquiv_apply_zero (p : ComplexModel 1 × ComplexModel 1) :
    pairEquiv p 0 = p.1 0 := by
  simp [pairEquiv, SGPT.Toric.projectiveModelEquiv_symm_apply]

@[simp] theorem pairEquiv_apply_one (p : ComplexModel 1 × ComplexModel 1) :
    pairEquiv p 1 = p.2 0 := by
  simp [pairEquiv, SGPT.Toric.projectiveModelEquiv_symm_apply]

attribute [local irreducible] pairEquiv

/-- **The counterexample domain** `Ω = {(z, w) : Re (z e^{-iw}) < 0} ⊆ ℂ × ℂ`. -/
def kDomain : Set (ComplexModel 1 × ComplexModel 1) := pairEquiv ⁻¹' omega2

theorem mem_kDomain (p : ComplexModel 1 × ComplexModel 1) :
    p ∈ kDomain ↔ (p.1 0 * Complex.exp (-(Complex.I * p.2 0))).re < 0 := by
  change (G (pairEquiv p)).re < 0 ↔ _
  rw [G, pairEquiv_apply_zero, pairEquiv_apply_one]

/-- **The counterexample function** `φ(z, w) = (arg (-z e^{-iw}) + Re w - π)²`. -/
def kPhi (p : ComplexModel 1 × ComplexModel 1) : EReal := (phi2 (pairEquiv p) : EReal)

theorem kPhi_eq (p : ComplexModel 1 × ComplexModel 1) :
    kPhi p = (((Complex.arg (-(p.1 0 * Complex.exp (-(Complex.I * p.2 0)))) + (p.2 0).re - π) ^ 2 :
      ℝ) : EReal) := by
  simp only [kPhi, phi2, G, pairEquiv_apply_zero, pairEquiv_apply_one, Complex.add_im,
    Complex.log_im, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]

theorem isPseudoconvex_kDomain : IsPseudoconvex kDomain := by
  refine ⟨isOpen_omega2.preimage pairEquiv.continuous, fun p => u2 (pairEquiv p),
    continuousOn_u2.comp pairEquiv.continuous.continuousOn (fun p hp => hp), ?_, fun c => ?_⟩
  · have h := plurisubharmonicOn_u2.comp_continuousLinearMap
      (pairEquiv : ComplexModel 1 × ComplexModel 1 →L[ℂ] ComplexModel 2)
    simp only [ContinuousLinearEquiv.coe_coe] at h
    exact h
  · have hset : {p | p ∈ kDomain ∧ u2 (pairEquiv p) ≤ c} =
        pairEquiv.toHomeomorph ⁻¹' {v | v ∈ omega2 ∧ u2 v ≤ c} := rfl
    rw [hset, Homeomorph.isCompact_preimage]
    exact isCompact_sublevel_u2 c

/-! ### Connectedness, slices and the function `φ` -/

theorem exp_neg_I_mul_eq (w : ℂ) :
    Complex.exp (-(Complex.I * w)) =
      Complex.exp (-(Complex.I * (w.re : ℂ))) * (Real.exp w.im : ℂ) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp

theorem re_mul_exp_neg_I_mul (z w : ℂ) :
    (z * Complex.exp (-(Complex.I * w))).re =
      (z * Complex.exp (-(Complex.I * (w.re : ℂ)))).re * Real.exp w.im := by
  rw [exp_neg_I_mul_eq, ← mul_assoc, Complex.re_mul_ofReal]

theorem mul_neg_iff_of_pos' {a r : ℝ} (hr : 0 < r) : a * r < 0 ↔ a < 0 := by
  constructor
  · intro h
    by_contra h'
    push Not at h'
    nlinarith
  · intro h
    nlinarith

/-- The slices of `Ω` are tubes `E_z + iℝ`. -/
theorem slice_kDomain_eq (z : ComplexModel 1) :
    slice kDomain z = {w | (fun k => (w k).re) ∈
      {x : Fin 1 → ℝ | (z 0 * Complex.exp (-(Complex.I * ((x 0 : ℝ) : ℂ)))).re < 0}} := by
  ext w
  change (z, w) ∈ kDomain ↔ _
  rw [mem_kDomain]
  simp only [mem_ofPred_eq]
  rw [re_mul_exp_neg_I_mul, mul_neg_iff_of_pos' (Real.exp_pos _)]

/-- `Ω` is the image of the convex set `{Re a < 0} × ℂ` under `(a, w) ↦ (a e^{iw}, w)`. -/
theorem isConnected_kDomain : IsConnected kDomain := by
  let Θ : ℂ × ComplexModel 1 → ComplexModel 1 × ComplexModel 1 := fun p =>
    (SGPT.Toric.projectiveModelEquiv (p.1 * Complex.exp (Complex.I * p.2 0)), p.2)
  have hΘ : Continuous Θ := by
    refine Continuous.prodMk ?_ continuous_snd
    refine SGPT.Toric.projectiveModelEquiv.continuous.comp ?_
    refine continuous_fst.mul (Complex.continuous_exp.comp (continuous_const.mul ?_))
    exact (EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).continuous.comp
      continuous_snd
  have hS : IsConnected ({a : ℂ | a.re < 0} ×ˢ (univ : Set (ComplexModel 1))) :=
    ((convex_halfSpace_re_lt (r := 0)).isConnected ⟨-1, by simp⟩).prod isConnected_univ
  have himage : Θ '' ({a : ℂ | a.re < 0} ×ˢ (univ : Set (ComplexModel 1))) = kDomain := by
    ext p
    constructor
    · rintro ⟨⟨a, w⟩, ⟨ha, -⟩, rfl⟩
      rw [mem_kDomain]
      simp only [Θ, SGPT.Toric.projectiveModelEquiv_apply_zero]
      rw [mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
      exact ha
    · intro hp
      refine ⟨(p.1 0 * Complex.exp (-(Complex.I * p.2 0)), p.2), ⟨(mem_kDomain p).mp hp, mem_univ _⟩, ?_⟩
      simp only [Θ]
      rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
      refine Prod.ext ?_ rfl
      change SGPT.Toric.projectiveModelEquiv (p.1 0) = p.1
      rw [← SGPT.Toric.projectiveModelEquiv_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [← himage]
  exact hS.image Θ hΘ.continuousOn

theorem arg_neg_mul_exp_eq (z w : ℂ) :
    Complex.arg (-(z * Complex.exp (-(Complex.I * w)))) =
      Complex.arg (-(z * Complex.exp (-(Complex.I * (w.re : ℂ))))) := by
  rw [exp_neg_I_mul_eq]
  have : -(z * (Complex.exp (-(Complex.I * (w.re : ℂ))) * (Real.exp w.im : ℂ))) =
      -(z * Complex.exp (-(Complex.I * (w.re : ℂ)))) * (Real.exp w.im : ℂ) := by ring
  rw [this, Complex.arg_mul_real (Real.exp_pos _)]

/-- `φ` only depends on `Re w`. -/
theorem kPhi_indep (z w w' : ComplexModel 1) (h : ∀ k, (w k).re = (w' k).re) :
    kPhi (z, w') = kPhi (z, w) := by
  rw [kPhi_eq, kPhi_eq]
  simp only
  rw [arg_neg_mul_exp_eq, arg_neg_mul_exp_eq (w := w 0), h 0]

/-- The base point `(-1, 0) ∈ Ω`. -/
def basePoint : ComplexModel 1 := SGPT.Toric.projectiveModelEquiv (-1)

theorem basePoint_apply : basePoint 0 = -1 := SGPT.Toric.projectiveModelEquiv_apply_zero _

theorem mem_kDomain_basePoint : (basePoint, (0 : ComplexModel 1)) ∈ kDomain := by
  rw [mem_kDomain, basePoint_apply]
  simp

theorem pshOn_kPhi : SGPT.PSH.PSHOn kPhi kDomain := by
  have h := plurisubharmonicOn_phi2.comp_continuousLinearMap
    (pairEquiv : ComplexModel 1 × ComplexModel 1 →L[ℂ] ComplexModel 2)
  simp only [ContinuousLinearEquiv.coe_coe] at h
  exact ⟨h.discPshOn, ⟨_, mem_kDomain_basePoint, EReal.coe_ne_bot _⟩⟩

/-! ### The infimum `ψ = (arg z)²` -/

theorem key_point (z₀ : ℂ) :
    z₀ * Complex.exp (-(Complex.I * ((Complex.arg z₀ + π : ℝ) : ℂ))) = -(‖z₀‖ : ℂ) := by
  have hz := Complex.norm_mul_exp_arg_mul_I z₀
  calc z₀ * Complex.exp (-(Complex.I * ((Complex.arg z₀ + π : ℝ) : ℂ)))
      = ((‖z₀‖ : ℂ) * Complex.exp (Complex.arg z₀ * Complex.I)) *
          Complex.exp (-(Complex.I * ((Complex.arg z₀ + π : ℝ) : ℂ))) := by rw [hz]
    _ = -(‖z₀‖ : ℂ) := ?_
  rw [mul_assoc, ← Complex.exp_add]
  have : (Complex.arg z₀ : ℂ) * Complex.I + -(Complex.I * ((Complex.arg z₀ + π : ℝ) : ℂ)) =
      -((π : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]
  simp

/-- The minimizing slice point `w = arg z + π`. -/
def wStar (z : ComplexModel 1) : ComplexModel 1 :=
  SGPT.Toric.projectiveModelEquiv (((Complex.arg (z 0) + π : ℝ) : ℂ))

theorem wStar_apply (z : ComplexModel 1) : wStar z 0 = ((Complex.arg (z 0) + π : ℝ) : ℂ) :=
  SGPT.Toric.projectiveModelEquiv_apply_zero _

theorem mem_kDomain_wStar {z : ComplexModel 1} (hz : z 0 ≠ 0) : (z, wStar z) ∈ kDomain := by
  rw [mem_kDomain]
  simp only
  rw [wStar_apply, key_point]
  simpa using norm_pos_iff.mpr hz

theorem kPhi_wStar {z : ComplexModel 1} : kPhi (z, wStar z) = ((Complex.arg (z 0) ^ 2 : ℝ) : EReal) := by
  rw [kPhi_eq]
  simp only
  rw [wStar_apply, key_point, neg_neg, Complex.arg_ofReal_of_nonneg (norm_nonneg _)]
  simp

theorem ne_zero_of_mem_kDomain {p : ComplexModel 1 × ComplexModel 1} (hp : p ∈ kDomain) : p.1 0 ≠ 0 := by
  intro h
  rw [mem_kDomain, h, zero_mul, Complex.zero_re] at hp
  exact lt_irrefl _ hp

theorem fst_image_kDomain : Prod.fst '' kDomain = {z : ComplexModel 1 | z 0 ≠ 0} := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ne_zero_of_mem_kDomain hp
  · intro hz
    exact ⟨(z, wStar z), mem_kDomain_wStar hz, rfl⟩

/-- Every value of `φ` on the slice over `z` is at least `(arg z)²`. -/
theorem arg_sq_le (z₀ w₀ : ℂ) (hz : z₀ ≠ 0) :
    Complex.arg z₀ ^ 2 ≤
      (Complex.arg (-(z₀ * Complex.exp (-(Complex.I * w₀)))) + w₀.re - π) ^ 2 := by
  set A := Complex.arg (-(z₀ * Complex.exp (-(Complex.I * w₀)))) + w₀.re - π
  have hA : (A : Real.Angle) = (Complex.arg z₀ : Real.Angle) := by
    have h1 : (Complex.arg (-(z₀ * Complex.exp (-(Complex.I * w₀)))) : Real.Angle) =
        Complex.arg z₀ + π + (-w₀.re : ℝ) := by
      rw [show -(z₀ * Complex.exp (-(Complex.I * w₀))) =
          (-z₀) * Complex.exp (-(Complex.I * w₀)) by ring,
        Complex.arg_mul_coe_angle (neg_ne_zero.mpr hz) (Complex.exp_ne_zero _),
        Complex.arg_neg_coe_angle hz, Complex.arg_exp, Real.Angle.coe_toIocMod]
      simp
    simp only [A, Real.Angle.coe_sub, Real.Angle.coe_add, h1, Real.Angle.coe_neg]
    abel
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hA
  rw [sq_le_sq]
  have harg := Complex.abs_arg_le_pi z₀
  rcases eq_or_ne k 0 with rfl | hk0
  · have : A = Complex.arg z₀ := by
      simp only [Int.cast_zero, mul_zero] at hk
      linarith
    rw [this]
  · have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hk0
    have hA' : A = Complex.arg z₀ + 2 * π * k := by linarith
    have h2 : 2 * π ≤ |2 * π * (k : ℝ)| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      nlinarith [Real.pi_pos]
    have h3 : |2 * π * (k : ℝ)| ≤ |A| + |Complex.arg z₀| := by
      calc |2 * π * (k : ℝ)| = |A - Complex.arg z₀| := by rw [hA']; ring_nf
        _ ≤ |A| + |Complex.arg z₀| := abs_sub _ _
    linarith [Real.pi_pos]

/-- **`ψ(z) = (arg z)²`** on `Ω' = ℂ*`. -/
theorem psi_eq {z : ComplexModel 1} (hz : z 0 ≠ 0) :
    (⨅ w ∈ slice kDomain z, kPhi (z, w)) = ((Complex.arg (z 0) ^ 2 : ℝ) : EReal) := by
  apply le_antisymm
  · rw [← kPhi_wStar]
    exact iInf₂_le (wStar z) (mem_kDomain_wStar hz)
  · refine le_iInf₂ fun w _ => ?_
    rw [kPhi_eq]
    exact EReal.coe_le_coe_iff.mpr (arg_sq_le _ _ hz)

/-! ### `ψ = (arg z)²` is not subharmonic -/

/-- The unit vector of `ComplexModel 1`. -/
def unitVec : ComplexModel 1 := SGPT.Toric.projectiveModelEquiv 1

theorem disc_point (ζ : ℂ) : basePoint + ζ • unitVec = SGPT.Toric.projectiveModelEquiv (-1 + ζ) := by
  rw [basePoint, unitVec, ← map_smul, ← map_add, smul_eq_mul, mul_one]

theorem disc_point_apply (ζ : ℂ) : (basePoint + ζ • unitVec) 0 = -1 + ζ := by
  rw [disc_point, SGPT.Toric.projectiveModelEquiv_apply_zero]

theorem neg_one_add_ne_zero {ζ : ℂ} (hζ : ‖ζ‖ < 1) : -1 + ζ ≠ 0 := by
  intro h
  have : ζ = 1 := by linear_combination h
  rw [this, norm_one] at hζ
  exact lt_irrefl _ hζ

/-- The function `ψ(z) = inf_{w ∈ Ω_z} φ(z, w)` of the counterexample. -/
def kPsi (z : ComplexModel 1) : EReal := ⨅ w ∈ slice kDomain z, kPhi (z, w)

theorem kPsi_basePoint : kPsi basePoint = ((π ^ 2 : ℝ) : EReal) := by
  rw [kPsi, psi_eq (by rw [basePoint_apply]; norm_num), basePoint_apply, Complex.arg_neg_one]

theorem im_circle (t : ℝ) : (-1 + circleMap 0 (1 / 2) t).im = (1 / 2) * Real.sin t := by
  simp only [circleMap, zero_add, Complex.add_im, Complex.neg_im, Complex.one_im, neg_zero]
  rw [show ((1 / 2 : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) from rfl, Complex.im_ofReal_mul,
    Complex.exp_ofReal_mul_I_im]

/-- `ψ` is not plurisubharmonic on `Ω' = ℂ*`: the sub-mean value inequality fails on the circle
of radius `1/2` around `-1`. -/
theorem not_pshOn_kPsi : ¬ SGPT.PSH.PSHOn kPsi (Prod.fst '' kDomain) := by
  intro hpsh
  rw [fst_image_kDomain] at hpsh
  have hr : (0 : ℝ) < 1 / 2 := by norm_num
  have hball : ∀ ζ ∈ Metric.closedBall (0 : ℂ) (1 / 2), ‖ζ‖ < 1 := by
    intro ζ hζ
    rw [mem_closedBall_zero_iff] at hζ
    linarith
  have hdisc : SGPT.Foundations.Analysis.affineClosedDisc basePoint unitVec (1 / 2) ⊆
      {z : ComplexModel 1 | z 0 ≠ 0} := by
    rintro _ ⟨ζ, hζ, rfl⟩
    change (basePoint + ζ • unitVec) 0 ≠ 0
    rw [disc_point_apply]
    exact neg_one_add_ne_zero (hball ζ hζ)
  have hbound : ∀ y ∈ SGPT.Foundations.Analysis.affineClosedDisc basePoint unitVec (1 / 2),
      kPsi y ≤ ((π ^ 2 : ℝ) : EReal) := by
    intro y hy
    rw [kPsi, psi_eq (hdisc hy)]
    refine EReal.coe_le_coe_iff.mpr ?_
    rw [sq_le_sq, abs_of_pos Real.pi_pos]
    exact Complex.abs_arg_le_pi _
  have hmean := hpsh.disc.submean basePoint unitVec (1 / 2) hr hdisc (π ^ 2) hbound
  rw [kPsi_basePoint, ← EReal.coe_sub, sub_self, EReal.coe_zero] at hmean
  simp only [EReal.toENNReal_zero, mul_zero, nonpos_iff_eq_zero] at hmean
  -- the circle points and the explicit integrand
  set g : ℝ → ℝ≥0∞ := fun t =>
    ENNReal.ofReal (π ^ 2 - Complex.arg (-1 + circleMap 0 (1 / 2) t) ^ 2) with hg
  have hcircle : ∀ t : ℝ, ((π ^ 2 : ℝ) : EReal) - kPsi (basePoint + circleMap 0 (1 / 2) t • unitVec) =
      ((π ^ 2 - Complex.arg (-1 + circleMap 0 (1 / 2) t) ^ 2 : ℝ) : EReal) := by
    intro t
    have hne : (basePoint + circleMap 0 (1 / 2) t • unitVec) 0 ≠ 0 := by
      rw [disc_point_apply]
      apply neg_one_add_ne_zero
      rw [norm_circleMap_zero, abs_of_pos hr]
      norm_num
    rw [kPsi, psi_eq hne, disc_point_apply, ← EReal.coe_sub]
  have hdef : SGPT.Foundations.Analysis.circleDeficit kPsi basePoint unitVec (1 / 2) (π ^ 2) =
      ∫⁻ t in Ioc 0 (2 * π), g t := by
    unfold SGPT.Foundations.Analysis.circleDeficit
    refine setLIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    rw [hcircle, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
  rw [hdef] at hmean
  have hgm : Measurable g := by
    refine ENNReal.measurable_ofReal.comp (measurable_const.sub ?_)
    exact (Complex.measurable_arg.comp
      (measurable_const.add (continuous_circleMap 0 (1 / 2)).measurable)).pow_const 2
  have hpos : 0 < ∫⁻ t in Ioc 0 (2 * π), g t := by
    rw [setLIntegral_pos_iff hgm]
    have hsub : Ioo 0 π ⊆ Function.support g ∩ Ioc 0 (2 * π) := by
      intro t ht
      refine ⟨?_, ht.1, by linarith [ht.2, Real.pi_pos]⟩
      have him : (-1 + circleMap 0 (1 / 2) t).im ≠ 0 := by
        rw [im_circle]
        exact ne_of_gt (mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2))
      have hlt : Complex.arg (-1 + circleMap 0 (1 / 2) t) < π :=
        Complex.arg_lt_pi_iff.mpr (Or.inr him)
      have hgt := Complex.neg_pi_lt_arg (-1 + circleMap 0 (1 / 2) t)
      have hsq : Complex.arg (-1 + circleMap 0 (1 / 2) t) ^ 2 < π ^ 2 := by
        rw [sq_lt_sq, abs_of_pos Real.pi_pos, abs_lt]
        exact ⟨hgt, hlt⟩
      simp only [Function.mem_support, hg, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      linarith
    calc (0 : ℝ≥0∞) < volume (Ioo 0 π) := by
          rw [Real.volume_Ioo, sub_zero]
          exact ENNReal.ofReal_pos.mpr Real.pi_pos
      _ ≤ volume (Function.support g ∩ Ioc 0 (2 * π)) := measure_mono hsub
  rw [hmean] at hpos
  exact lt_irrefl _ hpos

/-- **Erratum to `prop:Kis`: Kiselman's principle as printed is false** (already for
`m = n = 1`): `Ω = {Re (z e^{-iw}) < 0}` is a pseudoconvex domain whose slices are tubes
`E_z + iℝ` (with `E_z` a union of infinitely many intervals), `φ = (arg (-z e^{-iw}) + Re w - π)²`
is psh and independent of `Im w`, but `inf_w φ = (arg z)²` is neither `≡ -∞` nor psh on `ℂ*`. -/
theorem not_kiselmanPrinciplePrinted : ¬ KiselmanPrinciplePrinted 1 1 := by
  intro h
  rcases h kDomain isConnected_kDomain isPseudoconvex_kDomain (fun z => ⟨_, slice_kDomain_eq z⟩) kPhi pshOn_kPhi
      (fun z w w' _ hw => kPhi_indep z w w' hw) with hbot | hpsh
  · have hx : basePoint ∈ Prod.fst '' kDomain := ⟨(basePoint, 0), mem_kDomain_basePoint, rfl⟩
    have := hbot basePoint hx
    change kPsi basePoint = ⊥ at this
    rw [kPsi_basePoint] at this
    exact EReal.coe_ne_bot _ this
  · exact not_pshOn_kPsi hpsh

end SGPT.PSH.BookDeep2Kiselman
