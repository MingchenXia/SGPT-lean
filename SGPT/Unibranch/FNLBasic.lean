import SGPT.Foundations.Analysis.PshAddition
import SGPT.Foundations.Analysis.FirstPass.ComplexManifold
import SGPT.Foundations.Analysis.FirstPass.PshDiscLocalGlobal
import SGPT.PSH.Basic

/-!
# FN80 §5: weakly plurisubharmonic functions on embedded analytic sets

Source: J. E. Fornæss, R. Narasimhan, *The Levi problem on complex spaces with
singularities*, Math. Ann. 248 (1980), §5 (`[FN80]`), used by SGPT `thm:FN`
(`appendix_unibranch.tex`), implication (2) ⇒ (1) on singular spaces.

`[FN80]` §5 works with a closed subvariety `X` of a polydisc `Δⁿ`.  A function
`φ : X → [-∞, ∞)` is *weakly plurisubharmonic* (`φ ∈ WP(X)`) if it is upper
semicontinuous and `φ ∘ f` is subharmonic (possibly `≡ -∞`) on the unit disc for every
holomorphic map `f : Δ → X`.  We formalize this for an arbitrary subset `X ⊆ ℂⁿ`
(`IsWeaklyPSHOn`): holomorphic discs into `X` are maps `f : ℂ → ℂⁿ`, holomorphic on the
unit disc, with values in `X`; "subharmonic or `≡ -∞`" is the disc criterion
`SGPT.Foundations.Analysis.DiscPshOn` on the unit disc of `ℂ`.

Main results:

* `IsWeaklyPSHOn.discPshOn_comp`: for `φ ∈ WP(X)` and a holomorphic map `g : U → X`
  from an open subset of a complex normed space, `φ ∘ g` satisfies the disc criterion
  on `U` (it is plurisubharmonic or locally `≡ -∞`).
* `le_of_forall_punctured_le`: the value of a subharmonic function at the centre of a
  disc is bounded by any real upper bound on the punctured disc (sub-mean value
  inequality on a small circle).
-/

set_option autoImplicit false

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace SGPT.Unibranch.FNL

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {n : ℕ}

/-- `[FN80]` §5: `φ ∈ WP(X)`, the **weakly plurisubharmonic** functions on `X ⊆ ℂⁿ`:
`φ` is upper semicontinuous on `X` with values in `[-∞, ∞)`, and for every holomorphic
disc `f : Δ → X` the pull-back `φ ∘ f` is subharmonic on `Δ` (possibly `≡ -∞`). -/
structure IsWeaklyPSHOn (X : Set (ComplexModel n)) (φ : ComplexModel n → EReal) : Prop where
  ne_top : ∀ x ∈ X, φ x ≠ ⊤
  upperSemicontinuousOn : UpperSemicontinuousOn φ X
  disc : ∀ f : ℂ → ComplexModel n, DifferentiableOn ℂ f (ball (0 : ℂ) 1) →
    MapsTo f (ball (0 : ℂ) 1) X → DiscPshOn (fun t => φ (f t)) (ball (0 : ℂ) 1)

/-- Weak plurisubharmonicity passes to subsets. -/
theorem IsWeaklyPSHOn.mono {X Y : Set (ComplexModel n)} {φ : ComplexModel n → EReal}
    (hφ : IsWeaklyPSHOn X φ) (hYX : Y ⊆ X) : IsWeaklyPSHOn Y φ :=
  ⟨fun x hx => hφ.ne_top x (hYX hx), hφ.upperSemicontinuousOn.mono hYX,
    fun f hf hfY => hφ.disc f hf (hfY.mono_right hYX)⟩

/-- For `φ ∈ WP(X)` and a holomorphic map `g` from an open set `U` of a complex normed
space into `X`, the pull-back `φ ∘ g` satisfies the disc criterion on `U`. -/
theorem IsWeaklyPSHOn.discPshOn_comp {X : Set (ComplexModel n)} {φ : ComplexModel n → EReal}
    (hφ : IsWeaklyPSHOn X φ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} (hU : IsOpen U) {g : E → ComplexModel n} (hg : DifferentiableOn ℂ g U)
    (hgX : MapsTo g U X) : DiscPshOn (fun y => φ (g y)) U := by
  refine ⟨fun y hy => hφ.ne_top _ (hgX hy),
    hφ.upperSemicontinuousOn.comp hg.continuousOn hgX, ?_⟩
  intro x v r hr hD C hC
  by_cases hv : v = 0
  · subst v
    simpa only [circleDeficit, smul_zero, add_zero] using
      (circleDeficit_const (φ (g x)) x (0 : E) r C).le
  let L : ℂ → E := fun t => x + t • v
  have hLc : Continuous L := by fun_prop
  have hballU : closedBall (0 : ℂ) r ⊆ L ⁻¹' U := by
    intro t ht
    exact hD ⟨t, ht, rfl⟩
  obtain ⟨δ, hδ, hthick⟩ := (isCompact_closedBall (0 : ℂ) r).exists_thickening_subset_open
    (hU.preimage hLc) hballU
  rw [thickening_closedBall hδ hr.le] at hthick
  set R : ℝ := r + δ / 2 with hRdef
  have hR : 0 < R := by positivity
  have hrR : r < R := by linarith
  let f : ℂ → ComplexModel n := fun t => g (x + ((R : ℂ) * t) • v)
  have hmaps : MapsTo (fun t : ℂ => x + ((R : ℂ) * t) • v) (ball (0 : ℂ) 1) U := by
    intro t ht
    have h1 : ‖t‖ < 1 := mem_ball_zero_iff.mp ht
    have h2 : (R : ℂ) * t ∈ ball (0 : ℂ) (δ + r) := by
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
      calc R * ‖t‖ < R * 1 := mul_lt_mul_of_pos_left h1 hR
        _ = R := mul_one R
        _ < δ + r := by linarith
    exact hthick h2
  have hfd : DifferentiableOn ℂ f (ball (0 : ℂ) 1) := by
    have haff : Differentiable ℂ (fun t : ℂ => x + ((R : ℂ) * t) • v) := by fun_prop
    exact hg.comp haff.differentiableOn hmaps
  have hfX : MapsTo f (ball (0 : ℂ) 1) X := fun t ht => hgX (hmaps ht)
  have hw := hφ.disc f hfd hfX
  set ρ : ℝ := r / R with hρdef
  have hρ : 0 < ρ := div_pos hr hR
  have hρ1 : ρ < 1 := (div_lt_one hR).mpr hrR
  have hRρ : R * ρ = r := by rw [hρdef]; field_simp
  have hdisc0 : affineClosedDisc (0 : ℂ) 1 ρ ⊆ ball (0 : ℂ) 1 := by
    rintro _ ⟨s, hs, rfl⟩
    rw [mem_ball_zero_iff]
    have := mem_closedBall_zero_iff.mp hs
    simp only [smul_eq_mul, mul_one, zero_add]
    linarith
  have hbound : ∀ y ∈ affineClosedDisc (0 : ℂ) 1 ρ, φ (f y) ≤ (C : EReal) := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := hy
    apply hC
    refine ⟨(R : ℂ) * s, ?_, ?_⟩
    · rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
      have := mem_closedBall_zero_iff.mp hs
      calc R * ‖s‖ ≤ R * ρ := mul_le_mul_of_nonneg_left this hR.le
        _ = r := hRρ
    · simp
  have hmean := hw.submean 0 1 ρ hρ hdisc0 C hbound
  have hcirc : circleDeficit (fun t => φ (f t)) 0 1 ρ C =
      circleDeficit (fun y => φ (g y)) x v r C := by
    unfold circleDeficit
    apply MeasureTheory.lintegral_congr
    intro θ
    simp only [f, circleMap, smul_eq_mul, mul_one, zero_add]
    rw [← mul_assoc, ← Complex.ofReal_mul, hRρ]
  have hf0 : f 0 = g x := by simp [f]
  rw [← hcirc]
  simpa only [hf0] using hmean

/-- A disc-subharmonic function on `ℂ` is bounded at the centre of a disc by every real
upper bound on the punctured disc. -/
theorem le_of_forall_punctured_le {u : ℂ → EReal} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hu : DiscPshOn u (ball c R)) {C' : ℝ} (hC' : ∀ s ∈ ball c R, s ≠ c → u s ≤ C') :
    u c ≤ C' := by
  set r : ℝ := R / 2 with hrdef
  have hr : 0 < r := by positivity
  have hrR : r < R := by linarith
  have hD : affineClosedDisc c 1 r ⊆ ball c R := by
    rw [SGPT.PSH.affineClosedDisc_one]
    exact closedBall_subset_ball hrR
  obtain ⟨C, hC⟩ := hu.exists_disc_upper_bound c 1 hr.le hD
  set C₁ : ℝ := max C C' + 1 with hC₁def
  have hC₁ : ∀ y ∈ affineClosedDisc c 1 r, u y ≤ (C₁ : EReal) := by
    intro y hy
    refine (hC y hy).trans ?_
    exact EReal.coe_le_coe_iff.mpr (by rw [hC₁def]; linarith [le_max_left C C'])
  have hmean := hu.submean c 1 r hr hD C₁ hC₁
  have hlow : circleDeficit (fun _ : ℂ => (C' : EReal)) c 1 r C₁ ≤ circleDeficit u c 1 r C₁ := by
    apply circleDeficit_antitone
    intro t
    apply hC'
    · rw [mem_ball, dist_eq_norm, smul_eq_mul, mul_one, add_sub_cancel_left,
        norm_circleMap_zero, abs_of_pos hr]
      exact hrR
    · intro h
      have h0 : circleMap 0 r t = 0 := by
        have := congrArg (fun z => z - c) h
        simpa [smul_eq_mul] using this
      have := congrArg norm h0
      rw [norm_circleMap_zero, abs_of_pos hr, norm_zero] at this
      exact hr.ne' this
  rw [circleDeficit_const] at hlow
  have h2π : ENNReal.ofReal (2 * Real.pi) ≠ 0 := by
    simp [Real.pi_pos]
  have hle := (ENNReal.mul_le_mul_iff_right h2π ENNReal.ofReal_ne_top).mp (hlow.trans hmean)
  by_contra hlt
  push Not at hlt
  have hne_bot : u c ≠ ⊥ := ne_bot_of_gt hlt
  have hne_top : u c ≠ ⊤ := hu.ne_top c (mem_ball_self hR)
  set a : ℝ := (u c).toReal with hadef
  have ha : u c = (a : EReal) := (EReal.coe_toReal hne_top hne_bot).symm
  rw [ha] at hlt hle
  have hlt' : C' < a := EReal.coe_lt_coe_iff.mp hlt
  rw [← EReal.coe_sub, ← EReal.coe_sub, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _),
    EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe, EReal.toReal_coe] at hle
  have hpos : 0 < C₁ - C' := by rw [hC₁def]; linarith [le_max_right C C']
  rcases le_or_gt 0 (C₁ - a) with hnn | hneg
  · have := (ENNReal.ofReal_le_ofReal_iff hnn).mp hle
    linarith
  · rw [ENNReal.ofReal_of_nonpos hneg.le] at hle
    have := ENNReal.ofReal_pos.mpr hpos
    exact absurd hle (not_le.mpr this)

end SGPT.Unibranch.FNL
