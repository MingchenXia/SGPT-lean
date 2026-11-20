import SGPT.Foundations.Analysis.Pending.StokesCutoff
import SGPT.Foundations.Analysis.FirstPass.SmoothPshHessian
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorDecreasing

/-!
# Smooth functions of a difference as differences of decreasing PSH weights

The bounded-weight passage in Hermitian comparison can use the existing
one-PSH-weight Bedford--Taylor continuity theorem. On a bounded nonnegative
rectangle, adding `C(s²+t²)+A(s+t)` makes `H(t-s)` convex and increasing in
each coordinate, for suitable bounds on `H'` and `H''`. This module develops
the actual Levi estimates for that construction.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparisonWeights

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.LocalProductCurrents
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorContinuity
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorDecreasing
open Set Filter TopologicalSpace
open scoped ContDiff Topology Distributions

variable {n : ℕ}

/-- The quadratic correction used for both decreasing PSH weights. -/
def correction (C A s t : ℝ) : ℝ := C * (s ^ 2 + t ^ 2) + A * (s + t)

/-- The corrected smooth function of the actual difference. -/
def corrected (H : ℝ → ℝ) (C A s t : ℝ) : ℝ :=
  H (t - s) + C * (s ^ 2 + t ^ 2) + A * (s + t)

theorem leviForm_sq {u : ComplexModel n → ℝ} {z : ComplexModel n}
    (hu : ContDiffAt ℝ 2 u z) (ξ : ComplexModel n) :
    leviForm (fun y => u y ^ 2) z ξ = 2 * u z * leviForm u z ξ +
      (fderiv ℝ u z ξ ^ 2 + fderiv ℝ u z (Complex.I • ξ) ^ 2) / 2 := by
  have hθ : ContDiffAt ℝ 2 (fun t : ℝ => t ^ 2) (u z) := (contDiff_id.pow 2).contDiffAt
  have h := StokesCutoff.leviForm_comp hθ hu ξ
  have hd : deriv (fun t : ℝ => t ^ 2) = fun t => 2 * t := by
    funext t
    simp
  have hd₂ : deriv (fun t : ℝ => 2 * t) (u z) = 2 := by
    simp
  rw [hd, hd₂] at h
  convert h using 1
  ring

/-- The complete Levi identity retains the two independent first derivatives
and the genuine squared-gradient term of the difference. -/
theorem levi_corrected_eq {H : ℝ → ℝ} {u v : ComplexModel n → ℝ}
    {z : ComplexModel n} (hH : ContDiffAt ℝ 2 H (v z - u z))
    (hu : ContDiffAt ℝ 2 u z) (hv : ContDiffAt ℝ 2 v z) (C A : ℝ)
    (ξ : ComplexModel n) :
    leviForm (fun y => corrected H C A (u y) (v y)) z ξ =
      (A + 2 * C * u z - deriv H (v z - u z)) * leviForm u z ξ +
      (A + 2 * C * v z + deriv H (v z - u z)) * leviForm v z ξ +
      C / 2 * (fderiv ℝ u z ξ ^ 2 + fderiv ℝ u z (Complex.I • ξ) ^ 2 +
        fderiv ℝ v z ξ ^ 2 + fderiv ℝ v z (Complex.I • ξ) ^ 2) +
      deriv (deriv H) (v z - u z) / 4 *
        ((fderiv ℝ v z ξ - fderiv ℝ u z ξ) ^ 2 +
          (fderiv ℝ v z (Complex.I • ξ) - fderiv ℝ u z (Complex.I • ξ)) ^ 2) := by
  have hdiff : ContDiffAt ℝ 2 (fun y => v y - u y) z := hv.sub hu
  have hcomp : ContDiffAt ℝ 2 (fun y => H (v y - u y)) z := hH.comp z hdiff
  have hquad : ContDiffAt ℝ 2 (fun y => u y ^ 2 + v y ^ 2) z := (hu.pow 2).add (hv.pow 2)
  have hlinear : ContDiffAt ℝ 2 (u + v) z := hu.add hv
  have hLdiff : leviForm (fun y => v y - u y) z ξ =
      leviForm v z ξ - leviForm u z ξ := by
    have heq : (fun y => v y - u y) = v + -u := by funext y; simp [sub_eq_add_neg]
    rw [heq, leviForm_add (u := v) (v := -u) hv hu.neg, leviForm_neg]
    rfl
  have hDdiff : fderiv ℝ (fun y => v y - u y) z = fderiv ℝ v z - fderiv ℝ u z :=
    (hv.differentiableAt (by norm_num)).hasFDerivAt.sub
      (hu.differentiableAt (by norm_num)).hasFDerivAt |>.fderiv
  have hLquad : leviForm (fun y => u y ^ 2 + v y ^ 2) z ξ =
      leviForm (fun y => u y ^ 2) z ξ + leviForm (fun y => v y ^ 2) z ξ :=
    leviForm_add (u := fun y => u y ^ 2) (v := fun y => v y ^ 2) (hu.pow 2) (hv.pow 2) ξ
  change leviForm ((fun y => H (v y - u y)) +
    C • (fun y => u y ^ 2 + v y ^ 2) + A • (u + v)) z ξ = _
  rw [leviForm_add
      (u := (fun y => H (v y - u y)) + C • (fun y => u y ^ 2 + v y ^ 2))
      (v := A • (u + v)) (hcomp.add (hquad.const_smul C)) (hlinear.const_smul A),
    leviForm_add (u := fun y => H (v y - u y))
      (v := C • fun y => u y ^ 2 + v y ^ 2) hcomp (hquad.const_smul C),
    leviForm_smul (u := fun y => u y ^ 2 + v y ^ 2) hquad C,
    leviForm_smul (u := u + v) hlinear A, leviForm_add hu hv,
    hLquad, leviForm_sq hu, leviForm_sq hv,
    StokesCutoff.leviForm_comp (θ := H) (f := fun y => v y - u y) hH hdiff, hLdiff, hDdiff]
  simp only [sub_apply]
  ring

/-- The actual corrected composite has nonnegative Levi form. The derivative
bounds are pointwise, so local uniform bounds on a rectangle instantiate it
without an assumed convexity or PSH certificate. -/
theorem levi_convexified_difference_nonneg {H : ℝ → ℝ} {u v : ComplexModel n → ℝ}
    {z : ComplexModel n} (hH : ContDiffAt ℝ 2 H (v z - u z))
    (hu : ContDiffAt ℝ 2 u z) (hv : ContDiffAt ℝ 2 v z)
    {C A : ℝ} (hC : 0 ≤ C) (hu₀ : 0 ≤ u z) (hv₀ : 0 ≤ v z)
    (hA : |deriv H (v z - u z)| ≤ A) (hC₂ : |deriv (deriv H) (v z - u z)| ≤ C)
    (ξ : ComplexModel n) (hLu : 0 ≤ leviForm u z ξ) (hLv : 0 ≤ leviForm v z ξ) :
    0 ≤ leviForm (fun y => corrected H C A (u y) (v y)) z ξ := by
  rw [levi_corrected_eq hH hu hv]
  have hA' := abs_le.mp hA
  have hC' := abs_le.mp hC₂
  have hfirst : 0 ≤ A + 2 * C * u z - deriv H (v z - u z) := by
    nlinarith [mul_nonneg hC hu₀]
  have hsecond : 0 ≤ A + 2 * C * v z + deriv H (v z - u z) := by
    nlinarith [mul_nonneg hC hv₀]
  let P := fderiv ℝ u z ξ ^ 2 + fderiv ℝ u z (Complex.I • ξ) ^ 2 +
    fderiv ℝ v z ξ ^ 2 + fderiv ℝ v z (Complex.I • ξ) ^ 2
  let Q := (fderiv ℝ v z ξ - fderiv ℝ u z ξ) ^ 2 +
    (fderiv ℝ v z (Complex.I • ξ) - fderiv ℝ u z (Complex.I • ξ)) ^ 2
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hQP : Q ≤ 2 * P := by
    dsimp [Q, P]
    nlinarith [sq_nonneg (fderiv ℝ v z ξ + fderiv ℝ u z ξ),
      sq_nonneg (fderiv ℝ v z (Complex.I • ξ) + fderiv ℝ u z (Complex.I • ξ))]
  have hgrad : 0 ≤ C / 2 * P + deriv (deriv H) (v z - u z) / 4 * Q := by
    have h1 := mul_le_mul_of_nonneg_right hC'.1 hQ
    have h2 := mul_le_mul_of_nonneg_left hQP hC
    nlinarith
  dsimp [P, Q] at hgrad
  linarith [mul_nonneg hfirst hLu, mul_nonneg hsecond hLv]

/-- The actual first partial derivative in the first real variable. -/
theorem hasDerivAt_corrected_left {H : ℝ → ℝ} {s t : ℝ}
    (hH : DifferentiableAt ℝ H (t - s)) (C A : ℝ) :
    HasDerivAt (fun r => corrected H C A r t)
      (-deriv H (t - s) + 2 * C * s + A) s := by
  have h1 := hH.hasDerivAt.comp s ((hasDerivAt_const s t).sub (hasDerivAt_id s))
  have h2 := ((hasDerivAt_pow 2 s).add_const (t ^ 2)).const_mul C
  have h3 := ((hasDerivAt_id s).add_const t).const_mul A
  convert (h1.add h2).add h3 using 1
  all_goals first | rfl | (dsimp [corrected]; ring)

/-- The actual first partial derivative in the second real variable. -/
theorem hasDerivAt_corrected_right {H : ℝ → ℝ} {s t : ℝ}
    (hH : DifferentiableAt ℝ H (t - s)) (C A : ℝ) :
    HasDerivAt (fun r => corrected H C A s r)
      (deriv H (t - s) + 2 * C * t + A) t := by
  have h1 := hH.hasDerivAt.comp t ((hasDerivAt_id t).sub_const s)
  have h2 := ((hasDerivAt_pow 2 t).const_add (s ^ 2)).const_mul C
  have h3 := ((hasDerivAt_id t).const_add s).const_mul A
  convert (h1.add h2).add h3 using 1
  all_goals first | rfl | (dsimp [corrected]; ring)

/-- The correction makes the first-variable dependence increasing on the
same bounded nonnegative rectangle used by the smooth approximations. -/
theorem corrected_monotoneOn_left {H : ℝ → ℝ} (hH : Differentiable ℝ H)
    {C A M t : ℝ} (hC : 0 ≤ C) (ht : t ∈ Set.Icc 0 M)
    (hA : ∀ r ∈ Set.Icc (-M) M, |deriv H r| ≤ A) :
    MonotoneOn (fun s => corrected H C A s t) (Set.Icc 0 M) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun s =>
    -deriv H (t - s) + 2 * C * s + A) (convex_Icc 0 M)
  · intro s _
    exact (hasDerivAt_corrected_left (hH _) C A).continuousAt.continuousWithinAt
  · intro s _
    exact (hasDerivAt_corrected_left (hH _) C A).hasDerivWithinAt
  · intro s hs
    have hs' : s ∈ Set.Icc 0 M := interior_subset hs
    have hdiff : t - s ∈ Set.Icc (-M) M := ⟨by linarith [ht.1, hs'.2], by linarith [ht.2, hs'.1]⟩
    have hbound := (abs_le.mp (hA _ hdiff)).2
    nlinarith [mul_nonneg hC hs'.1]

/-- The same corrected function is increasing in the second variable. -/
theorem corrected_monotoneOn_right {H : ℝ → ℝ} (hH : Differentiable ℝ H)
    {C A M s : ℝ} (hC : 0 ≤ C) (hs : s ∈ Set.Icc 0 M)
    (hA : ∀ r ∈ Set.Icc (-M) M, |deriv H r| ≤ A) :
    MonotoneOn (fun t => corrected H C A s t) (Set.Icc 0 M) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t =>
    deriv H (t - s) + 2 * C * t + A) (convex_Icc 0 M)
  · intro t _
    exact (hasDerivAt_corrected_right (hH _) C A).continuousAt.continuousWithinAt
  · intro t _
    exact (hasDerivAt_corrected_right (hH _) C A).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Set.Icc 0 M := interior_subset ht
    have hdiff : t - s ∈ Set.Icc (-M) M := ⟨by linarith [ht'.1, hs.2], by linarith [ht'.2, hs.1]⟩
    have hbound := (abs_le.mp (hA _ hdiff)).1
    nlinarith [mul_nonneg hC ht'.1]

/-- Actual decreasing input sequences give a decreasing corrected weight;
no monotonicity of the original smooth difference weight is assumed. -/
theorem corrected_antitone {H : ℝ → ℝ} (hH : Differentiable ℝ H)
    {C A M : ℝ} (hC : 0 ≤ C)
    (hA : ∀ r ∈ Set.Icc (-M) M, |deriv H r| ≤ A)
    {u v : ℕ → ℝ} (hu : ∀ j, u j ∈ Set.Icc 0 M) (hv : ∀ j, v j ∈ Set.Icc 0 M)
    (hanti_u : Antitone u) (hanti_v : Antitone v) :
    Antitone (fun j => corrected H C A (u j) (v j)) := by
  intro i j hij
  exact (corrected_monotoneOn_left hH hC (hv j) hA (hu j) (hu i) (hanti_u hij)).trans
    (corrected_monotoneOn_right hH hC (hu i) hA (hv j) (hv i) (hanti_v hij))

private theorem pshOn_of_smooth_levi {U : Opens (ComplexModel n)}
    {f : ComplexModel n → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    (hL : ∀ z ∈ U, ∀ ξ, 0 ≤ leviForm f z ξ) :
    PlurisubharmonicOn (fun z => (f z : EReal)) U := by
  intro x hx
  obtain ⟨g, hg, heq⟩ := exists_contDiff_eventuallyEq_of_contDiffOn U.isOpen hf hx
  obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp (inter_mem heq (U.isOpen.mem_nhds hx))
  have hgL : ∀ y ∈ V, ∀ ξ, 0 ≤ leviForm g y ξ := by
    intro y hy ξ
    have hl : f =ᶠ[𝓝 y] g := by
      filter_upwards [hV.mem_nhds hy] with z hz
      exact (hVsub hz).1
    have h2 : fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ g) y :=
      (hl.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
    simpa only [leviForm, realHessian_eq_fderiv, h2] using hL y (hVsub hy).2 ξ
  apply ((plurisubharmonicOn_of_levi_nonneg
    (hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hV hgL) x hxV).congr
  filter_upwards [hV.mem_nhds hxV] with y hy
  exact congrArg ((↑) : ℝ → EReal) (hVsub hy).1.symm

/-- Smoothness only on the actual open set supplies the local boundedness
required by Bedford--Taylor theory. -/
theorem locallyBoundedPshOn_of_smooth {U : Opens (ComplexModel n)}
    {f : ComplexModel n → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    (hpsh : PlurisubharmonicOn (fun z => (f z : EReal)) U) :
    IsLocallyBoundedPshOn U f := by
  refine ⟨hpsh, ?_⟩
  intro x hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp U.isOpen x hx
  have hr₂ : 0 < r / 2 := by linarith
  have hclosed : Metric.closedBall x (r / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨C, hC⟩ := (isCompact_closedBall x (r / 2)).exists_bound_of_continuousOn
    (hf.continuousOn.mono hclosed)
  refine ⟨⟨Metric.ball x (r / 2), Metric.isOpen_ball⟩, Metric.mem_ball_self hr₂,
    (Metric.ball_subset_closedBall.trans hclosed), C, ?_⟩
  intro y hy
  simpa only [Real.norm_eq_abs] using hC y (Metric.ball_subset_closedBall hy)

/-- The corrected weight is internally proved to be locally bounded PSH from
the actual smooth PSH inputs and derivative bounds. -/
theorem corrected_locallyBoundedPshOn {U : Opens (ComplexModel n)}
    {H : ℝ → ℝ} {u v : ComplexModel n → ℝ} (hH : ContDiff ℝ ∞ H)
    (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U)
    (hup : PlurisubharmonicOn (fun z => (u z : EReal)) U)
    (hvp : PlurisubharmonicOn (fun z => (v z : EReal)) U)
    {C A : ℝ} (hC : 0 ≤ C) (hu₀ : ∀ z ∈ U, 0 ≤ u z) (hv₀ : ∀ z ∈ U, 0 ≤ v z)
    (hA : ∀ z ∈ U, |deriv H (v z - u z)| ≤ A)
    (hC₂ : ∀ z ∈ U, |deriv (deriv H) (v z - u z)| ≤ C) :
    IsLocallyBoundedPshOn U (fun z => corrected H C A (u z) (v z)) := by
  have hs : ContDiffOn ℝ ∞ (fun z => corrected H C A (u z) (v z)) U :=
    ((hH.comp_contDiffOn (hv.sub hu)).add (((hu.pow 2).add (hv.pow 2)).const_smul C)).add
      ((hu.add hv).const_smul A)
  apply locallyBoundedPshOn_of_smooth hs
  apply pshOn_of_smooth_levi hs
  intro z hz ξ
  have hu₂ := ((hu z hz).contDiffAt (U.isOpen.mem_nhds hz)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hv₂ := ((hv z hz).contDiffAt (U.isOpen.mem_nhds hz)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  exact levi_convexified_difference_nonneg
    (hH.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hu₂ hv₂ hC
    (hu₀ z hz) (hv₀ z hz) (hA z hz) (hC₂ z hz) ξ
    (leviForm_nonneg_of_contDiffOn_plurisubharmonicOn hu hup hz ξ)
    (leviForm_nonneg_of_contDiffOn_plurisubharmonicOn hv hvp hz ξ)

/-- A bounded real decreasing PSH family has its actual pointwise limit in
the same locally bounded PSH domain. The PSH conclusion is produced, not
supplied as a certificate for the new weight. -/
theorem locallyBoundedPshOn_limit_of_antitone {U : Opens (ComplexModel n)}
    {f : ℕ → ComplexModel n → ℝ} {f₀ : ComplexModel n → ℝ}
    (hf : ∀ j, IsLocallyBoundedPshOn U (f j))
    (hanti : ∀ z ∈ U, Antitone fun j => f j z)
    (hlim : ∀ z ∈ U, Tendsto (fun j => f j z) atTop (𝓝 (f₀ z)))
    (hbound : ∃ M : ℝ, ∀ j z, z ∈ U → |f j z| ≤ M) :
    IsLocallyBoundedPshOn U f₀ := by
  have hantiE : ∀ z ∈ U, Antitone fun j => (f j z : EReal) :=
    fun z hz i j hij => EReal.coe_le_coe_iff.mpr (hanti z hz hij)
  have heq : ∀ z ∈ U, (⨅ j, (f j z : EReal)) = (f₀ z : EReal) := by
    intro z hz
    exact tendsto_nhds_unique (tendsto_atTop_iInf (hantiE z hz))
      (EReal.tendsto_coe.mpr (hlim z hz))
  have hpsh := DiscPshOn.plurisubharmonicOn_iInf_of_antitone U.isOpen
    (fun j => (hf j).1.discPshOn) hantiE
  refine ⟨?_, ?_⟩
  · intro x hx
    apply (hpsh x hx).congr
    filter_upwards [U.isOpen.mem_nhds hx] with y hy
    exact heq y hy
  · obtain ⟨M, hM⟩ := hbound
    intro x hx
    refine ⟨U, hx, le_rfl, M, ?_⟩
    intro y hy
    exact le_of_tendsto' ((continuous_abs.tendsto (f₀ y)).comp (hlim y hy))
      (fun j => hM j y hy)

/-- Multiplication by bounded Borel weights is genuinely linear in a
difference, including signed weights. -/
theorem mulBorel_sub {U : Opens (ComplexModel n)} {q : ℕ}
    {S : LocalProductCurrent n U q} (hS : IsPositive S)
    {f g : ComplexModel n → ℝ} (hf : Measurable f) (hfb : IsLocallyBoundedOn f U)
    (hg : Measurable g) (hgb : IsLocallyBoundedOn g U) :
    mulBorel S (f - g) = mulBorel S f - mulBorel S g := by
  have hb : IsLocallyBoundedOn (f - g) U := by
    intro K hK hKU
    obtain ⟨B, hB⟩ := hfb K hK hKU
    obtain ⟨C, hC⟩ := hgb K hK hKU
    refine ⟨B + C, fun x hx => ?_⟩
    have h := abs_sub_le (f x) 0 (g x)
    simp only [sub_zero, zero_sub, abs_neg] at h
    exact h.trans (add_le_add (hB x hx) (hC x hx))
  have h := mulBorel_add hS (hf.sub hg) hb hg hgb
  have heq : (f - g) + g = f := by ext x; simp
  rw [heq] at h
  exact eq_sub_iff_add_eq.mpr h.symm

private theorem mulBorel_indicator_sub {U : Opens (ComplexModel n)} {q : ℕ}
    {S : LocalProductCurrent n U q} (hS : IsPositive S)
    {f g : ComplexModel n → ℝ} (hf : IsLocallyBoundedPshOn U f)
    (hg : IsLocallyBoundedPshOn U g) :
    mulBorel S ((U : Set (ComplexModel n)).indicator (f - g)) =
      mulBorel S ((U : Set (ComplexModel n)).indicator f) -
        mulBorel S ((U : Set (ComplexModel n)).indicator g) := by
  have heq : (U : Set (ComplexModel n)).indicator (f - g) =
      (U : Set (ComplexModel n)).indicator f - (U : Set (ComplexModel n)).indicator g := by
    ext x
    by_cases hx : x ∈ U <;> simp [hx]
  rw [heq]
  exact mulBorel_sub hS (measurable_indicator_of_isLocallyBoundedPshOn hf)
    (isLocallyBoundedOn_indicator hf) (measurable_indicator_of_isLocallyBoundedPshOn hg)
    (isLocallyBoundedOn_indicator hg)

/-- The actual Bedford--Taylor products converge with the difference of two
decreasing PSH weights. This is applied to the internally constructed corrected
weight and its quadratic correction, so the uncorrected smooth difference
weight need not itself be PSH or monotone. -/
theorem weakTendsto_mulBorel_difference_weights {U : Opens (ComplexModel n)}
    (q m : ℕ) (T : LocalProductCurrent n U (m + q))
    (hT : IsPositive T) (hTc : IsClosedAny (m + q) T)
    (u : ℕ → Fin q → ComplexModel n → ℝ) (u₀ : Fin q → ComplexModel n → ℝ)
    (hu : ∀ j i, IsLocallyBoundedPshOn U (u j i))
    (hu₀ : ∀ i, IsLocallyBoundedPshOn U (u₀ i))
    (hanti : ∀ i z, z ∈ U → Antitone fun j => u j i z)
    (hlim : ∀ i z, z ∈ U → Tendsto (fun j => u j i z) atTop (𝓝 (u₀ i z)))
    (f g : ℕ → ComplexModel n → ℝ) (f₀ g₀ : ComplexModel n → ℝ)
    (hf : ∀ j, IsLocallyBoundedPshOn U (f j)) (hf₀ : IsLocallyBoundedPshOn U f₀)
    (hg : ∀ j, IsLocallyBoundedPshOn U (g j)) (hg₀ : IsLocallyBoundedPshOn U g₀)
    (hanti_f : ∀ z ∈ U, Antitone fun j => f j z)
    (hanti_g : ∀ z ∈ U, Antitone fun j => g j z)
    (hlim_f : ∀ z ∈ U, Tendsto (fun j => f j z) atTop (𝓝 (f₀ z)))
    (hlim_g : ∀ z ∈ U, Tendsto (fun j => g j z) atTop (𝓝 (g₀ z))) :
    WeakTendsto (fun j => mulBorel (btProduct q m (u j) T)
        ((U : Set (ComplexModel n)).indicator (f j - g j)))
      (mulBorel (btProduct q m u₀ T) ((U : Set (ComplexModel n)).indicator (f₀ - g₀))) := by
  have hweight (w : ℕ → ComplexModel n → ℝ) (w₀ : ComplexModel n → ℝ)
      (hw : ∀ j, IsLocallyBoundedPshOn U (w j)) (hw₀ : IsLocallyBoundedPshOn U w₀)
      (hanti_w : ∀ z ∈ U, Antitone fun j => w j z)
      (hlim_w : ∀ z ∈ U, Tendsto (fun j => w j z) atTop (𝓝 (w₀ z))) :
      WeakTendsto (fun j => mulBorel (btProduct q m (u j) T)
        ((U : Set (ComplexModel n)).indicator (w j)))
        (mulBorel (btProduct q m u₀ T) ((U : Set (ComplexModel n)).indicator w₀)) := by
    have h := weakTendsto_mulBorel_btProduct_of_antitone q m T hT hTc
      (fun j => Fin.cons (w j) (u j)) (Fin.cons w₀ u₀)
      (fun j i => Fin.cases (hw j) (fun k => hu j k) i)
      (fun i => Fin.cases hw₀ (fun k => hu₀ k) i)
      (fun i => Fin.cases hanti_w (fun k => hanti k) i)
      (fun i => Fin.cases hlim_w (fun k => hlim k) i)
    simpa only [Fin.tail_cons, Fin.cons_zero] using h
  have hF := hweight f f₀ hf hf₀ hanti_f hlim_f
  have hG := hweight g g₀ hg hg₀ hanti_g hlim_g
  intro γ φ
  have hprod (j : ℕ) : IsPositive (btProduct q m (u j) T) :=
    (isPositive_btProduct q m (u j) T hT hTc (hu j)).1
  have hprod₀ : IsPositive (btProduct q m u₀ T) :=
    (isPositive_btProduct q m u₀ T hT hTc hu₀).1
  simp only [mulBorel_indicator_sub (hprod _) (hf _) (hg _),
    mulBorel_indicator_sub hprod₀ hf₀ hg₀, LinearMap.sub_apply, sub_apply]
  exact (hF γ φ).sub (hG γ φ)

/-- Uniform bounds for the actual quadratic correction on the same rectangle. -/
theorem correction_bounds {C A M s t : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hs : s ∈ Icc 0 M) (ht : t ∈ Icc 0 M) :
    0 ≤ correction C A s t ∧ correction C A s t ≤ 2 * C * M ^ 2 + 2 * A * M := by
  have hM : 0 ≤ M := hs.1.trans hs.2
  have hs₂ : s ^ 2 ≤ M ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (add_nonneg hM hs.1)]
  have ht₂ : t ^ 2 ≤ M ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (add_nonneg hM ht.1)]
  dsimp [correction]
  constructor
  · exact add_nonneg (mul_nonneg hC (add_nonneg (sq_nonneg _) (sq_nonneg _)))
      (mul_nonneg hA (add_nonneg hs.1 ht.1))
  · have h1 := mul_le_mul_of_nonneg_left (add_le_add hs₂ ht₂) hC
    have h2 := mul_le_mul_of_nonneg_left (add_le_add hs.2 ht.2) hA
    nlinarith

/-- The corrected smooth difference weight has a uniform absolute bound on
the input rectangle, independent of the approximation index. -/
theorem corrected_abs_le {H : ℝ → ℝ} {C A M B s t : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hs : s ∈ Icc 0 M) (ht : t ∈ Icc 0 M)
    (hH : ∀ r ∈ Icc (-M) M, |H r| ≤ B) :
    |corrected H C A s t| ≤ B + (2 * C * M ^ 2 + 2 * A * M) := by
  have hdiff : t - s ∈ Icc (-M) M := ⟨by linarith [ht.1, hs.2], by linarith [ht.2, hs.1]⟩
  have hR := correction_bounds hC hA hs ht
  have heq : corrected H C A s t = H (t - s) + correction C A s t := by
    dsimp [corrected, correction]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add (hH _ hdiff)
    (by rw [abs_of_nonneg hR.1]; exact hR.2))

/-- Genuine moving Bedford--Taylor products converge with a smooth function
of the difference of two bounded decreasing smooth PSH sequences. The two
PSH weights used in the proof, including their limit regularity, are all
constructed internally from the given functions and derivative bounds. -/
theorem weakTendsto_smooth_difference_weight_of_bounds {U : Opens (ComplexModel n)}
    (q m : ℕ) (T : LocalProductCurrent n U (m + q))
    (hT : IsPositive T) (hTc : IsClosedAny (m + q) T)
    (u : ℕ → Fin q → ComplexModel n → ℝ) (u₀ : Fin q → ComplexModel n → ℝ)
    (hu : ∀ j i, IsLocallyBoundedPshOn U (u j i))
    (hu₀ : ∀ i, IsLocallyBoundedPshOn U (u₀ i))
    (hanti : ∀ i z, z ∈ U → Antitone fun j => u j i z)
    (hlim : ∀ i z, z ∈ U → Tendsto (fun j => u j i z) atTop (𝓝 (u₀ i z)))
    (a b : ℕ → ComplexModel n → ℝ) (a₀ b₀ : ComplexModel n → ℝ)
    (has : ∀ j, ContDiffOn ℝ ∞ (a j) U) (hbs : ∀ j, ContDiffOn ℝ ∞ (b j) U)
    (hap : ∀ j, PlurisubharmonicOn (fun z => (a j z : EReal)) U)
    (hbp : ∀ j, PlurisubharmonicOn (fun z => (b j z : EReal)) U)
    (hanti_a : ∀ z ∈ U, Antitone fun j => a j z)
    (hanti_b : ∀ z ∈ U, Antitone fun j => b j z)
    (hlim_a : ∀ z ∈ U, Tendsto (fun j => a j z) atTop (𝓝 (a₀ z)))
    (hlim_b : ∀ z ∈ U, Tendsto (fun j => b j z) atTop (𝓝 (b₀ z)))
    {H : ℝ → ℝ} (hH : ContDiff ℝ ∞ H) {C A M B : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hbox_a : ∀ j z, z ∈ U → a j z ∈ Icc 0 M)
    (hbox_b : ∀ j z, z ∈ U → b j z ∈ Icc 0 M)
    (hH₀ : ∀ r ∈ Icc (-M) M, |H r| ≤ B)
    (hH₁ : ∀ r ∈ Icc (-M) M, |deriv H r| ≤ A)
    (hH₂ : ∀ r ∈ Icc (-M) M, |deriv (deriv H) r| ≤ C) :
    WeakTendsto (fun j => mulBorel (btProduct q m (u j) T)
        ((U : Set (ComplexModel n)).indicator (fun z => H (b j z - a j z))))
      (mulBorel (btProduct q m u₀ T)
        ((U : Set (ComplexModel n)).indicator (fun z => H (b₀ z - a₀ z)))) := by
  let G : ℕ → ComplexModel n → ℝ := fun j z => corrected H C A (a j z) (b j z)
  let R : ℕ → ComplexModel n → ℝ := fun j z => correction C A (a j z) (b j z)
  let G₀ : ComplexModel n → ℝ := fun z => corrected H C A (a₀ z) (b₀ z)
  let R₀ : ComplexModel n → ℝ := fun z => correction C A (a₀ z) (b₀ z)
  have hdiff (j : ℕ) (z : ComplexModel n) (hz : z ∈ U) : b j z - a j z ∈ Icc (-M) M :=
    ⟨by linarith [(hbox_b j z hz).1, (hbox_a j z hz).2],
      by linarith [(hbox_b j z hz).2, (hbox_a j z hz).1]⟩
  have hGp : ∀ j, IsLocallyBoundedPshOn U (G j) := fun j =>
    corrected_locallyBoundedPshOn hH (has j) (hbs j) (hap j) (hbp j) hC
      (fun z hz => (hbox_a j z hz).1) (fun z hz => (hbox_b j z hz).1)
      (fun z hz => hH₁ _ (hdiff j z hz)) (fun z hz => hH₂ _ (hdiff j z hz))
  have hRp : ∀ j, IsLocallyBoundedPshOn U (R j) := by
    intro j
    have h := corrected_locallyBoundedPshOn (H := fun _ => 0) contDiff_const
      (has j) (hbs j) (hap j) (hbp j) hC
      (fun z hz => (hbox_a j z hz).1) (fun z hz => (hbox_b j z hz).1)
      (fun _ _ => by simpa using hA) (fun _ _ => by simpa using hC)
    simpa only [R, corrected, correction, zero_add] using h
  have hGanti : ∀ z ∈ U, Antitone fun j => G j z := fun z hz =>
    corrected_antitone (hH.differentiable (by simp)) hC hH₁
      (fun j => hbox_a j z hz) (fun j => hbox_b j z hz) (hanti_a z hz) (hanti_b z hz)
  have hRanti : ∀ z ∈ U, Antitone fun j => R j z := by
    intro z hz
    have h := corrected_antitone (H := fun _ => 0) (differentiable_const (0 : ℝ)) hC
      (fun _ _ => by simpa using hA) (fun j => hbox_a j z hz) (fun j => hbox_b j z hz)
      (hanti_a z hz) (hanti_b z hz)
    simpa only [R, corrected, correction, zero_add] using h
  have hRlim : ∀ z ∈ U, Tendsto (fun j => R j z) atTop (𝓝 (R₀ z)) := by
    intro z hz
    exact (((hlim_a z hz).pow 2).add ((hlim_b z hz).pow 2)).const_mul C |>.add
      (((hlim_a z hz).add (hlim_b z hz)).const_mul A)
  have hGlim : ∀ z ∈ U, Tendsto (fun j => G j z) atTop (𝓝 (G₀ z)) := by
    intro z hz
    have h := (hH.continuous.tendsto (b₀ z - a₀ z)).comp ((hlim_b z hz).sub (hlim_a z hz))
    simpa only [G, G₀, R, R₀, corrected, correction, add_assoc, Function.comp_apply] using
      h.add (hRlim z hz)
  have hG₀ : IsLocallyBoundedPshOn U G₀ := locallyBoundedPshOn_limit_of_antitone hGp
    hGanti hGlim ⟨B + (2 * C * M ^ 2 + 2 * A * M), fun j z hz =>
      corrected_abs_le hC hA (hbox_a j z hz) (hbox_b j z hz) hH₀⟩
  have hR₀ : IsLocallyBoundedPshOn U R₀ := locallyBoundedPshOn_limit_of_antitone hRp
    hRanti hRlim ⟨2 * C * M ^ 2 + 2 * A * M, fun j z hz => by
      have hR := correction_bounds hC hA (hbox_a j z hz) (hbox_b j z hz)
      change |correction C A (a j z) (b j z)| ≤ _
      rw [abs_of_nonneg hR.1]
      exact hR.2⟩
  have h := weakTendsto_mulBorel_difference_weights q m T hT hTc u u₀ hu hu₀ hanti hlim
    G R G₀ R₀ hGp hG₀ hRp hR₀ hGanti hRanti hGlim hRlim
  have heq (s t : ComplexModel n → ℝ) :
      (fun z => corrected H C A (s z) (t z)) -
          (fun z => correction C A (s z) (t z)) = fun z => H (t z - s z) := by
    ext z
    dsimp [corrected, correction]
    ring
  simpa only [G, R, G₀, R₀, heq] using h

/-- The constants for the convexification are produced from genuine smoothness
on a compact interval. They are not additional analytic assumptions. -/
theorem exists_smooth_weight_bounds {H : ℝ → ℝ} (hH : ContDiff ℝ ∞ H) (M : ℝ) :
    ∃ C A B : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
      (∀ r ∈ Icc (-M) M, |H r| ≤ B) ∧
      (∀ r ∈ Icc (-M) M, |deriv H r| ≤ A) ∧
      (∀ r ∈ Icc (-M) M, |deriv (deriv H) r| ≤ C) := by
  have hH₁ : ContDiff ℝ ∞ (deriv H) := (contDiff_infty_iff_deriv.mp hH).2
  have hH₂ : ContDiff ℝ ∞ (deriv (deriv H)) := (contDiff_infty_iff_deriv.mp hH₁).2
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (-M) M)).exists_bound_of_continuousOn
    hH.continuous.continuousOn
  obtain ⟨A, hA⟩ := (isCompact_Icc : IsCompact (Icc (-M) M)).exists_bound_of_continuousOn
    hH₁.continuous.continuousOn
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (-M) M)).exists_bound_of_continuousOn
    hH₂.continuous.continuousOn
  refine ⟨max 0 C, max 0 A, max 0 B, le_max_left _ _, le_max_left _ _, ?_, ?_, ?_⟩
  · intro r hr
    simpa only [Real.norm_eq_abs] using (hB r hr).trans (le_max_right 0 B)
  · intro r hr
    simpa only [Real.norm_eq_abs] using (hA r hr).trans (le_max_right 0 A)
  · intro r hr
    simpa only [Real.norm_eq_abs] using (hC r hr).trans (le_max_right 0 C)

/-- The weight-continuity theorem on a nonnegative bounded rectangle, with
all correction and derivative-bound constants manufactured internally. -/
theorem weakTendsto_smooth_difference_weight_nonnegative {U : Opens (ComplexModel n)}
    (q m : ℕ) (T : LocalProductCurrent n U (m + q))
    (hT : IsPositive T) (hTc : IsClosedAny (m + q) T)
    (u : ℕ → Fin q → ComplexModel n → ℝ) (u₀ : Fin q → ComplexModel n → ℝ)
    (hu : ∀ j i, IsLocallyBoundedPshOn U (u j i))
    (hu₀ : ∀ i, IsLocallyBoundedPshOn U (u₀ i))
    (hanti : ∀ i z, z ∈ U → Antitone fun j => u j i z)
    (hlim : ∀ i z, z ∈ U → Tendsto (fun j => u j i z) atTop (𝓝 (u₀ i z)))
    (a b : ℕ → ComplexModel n → ℝ) (a₀ b₀ : ComplexModel n → ℝ)
    (has : ∀ j, ContDiffOn ℝ ∞ (a j) U) (hbs : ∀ j, ContDiffOn ℝ ∞ (b j) U)
    (hap : ∀ j, PlurisubharmonicOn (fun z => (a j z : EReal)) U)
    (hbp : ∀ j, PlurisubharmonicOn (fun z => (b j z : EReal)) U)
    (hanti_a : ∀ z ∈ U, Antitone fun j => a j z)
    (hanti_b : ∀ z ∈ U, Antitone fun j => b j z)
    (hlim_a : ∀ z ∈ U, Tendsto (fun j => a j z) atTop (𝓝 (a₀ z)))
    (hlim_b : ∀ z ∈ U, Tendsto (fun j => b j z) atTop (𝓝 (b₀ z)))
    {H : ℝ → ℝ} (hH : ContDiff ℝ ∞ H) {M : ℝ}
    (hbox_a : ∀ j z, z ∈ U → a j z ∈ Icc 0 M)
    (hbox_b : ∀ j z, z ∈ U → b j z ∈ Icc 0 M) :
    WeakTendsto (fun j => mulBorel (btProduct q m (u j) T)
        ((U : Set (ComplexModel n)).indicator (fun z => H (b j z - a j z))))
      (mulBorel (btProduct q m u₀ T)
        ((U : Set (ComplexModel n)).indicator (fun z => H (b₀ z - a₀ z)))) := by
  obtain ⟨C, A, B, hC, hA, hH₀, hH₁, hH₂⟩ := exists_smooth_weight_bounds hH M
  exact weakTendsto_smooth_difference_weight_of_bounds q m T hT hTc u u₀ hu hu₀ hanti hlim
    a b a₀ b₀ has hbs hap hbp hanti_a hanti_b hlim_a hlim_b hH hC hA hbox_a hbox_b hH₀ hH₁ hH₂

/-- The bounded smooth difference-weight passage needed in FPT's one-factor
comparison. The original inputs may have either sign; a common shift and all
convexification constants are produced inside the proof. -/
theorem weakTendsto_smooth_difference_weight {U : Opens (ComplexModel n)}
    (q m : ℕ) (T : LocalProductCurrent n U (m + q))
    (hT : IsPositive T) (hTc : IsClosedAny (m + q) T)
    (u : ℕ → Fin q → ComplexModel n → ℝ) (u₀ : Fin q → ComplexModel n → ℝ)
    (hu : ∀ j i, IsLocallyBoundedPshOn U (u j i))
    (hu₀ : ∀ i, IsLocallyBoundedPshOn U (u₀ i))
    (hanti : ∀ i z, z ∈ U → Antitone fun j => u j i z)
    (hlim : ∀ i z, z ∈ U → Tendsto (fun j => u j i z) atTop (𝓝 (u₀ i z)))
    (a b : ℕ → ComplexModel n → ℝ) (a₀ b₀ : ComplexModel n → ℝ)
    (has : ∀ j, ContDiffOn ℝ ∞ (a j) U) (hbs : ∀ j, ContDiffOn ℝ ∞ (b j) U)
    (hap : ∀ j, PlurisubharmonicOn (fun z => (a j z : EReal)) U)
    (hbp : ∀ j, PlurisubharmonicOn (fun z => (b j z : EReal)) U)
    (hanti_a : ∀ z ∈ U, Antitone fun j => a j z)
    (hanti_b : ∀ z ∈ U, Antitone fun j => b j z)
    (hlim_a : ∀ z ∈ U, Tendsto (fun j => a j z) atTop (𝓝 (a₀ z)))
    (hlim_b : ∀ z ∈ U, Tendsto (fun j => b j z) atTop (𝓝 (b₀ z)))
    {H : ℝ → ℝ} (hH : ContDiff ℝ ∞ H) {M : ℝ}
    (hbound_a : ∀ j z, z ∈ U → |a j z| ≤ M)
    (hbound_b : ∀ j z, z ∈ U → |b j z| ≤ M) :
    WeakTendsto (fun j => mulBorel (btProduct q m (u j) T)
        ((U : Set (ComplexModel n)).indicator (fun z => H (b j z - a j z))))
      (mulBorel (btProduct q m u₀ T)
        ((U : Set (ComplexModel n)).indicator (fun z => H (b₀ z - a₀ z)))) := by
  let a' : ℕ → ComplexModel n → ℝ := fun j z => a j z + M
  let b' : ℕ → ComplexModel n → ℝ := fun j z => b j z + M
  let a₀' : ComplexModel n → ℝ := fun z => a₀ z + M
  let b₀' : ComplexModel n → ℝ := fun z => b₀ z + M
  have ha' : ∀ j, IsLocallyBoundedPshOn U (a' j) := fun j =>
    isLocallyBoundedPshOn_add_const (locallyBoundedPshOn_of_smooth (has j) (hap j)) M
  have hb' : ∀ j, IsLocallyBoundedPshOn U (b' j) := fun j =>
    isLocallyBoundedPshOn_add_const (locallyBoundedPshOn_of_smooth (hbs j) (hbp j)) M
  have hbox_a : ∀ j z, z ∈ U → a' j z ∈ Icc 0 (2 * M) := by
    intro j z hz
    have h := abs_le.mp (hbound_a j z hz)
    dsimp [a']
    exact ⟨by linarith, by linarith⟩
  have hbox_b : ∀ j z, z ∈ U → b' j z ∈ Icc 0 (2 * M) := by
    intro j z hz
    have h := abs_le.mp (hbound_b j z hz)
    dsimp [b']
    exact ⟨by linarith, by linarith⟩
  have h := weakTendsto_smooth_difference_weight_nonnegative q m T hT hTc u u₀ hu hu₀ hanti hlim
    a' b' a₀' b₀' (fun j => (has j).add contDiffOn_const)
    (fun j => (hbs j).add contDiffOn_const) (fun j => (ha' j).1) (fun j => (hb' j).1)
    (fun z hz i j hij => add_le_add (hanti_a z hz hij) (le_refl M))
    (fun z hz i j hij => add_le_add (hanti_b z hz hij) (le_refl M))
    (fun z hz => (hlim_a z hz).add_const M) (fun z hz => (hlim_b z hz).add_const M)
    hH hbox_a hbox_b
  simpa only [a', b', a₀', b₀', add_sub_add_right_eq_sub] using h

end SGPT.PSH.HermitianComparisonWeights
