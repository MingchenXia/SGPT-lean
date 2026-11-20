import SGPT.Okounkov.TranscendentalWNLegendreChord
import SGPT.Okounkov.TranscendentalWNLegendreSmoothDensity
import SGPT.Foundations.Analysis.Pending.PshRadialRegularization

/-!
# The approximation of `u` by smooth functions of `(z, log |τ|²)` (package WN-LEG)

Blueprint `claude-tok-wn-leg`, node `tok-wn-leg:approx` (first part).  For `u` circle-invariant
psh on `B × ℂ*`, the function `Ũ(z, ζ) = u(z, e^{ζ/2})` (`expPullback`, read on the model `ℂᴺ⁺¹`
through `stripModelEquiv`) is psh on `B × ℂ` and invariant under `ζ ↦ ζ + i t`.  Its radial
regularizations `R_δ = Ũ * ρ_δ` (TN `PshRadialRegularization`) inherit the invariance
(`radialRegularization_expPullback_im_invariant`), so they are functions of `(z, Re ζ)`; the
descended functions `(z, τ) ↦ R_δ(z, log |τ|²)` are psh on `B' × ℂ*`
(`plurisubharmonicOn_descend`), via the local holomorphic branches `2 log τ` and `2 log (-τ)`.

This file also provides a smooth radial kernel (`exists_isRadialKernel`), which TN's radial
regularization takes as data.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality
  SGPT.Foundations.Analysis.Pending.PshRadialRegularization

/-! ### A smooth radial kernel -/

section Kernel

variable {n : ℕ}

/-- The unnormalized profile `y ↦ smoothTransition (1/2 - ‖y‖²)`. -/
def radialProfile (n : ℕ) (y : ComplexModel n) : ℝ := Real.smoothTransition (1 / 2 - ‖y‖ ^ 2)

theorem contDiff_radialProfile : ContDiff ℝ ∞ (radialProfile n) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_norm_sq ℝ))

theorem support_radialProfile_subset : Function.support (radialProfile n) ⊆ closedBall 0 1 := by
  intro y hy
  rw [Function.mem_support] at hy
  have h : 0 < 1 / 2 - ‖y‖ ^ 2 := by
    by_contra hle
    exact hy (Real.smoothTransition.zero_of_nonpos (not_lt.mp hle))
  rw [mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg y]

theorem tsupport_radialProfile_subset : tsupport (radialProfile n) ⊆ closedBall 0 1 :=
  closure_minimal support_radialProfile_subset isClosed_closedBall

theorem hasCompactSupport_radialProfile : HasCompactSupport (radialProfile n) :=
  (isCompact_closedBall (0 : ComplexModel n) 1).of_isClosed_subset (isClosed_tsupport _)
    tsupport_radialProfile_subset

theorem integral_radialProfile_pos : 0 < ∫ y, radialProfile n y := by
  have h0 : radialProfile n 0 ≠ 0 := by
    simp only [radialProfile, norm_zero]
    exact (Real.smoothTransition.pos_of_pos (by norm_num)).ne'
  exact contDiff_radialProfile.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    hasCompactSupport_radialProfile (fun y => Real.smoothTransition.nonneg _) h0

/-- **A smooth radial kernel exists.** -/
theorem exists_isRadialKernel : ∃ ρ : ComplexModel n → ℝ, IsRadialKernel ρ := by
  set c := (∫ y, radialProfile n y)⁻¹ with hc
  have hpos := integral_radialProfile_pos (n := n)
  refine ⟨fun y => c * radialProfile n y, ⟨contDiff_const.mul contDiff_radialProfile,
    fun y => mul_nonneg (inv_nonneg.mpr hpos.le) (Real.smoothTransition.nonneg _), ?_, ?_, ?_⟩⟩
  · rw [integral_const_mul, hc, inv_mul_cancel₀ hpos.ne']
  · exact (tsupport_mul_subset_right).trans tsupport_radialProfile_subset
  · intro a ha y
    simp only [radialProfile, norm_smul, ha, one_mul]

end Kernel

/-! ### Norms in `ℂᴺ⁺¹ = ℂᴺ × ℂ` -/

section Norms

variable {N : ℕ}

theorem norm_stripModelEquiv_fst_le (q : ComplexModel (N + 1)) :
    ‖(stripModelEquiv N q).1‖ ≤ ‖q‖ := by
  have h1 : ‖(stripModelEquiv N q).1‖ ^ 2 = ∑ j : Fin N, ‖q j.castSucc‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    congr 1
  have h2 : ‖q‖ ^ 2 = ∑ i : Fin (N + 1), ‖q i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  have h3 : ∑ j : Fin N, ‖q j.castSucc‖ ^ 2 ≤ ∑ i : Fin (N + 1), ‖q i‖ ^ 2 := by
    rw [Fin.sum_univ_castSucc]
    exact le_add_of_nonneg_right (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by rw [h1, h2]; exact h3)

theorem norm_apply_le_norm {ι : Type*} [Fintype ι] (q : EuclideanSpace ℂ ι) (i : ι) :
    ‖q i‖ ≤ ‖q‖ := by
  rw [EuclideanSpace.norm_eq]
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun j => ‖q j‖ ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ i)

theorem abs_re_stripModelEquiv_snd_le (q : ComplexModel (N + 1)) :
    |(stripModelEquiv N q).2.re| ≤ ‖q‖ := by
  rw [stripModelEquiv_snd_eq]
  exact (Complex.abs_re_le_norm _).trans (norm_apply_le_norm q _)

/-- The inner set `B' = {z : ∃ δ' > δ, ball z δ' ⊆ B}`. -/
def innerSet (B : Set (ComplexModel N)) (δ : ℝ) : Set (ComplexModel N) :=
  {z | ∃ δ', δ < δ' ∧ ball z δ' ⊆ B}

theorem isOpen_innerSet (B : Set (ComplexModel N)) (δ : ℝ) : IsOpen (innerSet B δ) := by
  rw [Metric.isOpen_iff]
  rintro z ⟨δ', hδ', hball⟩
  refine ⟨(δ' - δ) / 2, by linarith, fun w hw => ⟨δ + (δ' - δ) / 2, by linarith, ?_⟩⟩
  intro x hx
  apply hball
  rw [mem_ball] at hw hx ⊢
  linarith [dist_triangle x w z]

theorem stripModelEquiv_symm_mem_innerDomain {B : Set (ComplexModel N)} {δ : ℝ}
    {z : ComplexModel N} (hz : z ∈ innerSet B δ) (ζ : ℂ) :
    (stripModelEquiv N).symm (z, ζ) ∈ innerDomain (stripDomain B) δ := by
  obtain ⟨δ', hδ', hball⟩ := hz
  refine ⟨δ', hδ', fun x hx => ?_⟩
  show (stripModelEquiv N x).1 ∈ B
  apply hball
  rw [mem_ball] at hx ⊢
  have h := norm_stripModelEquiv_fst_le (x - (stripModelEquiv N).symm (z, ζ))
  rw [map_sub, ContinuousLinearEquiv.apply_symm_apply] at h
  simp only [Prod.fst_sub] at h
  rw [dist_eq_norm] at hx ⊢
  linarith

end Norms

/-! ### The pull-back `Ũ(z, ζ) = u(z, e^{ζ/2})` and its regularizations -/

section Pullback

variable {N : ℕ}

/-- `Ũ(q) = u(z, e^{ζ/2})` for `(z, ζ) = stripModelEquiv N q`. -/
def expPullback (u : ComplexModel N → ℂ → EReal) (q : ComplexModel (N + 1)) : EReal :=
  u (stripModelEquiv N q).1 (Complex.exp ((stripModelEquiv N q).2 / 2))

theorem plurisubharmonicOn_expPullback {B : Set (ComplexModel N)} (hB : IsOpen B)
    {u : ComplexModel N → ℂ → EReal}
    (hu : PlurisubharmonicOn (fun p : ComplexModel N × ℂ => u p.1 p.2) (B ×ˢ puncturedPlane)) :
    PlurisubharmonicOn (expPullback u) (stripDomain B) := by
  have h := plurisubharmonicOn_comp_stripModelEquiv (plurisubharmonicOn_comp_exp_half hB hu)
  refine h.mono ?_
  intro q hq
  exact ⟨hq, mem_univ _⟩

/-- `ζ ↦ ζ + i t` in the last coordinate. -/
theorem stripModelEquiv_add_im (q : ComplexModel (N + 1)) (t : ℝ) :
    stripModelEquiv N (q + ((t : ℂ) * Complex.I) • coordinateVector (Fin.last N)) =
      ((stripModelEquiv N q).1, (stripModelEquiv N q).2 + (t : ℂ) * Complex.I) := by
  rw [map_add, map_smul, stripModelEquiv_coordinateVector_last]
  ext <;> simp

theorem expPullback_add_im {u : ComplexModel N → ℂ → EReal} (hinv : IsCircleInvariant u)
    (q : ComplexModel (N + 1)) (t : ℝ) :
    expPullback u (q + ((t : ℂ) * Complex.I) • coordinateVector (Fin.last N)) =
      expPullback u q := by
  simp only [expPullback, stripModelEquiv_add_im]
  apply hinv
  rw [norm_exp_half, norm_exp_half]
  simp

/-- **The regularizations are functions of `(z, Re ζ)`.** -/
theorem radialRegularization_expPullback_add_im {u : ComplexModel N → ℂ → EReal}
    (hinv : IsCircleInvariant u) (ρ : ComplexModel (N + 1) → ℝ) (δ : ℝ)
    (x : ComplexModel (N + 1)) (t : ℝ) :
    radialRegularization ρ (expPullback u) δ
        (x + ((t : ℂ) * Complex.I) • coordinateVector (Fin.last N)) =
      radialRegularization ρ (expPullback u) δ x := by
  simp only [radialRegularization]
  congr 1
  funext y
  rw [show x + ((t : ℂ) * Complex.I) • coordinateVector (Fin.last N) - y =
    (x - y) + ((t : ℂ) * Complex.I) • coordinateVector (Fin.last N) by abel,
    expPullback_add_im hinv]

theorem stripModelEquiv_symm_eq_re_add (z : ComplexModel N) (ζ : ℂ) :
    (stripModelEquiv N).symm (z, ζ) =
      (stripModelEquiv N).symm (z, (ζ.re : ℂ)) +
        ((ζ.im : ℂ) * Complex.I) • coordinateVector (Fin.last N) := by
  apply (stripModelEquiv N).injective
  rw [stripModelEquiv_add_im, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  simp only [Prod.mk.injEq, true_and]
  exact (Complex.re_add_im ζ).symm

theorem radialRegularization_expPullback_re {u : ComplexModel N → ℂ → EReal}
    (hinv : IsCircleInvariant u) (ρ : ComplexModel (N + 1) → ℝ) (δ : ℝ)
    (z : ComplexModel N) (ζ : ℂ) :
    radialRegularization ρ (expPullback u) δ ((stripModelEquiv N).symm (z, ζ)) =
      radialRegularization ρ (expPullback u) δ ((stripModelEquiv N).symm (z, (ζ.re : ℂ))) := by
  rw [stripModelEquiv_symm_eq_re_add z ζ, radialRegularization_expPullback_add_im hinv]

/-- The real function `F_δ(z, y) = R_δ(z, y)` on `ℂᴺ × ℝ`. -/
def regularizedProfile (ρ : ComplexModel (N + 1) → ℝ) (u : ComplexModel N → ℂ → EReal) (δ : ℝ)
    (p : ComplexModel N × ℝ) : ℝ :=
  radialRegularization ρ (expPullback u) δ ((stripModelEquiv N).symm (p.1, (p.2 : ℂ)))

/-- **Descent to `B' × ℂ*`**: `(z, τ) ↦ F_δ(z, log |τ|²)` is psh on `B' × ℂ*`. -/
theorem plurisubharmonicOn_descend {B : Set (ComplexModel N)} (hB : IsOpen B)
    (hBc : IsPreconnected (stripDomain B)) {u : ComplexModel N → ℂ → EReal}
    (hu : PlurisubharmonicOn (fun p : ComplexModel N × ℂ => u p.1 p.2) (B ×ˢ puncturedPlane))
    (hinv : IsCircleInvariant u) (hne : ∃ q ∈ stripDomain B, expPullback u q ≠ ⊥)
    {ρ : ComplexModel (N + 1) → ℝ} (hρ : IsRadialKernel ρ) {δ : ℝ} (hδ : 0 < δ) :
    PlurisubharmonicOn
      (fun p : ComplexModel N × ℂ => (regularizedProfile ρ u δ (p.1, logNormSq p.2) : EReal))
      (innerSet B δ ×ˢ puncturedPlane) := by
  have hR := plurisubharmonicOn_radialRegularization hρ (isOpen_stripDomain hB) hBc
    (plurisubharmonicOn_expPullback hB hu) hne hδ
  have hΨ := plurisubharmonicOn_comp_stripModelEquiv_symm hR
  have hval : ∀ (z : ComplexModel N) (τ : ℂ) (ζ : ℂ), ζ.re = logNormSq τ →
      (regularizedProfile ρ u δ (z, logNormSq τ) : EReal) =
        (radialRegularization ρ (expPullback u) δ ((stripModelEquiv N).symm (z, ζ)) : EReal) := by
    intro z τ ζ hζ
    rw [radialRegularization_expPullback_re hinv, hζ]
    rfl
  have hre₁ : ∀ τ : ℂ, τ ≠ 0 → (2 * Complex.log τ).re = logNormSq τ := by
    intro τ _
    rw [logNormSq, Real.log_pow]
    simp [Complex.log_re]
  have hre₂ : ∀ τ : ℂ, τ ≠ 0 → (2 * Complex.log (-τ)).re = logNormSq τ := by
    intro τ _
    rw [logNormSq, Real.log_pow]
    simp [Complex.log_re, norm_neg]
  have hmaps : ∀ ζ : ℂ, ∀ z ∈ innerSet B δ,
      (z, ζ) ∈ (stripModelEquiv N).symm ⁻¹' innerDomain (stripDomain B) δ :=
    fun ζ z hz => stripModelEquiv_symm_mem_innerDomain hz ζ
  intro p hp
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane (show p.2 ≠ 0 from hp.2) with hs | hs
  · -- the branch `2 log τ`
    set U₁ : Set (ComplexModel N × ℂ) := innerSet B δ ×ˢ Complex.slitPlane
    have hU₁ : IsOpen U₁ := (isOpen_innerSet B δ).prod Complex.isOpen_slitPlane
    have hd : DifferentiableOn ℂ (fun p : ComplexModel N × ℂ => (p.1, 2 * Complex.log p.2)) U₁ := by
      intro x hx
      exact (differentiableAt_fst.prodMk ((differentiableAt_const _).mul
        ((Complex.differentiableAt_log hx.2).comp x differentiableAt_snd))).differentiableWithinAt
    have h1 := plurisubharmonicOn_comp_holomorphic_strip hU₁ hd
      (fun x hx => hmaps _ x.1 hx.1) hΨ
    refine (h1 p ⟨hp.1, hs⟩).congr ?_
    filter_upwards [hU₁.mem_nhds ⟨hp.1, hs⟩] with x hx
    exact (hval x.1 x.2 _ (hre₁ x.2 (Complex.slitPlane_ne_zero hx.2))).symm
  · -- the branch `2 log (-τ)`
    set U₂ : Set (ComplexModel N × ℂ) := innerSet B δ ×ˢ {τ | -τ ∈ Complex.slitPlane}
    have hU₂ : IsOpen U₂ :=
      (isOpen_innerSet B δ).prod (Complex.isOpen_slitPlane.preimage continuous_neg)
    have hd : DifferentiableOn ℂ
        (fun p : ComplexModel N × ℂ => (p.1, 2 * Complex.log (-p.2))) U₂ := by
      intro x hx
      exact (differentiableAt_fst.prodMk ((differentiableAt_const _).mul
        ((Complex.differentiableAt_log hx.2).comp x differentiableAt_snd.neg))).differentiableWithinAt
    have h1 := plurisubharmonicOn_comp_holomorphic_strip hU₂ hd
      (fun x hx => hmaps _ x.1 hx.1) hΨ
    refine (h1 p ⟨hp.1, hs⟩).congr ?_
    filter_upwards [hU₂.mem_nhds ⟨hp.1, hs⟩] with x hx
    have hx0 : x.2 ≠ 0 := fun h0 => Complex.slitPlane_ne_zero hx.2 (by simp [h0])
    exact (hval x.1 x.2 _ (hre₂ x.2 hx0)).symm

end Pullback

/-! ### The locally bounded case: data and growth bounds -/

section BoundedData

variable {N : ℕ}

/-- The hypotheses of `tok-wn-leg:bounded-case` on an open `B ⊆ ℂᴺ`: `u` circle-invariant psh on
`B × ℂ*`, `û_λ ≡ -∞` on `B` for `λ ∉ [a, b]`, and `|û_λ| ≤ C` on `B` for `λ ∈ [a, b]`, `a < b`. -/
structure IsBoundedLegendreData (B : Set (ComplexModel N)) (u : ComplexModel N → ℂ → EReal)
    (a b C : ℝ) : Prop where
  isOpen : IsOpen B
  psh : PlurisubharmonicOn (fun p : ComplexModel N × ℂ => u p.1 p.2) (B ×ˢ puncturedPlane)
  circleInvariant : IsCircleInvariant u
  lt : a < b
  eq_bot : ∀ lam : ℝ, lam ∉ Icc a b → ∀ z ∈ B, partialLegendre u lam z = ⊥
  lower : ∀ lam ∈ Icc a b, ∀ z ∈ B, ((-C : ℝ) : EReal) ≤ partialLegendre u lam z
  upper : ∀ lam ∈ Icc a b, ∀ z ∈ B, partialLegendre u lam z ≤ (C : EReal)

theorem mul_le_max_of_mem_Icc {a b lam y : ℝ} (hlam : lam ∈ Icc a b) :
    lam * y ≤ max (a * y) (b * y) := by
  rcases le_total 0 y with hy | hy
  · exact (mul_le_mul_of_nonneg_right hlam.2 hy).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_right hlam.1 hy).trans (le_max_left _ _)

/-- **Growth bounds from duality**: `-C + max(aℓ, bℓ) ≤ u(z, τ) ≤ C + max(aℓ, bℓ)`,
`ℓ = log |τ|²`. -/
theorem IsBoundedLegendreData.bounds {B : Set (ComplexModel N)} {u : ComplexModel N → ℂ → EReal}
    {a b C : ℝ} (h : IsBoundedLegendreData B u a b C) {z : ComplexModel N} (hz : z ∈ B)
    {τ : ℂ} (hτ : τ ≠ 0) :
    (((-C + max (a * logNormSq τ) (b * logNormSq τ) : ℝ)) : EReal) ≤ u z τ ∧
      u z τ ≤ ((C + max (a * logNormSq τ) (b * logNormSq τ) : ℝ) : EReal) := by
  have hdual := partialLegendre_duality_Icc h.isOpen h.psh h.circleInvariant hz
    (fun lam hlam => h.eq_bot lam hlam z hz) hτ
  set y := logNormSq τ
  have hterm : ∀ lam ∈ Icc a b, (((-C + lam * y : ℝ)) : EReal) ≤
      partialLegendre u lam z + ((lam * y : ℝ) : EReal) := by
    intro lam hlam
    rw [EReal.coe_add]
    exact add_le_add_left (h.lower lam hlam z hz) _
  refine ⟨?_, ?_⟩
  · rw [hdual]
    rcases le_total (a * y) (b * y) with hle | hle
    · rw [max_eq_right hle]
      exact (hterm b ⟨h.lt.le, le_rfl⟩).trans
        (le_iSup₂ (f := fun lam _ => partialLegendre u lam z + ((lam * y : ℝ) : EReal)) b
          ⟨h.lt.le, le_rfl⟩)
    · rw [max_eq_left hle]
      exact (hterm a ⟨le_rfl, h.lt.le⟩).trans
        (le_iSup₂ (f := fun lam _ => partialLegendre u lam z + ((lam * y : ℝ) : EReal)) a
          ⟨le_rfl, h.lt.le⟩)
  · rw [hdual]
    refine iSup₂_le fun lam hlam => ?_
    calc partialLegendre u lam z + ((lam * y : ℝ) : EReal)
        ≤ (C : EReal) + ((lam * y : ℝ) : EReal) := add_le_add_left (h.upper lam hlam z hz) _
      _ = ((C + lam * y : ℝ) : EReal) := (EReal.coe_add _ _).symm
      _ ≤ ((C + max (a * y) (b * y) : ℝ) : EReal) :=
          EReal.coe_le_coe_iff.mpr (by linarith [mul_le_max_of_mem_Icc (y := y) hlam])

/-- The same bounds for `Ũ(z, ζ) = u(z, e^{ζ/2})` on `B × ℂ`, with `ℓ = Re ζ`. -/
theorem IsBoundedLegendreData.expPullback_bounds {B : Set (ComplexModel N)}
    {u : ComplexModel N → ℂ → EReal} {a b C : ℝ} (h : IsBoundedLegendreData B u a b C)
    {q : ComplexModel (N + 1)} (hq : q ∈ stripDomain B) :
    ((-C + max (a * (stripModelEquiv N q).2.re) (b * (stripModelEquiv N q).2.re) : ℝ) : EReal) ≤
        expPullback u q ∧
      expPullback u q ≤
        ((C + max (a * (stripModelEquiv N q).2.re) (b * (stripModelEquiv N q).2.re) : ℝ) : EReal) := by
  have := h.bounds hq (Complex.exp_ne_zero ((stripModelEquiv N q).2 / 2))
  rwa [logNormSq_exp_half_complex] at this

/-- **`tok-wn-leg:bounded-case`** (statement only; *not proved here*): WN21 Theorem 3.3 for
locally bounded transforms, on an open `B ⊆ ℂᴺ`:
`⟨(dd^c u)^{N+1}⟩(E × ℂ*) = (N + 1) ∫_a^b ⟨(dd^c û_λ)^N⟩(E) dλ` for Borel `E ⊆ B`. -/
def BoundedLegendreMAStatement (N : ℕ) : Prop :=
  ∀ (B : Opens (ComplexModel N)) (u : ComplexModel N → ℂ → EReal) (a b C : ℝ),
    IsBoundedLegendreData (B : Set (ComplexModel N)) u a b C →
    ∀ (hu : PlurisubharmonicOn (productModelFunction u) (puncturedProductOpens B))
      (hû : ∀ lam : ℝ, PlurisubharmonicOn (partialLegendre u lam) B)
      (E : Set (ComplexModel N)), MeasurableSet E → E ⊆ B →
      MongeAmpere.truncationLimitMeasure (puncturedProductOpens B) (productModelFunction u) hu
          (stripModelEquiv N ⁻¹' (E ×ˢ puncturedPlane)) =
        ((N + 1 : ℕ) : ENNReal) *
          ∫⁻ lam in Icc a b, MongeAmpere.truncationLimitMeasure B (partialLegendre u lam) (hû lam) E

end BoundedData

end SGPT.Okounkov.TranscendentalWN
