import SGPT.Envelopes.MADirichlet2Envelope
import SGPT.Envelopes.MADirichlet2Density

/-!
# The Dirichlet problem `(ddᶜH)ⁿ = Fⁿ ηⁿ` on the unit polydisk for `C²` data

Xia, *Foundations of pluripotential theory* (FPT), `thm:continuous-density-ball-dirichlet`,
Step 3, on the unit polydisk `P` with zero boundary data (route: `claude-ma-dir2.tex`). Let
`F ≥ 0` be of class `C²` on `ℂⁿ`, `n ≥ 1`, and `H_F` the envelope of the nonpositive subsolutions
of `(ddᶜv)ⁿ ≥ Fⁿ ηⁿ` on `P` (`MADirichlet2Envelope`). Then

  `(ddᶜH_F)ⁿ = Fⁿ ηⁿ`   on `P`   (`ma_polydiskEnvelope_eq`).

The inequality `≥` is Step 1. For `≤`, `H_F` is locally semiconcave (Step 2), so its Monge–Ampère
measure is bounded by the determinant of its almost-everywhere complex Hessian
(`canonicalBedfordTaylorMeasure_le_of_peano`), and that determinant is at most `Fⁿ` at every
Peano point (`det_le_of_hasPeanoExpansion`, FPT's bump argument): otherwise the Taylor polynomial
of `H_F`, with a fraction `t` of its Levi form removed and raised by a small constant, is a smooth
plurisubharmonic function of constant Monge–Ampère density `(1 - t)ⁿ det(H_{j k̄}) > Fⁿ` near the
point, strictly below `H_F` on a sphere around it and strictly above `H_F` at its centre; gluing
its maximum with `H_F` produces a member of `𝒮_F` exceeding `H_F`, a contradiction.

Unlike FPT, which takes the density `f = Fⁿ` and boundary values `φ` with `F` and `φ` of class
`C²` near `B̄`, this file takes the boundary values `0` (the case used for the Dinew inequality)
on the polydisk instead of the ball.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace Matrix
open scoped Topology ENNReal ComplexOrder ContDiff

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.SemiconcaveHessian
open SGPT.NPP.LogConcavityDinew

variable {n : ℕ}

/-! ### Quadratic polynomials -/

/-- The quadratic polynomial `a + L(z - z₀) + B(z - z₀, z - z₀)/2 + c`. -/
def quadPoly (a c : ℝ) (L : ComplexModel n →L[ℝ] ℝ)
    (B : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) (z₀ z : ComplexModel n) : ℝ :=
  (a + L (z - z₀) + B (z - z₀) (z - z₀) / 2) + c

section Quad

variable {a c : ℝ} {L : ComplexModel n →L[ℝ] ℝ} {B : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
  {z₀ : ComplexModel n}

theorem contDiff_quadPoly : ContDiff ℝ ∞ (quadPoly a c L B z₀) := by
  have hlin : ContDiff ℝ ∞ (fun z : ComplexModel n ↦ z - z₀) := contDiff_id.sub contDiff_const
  have hquad : ContDiff ℝ ∞ fun z : ComplexModel n ↦ B (z - z₀) (z - z₀) :=
    ContDiff.clm_apply (B.contDiff.comp hlin) hlin
  exact ((contDiff_const.add (L.contDiff.comp hlin)).add (hquad.div_const 2)).add contDiff_const

theorem realHessian_quadPoly (hsymm : ∀ v w, B v w = B w v) (x v w : ComplexModel n) :
    realHessian (quadPoly a c L B z₀) x v w = B v w :=
  realHessian_quadratic hsymm x v w

theorem complexHessian_quadPoly (hsymm : ∀ v w, B v w = B w v) (x : ComplexModel n) :
    complexHessian (quadPoly a c L B z₀) x = complexHessianOfBilin B := by
  ext j k
  simp only [complexHessian, complexHessianOfBilin, realHessian_quadPoly hsymm]

theorem leviForm_quadPoly (hsymm : ∀ v w, B v w = B w v) (x v : ComplexModel n) :
    leviForm (quadPoly a c L B z₀) x v = leviFormOfBilin B v := by
  simp only [leviForm, leviFormOfBilin, realHessian_quadPoly hsymm]

end Quad

/-- The Hermitian form of `complexHessianOfBilin A` is the Levi form of `A`. -/
theorem dotProduct_mulVec_complexHessianOfBilin {A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (hsymm : ∀ v w, A v w = A w v) (y : Fin n → ℂ) :
    star y ⬝ᵥ ((complexHessianOfBilin A).mulVec y) =
      ((leviFormOfBilin A (coordCombination y) : ℝ) : ℂ) := by
  have h := dotProduct_mulVec_complexHessian_eq_leviForm
    (f := quadPoly (0 : ℝ) 0 0 A 0) (z := 0)
    (contDiff_quadPoly.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) y
  rwa [complexHessian_quadPoly hsymm, leviForm_quadPoly hsymm] at h

/-- A positive definite complex Hessian gives a uniform lower bound for the Levi form. -/
theorem exists_leviFormOfBilin_lower (hn : 0 < n)
    {A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ} (hsymm : ∀ v w, A v w = A w v)
    (hpd : (complexHessianOfBilin A).PosDef) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ v : ComplexModel n, c₀ * ‖v‖ ^ 2 ≤ leviFormOfBilin A v := by
  have hpos : ∀ v : ComplexModel n, v ≠ 0 → 0 < leviFormOfBilin A v := by
    intro v hv
    set x : Fin n → ℂ := fun i ↦ star (v i) with hxdef
    have hxne : x ≠ 0 := by
      intro hx
      refine hv ?_
      ext i
      have := congrFun hx i
      simpa [hxdef] using this
    have h := hpd.re_dotProduct_pos hxne
    rw [dotProduct_mulVec_complexHessianOfBilin hsymm, hxdef, coordCombination_star v] at h
    simpa using h
  have : ProperSpace (ComplexModel n) := FiniteDimensional.proper ℝ _
  have hne : (sphere (0 : ComplexModel n) 1).Nonempty := by
    refine ⟨coordinateVector ⟨0, hn⟩, ?_⟩
    simp [mem_sphere_iff_norm, coordinateVector]
  obtain ⟨v₀, hv₀mem, hv₀min⟩ :=
    (isCompact_sphere (0 : ComplexModel n) 1).exists_isMinOn hne
      (continuous_leviFormOfBilin A).continuousOn
  have hv₀norm : ‖v₀‖ = 1 := by simpa [mem_sphere_iff_norm] using hv₀mem
  have hv₀ne : v₀ ≠ 0 := by
    intro h; rw [h] at hv₀norm; simp at hv₀norm
  refine ⟨leviFormOfBilin A v₀, hpos v₀ hv₀ne, fun v ↦ ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp [leviFormOfBilin]
  · have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hw : ‖v‖⁻¹ • v ∈ sphere (0 : ComplexModel n) 1 := by
      simp [mem_sphere_iff_norm, norm_smul, inv_mul_cancel₀ hvn.ne']
    have hmin := hv₀min hw
    simp only [Set.mem_ofPred_eq] at hmin
    rw [leviFormOfBilin_smul A _ v] at hmin
    have hsq : (0:ℝ) < ‖v‖ ^ 2 := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hmin hsq.le
    have hcancel : ‖v‖ ^ 2 * ((‖v‖⁻¹) ^ 2 * leviFormOfBilin A v) = leviFormOfBilin A v := by
      field_simp
    rw [hcancel] at hscaled
    nlinarith [hscaled]

/-- A positive semidefinite Hermitian matrix with positive determinant is positive definite. -/
theorem posDef_of_posSemidef_of_det_re_pos {M : Matrix (Fin n) (Fin n) ℂ} (hpsd : M.PosSemidef)
    (hdet : 0 < M.det.re) : M.PosDef := by
  have hherm := hpsd.1
  refine (Matrix.IsHermitian.posDef_iff_eigenvalues_pos hherm).mpr fun i ↦ ?_
  rcases (hpsd.eigenvalues_nonneg i).lt_or_eq with h | h
  · exact h
  · exfalso
    have : M.det = 0 := by
      rw [hherm.det_eq_prod_eigenvalues]
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [← h]
      simp
    rw [this, Complex.zero_re] at hdet
    exact lt_irrefl 0 hdet

/-! ### Removing a fraction of the Levi form -/

/-- The bilinear form `B(v, w) = (A(v, w) + A(iv, iw))/2`, whose quadratic form is twice the Levi
form of `A`. -/
def leviBilin (A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) :
    ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ :=
  (2⁻¹ : ℝ) • (A + A.bilinearComp
    ((Complex.I • ContinuousLinearMap.id ℂ (ComplexModel n)).restrictScalars ℝ)
    ((Complex.I • ContinuousLinearMap.id ℂ (ComplexModel n)).restrictScalars ℝ))

theorem leviBilin_apply (A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) (v w : ComplexModel n) :
    leviBilin A v w = (A v w + A (Complex.I • v) (Complex.I • w)) / 2 := by
  have hJ : ∀ z : ComplexModel n,
      ((Complex.I • ContinuousLinearMap.id ℂ (ComplexModel n)).restrictScalars ℝ) z =
        Complex.I • z := fun z => rfl
  simp only [leviBilin, _root_.smul_apply, _root_.add_apply,
    ContinuousLinearMap.bilinearComp_apply, smul_eq_mul, hJ]
  ring

theorem I_smul_I_smul (v : ComplexModel n) : Complex.I • Complex.I • v = -v := by
  rw [smul_smul, Complex.I_mul_I, neg_one_smul]

theorem leviBilin_symm {A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (hsymm : ∀ v w, A v w = A w v) (v w : ComplexModel n) : leviBilin A v w = leviBilin A w v := by
  rw [leviBilin_apply, leviBilin_apply, hsymm v w, hsymm (Complex.I • v)]

theorem leviBilin_self (A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) (v : ComplexModel n) :
    leviBilin A v v / 2 = leviFormOfBilin A v := by
  rw [leviBilin_apply, leviFormOfBilin]; ring

theorem complexHessianOfBilin_sub_smul_leviBilin (A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (t : ℝ) : complexHessianOfBilin (A - t • leviBilin A) =
      ((1 - t : ℝ) : ℂ) • complexHessianOfBilin A := by
  ext j k
  simp only [complexHessianOfBilin, _root_.sub_apply, _root_.smul_apply,
    smul_eq_mul, leviBilin_apply, I_smul_I_smul, map_neg, _root_.neg_apply, neg_neg,
    Matrix.smul_apply]
  push_cast
  ring

theorem leviFormOfBilin_sub_smul_leviBilin (A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (t : ℝ) (v : ComplexModel n) :
    leviFormOfBilin (A - t • leviBilin A) v = (1 - t) * leviFormOfBilin A v := by
  simp only [leviFormOfBilin, _root_.sub_apply, _root_.smul_apply,
    smul_eq_mul, leviBilin_apply, I_smul_I_smul, map_neg, _root_.neg_apply, neg_neg]
  ring

/-- A `C²` function with nonnegative Levi form is locally bounded plurisubharmonic. -/
theorem isLocallyBoundedPshOn_of_contDiff {Ω : Opens (ComplexModel n)} {q : ComplexModel n → ℝ}
    (hq : ContDiff ℝ 2 q) (hlevi : ∀ y v, 0 ≤ leviForm q y v) : IsLocallyBoundedPshOn Ω q := by
  refine ⟨plurisubharmonicOn_of_levi_nonneg hq Ω.isOpen fun y _ v => hlevi y v, fun z hz => ?_⟩
  have : ProperSpace (ComplexModel n) := FiniteDimensional.proper ℝ _
  obtain ⟨C, hC⟩ := (isCompact_closedBall z 1).exists_bound_of_continuousOn
    hq.continuous.continuousOn
  exact ⟨Ω ⊓ ⟨ball z 1, isOpen_ball⟩, ⟨hz, mem_ball_self one_pos⟩, inf_le_left, C, fun w hw => by
    have := hC w (ball_subset_closedBall hw.2)
    rwa [Real.norm_eq_abs] at this⟩

/-! ### Ingredients of the bump argument -/

/-- A nonpositive function with a second-order expansion whose Levi form is positive definite
is negative at the expansion point (the expansion point is not a maximum). -/
theorem neg_of_hasPeanoExpansion (hn : 0 < n) {u : ComplexModel n → ℝ} {S : Set (ComplexModel n)}
    (hS : IsOpen S) (hu0 : ∀ z ∈ S, u z ≤ 0) {x : ComplexModel n} (hx : x ∈ S)
    {L : ComplexModel n →L[ℝ] ℝ} {A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (hpeano : HasPeanoExpansionAt u x L A) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hlevi : ∀ v, c₀ * ‖v‖ ^ 2 ≤ leviFormOfBilin A v) : u x < 0 := by
  obtain ⟨r0, hr0, hr0S⟩ := Metric.isOpen_iff.mp hS x hx
  obtain ⟨ρ₁, hρ₁, hρ₁ball⟩ := Metric.eventually_nhds_iff_ball.mp (hpeano (c₀ / 4) (by positivity))
  refine lt_of_le_of_ne (hu0 x hx) fun hux => ?_
  set s : ℝ := min ρ₁ r0 / 2 with hsdef
  have hs : 0 < s := by positivity
  have hsρ : s < ρ₁ := by rw [hsdef]; linarith [min_le_left ρ₁ r0]
  have hsr : s < r0 := by rw [hsdef]; linarith [min_le_right ρ₁ r0]
  set e : ComplexModel n := coordinateVector ⟨0, hn⟩ with hedef
  have he : ‖e‖ = 1 := by simp [hedef, coordinateVector]
  have hbound : ∀ h : ComplexModel n, ‖h‖ = s → L h + A h h / 2 ≤ c₀ / 4 * s ^ 2 := by
    intro h hh
    have hpe := hρ₁ball h (by rw [mem_ball, dist_zero_right, hh]; exact hsρ)
    have hmem : x + h ∈ S := hr0S (by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hh]; exact hsr)
    have hle := hu0 _ hmem
    have := (abs_le.mp hpe).1
    rw [hh] at this
    linarith
  have hnI : ∀ v : ComplexModel n, ‖Complex.I • v‖ = ‖v‖ := fun v => by
    rw [norm_smul, Complex.norm_I, one_mul]
  have hsn : ‖s • e‖ = s := by rw [norm_smul, he, Real.norm_eq_abs, abs_of_pos hs, mul_one]
  have h1 := hbound (s • e) hsn
  have h2 := hbound (-(s • e)) (by rw [norm_neg, hsn])
  have h3 := hbound (Complex.I • (s • e)) (by rw [hnI, hsn])
  have h4 := hbound (-(Complex.I • (s • e))) (by rw [norm_neg, hnI, hsn])
  simp only [map_neg, _root_.neg_apply, neg_neg] at h2 h4
  have hl := hlevi (s • e)
  rw [hsn] at hl
  simp only [leviFormOfBilin] at hl
  have hpos : 0 < c₀ * s ^ 2 := by positivity
  linarith only [h1, h2, h3, h4, hl, hpos]

/-- **The annulus estimate.** If `u` has a second-order expansion at `x` whose Levi form is at
least `c₀|v|²`, then for `t > 0` and all small `r` the quadratic polynomial `q` with the same
first-order part, quadratic part `A - t B` (a fraction `t` of the Levi form removed) and
constant `u(x) + t c₀ r²/4` lies strictly below `u` on the annulus `3r/4 ≤ |z - x| ≤ r`. -/
theorem exists_annulus_lt {u : ComplexModel n → ℝ} {x : ComplexModel n}
    {L : ComplexModel n →L[ℝ] ℝ} {A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (hpeano : HasPeanoExpansionAt u x L A) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hlevi : ∀ v, c₀ * ‖v‖ ^ 2 ≤ leviFormOfBilin A v) {t : ℝ} (ht : 0 < t) :
    ∃ ρ₂ > 0, ∀ r, 0 < r → r < ρ₂ → ∀ z : ComplexModel n, 3 / 4 * r ≤ ‖z - x‖ → ‖z - x‖ ≤ r →
      quadPoly (u x) (t * c₀ * r ^ 2 / 4) L (A - t • leviBilin A) x z < u z := by
  set ct : ℝ := t * c₀ with hctdef
  have hct : 0 < ct := by positivity
  obtain ⟨ρ₂, hρ₂, hρ₂ball⟩ := Metric.eventually_nhds_iff_ball.mp (hpeano (ct / 2) (by positivity))
  refine ⟨ρ₂, hρ₂, fun r hr hrρ z hz1 hz2 => ?_⟩
  set h : ComplexModel n := z - x with hhdef
  have hh : ‖h‖ < ρ₂ := lt_of_le_of_lt hz2 hrρ
  have hpe := hρ₂ball h (by simpa [mem_ball, dist_zero_right] using hh)
  have hz : x + h = z := by rw [hhdef]; abel
  rw [hz] at hpe
  have hq : quadPoly (u x) (ct * r ^ 2 / 4) L (A - t • leviBilin A) x z =
      (u x + L h + A h h / 2) - t * leviFormOfBilin A h + ct * r ^ 2 / 4 := by
    simp only [quadPoly, ← hhdef, _root_.sub_apply, _root_.smul_apply,
      smul_eq_mul]
    rw [← leviBilin_self]
    ring
  rw [hq]
  have hbound := (abs_le.mp hpe).1
  have h1 : t * (c₀ * ‖h‖ ^ 2) ≤ t * leviFormOfBilin A h :=
    mul_le_mul_of_nonneg_left (hlevi h) ht.le
  have h2 : ct * ‖h‖ ^ 2 = t * (c₀ * ‖h‖ ^ 2) := by rw [hctdef]; ring
  have hsq : (3 / 4 * r) ^ 2 ≤ ‖h‖ ^ 2 := pow_le_pow_left₀ (by positivity) hz1 2
  have h3 : ct * (3 / 4 * r) ^ 2 ≤ ct * ‖h‖ ^ 2 := mul_le_mul_of_nonneg_left hsq hct.le
  have h4 : 0 < ct * r ^ 2 := by positivity
  linarith only [hbound, h1, h2, h3, h4]

/-- The Monge–Ampère measure of a quadratic polynomial with positive semidefinite complex
Hessian: the constant density `(n!/πⁿ) det`. -/
theorem canonicalBedfordTaylorMeasure_quadPoly {V : Opens (ComplexModel n)} {a c : ℝ}
    {L : ComplexModel n →L[ℝ] ℝ} {B : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    {z₀ : ComplexModel n} (hsymm : ∀ v w, B v w = B w v)
    (hpsd : (complexHessianOfBilin B).PosSemidef)
    (hq : IsLocallyBoundedPshOn V (quadPoly a c L B z₀)) :
    canonicalBedfordTaylorMeasure V _ hq =
      (volume.restrict (V : Set (ComplexModel n))).withDensity
        fun _ => ENNReal.ofReal (mongeAmpereConst n * (complexHessianOfBilin B).det.re) := by
  have hsm : IsSmoothPsdOn V (quadPoly a c L B z₀) :=
    ⟨contDiff_quadPoly.contDiffOn, fun z _ => by rw [complexHessian_quadPoly hsymm]; exact hpsd⟩
  rw [(isBTLimit_canonicalBedfordTaylorMeasure hq).eq_densityMeasure (fun _ => hsm), densityMeasure]
  congr 1
  funext z
  rw [mixedDensity_diagonal, smoothDensity, complexHessian_quadPoly hsymm]
  rfl

open Classical in
/-- **Gluing a smooth bump into a subsolution.** If `H ∈ 𝒮_F`, `q` is a `C²` function with
nonnegative Levi form, `q ≤ 0` on the ball `B(x, r) ⊆ P`, `q < H` on the annulus
`3r/4 ≤ |z - x| ≤ r` and `(ddᶜq)ⁿ ≥ Fⁿ ηⁿ` on the ball, then the function equal to `max(H, q)` on
the ball and to `H` elsewhere belongs to `𝒮_F`. -/
theorem glue_mem_polydiskSubsolutions (hn : 0 < n) {F : ComplexModel n → ℝ} (hFc : Continuous F)
    {H q : ComplexModel n → ℝ} (hHmem : H ∈ polydiskSubsolutions F) (hqC : ContDiff ℝ 2 q)
    (hqlevi : ∀ y v, 0 ≤ leviForm q y v) {x : ComplexModel n} {r : ℝ}
    (hballP : ball x r ⊆ unitPolydisk n) (hqneg : ∀ z ∈ ball x r, q z ≤ 0)
    (hann : ∀ z : ComplexModel n, 3 / 4 * r ≤ ‖z - x‖ → ‖z - x‖ ≤ r → q z < H z)
    (hqα : ∀ hqV : IsLocallyBoundedPshOn ⟨ball x r, isOpen_ball⟩ q,
      (volume.withDensity fun z => ENNReal.ofReal (mongeAmpereConst n * F z ^ n)).restrict
        (ball x r) ≤ canonicalBedfordTaylorMeasure ⟨ball x r, isOpen_ball⟩ q hqV) :
    (fun z => if z ∈ ball x r then max (H z) (q z) else H z) ∈ polydiskSubsolutions F := by
  classical
  obtain ⟨hH, hH0, hHα⟩ := hHmem
  set P := unitPolydiskOpens n with hPdef
  set comp : ComplexModel n → ℝ := fun z ↦ if z ∈ ball x r then max (H z) (q z) else H z
    with hcompdef
  have hcompeq : ∀ z : ComplexModel n, 3 / 4 * r < ‖z - x‖ → comp z = H z := by
    intro z hz
    by_cases hzb : z ∈ ball x r
    · have h2 : ‖z - x‖ ≤ r := by
        have := mem_ball.mp hzb
        rw [dist_eq_norm] at this
        exact this.le
      simp only [hcompdef, if_pos hzb]
      exact max_eq_left (hann z hz.le h2).le
    · simp only [hcompdef, if_neg hzb]
  have hcompball : ∀ z ∈ ball x r, comp z = max (H z) (q z) := fun z hz => by
    simp only [hcompdef, if_pos hz]
  have hqB : IsLocallyBoundedPshOn P q := isLocallyBoundedPshOn_of_contDiff hqC hqlevi
  have hopenFar : IsOpen {z : ComplexModel n | 3 / 4 * r < ‖z - x‖} :=
    isOpen_lt continuous_const (by fun_prop)
  have hfar : ∀ y, y ∉ ball x r → 3 / 4 * r < ‖y - x‖ ∨ r ≤ 0 := by
    intro y hy
    by_cases hr : r ≤ 0
    · exact Or.inr hr
    · left
      have : r ≤ ‖y - x‖ := by
        by_contra hcon
        push Not at hcon
        exact hy (mem_ball.mpr (by rwa [dist_eq_norm]))
      push Not at hr
      linarith
  have hcomppsh : PlurisubharmonicOn (fun z ↦ (comp z : EReal)) (P : Set (ComplexModel n)) := by
    intro y hy
    by_cases hyr : y ∈ ball x r
    · have hmaxpsh : PlurisubharmonicAt (fun z ↦ max ((H z : EReal)) ((q z : EReal))) y :=
        (hH.1 y hy).max (hqB.1 y hy)
      refine hmaxpsh.congr ?_
      filter_upwards [isOpen_ball.mem_nhds hyr] with z hz
      rw [hcompball z hz]
      exact (coe_max_eq_max_coe (H z) (q z)).symm
    · rcases hfar y hyr with hyfar | hr
      · refine (hH.1 y hy).congr ?_
        filter_upwards [hopenFar.mem_nhds hyfar] with z hz
        exact congrArg (fun t : ℝ ↦ (t : EReal)) (hcompeq z hz).symm
      · refine (hH.1 y hy).congr (Eventually.of_forall fun z => ?_)
        have : z ∉ ball x r := fun hz => by
          have := mem_ball.mp hz
          linarith [dist_nonneg (x := z) (y := x)]
        simp only [hcompdef, if_neg this]
  have hcompB : IsLocallyBoundedPshOn P comp := by
    refine ⟨hcomppsh, fun z hz => ?_⟩
    obtain ⟨V, hzV, hVP, C₁, hC₁⟩ := hH.2 z hz
    obtain ⟨W, hzW, -, C₂, hC₂⟩ := hqB.2 z hz
    refine ⟨V ⊓ W, ⟨hzV, hzW⟩, inf_le_left.trans hVP, C₁ + C₂, fun w hw => ?_⟩
    have hHw := hC₁ w hw.1
    have hqw := hC₂ w hw.2
    by_cases hwb : w ∈ ball x r
    · rw [hcompball w hwb]
      have h1 : |max (H w) (q w)| ≤ |H w| + |q w| := by
        rcases le_total (H w) (q w) with h | h
        · rw [max_eq_right h]; linarith [abs_nonneg (H w)]
        · rw [max_eq_left h]; linarith [abs_nonneg (q w)]
      linarith
    · simp only [hcompdef, if_neg hwb]
      linarith [abs_nonneg (q w)]
  set α : Measure (ComplexModel n) :=
    volume.withDensity fun z => ENNReal.ofReal (mongeAmpereConst n * F z ^ n) with hαdef
  obtain ⟨Cb, -, hCb⟩ := exists_bound_of_continuous hFc
  have hαf : ∀ K, IsCompact K → K ⊆ (P : Set (ComplexModel n)) → α K < ⊤ :=
    withDensity_finite_of_bounded hCb
  have hαP : ∀ W : Opens (ComplexModel n), W ≤ P →
      α.restrict (W : Set (ComplexModel n)) ≤
        (canonicalBedfordTaylorMeasure P H hH).restrict (W : Set (ComplexModel n)) := by
    intro W hWP
    have := Measure.restrict_mono (s := (W : Set (ComplexModel n))) subset_rfl hHα
    rwa [polydiskDensityMeasure_eq_restrict, Measure.restrict_restrict_of_subset hWP] at this
  refine ⟨hcompB, fun z hz => ?_, ?_⟩
  · by_cases hzb : z ∈ ball x r
    · rw [hcompball z hzb]
      exact max_le (hH0 z hz) (hqneg z hzb)
    · simp only [hcompdef, if_neg hzb]
      exact hH0 z hz
  rw [polydiskDensityMeasure_eq_restrict]
  have hglue := restrict_le_restrict_of_isLindelof
    (μ := α) (ν := canonicalBedfordTaylorMeasure P comp hcompB)
    (HereditarilyLindelofSpace.isLindelof (P : Set (ComplexModel n))) fun y hy => by
      by_cases hyb : y ∈ ball x r
      · -- near the bump: the maximum of two subsolutions
        set V : Opens (ComplexModel n) := ⟨ball x r, isOpen_ball⟩ with hVdef
        have hVP : V ≤ P := hballP
        have hHV : IsLocallyBoundedPshOn V H := IsLocallyBoundedPshOn.mono_opens hH hVP
        have hqV : IsLocallyBoundedPshOn V q := isLocallyBoundedPshOn_of_contDiff hqC hqlevi
        have hcompV : IsLocallyBoundedPshOn V comp := IsLocallyBoundedPshOn.mono_opens hcompB hVP
        have hmV : IsLocallyBoundedPshOn V fun z => max (H z) (q z) :=
          IsLocallyBoundedPshOn.max hHV hqV
        have hαH : α.restrict (V : Set (ComplexModel n)) ≤
            canonicalBedfordTaylorMeasure V H hHV := by
          rw [← canonicalBedfordTaylorMeasure_restrict hVP hH hHV]
          exact hαP V hVP
        have hmax := ma_ge_max hn hHV hqV (fun K hK hKV => hαf K hK (hKV.trans hVP)) hαH
          (hqα hqV) hmV
        refine ⟨ball x r, isOpen_ball, hyb, ?_⟩
        have heq : (canonicalBedfordTaylorMeasure P comp hcompB).restrict (ball x r) =
            canonicalBedfordTaylorMeasure V (fun z => max (H z) (q z)) hmV := by
          rw [show ball x r = (V : Set (ComplexModel n)) from rfl,
            canonicalBedfordTaylorMeasure_restrict hVP hcompB hcompV]
          exact (isBTLimit_canonicalBedfordTaylorMeasure hcompV).unique
            ((isBTLimit_canonicalBedfordTaylorMeasure hmV).congr fun _ z hz =>
              (hcompball z hz).symm)
        rw [heq]
        exact hmax
      · -- away from the bump the competitor is `H`
        set W : Opens (ComplexModel n) :=
          ⟨(P : Set (ComplexModel n)) ∩ {z | 3 / 4 * r < ‖z - x‖}, P.isOpen.inter hopenFar⟩
          with hWdef
        have hWP : W ≤ P := inter_subset_left
        rcases hfar y hyb with hyfar | hr
        · refine ⟨W, W.isOpen, ⟨hy, hyfar⟩, ?_⟩
          have heq : (canonicalBedfordTaylorMeasure P comp hcompB).restrict
              (W : Set (ComplexModel n)) =
              (canonicalBedfordTaylorMeasure P H hH).restrict (W : Set (ComplexModel n)) :=
            (isBTLimit_canonicalBedfordTaylorMeasure hcompB).restrict_eq_of_eqOn
              (isBTLimit_canonicalBedfordTaylorMeasure hH) hWP fun _ z hz => hcompeq z hz.2
          rw [heq]
          exact hαP W hWP
        · refine ⟨P, P.isOpen, hy, ?_⟩
          have heq : canonicalBedfordTaylorMeasure P comp hcompB =
              canonicalBedfordTaylorMeasure P H hH :=
            (isBTLimit_canonicalBedfordTaylorMeasure hcompB).unique
              ((isBTLimit_canonicalBedfordTaylorMeasure hH).congr fun _ z _ => by
                have : z ∉ ball x r := fun hz => by
                  have := mem_ball.mp hz
                  linarith [dist_nonneg (x := z) (y := x)]
                simp only [hcompdef, if_neg this])
          rw [heq]
          exact hαP P le_rfl
  exact hglue.trans Measure.restrict_le_self

/-! ### The bump argument -/

/-- **FPT `thm:continuous-density-ball-dirichlet`, Step 3 (the bump argument), on the polydisk.**
At every point where the envelope `H_F` has a second-order expansion, the determinant of its
complex Hessian is at most `Fⁿ`. -/
theorem det_le_of_hasPeanoExpansion (hn : 0 < n) {F : ComplexModel n → ℝ} (hF : ContDiff ℝ 2 F)
    (hF0 : ∀ z, 0 ≤ F z) {x : ComplexModel n} (hx : x ∈ unitPolydisk n)
    {A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ} (hsymm : ∀ v w, A v w = A w v)
    (hpeano : HasPeanoExpansionAt (polydiskEnvelope F) x (fderiv ℝ (polydiskEnvelope F) x) A)
    (hpsd : (complexHessianOfBilin A).PosSemidef) :
    (complexHessianOfBilin A).det.re ≤ F x ^ n := by
  classical
  by_contra hlt
  push Not at hlt
  set H := polydiskEnvelope F with hHdef
  set L := fderiv ℝ H x with hLdef
  have hFc : Continuous F := hF.continuous
  have hHmem := polydiskEnvelope_mem hn hFc hF0
  set d : ℝ := (complexHessianOfBilin A).det.re with hd
  set f₀ : ℝ := F x ^ n with hf₀
  have hf₀0 : 0 ≤ f₀ := pow_nonneg (hF0 x) n
  have hd0 : 0 < d := lt_of_le_of_lt hf₀0 hlt
  obtain ⟨c₀, hc₀, hlevi⟩ := exists_leviFormOfBilin_lower hn hsymm
    (posDef_of_posSemidef_of_det_re_pos hpsd hd0)
  have hHx : H x < 0 :=
    neg_of_hasPeanoExpansion hn isOpen_unitPolydisk hHmem.2.1 hx hpeano hc₀ hlevi
  -- the fraction `t` of the Levi form to remove
  set C : ℝ := (d + f₀) / 2 with hCdef
  have hCf : f₀ < C := by rw [hCdef]; linarith
  have hCd : C < d := by rw [hCdef]; linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set t : ℝ := min (1 / 2) ((d - C) / (n * d)) with htdef
  have ht0 : 0 < t := lt_min (by norm_num) (div_pos (by linarith) (by positivity))
  have ht1 : t ≤ 1 / 2 := min_le_left _ _
  have htd : C ≤ (1 - t) ^ n * d := by
    have hb : 1 + (n : ℝ) * (-t) ≤ (1 + -t) ^ n := one_add_mul_le_pow (by linarith) n
    have hle : t ≤ (d - C) / (n * d) := min_le_right _ _
    have htn : (n : ℝ) * t * d ≤ d - C := by
      calc (n : ℝ) * t * d = t * (n * d) := by ring
        _ ≤ (d - C) / (n * d) * (n * d) := mul_le_mul_of_nonneg_right hle (by positivity)
        _ = d - C := by field_simp
    have : (1 - (n : ℝ) * t) * d ≤ (1 - t) ^ n * d :=
      mul_le_mul_of_nonneg_right (by simpa [sub_eq_add_neg] using hb) hd0.le
    nlinarith
  -- radii
  obtain ⟨r0, hr0, hr0P⟩ := Metric.isOpen_iff.mp isOpen_unitPolydisk x hx
  obtain ⟨r₁, hr₁, hr₁F⟩ : ∃ r₁ > 0, ∀ z ∈ ball x r₁, F z ^ n < C := by
    obtain ⟨r₁, hr₁, h⟩ := Metric.continuousAt_iff.mp (hFc.pow n).continuousAt (C - f₀)
      (by linarith)
    refine ⟨r₁, hr₁, fun z hz => ?_⟩
    have h' : |F z ^ n - F x ^ n| < C - f₀ := by simpa [Real.dist_eq] using h (mem_ball.mp hz)
    linarith [(abs_lt.mp h').2, hf₀]
  set At : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ := A - t • leviBilin A with hAtdef
  have hAtsymm : ∀ v w, At v w = At w v := by
    intro v w
    simp only [hAtdef, _root_.sub_apply, _root_.smul_apply, smul_eq_mul]
    rw [hsymm v w, leviBilin_symm hsymm v w]
  have hq₀c : Continuous (quadPoly (H x) 0 L At x) := contDiff_quadPoly.continuous
  obtain ⟨r₂, hr₂, hr₂q⟩ : ∃ r₂ > 0, ∀ z ∈ ball x r₂, quadPoly (H x) 0 L At x z < H x / 2 := by
    have hq₀x : quadPoly (H x) 0 L At x x = H x := by simp [quadPoly]
    obtain ⟨r₂, hr₂, h⟩ := Metric.continuousAt_iff.mp hq₀c.continuousAt (-(H x) / 2)
      (by linarith)
    refine ⟨r₂, hr₂, fun z hz => ?_⟩
    have := h (mem_ball.mp hz)
    rw [Real.dist_eq, hq₀x] at this
    linarith [(abs_lt.mp this).2]
  obtain ⟨ρ₂, hρ₂, hann⟩ := exists_annulus_lt hpeano hc₀ hlevi ht0
  set ct : ℝ := t * c₀ with hctdef
  have hct : 0 < ct := by positivity
  set r : ℝ := min (min (min (ρ₂ / 2) r0) (min r₁ r₂)) (min 1 (-(H x) / ct)) with hrdef
  have hr : 0 < r := lt_min (lt_min (lt_min (by linarith) hr0) (lt_min hr₁ hr₂))
    (lt_min one_pos (div_pos (by linarith) hct))
  have hrρ : r < ρ₂ := lt_of_le_of_lt ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _))) (by linarith)
  have hrr0 : r ≤ r0 := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrr₁ : r ≤ r₁ := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrr₂ : r ≤ r₂ := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hrH : r ≤ -(H x) / ct := (min_le_right _ _).trans (min_le_right _ _)
  set δ : ℝ := t * c₀ * r ^ 2 / 4 with hδdef
  have hδ : 0 < δ := by positivity
  have hδH : δ < -(H x) / 2 := by
    have h1 : ct * r ≤ -(H x) := by
      have := mul_le_mul_of_nonneg_left hrH hct.le
      rwa [mul_div_cancel₀ _ hct.ne'] at this
    have h2 : r ^ 2 ≤ r := by nlinarith
    have h3 : ct * r ^ 2 ≤ ct * r := mul_le_mul_of_nonneg_left h2 hct.le
    rw [hδdef]
    linarith
  set q : ComplexModel n → ℝ := quadPoly (H x) δ L At x with hqdef
  have hqq₀ : ∀ z, q z = quadPoly (H x) 0 L At x z + δ := fun z => by simp [hqdef, quadPoly]
  have hballP : ball x r ⊆ unitPolydisk n := (ball_subset_ball hrr0).trans hr0P
  have hqneg : ∀ z ∈ ball x r, q z ≤ 0 := by
    intro z hz
    rw [hqq₀]
    have := hr₂q z (ball_subset_ball hrr₂ hz)
    linarith
  -- `q` is plurisubharmonic with constant Monge–Ampère density `(1 - t)ⁿ det`
  have hqC2 : ContDiff ℝ 2 q :=
    contDiff_quadPoly.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hqlevi : ∀ y v, 0 ≤ leviForm q y v := by
    intro y v
    rw [hqdef, leviForm_quadPoly hAtsymm, hAtdef, leviFormOfBilin_sub_smul_leviBilin]
    exact mul_nonneg (by linarith) ((mul_nonneg hc₀.le (sq_nonneg _)).trans (hlevi v))
  have hhess : complexHessianOfBilin At = ((1 - t : ℝ) : ℂ) • complexHessianOfBilin A := by
    rw [hAtdef, complexHessianOfBilin_sub_smul_leviBilin]
  have hdet : (complexHessianOfBilin At).det.re = (1 - t) ^ n * d := by
    rw [hhess, Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  have hpsdt : (complexHessianOfBilin At).PosSemidef := by
    rw [hhess]
    have h1t : (0 : ℝ) ≤ 1 - t := by linarith
    have : ((1 - t : ℝ) : ℂ) = ((1 - t : ℝ) : ℂ) := rfl
    exact hpsd.smul (by exact_mod_cast h1t)
  have hqα : ∀ hqV : IsLocallyBoundedPshOn ⟨ball x r, isOpen_ball⟩ q,
      (volume.withDensity fun z => ENNReal.ofReal (mongeAmpereConst n * F z ^ n)).restrict
        (ball x r) ≤ canonicalBedfordTaylorMeasure ⟨ball x r, isOpen_ball⟩ q hqV := by
    intro hqV
    rw [canonicalBedfordTaylorMeasure_quadPoly hAtsymm hpsdt hqV,
      restrict_withDensity isOpen_ball.measurableSet]
    refine withDensity_mono ?_
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with z hz
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ mongeAmpereConst_pos.le)
    rw [hdet]
    have := hr₁F z (ball_subset_ball hrr₁ hz)
    linarith
  have hannq : ∀ z : ComplexModel n, 3 / 4 * r ≤ ‖z - x‖ → ‖z - x‖ ≤ r → q z < H z :=
    hann r hr hrρ
  have hmem := glue_mem_polydiskSubsolutions hn hFc hHmem hqC2 hqlevi hballP hqneg hannq hqα
  have hle := le_polydiskEnvelope hn hFc hF0 hmem hx
  have hxball : x ∈ ball x r := mem_ball_self hr
  rw [if_pos hxball] at hle
  have hqx : q x = H x + δ := by simp [hqdef, quadPoly]
  rw [hqx] at hle
  linarith [le_max_right (H x) (H x + δ)]

/-! ### The equation -/

/-- **The Dirichlet problem with `C²` density on the polydisk** (FPT
`thm:continuous-density-ball-dirichlet`, the equation for data of class `C²`, with zero boundary
data, on the unit polydisk): for `F ≥ 0` of class `C²`, the envelope `H_F` of the nonpositive
subsolutions solves `(ddᶜH_F)ⁿ = Fⁿ ηⁿ` on `P`. -/
theorem ma_polydiskEnvelope_eq (hn : 0 < n) {F : ComplexModel n → ℝ} (hF : ContDiff ℝ 2 F)
    (hF0 : ∀ z, 0 ≤ F z) :
    ∃ hH : IsLocallyBoundedPshOn (unitPolydiskOpens n) (polydiskEnvelope F),
      canonicalBedfordTaylorMeasure (unitPolydiskOpens n) _ hH = polydiskDensityMeasure F := by
  have hFc : Continuous F := hF.continuous
  obtain ⟨hH, -, hHα⟩ := polydiskEnvelope_mem hn hFc hF0
  refine ⟨hH, le_antisymm ?_ hHα⟩
  exact canonicalBedfordTaylorMeasure_le_of_peano hH
    (isLocallySemiconcaveOn_polydiskEnvelope hn hF hF0) (hFc.pow n) (fun z => pow_nonneg (hF0 z) n)
    fun x hx A hsymm hpe hpsd => det_le_of_hasPeanoExpansion hn hF hF0 hx hsymm hpe hpsd

end SGPT.Envelopes.MADirichlet
