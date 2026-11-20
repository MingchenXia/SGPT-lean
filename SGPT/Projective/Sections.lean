import SGPT.Projective.FubiniStudy
import SGPT.Foundations.Analysis.Pending.AnalyticSingularities
import SGPT.Foundations.Analysis.Pending.GlobalMultilinearExpansion
import SGPT.Foundations.Analysis.Pending.LocalPotentials
import SGPT.Foundations.Analysis.Pending.NefBoundedMixedMass
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple
import SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Sections of `O(d)` and their Fubini–Study potentials on `ℙᴺ`

The global sections of `O_{ℙᴺ}(d)` are the homogeneous polynomials of degree `d` in the
homogeneous coordinates `Z_0, …, Z_N`, and the Fubini–Study metric `h_FS` of `O(1)` (curvature
`ω_FS`) gives them the pointwise norm `|s|²_{h_FS^d}([Z]) = |P(Z)|² / ‖Z‖^{2d}`, which is
well defined because `P(cZ) = c^d P(Z)`.  For a finite family `s_1, …, s_r` we use
`∑_k |P_k(Z)|² / ‖Z‖^{2d}`.  This file proves:

* `sectionNormSq_smul`, `sectionLog_mk`: well-definedness of `log ∑_k |s_k|²_{h_FS^d}` on `ℙᴺ`;
* `chartFunction_sectionLog`: in the affine chart `U_i` it equals
  `log ∑_k |P_k(insertNth i 1 z)|² - d · log(1 + ‖z‖²)`;
* `isThetaPshPotential_smul_sectionLog`: for `0 < c` with `c d ≤ 1` and not all `P_k = 0`,
  `c · log ∑_k |s_k|²_{h_FS^d} ∈ PSH(ℙᴺ, ω_FS)` (`d⁻¹ log |s|²_{h^d}` is the potential of the
  current `d⁻¹ [div s]` in `c₁(O(1)) = {ω_FS}`);
* `hasManifoldAnalyticSingularityType_smul_sectionLog`: these potentials have analytic
  singularities (for rational `c > 0`);
* the coordinate potentials `coordLog i = log(|Z_i|² / ‖Z‖²)` (`d = 1`, `P = Z_i`), with chart
  expression `log |z_k|² - log(1 + ‖z‖²)` in the chart `U_j` and `-log(1 + ‖z‖²)` in `U_i`
  (`coordLog_affinePoint_self`: `ω_FS = -ddᶜ log |Z_i|²_{h_FS}` on `U_i`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open scoped Manifold ContDiff

namespace SGPT.Projective.ComplexProjectiveSpace

variable {N : ℕ} {r : ℕ}

/-! ### Homogeneous polynomials -/

/-- `P(c v) = c^d P(v)` for a homogeneous polynomial `P` of degree `d`. -/
theorem eval_smul_of_isHomogeneous {P : MvPolynomial (Fin (N + 1)) ℂ} {d : ℕ}
    (hP : P.IsHomogeneous d) (c : ℂ) (v : Fin (N + 1) → ℂ) :
    MvPolynomial.eval (c • v) P = c ^ d * MvPolynomial.eval v P := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i, m i = d := by
    have h := hP (MvPolynomial.mem_support_iff.mp hm)
    rw [← h]
    simp [Finsupp.weight_apply, Finsupp.sum_fintype]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg]
  ring

/-- A nonzero homogeneous polynomial of positive degree vanishes at the origin, and does not
vanish at some nonzero vector. -/
theorem exists_eval_ne_zero {P : MvPolynomial (Fin (N + 1)) ℂ} {d : ℕ} (hP : P.IsHomogeneous d)
    (hd : 0 < d) (hP0 : P ≠ 0) :
    ∃ v : Fin (N + 1) → ℂ, v ≠ 0 ∧ MvPolynomial.eval v P ≠ 0 := by
  obtain ⟨v, hv⟩ : ∃ v, MvPolynomial.eval v P ≠ 0 := by
    by_contra h
    push Not at h
    exact hP0 (MvPolynomial.funext fun v => by simpa using h v)
  refine ⟨v, ?_, hv⟩
  rintro rfl
  apply hv
  rw [MvPolynomial.eval_zero]
  rw [MvPolynomial.constantCoeff_eq]
  apply hP.coeff_eq_zero
  simp only [map_zero]
  exact hd.ne

/-! ### The Fubini–Study norm of a family of sections -/

/-- The pointwise Fubini–Study norm `∑_k |P_k(v)|² / ‖v‖^{2d}` of a family of sections
`s_k ∈ H⁰(ℙᴺ, O(d))` given by polynomials `P_k`, at a homogeneous vector `v`. -/
def sectionNormSq (d : ℕ) (P : Fin r → MvPolynomial (Fin (N + 1)) ℂ)
    (v : Fin (N + 1) → ℂ) : ℝ :=
  (∑ k, ‖MvPolynomial.eval v (P k)‖ ^ 2) / homNormSq v ^ d

theorem sectionNormSq_nonneg (d : ℕ) (P : Fin r → MvPolynomial (Fin (N + 1)) ℂ)
    (v : Fin (N + 1) → ℂ) : 0 ≤ sectionNormSq d P v :=
  div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (pow_nonneg (homNormSq_nonneg v) d)

/-- The Fubini–Study norm of homogeneous sections is invariant under rescaling. -/
theorem sectionNormSq_smul {d : ℕ} {P : Fin r → MvPolynomial (Fin (N + 1)) ℂ}
    (hP : ∀ k, (P k).IsHomogeneous d) {c : ℂ} (hc : c ≠ 0) (v : Fin (N + 1) → ℂ) :
    sectionNormSq d P (c • v) = sectionNormSq d P v := by
  unfold sectionNormSq
  have hnum : ∑ k, ‖MvPolynomial.eval (c • v) (P k)‖ ^ 2 =
      (‖c‖ ^ 2) ^ d * ∑ k, ‖MvPolynomial.eval v (P k)‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eval_smul_of_isHomogeneous (hP k), norm_mul, norm_pow]
    ring
  rw [hnum, homNormSq_smul, mul_pow]
  exact mul_div_mul_left _ _ (pow_ne_zero d (pow_ne_zero 2 (norm_ne_zero_iff.mpr hc)))

/-- `log ∑_k |s_k|²_{h_FS^d}` as a function on `ℙᴺ` (value `-∞` at the common zeros). -/
def sectionLog (d : ℕ) (P : Fin r → MvPolynomial (Fin (N + 1)) ℂ)
    (p : ComplexProjectiveSpace N) : EReal :=
  ENNReal.log (ENNReal.ofReal (sectionNormSq d P p.rep))

/-- Well-definedness: `sectionLog` may be computed on any homogeneous representative. -/
theorem sectionLog_mk {d : ℕ} {P : Fin r → MvPolynomial (Fin (N + 1)) ℂ}
    (hP : ∀ k, (P k).IsHomogeneous d) (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) :
    sectionLog d P (mk v hv) = ENNReal.log (ENNReal.ofReal (sectionNormSq d P v)) := by
  obtain ⟨c, hc, hrep⟩ := rep_smul (mk v hv) hv rfl
  rw [sectionLog, hrep, sectionNormSq_smul hP hc]

theorem sectionLog_ne_top (d : ℕ) (P : Fin r → MvPolynomial (Fin (N + 1)) ℂ)
    (p : ComplexProjectiveSpace N) : sectionLog d P p ≠ ⊤ := by
  rw [sectionLog, Ne, ENNReal.log_eq_top_iff]
  exact ENNReal.ofReal_ne_top

/-- `sectionLog = -∞` exactly at the common zeros of the sections. -/
theorem sectionLog_mk_eq_bot_iff {d : ℕ} {P : Fin r → MvPolynomial (Fin (N + 1)) ℂ}
    (hP : ∀ k, (P k).IsHomogeneous d) (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) :
    sectionLog d P (mk v hv) = ⊥ ↔ ∀ k, MvPolynomial.eval v (P k) = 0 := by
  rw [sectionLog_mk hP, ENNReal.log_eq_bot_iff, ENNReal.ofReal_eq_zero]
  have hden : 0 < homNormSq v ^ d := pow_pos (homNormSq_pos hv) d
  unfold sectionNormSq
  rw [div_le_iff₀ hden, zero_mul]
  constructor
  · intro h k
    have hle : ‖MvPolynomial.eval v (P k)‖ ^ 2 ≤ ∑ k, ‖MvPolynomial.eval v (P k)‖ ^ 2 :=
      Finset.single_le_sum (f := fun k => ‖MvPolynomial.eval v (P k)‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
    have : ‖MvPolynomial.eval v (P k)‖ ^ 2 = 0 := le_antisymm (hle.trans h) (sq_nonneg _)
    simpa using this
  · intro h
    simp [h]

/-! ### Chart expressions -/

/-- The dehomogenised generators `z ↦ P_k(insertNth i 1 z)` in the chart `U_i`. -/
def chartGenerators (i : Fin (N + 1)) (P : Fin r → MvPolynomial (Fin (N + 1)) ℂ) :
    Fin r → ComplexModel N → ℂ :=
  fun k z => MvPolynomial.eval (affineLift i z) (P k)

theorem differentiable_chartGenerators (i : Fin (N + 1))
    (P : Fin r → MvPolynomial (Fin (N + 1)) ℂ) (k : Fin r) :
    Differentiable ℂ (chartGenerators i P k) := fun z =>
  ((AnalyticOnNhd.eval_mvPolynomial (P k) (affineLift i z) (mem_univ _)).differentiableAt).comp z
    (differentiable_affineLift i z)

theorem holomorphicGeneratorsAt_chartGenerators (i : Fin (N + 1))
    (P : Fin r → MvPolynomial (Fin (N + 1)) ℂ) (z : ComplexModel N) :
    HolomorphicGeneratorsAt (chartGenerators i P) z :=
  ⟨univ, isOpen_univ, mem_univ z, fun k => (differentiable_chartGenerators i P k).differentiableOn⟩

private theorem log_ofReal_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    ENNReal.log (ENNReal.ofReal (a / b)) =
      ENNReal.log (ENNReal.ofReal a) - ((Real.log b : ℝ) : EReal) := by
  rcases ha.eq_or_lt with rfl | ha'
  · simp
  · rw [ENNReal.log_ofReal_of_pos (div_pos ha' hb), ENNReal.log_ofReal_of_pos ha',
      Real.log_div ha'.ne' hb.ne', EReal.coe_sub]

/-- The value of `sectionLog` at the affine point `z ∈ U_i`:
`log ∑_k |P_k(insertNth i 1 z)|² - d log(1 + ‖z‖²)`. -/
theorem sectionLog_affinePoint {d : ℕ} {P : Fin r → MvPolynomial (Fin (N + 1)) ℂ}
    (hP : ∀ k, (P k).IsHomogeneous d) (i : Fin (N + 1)) (z : ComplexModel N) :
    sectionLog d P (affinePoint i z) =
      generatorLog (chartGenerators i P) z - (((d : ℝ) * fsPotential z : ℝ) : EReal) := by
  rw [affinePoint, sectionLog_mk hP, sectionNormSq, homNormSq_affineLift,
    log_ofReal_div (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity),
    generatorLog_eq_log_sum, Real.log_pow, fsPotential]
  rfl

/-- `sectionLog` in an arbitrary chart of the atlas (which is some `U_i`). -/
theorem chartFunction_sectionLog {d : ℕ} {P : Fin r → MvPolynomial (Fin (N + 1)) ℂ}
    (hP : ∀ k, (P k).IsHomogeneous d) {e : ComplexChart N (ComplexProjectiveSpace N)}
    {i : Fin (N + 1)} (he : e.val = affineChart i) (z : ComplexModel N) :
    chartFunction (sectionLog d P) e z =
      generatorLog (chartGenerators i P) z - (((d : ℝ) * fsPotential z : ℝ) : EReal) := by
  change sectionLog d P (e.val.symm z) = _
  rw [he, affineChart_symm_apply, sectionLog_affinePoint hP]

/-! ### Plurisubharmonicity -/

private theorem ereal_mul_sub_add {a : EReal} (ha : a ≠ ⊤) {c d F : ℝ} (hc : 0 < c)
    (hcd : c * d = 1) :
    (c : EReal) * (a - ((d * F : ℝ) : EReal)) + (F : EReal) = (c : EReal) * a := by
  rcases eq_or_ne a ⊥ with rfl | hb
  · rw [EReal.bot_sub, EReal.coe_mul_bot_of_pos hc, EReal.bot_add]
  · lift a to ℝ using ⟨ha, hb⟩ with x
    rw [← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_mul, EReal.coe_eq_coe_iff]
    have : c * (x - d * F) + F = c * x + (1 - c * d) * F := by ring
    rw [this, hcd]
    ring

/-- `d⁻¹ log ∑_k |s_k|²_{h_FS^d}` satisfies the `ω_FS`-psh criterion: in the chart `U_i`,
with the potential `log(1 + ‖z‖²)` of `ω_FS`, the corrected function is
`d⁻¹ log ∑_k |P_k(insertNth i 1 z)|²`. -/
theorem thetaPlurisubharmonic_inv_smul_sectionLog {d : ℕ} (hd : 0 < d)
    {P : Fin r → MvPolynomial (Fin (N + 1)) ℂ} (hP : ∀ k, (P k).IsHomogeneous d) :
    ThetaPlurisubharmonic (fsBackground (N := N)).form.val
      (fun p => (((d : ℝ)⁻¹ : ℝ) : EReal) * sectionLog d P p) := by
  intro e z _
  obtain ⟨i, hi⟩ := (mem_atlas_iff e.val).mp e.property
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨univ, fsPotential, mem_univ z, isSmoothLocalPotential_fsPotential e, fun y _ => ?_⟩
  have heq : (fun y => chartFunction (fun p => (((d : ℝ)⁻¹ : ℝ) : EReal) * sectionLog d P p) e y +
      (fsPotential y : EReal)) =
      fun y => (((d : ℝ)⁻¹ : ℝ) : EReal) * generatorLog (chartGenerators i P) y := by
    funext y
    change (((d : ℝ)⁻¹ : ℝ) : EReal) * chartFunction (sectionLog d P) e y + _ = _
    rw [chartFunction_sectionLog hP hi y]
    exact ereal_mul_sub_add (logNormSq_ne_top _) (inv_pos.mpr hd') (inv_mul_cancel₀ hd'.ne')
  rw [heq]
  exact Pending.plurisubharmonicAt_scaled_generatorLog
    (holomorphicGeneratorsAt_chartGenerators i P y) (inv_pos.mpr hd')

/-- The sections have a point where they do not all vanish. -/
theorem exists_sectionLog_ne_bot {d : ℕ} (hd : 0 < d) {P : Fin r → MvPolynomial (Fin (N + 1)) ℂ}
    (hP : ∀ k, (P k).IsHomogeneous d) (hne : ∃ k, P k ≠ 0) :
    ∃ p : ComplexProjectiveSpace N, sectionLog d P p ≠ ⊥ := by
  obtain ⟨k, hk⟩ := hne
  obtain ⟨v, hv, hvk⟩ := exists_eval_ne_zero (hP k) hd hk
  refine ⟨mk v hv, ?_⟩
  rw [Ne, sectionLog_mk_eq_bot_iff hP]
  exact fun h => hvk (h k)

/-- Source: `ω_FS ∈ c₁(O(1))` and `ddᶜ log |s|²_{h^d} = [div s] - d ω_FS`.  For `0 < c` with
`c d ≤ 1` and sections `s_k ∈ H⁰(ℙᴺ, O(d))` not all zero,
`c · log ∑_k |s_k|²_{h_FS^d} ∈ PSH(ℙᴺ, ω_FS)`. -/
theorem isThetaPshPotential_smul_sectionLog {d : ℕ} (hd : 0 < d)
    {P : Fin r → MvPolynomial (Fin (N + 1)) ℂ} (hP : ∀ k, (P k).IsHomogeneous d)
    (hne : ∃ k, P k ≠ 0) {c : ℝ} (hc : 0 < c) (hcd : c * d ≤ 1) :
    IsThetaPshPotential (fsBackground (N := N)).form.val
      (fun p => (c : EReal) * sectionLog d P p) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 := thetaPlurisubharmonic_inv_smul_sectionLog hd hP
  have h2 := Pending.GlobalMultilinearExpansion.thetaPlurisubharmonic_smul
    (γ := (fsBackground (N := N)).form) (mul_pos hc hd') h1
  have hsemi := Pending.NefBoundedMixedMass.isSemipositive_smul
    (fsBackground (N := N)).isSemipositive (sub_nonneg.mpr hcd)
  have h3 := Pending.LocalPotentials.thetaPlurisubharmonic_add_of_semipositive h2 hsemi
  have hform : (c * d) • (fsBackground (N := N)).form + (1 - c * d) • (fsBackground (N := N)).form =
      (fsBackground (N := N)).form := by module
  have hfun : (fun p => ((c * d : ℝ) : EReal) * ((((d : ℝ)⁻¹ : ℝ) : EReal) * sectionLog d P p)) =
      fun p => (c : EReal) * sectionLog d P p := by
    funext p
    rw [← mul_assoc, ← EReal.coe_mul, mul_assoc, mul_inv_cancel₀ hd'.ne', mul_one]
  rw [hform, hfun] at h3
  refine ⟨h3, Pending.ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot h3 ?_⟩
  obtain ⟨p, hp⟩ := exists_sectionLog_ne_bot hd hP hne
  refine ⟨p, ?_⟩
  have htop := sectionLog_ne_top d P p
  lift sectionLog d P p to ℝ using ⟨htop, hp⟩ with x
  rw [← EReal.coe_mul]
  exact EReal.coe_ne_bot _

/-- The potentials `c · log ∑_k |s_k|²_{h_FS^d}` (`c ∈ ℚ_{>0}`) have analytic singularities:
in `U_i` they are `c log ∑_k |P_k(insertNth i 1 z)|² + O(1)`. -/
theorem hasManifoldAnalyticSingularityType_smul_sectionLog {d : ℕ}
    {P : Fin r → MvPolynomial (Fin (N + 1)) ℂ} (hP : ∀ k, (P k).IsHomogeneous d)
    {c : ℚ} (hc : 0 < c) :
    HasManifoldAnalyticSingularityType (n := N)
      (fun p : ComplexProjectiveSpace N => ((c : ℝ) : EReal) * sectionLog d P p) := by
  intro e z _
  obtain ⟨i, hi⟩ := (mem_atlas_iff e.val).mp e.property
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hcont : ContinuousAt (fun y : ComplexModel N => -((c : ℝ) * ((d : ℝ) * fsPotential y)))
      z := (continuous_const.mul (continuous_const.mul contDiff_fsPotential.continuous)).neg
        |>.continuousAt
  refine ⟨c, r, chartGenerators i P, ⟨hc', holomorphicGeneratorsAt_chartGenerators i P z,
    fun y => -((c : ℝ) * ((d : ℝ) * fsPotential y)), boundedRealGermAt_of_continuousAt hcont,
    Eventually.of_forall fun y => ?_⟩⟩
  change ((c : ℝ) : EReal) * chartFunction (sectionLog d P) e y = _
  dsimp only
  rw [chartFunction_sectionLog hP hi y]
  have htop : generatorLog (chartGenerators i P) y ≠ ⊤ := logNormSq_ne_top _
  rcases eq_or_ne (generatorLog (chartGenerators i P) y) ⊥ with hb | hb
  · rw [hb, EReal.bot_sub, EReal.coe_mul_bot_of_pos hc', EReal.bot_add]
  · lift generatorLog (chartGenerators i P) y to ℝ using ⟨htop, hb⟩ with x
    rw [← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
      EReal.coe_eq_coe_iff]
    ring

/-! ### Coordinate potentials -/

/-- The coordinate section `Z_i ∈ H⁰(ℙᴺ, O(1))`. -/
def coordSection (i : Fin (N + 1)) : Fin 1 → MvPolynomial (Fin (N + 1)) ℂ :=
  fun _ => MvPolynomial.X i

theorem coordSection_isHomogeneous (i : Fin (N + 1)) (k : Fin 1) :
    (coordSection i k).IsHomogeneous 1 :=
  MvPolynomial.isHomogeneous_X ℂ i

/-- The coordinate potential `log(|Z_i|² / ‖Z‖²) = log |Z_i|²_{h_FS}`. -/
def coordLog (i : Fin (N + 1)) : ComplexProjectiveSpace N → EReal :=
  sectionLog 1 (coordSection i)

theorem coordLog_mk (i : Fin (N + 1)) (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) :
    coordLog i (mk v hv) = ENNReal.log (ENNReal.ofReal (‖v i‖ ^ 2 / homNormSq v)) := by
  rw [coordLog, sectionLog_mk (coordSection_isHomogeneous i), sectionNormSq]
  simp [coordSection]

theorem coordLog_nonpos (i : Fin (N + 1)) (p : ComplexProjectiveSpace N) : coordLog i p ≤ 0 := by
  induction p using ind with
  | h v hv =>
    rw [coordLog_mk]
    have hle : ‖v i‖ ^ 2 / homNormSq v ≤ 1 := by
      rw [div_le_one (homNormSq_pos hv)]
      exact Finset.single_le_sum (f := fun m => ‖v m‖ ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ i)
    calc ENNReal.log (ENNReal.ofReal (‖v i‖ ^ 2 / homNormSq v))
        ≤ ENNReal.log (ENNReal.ofReal 1) := ENNReal.log_monotone (ENNReal.ofReal_le_ofReal hle)
      _ = 0 := by simp

theorem coordLog_mk_eq_bot_iff (i : Fin (N + 1)) (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) :
    coordLog i (mk v hv) = ⊥ ↔ v i = 0 := by
  rw [coordLog, sectionLog_mk_eq_bot_iff (coordSection_isHomogeneous i)]
  simp [coordSection]

theorem coordLog_ne_top (i : Fin (N + 1)) (p : ComplexProjectiveSpace N) : coordLog i p ≠ ⊤ :=
  sectionLog_ne_top _ _ p

/-- In the chart `U_j`, `log(|Z_i|²/‖Z‖²) = log |w_i|² - log(1 + ‖z‖²)`, `w = insertNth j 1 z`
(so `log |z_k|² - log(1 + ‖z‖²)` for `i = j.succAbove k`). -/
theorem coordLog_affinePoint (i j : Fin (N + 1)) (z : ComplexModel N) :
    coordLog i (affinePoint j z) = logNormSq (affineLift j z i) - (fsPotential z : EReal) := by
  rw [coordLog, sectionLog_affinePoint (coordSection_isHomogeneous i)]
  simp only [Nat.cast_one, one_mul]
  congr 1
  rw [generatorLog]
  simp only [logNormSq, chartGenerators, coordSection, MvPolynomial.eval_X,
    EuclideanSpace.norm_sq_eq, generatorVector, Finset.univ_unique, Finset.sum_singleton]

theorem coordLog_affinePoint_succAbove (j : Fin (N + 1)) (k : Fin N) (z : ComplexModel N) :
    coordLog (j.succAbove k) (affinePoint j z) = logNormSq (z k) - (fsPotential z : EReal) := by
  rw [coordLog_affinePoint, affineLift_succAbove]

/-- In its own chart `U_i`, `log |Z_i|²_{h_FS} = -log(1 + ‖z‖²)`: the curvature of
`(O(1), h_FS)` is `ω_FS`. -/
theorem coordLog_affinePoint_self (i : Fin (N + 1)) (z : ComplexModel N) :
    coordLog i (affinePoint i z) = ((-fsPotential z : ℝ) : EReal) := by
  rw [coordLog_affinePoint, affineLift_same]
  simp [logNormSq, EReal.coe_neg, sub_eq_add_neg]

/-- `c · log(|Z_i|²/‖Z‖²) ∈ PSH(ℙᴺ, ω_FS)` for `0 < c ≤ 1`. -/
theorem isThetaPshPotential_smul_coordLog (i : Fin (N + 1)) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    IsThetaPshPotential (fsBackground (N := N)).form.val (fun p => (c : EReal) * coordLog i p) :=
  isThetaPshPotential_smul_sectionLog one_pos (coordSection_isHomogeneous i)
    ⟨0, MvPolynomial.X_ne_zero i⟩ hc (by simpa using hc1)

/-- `log(|Z_i|²/‖Z‖²) ∈ PSH(ℙᴺ, ω_FS)`. -/
theorem isThetaPshPotential_coordLog (i : Fin (N + 1)) :
    IsThetaPshPotential (fsBackground (N := N)).form.val (coordLog i) := by
  simpa using isThetaPshPotential_smul_coordLog (N := N) i one_pos le_rfl

theorem hasManifoldAnalyticSingularityType_smul_coordLog (i : Fin (N + 1)) {c : ℚ}
    (hc : 0 < c) :
    HasManifoldAnalyticSingularityType (n := N)
      (fun p : ComplexProjectiveSpace N => ((c : ℝ) : EReal) * coordLog i p) :=
  hasManifoldAnalyticSingularityType_smul_sectionLog (coordSection_isHomogeneous i) hc

theorem hasManifoldAnalyticSingularityType_coordLog (i : Fin (N + 1)) :
    HasManifoldAnalyticSingularityType (n := N) (coordLog (N := N) i) := by
  simpa using hasManifoldAnalyticSingularityType_smul_coordLog (N := N) i (c := 1) one_pos

end SGPT.Projective.ComplexProjectiveSpace
