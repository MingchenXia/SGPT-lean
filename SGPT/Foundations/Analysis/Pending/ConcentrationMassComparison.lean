import SGPT.Foundations.Analysis.Pending.SubmanifoldMassConcentration

set_option autoImplicit false

/-!
# The integration step of Boucksom's concentration estimate (bou02 4.12, dp04 2.6)

Source: Boucksom, *On the volume of a line bundle*, Lemma 4.12 (`bou02-volume:4.12`), and
Demailly--Păun, Proposition 2.6 (`dp04-kahler-cone:2.6`, (2.7')--(2.9'')): with `α_ε` the solution of
the Monge--Ampère equation `α_ε^n = C_ε ω_ε^n` in the Kähler class `a + ε{ω}` (Yau), the mass of
`α_ε^p ∧ ω^{n-p}` near `Y` is bounded below by the concentrated mass of `ω_ε^p ∧ ω^{n-p}`.  Step "integration"
of blueprint `bou:concentrated-current`, agreed with TN23; statement posted on
I-0831 C-0008.  Yau's theorem is NOT used or assumed: the forms `α` with `α^n = c ω_ε^n` are
hypotheses of the lemma (no named input is filed).

## Main results

* `mixedMeasure_le_of_mongeAmpere`: for `ω_ε ≥ ω/2`, `α` Kähler with `α^n = c ω_ε^n` pointwise in
  charts, `p ≤ n`, `t > 0` and every set `S`,
  `ω_ε^p∧ω^{n-p}(S) ≤ (t/c) α^p∧ω^{n-p}(S) + (2^{n-p} n!/t) α^{n-p}∧ω_ε^p(S)` (global mixed measures with
  potentials `0`).
* `le_mixedMeasure_of_mongeAmpere`: hence, if `δ ≤ ω_ε^p∧ω^{n-p}(S)` and `α^{n-p}∧ω_ε^p(S) ≤ M₀`,
  `c δ² / (4 · 2^{n-p} n! M₀) ≤ α^p∧ω^{n-p}(S)` — bou02 4.12's bound, with `S = K ∩ V_ε` and `δ` from
  `SubmanifoldMassConcentration.exists_massConcentration`.

## Proof

Pointwise (`re_mixedCoefficient_le_of_mongeAmpere`, `chartDensity_le_of_mongeAmpere`): at a chart point,
either `C(A[n-p], B[p]) < t det B` and `ConcentrationEigenvalueBound.concentration_bound` gives
`(c/t) C(B[p], C[n-p]) ≤ C(A[p], C[n-p])`, or `C(B[p], C[n-p]) ≤ C(B[p], (2B)[n-p]) = 2^{n-p} n! det B ≤
(2^{n-p} n!/t) C(A[n-p], B[p])` (`ω ≤ 2ω_ε`, Loewner monotonicity, `mixedCoefficient_smul_family`).  The chart
densities are TN23's (`SmoothMixedMeasureDensity`), and `measure_le_of_forall_chart` compares the measures
on a finite measurable partition subordinate to charts.  This is the source's Markov argument without
naming the exceptional set `E`.
-/

open Set Filter MeasureTheory Matrix
open scoped Topology ComplexOrder ENNReal

namespace SGPT.Foundations.Analysis.Pending.ConcentrationMassComparison

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere ConcentrationEigenvalueBound

noncomputable section

/-! ### Matrix level -/

section Matrix

variable {n : ℕ}

theorem re_det_pos_of_posDef {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.PosDef) : 0 < B.det.re := by
  obtain ⟨R, hR, hRB, -⟩ := exists_simultaneous_diagonalization hB hB
  set dr : ℝ := Complex.normSq R.det
  have hdr : 0 < dr := Complex.normSq_pos.mpr hR
  have hd : (star R).det * R.det = (dr : ℂ) := by
    rw [star_eq_conjTranspose, det_conjTranspose, Complex.normSq_eq_conj_mul_self]
    rfl
  have h1 := congrArg Matrix.det hRB
  rw [det_mul, det_mul, det_one] at h1
  have h2 : (dr : ℂ) * B.det = 1 := by rw [← hd]; linear_combination h1
  have h3 : B.det = ((dr⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv]
    field_simp [Complex.ofReal_ne_zero.mpr hdr.ne']
    linear_combination h2
  rw [h3, Complex.ofReal_re]
  positivity

/-- Scaling every slot scales the mixed coefficient by the product of the factors. -/
theorem mixedCoefficient_smul_family (c : Fin n → ℂ) (H : Fin n → Matrix (Fin n) (Fin n) ℂ) :
    mixedCoefficient (fun i => c i • H i) = (∏ i, c i) * mixedCoefficient H := by
  unfold mixedCoefficient
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h := det_mul_column (fun j => c (σ j)) (of fun j k => H (σ j) j k)
  rw [Equiv.prod_comp σ c] at h
  convert h using 2
  · congr 1
  · rfl

/-- **The pointwise comparison** (bou02 4.12 (a)–(c) with the alternative): for `A, B ≻ 0`,
`C ⪰ 0`, `C ≤ 2B`, `det A = c det B`, `p ≤ n`, `t > 0`,
`C(B[p], C[n-p]) ≤ (t/c) C(A[p], C[n-p]) + (2^{n-p} n!/t) C(A[n-p], B[p])` (real parts). -/
theorem re_mixedCoefficient_le_of_mongeAmpere {A B C : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef)
    (hB : B.PosDef) (hC : C.PosSemidef) (hCB : ((2 : ℂ) • B - C).PosSemidef) {c : ℝ} (hc : 0 < c)
    (hdet : A.det.re = c * B.det.re) {p : ℕ} (hp : p ≤ n) {t : ℝ} (ht : 0 < t) :
    (mixedCoefficient (fun i : Fin n => if (i : ℕ) < p then B else C)).re ≤
      t / c * (mixedCoefficient (fun i : Fin n => if (i : ℕ) < p then A else C)).re +
        2 ^ (n - p) * n.factorial / t *
          (mixedCoefficient (fun i : Fin n => if (i : ℕ) < n - p then A else B)).re := by
  classical
  have hBdet := re_det_pos_of_posDef hB
  have hY0 : 0 ≤ (mixedCoefficient (fun i : Fin n => if (i : ℕ) < p then A else C)).re :=
    Pending.MixedMongeAmpere.mixedCoefficient_re_nonneg _ fun i => by
      split_ifs; exacts [hA.posSemidef, hC]
  have hZ0 : 0 ≤ (mixedCoefficient (fun i : Fin n => if (i : ℕ) < n - p then A else B)).re :=
    Pending.MixedMongeAmpere.mixedCoefficient_re_nonneg _ fun i => by
      split_ifs; exacts [hA.posSemidef, hB.posSemidef]
  have hX0 : 0 ≤ (mixedCoefficient (fun i : Fin n => if (i : ℕ) < p then B else C)).re :=
    Pending.MixedMongeAmpere.mixedCoefficient_re_nonneg _ fun i => by
      split_ifs; exacts [hB.posSemidef, hC]
  by_cases h : (mixedCoefficient (fun i : Fin n => if (i : ℕ) < n - p then A else B)).re <
      t * B.det.re
  · have hcb := concentration_bound hA hB hC p hp ht h
    rw [hdet] at hcb
    have hct : c * B.det.re / (t * B.det.re) = c / t := by field_simp
    rw [hct] at hcb
    have h1 : (mixedCoefficient (fun i : Fin n => if (i : ℕ) < p then B else C)).re ≤
        t / c * (mixedCoefficient (fun i : Fin n => if (i : ℕ) < p then A else C)).re := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      have := mul_le_mul_of_nonneg_left hcb ht.le
      rw [← mul_assoc, mul_div_cancel₀ _ ht.ne'] at this
      linarith
    have h2 : 0 ≤ 2 ^ (n - p) * n.factorial / t *
        (mixedCoefficient (fun i : Fin n => if (i : ℕ) < n - p then A else B)).re := by
      positivity
    linarith
  · push Not at h
    -- `C ≤ 2B` in the last `n - p` slots
    have hmono : (mixedCoefficient (fun i : Fin n => if (i : ℕ) < p then B else C)).re ≤
        (mixedCoefficient (fun i : Fin n => if (i : ℕ) < p then B else (2 : ℂ) • B)).re := by
      refine SubmanifoldMassConcentration.re_mixedCoefficient_mono (fun i => ?_) fun i => ?_
      · split_ifs; exacts [hB.posSemidef, hC]
      · split_ifs
        · simpa using PosSemidef.zero
        · exact hCB
    have hscale : mixedCoefficient (fun i : Fin n => if (i : ℕ) < p then B else (2 : ℂ) • B) =
        (2 : ℂ) ^ (n - p) * ((n.factorial : ℂ) * B.det) := by
      have hfam : (fun i : Fin n => if (i : ℕ) < p then B else (2 : ℂ) • B) =
          fun i : Fin n => (if (i : ℕ) < p then (1 : ℂ) else 2) • B := by
        funext i; split_ifs <;> simp
      rw [hfam, mixedCoefficient_smul_family, mixedCoefficient_diagonal]
      congr 1
      rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
      congr 1
      have : (Finset.univ.filter fun i : Fin n => ¬ (i : ℕ) < p) =
          (Finset.univ.filter fun i : Fin n => (i : ℕ) < p)ᶜ := by
        ext i; simp
      rw [this, Finset.card_compl, Fintype.card_fin]
      simp only [Fin.card_filter_val_lt]
      omega
    have hre : ((2 : ℂ) ^ (n - p) * ((n.factorial : ℂ) * B.det)).re =
        2 ^ (n - p) * n.factorial * B.det.re := by
      rw [show (2 : ℂ) ^ (n - p) * ((n.factorial : ℂ) * B.det) =
        (((2 : ℝ) ^ (n - p) * n.factorial : ℝ) : ℂ) * B.det by push_cast; ring,
        Complex.re_ofReal_mul]
    rw [hscale, hre] at hmono
    have h2 : 2 ^ (n - p) * (n.factorial : ℝ) * B.det.re ≤ 2 ^ (n - p) * n.factorial / t *
        (mixedCoefficient (fun i : Fin n => if (i : ℕ) < n - p then A else B)).re := by
      rw [div_mul_eq_mul_div, le_div_iff₀ ht]
      have h2n : (0 : ℝ) ≤ 2 ^ (n - p) * n.factorial := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h h2n]
    have h1 : 0 ≤ t / c * (mixedCoefficient (fun i : Fin n => if (i : ℕ) < p then A else C)).re := by
      positivity
    linarith

end Matrix

/-! ### Pointwise, at a chart point -/

section Pointwise

variable {n : ℕ}

open StronglyPositiveForms SubmanifoldMassConcentration

theorem isOneOne_add {a b : RealForm n 2} (ha : IsOneOne a) (hb : IsOneOne b) :
    IsOneOne (a + b) := fun u v => by
  simp only [ContinuousAlternatingMap.add_apply, ha u v, hb u v]

theorem isOneOne_smul {a : RealForm n 2} (ha : IsOneOne a) (r : ℝ) : IsOneOne (r • a) :=
  fun u v => by simp only [ContinuousAlternatingMap.smul_apply, ha u v]

/-- A strictly positive real `(1,1)`-form has a positive definite normalized matrix. -/
theorem normalizedHermitianMatrix_posDef {A : RealForm n 2} (hA : IsOneOne A)
    (hpos : IsStrictlyPositive A) : (normalizedHermitianMatrix A).PosDef := by
  classical
  refine posDef_iff_dotProduct_mulVec.mpr ⟨normalizedHermitianMatrix_isHermitian A hA,
    fun x hx => ?_⟩
  rw [dotProduct_normalizedHermitianMatrix hA]
  set y : ComplexModel n := ∑ j, (star (x j)) • coordinateVector j
  have hy : y ≠ 0 := by
    intro h0
    apply hx
    funext i
    have := coord_sum_star_smul_coordinateVector x i
    rw [← show y = ∑ j, (star (x j)) • coordinateVector j from rfl, h0] at this
    simpa using this.symm
  exact Complex.zero_lt_real.mpr (mul_pos Real.pi_pos (hpos y hy))

/-- `actualTopPowerDensity A = (n!/πⁿ) Re det H(A)`. -/
theorem actualTopPowerDensity_eq_det {A : RealForm n 2} (hA : IsOneOne A) :
    actualTopPowerDensity A =
      (n.factorial : ℝ) / Real.pi ^ n * (normalizedHermitianMatrix A).det.re := by
  rw [actualTopPowerDensity_eq_normalizedTopPowerDensity A hA, normalizedTopPowerDensity,
    complexTopCoefficient_eq, Complex.re_ofReal_mul]

/-- The mixed density of a family of `(1,1)`-forms through the normalized matrices. -/
theorem actualMixedTopDensity_eq_re {A : Fin n → RealForm n 2} (hA : ∀ i, IsOneOne (A i)) :
    actualMixedTopDensity A =
      (mixedCoefficient fun i => normalizedHermitianMatrix (A i)).re / Real.pi ^ n := by
  rw [actualMixedTopDensity_eq_normalizedMixedTopDensity A hA, normalizedMixedTopDensity]

end Pointwise

/-! ### The chart densities -/

section Density

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

open StronglyPositiveForms SubmanifoldMassConcentration SmoothMixedMeasureDensity
  PositiveClasses KahlerDomination

/-- **The pointwise comparison of the chart densities**: for `ω_ε ≥ ω/2`, `α` Kähler with
`α^n = c ω_ε^n` in charts, `ω_ε^p∧ω^{n-p} ≤ (t/c) α^p∧ω^{n-p} + (2^{n-p} n!/t) α^{n-p}∧ω_ε^p` as densities. -/
theorem chartDensity_le_of_mongeAmpere (omega : KahlerBackground n M)
    (ωε α : ClosedRealOneOneForm n M)
    (hωε : (ωε - (1 / 2 : ℝ) • omega.form).val.IsSemipositive) (hα : α.val.IsKahler)
    {c : ℝ} (hc : 0 < c)
    (hMA : ∀ (e : ComplexChart n M) z, z ∈ e.val.target →
      actualTopPowerDensity (α.val.coeff e z) = c * actualTopPowerDensity (ωε.val.coeff e z))
    {p : ℕ} (hp : p ≤ n) {t : ℝ} (ht : 0 < t) (e : ComplexChart n M) {z : ComplexModel n}
    (hz : z ∈ e.val.target) :
    chartDensity (fun i : Fin n => if (i : ℕ) < p then ωε else omega.form) e z ≤
      ENNReal.ofReal (t / c) *
          chartDensity (fun i : Fin n => if (i : ℕ) < p then α else omega.form) e z +
        ENNReal.ofReal (2 ^ (n - p) * n.factorial / t) *
          chartDensity (fun i : Fin n => if (i : ℕ) < n - p then α else ωε) e z := by
  classical
  set Aε := ωε.val.coeff e z with hAε
  set Aα := α.val.coeff e z with hAα
  set Aω := omega.form.val.coeff e z with hAω
  have hε1 : IsOneOne Aε := ωε.property.2 e z hz
  have hα1 : IsOneOne Aα := α.property.2 e z hz
  have hω1 : IsOneOne Aω := omega.form.property.2 e z hz
  have hdiff : ∀ y : ComplexModel n,
      0 ≤ Aε ![y, Complex.I • y] - 1 / 2 * Aω ![y, Complex.I • y] := by
    intro y
    have h := hωε e z hz y
    simpa [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_neg,
      ClosedRealOneOneForm.coeff_smul] using h
  have hωpos : IsStrictlyPositive Aω := (omega.isKahler.1 e z hz).2
  have hεpos : IsStrictlyPositive Aε := fun y hy => by
    have := hdiff y; have := hωpos y hy; linarith
  have hαpos : IsStrictlyPositive Aα := (hα.1 e z hz).2
  have hωsemi : ∀ v : ComplexModel n, 0 ≤ Aω ![v, Complex.I • v] :=
    lineValue_nonneg_of_isHermitian omega.isKahler.1 e hz
  set HA := normalizedHermitianMatrix Aα
  set HB := normalizedHermitianMatrix Aε
  set HC := normalizedHermitianMatrix Aω
  have hHA : HA.PosDef := normalizedHermitianMatrix_posDef hα1 hαpos
  have hHB : HB.PosDef := normalizedHermitianMatrix_posDef hε1 hεpos
  have hHC : HC.PosSemidef :=
    TopDegreeDensity.normalizedHermitianMatrix_posSemidef ⟨hω1, hωsemi⟩
  have hCB : ((2 : ℂ) • HB - HC).PosSemidef := by
    have hsemi : IsSemipositiveOneOne ((2 : ℝ) • Aε + (-1 : ℝ) • Aω) := by
      refine ⟨isOneOne_add (isOneOne_smul hε1 2) (isOneOne_smul hω1 (-1)), fun v => ?_⟩
      have := hdiff v
      simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
        smul_eq_mul]
      linarith
    have h := TopDegreeDensity.normalizedHermitianMatrix_posSemidef hsemi
    rw [normalizedHermitianMatrix_add, normalizedHermitianMatrix_smul,
      normalizedHermitianMatrix_smul] at h
    convert h using 1
    rw [← Complex.coe_smul, ← Complex.coe_smul, sub_eq_add_neg]
    simp
    rfl
  have hdet : HA.det.re = c * HB.det.re := by
    have h := hMA e z hz
    rw [actualTopPowerDensity_eq_det hα1, actualTopPowerDensity_eq_det hε1] at h
    have hk : (0 : ℝ) < (n.factorial : ℝ) / Real.pi ^ n := by positivity
    have : (n.factorial : ℝ) / Real.pi ^ n * (HA.det.re - c * HB.det.re) = 0 := by
      rw [mul_sub]; linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hk.ne'
    · linarith
  have hP := re_mixedCoefficient_le_of_mongeAmpere hHA hHB hHC hCB hc hdet hp ht
  -- the three densities
  have hslot : ∀ (X Y : ClosedRealOneOneForm n M) (q : ℕ), (∀ e z, z ∈ e.val.target →
      IsOneOne (X.val.coeff e z)) → (∀ e z, z ∈ e.val.target → IsOneOne (Y.val.coeff e z)) →
      chartDensity (fun i : Fin n => if (i : ℕ) < q then X else Y) e z =
        ENNReal.ofReal ((mixedCoefficient fun i : Fin n => if (i : ℕ) < q then
          normalizedHermitianMatrix (X.val.coeff e z) else
            normalizedHermitianMatrix (Y.val.coeff e z)).re / Real.pi ^ n) := by
    intro X Y q hX hY
    rw [chartDensity, actualMixedTopDensity_eq_re fun i => by
      split_ifs; exacts [hX e z hz, hY e z hz]]
    congr 3
    congr 1
    funext i
    split_ifs <;> rfl
  have h1 : ∀ e z, z ∈ e.val.target → IsOneOne (ωε.val.coeff e z) := fun e z hz => ωε.property.2 e z hz
  have h2 : ∀ e z, z ∈ e.val.target → IsOneOne (α.val.coeff e z) := fun e z hz => α.property.2 e z hz
  have h3 : ∀ e z, z ∈ e.val.target → IsOneOne (omega.form.val.coeff e z) :=
    fun e z hz => omega.form.property.2 e z hz
  rw [hslot ωε omega.form p h1 h3, hslot α omega.form p h2 h3, hslot α ωε (n - p) h2 h1]
  have hpi : 0 < Real.pi ^ n := by positivity
  set X := (mixedCoefficient fun i : Fin n => if (i : ℕ) < p then HB else HC).re
  set Y := (mixedCoefficient fun i : Fin n => if (i : ℕ) < p then HA else HC).re
  set Z := (mixedCoefficient fun i : Fin n => if (i : ℕ) < n - p then HA else HB).re
  have hY0 : 0 ≤ Y := Pending.MixedMongeAmpere.mixedCoefficient_re_nonneg _ fun i => by
    split_ifs; exacts [hHA.posSemidef, hHC]
  have hZ0 : 0 ≤ Z := Pending.MixedMongeAmpere.mixedCoefficient_re_nonneg _ fun i => by
    split_ifs; exacts [hHA.posSemidef, hHB.posSemidef]
  have hcoef1 : 0 ≤ t / c := by positivity
  have hcoef2 : (0 : ℝ) ≤ 2 ^ (n - p) * n.factorial / t := by positivity
  rw [← ENNReal.ofReal_mul hcoef1, ← ENNReal.ofReal_mul hcoef2,
    ← ENNReal.ofReal_add (mul_nonneg hcoef1 (div_nonneg hY0 hpi.le))
      (mul_nonneg hcoef2 (div_nonneg hZ0 hpi.le))]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_iff₀ hpi]
  have : (t / c * (Y / Real.pi ^ n) + 2 ^ (n - p) * n.factorial / t * (Z / Real.pi ^ n)) *
      Real.pi ^ n = t / c * Y + 2 ^ (n - p) * n.factorial / t * Z := by
    field_simp
  rw [this]
  exact hP

end Density

/-! ### From charts to the manifold -/

section Global

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M]

open SmoothMixedMeasureDensity

omit [IsComplexManifold n M] in
/-- **Measures on a compact manifold are compared chart by chart**: if `μ ≤ ν` on the images
`e⁻¹(K)` of measurable subsets of chart targets, then `μ ≤ ν`. -/
theorem measure_le_of_forall_chart [CompactSpace M] {μ ν : Measure M}
    (h : ∀ (e : ComplexChart n M) (K : Set (ComplexModel n)), MeasurableSet K →
      K ⊆ e.val.target → μ (e.val.symm '' K) ≤ ν (e.val.symm '' K)) : μ ≤ ν := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M => (complexChartAt (n := n) x).val.source)
    (fun x => (complexChartAt (n := n) x).val.open_source)
    (fun x _ => mem_iUnion.mpr ⟨x, mem_complexChartAt_source x⟩)
  set m := t.card
  set pts : Fin m → M := fun j => (t.equivFin.symm j : M)
  set f : ℕ → Set M := fun j =>
    if hj : j < m then (complexChartAt (n := n) (pts ⟨j, hj⟩)).val.source else ∅ with hfdef
  have hfm : ∀ j, MeasurableSet (f j) := fun j => by
    simp only [hfdef]; split_ifs
    · exact (complexChartAt (n := n) _).val.open_source.measurableSet
    · exact MeasurableSet.empty
  have hcov : (⋃ j, f j) = univ := by
    refine eq_univ_iff_forall.mpr fun y => ?_
    obtain ⟨x, hxt, hy⟩ := mem_iUnion₂.mp (ht (mem_univ y))
    set j := t.equivFin ⟨x, hxt⟩
    refine mem_iUnion.mpr ⟨j, ?_⟩
    have : pts ⟨(j : ℕ), j.isLt⟩ = x := by
      simp only [pts, Fin.eta, j, Equiv.symm_apply_apply]
    simp only [hfdef]
    rw [dif_pos j.isLt, this]
    exact hy
  set D := disjointed f
  have hDm : ∀ j, MeasurableSet (D j) := MeasurableSet.disjointed hfm
  have hDdisj : Pairwise (Function.onFun Disjoint D) := disjoint_disjointed f
  have hDcov : (⋃ j, D j) = univ := by rw [iUnion_disjointed, hcov]
  refine Measure.le_iff.mpr fun A hA => ?_
  have hsplit : ∀ ρ : Measure M, ρ A = ∑' j, ρ (A ∩ D j) := by
    intro ρ
    have hA' : A = ⋃ j, A ∩ D j := by rw [← inter_iUnion, hDcov, inter_univ]
    conv_lhs => rw [hA']
    exact measure_iUnion (fun i j hij => (hDdisj hij).mono inter_subset_right inter_subset_right)
      fun j => hA.inter (hDm j)
  rw [hsplit μ, hsplit ν]
  refine ENNReal.tsum_le_tsum fun j => ?_
  by_cases hj : j < m
  · set e := complexChartAt (n := n) (pts ⟨j, hj⟩)
    have hsub : A ∩ D j ⊆ e.val.source := fun y hy => by
      have := disjointed_subset f j hy.2
      simpa [hfdef, hj] using this
    set K := e.val '' (A ∩ D j)
    have hK : K = e.val.target ∩ e.val.symm ⁻¹' (A ∩ D j) :=
      e.val.image_eq_target_inter_inv_preimage hsub
    have hKm : MeasurableSet K := by
      rw [hK]
      exact measurableSet_inter_preimage_of_continuousOn e.val.open_target.measurableSet
        e.val.continuousOn_symm (hA.inter (hDm j))
    have hKt : K ⊆ e.val.target := by rw [hK]; exact inter_subset_left
    have hback : e.val.symm '' K = A ∩ D j := e.val.symm_image_image_of_subset_source hsub
    rw [← hback]
    exact h e K hKm hKt
  · have : D j = ∅ := by
      have := disjointed_subset f j
      simp only [hfdef, hj, dif_neg, not_false_eq_true] at this
      exact subset_empty_iff.mp this
    simp [this]

end Global

/-! ### The integrated comparison -/

section Main

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

open SmoothMixedMeasureDensity GlobalNonPluripolar PositiveClasses

/-- **The integration step of Boucksom's 4.12 (dp04 2.6)**: if `ω_ε ≥ ω/2` and `α` is a Kähler form
with `α^n = c ω_ε^n` (`c > 0`), then for every `p ≤ n`, `t > 0` and every set `S`,
`ω_ε^p∧ω^{n-p}(S) ≤ (t/c) α^p∧ω^{n-p}(S) + (2^{n-p} n!/t) α^{n-p}∧ω_ε^p(S)` (global mixed measures with
potentials `0`).  Pointwise this is `ConcentrationEigenvalueBound.concentration_bound` on the set where
`α^{n-p}∧ω_ε^p < t ω_ε^n`, and `ω ≤ 2ω_ε` with Markov's inequality on its complement. -/
theorem mixedMeasure_le_of_mongeAmpere (omega : KahlerBackground n M)
    (ωε α : ClosedRealOneOneForm n M)
    (hωε : (ωε - (1 / 2 : ℝ) • omega.form).val.IsSemipositive) (hα : α.val.IsKahler)
    {c : ℝ} (hc : 0 < c)
    (hMA : ∀ (e : ComplexChart n M) z, z ∈ e.val.target →
      actualTopPowerDensity (α.val.coeff e z) = c * actualTopPowerDensity (ωε.val.coeff e z))
    {p : ℕ} (hp : p ≤ n) {t : ℝ} (ht : 0 < t)
    (h₁ : ∀ i, ThetaPlurisubharmonic
      ((fun i : Fin n => if (i : ℕ) < p then ωε else omega.form) i).val (fun _ => 0))
    (h₂ : ∀ i, ThetaPlurisubharmonic
      ((fun i : Fin n => if (i : ℕ) < p then α else omega.form) i).val (fun _ => 0))
    (h₃ : ∀ i, ThetaPlurisubharmonic
      ((fun i : Fin n => if (i : ℕ) < n - p then α else ωε) i).val (fun _ => 0))
    (S : Set M) :
    globalMixedMeasure (fun i : Fin n => if (i : ℕ) < p then ωε else omega.form)
        (fun _ _ => 0) h₁ S ≤
      ENNReal.ofReal (t / c) * globalMixedMeasure
          (fun i : Fin n => if (i : ℕ) < p then α else omega.form) (fun _ _ => 0) h₂ S +
        ENNReal.ofReal (2 ^ (n - p) * n.factorial / t) * globalMixedMeasure
          (fun i : Fin n => if (i : ℕ) < n - p then α else ωε) (fun _ _ => 0) h₃ S := by
  set θε := fun i : Fin n => if (i : ℕ) < p then ωε else omega.form
  set θα := fun i : Fin n => if (i : ℕ) < p then α else omega.form
  set θκ := fun i : Fin n => if (i : ℕ) < n - p then α else ωε
  have hle : globalMixedMeasure θε (fun _ _ => 0) h₁ ≤
      ENNReal.ofReal (t / c) • globalMixedMeasure θα (fun _ _ => 0) h₂ +
        ENNReal.ofReal (2 ^ (n - p) * n.factorial / t) •
          globalMixedMeasure θκ (fun _ _ => 0) h₃ := by
    refine measure_le_of_forall_chart (n := n) fun e K hK hKt => ?_
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
      globalMixedMeasure_image_eq_lintegral h₁ e hK hKt,
      globalMixedMeasure_image_eq_lintegral h₂ e hK hKt,
      globalMixedMeasure_image_eq_lintegral h₃ e hK hKt]
    have hae : ∀ θ : Fin n → ClosedRealOneOneForm n M,
        AEMeasurable (chartDensity θ e) (volume.restrict K) := fun θ =>
      ((continuousOn_chartDensity θ e).mono hKt).aemeasurable hK
    calc ∫⁻ z in K, chartDensity θε e z
        ≤ ∫⁻ z in K, (ENNReal.ofReal (t / c) * chartDensity θα e z +
            ENNReal.ofReal (2 ^ (n - p) * n.factorial / t) * chartDensity θκ e z) :=
          setLIntegral_mono' hK fun z hz =>
            chartDensity_le_of_mongeAmpere omega ωε α hωε hα hc hMA hp ht e (hKt hz)
      _ = ENNReal.ofReal (t / c) * (∫⁻ z in K, chartDensity θα e z) +
            ENNReal.ofReal (2 ^ (n - p) * n.factorial / t) * (∫⁻ z in K, chartDensity θκ e z) := by
          rw [lintegral_add_left' ((hae θα).const_mul _), lintegral_const_mul'' _ (hae θα),
            lintegral_const_mul'' _ (hae θκ)]
  have := Measure.le_iff'.mp hle S
  simpa only [Measure.add_apply, Measure.smul_apply, smul_eq_mul] using this

/-- **Boucksom's 4.12 lower bound** (the form used for `bou:concentrated-current`): if moreover
`δ ≤ ω_ε^p∧ω^{n-p}(S)` and `α^{n-p}∧ω_ε^p(S) ≤ M₀`, then
`c δ² / (4 · 2^{n-p} n! M₀) ≤ α^p∧ω^{n-p}(S)` (the choice `t = 2 · 2^{n-p} n! M₀ / δ`). -/
theorem le_mixedMeasure_of_mongeAmpere (omega : KahlerBackground n M)
    (ωε α : ClosedRealOneOneForm n M)
    (hωε : (ωε - (1 / 2 : ℝ) • omega.form).val.IsSemipositive) (hα : α.val.IsKahler)
    {c : ℝ} (hc : 0 < c)
    (hMA : ∀ (e : ComplexChart n M) z, z ∈ e.val.target →
      actualTopPowerDensity (α.val.coeff e z) = c * actualTopPowerDensity (ωε.val.coeff e z))
    {p : ℕ} (hp : p ≤ n)
    (h₁ : ∀ i, ThetaPlurisubharmonic
      ((fun i : Fin n => if (i : ℕ) < p then ωε else omega.form) i).val (fun _ => 0))
    (h₂ : ∀ i, ThetaPlurisubharmonic
      ((fun i : Fin n => if (i : ℕ) < p then α else omega.form) i).val (fun _ => 0))
    (h₃ : ∀ i, ThetaPlurisubharmonic
      ((fun i : Fin n => if (i : ℕ) < n - p then α else ωε) i).val (fun _ => 0))
    {S : Set M} {δ M₀ : ℝ} (hδ : 0 < δ) (hM₀ : 0 < M₀)
    (hlow : ENNReal.ofReal δ ≤ globalMixedMeasure
      (fun i : Fin n => if (i : ℕ) < p then ωε else omega.form) (fun _ _ => 0) h₁ S)
    (hup : globalMixedMeasure (fun i : Fin n => if (i : ℕ) < n - p then α else ωε)
      (fun _ _ => 0) h₃ S ≤ ENNReal.ofReal M₀) :
    ENNReal.ofReal (c * δ ^ 2 / (4 * 2 ^ (n - p) * n.factorial * M₀)) ≤
      globalMixedMeasure (fun i : Fin n => if (i : ℕ) < p then α else omega.form)
        (fun _ _ => 0) h₂ S := by
  set K := (2 : ℝ) ^ (n - p) * n.factorial with hKdef
  have hK : 0 < K := by positivity
  set t := 2 * K * M₀ / δ with htdef
  have ht : 0 < t := by positivity
  have hmain := mixedMeasure_le_of_mongeAmpere omega ωε α hωε hα hc hMA hp ht h₁ h₂ h₃ S
  set X := globalMixedMeasure (fun i : Fin n => if (i : ℕ) < p then α else omega.form)
    (fun _ _ => 0) h₂ S
  by_cases hX : X = ⊤
  · rw [hX]; exact le_top
  have hXr : X = ENNReal.ofReal X.toReal := (ENNReal.ofReal_toReal hX).symm
  have hcoef : 2 ^ (n - p) * (n.factorial : ℝ) / t * M₀ = δ / 2 := by
    rw [htdef, ← hKdef]; field_simp
  have h1 : ENNReal.ofReal (2 ^ (n - p) * n.factorial / t) *
      globalMixedMeasure (fun i : Fin n => if (i : ℕ) < n - p then α else ωε) (fun _ _ => 0) h₃ S ≤
        ENNReal.ofReal (δ / 2) := by
    calc _ ≤ ENNReal.ofReal (2 ^ (n - p) * n.factorial / t) * ENNReal.ofReal M₀ :=
          mul_le_mul_right hup _
      _ = ENNReal.ofReal (δ / 2) := by
          rw [← ENNReal.ofReal_mul (by positivity), hcoef]
  have h2 : ENNReal.ofReal δ ≤ ENNReal.ofReal (t / c * X.toReal + δ / 2) := by
    calc ENNReal.ofReal δ ≤ _ := hlow.trans hmain
      _ ≤ ENNReal.ofReal (t / c) * X + ENNReal.ofReal (δ / 2) := add_le_add_right h1 _
      _ = ENNReal.ofReal (t / c * X.toReal + δ / 2) := by
          rw [hXr, ← ENNReal.ofReal_mul (by positivity), ENNReal.toReal_ofReal ENNReal.toReal_nonneg,
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have h3 : δ ≤ t / c * X.toReal + δ / 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2
  rw [hXr]
  refine ENNReal.ofReal_le_ofReal ?_
  have h4 : δ / 2 ≤ t / c * X.toReal := by linarith
  have h5 : c * δ ^ 2 / (4 * K * M₀) = c / t * (δ / 2) := by
    rw [htdef]; field_simp; ring
  rw [show 4 * 2 ^ (n - p) * (n.factorial : ℝ) * M₀ = 4 * K * M₀ by rw [hKdef]; ring, h5]
  have : c / t * (δ / 2) ≤ c / t * (t / c * X.toReal) :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  calc c / t * (δ / 2) ≤ c / t * (t / c * X.toReal) := this
    _ = X.toReal := by field_simp

end Main

end

end SGPT.Foundations.Analysis.Pending.ConcentrationMassComparison
