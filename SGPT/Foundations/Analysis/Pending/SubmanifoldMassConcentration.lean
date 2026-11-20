import SGPT.Foundations.Analysis.Pending.SubmanifoldConcentrationPotential
import SGPT.Foundations.Analysis.Pending.ConcentrationEigenvalueBound
import SGPT.Foundations.Analysis.Pending.TopDegreeDensity
import SGPT.Foundations.Analysis.Pending.SmoothMixedMeasureDensity
import SGPT.Foundations.Analysis.Pending.CoordinateDensityMixedPullback
import SGPT.Foundations.Analysis.Pending.LeviFormHolomorphicComp
import SGPT.Foundations.Analysis.Pending.ProductComplexManifold

set_option autoImplicit false

/-!
# Demailly--Păun's concentration of mass along a closed submanifold, and on the diagonal

Source: Demailly--Păun, Lemma 2.1 (iii)/(iv) (`dp04-kahler-cone:2.1`,
`references/dp04-kahler-cone/source/0105176.tex:588-800`), quoted by Boucksom as the concentration
of mass (`bou02-volume:4.11`); used on the diagonal of `X × X` in dp04 2.12 and in Boucksom's proof
of 4.8.  Step B3 (part 2) of the TN.4 plan for Boucksom 4.8;
the statement of `exists_massConcentration` is the target posted the statement under discussion C-0004.

## Main results

* `exists_massConcentration` — for a closed complex submanifold `Y` of a compact complex manifold
  `M` with a Kähler form `ω` and a point `x ∈ Y` regular of dimension `k`: chart-smooth `f_ε`,
  open tubes `V_ε` (increasing in `ε`, `⋂_{ε ≤ 1} closure V_ε ⊆ Y`), `ω_ε = ω + ddᶜ f_ε ≥ ω/2`, and
  for every neighbourhood `U` of `x` a `δ > 0` with
  `δ ≤ μ_ε(U ∩ V_ε)` for all `ε ∈ (0,1]`, `μ_ε` the global mixed measure (potentials `0`) of
  `n - k` copies of `ω_ε` and `k` copies of `ω` (`concentrationSlot`).
* `exists_diagonal_massConcentration` — the same for the diagonal of `X × X` with
  `p₁^*ω + p₂^*ω` (`ProductComplexManifold`), the first `n` slots carrying `ω_ε`.

## Proof

`f_ε`, `V_ε` and `ω_ε ≥ ω/2` are `Pending.SubmanifoldConcentrationPotential` (dp04 2.1 (ii)), with
a partition adapted to `x` (`exists_adapted`): near `x`, `f_ε = log(|ζ''|² + ε²)/(2A)` in the
flattening coordinates `ζ = Φ(z)` of `Y` at `x`.  The mass bound (`exists_mass_lower_bound`) is
dp04's "Fubini--Study volume rescaled by `ε`", made literal: with `T_ε(ξ', ξ'') = (ξ', εξ'')`
(`scaleNormal`) and `F_ε = Φ⁻¹ ∘ T_ε` on a fixed ball `B`,

* the change of variables (`lintegral_image_eq_lintegral_abs_det_fderiv_mul`) and TN23's chart
  density (`SmoothMixedMeasureDensity.globalMixedMeasure_image_eq_lintegral`) give
  `μ_ε(F_ε(B)) = ∫_B |det dF_ε| · density`, and `|det dF_ε| · density` is the mixed density of the
  pulled-back forms (`actualMixedTopDensity_compContinuousLinearMap`; `det_ℝ ≥ 0` for ℂ-linear maps);
* in the variable `ξ`, `f_ε ∘ F_ε = (log ε² + log(|ξ''|² + 1))/(2A)`: the pulled-back `ddᶜ f_ε` does not
  depend on `ε` and is `≥ |v''|²/(8A)` on `B` (`le_leviForm_log_normalSq`, from
  `ConcentrationPotentialLevi.le_leviForm_log_sum`); the pulled-back `ω` is `≥ (π m / C²)|v'|²`;
* the mixed coefficient is monotone in the Loewner order (`re_mixedCoefficient_mono`) and its
  value on the model family is `≥ a^p b^k` (`pow_mul_pow_le_re_mixedCoefficient_modelSlot`,
  one bijection sending the `p` normal slots to the normal directions), so the density is
  `≥ c > 0` on `B` uniformly in `ε`, and `δ = c · vol(B)`.

The source's eigenvalue argument with the forms `γ_{j,k}` is not needed, because the partition is
adapted to `x`; this is the only difference from dp04 2.1 and it is stated in the theorem: the
family depends on `x` (dp04's single family serving all points of `Y` is not claimed).  The
consumer (blueprint `bou:uniform-diagonal-domination`) fixes `x` and `U` before using the family.
No consumer in Lean yet.
-/

open Set Filter MeasureTheory Matrix
open scoped Topology Manifold ContDiff ComplexOrder ENNReal

namespace SGPT.Foundations.Analysis.Pending.SubmanifoldMassConcentration

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

noncomputable section

/-! ### Linear algebra: monotonicity and a model value of the mixed coefficient -/

section LinearAlgebra

variable {n : ℕ}

open Pending.MixedMongeAmpere in
/-- **Monotonicity of the mixed coefficient** in the Loewner order, for positive semidefinite
slots. -/
theorem re_mixedCoefficient_mono {G H : Fin n → Matrix (Fin n) (Fin n) ℂ}
    (hG : ∀ i, (G i).PosSemidef) (hHG : ∀ i, (H i - G i).PosSemidef) :
    (mixedCoefficient G).re ≤ (mixedCoefficient H).re := by
  classical
  have hH : ∀ i, (H i).PosSemidef := fun i => by
    have := (hG i).add (hHG i)
    rwa [add_sub_cancel] at this
  -- hybrid families: `G` on `s`, `H` off `s`
  have key : ∀ s : Finset (Fin n),
      (mixedCoefficient fun i => if i ∈ s then G i else H i).re ≤ (mixedCoefficient H).re := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert j s hj ih =>
      refine le_trans ?_ ih
      set K : Fin n → Matrix (Fin n) (Fin n) ℂ := fun i => if i ∈ s then G i else H i with hK
      have hKpsd : ∀ i, (K i).PosSemidef := fun i => by
        by_cases hi : i ∈ s <;> simp [hK, hi, hG i, hH i]
      have hKj : K j = H j := by simp [hK, hj]
      have hins : (fun i => if i ∈ insert j s then G i else H i) = Function.update K j (G j) := by
        funext i
        by_cases hij : i = j
        · subst hij; simp
        · simp [hK, Finset.mem_insert, hij]
      have hsplit : K = Function.update K j (G j + (H j - G j)) := by
        rw [add_sub_cancel, ← hKj, Function.update_eq_self]
      have hadd := MongeAmpere.mixedCoefficient_update_add K j (G j) (H j - G j)
      rw [← hsplit] at hadd
      rw [hins, hadd, Complex.add_re]
      have h0 : 0 ≤ (mixedCoefficient (Function.update K j (H j - G j))).re := by
        refine mixedCoefficient_re_nonneg _ fun i => ?_
        by_cases hij : i = j
        · subst hij; simpa using hHG i
        · rw [Function.update_of_ne hij]; exact hKpsd i
      linarith
  have := key Finset.univ
  simpa using this

/-- The model family: `p` slots `a · diag(1_{j ≥ k})` (normal directions) and `n - p` slots
`b · diag(1_{j < k})` (tangential directions), `p = n - k`. -/
def modelSlot (k p : ℕ) (a b : ℝ) (i : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  if (i : ℕ) < p then diagonal (fun j => if k ≤ (j : ℕ) then (a : ℂ) else 0)
  else diagonal (fun j => if (j : ℕ) < k then (b : ℂ) else 0)

theorem modelSlot_posSemidef (k p : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (i : Fin n) :
    (modelSlot (n := n) k p a b i).PosSemidef := by
  unfold modelSlot
  split_ifs
  · refine PosSemidef.diagonal fun j => ?_
    simp only [Pi.zero_apply]
    split_ifs
    · exact_mod_cast ha
    · exact le_rfl
  · refine PosSemidef.diagonal fun j => ?_
    simp only [Pi.zero_apply]
    split_ifs
    · exact_mod_cast hb
    · exact le_rfl

open ConcentrationEigenvalueBound in
/-- **The model value**: with `p + k = n`, the mixed coefficient of the model family is at least
`a^p b^k` (one bijection sends the `p` normal slots to the normal directions). -/
theorem pow_mul_pow_le_re_mixedCoefficient_modelSlot {k p : ℕ} (hkp : k + p = n) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ p * b ^ k ≤ (mixedCoefficient (modelSlot (n := n) k p a b)).re := by
  classical
  set Q : Finset (Fin n) := Finset.univ.filter fun i => (i : ℕ) < p
  set T : Finset (Fin n) := (Finset.univ.filter fun j => (j : ℕ) < k)ᶜ
  have hQc : Q.card = p := by
    simp only [Q, Fin.card_filter_val_lt]; omega
  have hTc : T.card = p := by
    rw [Finset.card_compl]
    simp only [Fin.card_filter_val_lt, Fintype.card_fin]; omega
  obtain ⟨σ, hσ⟩ := exists_perm_mapsTo Q T (hQc.trans hTc.symm)
  have hσc : ∀ i, i ∉ Q → σ i ∉ T := by
    intro i hi hiT
    have hinj : Set.InjOn σ (insert i Q : Finset (Fin n)) := σ.injective.injOn
    have hmaps : ∀ j ∈ insert i Q, σ j ∈ T := by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hiT
      · exact hσ j hj
    have hle := Finset.card_le_card_of_injOn σ hmaps hinj
    rw [Finset.card_insert_of_notMem hi, hQc, hTc] at hle
    omega
  set ν : Fin n → Fin n → ℝ := fun i j =>
    if (i : ℕ) < p then (if k ≤ (j : ℕ) then a else 0)
    else (if (j : ℕ) < k then b else 0) with hν
  have hslot : modelSlot (n := n) k p a b = fun i => diagonal (fun j => ((ν i j : ℝ) : ℂ)) := by
    funext i
    by_cases hi : (i : ℕ) < p
    · simp only [modelSlot, hi, if_true, hν]
      congr 1; funext j; split_ifs <;> simp
    · simp only [modelSlot, hi, if_false, hν]
      congr 1; funext j; split_ifs <;> simp
  have hνnn : ∀ i j, 0 ≤ ν i j := by
    intro i j; simp only [hν]; split_ifs <;> first | exact ha | exact hb | exact le_rfl
  rw [hslot, mixedCoefficient_diagonal_family, Complex.re_sum]
  have hterm : ∀ r : Fin n → Fin n,
      ((if Function.Bijective r then ∏ i, ((ν i (r i) : ℝ) : ℂ) else 0 : ℂ)).re =
        if Function.Bijective r then ∏ i, ν i (r i) else 0 := by
    intro r
    split_ifs
    · rw [← Complex.ofReal_prod, Complex.ofReal_re]
    · simp
  simp_rw [hterm]
  have hle := Finset.single_le_sum (f := fun r : Fin n → Fin n =>
      if Function.Bijective r then ∏ i, ν i (r i) else 0)
    (fun r _ => by
      split_ifs
      · exact Finset.prod_nonneg fun i _ => hνnn i (r i)
      · exact le_rfl) (Finset.mem_univ (σ : Fin n → Fin n))
  refine le_trans (le_of_eq ?_) hle
  simp only [σ.bijective, if_true]
  have hfactor : ∀ i, ν i (σ i) = if i ∈ Q then a else b := by
    intro i
    by_cases hi : (i : ℕ) < p
    · have hiQ : i ∈ Q := by simp [Q, hi]
      have := hσ i hiQ
      simp only [T, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at this
      simp [hν, hi, hiQ, this]
    · have hiQ : i ∉ Q := by simp [Q, hi]
      have := hσc i hiQ
      simp only [T, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_lt,
        not_le] at this
      simp [hν, hi, hiQ, this]
  simp_rw [hfactor]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have hc1 : (Finset.univ.filter fun i => i ∈ Q).card = p := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter, hQc]
  have hc2 : (Finset.univ.filter fun i => i ∉ Q).card = k := by
    rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter,
      ← Finset.compl_eq_univ_sdiff, Finset.card_compl, hQc, Fintype.card_fin]; omega
  rw [hc1, hc2]

open StronglyPositiveForms in
/-- `x^* H(A) x = π A(y, iy)` with `y = ∑ x̄_j e_j`: the normalized Hermitian matrix of a real
`(1,1)`-form represents its line values. -/
theorem dotProduct_normalizedHermitianMatrix {A : RealForm n 2} (hA : IsOneOne A)
    (x : Fin n → ℂ) :
    star x ⬝ᵥ (normalizedHermitianMatrix A *ᵥ x) =
      ((Real.pi * A ![∑ j, (star (x j)) • coordinateVector j,
        Complex.I • ∑ j, (star (x j)) • coordinateVector j] : ℝ) : ℂ) := by
  classical
  set y : ComplexModel n := ∑ j, (star (x j)) • coordinateVector j
  have hG : hermitianEntry A y y =
      ∑ j, star (x j) * ∑ k, x k * hermitianEntry A (coordinateVector j) (coordinateVector k) := by
    rw [hermitianEntry_sum_left hA]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hermitianEntry_sum_right]
    simp only [Complex.star_def, RCLike.conj_conj]
  have hyy : A ![y, y] = 0 :=
    A.map_eq_zero_of_eq ![y, y] (i := 0) (j := 1) (by simp) (by decide)
  have hGreal : hermitianEntry A y y = ((A ![y, Complex.I • y] : ℝ) : ℂ) := by
    simp [hermitianEntry, hyy]
  have hdot : star x ⬝ᵥ (normalizedHermitianMatrix A *ᵥ x) =
      (Real.pi : ℂ) * hermitianEntry A y y := by
    rw [hG, Finset.mul_sum]
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, normalizedHermitianMatrix_apply',
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hdot, hGreal, ← Complex.ofReal_mul]

theorem coord_sum_star_smul_coordinateVector (x : Fin n → ℂ) (i : Fin n) :
    (∑ j, (star (x j)) • coordinateVector j : ComplexModel n) i = star (x i) := by
  classical
  simp [coordinateVector, Pi.single_apply]

open StronglyPositiveForms in
/-- **A diagonal lower bound for the normalized matrix**: if `∑ d_j |y_j|² ≤ π A(y, iy)` for every
`y`, then `H(A) - diag(d)` is positive semidefinite. -/
theorem posSemidef_normalizedHermitianMatrix_sub_diagonal {A : RealForm n 2} (hA : IsOneOne A)
    (d : Fin n → ℝ)
    (h : ∀ y : ComplexModel n, ∑ j, d j * ‖y j‖ ^ 2 ≤ Real.pi * A ![y, Complex.I • y]) :
    (normalizedHermitianMatrix A - diagonal (fun j => (d j : ℂ))).PosSemidef := by
  classical
  have hherm : (normalizedHermitianMatrix A - diagonal (fun j => (d j : ℂ))).IsHermitian := by
    refine (normalizedHermitianMatrix_isHermitian A hA).sub ?_
    rw [Matrix.IsHermitian, diagonal_conjTranspose]
    congr 1
    funext j
    simp
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun x => ?_
  rw [Matrix.sub_mulVec, dotProduct_sub, dotProduct_normalizedHermitianMatrix hA]
  set y : ComplexModel n := ∑ j, (star (x j)) • coordinateVector j
  have hdiag : star x ⬝ᵥ (diagonal (fun j => (d j : ℂ)) *ᵥ x) =
      ((∑ j, d j * ‖y j‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coord_sum_star_smul_coordinateVector, norm_star, ← Complex.conj_mul', Complex.star_def]
    ring
  rw [hdiag, ← Complex.ofReal_sub]
  exact Complex.zero_le_real.mpr (sub_nonneg.mpr (h y))

open StronglyPositiveForms in
/-- **The mixed density of forms dominating the model family**: if the first `p` forms dominate
`a |y''|²` and the others `b |y'|²` on complex lines (`y' = (y_j)_{j < k}`, `y'' = (y_j)_{j ≥ k}`,
`k + p = n`), the mixed top density is at least `a^p b^k / π^n`. -/
theorem le_actualMixedTopDensity_of_model {A : Fin n → RealForm n 2} (hA : ∀ i, IsOneOne (A i))
    {k p : ℕ} (hkp : k + p = n) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hnor : ∀ i : Fin n, (i : ℕ) < p → ∀ y : ComplexModel n,
      ∑ j : Fin n, (if k ≤ (j : ℕ) then a else 0) * ‖y j‖ ^ 2 ≤
        Real.pi * A i ![y, Complex.I • y])
    (htan : ∀ i : Fin n, ¬ (i : ℕ) < p → ∀ y : ComplexModel n,
      ∑ j : Fin n, (if (j : ℕ) < k then b else 0) * ‖y j‖ ^ 2 ≤
        Real.pi * A i ![y, Complex.I • y]) :
    a ^ p * b ^ k / Real.pi ^ n ≤ actualMixedTopDensity A := by
  rw [actualMixedTopDensity_eq_normalizedMixedTopDensity A hA, normalizedMixedTopDensity]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine (pow_mul_pow_le_re_mixedCoefficient_modelSlot hkp ha hb).trans ?_
  refine re_mixedCoefficient_mono (modelSlot_posSemidef k p ha hb) fun i => ?_
  by_cases hi : (i : ℕ) < p
  · have := posSemidef_normalizedHermitianMatrix_sub_diagonal (hA i)
      (fun j => if k ≤ (j : ℕ) then a else 0) (hnor i hi)
    convert this using 2
    simp only [modelSlot, hi, if_true]
    congr 1; funext j; split_ifs <;> simp
  · have := posSemidef_normalizedHermitianMatrix_sub_diagonal (hA i)
      (fun j => if (j : ℕ) < k then b else 0) (htan i hi)
    convert this using 2
    simp only [modelSlot, hi, if_false]
    congr 1; funext j; split_ifs <;> simp

end LinearAlgebra

/-! ### The normal rescaling `T_ε(ξ', ξ'') = (ξ', ε ξ'')` -/

section Scaling

variable {n : ℕ}

/-- The ℂ-linear rescaling of the coordinates `j ≥ k` by `ε`. -/
def scaleNormalₗ (k : ℕ) (ε : ℂ) : ComplexModel n →ₗ[ℂ] ComplexModel n where
  toFun ξ := WithLp.toLp 2 (fun j => (if k ≤ (j : ℕ) then ε else 1) * ξ j)
  map_add' ξ η := by
    ext j
    simp only [PiLp.add_apply, mul_add]
  map_smul' c ξ := by
    ext j
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- `T_ε` as a continuous ℂ-linear map. -/
def scaleNormal (k : ℕ) (ε : ℂ) : ComplexModel n →L[ℂ] ComplexModel n :=
  LinearMap.toContinuousLinearMap (scaleNormalₗ k ε)

@[simp] theorem scaleNormal_apply (k : ℕ) (ε : ℂ) (ξ : ComplexModel n) (j : Fin n) :
    scaleNormal k ε ξ j = (if k ≤ (j : ℕ) then ε else 1) * ξ j := rfl

theorem norm_sq_scaleNormal (k : ℕ) (ε : ℂ) (ξ : ComplexModel n) :
    ‖scaleNormal k ε ξ‖ ^ 2 = ∑ j : Fin n, ‖(if k ≤ (j : ℕ) then ε else 1)‖ ^ 2 * ‖ξ j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [scaleNormal_apply, norm_mul, mul_pow]

theorem norm_scaleNormal_le (k : ℕ) {ε : ℂ} (hε : ‖ε‖ ≤ 1) (ξ : ComplexModel n) :
    ‖scaleNormal k ε ξ‖ ≤ ‖ξ‖ := by
  have h : ‖scaleNormal k ε ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by
    rw [norm_sq_scaleNormal, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_le_sum fun j _ => ?_
    have hc : ‖(if k ≤ (j : ℕ) then ε else 1)‖ ^ 2 ≤ 1 := by
      split_ifs
      · exact pow_le_one₀ (norm_nonneg _) hε
      · simp
    nlinarith [sq_nonneg ‖ξ j‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

theorem tangential_le_norm_sq_scaleNormal (k : ℕ) (ε : ℂ) (ξ : ComplexModel n) :
    ∑ j : Fin n, (if (j : ℕ) < k then (1 : ℝ) else 0) * ‖ξ j‖ ^ 2 ≤ ‖scaleNormal k ε ξ‖ ^ 2 := by
  rw [norm_sq_scaleNormal]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hj : (j : ℕ) < k
  · simp [hj, not_le.mpr hj]
  · simp only [hj, if_false, zero_mul]
    positivity

theorem scaleNormal_injective (k : ℕ) {ε : ℂ} (hε : ε ≠ 0) :
    Function.Injective (scaleNormal (n := n) k ε) := by
  intro ξ η h
  ext j
  have := congrArg (fun ζ : ComplexModel n => ζ j) h
  simp only [scaleNormal_apply] at this
  split_ifs at this with hj
  · exact mul_left_cancel₀ hε this
  · simpa using this

end Scaling

/-! ### The model potential `log (|ξ''|² + 1)` -/

section Model

variable {n : ℕ}

open ConcentrationPotentialLevi

/-- The normal indicator `1_{j ≥ k}`. -/
def nrm (k : ℕ) (j : Fin n) : ℝ := if k ≤ (j : ℕ) then 1 else 0

theorem nrm_sq (k : ℕ) (j : Fin n) : nrm k j ^ 2 = nrm k j := by
  unfold nrm; split_ifs <;> simp

theorem nrm_nonneg (k : ℕ) (j : Fin n) : 0 ≤ nrm k j := by
  unfold nrm; split_ifs <;> simp

/-- `|ξ''|² = ∑_{j ≥ k} |ξ_j|²`. -/
def normalSq (k : ℕ) (ξ : ComplexModel n) : ℝ := ∑ j, nrm k j * ‖ξ j‖ ^ 2

theorem normalSq_nonneg (k : ℕ) (ξ : ComplexModel n) : 0 ≤ normalSq k ξ :=
  Finset.sum_nonneg fun j _ => mul_nonneg (nrm_nonneg k j) (sq_nonneg _)

theorem normalSq_le_norm_sq (k : ℕ) (ξ : ComplexModel n) : normalSq k ξ ≤ ‖ξ‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_le_sum fun j _ => ?_
  unfold nrm; split_ifs <;> simp

/-- **The Levi form of the model potential**: `ddᶜ log (|ξ''|² + 1) ≥ |v''|² / (|ξ''|² + 1)²`
(the Fubini--Study form of the normal directions, dp04 2.1's "rescaled by `ε`"). -/
theorem le_leviForm_log_normalSq (k : ℕ) (ξ v : ComplexModel n) :
    normalSq k v / (normalSq k ξ + 1) ^ 2 ≤
      leviForm (fun ζ => Real.log (normalSq k ζ + 1)) ξ v := by
  have hc : ∀ j : Fin n, ContDiffAt ℝ 2 (fun _ : ComplexModel n => nrm k j) ξ :=
    fun j => contDiffAt_const
  have hG : ∀ j : Fin n, ∀ᶠ ζ in 𝓝 ξ,
      DifferentiableAt ℂ (fun ζ : ComplexModel n => ζ j) ζ :=
    fun j => Eventually.of_forall fun ζ =>
      (EuclideanSpace.proj (𝕜 := ℂ) j).differentiableAt
  have h := le_leviForm_log_sum (c := fun j _ => nrm k j) (G := fun j ζ => ζ j)
    (s := 1) one_pos hc hG v
  have hfun : (fun ζ : ComplexModel n => Real.log (∑ j, (fun j _ => nrm k j) j ζ ^ 2 *
      Complex.normSq ((fun j (ζ : ComplexModel n) => ζ j) j ζ) + 1)) =
      fun ζ => Real.log (normalSq k ζ + 1) := by
    funext ζ
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [nrm_sq, Complex.normSq_eq_norm_sq]
  rw [hfun] at h
  have hS : ∀ ζ : ComplexModel n, ∑ j, (fun j _ => nrm k j) j ζ ^ 2 *
      Complex.normSq ((fun j (ζ : ComplexModel n) => ζ j) j ζ) + 1 = normalSq k ζ + 1 := by
    intro ζ
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [nrm_sq, Complex.normSq_eq_norm_sq]
  rw [hS ξ] at h
  have hdel : ∀ j : Fin n, delC (fun _ : ComplexModel n => nrm k j) ξ v = 0 := by
    intro j; simp [delC]
  have hgam : ∀ j : Fin n, gammaTerm (fun _ : ComplexModel n => nrm k j)
      (fun ζ : ComplexModel n => ζ j) ξ v = (nrm k j : ℂ) * v j := by
    intro j
    rw [gammaTerm, hdel, mul_zero, add_zero]
    congr 1
    exact congrArg (fun L : ComplexModel n →L[ℂ] ℂ => L v)
      (EuclideanSpace.proj (𝕜 := ℂ) j).fderiv
  simp only [hgam, hdel, leviForm_const, mul_zero, Complex.normSq_zero, sub_zero,
    Finset.sum_const_zero, zero_div, add_zero, one_mul] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq, ← sq, nrm_sq]

end Model

/-! ### Pullbacks of forms by ℂ-linear maps -/

section Pullback

variable {n : ℕ}

open StronglyPositiveForms

/-- The real determinant of a ℂ-linear map is `|det_ℂ|² ≥ 0`. -/
theorem det_restrictScalars_nonneg (L : ComplexModel n →L[ℂ] ComplexModel n) :
    0 ≤ LinearMap.det ((L.restrictScalars ℝ : ComplexModel n →L[ℝ] ComplexModel n) :
      ComplexModel n →ₗ[ℝ] ComplexModel n) := by
  have h : ((L.restrictScalars ℝ : ComplexModel n →L[ℝ] ComplexModel n) :
      ComplexModel n →ₗ[ℝ] ComplexModel n) =
      (L : ComplexModel n →ₗ[ℂ] ComplexModel n).restrictScalars ℝ := rfl
  rw [h, LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  exact Complex.normSq_nonneg _

theorem isOneOne_comp {a : RealForm n 2} (ha : IsOneOne a)
    (L : ComplexModel n →L[ℂ] ComplexModel n) :
    IsOneOne (a.compContinuousLinearMap (L.restrictScalars ℝ)) := by
  intro u v
  have h1 : ⇑(L.restrictScalars ℝ) ∘ ![Complex.I • u, Complex.I • v] =
      ![Complex.I • L u, Complex.I • L v] := by
    funext i; fin_cases i <;> simp
  have h2 : ⇑(L.restrictScalars ℝ) ∘ ![u, v] = ![L u, L v] := by
    funext i; fin_cases i <;> simp
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, h1, h2]
  exact ha _ _

theorem lineValue_comp (a : RealForm n 2) (L : ComplexModel n →L[ℂ] ComplexModel n)
    (y : ComplexModel n) :
    (a.compContinuousLinearMap (L.restrictScalars ℝ)) ![y, Complex.I • y] =
      a ![L y, Complex.I • L y] := by
  have h1 : ⇑(L.restrictScalars ℝ) ∘ ![y, Complex.I • y] = ![L y, Complex.I • L y] := by
    funext i; fin_cases i <;> simp
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, h1]

end Pullback

/-! ### The local data at a point of `Y` -/

section Local

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

open SubmanifoldConcentrationPotential BlowupFlatCoordinates PositiveClasses

/-- **The ball in flat coordinates.**  Around `0 = Φ(x)` there is a ball `B(0, ρ)`, `ρ ≤ 1`, on which
`Ψ = Φ⁻¹` lands in the chart, its points lie in `U`, the weight is `|ζ''|²`, the Kähler form is
`≥ m |·|²`, and `‖u‖ ≤ C ‖dΨ(ζ) u‖`. -/
theorem exists_flat_ball (omega : KahlerBackground n M) {Y : Set M} {ι : Type*} [Fintype ι]
    (P : ConcentrationPartition n Y ι) {x : M} {k : ℕ}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (hPw : ∀ᶠ y in 𝓝 x, P.weight y = ∑ i : Fin n, ‖flatGen Φ k i y‖ ^ 2)
    {U : Set M} (hU : U ∈ 𝓝 x) :
    ∃ ρ m C : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 0 < m ∧ 0 < C ∧
      ∀ ζ ∈ Metric.ball (0 : ComplexModel n) ρ, ζ ∈ Φ.target ∧
        Φ.invFun ζ ∈ (chartAt (ComplexModel n) x).target ∧
        (chartAt (ComplexModel n) x).symm (Φ.invFun ζ) ∈ U ∧
        P.weight ((chartAt (ComplexModel n) x).symm (Φ.invFun ζ)) = normalSq k ζ ∧
        (∀ w : ComplexModel n, m * ‖w‖ ^ 2 ≤
          omega.form.val.coeff (complexChartAt (n := n) x) (Φ.invFun ζ) ![w, Complex.I • w]) ∧
        ∀ u : ComplexModel n, ‖u‖ ≤ C * ‖fderiv ℂ Φ.invFun ζ u‖ := by
  classical
  set e := complexChartAt (n := n) x with he
  have hxe : x ∈ (chartAt (ComplexModel n) x).source := mem_chart_source _ x
  have hz₀ : (chartAt (ComplexModel n) x x) ∈ (chartAt (ComplexModel n) x).target :=
    (chartAt (ComplexModel n) x).map_source hxe
  have hz₀Φ : (chartAt (ComplexModel n) x x) ∈ Φ.source := Φ.center_mem_source
  have h0T : (0 : ComplexModel n) ∈ Φ.target := by rw [← hΦ0]; exact Φ.mapsTo_toFun hz₀Φ
  have hΨ0 : Φ.invFun 0 = (chartAt (ComplexModel n) x x) := by rw [← hΦ0]; exact Φ.left_inv (chartAt (ComplexModel n) x x) hz₀Φ
  have hΨc : ContinuousAt Φ.invFun 0 :=
    (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds h0T)).continuousAt
  have htend : Tendsto Φ.invFun (𝓝 0) (𝓝 (chartAt (ComplexModel n) x x)) := by
    have := hΨc.tendsto; rwa [hΨ0] at this
  -- the Kähler bound near `(chartAt (ComplexModel n) x x)`
  obtain ⟨m, hm, hmz⟩ := exists_eventually_kahler_lower omega e hz₀
  -- `dΦ` is bounded near `(chartAt (ComplexModel n) x x)`
  have hΦsm : ContDiffOn ℂ ∞ Φ.toFun Φ.source :=
    contDiffOn_of_differentiableOn_complex Φ.toFun_holomorphic Φ.isOpen_source
  have hΦd : ContinuousAt (fderiv ℂ Φ.toFun) (chartAt (ComplexModel n) x x) :=
    (hΦsm.continuousOn_fderiv_of_isOpen Φ.isOpen_source (by simp)).continuousAt
      (Φ.isOpen_source.mem_nhds hz₀Φ)
  set C := ‖fderiv ℂ Φ.toFun (chartAt (ComplexModel n) x x)‖ + 1 with hCdef
  have hC : 0 < C := by positivity
  have hCz : ∀ᶠ z in 𝓝 (chartAt (ComplexModel n) x x), ‖fderiv ℂ Φ.toFun z‖ ≤ C :=
    (hΦd.norm.eventually (gt_mem_nhds (show ‖fderiv ℂ Φ.toFun (chartAt (ComplexModel n) x x)‖ < C by simp [hCdef]))).mono
      fun z hz => hz.le
  -- the weight formula and `U`, pulled back to the chart
  have hsymm : Tendsto (chartAt (ComplexModel n) x).symm (𝓝 (chartAt (ComplexModel n) x x)) (𝓝 x) := by
    have := ((chartAt (ComplexModel n) x).continuousAt_symm hz₀).tendsto
    rwa [(chartAt (ComplexModel n) x).left_inv hxe] at this
  have hWz := hsymm.eventually (hPw.and hU)
  have hz : ∀ᶠ z in 𝓝 (chartAt (ComplexModel n) x x),
      (z ∈ (chartAt (ComplexModel n) x).target ∧ z ∈ Φ.source) ∧
      ((∀ w : ComplexModel n, m * ‖w‖ ^ 2 ≤ omega.form.val.coeff e z ![w, Complex.I • w]) ∧
        ‖fderiv ℂ Φ.toFun z‖ ≤ C) ∧
      (P.weight ((chartAt (ComplexModel n) x).symm z) =
          ∑ i : Fin n, ‖flatGen Φ k i ((chartAt (ComplexModel n) x).symm z)‖ ^ 2 ∧
        (chartAt (ComplexModel n) x).symm z ∈ U) := by
    filter_upwards [(chartAt (ComplexModel n) x).open_target.mem_nhds hz₀,
      Φ.isOpen_source.mem_nhds hz₀Φ, hmz, hCz, hWz] with z h1 h2 h3 h4 h5
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩
  have hζ : ∀ᶠ ζ in 𝓝 (0 : ComplexModel n),
      ((Φ.invFun ζ ∈ (chartAt (ComplexModel n) x).target ∧ Φ.invFun ζ ∈ Φ.source) ∧
      ((∀ w : ComplexModel n, m * ‖w‖ ^ 2 ≤
          omega.form.val.coeff e (Φ.invFun ζ) ![w, Complex.I • w]) ∧
        ‖fderiv ℂ Φ.toFun (Φ.invFun ζ)‖ ≤ C) ∧
      (P.weight ((chartAt (ComplexModel n) x).symm (Φ.invFun ζ)) =
          ∑ i : Fin n, ‖flatGen Φ k i ((chartAt (ComplexModel n) x).symm (Φ.invFun ζ))‖ ^ 2 ∧
        (chartAt (ComplexModel n) x).symm (Φ.invFun ζ) ∈ U)) ∧ ζ ∈ Φ.target := by
    filter_upwards [htend.eventually hz, Φ.isOpen_target.mem_nhds h0T] with ζ h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨ρ', hρ', hball⟩ := Metric.eventually_nhds_iff_ball.mp hζ
  refine ⟨min ρ' 1, m, C, lt_min hρ' one_pos, min_le_right _ _, hm, hC, fun ζ hζB => ?_⟩
  have hζB' : ζ ∈ Metric.ball (0 : ComplexModel n) ρ' :=
    Metric.ball_subset_ball (min_le_left _ _) hζB
  obtain ⟨⟨⟨hzt, hzs⟩, ⟨hzm, hzC⟩, ⟨hzw, hzU⟩⟩, hζT⟩ := hball ζ hζB'
  refine ⟨hζT, hzt, hzU, ?_, hzm, fun u => ?_⟩
  · -- the weight is `|ζ''|²`
    rw [hzw, normalSq]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hc : chartAt (ComplexModel n) x ((chartAt (ComplexModel n) x).symm (Φ.invFun ζ)) =
        Φ.invFun ζ := (chartAt (ComplexModel n) x).right_inv hzt
    simp only [flatGen, nrm]
    split_ifs with hik
    · simp only [flatCoord, hc, Φ.right_inv ζ hζT, one_mul]
    · simp
  · -- `dΦ ∘ dΨ = id`
    have hΨd : DifferentiableAt ℂ Φ.invFun ζ :=
      Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hζT)
    have hΦd' : DifferentiableAt ℂ Φ.toFun (Φ.invFun ζ) :=
      Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hzs)
    have hid : fderiv ℂ (fun w => Φ.toFun (Φ.invFun w)) ζ = ContinuousLinearMap.id ℂ _ := by
      have heq : (fun w => Φ.toFun (Φ.invFun w)) =ᶠ[𝓝 ζ] id := by
        filter_upwards [Φ.isOpen_target.mem_nhds hζT] with w hw
        exact Φ.right_inv w hw
      rw [heq.fderiv_eq, fderiv_id]
    have hchain := fderiv_comp ζ hΦd' hΨd
    rw [show (Φ.toFun ∘ Φ.invFun) = fun w => Φ.toFun (Φ.invFun w) from rfl, hid] at hchain
    have hu : u = fderiv ℂ Φ.toFun (Φ.invFun ζ) (fderiv ℂ Φ.invFun ζ u) := by
      have := congrArg (fun L : ComplexModel n →L[ℂ] ComplexModel n => L u) hchain
      simpa using this
    calc ‖u‖ = ‖fderiv ℂ Φ.toFun (Φ.invFun ζ) (fderiv ℂ Φ.invFun ζ u)‖ := by rw [← hu]
      _ ≤ ‖fderiv ℂ Φ.toFun (Φ.invFun ζ)‖ * ‖fderiv ℂ Φ.invFun ζ u‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * ‖fderiv ℂ Φ.invFun ζ u‖ :=
          mul_le_mul_of_nonneg_right hzC (norm_nonneg _)

/-- The slots of dp04 2.1 (iv): `ω_ε = ω + ddᶜ f` in the first `p` slots, `ω` in the others. -/
def concentrationSlot (omega : KahlerBackground n M) (f : M → ℝ) (hf : ChartSmooth (n := n) f)
    (p : ℕ) (i : Fin n) : ClosedRealOneOneForm n M :=
  if (i : ℕ) < p then omega.form + ManifoldTubePositivity.ddcClosedForm f hf else omega.form

theorem contDiff_normalSq (k : ℕ) : ContDiff ℝ ∞ (normalSq (n := n) k) := by
  unfold normalSq
  refine ContDiff.sum fun j _ => contDiff_const.mul ?_
  exact (contDiff_norm_sq ℝ).comp
    ((EuclideanSpace.proj (𝕜 := ℂ) j).restrictScalars ℝ).contDiff

theorem normalSq_scaleNormal (k : ℕ) (ε : ℂ) (ξ : ComplexModel n) :
    normalSq k (scaleNormal k ε ξ) = ‖ε‖ ^ 2 * normalSq k ξ := by
  unfold normalSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [scaleNormal_apply]
  unfold nrm
  split_ifs <;> simp [mul_pow]

end Local

/-! ### The mass lower bound at a point (dp04 2.1 (iii)/(iv)) -/

section Mass

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

open SubmanifoldConcentrationPotential BlowupFlatCoordinates PositiveClasses
  ConcentrationPotentialLevi KahlerDomination ManifoldTubePositivity SmoothMixedMeasureDensity
  StronglyPositiveForms GlobalNonPluripolar

/-- **dp04 2.1 (iii)/(iv) at a point of `Y`.**  In the situation of `exists_flat_ball`, there is
`δ > 0` with `δ ≤ μ_ε(U ∩ V_ε)` for every `ε ∈ (0,1]`, where `μ_ε` is the mixed measure of `p`
copies of `ω_ε = ω + ddᶜ f_ε` and `k` copies of `ω` (`p + k = n`).  Proof by the rescaling
`ξ ↦ Φ⁻¹(ξ', εξ'')`: in the variable `ξ` the potential `f_ε` becomes `(log ε² + log(|ξ''|² + 1))/(2A)`,
independent of `ε` up to a constant, so the pulled-back density is bounded below on a fixed ball. -/
theorem exists_mass_lower_bound (omega : KahlerBackground n M) {Y : Set M} {ι : Type*}
    [Fintype ι] (P : ConcentrationPartition n Y ι) {x : M} {k : ℕ} (hk : k ≤ n)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (hPw : ∀ᶠ y in 𝓝 x, P.weight y = ∑ i : Fin n, ‖flatGen Φ k i y‖ ^ 2)
    {A : ℝ} (hA : 0 < A) {U : Set M} (hU : U ∈ 𝓝 x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ (hf : ChartSmooth (n := n) (P.potential A ε))
        (hpsh : ∀ i, ThetaPlurisubharmonic
          (concentrationSlot omega (P.potential A ε) hf (n - k) i).val (fun _ => 0)),
        ENNReal.ofReal δ ≤ globalMixedMeasure (concentrationSlot omega (P.potential A ε) hf (n - k))
          (fun _ _ => 0) hpsh (U ∩ P.tube ε) := by
  classical
  obtain ⟨ρ, m, C, hρ, hρ1, hm, hC, hball⟩ := exists_flat_ball omega P Φ hΦ0 hPw hU
  set p := n - k with hpdef
  have hkp : k + p = n := by omega
  set a : ℝ := 1 / (8 * A) with ha_def
  set b : ℝ := Real.pi * m / C ^ 2 with hb_def
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  set c : ℝ := a ^ p * b ^ k / Real.pi ^ n with hc_def
  have hcpos : 0 < c := by
    have : 0 < a := by positivity
    have : 0 < b := by positivity
    positivity
  set B : Set (ComplexModel n) := Metric.ball 0 ρ with hBdef
  have hBopen : IsOpen B := Metric.isOpen_ball
  have hvol0 : volume B ≠ 0 := (Metric.measure_ball_pos volume (0 : ComplexModel n) hρ).ne'
  have hvoltop : volume B ≠ ⊤ := measure_ball_lt_top.ne
  refine ⟨c * (volume B).toReal, mul_pos hcpos (ENNReal.toReal_pos hvol0 hvoltop), ?_⟩
  intro ε hε hε1 hf hpsh
  set θ := concentrationSlot omega (P.potential A ε) hf p with hθdef
  set e := complexChartAt (n := n) x with he
  have hεC : ‖(ε : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_of_nonneg hε.le]; exact hε1
  have hεC0 : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  set T : ComplexModel n →L[ℂ] ComplexModel n := scaleNormal k (ε : ℂ) with hTdef
  have hTB : ∀ ξ ∈ B, T ξ ∈ B := fun ξ hξ => by
    simp only [hBdef, Metric.mem_ball, dist_zero_right] at hξ ⊢
    exact (norm_scaleNormal_le k hεC ξ).trans_lt hξ
  set F : ComplexModel n → ComplexModel n := fun ξ => Φ.invFun (T ξ) with hFdef
  set L : ComplexModel n → ComplexModel n →L[ℂ] ComplexModel n :=
    fun ξ => (fderiv ℂ Φ.invFun (T ξ)).comp T with hLdef
  have hT_target : ∀ ξ ∈ B, T ξ ∈ Φ.target := fun ξ hξ => (hball _ (hTB ξ hξ)).1
  have hFd : ∀ ξ ∈ B, HasFDerivAt F (L ξ) ξ := fun ξ hξ =>
    ((Φ.invFun_holomorphic.differentiableAt
      (Φ.isOpen_target.mem_nhds (hT_target ξ hξ))).hasFDerivAt).comp ξ T.hasFDerivAt
  have hFdR : ∀ ξ ∈ B, HasFDerivAt F ((L ξ).restrictScalars ℝ) ξ := fun ξ hξ =>
    (hFd ξ hξ).restrictScalars ℝ
  have hF' : ∀ ξ ∈ B, HasFDerivWithinAt F ((L ξ).restrictScalars ℝ) B ξ := fun ξ hξ =>
    (hFdR ξ hξ).hasFDerivWithinAt
  have hFinj : InjOn F B := by
    intro ξ hξ η hη h
    have h' := congrArg Φ.toFun h
    simp only [hFdef] at h'
    rw [Φ.right_inv _ (hT_target ξ hξ), Φ.right_inv _ (hT_target η hη)] at h'
    exact scaleNormal_injective k hεC0 h'
  have hFcont : ContinuousOn F B := fun ξ hξ => (hFd ξ hξ).continuousAt.continuousWithinAt
  have hFt : ∀ ξ ∈ B, F ξ ∈ e.val.target := fun ξ hξ => (hball _ (hTB ξ hξ)).2.1
  have hFBt : F '' B ⊆ e.val.target := by
    rintro _ ⟨ξ, hξ, rfl⟩; exact hFt ξ hξ
  have hFmeas : MeasurableSet (F '' B) :=
    measurableSet_ball.image_of_continuousOn_injOn hFcont hFinj
  -- the image lies in `U ∩ V_ε`
  have hsub : e.val.symm '' (F '' B) ⊆ U ∩ P.tube ε := by
    rintro _ ⟨_, ⟨ξ, hξ, rfl⟩, rfl⟩
    obtain ⟨-, -, hU', hw, -, -⟩ := hball _ (hTB ξ hξ)
    refine ⟨hU', ?_⟩
    show P.weight _ < ε ^ 2
    have hw' : P.weight (e.val.symm (F ξ)) = normalSq k (T ξ) := hw
    rw [hw', normalSq_scaleNormal, Complex.norm_real, Real.norm_of_nonneg hε.le]
    have hξ1 : normalSq k ξ < 1 := by
      have := normalSq_le_norm_sq k ξ
      have hξn : ‖ξ‖ < ρ := by simpa [hBdef] using hξ
      nlinarith [norm_nonneg ξ]
    have hε2 : 0 < ε ^ 2 := by positivity
    nlinarith
  -- the pointwise lower bound of the pulled-back density
  have hpt : ∀ ξ ∈ B, ENNReal.ofReal c ≤
      ENNReal.ofReal |LinearMap.det (((L ξ).restrictScalars ℝ : ComplexModel n →L[ℝ] ComplexModel n) :
        ComplexModel n →ₗ[ℝ] ComplexModel n)| * chartDensity θ e (F ξ) := by
    intro ξ hξ
    have hζB := hTB ξ hξ
    obtain ⟨-, hzt, -, -, hkah, hdΨ⟩ := hball _ hζB
    have hzt' : F ξ ∈ e.val.target := hzt
    set Acoef : Fin n → RealForm n 2 := fun i => (θ i).val.coeff e (F ξ) with hAcoef
    have hsemi : ∀ i, IsSemipositiveOneOne (Acoef i) := fun i =>
      isSemipositiveOneOne_coeff (hpsh i) hzt'
    have hdet := det_restrictScalars_nonneg (L ξ)
    have hdens := actualMixedTopDensity_compContinuousLinearMap Acoef
      ((L ξ).restrictScalars ℝ)
    rw [chartDensity, ← ENNReal.ofReal_mul (abs_nonneg _), abs_of_nonneg hdet]
    change ENNReal.ofReal c ≤ ENNReal.ofReal (_ * actualMixedTopDensity Acoef)
    rw [← hdens]
    apply ENNReal.ofReal_le_ofReal
    refine le_actualMixedTopDensity_of_model (fun i => isOneOne_comp (hsemi i).1 (L ξ)) hkp ha hb
      ?_ ?_
    · -- the normal slots: `ω_ε`
      intro i hi y
      have hθi : θ i = omega.form + ddcClosedForm (P.potential A ε) hf := by
        simp only [hθdef, concentrationSlot, hi, if_true]
      rw [lineValue_comp]
      set w := L ξ y with hw
      have hsplit : (θ i).val.coeff e (F ξ) ![w, Complex.I • w] =
          omega.form.val.coeff e (F ξ) ![w, Complex.I • w] +
            (ddcClosedForm (P.potential A ε) hf).val.coeff e (F ξ) ![w, Complex.I • w] := by
        rw [hθi]; simp
      have hω0 := lineValue_nonneg_of_isHermitian omega.isKahler.1 e hzt' w
      have hddc := quad_ddcClosedForm_coeff hf e hzt' w
      simp only [PositivityPerturbation.quad] at hddc
      -- the Levi form through the rescaled flattening
      have hFsmooth : ContDiffOn ℂ ∞ F B :=
        (contDiffOn_of_differentiableOn_complex Φ.invFun_holomorphic Φ.isOpen_target).comp
          T.contDiff.contDiffOn hT_target
      have hcomp := LeviFormHolomorphicComp.leviForm_comp hBopen e.val.open_target hFsmooth
        (hf e) hFt hξ y
      rw [(hFdR ξ hξ).fderiv] at hcomp
      change leviForm (fun ξ' => P.potential A ε (e.val.symm (F ξ'))) ξ y =
        leviForm (fun w' => P.potential A ε (e.val.symm w')) (F ξ) w at hcomp
      have hpot : (fun ξ' => P.potential A ε (e.val.symm (F ξ'))) =ᶠ[𝓝 ξ]
          (1 / (2 * A)) • ((fun _ : ComplexModel n => Real.log (ε ^ 2)) +
            fun ξ' => Real.log (normalSq k ξ' + 1)) := by
        filter_upwards [hBopen.mem_nhds hξ] with ξ' hξ'
        obtain ⟨-, -, -, hw', -, -⟩ := hball _ (hTB ξ' hξ')
        have hw'' : P.weight (e.val.symm (F ξ')) = normalSq k (T ξ') := hw'
        simp only [ConcentrationPartition.potential, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        rw [hw'', normalSq_scaleNormal, Complex.norm_real, Real.norm_of_nonneg hε.le]
        have hε2 : ε ^ 2 ≠ 0 := by positivity
        have hs1 : normalSq k ξ' + 1 ≠ 0 := by linarith [normalSq_nonneg k ξ']
        rw [show ε ^ 2 * normalSq k ξ' + ε ^ 2 = ε ^ 2 * (normalSq k ξ' + 1) by ring,
          Real.log_mul hε2 hs1]
        ring
      have hlog2 : ContDiffAt ℝ 2 (fun ξ' : ComplexModel n => Real.log (normalSq k ξ' + 1)) ξ := by
        refine (((contDiff_normalSq k).add contDiff_const).contDiffAt.log ?_).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
        exact ne_of_gt (by linarith [normalSq_nonneg k ξ])
      have hsum2 : ContDiffAt ℝ 2 ((fun _ : ComplexModel n => Real.log (ε ^ 2)) +
          fun ξ' => Real.log (normalSq k ξ' + 1)) ξ := contDiffAt_const.add hlog2
      have hlevi : leviForm (fun ξ' => P.potential A ε (e.val.symm (F ξ'))) ξ y =
          1 / (2 * A) * leviForm (fun ξ' => Real.log (normalSq k ξ' + 1)) ξ y := by
        rw [GlobalTubeFunction.leviForm_congr_of_eventuallyEq hpot, leviForm_smul hsum2,
          leviForm_add contDiffAt_const hlog2, leviForm_const, zero_add]
      have hmodel := le_leviForm_log_normalSq k ξ y
      have hξ1 : normalSq k ξ ≤ 1 := by
        have := normalSq_le_norm_sq k ξ
        have hξn : ‖ξ‖ < ρ := by simpa [hBdef] using hξ
        nlinarith [norm_nonneg ξ]
      have hden : (normalSq k ξ + 1) ^ 2 ≤ 4 := by nlinarith [normalSq_nonneg k ξ]
      have hy0 := normalSq_nonneg k y
      have hq : normalSq k y / 4 ≤ normalSq k y / (normalSq k ξ + 1) ^ 2 :=
        div_le_div_of_nonneg_left hy0 (by have := normalSq_nonneg k ξ; positivity) hden
      have hLsum : ∑ j : Fin n, (if k ≤ (j : ℕ) then a else 0) * ‖y j‖ ^ 2 = a * normalSq k y := by
        rw [normalSq, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        unfold nrm; split_ifs <;> ring
      rw [hLsum, hsplit, hddc, ← hcomp, hlevi]
      have hpi := Real.pi_pos
      have hA2 : 0 < 1 / (2 * A) := by positivity
      have h1 : a * normalSq k y ≤ 1 / (2 * A) * (normalSq k y / 4) := by
        rw [ha_def]; field_simp; ring_nf; exact le_rfl
      have h2 : 1 / (2 * A) * (normalSq k y / 4) ≤
          1 / (2 * A) * leviForm (fun ξ' => Real.log (normalSq k ξ' + 1)) ξ y :=
        mul_le_mul_of_nonneg_left (hq.trans hmodel) hA2.le
      have h3 : Real.pi * (omega.form.val.coeff e (F ξ) ![w, Complex.I • w] +
          1 / (2 * A) * leviForm (fun ξ' => Real.log (normalSq k ξ' + 1)) ξ y / Real.pi) =
          Real.pi * omega.form.val.coeff e (F ξ) ![w, Complex.I • w] +
            1 / (2 * A) * leviForm (fun ξ' => Real.log (normalSq k ξ' + 1)) ξ y := by
        field_simp
      rw [h3]
      have h4 := mul_nonneg hpi.le hω0
      linarith
    · -- the tangential slots: `ω`
      intro i hi y
      have hθi : θ i = omega.form := by
        simp only [hθdef, concentrationSlot, hi, if_false]
      rw [lineValue_comp]
      simp only [hAcoef]
      rw [hθi]
      set w := L ξ y with hw
      have hwT : w = fderiv ℂ Φ.invFun (T ξ) (T y) := rfl
      have hTy := hdΨ (T y)
      rw [← hwT] at hTy
      have htan := tangential_le_norm_sq_scaleNormal k (ε : ℂ) y
      have hk1 := hkah w
      have hLsum : ∑ j : Fin n, (if (j : ℕ) < k then b else 0) * ‖y j‖ ^ 2 =
          b * ∑ j : Fin n, (if (j : ℕ) < k then (1 : ℝ) else 0) * ‖y j‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> ring
      rw [hLsum]
      have hTy2 : ‖T y‖ ^ 2 ≤ C ^ 2 * ‖w‖ ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hTy 2
      have hpi := Real.pi_pos
      have hC2 : 0 < C ^ 2 := by positivity
      calc b * ∑ j : Fin n, (if (j : ℕ) < k then (1 : ℝ) else 0) * ‖y j‖ ^ 2
          ≤ b * (C ^ 2 * ‖w‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (htan.trans hTy2) hb
        _ = Real.pi * (m * ‖w‖ ^ 2) := by rw [hb_def]; field_simp
        _ ≤ Real.pi * omega.form.val.coeff e (F ξ) ![w, Complex.I • w] :=
            mul_le_mul_of_nonneg_left hk1 hpi.le
  calc ENNReal.ofReal (c * (volume B).toReal)
      = ENNReal.ofReal c * volume B := by
        rw [ENNReal.ofReal_mul hcpos.le, ENNReal.ofReal_toReal hvoltop]
    _ = ∫⁻ _ in B, ENNReal.ofReal c := (setLIntegral_const B _).symm
    _ ≤ ∫⁻ ξ in B, ENNReal.ofReal |LinearMap.det (((L ξ).restrictScalars ℝ :
          ComplexModel n →L[ℝ] ComplexModel n) : ComplexModel n →ₗ[ℝ] ComplexModel n)| *
            chartDensity θ e (F ξ) := setLIntegral_mono' measurableSet_ball hpt
    _ = ∫⁻ z in F '' B, chartDensity θ e z :=
        (lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_ball hF' hFinj
          (chartDensity θ e)).symm
    _ = globalMixedMeasure θ (fun _ _ => 0) hpsh (e.val.symm '' (F '' B)) :=
        (globalMixedMeasure_image_eq_lintegral hpsh e hFmeas hFBt).symm
    _ ≤ globalMixedMeasure θ (fun _ _ => 0) hpsh (U ∩ P.tube ε) := measure_mono hsub

end Mass

/-! ### Demailly--Păun 2.1 at a point of a closed submanifold, and the diagonal -/

section Main

open SubmanifoldConcentrationPotential BlowupFlatCoordinates PositiveClasses
  ManifoldTubePositivity GlobalNonPluripolar FirstPass.BlowupSequences

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

theorem ddcClosedForm_congr {f g : M → ℝ} (h : f = g) (hf : ChartSmooth (n := n) f)
    (hg : ChartSmooth (n := n) g) : ddcClosedForm f hf = ddcClosedForm g hg := by
  subst h; rfl


/-- The slots are semipositive as soon as `½ ω + ddᶜ f ≥ 0` (so the `∀ hpsh` in
`exists_massConcentration` is not vacuous): `ω_ε = ½ω + (½ω + ddᶜ f)`. -/
theorem thetaPlurisubharmonic_concentrationSlot (omega : KahlerBackground n M) {f : M → ℝ}
    (hf : ChartSmooth (n := n) f) (p : ℕ)
    (h : ((1 / 2 : ℝ) • omega.form + ddcClosedForm f hf).val.IsSemipositive) (i : Fin n) :
    ThetaPlurisubharmonic (concentrationSlot omega f hf p i).val (fun _ => 0) := by
  refine (LocalPotentials.thetaPlurisubharmonic_zero_iff _).mpr ?_
  intro e z hz v
  have h1 := h e z hz v
  have h2 := omega.isSemipositive e z hz v
  unfold concentrationSlot
  split_ifs
  · simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul] at h1 ⊢
    linarith
  · exact h2

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **Demailly--Păun's concentration of mass along a closed submanifold**
(`dp04-kahler-cone:2.1 (ii)-(iv)`, `bou02-volume:4.11`), at a point `x ∈ Y` regular of dimension
`k`: chart-smooth `f_ε`, open tubes `V_ε` increasing in `ε` and shrinking to `Y`,
`ω_ε = ω + ddᶜ f_ε ≥ ω/2` (cohomologous to `ω`), and for every neighbourhood `U` of `x` a `δ > 0`
bounding below the mass on `U ∩ V_ε` of the mixed measure of `n - k` copies of `ω_ε` and `k` copies
of `ω`, uniformly in `ε ∈ (0,1]`.  The family is adapted to `x` (dp04's single family serving every
point of `Y` is not claimed; the consumer fixes `x` first). -/
theorem exists_massConcentration (omega : KahlerBackground n M) {Y : Set M}
    (hY : IsClosedSubmanifold n Y) {x : M} {k : ℕ} (hx : RegularAtDim (n := n) Y x k) :
    ∃ (f : ℝ → M → ℝ) (hf : ∀ ε, ChartSmooth (n := n) (f ε)) (V : ℝ → Set M),
      (∀ ε, IsOpen (V ε)) ∧ (∀ ε ε', 0 < ε → ε ≤ ε' → V ε ⊆ V ε') ∧
      (⋂ ε ∈ Set.Ioc (0 : ℝ) 1, closure (V ε)) ⊆ Y ∧
      (∀ ε ∈ Set.Ioc (0 : ℝ) 1,
        ((1 / 2 : ℝ) • omega.form + ddcClosedForm (f ε) (hf ε)).val.IsSemipositive) ∧
      ∀ U ∈ 𝓝 x, ∃ δ : ℝ, 0 < δ ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
        ∀ hpsh : ∀ i, ThetaPlurisubharmonic
            (concentrationSlot omega (f ε) (hf ε) (n - k) i).val (fun _ => 0),
          ENNReal.ofReal δ ≤ globalMixedMeasure (concentrationSlot omega (f ε) (hf ε) (n - k))
            (fun _ _ => 0) hpsh (U ∩ V ε) := by
  classical
  obtain ⟨Φ, -, hΦ0, -, ι, hι, P, hPw⟩ := exists_adapted hY hx
  obtain ⟨A, hA, hsemi⟩ := P.exists_pos_isSemipositive_ddc_log_weight omega
  set f : ℝ → M → ℝ := fun ε => if ε = 0 then 0 else P.potential A ε with hfdef
  have hfeq : ∀ ε, ε ≠ 0 → f ε = P.potential A ε := fun ε hε => by simp [hfdef, hε]
  have hf : ∀ ε, ChartSmooth (n := n) (f ε) := by
    intro ε
    by_cases hε : ε = 0
    · have : f ε = 0 := by simp [hfdef, hε]
      rw [this]
      exact fun e => contDiffOn_const
    · rw [hfeq ε hε]; exact P.chartSmooth_potential A hε
  refine ⟨f, hf, P.tube, P.isOpen_tube, fun ε ε' hε h => P.tube_mono hε h,
    P.iInter_closure_tube_subset hY.1, ?_, ?_⟩
  · intro ε hε
    have hε0 : ε ≠ 0 := hε.1.ne'
    rw [ddcClosedForm_congr (hfeq ε hε0) (hf ε) (P.chartSmooth_potential A hε0)]
    exact P.isSemipositive_half_add_ddc_potential omega hA hsemi hε0
  · intro U hU
    obtain ⟨δ, hδ, hbound⟩ := exists_mass_lower_bound omega P hx.1 Φ hΦ0 hPw hA hU
    refine ⟨δ, hδ, fun ε hε => ?_⟩
    have key : ∀ (g : M → ℝ) (hg : ChartSmooth (n := n) g), g = P.potential A ε →
        ∀ hpsh : ∀ i, ThetaPlurisubharmonic
            (concentrationSlot omega g hg (n - k) i).val (fun _ => 0),
          ENNReal.ofReal δ ≤ globalMixedMeasure (concentrationSlot omega g hg (n - k))
            (fun _ _ => 0) hpsh (U ∩ P.tube ε) := by
      intro g hg hgeq
      subst hgeq
      exact hbound ε hε.1 hε.2 hg
    exact key (f ε) (hf ε) (hfeq ε hε.1.ne')

end Main

section Diagonal

open SubmanifoldConcentrationPotential PositiveClasses ManifoldTubePositivity GlobalNonPluripolar
  FirstPass.BlowupSequences ProductComplexManifold
open scoped ProductComplexManifold

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- The diagonal of `X × X` is a closed submanifold (regular of dimension `n` at each point). -/
theorem isClosedSubmanifold_diagonal :
    IsClosedSubmanifold (n + n) (Set.diagonal X) := by
  refine ⟨isClosed_diagonal, ?_⟩
  rintro ⟨a, b⟩ (h : a = b)
  subst h
  exact ⟨n, regularAtDim_diagonal a⟩

/-- **Demailly--Păun's concentration of mass on the diagonal of `X × X`** (the case used by
Boucksom 4.8 and dp04 2.12): `p₁^*ω + p₂^*ω`, the diagonal of codimension `n`, the first `n` slots
carrying `ω_ε`. -/
theorem exists_diagonal_massConcentration [CompactSpace X] [MeasurableSpace (X × X)]
    [BorelSpace (X × X)] (omega : KahlerBackground n X) (x : X) :
    ∃ (f : ℝ → X × X → ℝ) (hf : ∀ ε, ChartSmooth (n := n + n) (f ε)) (V : ℝ → Set (X × X)),
      (∀ ε, IsOpen (V ε)) ∧ (∀ ε ε', 0 < ε → ε ≤ ε' → V ε ⊆ V ε') ∧
      (⋂ ε ∈ Set.Ioc (0 : ℝ) 1, closure (V ε)) ⊆ Set.diagonal X ∧
      (∀ ε ∈ Set.Ioc (0 : ℝ) 1, ((1 / 2 : ℝ) • (prodKahlerBackground omega omega).form +
        ddcClosedForm (f ε) (hf ε)).val.IsSemipositive) ∧
      ∀ U ∈ 𝓝 (x, x), ∃ δ : ℝ, 0 < δ ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
        ∀ hpsh : ∀ i, ThetaPlurisubharmonic
            (concentrationSlot (prodKahlerBackground omega omega) (f ε) (hf ε) n i).val
            (fun _ => 0),
          ENNReal.ofReal δ ≤ globalMixedMeasure
            (concentrationSlot (prodKahlerBackground omega omega) (f ε) (hf ε) n)
            (fun _ _ => 0) hpsh (U ∩ V ε) := by
  have h := exists_massConcentration (prodKahlerBackground omega omega)
    isClosedSubmanifold_diagonal (regularAtDim_diagonal x)
  have hp : n + n - n = n := Nat.add_sub_cancel n n
  rw [hp] at h
  exact h

end Diagonal

end

end SGPT.Foundations.Analysis.Pending.SubmanifoldMassConcentration
