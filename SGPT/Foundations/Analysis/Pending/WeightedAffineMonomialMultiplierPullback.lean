import SGPT.Foundations.Analysis.Pending.BlowupMonomialJacobian
import SGPT.Foundations.Analysis.Pending.BlowupJacobianMultiplierGermEquivalence
import SGPT.Foundations.Analysis.Pending.SNCHolomorphicLogNormalForm

set_option autoImplicit false

/-! # Actual weighted affine monomial charts and original Jacobian multiplier germs -/

open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.WeightedAffineMonomialMultiplierPullback

open FirstPass DivisorialChangeOfVariables

noncomputable section

/-- The literal polynomial weighted affine chart; the pivot exponent is unused. -/
def affineMonomial {n : ℕ} (a : Fin n → ℕ) (v : ComplexModel n) (j : Fin n)
    (w : ComplexModel n) : ComplexModel n :=
  WithLp.toLp 2 fun i => if i = j then w i else w j ^ a i * (v i + w i)

private theorem contDiff_affineMonomial {n : ℕ} (a : Fin n → ℕ)
    (v : ComplexModel n) (j : Fin n) : ContDiff ℂ ∞ (affineMonomial a v j) := by
  refine (contDiff_piLp 2).2 fun i => ?_
  have hp (l : Fin n) : ContDiff ℂ ∞ fun w : ComplexModel n => w l :=
    (EuclideanSpace.proj l : ComplexModel n →L[ℂ] ℂ).contDiff
  simp only [affineMonomial]
  split_ifs
  · exact hp i
  · exact ((hp j).pow (a i)).mul (contDiff_const.add (hp i))

private theorem fderiv_affineMonomial_apply {n : ℕ} (a : Fin n → ℕ)
    (v : ComplexModel n) (j : Fin n) (w u : ComplexModel n) (i : Fin n) :
    (fderiv ℂ (affineMonomial a v j) w u) i =
      if i = j then u i else
        ((a i : ℂ) * w j ^ (a i - 1) * u j) * (v i + w i) + w j ^ a i * u i := by
  classical
  let pr (l : Fin n) : ComplexModel n →L[ℂ] ℂ := EuclideanSpace.proj l
  have hF := (contDiff_affineMonomial a v j).differentiable (by simp) w
  have hcomp : HasFDerivAt (fun z => affineMonomial a v j z i)
      ((pr i).comp (fderiv ℂ (affineMonomial a v j) w)) w :=
    (pr i).hasFDerivAt.comp w hF.hasFDerivAt
  by_cases hi : i = j
  · have heq : (fun z => affineMonomial a v j z i) = fun z : ComplexModel n => z i := by
      funext z
      simp only [affineMonomial, hi, if_true, PiLp.toLp_apply]
    rw [heq] at hcomp
    have he := congrArg (fun L : ComplexModel n →L[ℂ] ℂ => L u)
      (hcomp.unique (pr i).hasFDerivAt)
    simpa [pr, hi] using he
  · have heq : (fun z => affineMonomial a v j z i) =
        fun z : ComplexModel n => z j ^ a i * (v i + z i) := by
      funext z
      simp only [affineMonomial, hi, if_false, PiLp.toLp_apply]
    rw [heq] at hcomp
    have hh := ((pr j).hasFDerivAt.pow (a i)).mul
      ((hasFDerivAt_const (v i) w).add (pr i).hasFDerivAt)
    have he := congrArg (fun L : ComplexModel n →L[ℂ] ℂ => L u) (hcomp.unique hh)
    simpa [pr, hi, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc] using he

private theorem exists_moved_ne {n : ℕ} (σ : Equiv.Perm (Fin n)) (j : Fin n)
    (hσ : σ ≠ 1) : ∃ i : Fin n, i ≠ j ∧ σ i ≠ i := by
  classical
  by_contra hnot
  have hfix (i : Fin n) (hi : i ≠ j) : σ i = i := by
    by_contra hmove
    exact hnot ⟨i, hi, hmove⟩
  have hj : σ j = j := by
    by_cases hh : σ j = j
    · exact hh
    · exact σ.injective (hfix (σ j) hh)
  apply hσ
  apply Equiv.ext
  intro i
  by_cases hi : i = j
  · simpa [hi] using hj
  · exact hfix i hi

/-- All actual smoothness, determinant, injectivity and null geometry is
produced from the literal weighted chart, including zero pivots and exponents. -/
theorem geometry_affineMonomial {n : ℕ} (a : Fin n → ℕ) (v : ComplexModel n)
    (j : Fin n) :
    ContDiff ℂ ∞ (affineMonomial a v j) ∧
      (∀ w, complexJacobian (affineMonomial a v j) w =
        w j ^ (∑ i ∈ Finset.univ.erase j, a i)) ∧
      InjOn (affineMonomial a v j) {w | w j ≠ 0} ∧
      volume {w : ComplexModel n | w j = 0} = 0 := by
  classical
  refine ⟨contDiff_affineMonomial a v j, ?_, ?_, ?_⟩
  · intro w
    let M := FirstPass.MongeAmpere.standardMatrix
      (fderiv ℂ (affineMonomial a v j) w).toLinearMap
    have hoff (r c : Fin n) (hc : c ≠ j) (hrc : r ≠ c) : M r c = 0 := by
      change FirstPass.MongeAmpere.standardMatrix
        (fderiv ℂ (affineMonomial a v j) w).toLinearMap r c = 0
      rw [FirstPass.MongeAmpere.standardMatrix_apply]
      change (fderiv ℂ (affineMonomial a v j) w (FirstPass.MongeAmpere.coordinateVector c)) r = 0
      rw [fderiv_affineMonomial_apply]
      split_ifs <;> simp [FirstPass.MongeAmpere.coordinateVector, hrc, hc.symm]
    have hdiag (i : Fin n) : M i i = if i = j then 1 else w j ^ a i := by
      change FirstPass.MongeAmpere.standardMatrix
        (fderiv ℂ (affineMonomial a v j) w).toLinearMap i i = _
      rw [FirstPass.MongeAmpere.standardMatrix_apply]
      change (fderiv ℂ (affineMonomial a v j) w (FirstPass.MongeAmpere.coordinateVector i)) i = _
      rw [fderiv_affineMonomial_apply]
      split_ifs with hi
      · simp [FirstPass.MongeAmpere.coordinateVector]
      · simp [FirstPass.MongeAmpere.coordinateVector, Ne.symm hi]
    have hdet : M.det = ∏ i : Fin n, M i i := by
      rw [Matrix.det_apply, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
      · simp
      · intro σ _ hσ
        obtain ⟨i, hij, hmove⟩ := exists_moved_ne σ j hσ
        have hz : ∏ r : Fin n, M (σ r) r = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ i)
          exact hoff (σ i) i hij hmove
        rw [hz, smul_zero]
      · simp
    have hJ : complexJacobian (affineMonomial a v j) w = M.det :=
      (FirstPass.MongeAmpere.det_standardMatrix
        (fderiv ℂ (affineMonomial a v j) w).toLinearMap).symm
    rw [hJ, hdet]
    simp_rw [hdiag]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
    simp only [ite_true, mul_one]
    calc
      _ = ∏ i ∈ Finset.univ.erase j, w j ^ a i := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [if_neg (Finset.mem_erase.mp hi).1]
      _ = _ := Finset.prod_pow_eq_pow_sum _ _ (w j)
  · intro w hw z hz heq
    have hpivot : w j = z j := by
      have h := congrArg (fun q : ComplexModel n => q j) heq
      simpa [affineMonomial] using h
    apply PiLp.ext
    intro i
    by_cases hi : i = j
    · simpa only [hi] using hpivot
    · have h := congrArg (fun q : ComplexModel n => q i) heq
      simp only [affineMonomial, PiLp.toLp_apply, hi, if_false, hpivot] at h
      exact add_left_cancel (mul_left_cancel₀ (pow_ne_zero (a i) hz) h)
  · apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [SNCHolomorphicLogNormalForm.ae_coordinates_ne_zero n] with w hw
    exact hw j

/-- The actual chart internally supplies every geometric hypothesis of the
original Jacobian-weighted germ transport. -/
theorem multiplierIntegrableAt_comp_affineMonomial {n : ℕ} (a : Fin n → ℕ)
    (v : ComplexModel n) (j : Fin n) {w : ComplexModel n}
    {ψ : ComplexModel n → EReal} {c : ℝ} {f : ComplexModel n → ℂ}
    (hψ : QuasiPlurisubharmonicAt ψ (affineMonomial a v j w))
    (hint : MultiplierIntegrableAt ψ c f (affineMonomial a v j w) volume) :
    MultiplierIntegrableAt (fun z => ψ (affineMonomial a v j z)) c
      (fun z => f (affineMonomial a v j z) * z j ^ (∑ i ∈ Finset.univ.erase j, a i)) w volume := by
  obtain ⟨hT, hJ, hinj, hnull⟩ := geometry_affineMonomial a v j
  have hpull := BlowupJacobianMultiplierGermEquivalence.multiplierIntegrableAt_comp_mul_complexJacobian
    isOpen_univ hT.contDiffOn (mem_univ w) hnull
    (by
      intro z hz z' hz' he
      exact hinj hz.2 hz'.2 he) hψ hint
  simpa only [hJ] using hpull

end
end SGPT.Foundations.Analysis.Pending.WeightedAffineMonomialMultiplierPullback
