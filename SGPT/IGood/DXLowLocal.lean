import SGPT.Foundations.Analysis.Pending.CoordinateDensityHermitian
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialIndependence
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity

/-!
# Local calculus for the sharp Bergman lower bound

Blueprint `claude-dx-low`, nodes `claude-dx-low:gaussian` and `claude-dx-low:gauge`. Two local
facts on `ℂⁿ` used by the peak-section lower bound of the asymptotic Riemann–Roch formula
(source `thm:DXmain1`, `prop:DXmainanalytic`):

* `lintegral_exp_neg_leviForm` (**Gaussian integral of a positive Levi form**): if `Φ` is `C²`
  at `p` and its Levi form `L(w) = leviForm Φ p w` is positive definite, then for `t > 0`
  `∫_{ℂⁿ} e^{-t L(w)} dλ(w) = n! / (tⁿ · smoothDensity Φ p)`, where
  `smoothDensity Φ p = (n!/πⁿ) det(∂²Φ/∂zⱼ∂z̄ₖ)(p)` is the density of `(ddᶜΦ)ⁿ` at `p` with
  respect to Lebesgue measure (TN's `MongeAmpere.smoothDensity`). Proof: unitary
  diagonalization of the coefficient matrix of `ddᶜΦ(p)` (as in TN's
  `actualTopPowerDensity_eq_normalizedTopPowerDensity`) and the one-variable complex Gaussian.
* `gaugeExponent` (**the quadratic holomorphic gauge**): for a `C²` function `Φ` near `p` the
  holomorphic polynomial `P(w) = ½(ℓ(w) + Q(w))` (`ℓ` the `ℂ`-linear extension of `dΦ(p)`, `Q`
  the holomorphic part of the Hessian) satisfies
  `Φ(p + w) = Φ(p) + 2 Re P(w) + L(w) + R(w)` with `|R(w)| ≤ η |w|²` near `0` for every `η > 0`
  (`exists_gauge_remainder_le`). It is the standard normalization of the weight at a point.

The Hessian decomposition, the Taylor remainder and the measure-preservation of the Euclidean
coordinates are adapted from the previous team's drafts
(`wip/RESUME-20261109/KODAIRA-TRANSPORT`, also ported by lane BERGMAN2 as
`SGPT.Bergman.SharpLocalUpper`, not imported here).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.IGood.DXLow

open MeasureTheory Set Filter Metric Module
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open scoped Topology ENNReal ComplexConjugate Matrix

/-! ### Lebesgue measure on the complex model and the complex Gaussian -/

/-- The Euclidean coordinates `ℂⁿ → (Fin n → ℂ)` preserve Lebesgue measure. -/
theorem complexModel_ofLp_measurePreserving (n : ℕ) :
    MeasurePreserving (@WithLp.ofLp 2 (Fin n → ℂ)) := by
  classical
  let b := Pi.basis (fun _ : Fin n => Complex.basisOneI)
  let B := Pi.orthonormalBasis (fun _ : Fin n => Complex.orthonormalBasisOneI)
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)
  have hpar : (b.parallelepiped : Set (Fin n → ℂ)) =
      Set.univ.pi (fun _ : Fin n => (Complex.basisOneI.parallelepiped : Set ℂ)) := by
    change _root_.parallelepiped b =
      Set.univ.pi (fun _ : Fin n => _root_.parallelepiped Complex.basisOneI)
    simp_rw [parallelepiped_basis_eq]
    ext z
    simp [b, Pi.basis_repr]
    constructor
    · intro h i
      exact ⟨by simpa using h ⟨i, 0⟩, by simpa using h ⟨i, 1⟩⟩
    · intro h ⟨i, j⟩
      fin_cases j
      · simpa using (h i).1
      · simpa using (h i).2
  have hcomplex : (volume : Measure ℂ) Complex.basisOneI.parallelepiped = 1 := by
    change volume (_root_.parallelepiped Complex.basisOneI) = 1
    simpa only [← Complex.toBasis_orthonormalBasisOneI, OrthonormalBasis.coe_toBasis] using
      Complex.orthonormalBasisOneI.volume_parallelepiped
  have hb : b.addHaar = (volume : Measure (Fin n → ℂ)) := by
    apply (Basis.addHaar_eq_iff b volume).mpr
    rw [hpar, volume_pi_pi]
    simp only [hcomplex, Finset.prod_const_one]
  have hmapbasis : B.toBasis.map e.toLinearEquiv = b := by
    rw [show B.toBasis = b.map e.symm.toLinearEquiv from Pi.orthonormalBasis.toBasis _]
    apply DFunLike.ext
    intro j
    change e (e.symm (b j)) = b j
    exact e.apply_symm_apply (b j)
  have hm : Measure.map e (volume : Measure (EuclideanSpace ℂ (Fin n))) = volume := by
    rw [← B.addHaar_eq_volume, Basis.map_addHaar, hmapbasis, hb]
  change MeasurePreserving e
  exact ⟨e.continuous.measurable, hm⟩

theorem complexGaussian_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : ℂ => Real.exp (-b * ‖z‖ ^ 2)) := by
  have hprod := (integrable_exp_neg_mul_sq hb).mul_prod (integrable_exp_neg_mul_sq hb)
  have hcomplex := (Complex.volume_preserving_equiv_real_prod.integrable_comp_emb
    Complex.measurableEquivRealProd.measurableEmbedding).2 hprod
  have hfun : (fun z : ℂ => Real.exp (-b * ‖z‖ ^ 2)) =
      (fun z : ℝ × ℝ => Real.exp (-b * z.1 ^ 2) * Real.exp (-b * z.2 ^ 2)) ∘
        Complex.measurableEquivRealProd := by
    funext z
    change Real.exp (-b * ‖z‖ ^ 2) = Real.exp (-b * z.re ^ 2) * Real.exp (-b * z.im ^ 2)
    rw [← Real.exp_add, Complex.sq_norm, Complex.normSq_apply]
    congr 1
    ring
  rw [hfun]
  exact hcomplex

theorem complexGaussian_integral {b : ℝ} (hb : 0 < b) :
    (∫ z : ℂ, Real.exp (-b * ‖z‖ ^ 2)) = Real.pi / b := by
  calc
    (∫ z : ℂ, Real.exp (-b * ‖z‖ ^ 2)) =
        ∫ z : ℂ, Real.exp (-b * z.re ^ 2) * Real.exp (-b * z.im ^ 2) := by
      congr 1
      ext z
      rw [← Real.exp_add, Complex.sq_norm, Complex.normSq_apply]
      congr 1
      ring
    _ = ∫ x : ℝ × ℝ, Real.exp (-b * x.1 ^ 2) * Real.exp (-b * x.2 ^ 2) :=
      Complex.volume_preserving_equiv_real_prod.integral_comp'
        (fun x : ℝ × ℝ => Real.exp (-b * x.1 ^ 2) * Real.exp (-b * x.2 ^ 2))
    _ = (Real.sqrt (Real.pi / b)) ^ 2 := by
      change (∫ x : ℝ × ℝ, Real.exp (-b * x.1 ^ 2) * Real.exp (-b * x.2 ^ 2)
        ∂(volume.prod volume)) = _
      rw [integral_prod_mul (fun x : ℝ => Real.exp (-b * x ^ 2))
        (fun x : ℝ => Real.exp (-b * x ^ 2)), integral_gaussian, ← pow_two]
    _ = Real.pi / b := Real.sq_sqrt (div_nonneg Real.pi_pos.le hb.le)

/-- **The diagonal complex Gaussian**: `∫_{ℂⁿ} e^{-∑ bⱼ |zⱼ|²} = ∏ π / bⱼ` for `bⱼ > 0`. -/
theorem lintegral_exp_neg_diag {n : ℕ} {b : Fin n → ℝ} (hb : ∀ j, 0 < b j) :
    ∫⁻ z : ComplexModel n, ENNReal.ofReal (Real.exp (-∑ j, b j * ‖z j‖ ^ 2)) =
      ENNReal.ofReal (∏ j, Real.pi / b j) := by
  have hpres := complexModel_ofLp_measurePreserving n
  have h1 : ∫⁻ z : ComplexModel n, ENNReal.ofReal (Real.exp (-∑ j, b j * ‖z j‖ ^ 2)) =
      ∫⁻ z : Fin n → ℂ, ENNReal.ofReal (Real.exp (-∑ j, b j * ‖z j‖ ^ 2)) := by
    have := hpres.lintegral_comp_emb (MeasurableEquiv.toLp 2 (Fin n → ℂ)).symm.measurableEmbedding
      (fun z : Fin n → ℂ => ENNReal.ofReal (Real.exp (-∑ j, b j * ‖z j‖ ^ 2)))
    exact this
  have hprod : (fun z : Fin n → ℂ => Real.exp (-∑ j, b j * ‖z j‖ ^ 2)) =
      fun z => ∏ j, Real.exp (-b j * ‖z j‖ ^ 2) := by
    funext z
    simp only [← Finset.sum_neg_distrib, neg_mul]
    exact Real.exp_sum _ _
  have hint : Integrable (fun z : Fin n → ℂ => Real.exp (-∑ j, b j * ‖z j‖ ^ 2)) := by
    rw [hprod]
    exact Integrable.fintype_prod (fun j => complexGaussian_integrable (hb j))
  rw [h1, ← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun z => (Real.exp_pos _).le), hprod,
    integral_fintype_prod_volume_eq_prod (fun j (z : ℂ) => Real.exp (-b j * ‖z‖ ^ 2))]
  congr 1
  exact Finset.prod_congr rfl fun j _ => complexGaussian_integral (hb j)

/-! ### Unitary diagonalization of a real `(1,1)`-form -/

section Diagonalization

variable {n : ℕ}

/-- The quadratic form of a `(1,1)`-form with real diagonal coefficient matrix. -/
theorem diag_quadratic (A : CoordinateRealTwoForm n) (hA : IsOneOne A) (d : Fin n → ℝ)
    (hdiag : normalizedHermitianMatrix A = Matrix.diagonal (fun j => (d j : ℂ)))
    (z : ComplexModel n) :
    Real.pi * A ![z, Complex.I • z] = ∑ j, d j * ‖z j‖ ^ 2 := by
  have hz : (∑ j, z j • coordinateVector j : ComplexModel n) = z := by
    ext k
    rw [show ((∑ j, z j • coordinateVector j : ComplexModel n)).ofLp k =
      ∑ j, (z j • coordinateVector j : ComplexModel n).ofLp k by simp]
    rw [Finset.sum_eq_single k]
    · simp [coordinateVector]
    · intro j _ hj
      simp [coordinateVector, Ne.symm hj]
    · simp
  have hkey (j k : Fin n) :
      (Real.pi : ℂ) * hermitianEntry A (coordinateVector j) (coordinateVector k) =
        if j = k then (d j : ℂ) else 0 := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M j k) hdiag
    simpa only [normalizedHermitianMatrix_apply', Matrix.diagonal_apply] using h
  have hinner (j : Fin n) :
      (Real.pi : ℂ) * hermitianEntry A (coordinateVector j) z =
        conj (z j) * (d j : ℂ) := by
    have hexp := hermitianEntry_sum_right Finset.univ (fun k => z k)
      coordinateVector (coordinateVector j) (A := A)
    rw [hz] at hexp
    rw [hexp, Finset.mul_sum]
    calc
      (∑ k, (Real.pi : ℂ) *
          (conj (z k) * hermitianEntry A (coordinateVector j) (coordinateVector k))) =
          ∑ k, conj (z k) *
            ((Real.pi : ℂ) * hermitianEntry A (coordinateVector j) (coordinateVector k)) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = conj (z j) * (d j : ℂ) := by simp_rw [hkey]; simp
  have hleft : hermitianEntry A z z =
      ∑ j, z j * hermitianEntry A (coordinateVector j) z := by
    simpa only [hz] using
      (hermitianEntry_sum_left hA Finset.univ (fun j => z j) coordinateVector z)
  have hQ : (Real.pi : ℂ) * hermitianEntry A z z =
      ∑ j, (d j : ℂ) * (‖z j‖ ^ 2 : ℝ) := by
    rw [hleft, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    calc
      (Real.pi : ℂ) * (z j * hermitianEntry A (coordinateVector j) z) =
          z j * ((Real.pi : ℂ) * hermitianEntry A (coordinateVector j) z) := by ring
      _ = z j * (conj (z j) * (d j : ℂ)) := by rw [hinner]
      _ = (d j : ℂ) * (‖z j‖ ^ 2 : ℝ) := by
        rw [← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        ring
  have hreal := congrArg Complex.re hQ
  simp [hermitianEntry, Complex.mul_re] at hreal
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using hreal

/-- **Unitary diagonalization** of a real `(1,1)`-form `A`: a `ℂ`-linear `S` with
`|det S| = 1` and real weights `d` with `π A(Sz, iSz) = ∑ dⱼ |zⱼ|²` and
`actualTopPowerDensity A = (n!/πⁿ) ∏ dⱼ`. -/
theorem exists_unitary_diagonalization (A : CoordinateRealTwoForm n) (hA : IsOneOne A) :
    ∃ S : ComplexModel n →ₗ[ℂ] ComplexModel n, ∃ d : Fin n → ℝ,
      Complex.normSq (LinearMap.det S) = 1 ∧
      (∀ z, Real.pi * A ![S z, Complex.I • S z] = ∑ j, d j * ‖z j‖ ^ 2) ∧
      actualTopPowerDensity A = (n.factorial : ℝ) / Real.pi ^ n * ∏ j, d j := by
  classical
  have hH : (normalizedHermitianMatrix A).IsHermitian :=
    normalizedHermitianMatrix_isHermitian A hA
  set U : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
    with hUdef
  set S : ComplexModel n →ₗ[ℂ] ComplexModel n :=
    (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis).symm (U.map (starRingEnd ℂ)) with hSdef
  have hSM : standardMatrix S = U.map (starRingEnd ℂ) := by
    rw [standardMatrix, hSdef, LinearEquiv.apply_symm_apply]
  have htrans : (U.map (starRingEnd ℂ))ᵀ = star U := by
    ext j k
    simp
  have hmapmap : (U.map (starRingEnd ℂ)).map (starRingEnd ℂ) = U := by
    ext j k
    simp
  have hdiag : normalizedHermitianMatrix (compLinearMap A S) =
      Matrix.diagonal fun j => ((hH.eigenvalues j : ℝ) : ℂ) := by
    rw [normalizedHermitianMatrix_compLinearMap hA, hSM, htrans, hmapmap]
    have := hH.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at this
    rw [← hUdef] at this
    exact this
  have hdetU : Complex.normSq (Matrix.det U) = 1 := by
    have h1 : (star U) * U = 1 := by
      rw [hUdef]
      exact_mod_cast Unitary.coe_star_mul_self hH.eigenvectorUnitary
    have h2 : (starRingEnd ℂ) (Matrix.det U) * Matrix.det U = 1 := by
      have := congrArg Matrix.det h1
      rwa [Matrix.det_mul, Matrix.det_one, Matrix.star_eq_conjTranspose,
        Matrix.det_conjTranspose, Complex.star_def] at this
    have h3 : ((Complex.normSq (Matrix.det U) : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      exact h2
    exact_mod_cast h3
  have hdetS : Complex.normSq (LinearMap.det S) = 1 := by
    have hd : LinearMap.det S = (U.map (starRingEnd ℂ)).det := by
      rw [← det_standardMatrix, hSM]
    have hconj : (U.map (starRingEnd ℂ)).det = (starRingEnd ℂ) U.det :=
      (RingHom.map_det (starRingEnd ℂ) U).symm
    rw [hd, hconj, Complex.normSq_conj, hdetU]
  refine ⟨S, fun j => hH.eigenvalues j, hdetS, fun z => ?_, ?_⟩
  · have h := diag_quadratic (compLinearMap A S) (isOneOne_compLinearMap hA S)
      (fun j => hH.eigenvalues j) hdiag z
    simpa only [compLinearMap_apply, map_smul] using h
  · have h3 := actualTopPowerDensity_eq_normalizedTopPowerDensity_of_diagonal
      (isOneOne_compLinearMap hA S) (fun j => hH.eigenvalues j) hdiag
    rw [actualTopPowerDensity_compLinearMap S, hdetS, one_mul] at h3
    rw [h3, normalizedTopPowerDensity, hdiag, complexTopCoefficient_eq, Matrix.det_diagonal]
    have hprod : (∏ j, ((hH.eigenvalues j : ℝ) : ℂ)) = ((∏ j, hH.eigenvalues j : ℝ) : ℂ) := by
      push_cast; rfl
    rw [hprod, ← Complex.ofReal_mul, Complex.ofReal_re]

end Diagonalization

/-! ### The Gaussian integral of a positive `(1,1)`-form -/

section Gaussian

variable {n : ℕ}

/-- The real determinant of a `ℂ`-linear map is `|det_ℂ|²`. -/
theorem realDet_eq_normSq (S : ComplexModel n →ₗ[ℂ] ComplexModel n) :
    LinearMap.det (S.restrictScalars ℝ) = Complex.normSq (LinearMap.det S) := by
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_eq]
  rfl

/-- Change of variables along a `ℂ`-linear map of determinant of modulus one. -/
theorem lintegral_comp_of_normSq_det_eq_one (S : ComplexModel n →ₗ[ℂ] ComplexModel n)
    (hS : Complex.normSq (LinearMap.det S) = 1) {f : ComplexModel n → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ w, f w = ∫⁻ z, f (S z) := by
  have hdet : LinearMap.det (S.restrictScalars ℝ) = 1 := by rw [realDet_eq_normSq, hS]
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := (volume : Measure (ComplexModel n))) (f := S.restrictScalars ℝ)
    (by rw [hdet]; exact one_ne_zero)
  rw [hdet, inv_one, abs_one, ENNReal.ofReal_one, one_smul] at hmap
  have hSm : Measurable (S.restrictScalars ℝ) :=
    (LinearMap.continuous_of_finiteDimensional (S.restrictScalars ℝ)).measurable
  conv_lhs => rw [← hmap]
  rw [lintegral_map hf hSm]
  rfl

/-- **Unitary diagonalization of a positive `(1,1)`-form**: the weights are positive. -/
theorem exists_pos_unitary_diagonalization (A : CoordinateRealTwoForm n) (hA : IsOneOne A)
    (hpos : ∀ v : ComplexModel n, v ≠ 0 → 0 < A ![v, Complex.I • v]) :
    ∃ S : ComplexModel n →ₗ[ℂ] ComplexModel n, ∃ d : Fin n → ℝ,
      Complex.normSq (LinearMap.det S) = 1 ∧ (∀ j, 0 < d j) ∧
      (∀ z, Real.pi * A ![S z, Complex.I • S z] = ∑ j, d j * ‖z j‖ ^ 2) ∧
      actualTopPowerDensity A = (n.factorial : ℝ) / Real.pi ^ n * ∏ j, d j := by
  classical
  obtain ⟨S, d, hS, hq, hdens⟩ := exists_unitary_diagonalization A hA
  have hSinj : Function.Injective S := by
    have hne : LinearMap.det S ≠ 0 := by
      intro h; rw [h, map_zero] at hS; exact zero_ne_one hS
    have hker : LinearMap.ker S = ⊥ := by
      by_contra h
      exact hne (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)
    exact LinearMap.ker_eq_bot.mp hker
  have hd : ∀ j, 0 < d j := by
    intro j
    have hv : S (coordinateVector j) ≠ 0 := by
      intro h
      have : coordinateVector (n := n) j = 0 := hSinj (by rw [h, map_zero])
      have h1 := congrArg (fun v : ComplexModel n => v j) this
      simp [coordinateVector] at h1
    have h1 := hq (coordinateVector j)
    have h2 : ∑ i, d i * ‖(coordinateVector (n := n) j) i‖ ^ 2 = d j := by
      rw [Finset.sum_eq_single j]
      · simp [coordinateVector]
      · intro i _ hij
        simp [coordinateVector, hij]
      · simp
    rw [h2] at h1
    rw [← h1]
    exact mul_pos Real.pi_pos (hpos _ hv)
  exact ⟨S, d, hS, hd, hq, hdens⟩

/-- A positive `(1,1)`-form has positive top-power density. -/
theorem actualTopPowerDensity_pos (A : CoordinateRealTwoForm n) (hA : IsOneOne A)
    (hpos : ∀ v : ComplexModel n, v ≠ 0 → 0 < A ![v, Complex.I • v]) :
    0 < actualTopPowerDensity A := by
  obtain ⟨S, d, -, hd, -, hdens⟩ := exists_pos_unitary_diagonalization A hA hpos
  rw [hdens]
  have : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  exact mul_pos (div_pos this (pow_pos Real.pi_pos n)) (Finset.prod_pos fun j _ => hd j)

/-- **The Gaussian integral of a positive `(1,1)`-form** (blueprint `claude-dx-low:gaussian`):
`∫_{ℂⁿ} e^{-t π A(w, iw)} dλ(w) = n! / (tⁿ · actualTopPowerDensity A)` for `t > 0`, when `A` is
of type `(1,1)` and `A(v, iv) > 0` for `v ≠ 0`. -/
theorem lintegral_exp_neg_twoForm (A : CoordinateRealTwoForm n) (hA : IsOneOne A)
    (hpos : ∀ v : ComplexModel n, v ≠ 0 → 0 < A ![v, Complex.I • v]) {t : ℝ} (ht : 0 < t) :
    ∫⁻ w : ComplexModel n, ENNReal.ofReal (Real.exp (-(t * (Real.pi * A ![w, Complex.I • w])))) =
      ENNReal.ofReal ((n.factorial : ℝ) / (t ^ n * actualTopPowerDensity A)) := by
  classical
  obtain ⟨S, d, hS, hd, hq, hdens⟩ := exists_pos_unitary_diagonalization A hA hpos
  have hmeas : Measurable fun w : ComplexModel n =>
      ENNReal.ofReal (Real.exp (-(t * (Real.pi * A ![w, Complex.I • w])))) := by
    refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
    refine (Measurable.const_mul (Measurable.const_mul ?_ _) _).neg
    have hc : Continuous fun w : ComplexModel n => A ![w, Complex.I • w] := by
      have : Continuous fun w : ComplexModel n => (![w, Complex.I • w] : Fin 2 → ComplexModel n) :=
        continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop
      exact A.cont.comp this
    exact hc.measurable
  rw [lintegral_comp_of_normSq_det_eq_one S hS hmeas]
  have hfun : (fun z : ComplexModel n =>
      ENNReal.ofReal (Real.exp (-(t * (Real.pi * A ![S z, Complex.I • S z]))))) =
      fun z => ENNReal.ofReal (Real.exp (-∑ j, (t * d j) * ‖z j‖ ^ 2)) := by
    funext z
    rw [hq z, Finset.mul_sum]
    simp only [mul_assoc]
  rw [hfun, lintegral_exp_neg_diag (fun j => mul_pos ht (hd j)), hdens]
  congr 1
  have hprodd : 0 < ∏ j, d j := Finset.prod_pos fun j _ => hd j
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hpi : 0 < Real.pi ^ n := pow_pos Real.pi_pos n
  have htn : 0 < t ^ n := pow_pos ht n
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  field_simp

/-- **The Gaussian integral of a positive Levi form** (blueprint `claude-dx-low:gaussian`): if
`Φ` is `C²` at `p` with positive definite Levi form, then for `t > 0`,
`∫_{ℂⁿ} e^{-t L(w)} dλ(w) = n! / (tⁿ · smoothDensity Φ p)`, `L = leviForm Φ p`. -/
theorem lintegral_exp_neg_leviForm {Φ : ComplexModel n → ℝ} {p : ComplexModel n}
    (hΦ : ContDiffAt ℝ 2 Φ p) (hpos : ∀ v : ComplexModel n, v ≠ 0 → 0 < leviForm Φ p v)
    {t : ℝ} (ht : 0 < t) :
    ∫⁻ w : ComplexModel n, ENNReal.ofReal (Real.exp (-(t * leviForm Φ p w))) =
      ENNReal.ofReal ((n.factorial : ℝ) / (t ^ n * smoothDensity Φ p)) := by
  have hA : IsOneOne (smoothDDC Φ p) := smoothDDC_isOneOne hΦ
  have hlevi : ∀ w, Real.pi * smoothDDC Φ p ![w, Complex.I • w] = leviForm Φ p w := by
    intro w
    rw [smoothDDC_complexDiagonal_eq_leviForm hΦ w]
    field_simp
  have h := lintegral_exp_neg_twoForm (smoothDDC Φ p) hA (fun v hv => by
    have := hpos v hv
    rw [← hlevi v] at this
    exact pos_of_mul_pos_right this Real.pi_pos.le) ht
  simp only [hlevi] at h
  rw [h, actualTopPowerDensity_smoothDDC hΦ]

/-- A `C²` function with positive definite Levi form at `p` has `smoothDensity Φ p > 0`. -/
theorem smoothDensity_pos {Φ : ComplexModel n → ℝ} {p : ComplexModel n}
    (hΦ : ContDiffAt ℝ 2 Φ p) (hpos : ∀ v : ComplexModel n, v ≠ 0 → 0 < leviForm Φ p v) :
    0 < smoothDensity Φ p := by
  rw [← actualTopPowerDensity_smoothDDC hΦ]
  refine actualTopPowerDensity_pos _ (smoothDDC_isOneOne hΦ) fun v hv => ?_
  rw [smoothDDC_complexDiagonal_eq_leviForm hΦ v]
  exact div_pos (hpos v hv) Real.pi_pos

end Gaussian

/-! ### The quadratic holomorphic gauge -/

section Gauge

variable {n : ℕ}

/-- The `ℂ`-linear part `C - i C(i ·)` of a real-linear map into a complex space. -/
def complexLinearProjection {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (C : ComplexModel n →L[ℝ] F) : ComplexModel n →L[ℂ] F := by
  let J : ComplexModel n →L[ℝ] ComplexModel n :=
    ((Complex.I : ℂ) • ContinuousLinearMap.id ℂ (ComplexModel n)).restrictScalars ℝ
  let A : ComplexModel n →L[ℝ] F := C - Complex.I • C.comp J
  have hI (x : ComplexModel n) : A (Complex.I • x) = Complex.I • A x := by
    simp only [A, J, _root_.sub_apply, _root_.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.id_apply, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg,
      smul_sub, smul_neg]
    abel
  refine
    { toFun := A
      map_add' := A.map_add
      map_smul' := ?_
      cont := A.continuous }
  intro c x
  have hR (t : ℝ) (y : ComplexModel n) : A ((t : ℂ) • y) = (t : ℂ) • A y := by
    change A (algebraMap ℝ ℂ t • y) = algebraMap ℝ ℂ t • A y
    simp only [IsScalarTower.algebraMap_smul, A.map_smul]
  rw [← Complex.re_add_im c]
  simp only [add_smul, mul_smul, A.map_add, hR, hI, RingHom.id_apply]

/-- The complex bilinear part of a real bilinear map (a real Hessian). -/
def hessianComplexBilinear (B : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) :
    ComplexModel n →L[ℂ] ComplexModel n →L[ℂ] ℂ :=
  (1 / 4 : ℂ) • complexLinearProjection
    ((StrongDual.extendRCLikeL (𝕜 := ℂ) (F := ComplexModel n)).toContinuousLinearMap.comp B)

/-- The holomorphic quadratic part `Q(w)` of a real Hessian. -/
def hessianHoloQuadratic (B : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (w : ComplexModel n) : ℂ :=
  hessianComplexBilinear B w w

theorem hessianComplexBilinear_apply (B : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (z w : ComplexModel n) :
    hessianComplexBilinear B z w =
      ((B z w : ℂ) - (B (Complex.I • z) (Complex.I • w) : ℂ) -
        Complex.I * (B z (Complex.I • w) : ℂ) -
        Complex.I * (B (Complex.I • z) w : ℂ)) / 4 := by
  simp only [hessianComplexBilinear, complexLinearProjection,
    _root_.smul_apply, ContinuousLinearMap.coe_mk',
    LinearMap.coe_mk, AddHom.coe_mk, _root_.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    StrongDual.extendRCLikeL_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.id_apply, StrongDual.extendRCLike_apply, smul_eq_mul,
    RCLike.I_to_complex]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem hessianHoloQuadratic_differentiable (B : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) :
    Differentiable ℂ (hessianHoloQuadratic B) :=
  (hessianComplexBilinear B).differentiable.clm_apply differentiable_id

/-- `Re Q(w) + (B(w,w) + B(iw,iw))/4 = B(w,w)/2`. -/
theorem hessianHoloQuadratic_re (B : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (w : ComplexModel n) :
    (hessianHoloQuadratic B w).re + (B w w + B (Complex.I • w) (Complex.I • w)) / 4 =
      B w w / 2 := by
  rw [hessianHoloQuadratic, hessianComplexBilinear_apply]
  simp only [Complex.div_ofNat_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero]
  ring

/-- **The gauge exponent** of `Φ` at `p`: `P(w) = ½(ℓ(w) + Q(w))`, `ℓ` the `ℂ`-linear extension
of `dΦ(p)` and `Q` the holomorphic part of the Hessian of `Φ` at `p`. -/
def gaugeExponent (Φ : ComplexModel n → ℝ) (p : ComplexModel n) (w : ComplexModel n) : ℂ :=
  (StrongDual.extendRCLike (𝕜 := ℂ) (fderiv ℝ Φ p) w +
    hessianHoloQuadratic (fderiv ℝ (fderiv ℝ Φ) p) w) / 2

theorem gaugeExponent_differentiable (Φ : ComplexModel n → ℝ) (p : ComplexModel n) :
    Differentiable ℂ (gaugeExponent Φ p) := by
  have h := ((StrongDual.extendRCLike (𝕜 := ℂ) (fderiv ℝ Φ p)).differentiable.add
    (hessianHoloQuadratic_differentiable (fderiv ℝ (fderiv ℝ Φ) p))).mul_const ((2 : ℂ)⁻¹)
  have he : gaugeExponent Φ p = fun y =>
      (⇑(StrongDual.extendRCLike (𝕜 := ℂ) (fderiv ℝ Φ p)) +
        hessianHoloQuadratic (fderiv ℝ (fderiv ℝ Φ) p)) y * 2⁻¹ := by
    funext w
    simp [gaugeExponent, div_eq_mul_inv]
  rw [he]
  exact h

@[simp] theorem gaugeExponent_zero (Φ : ComplexModel n → ℝ) (p : ComplexModel n) :
    gaugeExponent Φ p 0 = 0 := by
  simp [gaugeExponent, hessianHoloQuadratic]

/-- The second-order Taylor residual `Φ(z) - Φ(p) - dΦ(p)(z-p) - ½ d²Φ(p)(z-p, z-p)`. -/
def taylorResidual (Φ : ComplexModel n → ℝ) (p z : ComplexModel n) : ℝ :=
  Φ z - Φ p - fderiv ℝ Φ p (z - p) - fderiv ℝ (fderiv ℝ Φ) p (z - p) (z - p) / 2

/-- **The gauge identity**: `Φ(z) = Φ(p) + 2 Re P(z - p) + L(z - p) + R(z)`, with `L` the Levi
form of `Φ` at `p` and `R` the Taylor residual. -/
theorem gauge_identity (Φ : ComplexModel n → ℝ) (p z : ComplexModel n) :
    Φ z = Φ p + 2 * (gaugeExponent Φ p (z - p)).re + leviForm Φ p (z - p) +
      taylorResidual Φ p z := by
  have h := hessianHoloQuadratic_re (fderiv ℝ (fderiv ℝ Φ) p) (z - p)
  have hr : (StrongDual.extendRCLike (𝕜 := ℂ) (fderiv ℝ Φ p) (z - p)).re =
      fderiv ℝ Φ p (z - p) := by simp [StrongDual.extendRCLike_apply]
  have hl : leviForm Φ p (z - p) = (fderiv ℝ (fderiv ℝ Φ) p (z - p) (z - p) +
      fderiv ℝ (fderiv ℝ Φ) p (Complex.I • (z - p)) (Complex.I • (z - p))) / 4 := by
    simp only [leviForm, realHessian_eq_fderiv]
  simp only [gaugeExponent, Complex.div_ofNat_re, Complex.add_re, hr, taylorResidual, hl]
  linarith

set_option backward.isDefEq.respectTransparency false in
/-- **Small Taylor residual**: for `Φ` of class `C²` on an open `U ∋ p` and `η > 0`, there is
`r > 0` with `B̄(p, r) ⊆ U` and `|R(z)| ≤ η |z - p|²` on `B̄(p, r)`. -/
theorem exists_taylorResidual_le {U : Set (ComplexModel n)} (hU : IsOpen U)
    {Φ : ComplexModel n → ℝ} (hΦ : ContDiffOn ℝ 2 Φ U) {p : ComplexModel n} (hp : p ∈ U)
    {η : ℝ} (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ closedBall p r ⊆ U ∧
      ∀ z ∈ closedBall p r, |taylorResidual Φ p z| ≤ η * ‖z - p‖ ^ 2 := by
  let B := fderiv ℝ (fderiv ℝ Φ) p
  have hD : ContDiffOn ℝ 1 (fderiv ℝ Φ) U :=
    hΦ.fderiv_of_isOpen hU (by norm_num)
  have hDD : ContinuousAt (fderiv ℝ (fderiv ℝ Φ)) p :=
    (hD.continuousOn_fderiv_of_isOpen hU (by norm_num)).continuousAt (hU.mem_nhds hp)
  have hnorm : ContinuousAt (fun y => ‖fderiv ℝ (fderiv ℝ Φ) y - B‖) p :=
    (show Continuous (fun A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ => ‖A‖) from
      @continuous_norm (ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) inferInstance).continuousAt.comp
        (hDD.sub continuousAt_const)
  have hzero : ‖fderiv ℝ (fderiv ℝ Φ) p - B‖ = 0 := by
    dsimp only [B]
    rw [sub_self]
    exact @norm_zero (ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) inferInstance
  have hbound : ∀ᶠ y in 𝓝 p, ‖fderiv ℝ (fderiv ℝ Φ) y - B‖ < η :=
    hnorm.eventually (gt_mem_nhds (by
      change ‖fderiv ℝ (fderiv ℝ Φ) p - B‖ < η
      rw [hzero]
      exact hη))
  have hnear : ∀ᶠ y in 𝓝 p, y ∈ U ∧ ‖fderiv ℝ (fderiv ℝ Φ) y - B‖ < η := by
    filter_upwards [hU.mem_nhds hp, hbound] with y hy hby
    exact ⟨hy, hby⟩
  obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let r := r₀ / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hb (y : ComplexModel n) (hy : y ∈ closedBall p r) :
      y ∈ U ∧ ‖fderiv ℝ (fderiv ℝ Φ) y - B‖ ≤ η := by
    have hlt : y ∈ ball p r₀ := by
      apply mem_ball.mpr
      apply lt_of_le_of_lt (mem_closedBall.mp hy)
      dsimp [r]
      linarith
    exact ⟨(hball hlt).1, (hball hlt).2.le⟩
  have hd (y : ComplexModel n) (hy : y ∈ U) : DifferentiableAt ℝ Φ y :=
    (hΦ.differentiableOn (by norm_num) y hy).differentiableAt (hU.mem_nhds hy)
  have hdd (y : ComplexModel n) (hy : y ∈ U) : DifferentiableAt ℝ (fderiv ℝ Φ) y :=
    (hD.differentiableOn (by norm_num) y hy).differentiableAt (hU.mem_nhds hy)
  have hsym (v w : ComplexModel n) : B v w = B w v :=
    (hΦ.contDiffAt (hU.mem_nhds hp)).isSymmSndFDerivAt (by norm_num) v w
  have hlin (y : ComplexModel n) (hy : y ∈ closedBall p r) :
      ‖fderiv ℝ Φ y - fderiv ℝ Φ p - B (y - p)‖ ≤ η * ‖y - p‖ :=
    (convex_closedBall p r).norm_image_sub_le_of_norm_fderiv_le'
      (fun w hw => hdd w (hb w hw).1) (fun w hw => (hb w hw).2)
      (mem_closedBall_self hr.le) hy
  let g : ComplexModel n → ℝ := fun y => Φ y - B (y - p) (y - p) / 2
  have hg (y : ComplexModel n) (hy : y ∈ U) :
      HasFDerivAt g (fderiv ℝ Φ y - B (y - p)) y := by
    have hquad : HasFDerivAt (fun w => B (w - p) (w - p) / 2) (B (y - p)) y := by
      let T : ComplexModel n →L[ℝ] ℝ :=
        B.precompR (ComplexModel n) (y - p) (ContinuousLinearMap.id ℝ (ComplexModel n)) +
        B.precompL (ComplexModel n) (ContinuousLinearMap.id ℝ (ComplexModel n)) (y - p)
      have hq : HasFDerivAt (fun w => B (w - p) (w - p)) T y :=
        B.hasFDerivAt_of_bilinear
          ((hasFDerivAt_id y).sub_const p) ((hasFDerivAt_id y).sub_const p)
      have hT : (1 / 2 : ℝ) • T = B (y - p) := by
        ext v
        simp only [T, _root_.smul_apply, _root_.add_apply,
          ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply,
          ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.id_apply, smul_eq_mul]
        rw [hsym]
        ring
      have hh := hq.const_smul (1 / 2 : ℝ)
      rw [hT] at hh
      have hfun : (fun w => B (w - p) (w - p) / 2) =
          (1 / 2 : ℝ) • (fun w => B (w - p) (w - p)) := by
        funext w
        change B (w - p) (w - p) / 2 = (1 / 2 : ℝ) * B (w - p) (w - p)
        ring
      rw [hfun]
      exact hh
    exact (hd y hy).hasFDerivAt.sub hquad
  refine ⟨r, hr, fun z hz => (hb z hz).1, fun z hz => ?_⟩
  have hseg : segment ℝ p z ⊆ closedBall p r :=
    (convex_closedBall p r).segment_subset (mem_closedBall_self hr.le) hz
  have hbound (y : ComplexModel n) (hy : y ∈ segment ℝ p z) :
      ‖fderiv ℝ g y - fderiv ℝ Φ p‖ ≤ η * ‖z - p‖ := by
    rw [(hg y (hb y (hseg hy)).1).fderiv]
    have h := hlin y (hseg hy)
    have heq : fderiv ℝ Φ y - B (y - p) - fderiv ℝ Φ p =
        fderiv ℝ Φ y - fderiv ℝ Φ p - B (y - p) := by abel
    rw [heq]
    exact h.trans (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hy) hη.le)
  have hm := (convex_segment p z).norm_image_sub_le_of_norm_fderiv_le'
    (fun y hy => (hg y (hb y (hseg hy)).1).differentiableAt) hbound
    (left_mem_segment ℝ p z) (right_mem_segment ℝ p z)
  have heq : ∀ z : ComplexModel n, Φ z - B (z - p) (z - p) / 2 - Φ p - fderiv ℝ Φ p (z - p) =
      taylorResidual Φ p z := by
    intro z
    dsimp [taylorResidual, B]
    ring
  simpa only [g, sub_self, map_zero, zero_div, sub_zero, heq,
    Real.norm_eq_abs, taylorResidual, pow_two, mul_assoc,
    sub_sub_sub_comm] using hm

end Gauge

end SGPT.IGood.DXLow
