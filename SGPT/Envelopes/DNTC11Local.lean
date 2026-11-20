import SGPT.Okounkov.TranscendentalWNRegContactLocal
import SGPT.Foundations.Analysis.Pending.SemiconcaveDegenerateHessian
import SGPT.Foundations.Analysis.Pending.PshRepresentative
import SGPT.Foundations.Analysis.Pending.ContinuousThetaPsh
import SGPT.Foundations.Analysis.TestLeviPairing
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

/-!
# Functions with locally bounded distributional complex Hessian (local theory)

Lane S53 (`claude-dnt-c11`).  In a coordinate domain `U ⊆ ℂⁿ`, a continuous function `g` has the
*bounded Hessian density* `h : ℂⁿ → Mat_n(ℂ)` (`IsBoundedHessianDensityOn g h U`) if `h` is a
measurable, pointwise Hermitian, locally essentially bounded matrix function such that, for every
smooth test function `φ` with compact support in `U` and every direction `v`,

  `∫ g · ∂_v∂̄_v φ = ∫ ⟨h v, v⟩ φ`,

i.e. `h` is the `L^∞_loc` density of the distributional complex Hessian `(∂_j∂̄_k g)` of `g`
(`∂_v∂̄_v = leviForm · v`, `⟨h v, v⟩ = hermQuad h v`).  This is the local content of the
`C^{1,1̄}` regularity used by the book (Darvas–Rubinstein's class `C^{1,1̄}` of functions with
bounded Laplacian, intersected with the quasi-psh functions; see `DNTC11Measure` for the global
class and the discussion of the convention).

Main results of this file:

* `hermQuad`, `polarize`, `polarize_hermQuad`, `complexHessian_eq_polarize`: the Hermitian
  quadratic form of a matrix and its polarization; for a `C²` function the complex Hessian is the
  polarization of its Levi form.
* `IsBoundedHessianDensityOn` and its calculus (`add`, `smul`, `of_contDiffOn`, `add_contDiffOn`).
* `leviForm_mollified_eq`, `ae_tendsto_complexHessian_mollified`: the complex Hessians of the
  radial mollifications `g * κ_j` are the mollifications of `h`, hence converge to `h`
  almost everywhere (Lebesgue differentiation, TN's
  `ae_tendsto_translationPairing_explicitRadialKernel`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff ENNReal

namespace SGPT.Envelopes.DNTC11

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.HolomorphicPullback
open SGPT.Okounkov.TranscendentalWNReg

variable {n : ℕ}

/-! ### Hermitian forms of matrices -/

/-- The sesquilinear form `B_A(v, w) = ∑_{p,q} v_p A_{pq} \bar w_q` of a complex matrix. -/
def sesqForm (A : Matrix (Fin n) (Fin n) ℂ) (v w : ComplexModel n) : ℂ :=
  ∑ p, ∑ q, v p * A p q * star (w q)

/-- The real quadratic form `v ↦ Re B_A(v, v)`.  For the complex Hessian of a `C²` function this is
the Levi form `∂_v∂̄_v` (`hermQuad_complexHessian`). -/
def hermQuad (A : Matrix (Fin n) (Fin n) ℂ) (v : ComplexModel n) : ℝ :=
  (sesqForm A v v).re

theorem sesqForm_add_left (A : Matrix (Fin n) (Fin n) ℂ) (v v' w : ComplexModel n) :
    sesqForm A (v + v') w = sesqForm A v w + sesqForm A v' w := by
  simp only [sesqForm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [PiLp.add_apply]
  ring

theorem sesqForm_add_right (A : Matrix (Fin n) (Fin n) ℂ) (v w w' : ComplexModel n) :
    sesqForm A v (w + w') = sesqForm A v w + sesqForm A v w' := by
  simp only [sesqForm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [PiLp.add_apply, star_add]
  ring

theorem sesqForm_neg_left (A : Matrix (Fin n) (Fin n) ℂ) (v w : ComplexModel n) :
    sesqForm A (-v) w = -sesqForm A v w := by
  simp only [sesqForm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [PiLp.neg_apply]
  ring

theorem sesqForm_neg_right (A : Matrix (Fin n) (Fin n) ℂ) (v w : ComplexModel n) :
    sesqForm A v (-w) = -sesqForm A v w := by
  simp only [sesqForm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [PiLp.neg_apply, star_neg]
  ring

theorem sesqForm_swap {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (v w : ComplexModel n) :
    sesqForm A w v = star (sesqForm A v w) := by
  simp only [sesqForm, star_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
  rw [← hA.apply q p]
  simp only [star_mul', star_star]
  ring

theorem sesqForm_single (A : Matrix (Fin n) (Fin n) ℂ) (j k : Fin n) (a b : ℂ) :
    sesqForm A (EuclideanSpace.single j a) (EuclideanSpace.single k b) = a * A j k * star b := by
  classical
  simp only [sesqForm, PiLp.single_apply]
  rw [Finset.sum_eq_single j (fun p _ hp => by simp [hp]) (by simp)]
  rw [Finset.sum_eq_single k (fun q _ hq => by simp [hq]) (by simp)]
  simp

/-- `Q(v + w) - Q(v - w) = 4 Re B(v, w)` for a Hermitian matrix. -/
theorem hermQuad_add_sub {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (v w : ComplexModel n) :
    hermQuad A (v + w) - hermQuad A (v - w) = 4 * (sesqForm A v w).re := by
  have hswap := sesqForm_swap hA v w
  simp only [hermQuad, sub_eq_add_neg, sesqForm_add_left, sesqForm_add_right, sesqForm_neg_left,
    sesqForm_neg_right, Complex.add_re, Complex.neg_re, hswap, Complex.star_def,
    Complex.conj_re]
  ring

/-- The vectors used to polarize a Hermitian form: `e_j ± e_k`, `e_j ± i e_k`. -/
def polVec (j k : Fin n) : Fin 4 → ComplexModel n
  | 0 => coordinateVector j + coordinateVector k
  | 1 => coordinateVector j - coordinateVector k
  | 2 => coordinateVector j + Complex.I • coordinateVector k
  | 3 => coordinateVector j - Complex.I • coordinateVector k

/-- The polarization of a real quadratic form on `ℂⁿ` into a complex matrix. -/
def polarize (Q : ComplexModel n → ℝ) : Matrix (Fin n) (Fin n) ℂ := fun j k =>
  (((Q (polVec j k 0) - Q (polVec j k 1)) / 4 : ℝ) : ℂ) +
    Complex.I * (((Q (polVec j k 2) - Q (polVec j k 3)) / 4 : ℝ) : ℂ)

/-- **Polarization**: a Hermitian matrix is recovered from its quadratic form. -/
theorem polarize_hermQuad {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    polarize (hermQuad A) = A := by
  ext j k
  have h1 := hermQuad_add_sub hA (coordinateVector j) (coordinateVector k)
  have h2 := hermQuad_add_sub hA (coordinateVector j) (Complex.I • coordinateVector k)
  have hs1 : sesqForm A (coordinateVector j) (coordinateVector k) = A j k := by
    simp only [coordinateVector, sesqForm_single, star_one, one_mul, mul_one]
  have hs2 : sesqForm A (coordinateVector j) (Complex.I • coordinateVector k) =
      -Complex.I * A j k := by
    have : Complex.I • (coordinateVector k : ComplexModel n) =
        EuclideanSpace.single k Complex.I := by
      ext i
      simp only [coordinateVector, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
      split_ifs <;> simp
    rw [this]
    simp only [coordinateVector, sesqForm_single, one_mul, Complex.star_def, Complex.conj_I]
    ring
  rw [hs1] at h1
  rw [hs2] at h2
  simp only [polarize, polVec]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, one_mul, sub_zero]
    rw [h1]
    ring
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, zero_mul, one_mul, zero_add]
    rw [h2]
    simp only [Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.neg_im, Complex.I_im]
    ring

/-- For a `C²` function the Hermitian form of the complex Hessian is the Levi form. -/
theorem hermQuad_complexHessian {u : ComplexModel n → ℝ} {z : ComplexModel n}
    (hu : ContDiffAt ℝ 2 u z) (v : ComplexModel n) :
    hermQuad (complexHessian u z) v = leviForm u z v := by
  have h := SemiconcaveHessian.dotProduct_mulVec_complexHessian_eq_leviForm hu
    (fun i => star (v i))
  rw [SemiconcaveHessian.coordCombination_star] at h
  have hs : sesqForm (complexHessian u z) v v =
      star (fun i => star (v i)) ⬝ᵥ (complexHessian u z).mulVec (fun i => star (v i)) := by
    simp only [sesqForm, dotProduct, Matrix.mulVec, Pi.star_apply, star_star, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [hermQuad, hs, h, Complex.ofReal_re]

/-- For a `C²` function the complex Hessian is the polarization of the Levi form. -/
theorem complexHessian_eq_polarize {u : ComplexModel n → ℝ} {z : ComplexModel n}
    (hu : ContDiffAt ℝ 2 u z) : complexHessian u z = polarize (leviForm u z) := by
  conv_lhs => rw [← polarize_hermQuad (complexHessian_isHermitian hu)]
  congr 1
  funext v
  exact hermQuad_complexHessian hu v

/-- Convergence of the four polarization values of quadratic forms gives convergence of the
polarized matrices. -/
theorem tendsto_polarize {ι : Type*} {l : Filter ι} {Q : ι → ComplexModel n → ℝ}
    {Q' : ComplexModel n → ℝ}
    (h : ∀ j k : Fin n, ∀ i : Fin 4, Tendsto (fun m => Q m (polVec j k i)) l (𝓝 (Q' (polVec j k i)))) :
    Tendsto (fun m => polarize (Q m)) l (𝓝 (polarize Q')) := by
  have hc : Continuous (fun r : ℝ => (r : ℂ)) := Complex.continuous_ofReal
  refine tendsto_pi_nhds.mpr fun j => tendsto_pi_nhds.mpr fun k => ?_
  simp only [polarize]
  refine Tendsto.add ((hc.tendsto _).comp (((h j k 0).sub (h j k 1)).div_const 4))
    (Tendsto.const_mul _ ((hc.tendsto _).comp (((h j k 2).sub (h j k 3)).div_const 4)))

/-- `|Q_A(v)| ≤ (∑ ‖A_{pq}‖) ‖v‖²`. -/
theorem abs_hermQuad_le (A : Matrix (Fin n) (Fin n) ℂ) (v : ComplexModel n) :
    |hermQuad A v| ≤ (∑ p, ∑ q, ‖A p q‖) * ‖v‖ ^ 2 := by
  have hv : ∀ p, ‖v p‖ ≤ ‖v‖ := fun p => PiLp.norm_apply_le v p
  calc |hermQuad A v| ≤ ‖sesqForm A v v‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ p, ∑ q, ‖v p * A p q * star (v q)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => norm_sum_le _ _)
    _ ≤ ∑ p, ∑ q, ‖A p q‖ * ‖v‖ ^ 2 := by
        refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => ?_
        rw [norm_mul, norm_mul, norm_star]
        have h1 := hv p
        have h2 := hv q
        have h3 := norm_nonneg (A p q)
        have h4 := mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
        have h5 := mul_le_mul_of_nonneg_left h4 h3
        calc ‖v p‖ * ‖A p q‖ * ‖v q‖ = ‖A p q‖ * (‖v p‖ * ‖v q‖) := by ring
          _ ≤ ‖A p q‖ * (‖v‖ * ‖v‖) := h5
          _ = ‖A p q‖ * ‖v‖ ^ 2 := by ring
    _ = (∑ p, ∑ q, ‖A p q‖) * ‖v‖ ^ 2 := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun p _ => (Finset.sum_mul _ _ _).symm

/-- `|Q_A(v)| ≤ n² C ‖v‖²` when all entries are bounded by `C`. -/
theorem abs_hermQuad_le_of_norm_le {A : Matrix (Fin n) (Fin n) ℂ} {C : ℝ}
    (hA : ∀ p q, ‖A p q‖ ≤ C) (v : ComplexModel n) :
    |hermQuad A v| ≤ (n : ℝ) ^ 2 * C * ‖v‖ ^ 2 := by
  refine (abs_hermQuad_le A v).trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
  calc (∑ p, ∑ q, ‖A p q‖) ≤ ∑ _p : Fin n, ∑ _q : Fin n, C :=
        Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hA p q
    _ = (n : ℝ) ^ 2 * C := by simp [Finset.sum_const, Finset.card_univ]; ring

theorem hermQuad_add (A B : Matrix (Fin n) (Fin n) ℂ) (v : ComplexModel n) :
    hermQuad (A + B) v = hermQuad A v + hermQuad B v := by
  simp only [hermQuad, sesqForm, Matrix.add_apply, ← Complex.add_re, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

theorem hermQuad_smul (c : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) (v : ComplexModel n) :
    hermQuad ((c : ℂ) • A) v = c * hermQuad A v := by
  simp only [hermQuad, sesqForm, Matrix.smul_apply, smul_eq_mul]
  rw [← Complex.re_ofReal_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

theorem hermQuad_one (v : ComplexModel n) : hermQuad (1 : Matrix (Fin n) (Fin n) ℂ) v = ‖v‖ ^ 2 := by
  classical
  simp only [hermQuad, sesqForm, Matrix.one_apply]
  have : ∀ p : Fin n, ∑ q, v p * (if p = q then (1 : ℂ) else 0) * star (v q) =
      v p * star (v p) := by
    intro p
    rw [Finset.sum_eq_single p (fun q _ hq => by simp [Ne.symm hq]) (by simp)]
    simp
  simp only [this, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ =>
    sq_nonneg _)]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem measurable_hermQuad {h : ComplexModel n → Matrix (Fin n) (Fin n) ℂ}
    (hm : ∀ i j, Measurable fun z => h z i j) (v : ComplexModel n) :
    Measurable fun z => hermQuad (h z) v := by
  simp only [hermQuad, sesqForm]
  refine Complex.measurable_re.comp ?_
  refine Finset.measurable_sum _ fun p _ => Finset.measurable_sum _ fun q _ => ?_
  exact (measurable_const.mul (hm p q)).mul measurable_const

instance : MeasurableSpace (Matrix (Fin n) (Fin n) ℂ) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin n → ℂ))

instance : BorelSpace (Matrix (Fin n) (Fin n) ℂ) :=
  inferInstanceAs (BorelSpace (Fin n → Fin n → ℂ))

/-- The normalized Monge–Ampère density `(n!/πⁿ) Re det h(z)` of a matrix-valued function. -/
def hessDensity (h : ComplexModel n → Matrix (Fin n) (Fin n) ℂ) (z : ComplexModel n) : ℝ :=
  (n.factorial : ℝ) / Real.pi ^ n * (h z).det.re

theorem smoothDensity_eq_hessDensity (u : ComplexModel n → ℝ) (z : ComplexModel n) :
    smoothDensity u z = hessDensity (complexHessian u) z := rfl

theorem tendsto_hessDensity {ι : Type*} {l : Filter ι} {H : ι → Matrix (Fin n) (Fin n) ℂ}
    {A : Matrix (Fin n) (Fin n) ℂ} (h : Tendsto H l (𝓝 A)) :
    Tendsto (fun m => (n.factorial : ℝ) / Real.pi ^ n * (H m).det.re) l
      (𝓝 ((n.factorial : ℝ) / Real.pi ^ n * A.det.re)) :=
  tendsto_const_nhds.mul ((Complex.continuous_re.tendsto _).comp
    (((continuous_id.matrix_det).tendsto _).comp h))

theorem measurable_hessDensity {h : ComplexModel n → Matrix (Fin n) (Fin n) ℂ}
    (hm : ∀ i j, Measurable fun z => h z i j) : Measurable (hessDensity h) := by
  have hM : Measurable h := measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => hm i j
  exact measurable_const.mul (Complex.measurable_re.comp
    ((continuous_id.matrix_det).measurable.comp hM))

/-- A bound on the entries bounds the density. -/
theorem abs_hessDensity_le {A : Matrix (Fin n) (Fin n) ℂ} {C : ℝ}
    (hA : ∀ p q, ‖A p q‖ ≤ C) :
    |(n.factorial : ℝ) / Real.pi ^ n * A.det.re| ≤
      (n.factorial : ℝ) / Real.pi ^ n * ((n.factorial : ℝ) * C ^ n) := by
  rw [abs_mul, abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (Complex.abs_re_le_norm _).trans ?_
  have := Matrix.det_le (A := A) (abv := NormedField.toAbsoluteValue ℂ) (x := C) hA
  have h2 : (NormedField.toAbsoluteValue ℂ) A.det ≤ (n.factorial : ℝ) * C ^ n := by
    simpa [Fintype.card_fin, nsmul_eq_mul] using this
  exact h2


theorem norm_coordinateVector (j : Fin n) : ‖(coordinateVector j : ComplexModel n)‖ = 1 := by
  simp [coordinateVector]

theorem norm_polVec_le (j k : Fin n) (i : Fin 4) : ‖polVec j k i‖ ≤ 2 := by
  have hI : ‖Complex.I • (coordinateVector k : ComplexModel n)‖ = 1 := by
    rw [norm_smul, Complex.norm_I, one_mul, norm_coordinateVector]
  fin_cases i <;> simp only [polVec]
  · exact (norm_add_le _ _).trans (by rw [norm_coordinateVector, norm_coordinateVector]; norm_num)
  · exact (norm_sub_le _ _).trans (by rw [norm_coordinateVector, norm_coordinateVector]; norm_num)
  · exact (norm_add_le _ _).trans (by rw [norm_coordinateVector, hI]; norm_num)
  · exact (norm_sub_le _ _).trans (by rw [norm_coordinateVector, hI]; norm_num)

/-- A uniform bound on a quadratic form bounds the entries of its polarization. -/
theorem norm_polarize_le {Q : ComplexModel n → ℝ} {C : ℝ} (hQ : ∀ v, |Q v| ≤ C * ‖v‖ ^ 2)
    (j k : Fin n) : ‖polarize Q j k‖ ≤ 4 * C := by
  have hb : ∀ i, |Q (polVec j k i)| ≤ 4 * C := fun i => by
    refine (hQ _).trans ?_
    have h0 : 0 ≤ C := by
      have := (abs_nonneg _).trans (hQ (coordinateVector j))
      rwa [norm_coordinateVector, one_pow, mul_one] at this
    have := norm_polVec_le j k i
    have h2 : ‖polVec j k i‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (polVec j k i)]
    nlinarith [mul_le_mul_of_nonneg_left h2 h0]
  simp only [polarize]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_div, abs_div]
  have e1 := abs_sub _ _ |>.trans (add_le_add (hb 0) (hb 1))
  have e2 := abs_sub _ _ |>.trans (add_le_add (hb 2) (hb 3))
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  linarith

/-! ### Bounded complex Hessian densities -/

/-- **Bounded complex Hessian density.**  On the open set `U ⊆ ℂⁿ`, the continuous function `g` has
the measurable, pointwise Hermitian, locally essentially bounded matrix function `h` as the density
of its distributional complex Hessian: `∫ g ∂_v∂̄_v φ = ∫ ⟨h v, v⟩ φ` for all smooth `φ` with
compact support in `U` and all `v`.  (`L^∞_loc` complex Hessian, the local form of `C^{1,1̄}`
regularity of a quasi-psh function.) -/
structure IsBoundedHessianDensityOn (g : ComplexModel n → ℝ)
    (h : ComplexModel n → Matrix (Fin n) (Fin n) ℂ) (U : Set (ComplexModel n)) : Prop where
  isOpen : IsOpen U
  continuousOn : ContinuousOn g U
  isHermitian : ∀ z, (h z).IsHermitian
  measurable : ∀ i j, Measurable fun z => h z i j
  bounded : ∀ K, IsCompact K → K ⊆ U → ∃ C, ∀ᵐ z ∂(volume.restrict K), ∀ i j, ‖h z i j‖ ≤ C
  levi : ∀ φ : ComplexModel n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    ∀ v, ∫ z, g z * leviForm φ z v = ∫ z, hermQuad (h z) v * φ z

namespace IsBoundedHessianDensityOn

variable {g g' : ComplexModel n → ℝ} {h h' : ComplexModel n → Matrix (Fin n) (Fin n) ℂ}
  {U : Set (ComplexModel n)}

theorem mono (hg : IsBoundedHessianDensityOn g h U) {V : Set (ComplexModel n)} (hV : IsOpen V)
    (hVU : V ⊆ U) : IsBoundedHessianDensityOn g h V where
  isOpen := hV
  continuousOn := hg.continuousOn.mono hVU
  isHermitian := hg.isHermitian
  measurable := hg.measurable
  bounded K hK hKV := hg.bounded K hK (hKV.trans hVU)
  levi φ hφ hφc hφV := hg.levi φ hφ hφc (hφV.trans hVU)

/-- The quadratic forms of a bounded density are essentially bounded on compact subsets. -/
theorem exists_ae_abs_hermQuad_le (hg : IsBoundedHessianDensityOn g h U) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C, 0 ≤ C ∧ ∀ᵐ z ∂(volume.restrict K), ∀ v, |hermQuad (h z) v| ≤ C * ‖v‖ ^ 2 := by
  obtain ⟨C, hC⟩ := hg.bounded K hK hKU
  refine ⟨(n : ℝ) ^ 2 * max C 0, by positivity, ?_⟩
  filter_upwards [hC] with z hz v
  exact abs_hermQuad_le_of_norm_le (fun p q => (hz p q).trans (le_max_left _ _)) v

theorem integrableOn_hermQuad (hg : IsBoundedHessianDensityOn g h U) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKU : K ⊆ U) (v : ComplexModel n) :
    IntegrableOn (fun z => hermQuad (h z) v) K := by
  obtain ⟨C, -, hC⟩ := hg.exists_ae_abs_hermQuad_le hK hKU
  refine Measure.integrableOn_of_bounded hK.measure_lt_top.ne
    (measurable_hermQuad hg.measurable v).aestronglyMeasurable (M := C * ‖v‖ ^ 2) ?_
  filter_upwards [hC] with z hz
  rw [Real.norm_eq_abs]
  exact hz v

/-- Products with a compactly supported continuous function are integrable. -/
theorem integrable_hermQuad_mul (hg : IsBoundedHessianDensityOn g h U) {φ : ComplexModel n → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) (v : ComplexModel n) :
    Integrable (fun z => hermQuad (h z) v * φ z) := by
  have hK : IsCompact (tsupport φ) := hφc
  have h1 : IntegrableOn (fun z => hermQuad (h z) v * φ z) (tsupport φ) := by
    obtain ⟨B, hB⟩ := hφc.exists_bound_of_continuous hφ
    exact (hg.integrableOn_hermQuad hK hφU v).mul_continuousOn hφ.continuousOn hK
  have heq : (fun z => hermQuad (h z) v * φ z) =
      (tsupport φ).indicator (fun z => hermQuad (h z) v * φ z) := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · rw [indicator_of_mem hz]
    · rw [indicator_of_notMem hz, image_eq_zero_of_notMem_tsupport hz, mul_zero]
  rw [heq]
  exact h1.integrable_indicator (isClosed_tsupport φ).measurableSet

theorem integrable_mul_leviForm (hg : IsBoundedHessianDensityOn g h U) {φ : ComplexModel n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) (v : ComplexModel n) :
    Integrable (fun z => g z * leviForm φ z v) := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hsub : Function.support (fun x => leviForm φ x v) ⊆ tsupport φ := by
    intro x hx
    by_contra hxt
    apply hx
    simp only [leviForm, ContactLocal.realHessian_eq_zero_of_notMem_tsupport hxt, add_zero,
      zero_div]
  have hcs : HasCompactSupport (fun x => leviForm φ x v) := hφc.mono' hsub
  have hts : tsupport (fun x => leviForm φ x v) ⊆ U :=
    (closure_minimal hsub (isClosed_tsupport φ)).trans hφU
  exact integrable_mul_of_continuousOn hg.isOpen hg.continuousOn (continuous_leviForm hφ2 v) hcs hts

theorem add (hg : IsBoundedHessianDensityOn g h U) (hg' : IsBoundedHessianDensityOn g' h' U) :
    IsBoundedHessianDensityOn (fun z => g z + g' z) (fun z => h z + h' z) U where
  isOpen := hg.isOpen
  continuousOn := hg.continuousOn.add hg'.continuousOn
  isHermitian z := (hg.isHermitian z).add (hg'.isHermitian z)
  measurable i j := by
    show Measurable fun z => h z i j + h' z i j
    exact (hg.measurable i j).add (hg'.measurable i j)
  bounded K hK hKU := by
    obtain ⟨C, hC⟩ := hg.bounded K hK hKU
    obtain ⟨C', hC'⟩ := hg'.bounded K hK hKU
    refine ⟨C + C', ?_⟩
    filter_upwards [hC, hC'] with z hz hz' i j
    rw [Matrix.add_apply]
    exact (norm_add_le _ _).trans (add_le_add (hz i j) (hz' i j))
  levi φ hφ hφc hφU v := by
    simp only [add_mul, hermQuad_add]
    rw [integral_add (hg.integrable_mul_leviForm hφ hφc hφU v)
        (hg'.integrable_mul_leviForm hφ hφc hφU v),
      integral_add (hg.integrable_hermQuad_mul hφ.continuous hφc hφU v)
        (hg'.integrable_hermQuad_mul hφ.continuous hφc hφU v),
      hg.levi φ hφ hφc hφU v, hg'.levi φ hφ hφc hφU v]

theorem smul (hg : IsBoundedHessianDensityOn g h U) (c : ℝ) :
    IsBoundedHessianDensityOn (fun z => c * g z) (fun z => (c : ℂ) • h z) U where
  isOpen := hg.isOpen
  continuousOn := continuousOn_const.mul hg.continuousOn
  isHermitian z := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, (hg.isHermitian z).eq, Complex.star_def, Complex.conj_ofReal]
  measurable i j := by
    show Measurable fun z => (c : ℂ) * h z i j
    exact measurable_const.mul (hg.measurable i j)
  bounded K hK hKU := by
    obtain ⟨C, hC⟩ := hg.bounded K hK hKU
    refine ⟨|c| * C, ?_⟩
    filter_upwards [hC] with z hz i j
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hz i j) (abs_nonneg c)
  levi φ hφ hφc hφU v := by
    simp only [hermQuad_smul, mul_assoc]
    rw [integral_const_mul, integral_const_mul, hg.levi φ hφ hφc hφU v]

end IsBoundedHessianDensityOn

/-- The complex Hessian of a function smooth on `U`, extended by `0`. -/
def smoothHess (U : Set (ComplexModel n)) (ρ : ComplexModel n → ℝ) (z : ComplexModel n) :
    Matrix (Fin n) (Fin n) ℂ := by
  classical
  exact if z ∈ U then complexHessian ρ z else 0

theorem continuousOn_complexHessian_apply {ρ : ComplexModel n → ℝ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ U) (i j : Fin n) :
    ContinuousOn (fun z => complexHessian ρ z i j) U := by
  have h2 : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ ρ)) U :=
    (hρ.fderiv_of_isOpen (m := ∞) hU (by simp)).fderiv_of_isOpen hU (by simp)
  have hH : ∀ a b, ContinuousOn (fun z => realHessian ρ z a b) U := by
    intro a b
    simp only [realHessian_eq_fderiv]
    exact (h2.continuousOn.clm_apply continuousOn_const).clm_apply continuousOn_const
  have hc : Continuous (fun r : ℝ => (r : ℂ)) := Complex.continuous_ofReal
  simp only [complexHessian]
  exact ((hc.comp_continuousOn ((hH _ _).add (hH _ _))).div_const _).add
    ((continuousOn_const.mul (hc.comp_continuousOn ((hH _ _).sub (hH _ _)))).div_const _)

/-- **Smooth functions have bounded Hessian densities**: their classical complex Hessian. -/
theorem isBoundedHessianDensityOn_of_contDiffOn {ρ : ComplexModel n → ℝ}
    {U : Set (ComplexModel n)} (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ U) :
    IsBoundedHessianDensityOn ρ (smoothHess U ρ) U where
  isOpen := hU
  continuousOn := hρ.continuousOn
  isHermitian z := by
    classical
    unfold smoothHess
    split_ifs with hz
    · exact complexHessian_isHermitian (((hρ z hz).contDiffAt (hU.mem_nhds hz)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    · exact Matrix.isHermitian_zero
  measurable i j := by
    classical
    have h := (continuousOn_complexHessian_apply hU hρ i j).measurable_piecewise
      (continuousOn_const (c := (0 : ℂ))) hU.measurableSet
    convert h using 1
    funext z
    by_cases hz : z ∈ U <;> simp [smoothHess, Set.piecewise, hz]
  bounded K hK hKU := by
    classical
    have : ∀ i j, ∃ C, ∀ z ∈ K, ‖complexHessian ρ z i j‖ ≤ C := fun i j =>
      hK.exists_bound_of_continuousOn ((continuousOn_complexHessian_apply hU hρ i j).mono hKU)
    choose C hC using this
    refine ⟨∑ i, ∑ j, |C i j|, ?_⟩
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz i j
    have hzU : z ∈ U := hKU hz
    simp only [smoothHess, hzU, if_true]
    refine (hC i j z hz).trans ((le_abs_self _).trans ?_)
    exact (Finset.single_le_sum (f := fun j => |C i j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, |C i j|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  levi φ hφ hφc hφU v := by
    classical
    rw [integral_mul_leviForm_eq hU hρ hφ hφc hφU v]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ U
    · simp only [smoothHess, hz, if_true]
      rw [hermQuad_complexHessian (((hρ z hz).contDiffAt (hU.mem_nhds hz)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
    · have : φ z = 0 := image_eq_zero_of_notMem_tsupport fun h' => hz (hφU h')
      simp [this]

theorem IsBoundedHessianDensityOn.add_contDiffOn {g ρ : ComplexModel n → ℝ}
    {h : ComplexModel n → Matrix (Fin n) (Fin n) ℂ} {U : Set (ComplexModel n)}
    (hg : IsBoundedHessianDensityOn g h U) (hρ : ContDiffOn ℝ ∞ ρ U) :
    IsBoundedHessianDensityOn (fun z => g z + ρ z) (fun z => h z + smoothHess U ρ z) U :=
  hg.add (isBoundedHessianDensityOn_of_contDiffOn hg.isOpen hρ)


/-! ### Radial mollifications -/

section Mollifier

variable {Ω : Opens (ComplexModel n)} {g : ComplexModel n → ℝ}
  {h : ComplexModel n → Matrix (Fin n) (Fin n) ℂ} {x₀ : ComplexModel n} {R : ℝ}

open ContactLocal in
theorem locallyIntegrable_indicator_closedBall (hg : ContinuousOn g Ω) (hR : 0 < R)
    (hball : closedBall x₀ (4 * R) ⊆ Ω) :
    LocallyIntegrable ((closedBall x₀ (3 * R)).indicator g) volume := by
  have hK : closedBall x₀ (3 * R) ⊆ Ω := (closedBall_subset_closedBall (by linarith)).trans hball
  exact (((hg.mono hK).integrableOn_compact (isCompact_closedBall _ _)).integrable_indicator
    measurableSet_closedBall).locallyIntegrable

open ContactLocal in
theorem contDiff_mollified_of_continuousOn (hg : ContinuousOn g Ω) (hR : 0 < R)
    (hball : closedBall x₀ (4 * R) ⊆ Ω) (j : ℕ) : ContDiff ℝ ∞ (mollified g x₀ R hR j) :=
  contDiff_translationPairing (locallyIntegrable_indicator_closedBall hg hR hball)
    (explicitRadialKernel_hasCompactSupport R hR j) (explicitRadialKernel_contDiff R hR j)

theorem dist_lt_of_notMem_closedBall {z x : ComplexModel n} (hz : z ∈ ball x₀ (2 * R))
    (hx : x ∉ closedBall x₀ (3 * R)) (j : ℕ) : R / ((j : ℝ) + 1) < dist x z := by
  rw [mem_ball] at hz
  rw [mem_closedBall, not_le] at hx
  have h1 : R / ((j : ℝ) + 1) ≤ R := by
    have hR : 0 ≤ R := by
      have := dist_nonneg (x := z) (y := x₀)
      linarith
    exact div_le_self hR (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
  have h2 := dist_triangle x z x₀
  linarith

open ContactLocal in
/-- **The Levi forms of the mollifications are the mollified Levi densities.** -/
theorem leviForm_mollified_eq (hg : IsBoundedHessianDensityOn g h Ω) (hR : 0 < R)
    (hball : closedBall x₀ (4 * R) ⊆ Ω) {z : ComplexModel n} (hz : z ∈ ball x₀ (2 * R)) (j : ℕ)
    (v : ComplexModel n) :
    leviForm (mollified g x₀ R hR j) z v =
      ∫ x, hermQuad (h x) v * explicitRadialKernel R hR j (x - z) := by
  set K := closedBall x₀ (3 * R) with hKdef
  have hKΩ : K ⊆ Ω := (closedBall_subset_closedBall (by linarith)).trans hball
  have hloc := locallyIntegrable_indicator_closedBall hg.continuousOn hR hball
  rw [mollified, leviForm_translationPairing hloc (explicitRadialKernel_hasCompactSupport R hR j)
    (explicitRadialKernel_contDiff_two R hR j)]
  have hzK : closedBall z R ⊆ K := closedBall_subset_of_mem_innerBall hz
  have hφ : ContDiff ℝ ∞ (fun x => explicitRadialKernel (n := n) R hR j (x - z)) :=
    (explicitRadialKernel_contDiff R hR j).comp (contDiff_id.sub contDiff_const)
  have hφc : HasCompactSupport (fun x => explicitRadialKernel (n := n) R hR j (x - z)) :=
    (explicitRadialKernel_hasCompactSupport R hR j).comp_homeomorph (Homeomorph.subRight z)
  have hφK : tsupport (fun x => explicitRadialKernel (n := n) R hR j (x - z)) ⊆ K :=
    (tsupport_explicitRadialKernel_translate_subset R hR j z).trans
      ((closedBall_subset_closedBall (shrinkingBump_rOut_le (E := ComplexModel n) R hR j)).trans hzK)
  rw [← hg.levi _ hφ hφc (hφK.trans hKΩ) v]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [SGPT.Okounkov.TranscendentalWN.EnvelopeLocal.leviForm_comp_sub]
  by_cases hx : x ∈ K
  · rw [indicator_of_mem hx]
  · have hxr := dist_lt_of_notMem_closedBall hz hx j
    have h0 : leviForm (explicitRadialKernel (n := n) R hR j) (x - z) v = 0 := by
      simp only [leviForm, realHessian_explicitRadialKernel_sub_eq_zero R hR j hxr, add_zero,
        zero_div]
    rw [indicator_of_notMem hx, h0, mul_zero, mul_zero]

open ContactLocal in
theorem integral_hermQuad_mul_kernel_eq (hR : 0 < R) {z : ComplexModel n}
    (hz : z ∈ ball x₀ (2 * R)) (j : ℕ) (F : ComplexModel n → ℝ) :
    ∫ x, F x * explicitRadialKernel R hR j (x - z) =
      translationPairing volume ((closedBall x₀ (3 * R)).indicator F)
        (explicitRadialKernel R hR j) z := by
  simp only [translationPairing]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ closedBall x₀ (3 * R)
  · simp only [indicator_of_mem hx]
  · simp only [indicator_of_notMem hx,
      explicitRadialKernel_sub_eq_zero R hR j (dist_lt_of_notMem_closedBall hz hx j), mul_zero]

open ContactLocal in
/-- **Almost everywhere convergence of the mollified Levi forms** (Lebesgue differentiation). -/
theorem ae_tendsto_leviForm_mollified (hg : IsBoundedHessianDensityOn g h Ω) (hR : 0 < R)
    (hball : closedBall x₀ (4 * R) ⊆ Ω) (v : ComplexModel n) :
    ∀ᵐ z, z ∈ ball x₀ (2 * R) →
      Tendsto (fun j => leviForm (mollified g x₀ R hR j) z v) atTop (𝓝 (hermQuad (h z) v)) := by
  set K := closedBall x₀ (3 * R) with hKdef
  have hKΩ : K ⊆ Ω := (closedBall_subset_closedBall (by linarith)).trans hball
  have hint : LocallyIntegrable (K.indicator fun x => hermQuad (h x) v) volume :=
    ((hg.integrableOn_hermQuad (isCompact_closedBall _ _) hKΩ v).integrable_indicator
      measurableSet_closedBall).locallyIntegrable
  filter_upwards [ae_tendsto_translationPairing_explicitRadialKernel hint R hR] with z hz hz2
  have hzK : z ∈ K := ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)) hz2
  rw [indicator_of_mem hzK] at hz
  refine hz.congr' (Eventually.of_forall fun j => ?_)
  show _ = leviForm (mollified g x₀ R hR j) z v
  rw [leviForm_mollified_eq hg hR hball hz2 j v, integral_hermQuad_mul_kernel_eq hR hz2 j]

open ContactLocal in
/-- **Almost everywhere convergence of the mollified complex Hessians.** -/
theorem ae_tendsto_complexHessian_mollified (hg : IsBoundedHessianDensityOn g h Ω) (hR : 0 < R)
    (hball : closedBall x₀ (4 * R) ⊆ Ω) :
    ∀ᵐ z, z ∈ ball x₀ (2 * R) →
      Tendsto (fun j => complexHessian (mollified g x₀ R hR j) z) atTop (𝓝 (h z)) := by
  have hall : ∀ᵐ z, ∀ t : Fin n × Fin n × Fin 4, z ∈ ball x₀ (2 * R) →
      Tendsto (fun j => leviForm (mollified g x₀ R hR j) z (polVec t.1 t.2.1 t.2.2)) atTop
        (𝓝 (hermQuad (h z) (polVec t.1 t.2.1 t.2.2))) :=
    ae_all_iff.mpr fun t => ae_tendsto_leviForm_mollified hg hR hball _
  filter_upwards [hall] with z hz hz2
  have hfun : (fun j => complexHessian (mollified g x₀ R hR j) z) =
      fun j => polarize (leviForm (mollified g x₀ R hR j) z) := by
    funext j
    exact complexHessian_eq_polarize
      ((contDiff_mollified_of_continuousOn hg.continuousOn hR hball j).contDiffAt.of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  rw [hfun, ← polarize_hermQuad (hg.isHermitian z)]
  exact tendsto_polarize fun a b i => hz ⟨a, b, i⟩ hz2

theorem ae_tendsto_smoothDensity_mollified_of_density (hg : IsBoundedHessianDensityOn g h Ω)
    (hR : 0 < R) (hball : closedBall x₀ (4 * R) ⊆ Ω) :
    ∀ᵐ z, z ∈ ball x₀ (2 * R) →
      Tendsto (fun j => smoothDensity (ContactLocal.mollified g x₀ R hR j) z) atTop
        (𝓝 (hessDensity h z)) := by
  filter_upwards [ae_tendsto_complexHessian_mollified hg hR hball] with z hz hz2
  exact tendsto_hessDensity (hz hz2)

open ContactLocal in
/-- A uniform bound for the Levi forms of the mollifications. -/
theorem exists_abs_leviForm_mollified_le (hg : IsBoundedHessianDensityOn g h Ω) (hR : 0 < R)
    (hball : closedBall x₀ (4 * R) ⊆ Ω) :
    ∃ C, 0 ≤ C ∧ ∀ j, ∀ z ∈ ball x₀ (2 * R), ∀ v,
      |leviForm (mollified g x₀ R hR j) z v| ≤ C * ‖v‖ ^ 2 := by
  set K := closedBall x₀ (3 * R) with hKdef
  have hKΩ : K ⊆ Ω := (closedBall_subset_closedBall (by linarith)).trans hball
  obtain ⟨C, hC0, hC⟩ := hg.exists_ae_abs_hermQuad_le (isCompact_closedBall x₀ (3 * R)) hKΩ
  have hC' : ∀ᵐ x, x ∈ K → ∀ v, |hermQuad (h x) v| ≤ C * ‖v‖ ^ 2 :=
    (ae_restrict_iff' measurableSet_closedBall).mp hC
  refine ⟨C, hC0, fun j z hz v => ?_⟩
  rw [leviForm_mollified_eq hg hR hball hz j v]
  have hκc : Continuous fun x => explicitRadialKernel (n := n) R hR j (x - z) :=
    (explicitRadialKernel_contDiff R hR j).continuous.comp (continuous_id.sub continuous_const)
  have hκs : HasCompactSupport fun x => explicitRadialKernel (n := n) R hR j (x - z) :=
    (explicitRadialKernel_hasCompactSupport R hR j).comp_homeomorph (Homeomorph.subRight z)
  have hbound : ∀ᵐ x, ‖hermQuad (h x) v * explicitRadialKernel R hR j (x - z)‖ ≤
      C * ‖v‖ ^ 2 * explicitRadialKernel R hR j (x - z) := by
    filter_upwards [hC'] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (explicitRadialKernel_nonneg R hR j _)]
    by_cases hxK : x ∈ K
    · exact mul_le_mul_of_nonneg_right (hx hxK v) (explicitRadialKernel_nonneg R hR j _)
    · rw [explicitRadialKernel_sub_eq_zero R hR j (dist_lt_of_notMem_closedBall hz hxK j)]
      simp
  calc |∫ x, hermQuad (h x) v * explicitRadialKernel R hR j (x - z)|
      = ‖∫ x, hermQuad (h x) v * explicitRadialKernel R hR j (x - z)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x, C * ‖v‖ ^ 2 * explicitRadialKernel R hR j (x - z) :=
        norm_integral_le_of_norm_le ((hκc.integrable_of_hasCompactSupport hκs).const_mul _) hbound
    _ = C * ‖v‖ ^ 2 := by rw [integral_const_mul, integral_explicitRadialKernel_sub, mul_one]

/-- A uniform bound for the entries of the complex Hessians of the mollifications. -/
theorem exists_norm_complexHessian_mollified_le (hg : IsBoundedHessianDensityOn g h Ω)
    (hR : 0 < R) (hball : closedBall x₀ (4 * R) ⊆ Ω) :
    ∃ C, 0 ≤ C ∧ ∀ j, ∀ z ∈ ball x₀ (2 * R), ∀ p q,
      ‖complexHessian (ContactLocal.mollified g x₀ R hR j) z p q‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_leviForm_mollified_le hg hR hball
  refine ⟨4 * C, by positivity, fun j z hz p q => ?_⟩
  rw [complexHessian_eq_polarize
    ((contDiff_mollified_of_continuousOn hg.continuousOn hR hball j).contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
  exact norm_polarize_le (hC j z hz) p q

end Mollifier

/-! ### Plurisubharmonicity from a semipositive density -/

/-- **A continuous function whose Hessian density is semipositive is plurisubharmonic.**  The
regular distribution of `g` has nonnegative distributional Levi form, hence a psh representative
(Demailly I.5.8, TN `exists_pshRepresentative`), which equals `g` everywhere because `g` is
continuous. -/
theorem plurisubharmonicOn_of_hermQuad_nonneg {g : ComplexModel n → ℝ}
    {h : ComplexModel n → Matrix (Fin n) (Fin n) ℂ} {U : Set (ComplexModel n)}
    (hg : IsBoundedHessianDensityOn g h U)
    (hpos : ∀ v, ∀ᵐ z ∂(volume.restrict U), 0 ≤ hermQuad (h z) v) :
    PlurisubharmonicOn (fun z => (g z : EReal)) U := by
  let Ω : Opens (ComplexModel n) := ⟨U, hg.isOpen⟩
  have hloc : LocallyIntegrableOn g (Ω : Set (ComplexModel n)) volume :=
    hg.continuousOn.locallyIntegrableOn hg.isOpen.measurableSet
  have hT : HasNonnegativeDistributionalLevi (regularDistribution volume g hloc) := by
    intro v φ hφ
    rw [distributionalLeviCLM_regularDistribution_apply hloc φ v,
      hg.levi φ φ.contDiff φ.hasCompactSupport φ.tsupport_subset v]
    refine integral_nonneg_of_ae ?_
    have h1 := (ae_restrict_iff' hg.isOpen.measurableSet).mp (hpos v)
    filter_upwards [h1] with z hz
    by_cases hzU : z ∈ U
    · exact mul_nonneg (hz hzU) (hφ z)
    · have h0 : φ z = 0 := image_eq_zero_of_notMem_tsupport (fun h' => hzU (φ.tsupport_subset h'))
      simp [h0]
  obtain ⟨u, huP, huF, huL, huT⟩ := Pending.exists_pshRepresentative volume hT
  have hae := ae_eq_of_regularDistribution_eq volume hloc huL huT
  have hae' : ∀ᵐ y ∂volume.restrict U, u y = (g y : EReal) := by
    filter_upwards [hae, huF] with y hy hyF
    rw [← EReal.coe_toReal hyF.1 hyF.2, hy]
  have hgc : ContinuousOn (fun y => (g y : EReal)) U :=
    continuous_coe_real_ereal.comp_continuousOn hg.continuousOn
  have hle1 := huP.le_of_ae_le hg.isOpen hgc.upperSemicontinuousOn volume
    (hae'.mono fun _ hy => hy.le)
  have hle2 := Pending.ContinuousThetaPsh.le_of_ae_le_of_semicontinuousOn hg.isOpen
    huP.upperSemicontinuousOn hgc.lowerSemicontinuousOn (hae'.mono fun _ hy => hy.ge)
  intro y hy
  refine (huP y hy).congr ?_
  filter_upwards [hg.isOpen.mem_nhds hy] with x hx
  exact le_antisymm (hle1 x hx) (hle2 x hx)

end SGPT.Envelopes.DNTC11
