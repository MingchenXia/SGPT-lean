import SGPT.Hodge.Trace
import SGPT.Hodge.SourceSmoothMixedCohomology
import SGPT.NPP.LogConcavityMixedDiscriminant
import SGPT.Foundations.Analysis.Pending.ConcentrationEigenvalueBound
import SGPT.Foundations.Analysis.Pending.ConcentrationMassComparison
import SGPT.Foundations.Analysis.Pending.OneOneFormMixedTrace
import SGPT.Foundations.Analysis.Pending.LocalCurrentDensityMatrix
import SGPT.Foundations.Analysis.Pending.KahlerLaplacianStokes

/-!
# The Hodge index theorem for real `(1,1)`-classes

Lane NUMEQ, blueprint `claude-numeq.tex`.  Infrastructure for `prop:Okounonlydepnum` (numerical
equivalence of line bundles) and for open clause (1) of `rmk:bdiv:L749` (Dang–Favre's numerical
space `N¹(Y)_ℝ` versus its image `NS(Y)_ℝ ⊆ H^{1,1}(Y, ℝ)`): the cohomological half of
"numerically trivial ⇒ `c₁ = 0`" is the Hodge index theorem for `(1,1)`-classes.

Let `(X, ω)` be a compact connected Kähler manifold of dimension `n = m + 2 ≥ 2` and write
`α · β · {ω}^{n-2}`, `α · {ω}^{n-1}` for the intersection numbers of real Bott–Chern classes,
computed by the slot integrals `∫_X θ₀ ∧ ⋯ ∧ θ_{n-1}` of representatives (TN `slotIntegral`; they
only depend on the classes, `slotIntegral_eq_of_bottChernRel`).

* `re_mixedCoefficient_twoSlot` (pointwise, matrices): for `A` positive definite and `B`
  Hermitian with `Re C(B, A, …, A) = 0` (`B` is `A`-trace free), `Re C(B, B, A, …, A) ≤ 0`, with
  equality only for `B = 0` (`C` = mixed discriminant).
* **`hodgeIndex`, `slotIntegral_twoSlot_nonpos`,
  `ofRepresentative_eq_zero_of_slotIntegral_twoSlot_eq_zero` (Hodge index theorem)**: if `α · {ω}^{n-1} = 0` then `α² · {ω}^{n-2} ≤ 0`, and
  `α² · {ω}^{n-2} = 0` iff `α = 0`.
* **`ofRepresentative_eq_zero_of_nef_of_slotIntegral_oneSlot_eq_zero`**: a nef class `α` with
  `α · {ω}^{n-1} = 0` vanishes.
* **`eq_zero_of_classNef_of_classNef_neg`**: if `α` and `-α` are both nef then `α = 0`.

*Proof.*  Replace `θ` by the constant-trace (harmonic) representative `γ` of its class
(`SGPT.Hodge.exists_constantTrace_bottChernRel`).  Pointwise `γ ∧ ω^{n-1} = (tr_ω γ / n) ωⁿ`, so
`α · {ω}^{n-1} = 0` forces `tr_ω γ ≡ 0`.  For a trace-free `γ`, after a congruence making
`H_ω = 1` and `H_γ = diag(d)` (`∑ d = 0`), the density of `γ² ∧ ω^{n-2}` is a positive multiple
of `∑_σ d(σ 0) d(σ 1) = -(n-2)! ∑ d_k²` (`sum_perm_mul_eq_neg`), hence `≤ 0` and `= 0` only where
`γ = 0`.  Integrating against the Kähler volume (which charges every open set) gives the
theorem.  Nef classes have `α² · {ω}^{n-2} ≥ 0` (TN `slotIntegral_nonneg_of_nef`).
-/

set_option autoImplicit false

noncomputable section

open Matrix Set Filter MeasureTheory
open scoped ComplexOrder

namespace SGPT.Projective.NumEq

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere

/-! ### Matrix algebra -/

section Matrix

variable {n : ℕ}

/-- **Diagonalization of a Hermitian matrix relative to a positive definite one**: for `B`
positive definite and `A` Hermitian there is an invertible `R` with `R^* B R = 1` and
`R^* A R = diag(λ)`, `λ` real. -/
theorem exists_conj_eq_one_and_diagonal {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (hB : B.PosDef) :
    ∃ R : Matrix (Fin n) (Fin n) ℂ, R.det ≠ 0 ∧ star R * B * R = 1 ∧
      ∃ lam : Fin n → ℝ, star R * A * R = diagonal (fun k => (lam k : ℂ)) := by
  classical
  set U := hB.1.eigenvectorUnitary
  set μ := hB.1.eigenvalues
  have hμ : ∀ k, 0 < μ k := hB.eigenvalues_pos
  have hUB : star (U : Matrix (Fin n) (Fin n) ℂ) * B * U = diagonal (fun k => (μ k : ℂ)) := by
    have := hB.1.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Function.comp_def] using this
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal fun k => ((Real.sqrt (μ k))⁻¹ : ℂ)
  have hDstar : star D = D := by
    simp only [D, star_eq_conjTranspose, diagonal_conjTranspose]
    congr 1
    funext k
    simp [Complex.conj_ofReal]
  set R1 := (U : Matrix (Fin n) (Fin n) ℂ) * D
  have hR1B : star R1 * B * R1 = 1 := by
    simp only [R1, star_mul, hDstar]
    have : D * star (U : Matrix (Fin n) (Fin n) ℂ) * B * ((U : Matrix (Fin n) (Fin n) ℂ) * D) =
        D * (star (U : Matrix (Fin n) (Fin n) ℂ) * B * U) * D := by
      simp only [Matrix.mul_assoc]
    rw [this, hUB]
    simp only [D, diagonal_mul_diagonal]
    rw [← diagonal_one]
    congr 1
    funext k
    have hs : (Real.sqrt (μ k) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (hμ k)).ne'
    have hsq : ((Real.sqrt (μ k) : ℂ)) * (Real.sqrt (μ k) : ℂ) = (μ k : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hμ k).le]
    field_simp
    rw [← hsq]
    ring
  have hdetU : (U : Matrix (Fin n) (Fin n) ℂ).det ≠ 0 := by
    have h := Matrix.UnitaryGroup.star_mul_self U
    intro h0
    have := congrArg Matrix.det h
    rw [det_mul, h0, mul_zero, det_one] at this
    exact zero_ne_one this
  have hdetD : D.det ≠ 0 := by
    simp only [D, det_diagonal]
    refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
    have : (Real.sqrt (μ k) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (hμ k)).ne'
    exact inv_ne_zero this
  have hdetR1 : R1.det ≠ 0 := by
    simp only [R1, det_mul]; exact mul_ne_zero hdetU hdetD
  set A1 := star R1 * A * R1
  have hA1 : A1.IsHermitian := by
    simpa [A1, star_eq_conjTranspose] using isHermitian_conjTranspose_mul_mul R1 hA
  set U1 := hA1.eigenvectorUnitary
  set lam := hA1.eigenvalues
  have hU1A : star (U1 : Matrix (Fin n) (Fin n) ℂ) * A1 * U1 =
      diagonal (fun k => (lam k : ℂ)) := by
    have := hA1.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Function.comp_def] using this
  have hdetU1 : (U1 : Matrix (Fin n) (Fin n) ℂ).det ≠ 0 := by
    have h := Matrix.UnitaryGroup.star_mul_self U1
    intro h0
    have := congrArg Matrix.det h
    rw [det_mul, h0, mul_zero, det_one] at this
    exact zero_ne_one this
  refine ⟨R1 * U1, ?_, ?_, lam, ?_⟩
  · rw [det_mul]; exact mul_ne_zero hdetR1 hdetU1
  · rw [star_mul]
    have : star (U1 : Matrix (Fin n) (Fin n) ℂ) * star R1 * B * (R1 * U1) =
        star (U1 : Matrix (Fin n) (Fin n) ℂ) * (star R1 * B * R1) * U1 := by
      simp only [Matrix.mul_assoc]
    rw [this, hR1B, Matrix.mul_one]
    exact Matrix.UnitaryGroup.star_mul_self U1
  · rw [star_mul]
    have : star (U1 : Matrix (Fin n) (Fin n) ℂ) * star R1 * A * (R1 * U1) =
        star (U1 : Matrix (Fin n) (Fin n) ℂ) * A1 * U1 := by
      simp only [A1, Matrix.mul_assoc]
    rw [this, hU1A]

/-- The mixed coefficient of diagonal slots: `C(diag μ₀, …, diag μ_{n-1}) = ∑_σ ∏_j μ_{σ j}(j)`. -/
theorem mixedCoefficient_diagonal_slots (μ : Fin n → Fin n → ℂ) :
    mixedCoefficient (fun i => diagonal (μ i)) = ∑ σ : Equiv.Perm (Fin n), ∏ j, μ (σ j) j := by
  unfold mixedCoefficient
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h : (Matrix.of fun j k => diagonal (μ (σ j)) j k) = diagonal (fun j => μ (σ j) j) := by
    ext j k
    by_cases hjk : j = k
    · subst hjk
      simp
    · simp [diagonal_apply_ne _ hjk]
  change (Matrix.of fun j k => diagonal (μ (σ j)) j k).det = _
  rw [h, det_diagonal]

/-- Reindexing a sum over permutations by a right multiplication. -/
theorem sum_perm_mul_swap {m : ℕ} (f : Equiv.Perm (Fin (m + 2)) → ℝ) (s : Equiv.Perm (Fin (m + 2))) :
    ∑ σ : Equiv.Perm (Fin (m + 2)), f (σ * s) = ∑ σ, f σ :=
  Fintype.sum_equiv (Equiv.mulRight s) _ _ fun _ => rfl

/-- **The key permutation identity**: if `∑ d = 0` then
`∑_σ d(σ 0) d(σ 1) = - m! ∑_k d_k²` (`n = m + 2`). -/
theorem sum_perm_mul_eq_neg {m : ℕ} (d : Fin (m + 2) → ℝ) (hd : ∑ k, d k = 0) :
    ∑ σ : Equiv.Perm (Fin (m + 2)), d (σ 0) * d (σ 1) = -((m.factorial : ℝ) * ∑ k, d k ^ 2) := by
  classical
  set T := ∑ σ : Equiv.Perm (Fin (m + 2)), d (σ 0) * d (σ 1) with hT
  have hswap : ∀ i : Fin (m + 2), i ≠ 0 →
      ∑ σ : Equiv.Perm (Fin (m + 2)), d (σ 0) * d (σ i) = T := by
    intro i hi
    rw [hT, ← sum_perm_mul_swap _ (Equiv.swap 1 i)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have h0 : (Equiv.swap (1 : Fin (m + 2)) i) 0 = 0 := by
      rw [Equiv.swap_apply_of_ne_of_ne (by simp) hi.symm]
    simp [Equiv.Perm.mul_apply, h0]
  have hsum0 : ∑ σ : Equiv.Perm (Fin (m + 2)), d (σ 0) * ∑ i, d (σ i) = 0 := by
    refine Finset.sum_eq_zero fun σ _ => ?_
    rw [Equiv.sum_comp σ d, hd, mul_zero]
  have hsplit : ∑ σ : Equiv.Perm (Fin (m + 2)), d (σ 0) * ∑ i, d (σ i) =
      ∑ σ : Equiv.Perm (Fin (m + 2)), d (σ 0) ^ 2 + ((m + 1 : ℕ) : ℝ) * T := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, Fin.sum_univ_succ]
    congr 1
    · exact Finset.sum_congr rfl fun σ _ => by ring
    · rw [Finset.sum_congr rfl fun (i : Fin (m + 1)) _ => hswap i.succ (Fin.succ_ne_zero i)]
      simp
  have hsq : ∑ σ : Equiv.Perm (Fin (m + 2)), d (σ 0) ^ 2 =
      ((m + 1).factorial : ℝ) * ∑ k, d k ^ 2 := by
    have h := Pending.OneOneFormMixedTrace.sum_perm_apply (m + 1) (fun k => d k ^ 2) 0
    rw [h, nsmul_eq_mul]
  rw [hsplit, hsq] at hsum0
  have hm : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have : ((m + 1 : ℕ) : ℝ) * T = ((m + 1 : ℕ) : ℝ) * (-((m.factorial : ℝ) * ∑ k, d k ^ 2)) := by
    rw [Nat.factorial_succ] at hsum0
    push_cast at hsum0 ⊢
    linarith
  exact mul_left_cancel₀ hm this

/-- The coefficient of the conjugated diagonal family `(D, D, 1, …, 1)` along a permutation. -/
theorem prod_twoSlot_diagonal {m : ℕ} (d : Fin (m + 2) → ℂ) (σ : Equiv.Perm (Fin (m + 2))) :
    ∏ j, (fun i : Fin (m + 2) => if i = 0 ∨ i = 1 then d else fun _ => (1 : ℂ)) (σ j) j =
      d (σ.symm 0) * d (σ.symm 1) := by
  classical
  have h : ∏ j, (fun i : Fin (m + 2) => if i = 0 ∨ i = 1 then d else fun _ => (1 : ℂ)) (σ j) j =
      ∏ i, (fun i : Fin (m + 2) => if i = 0 ∨ i = 1 then d else fun _ => (1 : ℂ)) i (σ.symm i) := by
    rw [← Equiv.prod_comp σ (fun i => (fun i : Fin (m + 2) =>
      if i = 0 ∨ i = 1 then d else fun _ => (1 : ℂ)) i (σ.symm i))]
    simp
  rw [h, Fin.prod_univ_succ, Fin.prod_univ_succ]
  have hrest : ∀ i : Fin m, ¬ ((i.succ.succ : Fin (m + 2)) = 0 ∨ (i.succ.succ : Fin (m + 2)) = 1) := by
    intro i hi
    rcases hi with hi | hi
    · exact Fin.succ_ne_zero _ hi
    · exact Fin.succ_ne_zero _ (Fin.succ_injective _ (by simpa using hi))
  rw [Finset.prod_eq_one fun i _ => by simp only [if_neg (hrest i)]]
  beta_reduce
  rw [if_pos (Or.inl rfl), if_pos (Or.inr Fin.succ_zero_eq_one), mul_one, Fin.succ_zero_eq_one]

/-- **Pointwise Hodge index inequality** for matrices (`n = m + 2`): if `A` is positive definite,
`B` Hermitian and `B` is `A`-trace free in the sense `Re C(B, A, …, A) = 0`, then
`Re C(B, B, A, …, A) ≤ 0`, with equality only for `B = 0`. -/
theorem re_mixedCoefficient_twoSlot {m : ℕ} {A B : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ}
    (hA : A.PosDef) (hB : B.IsHermitian)
    (htr : (mixedCoefficient (Function.update (fun _ => A) 0 B)).re = 0) :
    (mixedCoefficient (Function.update (Function.update (fun _ => A) 0 B) 1 B)).re ≤ 0 ∧
      ((mixedCoefficient (Function.update (Function.update (fun _ => A) 0 B) 1 B)).re = 0 →
        B = 0) := by
  classical
  obtain ⟨R, hR, hRA, d, hRB⟩ := exists_conj_eq_one_and_diagonal hB hA
  have hc : (star R).det * R.det = ((Complex.normSq R.det : ℝ) : ℂ) := by
    rw [star_eq_conjTranspose, det_conjTranspose, Complex.normSq_eq_conj_mul_self]
    rfl
  have hcpos : 0 < Complex.normSq R.det := Complex.normSq_pos.mpr hR
  -- the trace condition
  have hfam1 : (fun i : Fin (m + 2) => star R * Function.update (fun _ => A) 0 B i * R) =
      Function.update (fun _ => (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)) 0
        (diagonal fun k => (d k : ℂ)) := by
    funext i
    by_cases hi : i = 0
    · subst hi
      simp [hRB]
    · simp [Function.update_of_ne hi, hRA]
  have h1 : mixedCoefficient (Function.update (fun _ => (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)) 0
        (diagonal fun k => (d k : ℂ))) =
      (star R).det * R.det * mixedCoefficient (Function.update (fun _ => A) 0 B) := by
    exact (congrArg mixedCoefficient hfam1).symm.trans
      (Pending.MixedMongeAmpere.mixedCoefficient_mul_mul _ _ _)
  rw [Pending.OneOneFormMixedTrace.mixedCoefficient_update_const (m + 1), adjugate_one,
    Matrix.mul_one, trace_diagonal, hc] at h1
  have hsum : ∑ k, d k = 0 := by
    have hre := congrArg Complex.re h1
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero, Complex.ofReal_re, Complex.ofReal_im] at hre
    rw [htr, mul_zero, Complex.re_sum] at hre
    simp only [Complex.ofReal_re] at hre
    have hf : ((m + 1).factorial : ℝ) ≠ 0 := by positivity
    exact (mul_eq_zero.mp hre).resolve_left hf
  -- the two-slot family
  have hfam2 : (fun i : Fin (m + 2) => star R * Function.update (Function.update (fun _ => A) 0 B) 1 B i * R) =
      fun i => diagonal ((fun i : Fin (m + 2) => if i = 0 ∨ i = 1 then (fun k => (d k : ℂ))
        else fun _ => (1 : ℂ)) i) := by
    funext i
    by_cases hi1 : i = 1
    · subst hi1
      simp [hRB]
    · by_cases hi0 : i = 0
      · subst hi0
        simp [hRB]
      · simp [hRA, hi0, hi1]
  have h2 : mixedCoefficient (fun i => diagonal ((fun i : Fin (m + 2) =>
        if i = 0 ∨ i = 1 then (fun k => (d k : ℂ)) else fun _ => (1 : ℂ)) i)) =
      (star R).det * R.det * mixedCoefficient (Function.update (Function.update (fun _ => A) 0 B) 1 B) := by
    exact (congrArg mixedCoefficient hfam2).symm.trans
      (Pending.MixedMongeAmpere.mixedCoefficient_mul_mul _ _ _)
  rw [mixedCoefficient_diagonal_slots, hc] at h2
  simp_rw [prod_twoSlot_diagonal] at h2
  have hperm : ∑ σ : Equiv.Perm (Fin (m + 2)), ((d (σ.symm 0) : ℂ) * (d (σ.symm 1) : ℂ)) =
      ((∑ σ : Equiv.Perm (Fin (m + 2)), d (σ 0) * d (σ 1) : ℝ) : ℂ) := by
    push_cast
    exact Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin (m + 2)))) _ _ fun σ => rfl
  rw [hperm, sum_perm_mul_eq_neg d hsum] at h2
  have hre := congrArg Complex.re h2
  simp only [Complex.ofReal_re, Complex.re_ofReal_mul] at hre
  -- hre : -(m! ∑ d²) = normSq * Re C
  have hS : 0 ≤ (m.factorial : ℝ) * ∑ k, d k ^ 2 :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => sq_nonneg _)
  refine ⟨?_, fun h0 => ?_⟩
  · by_contra hpos
    have := mul_pos hcpos (not_le.mp hpos)
    linarith
  · rw [h0, mul_zero] at hre
    have hS0 : ∑ k, d k ^ 2 = 0 := by
      have hf : (m.factorial : ℝ) ≠ 0 := by positivity
      have : (m.factorial : ℝ) * ∑ k, d k ^ 2 = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hf
    have hd0 : ∀ k, d k = 0 := by
      intro k
      have := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg (d k)).mp hS0 k
        (Finset.mem_univ k)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    have hD : star R * B * R = 0 := by
      rw [hRB]
      ext j k
      simp [diagonal_apply, hd0]
    have hRu : IsUnit R.det := isUnit_iff_ne_zero.mpr hR
    have hsRu : IsUnit (star R).det := by
      rw [star_eq_conjTranspose, det_conjTranspose]
      exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hR)
    have hBR : (star R)⁻¹ * (star R * B * R) * R⁻¹ = B := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hRu, Matrix.mul_one,
        ← Matrix.mul_assoc, nonsing_inv_mul _ hsRu, Matrix.one_mul]
    rw [← hBR, hD, Matrix.mul_zero, Matrix.zero_mul]

end Matrix

/-! ### Mixed densities of `(1,1)`-forms -/

section Forms

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.IntegrationCurrent SGPT.Foundations.Analysis.Pending.TopDegreeDensity
  SGPT.Foundations.Analysis.Pending.ProductTestForms
  SGPT.Foundations.Analysis.Pending.MixedMassClassInvariance SGPT.Foundations.Analysis.Pending.NefMixedMass

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The coefficient matrix of a two-form at a point, read in the preferred chart. -/
def pointMatrix (a : SmoothRealForm n M 2) (x : M) : Matrix (Fin n) (Fin n) ℂ :=
  normalizedHermitianMatrix (a.coeff (complexChartAt (n := n) x) ((complexChartAt (n := n) x).val x))

theorem pointMatrix_posDef (w : KahlerBackground n M) (x : M) :
    (pointMatrix w.form.val x).PosDef := by
  have hz := (complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x)
  exact ConcentrationMassComparison.normalizedHermitianMatrix_posDef (w.isKahler.1 _ _ hz).1
    (w.isKahler.1 _ _ hz).2

theorem pointMatrix_isHermitian (θ : ClosedRealOneOneForm n M) (x : M) :
    (pointMatrix θ.val x).IsHermitian := by
  have hz := (complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x)
  exact normalizedHermitianMatrix_isHermitian _ (θ.2.2 _ _ hz)

/-- **The mixed density ratio as a mixed discriminant**: in the preferred chart at `x`,
`(θ₀ ∧ ⋯ ∧ θ_{n-1}) / ωⁿ = Re C(H_{θ₀}, …, H_{θ_{n-1}}) / (n! det H_ω)`. -/
theorem topRatio_slotForm_eq (w : KahlerBackground n M) (F : Fin n → ClosedRealOneOneForm n M)
    (x : M) :
    topRatio w.form.val (slotForm F) x =
      (mixedCoefficient fun i => pointMatrix (F i).val x).re /
        ((n.factorial : ℝ) * (pointMatrix w.form.val x).det.re) := by
  have hz := (complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x)
  have hd := SGPT.NPP.LogConcavity.det_re_pos (pointMatrix_posDef w x)
  simp only [topRatio, chartRatio]
  rw [topDensity_slotForm_coeff, formPow_coeff, topDensity_formPower,
    ConcentrationMassComparison.actualMixedTopDensity_eq_re (fun i => (F i).2.2 _ _ hz),
    ConcentrationMassComparison.actualTopPowerDensity_eq_det (w.isKahler.1 _ _ hz).1]
  unfold pointMatrix
  have hpi : (0 : ℝ) < Real.pi ^ n := pow_pos Real.pi_pos n
  field_simp

/-- A closed real `(1,1)`-form whose coefficient matrix vanishes at every point (in the
preferred chart) is geometrically zero: its coefficients vanish on every chart target. -/
theorem geometricallyEq_zero_of_pointMatrix_eq_zero {θ : ClosedRealOneOneForm n M}
    (h : ∀ x, pointMatrix θ.val x = 0) :
    θ.val.GeometricallyEq (0 : ClosedRealOneOneForm n M).val := by
  intro e z hz
  set x := e.val.symm z
  set f := complexChartAt (n := n) x
  have hxf : x ∈ f.val.source := mem_complexChartAt_source x
  have hfz : f.val x ∈ f.val.target := f.val.map_source hxf
  have hzt : z ∈ (chartTransition e f).source := by
    simp only [chartTransition, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source]
    exact ⟨hz, hxf⟩
  have hf0 : θ.val.coeff f (f.val x) = 0 :=
    LocalCurrentDensityMatrix.eq_zero_of_normalizedHermitianMatrix_eq_zero (θ.2.2 _ _ hfz) (h x)
  have htr : chartTransition e f z = f.val x := rfl
  rw [IntegrationCurrent.coeff_eq_compContinuousLinearMap θ.val hzt, htr, hf0]
  ext v
  simp

/-- `θ ∧ ω^{n-1} = (tr_ω θ / n) ωⁿ` pointwise (`n = m + 1`, `θ` in slot `0`). -/
theorem topRatio_update_zero {m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    (w : KahlerBackground (m + 1) M) (θ : ClosedRealOneOneForm (m + 1) M) (x : M) :
    topRatio w.form.val (slotForm (Function.update (fun _ => w.form) 0 θ)) x =
      SGPT.Hodge.trace w.form.val θ.val x / (m + 1 : ℕ) := by
  have hP := pointMatrix_posDef w x
  have hd := SGPT.NPP.LogConcavity.det_re_pos hP
  have him := SGPT.NPP.LogConcavity.det_im_eq_zero hP
  have hfam : (fun i : Fin (m + 1) =>
      pointMatrix (Function.update (fun _ : Fin (m + 1) => w.form) 0 θ i).val x) =
      Function.update (fun _ => pointMatrix w.form.val x) 0 (pointMatrix θ.val x) := by
    funext i
    by_cases hi : i = 0
    · subst hi
      simp
    · simp [Function.update_of_ne hi]
  rw [topRatio_slotForm_eq, hfam, Pending.OneOneFormMixedTrace.mixedCoefficient_update_const m]
  have hadj : adjugate (pointMatrix w.form.val x) =
      (pointMatrix w.form.val x).det • (pointMatrix w.form.val x)⁻¹ := by
    have hu : IsUnit (pointMatrix w.form.val x).det :=
      isUnit_iff_ne_zero.mpr fun h0 => by rw [h0, Complex.zero_re] at hd; exact lt_irrefl 0 hd
    rw [Matrix.inv_def, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hu.ne_zero, one_smul]
  rw [hadj, Matrix.mul_smul, trace_smul, smul_eq_mul, trace_mul_comm]
  simp only [SGPT.Hodge.trace, SGPT.Hodge.chartTrace]
  unfold pointMatrix at hd him ⊢
  rw [Complex.mul_re, Complex.mul_re, him]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  rw [Nat.factorial_succ m]
  push_cast
  field_simp

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 2)) M]
  [IsComplexManifold (m + 2) M]

/-- The family `(θ, ω, …, ω)`: its slot integral is `{θ} · {ω}^{n-1}`. -/
def oneSlot (w : KahlerBackground (m + 2) M) (θ : ClosedRealOneOneForm (m + 2) M) :
    Fin (m + 2) → ClosedRealOneOneForm (m + 2) M :=
  Function.update (fun _ => w.form) 0 θ

/-- The family `(θ, θ, ω, …, ω)`: its slot integral is `{θ}² · {ω}^{n-2}`. -/
def twoSlot (w : KahlerBackground (m + 2) M) (θ : ClosedRealOneOneForm (m + 2) M) :
    Fin (m + 2) → ClosedRealOneOneForm (m + 2) M :=
  Function.update (Function.update (fun _ => w.form) 0 θ) 1 θ

theorem pointMatrix_oneSlot (w : KahlerBackground (m + 2) M) (θ : ClosedRealOneOneForm (m + 2) M)
    (x : M) : (fun i => pointMatrix (oneSlot w θ i).val x) =
      Function.update (fun _ => pointMatrix w.form.val x) 0 (pointMatrix θ.val x) := by
  funext i
  by_cases hi : i = 0
  · subst hi
    simp [oneSlot]
  · simp [oneSlot, Function.update_of_ne hi]

theorem pointMatrix_twoSlot (w : KahlerBackground (m + 2) M) (θ : ClosedRealOneOneForm (m + 2) M)
    (x : M) : (fun i => pointMatrix (twoSlot w θ i).val x) =
      Function.update (Function.update (fun _ => pointMatrix w.form.val x) 0 (pointMatrix θ.val x))
        1 (pointMatrix θ.val x) := by
  funext i
  by_cases hi1 : i = 1
  · subst hi1
    simp [twoSlot]
  · by_cases hi0 : i = 0
    · subst hi0
      simp [twoSlot]
    · simp [twoSlot, Function.update_of_ne hi1, Function.update_of_ne hi0]

/-- `θ ∧ ω^{n-1} = (tr_ω θ / n) ωⁿ` pointwise. -/
theorem topRatio_oneSlot (w : KahlerBackground (m + 2) M) (θ : ClosedRealOneOneForm (m + 2) M)
    (x : M) :
    topRatio w.form.val (slotForm (oneSlot w θ)) x =
      SGPT.Hodge.trace w.form.val θ.val x / (m + 2 : ℕ) := by
  have hP := pointMatrix_posDef w x
  have hd := SGPT.NPP.LogConcavity.det_re_pos hP
  have him := SGPT.NPP.LogConcavity.det_im_eq_zero hP
  rw [topRatio_slotForm_eq, pointMatrix_oneSlot,
    Pending.OneOneFormMixedTrace.mixedCoefficient_update_const (m + 1)]
  have hadj : adjugate (pointMatrix w.form.val x) =
      (pointMatrix w.form.val x).det • (pointMatrix w.form.val x)⁻¹ := by
    have hu : IsUnit (pointMatrix w.form.val x).det :=
      isUnit_iff_ne_zero.mpr fun h0 => by rw [h0, Complex.zero_re] at hd; exact lt_irrefl 0 hd
    rw [Matrix.inv_def, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hu.ne_zero, one_smul]
  rw [hadj, Matrix.mul_smul, trace_smul, smul_eq_mul, trace_mul_comm]
  simp only [SGPT.Hodge.trace, SGPT.Hodge.chartTrace]
  unfold pointMatrix at hd him ⊢
  rw [Complex.mul_re, Complex.mul_re, him]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  rw [Nat.factorial_succ (m + 1)]
  push_cast
  field_simp
  ring

end Forms

/-! ### The Hodge index theorem -/

section Global

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.IntegrationCurrent
  SGPT.Foundations.Analysis.Pending.MixedMassClassInvariance SGPT.Foundations.Analysis.Pending.NefMixedMass

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 2)) M]
  [IsComplexManifold (m + 2) M]

/-- Pointwise Hodge index: for an `ω`-trace-free form `γ`, `γ² ∧ ω^{n-2} ≤ 0`, with equality at
`x` only where the coefficient matrix of `γ` vanishes. -/
theorem topRatio_twoSlot_nonpos (w : KahlerBackground (m + 2) M) {γ : ClosedRealOneOneForm (m + 2) M}
    (hγ : ∀ y, SGPT.Hodge.trace w.form.val γ.val y = 0) (x : M) :
    topRatio w.form.val (slotForm (twoSlot w γ)) x ≤ 0 ∧
      (topRatio w.form.val (slotForm (twoSlot w γ)) x = 0 → pointMatrix γ.val x = 0) := by
  have hd := SGPT.NPP.LogConcavity.det_re_pos (pointMatrix_posDef w x)
  have hden : 0 < ((m + 2).factorial : ℝ) * (pointMatrix w.form.val x).det.re :=
    mul_pos (by positivity) hd
  have htr : (mixedCoefficient (Function.update (fun _ => pointMatrix w.form.val x) 0
      (pointMatrix γ.val x))).re = 0 := by
    have h1 := topRatio_oneSlot w γ x
    rw [hγ x, zero_div, topRatio_slotForm_eq, pointMatrix_oneSlot] at h1
    exact (div_eq_zero_iff.mp h1).resolve_right hden.ne'
  obtain ⟨hle, heq⟩ := re_mixedCoefficient_twoSlot (pointMatrix_posDef w x)
    (pointMatrix_isHermitian γ x) htr
  rw [topRatio_slotForm_eq, pointMatrix_twoSlot]
  exact ⟨div_nonpos_of_nonpos_of_nonneg hle hden.le,
    fun h0 => heq ((div_eq_zero_iff.mp h0).resolve_right hden.ne')⟩

/-- The Kähler form is nef. -/
theorem nefWithRespectTo_form (w : KahlerBackground (m + 2) M) : NefWithRespectTo w w.form :=
  nefWithRespectTo_of_isSemipositive w.isSemipositive

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

theorem slotIntegral_oneSlot_eq_of_bottChernRel (w : KahlerBackground (m + 2) M)
    {θ γ : ClosedRealOneOneForm (m + 2) M} (h : ClosedRealOneOneForm.BottChernRel θ γ) :
    slotIntegral w (oneSlot w θ) = slotIntegral w (oneSlot w γ) := by
  refine SGPT.Hodge.BDivChain.SourceMixedOrderDraft.slotIntegral_eq_of_bottChernRel w _ _
    fun i => ?_
  by_cases hi : i = 0
  · subst hi
    simpa [oneSlot] using h
  · simpa [oneSlot, Function.update_of_ne hi] using ClosedRealOneOneForm.BottChernRel.refl w.form

theorem slotIntegral_twoSlot_eq_of_bottChernRel (w : KahlerBackground (m + 2) M)
    {θ γ : ClosedRealOneOneForm (m + 2) M} (h : ClosedRealOneOneForm.BottChernRel θ γ) :
    slotIntegral w (twoSlot w θ) = slotIntegral w (twoSlot w γ) := by
  refine SGPT.Hodge.BDivChain.SourceMixedOrderDraft.slotIntegral_eq_of_bottChernRel w _ _
    fun i => ?_
  by_cases hi1 : i = 1
  · subst hi1
    simpa [twoSlot] using h
  · by_cases hi0 : i = 0
    · subst hi0
      simpa [twoSlot] using h
    · simpa [twoSlot, Function.update_of_ne hi1, Function.update_of_ne hi0] using
        ClosedRealOneOneForm.BottChernRel.refl w.form

/-- `{θ} · {ω}^{n-1} = 0` lets one choose a cohomologous representative of trace `0`. -/
theorem exists_traceZero_bottChernRel [ConnectedSpace M] (w : KahlerBackground (m + 2) M)
    (θ : ClosedRealOneOneForm (m + 2) M) (h1 : slotIntegral w (oneSlot w θ) = 0) :
    ∃ γ : ClosedRealOneOneForm (m + 2) M, ClosedRealOneOneForm.BottChernRel θ γ ∧
      ∀ y, SGPT.Hodge.trace w.form.val γ.val y = 0 := by
  obtain ⟨γ, ⟨c, hc⟩, hrel⟩ := SGPT.Hodge.exists_constantTrace_bottChernRel w θ
  refine ⟨γ, hrel, fun y => ?_⟩
  rw [hc]
  rw [slotIntegral_oneSlot_eq_of_bottChernRel w hrel, slotIntegral] at h1
  simp_rw [topRatio_oneSlot, hc] at h1
  rw [integral_const, smul_eq_mul] at h1
  have hV := KahlerLaplacianSolvability.kahlerVolume_real_univ_pos w
  have : c / ((m + 2 : ℕ) : ℝ) = 0 := (mul_eq_zero.mp h1).resolve_left hV.ne'
  rcases div_eq_zero_iff.mp this with h | h
  · exact h
  · exact absurd h (by positivity)

/-- **Hodge index theorem, inequality**: on a compact connected Kähler manifold `(X, ω)` of
dimension `n ≥ 2`, a real `(1,1)`-class `α` with `α · {ω}^{n-1} = 0` has
`α² · {ω}^{n-2} ≤ 0`. -/
theorem slotIntegral_twoSlot_nonpos [ConnectedSpace M] (w : KahlerBackground (m + 2) M)
    (θ : ClosedRealOneOneForm (m + 2) M) (h1 : slotIntegral w (oneSlot w θ) = 0) :
    slotIntegral w (twoSlot w θ) ≤ 0 := by
  obtain ⟨γ, hrel, hγ⟩ := exists_traceZero_bottChernRel w θ h1
  rw [slotIntegral_twoSlot_eq_of_bottChernRel w hrel, slotIntegral]
  exact integral_nonpos fun x => (topRatio_twoSlot_nonpos w hγ x).1

/-- **Hodge index theorem, equality case**: if `α · {ω}^{n-1} = 0` and `α² · {ω}^{n-2} = 0`, then
`α = 0` in `H^{1,1}(X, ℝ)`. -/
theorem ofRepresentative_eq_zero_of_slotIntegral_twoSlot_eq_zero [ConnectedSpace M]
    (w : KahlerBackground (m + 2) M) (θ : ClosedRealOneOneForm (m + 2) M)
    (h1 : slotIntegral w (oneSlot w θ) = 0) (h2 : slotIntegral w (twoSlot w θ) = 0) :
    RealBottChern.ofRepresentative θ = 0 := by
  obtain ⟨γ, hrel, hγ⟩ := exists_traceZero_bottChernRel w θ h1
  rw [slotIntegral_twoSlot_eq_of_bottChernRel w hrel, slotIntegral] at h2
  set f := topRatio w.form.val (slotForm (twoSlot w γ)) with hf
  have hcont : Continuous f := continuous_topRatio w.isKahler.1 _
  have hae : (fun x => -f x) =ᵐ[kahlerVolume w] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => neg_nonneg.mpr (topRatio_twoSlot_nonpos w hγ x).1)
      (IntegrationCurrent.integrable_topRatio w _).neg).mp (by rw [integral_neg, h2, neg_zero])
  have hall : (fun x => -f x) = 0 :=
    (Continuous.ae_eq_iff_eq (kahlerVolume w) hcont.neg continuous_const).mp hae
  have hpt : ∀ x, pointMatrix γ.val x = 0 := fun x =>
    (topRatio_twoSlot_nonpos w hγ x).2 (neg_eq_zero.mp (congrFun hall x))
  rw [(RealBottChern.ofRepresentative_eq_iff θ γ).mpr hrel,
    RealBottChern.ofRepresentative_eq_of_geometricallyEq
      (geometricallyEq_zero_of_pointMatrix_eq_zero hpt),
    RealBottChern.ofRepresentative_zero]

/-- **Hodge index theorem** (`(1,1)`-classes on a compact connected Kähler manifold of dimension
`n ≥ 2`): if `α · {ω}^{n-1} = 0`, then `α² · {ω}^{n-2} ≤ 0`, with equality iff `α = 0`. -/
theorem hodgeIndex [ConnectedSpace M] (w : KahlerBackground (m + 2) M)
    (θ : ClosedRealOneOneForm (m + 2) M) (h1 : slotIntegral w (oneSlot w θ) = 0) :
    slotIntegral w (twoSlot w θ) ≤ 0 ∧
      (slotIntegral w (twoSlot w θ) = 0 ↔ RealBottChern.ofRepresentative θ = 0) := by
  refine ⟨slotIntegral_twoSlot_nonpos w θ h1,
    ⟨ofRepresentative_eq_zero_of_slotIntegral_twoSlot_eq_zero w θ h1, fun h0 => ?_⟩⟩
  have hrel : ClosedRealOneOneForm.BottChernRel θ 0 :=
    (RealBottChern.ofRepresentative_eq_iff θ 0).mp (h0.trans RealBottChern.ofRepresentative_zero.symm)
  rw [slotIntegral_twoSlot_eq_of_bottChernRel w hrel]
  exact SGPT.Hodge.BDivChain.SourceMixedOrderDraft.slotIntegral_update_zero w _ 1

/-- **A nef class `α` with `α · {ω}^{n-1} = 0` vanishes** (`n ≥ 2`). -/
theorem ofRepresentative_eq_zero_of_nef_of_slotIntegral_oneSlot_eq_zero [ConnectedSpace M]
    (w : KahlerBackground (m + 2) M) {θ : ClosedRealOneOneForm (m + 2) M}
    (hθ : NefWithRespectTo w θ) (h1 : slotIntegral w (oneSlot w θ) = 0) :
    RealBottChern.ofRepresentative θ = 0 := by
  have h0 : 0 ≤ slotIntegral w (twoSlot w θ) := by
    refine slotIntegral_nonneg_of_nef w fun i => ?_
    by_cases hi1 : i = 1
    · subst hi1
      simpa [twoSlot] using hθ
    · by_cases hi0 : i = 0
      · subst hi0
        simpa [twoSlot] using hθ
      · simpa [twoSlot, Function.update_of_ne hi1, Function.update_of_ne hi0] using
          nefWithRespectTo_form w
  exact ofRepresentative_eq_zero_of_slotIntegral_twoSlot_eq_zero w θ h1
    (le_antisymm (slotIntegral_twoSlot_nonpos w θ h1) h0)

/-- Mixed integrals with nef slots are nonnegative: `α · {ω}^{n-1} ≥ 0` for nef `α`. -/
theorem slotIntegral_oneSlot_nonneg_of_nef (w : KahlerBackground (m + 2) M)
    {θ : ClosedRealOneOneForm (m + 2) M} (hθ : NefWithRespectTo w θ) :
    0 ≤ slotIntegral w (oneSlot w θ) := by
  refine slotIntegral_nonneg_of_nef w fun i => ?_
  by_cases hi : i = 0
  · subst hi
    simpa [oneSlot] using hθ
  · simpa [oneSlot, Function.update_of_ne hi] using nefWithRespectTo_form w

theorem slotIntegral_oneSlot_neg (w : KahlerBackground (m + 2) M)
    (θ : ClosedRealOneOneForm (m + 2) M) :
    slotIntegral w (oneSlot w (-θ)) = -slotIntegral w (oneSlot w θ) := by
  have h := SGPT.Hodge.BDivChain.SourceMixedOrderDraft.slotIntegral_update_smul w
    (fun _ => w.form) 0 (-1) θ
  rw [neg_one_smul, smul_eq_mul, neg_one_mul] at h
  exact h

/-- **If `α` and `-α` are both nef, then `α = 0`** (`n ≥ 2`; numerically trivial classes in
the sense of nefness). -/
theorem eq_zero_of_classNef_of_classNef_neg [ConnectedSpace M] (w : KahlerBackground (m + 2) M)
    (α : RealBottChern (m + 2) M) (hα : ClassNefWithRespectTo w α)
    (hα' : ClassNefWithRespectTo w (-α)) : α = 0 := by
  induction α using Quotient.inductionOn with
  | h θ =>
    change ClassNefWithRespectTo w (RealBottChern.ofRepresentative θ) at hα
    change ClassNefWithRespectTo w (-RealBottChern.ofRepresentative θ) at hα'
    rw [← RealBottChern.ofRepresentative_neg, classNefWithRespectTo_ofRepresentative] at hα'
    rw [classNefWithRespectTo_ofRepresentative] at hα
    have hp := slotIntegral_oneSlot_nonneg_of_nef w hα
    have hn := slotIntegral_oneSlot_nonneg_of_nef w hα'
    rw [slotIntegral_oneSlot_neg] at hn
    exact ofRepresentative_eq_zero_of_nef_of_slotIntegral_oneSlot_eq_zero w hα (by linarith)

end Global

end SGPT.Projective.NumEq
