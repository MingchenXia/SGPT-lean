import SGPT.Foundations.Analysis.Pending.ProductComplexManifold
import SGPT.Foundations.Analysis.Pending.SmoothMixedMeasureDensity
import SGPT.Foundations.Analysis.Pending.MixedCoordinateDensity
import SGPT.Foundations.Analysis.Pending.SymmetricMultilinearDiagonal
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Mixed Monge--Ampère measures on a product: Fubini, and the top power of `p₁^*a + p₂^*b`

Sources: Boucksom, proof of Theorem 4.8 (`bou02-volume:4.8`), and Demailly--Păun, proof of
Theorem 2.12 (`dp04-kahler-cone:2.12`): the argument runs on `X × X` with the class
`p₁^*b + p₂^*b`, whose top power is `(p₁^*b + p₂^*b)^{2n} = C(2n, n) (bⁿ)²` (blueprint
`bou:uniform-diagonal-domination`); the class computation in `bou:pushforward-lower-bound`
integrates along the fibres of `p₁`.  TN.4 plan, step B6.

For complex manifolds `X`, `Y` of dimensions `n`, `m` (`X × Y` modelled on `ℂⁿ⁺ᵐ`,
`Pending.ProductComplexManifold`) and smooth closed semipositive `(1,1)`-forms:

* `globalMixedMeasure_prodSlots` — **Fubini for mixed measures**: the mixed measure of
  `p₁^*A₁, …, p₁^*Aₙ, p₂^*B₁, …, p₂^*Bₘ` (zero potentials) is the product of the mixed measures
  of the `Aᵢ` on `X` and of the `Bⱼ` on `Y`.
* `globalMixedMeasure_prodForm` — the measure `(p₁^*a + p₂^*b)^{n+m}` is
  `C(n+m, n) · aⁿ ⊗ bᵐ`; `globalMixedMeasure_prodForm_univ` — its total mass is
  `C(n+m, n) ∫ aⁿ ∫ bᵐ`.

The pointwise core is linear algebra: in the product chart the coefficient matrix of `p₁^*α` is
`H(α) ⊕ 0` and that of `p₂^*β` is `0 ⊕ H(β)` (`normalizedHermitianMatrix_comp_projFst`), the
mixed coefficient of block-diagonal slots factors (`mixedCoeff_blockFamily`, the mixed analogue
of `Matrix.det_fromBlocks_zero₂₁`), and the mixed coefficient of real `(1,1)`-forms is real
(`mixedCoefficient_im_eq_zero`, by polarization).  The measure statement then follows from TN23's
chart densities (`SmoothMixedMeasureDensity.globalMixedMeasure_image_eq_lintegral`) on the
product charts, the measure-preserving identification `ℂⁿ × ℂᵐ ≃ ℂⁿ⁺ᵐ`, Tonelli and
`Measure.prod_eq`.
-/

open Set Filter MeasureTheory Matrix
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.ProductMixedMeasure

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses ProductComplexManifold
  SymmetricMultilinearDiagonal Equiv Finset GlobalNonPluripolar SmoothMixedMeasureDensity
  StronglyPositiveForms
open scoped ProductComplexManifold

noncomputable section


section Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The mixed coefficient `∑_σ det (H (σ j) j k)` over a finite index type. -/
def mixedCoeff (H : ι → Matrix ι ι ℂ) : ℂ :=
  ∑ σ : Perm ι, (Matrix.of fun j k => H (σ j) j k).det

theorem mixedCoefficient_eq_mixedCoeff {N : ℕ} (e : ι ≃ Fin N)
    (H : Fin N → Matrix (Fin N) (Fin N) ℂ) :
    FirstPass.MixedMongeAmpere.mixedCoefficient H =
      mixedCoeff (fun a => (H (e a)).submatrix e e) := by
  unfold FirstPass.MixedMongeAmpere.mixedCoefficient mixedCoeff
  rw [← Equiv.sum_comp (Equiv.permCongr e)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  calc Matrix.det (fun j k => H (Equiv.permCongr e τ j) j k)
      = ((Matrix.of fun j k => H (Equiv.permCongr e τ j) j k).submatrix e e).det :=
        (det_submatrix_equiv_self e _).symm
    _ = _ := by
        congr 1
        ext a b
        simp [Equiv.permCongr_apply]

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The block family: `HA i ⊕ 0` on the left slots, `0 ⊕ HB j` on the right slots. -/
def blockFamily (HA : α → Matrix α α ℂ) (HB : β → Matrix β β ℂ) :
    α ⊕ β → Matrix (α ⊕ β) (α ⊕ β) ℂ :=
  Sum.elim (fun i => fromBlocks (HA i) 0 0 0) (fun j => fromBlocks 0 0 0 (HB j))

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem blockFamily_inl_inr (HA : α → Matrix α α ℂ) (HB : β → Matrix β β ℂ) (c : α ⊕ β)
    (j : α) (k : β) : blockFamily HA HB c (Sum.inl j) (Sum.inr k) = 0 := by
  cases c <;> simp [blockFamily]

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem blockFamily_inr_inl (HA : α → Matrix α α ℂ) (HB : β → Matrix β β ℂ) (c : α ⊕ β)
    (j : β) (k : α) : blockFamily HA HB c (Sum.inr j) (Sum.inl k) = 0 := by
  cases c <;> simp [blockFamily]

/-- **The mixed coefficient of block-diagonal slots factors**:
`C_{α ⊕ β}(HA ⊕ 0, 0 ⊕ HB) = C_α(HA) · C_β(HB)`. -/
theorem mixedCoeff_blockFamily (HA : α → Matrix α α ℂ) (HB : β → Matrix β β ℂ) :
    mixedCoeff (blockFamily HA HB) = mixedCoeff HA * mixedCoeff HB := by
  classical
  unfold mixedCoeff
  set f : Perm (α ⊕ β) → ℂ := fun σ =>
    (Matrix.of fun j k => blockFamily HA HB (σ (Sum.inl j)) (Sum.inl j) (Sum.inl k)).det *
      (Matrix.of fun j k => blockFamily HA HB (σ (Sum.inr j)) (Sum.inr j) (Sum.inr k)).det with hf
  have hblock : ∀ σ : Perm (α ⊕ β),
      (Matrix.of fun j k => blockFamily HA HB (σ j) j k).det = f σ := by
    intro σ
    have : (Matrix.of fun j k => blockFamily HA HB (σ j) j k) =
        fromBlocks (Matrix.of fun j k => blockFamily HA HB (σ (Sum.inl j)) (Sum.inl j) (Sum.inl k))
          0 0 (Matrix.of fun j k => blockFamily HA HB (σ (Sum.inr j)) (Sum.inr j) (Sum.inr k)) := by
      ext (j | j) (k | k)
      · rfl
      · simp [blockFamily_inl_inr]
      · simp [blockFamily_inr_inl]
      · rfl
    rw [this, det_fromBlocks_zero₂₁]
  simp_rw [hblock]
  have hzero : ∀ σ ∈ (univ : Finset (Perm (α ⊕ β))),
      σ ∉ (univ : Finset (Perm α × Perm β)).image (Perm.sumCongrHom α β) → f σ = 0 := by
    intro σ _ hσ
    have hσ' : σ ∉ (Perm.sumCongrHom α β).range := by
      rintro ⟨p, rfl⟩
      exact hσ (mem_image_of_mem _ (mem_univ p))
    have h1 : ¬∀ x, ∃ y, Sum.inl y = σ (Sum.inl x) := by
      intro h
      apply hσ'
      apply Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
      rintro _ ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := h x
      exact ⟨y, hy⟩
    obtain ⟨a, ha⟩ := not_forall.mp h1
    rcases hx : σ (Sum.inl a) with a2 | b
    · exact absurd hx.symm ((not_exists.mp ha) a2)
    · rw [hf]
      dsimp only
      rw [det_eq_zero_of_row_eq_zero a fun k => ?_, zero_mul]
      simp [hx, blockFamily]
  rw [← sum_subset (subset_univ _) hzero, sum_image
    (fun x _ y _ h => Perm.sumCongrHom_injective h), sum_mul_sum, ← Finset.univ_product_univ,
    sum_product]
  refine sum_congr rfl fun σ₁ _ => sum_congr rfl fun σ₂ _ => ?_
  simp only [hf, Perm.sumCongrHom_apply, Perm.sumCongr_apply, Sum.map_inl, Sum.map_inr]
  rfl

end Algebra

section Real

variable {n : ℕ}

/-- The imaginary part of the mixed coefficient, as an `ℝ`-multilinear function of the
matrices. -/
def mixedCoefficientImMultilinear :
    MultilinearMap ℝ (fun _ : Fin n => Matrix (Fin n) (Fin n) ℂ) ℝ where
  toFun H := (MixedMongeAmpere.mixedCoefficient H).im
  map_update_add' := by
    intro inst H i X Y
    have hinst : inst = instDecidableEqFin n := by
      funext a b
      exact Subsingleton.elim _ _
    subst hinst
    rw [mixedCoefficient_update_add H i X Y, Complex.add_im]
  map_update_smul' := by
    intro inst H i r X
    have hinst : inst = instDecidableEqFin n := by
      funext a b
      exact Subsingleton.elim _ _
    subst hinst
    rw [mixedCoefficient_update_smul H i r X, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im]
    simp only [smul_eq_mul, zero_mul, add_zero]

/-- **The mixed coefficient of the coefficient matrices of real `(1,1)`-forms is real.** -/
theorem mixedCoefficient_im_eq_zero (A : Fin n → CoordinateRealTwoForm n)
    (hA : ∀ i, IsOneOne (A i)) :
    (MixedMongeAmpere.mixedCoefficient fun i => normalizedHermitianMatrix (A i)).im = 0 := by
  set M : MultilinearMap ℝ (fun _ : Fin n => oneOneSubmodule n) ℝ :=
    (mixedCoefficientImMultilinear.compLinearMap fun _ => normalizedHermitianMatrixₗ).compLinearMap
      fun _ => (oneOneSubmodule n).subtype with hM
  have hsymm : IsSymmetricMultilinear M := by
    intro x τ
    show (MixedMongeAmpere.mixedCoefficient fun i =>
        normalizedHermitianMatrix ((x (τ i) : CoordinateRealTwoForm n))).im =
      (MixedMongeAmpere.mixedCoefficient fun i =>
        normalizedHermitianMatrix ((x i : CoordinateRealTwoForm n))).im
    rw [MixedMongeAmpere.mixedCoefficient_perm
      (fun i => normalizedHermitianMatrix ((x i : CoordinateRealTwoForm n))) τ]
  have hdiag : ∀ y : oneOneSubmodule n, M (fun _ => y) = (0 : MultilinearMap ℝ
      (fun _ : Fin n => oneOneSubmodule n) ℝ) (fun _ => y) := by
    intro y
    show (MixedMongeAmpere.mixedCoefficient fun _ =>
        normalizedHermitianMatrix ((y : CoordinateRealTwoForm n))).im = 0
    rw [MixedMongeAmpere.mixedCoefficient_diagonal, Complex.mul_im, Complex.natCast_re,
      Complex.natCast_im, normalizedHermitianMatrix_det_im_eq_zero _ y.2]
    simp
  have h := eq_of_diagonal_eq M 0 hsymm (fun _ _ => rfl) hdiag (fun i => ⟨A i, hA i⟩)
  exact h

end Real

section Coordinates

variable {n m : ℕ}

/-- The first projection `ℂⁿ⁺ᵐ → ℂⁿ`, as a real-linear map. -/
def projFst (n m : ℕ) : ComplexModel (n + m) →L[ℝ] ComplexModel n :=
  ((ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel m)).comp
    ((prodModelEquiv n m).symm : ComplexModel (n + m) →L[ℂ] _)).restrictScalars ℝ

/-- The second projection `ℂⁿ⁺ᵐ → ℂᵐ`, as a real-linear map. -/
def projSnd (n m : ℕ) : ComplexModel (n + m) →L[ℝ] ComplexModel m :=
  ((ContinuousLinearMap.snd ℂ (ComplexModel n) (ComplexModel m)).comp
    ((prodModelEquiv n m).symm : ComplexModel (n + m) →L[ℂ] _)).restrictScalars ℝ

theorem projFst_apply (v : ComplexModel (n + m)) : projFst n m v = ((prodModelEquiv n m).symm v).1 :=
  rfl

theorem projSnd_apply (v : ComplexModel (n + m)) : projSnd n m v = ((prodModelEquiv n m).symm v).2 :=
  rfl

theorem projFst_smul (c : ℂ) (v : ComplexModel (n + m)) : projFst n m (c • v) = c • projFst n m v := by
  simp [projFst_apply]

theorem projSnd_smul (c : ℂ) (v : ComplexModel (n + m)) : projSnd n m (c • v) = c • projSnd n m v := by
  simp [projSnd_apply]

theorem prodModelEquiv_symm_coordinateVector_castAdd (j : Fin n) :
    (prodModelEquiv n m).symm (coordinateVector (Fin.castAdd m j)) = (coordinateVector j, 0) := by
  simp only [prodModelEquiv, coordinateVector, ContinuousLinearEquiv.symm_symm]
  ext i <;> simp

theorem prodModelEquiv_symm_coordinateVector_natAdd (j : Fin m) :
    (prodModelEquiv n m).symm (coordinateVector (Fin.natAdd n j)) = (0, coordinateVector j) := by
  simp only [prodModelEquiv, coordinateVector, ContinuousLinearEquiv.symm_symm]
  ext i <;> simp

theorem comp_vec {k l : ℕ} (L : ComplexModel l →L[ℝ] ComplexModel k) (u v : ComplexModel l) :
    (⇑L ∘ ![u, v]) = ![L u, L v] := by
  funext i
  fin_cases i <;> rfl

theorem apply_vec_zero_right {k : ℕ} (A : CoordinateRealTwoForm k) (u : ComplexModel k) :
    A ![u, 0] = 0 :=
  A.map_coord_zero (1 : Fin 2) rfl

theorem apply_vec_zero_left {k : ℕ} (A : CoordinateRealTwoForm k) (v : ComplexModel k) :
    A ![0, v] = 0 :=
  A.map_coord_zero (0 : Fin 2) rfl

theorem projFst_castAdd (j : Fin n) :
    projFst n m (coordinateVector (Fin.castAdd m j)) = coordinateVector j := by
  rw [projFst_apply, prodModelEquiv_symm_coordinateVector_castAdd]

theorem projFst_natAdd (j : Fin m) :
    projFst n m (coordinateVector (Fin.natAdd n j)) = 0 := by
  rw [projFst_apply, prodModelEquiv_symm_coordinateVector_natAdd]

theorem projSnd_castAdd (j : Fin n) :
    projSnd n m (coordinateVector (Fin.castAdd m j)) = 0 := by
  rw [projSnd_apply, prodModelEquiv_symm_coordinateVector_castAdd]

theorem projSnd_natAdd (j : Fin m) :
    projSnd n m (coordinateVector (Fin.natAdd n j)) = coordinateVector j := by
  rw [projSnd_apply, prodModelEquiv_symm_coordinateVector_natAdd]

/-- The coefficient matrix of `p₁^*α` is `H(α) ⊕ 0`. -/
theorem normalizedHermitianMatrix_comp_projFst (A : CoordinateRealTwoForm n) :
    (normalizedHermitianMatrix (A.compContinuousLinearMap (projFst n m))).submatrix
        finSumFinEquiv finSumFinEquiv = fromBlocks (normalizedHermitianMatrix A) 0 0 0 := by
  ext (j | j) (k | k) <;>
    simp only [submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, normalizedHermitianMatrix, ContinuousAlternatingMap.compContinuousLinearMap_apply,
      comp_vec, projFst_smul, projFst_castAdd, projFst_natAdd, smul_zero, apply_vec_zero_right,
      apply_vec_zero_left, Complex.ofReal_zero, mul_zero, sub_zero]

/-- The coefficient matrix of `p₂^*β` is `0 ⊕ H(β)`. -/
theorem normalizedHermitianMatrix_comp_projSnd (B : CoordinateRealTwoForm m) :
    (normalizedHermitianMatrix (B.compContinuousLinearMap (projSnd n m))).submatrix
        finSumFinEquiv finSumFinEquiv = fromBlocks 0 0 0 (normalizedHermitianMatrix B) := by
  ext (j | j) (k | k) <;>
    simp only [submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, normalizedHermitianMatrix, ContinuousAlternatingMap.compContinuousLinearMap_apply,
      comp_vec, projSnd_smul, projSnd_castAdd, projSnd_natAdd, smul_zero, apply_vec_zero_right,
      apply_vec_zero_left, Complex.ofReal_zero, mul_zero, sub_zero]

end Coordinates

section Density

variable {n m : ℕ}

theorem mixedCoeff_eq_mixedCoefficient {N : ℕ} (H : Fin N → Matrix (Fin N) (Fin N) ℂ) :
    mixedCoeff H = MixedMongeAmpere.mixedCoefficient H := rfl

theorem isOneOne_comp_projFst {A : CoordinateRealTwoForm n} (hA : IsOneOne A) :
    IsOneOne (A.compContinuousLinearMap (projFst n m)) :=
  ProductTestForms.isOneOne_compContinuousLinearMap hA _ fun v => projFst_smul Complex.I v

theorem isOneOne_comp_projSnd {B : CoordinateRealTwoForm m} (hB : IsOneOne B) :
    IsOneOne (B.compContinuousLinearMap (projSnd n m)) :=
  ProductTestForms.isOneOne_compContinuousLinearMap hB _ fun v => projSnd_smul Complex.I v

/-- **The density of a product family factors**: in the coordinates `ℂⁿ⁺ᵐ = ℂⁿ × ℂᵐ`,
`p₁^*α₁ ∧ ⋯ ∧ p₁^*αₙ ∧ p₂^*β₁ ∧ ⋯ ∧ p₂^*βₘ` has density `(α₁ ∧ ⋯ ∧ αₙ)(β₁ ∧ ⋯ ∧ βₘ)`. -/
theorem actualMixedTopDensity_append_comp (A : Fin n → CoordinateRealTwoForm n)
    (B : Fin m → CoordinateRealTwoForm m) (hA : ∀ i, IsOneOne (A i)) (hB : ∀ j, IsOneOne (B j)) :
    actualMixedTopDensity (Fin.append (fun i => (A i).compContinuousLinearMap (projFst n m))
        (fun j => (B j).compContinuousLinearMap (projSnd n m))) =
      actualMixedTopDensity A * actualMixedTopDensity B := by
  have hone : ∀ i, IsOneOne (Fin.append (fun i => (A i).compContinuousLinearMap (projFst n m))
      (fun j => (B j).compContinuousLinearMap (projSnd n m)) i) := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      exact isOneOne_comp_projFst (hA i)
    · rw [Fin.append_right]
      exact isOneOne_comp_projSnd (hB j)
  rw [actualMixedTopDensity_eq_normalizedMixedTopDensity _ hone,
    actualMixedTopDensity_eq_normalizedMixedTopDensity _ hA,
    actualMixedTopDensity_eq_normalizedMixedTopDensity _ hB]
  unfold normalizedMixedTopDensity
  have hfam : (fun a => (normalizedHermitianMatrix (Fin.append
      (fun i => (A i).compContinuousLinearMap (projFst n m))
      (fun j => (B j).compContinuousLinearMap (projSnd n m)) (finSumFinEquiv a))).submatrix
        finSumFinEquiv finSumFinEquiv) =
      blockFamily (fun i => normalizedHermitianMatrix (A i))
        (fun j => normalizedHermitianMatrix (B j)) := by
    funext a
    rcases a with i | j
    · rw [finSumFinEquiv_apply_left, Fin.append_left, normalizedHermitianMatrix_comp_projFst]
      rfl
    · rw [finSumFinEquiv_apply_right, Fin.append_right, normalizedHermitianMatrix_comp_projSnd]
      rfl
  rw [mixedCoefficient_eq_mixedCoeff finSumFinEquiv, hfam, mixedCoeff_blockFamily,
    mixedCoeff_eq_mixedCoefficient, mixedCoeff_eq_mixedCoefficient, Complex.mul_re,
    mixedCoefficient_im_eq_zero A hA, mixedCoefficient_im_eq_zero B hB, pow_add]
  field_simp
  ring

/-- **The top power of `p₁^*a + p₂^*b`**: its density is `C(n+m, n) · aⁿ · bᵐ`. -/
theorem actualMixedTopDensity_const_add_comp (a : CoordinateRealTwoForm n)
    (b : CoordinateRealTwoForm m) (ha : IsOneOne a) (hb : IsOneOne b) :
    actualMixedTopDensity (fun _ : Fin (n + m) =>
        a.compContinuousLinearMap (projFst n m) + b.compContinuousLinearMap (projSnd n m)) =
      ((n + m).choose n : ℝ) * actualMixedTopDensity (fun _ : Fin n => a) *
        actualMixedTopDensity (fun _ : Fin m => b) := by
  have hone : IsOneOne (a.compContinuousLinearMap (projFst n m) +
      b.compContinuousLinearMap (projSnd n m)) :=
    isOneOne_add (isOneOne_comp_projFst ha) (isOneOne_comp_projSnd hb)
  rw [actualMixedTopDensity_eq_normalizedMixedTopDensity _ fun _ => hone,
    actualMixedTopDensity_eq_normalizedMixedTopDensity _ fun _ => ha,
    actualMixedTopDensity_eq_normalizedMixedTopDensity _ fun _ => hb]
  unfold normalizedMixedTopDensity
  rw [MixedMongeAmpere.mixedCoefficient_diagonal, MixedMongeAmpere.mixedCoefficient_diagonal,
    MixedMongeAmpere.mixedCoefficient_diagonal]
  have hdet : (normalizedHermitianMatrix (a.compContinuousLinearMap (projFst n m) +
      b.compContinuousLinearMap (projSnd n m))).det =
        (normalizedHermitianMatrix a).det * (normalizedHermitianMatrix b).det := by
    have hsub : ∀ (P Q : Matrix (Fin (n + m)) (Fin (n + m)) ℂ),
        (P + Q).submatrix finSumFinEquiv finSumFinEquiv =
          P.submatrix finSumFinEquiv finSumFinEquiv + Q.submatrix finSumFinEquiv finSumFinEquiv :=
      fun P Q => by ext; rfl
    rw [← det_submatrix_equiv_self finSumFinEquiv, normalizedHermitianMatrix_add, hsub,
      normalizedHermitianMatrix_comp_projFst, normalizedHermitianMatrix_comp_projSnd, fromBlocks_add]
    simp
  rw [hdet]
  have hia := normalizedHermitianMatrix_det_im_eq_zero a ha
  have hib := normalizedHermitianMatrix_det_im_eq_zero b hb
  have hfact : (((n + m).factorial : ℕ) : ℝ) =
      ((n + m).choose n : ℝ) * (n.factorial : ℝ) * (m.factorial : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right n m)
    rw [Nat.add_sub_cancel_left] at h
    exact_mod_cast h.symm
  simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, hia, hib,
    zero_mul, mul_zero, sub_zero, add_zero]
  rw [hfact, pow_add]
  field_simp

end Density


/-! ### Product charts -/

section Charts

variable {n m : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y]
  [IsComplexManifold m Y]

/-- The product of two charts, as a chart of the product atlas of `X × Y`. -/
def prodComplexChart (e : ComplexChart n X) (e' : ComplexChart m Y) : ComplexChart (n + m) (X × Y) :=
  ⟨prodChart e.val e'.val, mem_image2_of_mem e.2 e'.2⟩

theorem prodComplexChart_val (e : ComplexChart n X) (e' : ComplexChart m Y) :
    (prodComplexChart e e').val = prodChart e.val e'.val := rfl

theorem mem_prodComplexChart_target {e : ComplexChart n X} {e' : ComplexChart m Y}
    {z : ComplexModel n} {z' : ComplexModel m} (hz : z ∈ e.val.target) (hz' : z' ∈ e'.val.target) :
    prodModelEquiv n m (z, z') ∈ (prodComplexChart e e').val.target := by
  rw [prodComplexChart_val, prodChart_target]
  simp [hz, hz']

theorem prodComplexChart_symm_apply (e : ComplexChart n X) (e' : ComplexChart m Y)
    (z : ComplexModel n) (z' : ComplexModel m) :
    (prodComplexChart e e').val.symm (prodModelEquiv n m (z, z')) = (e.val.symm z, e'.val.symm z') := by
  rw [prodComplexChart_val, prodChart_symm_apply]
  simp

/-- On the product chart, the first projection reads `projFst` (near every point of the target). -/
theorem coordinateMap_fst_eventuallyEq (e : ComplexChart n X) (e' : ComplexChart m Y)
    {w : ComplexModel (n + m)} (hw : w ∈ (prodComplexChart e e').val.target) :
    HolomorphicMaps.coordinateMap Prod.fst (prodComplexChart e e') e =ᶠ[𝓝 w] projFst n m := by
  filter_upwards [(prodComplexChart e e').val.open_target.mem_nhds hw] with w' hw'
  rw [prodComplexChart_val, prodChart_target] at hw'
  show e.val ((prodChart e.val e'.val).symm w').1 = ((prodModelEquiv n m).symm w').1
  rw [prodChart_symm_apply]
  exact e.val.right_inv hw'.1

theorem coordinateMap_snd_eventuallyEq (e : ComplexChart n X) (e' : ComplexChart m Y)
    {w : ComplexModel (n + m)} (hw : w ∈ (prodComplexChart e e').val.target) :
    HolomorphicMaps.coordinateMap Prod.snd (prodComplexChart e e') e' =ᶠ[𝓝 w] projSnd n m := by
  filter_upwards [(prodComplexChart e e').val.open_target.mem_nhds hw] with w' hw'
  rw [prodComplexChart_val, prodChart_target] at hw'
  show e'.val ((prodChart e.val e'.val).symm w').2 = ((prodModelEquiv n m).symm w').2
  rw [prodChart_symm_apply]
  exact e'.val.right_inv hw'.2

/-- **The coefficients of `p₁^*α` in a product chart** are those of `α` composed with the
projection `ℂⁿ⁺ᵐ → ℂⁿ`. -/
theorem pullback_fst_coeff {p : ℕ} (α : SmoothRealForm n X p) (e : ComplexChart n X)
    (e' : ComplexChart m Y) {z : ComplexModel n} {z' : ComplexModel m} (hz : z ∈ e.val.target)
    (hz' : z' ∈ e'.val.target) :
    (SmoothRealForm.pullback (contMDiff_fst (X := X) (Y := Y)) α).coeff (prodComplexChart e e')
        (prodModelEquiv n m (z, z')) =
      (α.coeff e z).compContinuousLinearMap (projFst n m) := by
  have hw := mem_prodComplexChart_target (e := e) (e' := e') hz hz'
  have hdom : prodModelEquiv n m (z, z') ∈
      HolomorphicMaps.coordinateDomain Prod.fst (prodComplexChart e e') e := by
    refine ⟨hw, ?_⟩
    simp only [Set.mem_preimage, prodComplexChart_symm_apply]
    exact e.val.map_target hz
  rw [SmoothRealForm.pullback_coeff contMDiff_fst α _ e hdom,
    (coordinateMap_fst_eventuallyEq e e' hw).fderiv_eq, ContinuousLinearMap.fderiv]
  congr 2
  show e.val ((prodComplexChart e e').val.symm (prodModelEquiv n m (z, z'))).1 = z
  rw [prodComplexChart_symm_apply]
  exact e.val.right_inv hz

/-- **The coefficients of `p₂^*β` in a product chart.** -/
theorem pullback_snd_coeff {p : ℕ} (β : SmoothRealForm m Y p) (e : ComplexChart n X)
    (e' : ComplexChart m Y) {z : ComplexModel n} {z' : ComplexModel m} (hz : z ∈ e.val.target)
    (hz' : z' ∈ e'.val.target) :
    (SmoothRealForm.pullback (contMDiff_snd (X := X) (Y := Y)) β).coeff (prodComplexChart e e')
        (prodModelEquiv n m (z, z')) =
      (β.coeff e' z').compContinuousLinearMap (projSnd n m) := by
  have hw := mem_prodComplexChart_target (e := e) (e' := e') hz hz'
  have hdom : prodModelEquiv n m (z, z') ∈
      HolomorphicMaps.coordinateDomain Prod.snd (prodComplexChart e e') e' := by
    refine ⟨hw, ?_⟩
    simp only [Set.mem_preimage, prodComplexChart_symm_apply]
    exact e'.val.map_target hz'
  rw [SmoothRealForm.pullback_coeff contMDiff_snd β _ e' hdom,
    (coordinateMap_snd_eventuallyEq e e' hw).fderiv_eq, ContinuousLinearMap.fderiv]
  congr 2
  show e'.val ((prodComplexChart e e').val.symm (prodModelEquiv n m (z, z'))).2 = z'
  rw [prodComplexChart_symm_apply]
  exact e'.val.right_inv hz'

end Charts

/-! ### Measures -/

section Measures

/-- The identification `ℂⁿ × ℂᵐ ≃ ℂⁿ⁺ᵐ` preserves Lebesgue measure. -/
theorem measurePreserving_prodModelEquiv (n m : ℕ) :
    MeasurePreserving (prodModelEquiv n m) (volume.prod volume) volume := by
  set J : WithLp 2 (ComplexModel n × ComplexModel m) ≃ₗᵢ[ℂ] ComplexModel (n + m) :=
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin n ⊕ Fin m => ℂ)).symm.trans
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finSumFinEquiv) with hJ
  have hiso := (IsometryEquiv.toRealLinearIsometryEquivOfMapZero J.toIsometryEquiv
    (by rw [LinearIsometryEquiv.coe_toIsometryEquiv]; exact map_zero _)).measurePreserving
  rw [IsometryEquiv.coe_toRealLinearIsometryEquivOfMapZero] at hiso
  have hcomp := hiso.comp (WithLp.volume_preserving_toLp (ComplexModel n) (ComplexModel m))
  have hfun : ⇑(prodModelEquiv n m) = ⇑J.toIsometryEquiv ∘ WithLp.toLp 2 := by
    funext p
    ext i
    simp [prodModelEquiv, J]
  rw [← Measure.volume_eq_prod, hfun]
  exact hcomp

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M]

/-- The mixed measure of smooth semipositive forms (zero potentials) on a compact manifold is
finite: on a chart ball its density is bounded. -/
theorem isFiniteMeasure_globalMixedMeasure [CompactSpace M] {θ : Fin n → ClosedRealOneOneForm n M}
    (hθ : ∀ i, ThetaPlurisubharmonic (θ i).val (fun _ => 0)) :
    IsFiniteMeasure (globalMixedMeasure θ (fun _ _ => 0) hθ) := by
  set μ := globalMixedMeasure θ (fun _ _ => 0) hθ with hμ
  have hloc : IsLocallyFiniteMeasure μ := by
    refine ⟨fun x => ?_⟩
    set e := complexChartAt (n := n) x
    have hz : e.val x ∈ e.val.target := e.val.map_source (mem_complexChartAt_source x)
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.val.open_target _ hz
    have hcb : Metric.closedBall (e.val x) (r / 2) ⊆ e.val.target :=
      (Metric.closedBall_subset_ball (by linarith)).trans hball
    have hbt : Metric.ball (e.val x) (r / 2) ⊆ e.val.target :=
      Metric.ball_subset_closedBall.trans hcb
    refine ⟨e.val.symm '' Metric.ball (e.val x) (r / 2), ?_, ?_⟩
    · rw [e.val.symm_image_eq_source_inter_preimage hbt]
      refine (e.val.isOpen_inter_preimage Metric.isOpen_ball).mem_nhds ⟨mem_complexChartAt_source x, ?_⟩
      exact Metric.mem_ball_self (by linarith)
    · refine lt_of_le_of_lt (measure_mono (image_mono Metric.ball_subset_closedBall)) ?_
      rw [globalMixedMeasure_image_eq_lintegral hθ e Metric.isClosed_closedBall.measurableSet hcb]
      have hK : IsCompact (Metric.closedBall (e.val x) (r / 2)) := isCompact_closedBall _ _
      obtain ⟨z₀, -, hmax⟩ := hK.exists_isMaxOn
        (Metric.nonempty_closedBall.mpr (by linarith)) ((continuousOn_chartDensity θ e).mono hcb)
      calc ∫⁻ z in Metric.closedBall (e.val x) (r / 2), chartDensity θ e z
          ≤ ∫⁻ _ in Metric.closedBall (e.val x) (r / 2), chartDensity θ e z₀ :=
            setLIntegral_mono measurable_const fun z hz => hmax hz
        _ = chartDensity θ e z₀ * volume (Metric.closedBall (e.val x) (r / 2)) :=
            setLIntegral_const _ _
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top
  exact CompactSpace.isFiniteMeasure

/-- A measurable partition of a compact manifold into countably many pieces, each inside the
source of a chart (finitely many nonempty). -/
theorem exists_chart_partition [CompactSpace M] :
    ∃ D : ℕ → Set M, (∀ j, MeasurableSet (D j)) ∧ Pairwise (Function.onFun Disjoint D) ∧
      (⋃ j, D j) = univ ∧ ∀ j, (D j).Nonempty → ∃ e : ComplexChart n M, D j ⊆ e.val.source := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M => (complexChartAt (n := n) x).val.source)
    (fun x => (complexChartAt (n := n) x).val.open_source)
    (fun x _ => mem_iUnion.mpr ⟨x, mem_complexChartAt_source x⟩)
  set k := t.card
  set pts : Fin k → M := fun j => (t.equivFin.symm j : M)
  set f : ℕ → Set M := fun j =>
    if hj : j < k then (complexChartAt (n := n) (pts ⟨j, hj⟩)).val.source else ∅ with hfdef
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
  refine ⟨disjointed f, MeasurableSet.disjointed hfm, disjoint_disjointed f, by
    rw [iUnion_disjointed, hcov], fun j hne => ?_⟩
  by_cases hj : j < k
  · refine ⟨complexChartAt (n := n) (pts ⟨j, hj⟩), fun y hy => ?_⟩
    have := disjointed_subset f j hy
    simpa [hfdef, hj] using this
  · exfalso
    obtain ⟨y, hy⟩ := hne
    have := disjointed_subset f j hy
    simp [hfdef, hj] at this

/-- The image of a measurable subset of a chart source is a measurable subset of the target. -/
theorem measurableSet_chart_image (e : ComplexChart n M) {s : Set M} (hs : MeasurableSet s)
    (hse : s ⊆ e.val.source) : MeasurableSet (e.val '' s) := by
  rw [e.val.image_eq_target_inter_inv_preimage hse]
  exact measurableSet_inter_preimage_of_continuousOn e.val.open_target.measurableSet
    e.val.continuousOn_symm hs

end Measures

/-! ### Fubini for mixed measures -/

section Fubini

variable {n m : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y]
  [IsComplexManifold m Y] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

/-- **The mixed measure of a product chart rectangle**, when the chart density factors. -/
theorem globalMixedMeasure_rect [CompactSpace X] [CompactSpace Y]
    {θ : Fin (n + m) → ClosedRealOneOneForm (n + m) (X × Y)}
    (hθ : ∀ i, ThetaPlurisubharmonic (θ i).val (fun _ => 0)) (e : ComplexChart n X)
    (e' : ComplexChart m Y) {ρ₁ : ComplexModel n → ℝ≥0∞} {ρ₂ : ComplexModel m → ℝ≥0∞}
    (hρ₁ : ContinuousOn ρ₁ e.val.target) (hρ₂ : ContinuousOn ρ₂ e'.val.target)
    (hfac : ∀ z ∈ e.val.target, ∀ z' ∈ e'.val.target,
      chartDensity θ (prodComplexChart e e') (prodModelEquiv n m (z, z')) = ρ₁ z * ρ₂ z')
    {S : Set (ComplexModel n)} {T : Set (ComplexModel m)} (hS : MeasurableSet S)
    (hT : MeasurableSet T) (hSe : S ⊆ e.val.target) (hTe : T ⊆ e'.val.target) :
    globalMixedMeasure θ (fun _ _ => 0) hθ ((e.val.symm '' S) ×ˢ (e'.val.symm '' T)) =
      (∫⁻ z in S, ρ₁ z) * ∫⁻ z' in T, ρ₂ z' := by
  set E := prodComplexChart e e'
  set L := prodModelEquiv n m
  have himg : (e.val.symm '' S) ×ˢ (e'.val.symm '' T) = E.val.symm '' (L '' (S ×ˢ T)) := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨⟨z, hz, hzx⟩, ⟨z', hz', hzy⟩⟩
      refine ⟨L (z, z'), ⟨(z, z'), ⟨hz, hz'⟩, rfl⟩, ?_⟩
      rw [prodComplexChart_symm_apply, hzx, hzy]
    · rintro ⟨w, ⟨⟨z, z'⟩, ⟨hz, hz'⟩, rfl⟩, hw⟩
      rw [prodComplexChart_symm_apply, Prod.mk.injEq] at hw
      exact ⟨⟨z, hz, hw.1⟩, ⟨z', hz', hw.2⟩⟩
  have hemb : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
  have hK : MeasurableSet (L '' (S ×ˢ T)) := hemb.measurableSet_image.mpr (hS.prod hT)
  have hKt : L '' (S ×ˢ T) ⊆ E.val.target := by
    rintro _ ⟨⟨z, z'⟩, ⟨hz, hz'⟩, rfl⟩
    exact mem_prodComplexChart_target (hSe hz) (hTe hz')
  rw [himg, globalMixedMeasure_image_eq_lintegral hθ E hK hKt,
    ← (measurePreserving_prodModelEquiv n m).setLIntegral_comp_emb hemb,
    setLIntegral_congr_fun (hS.prod hT) fun p hp => hfac p.1 (hSe hp.1) p.2 (hTe hp.2),
    ← Measure.prod_restrict]
  exact lintegral_prod_mul ((hρ₁.mono hSe).aemeasurable hS) ((hρ₂.mono hTe).aemeasurable hT)

/-- Splitting a measure along a countable measurable partition. -/
theorem measure_eq_tsum_inter {Z : Type*} [MeasurableSpace Z] (ν : Measure Z) {A : Set Z}
    (hA : MeasurableSet A) {P : ℕ → Set Z} (hP : ∀ j, MeasurableSet (P j))
    (hPd : Pairwise (Function.onFun Disjoint P)) (hPu : (⋃ j, P j) = univ) :
    ν A = ∑' j, ν (A ∩ P j) := by
  have hA' : A = ⋃ j, A ∩ P j := by rw [← inter_iUnion, hPu, inter_univ]
  conv_lhs => rw [hA']
  exact measure_iUnion (fun i j hij => (hPd hij).mono inter_subset_right inter_subset_right)
    fun j => hA.inter (hP j)

/-- **Rectangles in chart sources suffice**: a measure on `X × Y` that is the product of `μA` and
`μB` on rectangles inside product chart sources is the product on all measurable rectangles. -/
theorem measure_prod_eq_of_chart [CompactSpace X] [CompactSpace Y] {μ : Measure (X × Y)}
    {μA : Measure X} {μB : Measure Y}
    (h : ∀ (e : ComplexChart n X) (e' : ComplexChart m Y) (s : Set X) (t : Set Y),
      MeasurableSet s → MeasurableSet t → s ⊆ e.val.source → t ⊆ e'.val.source →
        μ (s ×ˢ t) = μA s * μB t)
    {s : Set X} {t : Set Y} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ (s ×ˢ t) = μA s * μB t := by
  obtain ⟨D, hDm, hDd, hDu, hDe⟩ := exists_chart_partition (n := n) (M := X)
  obtain ⟨D', hDm', hDd', hDu', hDe'⟩ := exists_chart_partition (n := m) (M := Y)
  have hprodD : Pairwise (Function.onFun Disjoint fun p : ℕ × ℕ => D p.1 ×ˢ D' p.2) := by
    intro p q hpq
    simp only [Function.onFun]
    rcases p with ⟨a, b⟩
    rcases q with ⟨c, d⟩
    by_cases hac : a = c
    · have hbd : b ≠ d := fun h => hpq (by rw [hac, h])
      exact Set.disjoint_prod.mpr (Or.inr (hDd' hbd))
    · exact Set.disjoint_prod.mpr (Or.inl (hDd hac))
  have hprodU : (⋃ p : ℕ × ℕ, D p.1 ×ˢ D' p.2) = univ := by
    refine eq_univ_iff_forall.mpr fun ⟨x, y⟩ => ?_
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hDu ▸ mem_univ x : x ∈ ⋃ j, D j)
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hDu' ▸ mem_univ y : y ∈ ⋃ j, D' j)
    exact mem_iUnion.mpr ⟨(j, k), hj, hk⟩
  have hμ : μ (s ×ˢ t) = ∑' p : ℕ × ℕ, μ ((s ∩ D p.1) ×ˢ (t ∩ D' p.2)) := by
    rw [show (∑' p : ℕ × ℕ, μ ((s ∩ D p.1) ×ˢ (t ∩ D' p.2))) =
        ∑' p : ℕ × ℕ, μ (s ×ˢ t ∩ D p.1 ×ˢ D' p.2) by
      congr 1; funext p; rw [Set.prod_inter_prod]]
    have hA' : s ×ˢ t = ⋃ p : ℕ × ℕ, s ×ˢ t ∩ D p.1 ×ˢ D' p.2 := by
      rw [← inter_iUnion, hprodU, inter_univ]
    conv_lhs => rw [hA']
    exact measure_iUnion (fun p q hpq => (hprodD hpq).mono inter_subset_right inter_subset_right)
      fun p => (hs.prod ht).inter ((hDm p.1).prod (hDm' p.2))
  rw [hμ, measure_eq_tsum_inter μA hs hDm hDd hDu, measure_eq_tsum_inter μB ht hDm' hDd' hDu',
    ENNReal.tsum_prod (f := fun a b => μ ((s ∩ D a) ×ˢ (t ∩ D' b))),
    ← ENNReal.tsum_mul_right]
  refine tsum_congr fun j => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun k => ?_
  rcases (s ∩ D j).eq_empty_or_nonempty with h1 | h1
  · simp [h1]
  rcases (t ∩ D' k).eq_empty_or_nonempty with h2 | h2
  · simp [h2]
  obtain ⟨e, he⟩ := hDe j (h1.mono inter_subset_right)
  obtain ⟨e', he'⟩ := hDe' k (h2.mono inter_subset_right)
  exact h e e' _ _ (hs.inter (hDm j)) (ht.inter (hDm' k)) (inter_subset_right.trans he)
    (inter_subset_right.trans he')

end Fubini

/-! ### The product slots and the main theorems -/

section Main

variable {n m : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y]
  [IsComplexManifold m Y]

/-- The slots `p₁^*A₀, …, p₁^*A_{n-1}, p₂^*B₀, …, p₂^*B_{m-1}` on `X × Y`. -/
def prodSlots (A : Fin n → ClosedRealOneOneForm n X) (B : Fin m → ClosedRealOneOneForm m Y) :
    Fin (n + m) → ClosedRealOneOneForm (n + m) (X × Y) :=
  Fin.append (fun i => ClosedRealOneOneForm.pullback contMDiff_fst (A i))
    (fun j => ClosedRealOneOneForm.pullback contMDiff_snd (B j))

/-- The slots are semipositive when the factors are. -/
theorem thetaPlurisubharmonic_prodSlots {A : Fin n → ClosedRealOneOneForm n X}
    {B : Fin m → ClosedRealOneOneForm m Y} (hA : ∀ i, ThetaPlurisubharmonic (A i).val (fun _ => 0))
    (hB : ∀ j, ThetaPlurisubharmonic (B j).val (fun _ => 0)) (i : Fin (n + m)) :
    ThetaPlurisubharmonic (prodSlots A B i).val (fun _ => 0) := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · rw [prodSlots, Fin.append_left, LocalPotentials.thetaPlurisubharmonic_zero_iff]
    exact (SmoothRealForm.IsSemipositive.pullback contMDiff_fst
      ((LocalPotentials.thetaPlurisubharmonic_zero_iff _).mp (hA i)))
  · rw [prodSlots, Fin.append_right, LocalPotentials.thetaPlurisubharmonic_zero_iff]
    exact (SmoothRealForm.IsSemipositive.pullback contMDiff_snd
      ((LocalPotentials.thetaPlurisubharmonic_zero_iff _).mp (hB j)))

/-- The chart density of the product slots factors in a product chart. -/
theorem chartDensity_prodSlots {A : Fin n → ClosedRealOneOneForm n X}
    {B : Fin m → ClosedRealOneOneForm m Y} (hA : ∀ i, ThetaPlurisubharmonic (A i).val (fun _ => 0))
    (e : ComplexChart n X)
    (e' : ComplexChart m Y) {z : ComplexModel n} {z' : ComplexModel m} (hz : z ∈ e.val.target)
    (hz' : z' ∈ e'.val.target) :
    chartDensity (prodSlots A B) (prodComplexChart e e') (prodModelEquiv n m (z, z')) =
      chartDensity A e z * chartDensity B e' z' := by
  have hcoeff : (fun i => (prodSlots A B i).val.coeff (prodComplexChart e e')
      (prodModelEquiv n m (z, z'))) =
      Fin.append (fun i => ((A i).val.coeff e z).compContinuousLinearMap (projFst n m))
        (fun j => ((B j).val.coeff e' z').compContinuousLinearMap (projSnd n m)) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · rw [Fin.append_left, prodSlots, Fin.append_left, ClosedRealOneOneForm.pullback_val,
        pullback_fst_coeff _ e e' hz hz']
    · rw [Fin.append_right, prodSlots, Fin.append_right, ClosedRealOneOneForm.pullback_val,
        pullback_snd_coeff _ e e' hz hz']
  rw [chartDensity, hcoeff, actualMixedTopDensity_append_comp _ _
      (fun i => (A i).2.2 e z hz) (fun j => (B j).2.2 e' z' hz'),
    ENNReal.ofReal_mul (TopDegreeDensity.actualMixedTopDensity_nonneg
      fun i => isSemipositiveOneOne_coeff (hA i) hz)]
  rfl

variable [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

/-- **Fubini for mixed measures**: the mixed measure of
`p₁^*A₀, …, p₁^*A_{n-1}, p₂^*B₀, …, p₂^*B_{m-1}` on `X × Y` is the product of the mixed measures
of the `Aᵢ` on `X` and of the `Bⱼ` on `Y` (smooth closed semipositive forms, zero potentials). -/
theorem globalMixedMeasure_prodSlots [CompactSpace X] [CompactSpace Y]
    (A : Fin n → ClosedRealOneOneForm n X) (B : Fin m → ClosedRealOneOneForm m Y)
    (hA : ∀ i, ThetaPlurisubharmonic (A i).val (fun _ => 0))
    (hB : ∀ j, ThetaPlurisubharmonic (B j).val (fun _ => 0))
    (hAB : ∀ i, ThetaPlurisubharmonic (prodSlots A B i).val (fun _ => 0)) :
    globalMixedMeasure (prodSlots A B) (fun _ _ => 0) hAB =
      (globalMixedMeasure A (fun _ _ => 0) hA).prod (globalMixedMeasure B (fun _ _ => 0) hB) := by
  have := isFiniteMeasure_globalMixedMeasure hA
  have := isFiniteMeasure_globalMixedMeasure hB
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  refine measure_prod_eq_of_chart (n := n) (m := m) (fun e e' s t hs ht hse hte => ?_) hs ht
  have hS := measurableSet_chart_image e hs hse
  have hT := measurableSet_chart_image e' ht hte
  have hSt : e.val '' s ⊆ e.val.target := fun _ ⟨x, hx, hxe⟩ => hxe ▸ e.val.map_source (hse hx)
  have hTt : e'.val '' t ⊆ e'.val.target := fun _ ⟨x, hx, hxe⟩ => hxe ▸ e'.val.map_source (hte hx)
  have hs' : e.val.symm '' (e.val '' s) = s := e.val.symm_image_image_of_subset_source hse
  have ht' : e'.val.symm '' (e'.val '' t) = t := e'.val.symm_image_image_of_subset_source hte
  have hrect := globalMixedMeasure_rect hAB e e' (continuousOn_chartDensity A e)
    (continuousOn_chartDensity B e') (fun z hz z' hz' => chartDensity_prodSlots hA e e' hz hz')
    hS hT hSt hTt
  rw [hs', ht'] at hrect
  rw [hrect, ← globalMixedMeasure_image_eq_lintegral hA e hS hSt,
    ← globalMixedMeasure_image_eq_lintegral hB e' hT hTt, hs', ht']

/-- The total mass in Fubini: `∫_{X×Y} p₁^*A ∧ p₂^*B = ∫_X A · ∫_Y B`. -/
theorem globalMixedMeasure_prodSlots_univ [CompactSpace X] [CompactSpace Y]
    (A : Fin n → ClosedRealOneOneForm n X) (B : Fin m → ClosedRealOneOneForm m Y)
    (hA : ∀ i, ThetaPlurisubharmonic (A i).val (fun _ => 0))
    (hB : ∀ j, ThetaPlurisubharmonic (B j).val (fun _ => 0))
    (hAB : ∀ i, ThetaPlurisubharmonic (prodSlots A B i).val (fun _ => 0)) :
    globalMixedMeasure (prodSlots A B) (fun _ _ => 0) hAB univ =
      globalMixedMeasure A (fun _ _ => 0) hA univ * globalMixedMeasure B (fun _ _ => 0) hB univ := by
  have := isFiniteMeasure_globalMixedMeasure hA
  have := isFiniteMeasure_globalMixedMeasure hB
  rw [globalMixedMeasure_prodSlots A B hA hB hAB, ← univ_prod_univ, Measure.prod_prod]

/-- The chart density of `(p₁^*a + p₂^*b)^{n+m}` in a product chart. -/
theorem chartDensity_prodForm {a : ClosedRealOneOneForm n X} {b : ClosedRealOneOneForm m Y}
    (ha : ThetaPlurisubharmonic a.val (fun _ => 0)) (hb : ThetaPlurisubharmonic b.val (fun _ => 0))
    (e : ComplexChart n X) (e' : ComplexChart m Y) {z : ComplexModel n} {z' : ComplexModel m}
    (hz : z ∈ e.val.target) (hz' : z' ∈ e'.val.target) :
    chartDensity (fun _ : Fin (n + m) => prodForm a b) (prodComplexChart e e')
        (prodModelEquiv n m (z, z')) =
      ((n + m).choose n : ℝ≥0∞) * chartDensity (fun _ : Fin n => a) e z *
        chartDensity (fun _ : Fin m => b) e' z' := by
  have hcoeff : (prodForm a b).val.coeff (prodComplexChart e e') (prodModelEquiv n m (z, z')) =
      (a.val.coeff e z).compContinuousLinearMap (projFst n m) +
        (b.val.coeff e' z').compContinuousLinearMap (projSnd n m) := by
    rw [prodForm, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.pullback_val,
      ClosedRealOneOneForm.pullback_val, pullback_fst_coeff _ e e' hz hz',
      pullback_snd_coeff _ e e' hz hz']
  have h0a := TopDegreeDensity.actualMixedTopDensity_nonneg
    fun _ : Fin n => isSemipositiveOneOne_coeff ha hz
  have h0b := TopDegreeDensity.actualMixedTopDensity_nonneg
    fun _ : Fin m => isSemipositiveOneOne_coeff hb hz'
  simp only [chartDensity]
  rw [hcoeff, actualMixedTopDensity_const_add_comp _ _ (a.2.2 e z hz) (b.2.2 e' z' hz'),
    ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) h0a), ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_natCast]

/-- **The top power of `p₁^*a + p₂^*b`**: `(p₁^*a + p₂^*b)^{n+m} = C(n+m, n) · aⁿ ⊗ bᵐ` as
measures on `X × Y` (smooth closed semipositive `a`, `b`, zero potentials). -/
theorem globalMixedMeasure_prodForm [CompactSpace X] [CompactSpace Y]
    (a : ClosedRealOneOneForm n X) (b : ClosedRealOneOneForm m Y)
    (ha : ThetaPlurisubharmonic a.val (fun _ => 0)) (hb : ThetaPlurisubharmonic b.val (fun _ => 0))
    (hab : ∀ _ : Fin (n + m), ThetaPlurisubharmonic (prodForm a b).val (fun _ => 0)) :
    globalMixedMeasure (fun _ => prodForm a b) (fun _ _ => 0) hab =
      ((n + m).choose n : ℝ≥0∞) •
        (globalMixedMeasure (fun _ : Fin n => a) (fun _ _ => 0) fun _ => ha).prod
          (globalMixedMeasure (fun _ : Fin m => b) (fun _ _ => 0) fun _ => hb) := by
  set c : ℝ≥0∞ := ((n + m).choose n : ℝ≥0∞) with hc
  have hctop : c ≠ ⊤ := ENNReal.natCast_ne_top _
  have := isFiniteMeasure_globalMixedMeasure (θ := fun _ : Fin n => a) fun _ => ha
  have := isFiniteMeasure_globalMixedMeasure (θ := fun _ : Fin m => b) fun _ => hb
  have : IsFiniteMeasure (c • globalMixedMeasure (fun _ : Fin n => a) (fun _ _ => 0) fun _ => ha) :=
    isFiniteMeasureSMulOfNNRealTower (r := ((n + m).choose n : NNReal))
  rw [← Measure.prod_smul_left]
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  refine measure_prod_eq_of_chart (n := n) (m := m) (fun e e' s t hs ht hse hte => ?_) hs ht
  have hS := measurableSet_chart_image e hs hse
  have hT := measurableSet_chart_image e' ht hte
  have hSt : e.val '' s ⊆ e.val.target := fun _ ⟨x, hx, hxe⟩ => hxe ▸ e.val.map_source (hse hx)
  have hTt : e'.val '' t ⊆ e'.val.target := fun _ ⟨x, hx, hxe⟩ => hxe ▸ e'.val.map_source (hte hx)
  have hs' : e.val.symm '' (e.val '' s) = s := e.val.symm_image_image_of_subset_source hse
  have ht' : e'.val.symm '' (e'.val '' t) = t := e'.val.symm_image_image_of_subset_source hte
  have hρ₁ : ContinuousOn (fun z => c * chartDensity (fun _ : Fin n => a) e z) e.val.target :=
    (ENNReal.continuous_const_mul hctop).comp_continuousOn (continuousOn_chartDensity _ e)
  have hrect := globalMixedMeasure_rect hab e e' hρ₁ (continuousOn_chartDensity _ e')
    (fun z hz z' hz' => by rw [chartDensity_prodForm ha hb e e' hz hz'])
    hS hT hSt hTt
  rw [hs', ht'] at hrect
  rw [hrect, lintegral_const_mul' c _ hctop,
    ← globalMixedMeasure_image_eq_lintegral (θ := fun _ : Fin n => a) (fun _ => ha) e hS hSt,
    ← globalMixedMeasure_image_eq_lintegral (θ := fun _ : Fin m => b) (fun _ => hb) e' hT hTt,
    hs', ht', Measure.smul_apply, smul_eq_mul]

/-- **The top intersection number of `p₁^*a + p₂^*b`**:
`∫_{X×Y} (p₁^*a + p₂^*b)^{n+m} = C(n+m, n) ∫_X aⁿ ∫_Y bᵐ`; for `Y = X`, `b = a`:
`(p₁^*a + p₂^*a)^{2n} = C(2n, n) (aⁿ)²` (blueprint `bou:uniform-diagonal-domination`). -/
theorem globalMixedMeasure_prodForm_univ [CompactSpace X] [CompactSpace Y]
    (a : ClosedRealOneOneForm n X) (b : ClosedRealOneOneForm m Y)
    (ha : ThetaPlurisubharmonic a.val (fun _ => 0)) (hb : ThetaPlurisubharmonic b.val (fun _ => 0))
    (hab : ∀ _ : Fin (n + m), ThetaPlurisubharmonic (prodForm a b).val (fun _ => 0)) :
    globalMixedMeasure (fun _ => prodForm a b) (fun _ _ => 0) hab univ =
      ((n + m).choose n : ℝ≥0∞) *
        (globalMixedMeasure (fun _ : Fin n => a) (fun _ _ => 0) fun _ => ha) univ *
          (globalMixedMeasure (fun _ : Fin m => b) (fun _ _ => 0) fun _ => hb) univ := by
  have := isFiniteMeasure_globalMixedMeasure (θ := fun _ : Fin n => a) fun _ => ha
  have := isFiniteMeasure_globalMixedMeasure (θ := fun _ : Fin m => b) fun _ => hb
  rw [globalMixedMeasure_prodForm a b ha hb hab, Measure.smul_apply, smul_eq_mul,
    ← univ_prod_univ, Measure.prod_prod, mul_assoc]

end Main

end

end SGPT.Foundations.Analysis.Pending.ProductMixedMeasure
