import SGPT.Okounkov.TranscendentalCoreValuationBounded
import SGPT.Okounkov.FlagCorrectionComposition
import SGPT.Okounkov.PotentialFlagCorrection
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Valuations of pulled-back potentials and the correction matrix

Source: blueprint nodes `tok:lifting-invariance` and `tok:approx-pushforward` (chapter
`claude-okounkov-transcendental`), i.e. DRWNXZ (Darvas--Reboulet--Witt Nyström--Xia--Zhang,
*Transcendental Okounkov bodies*) Lemma 4.2 = the book's `prop:cormatrix` / `prop:cormult`, in the
form consumed by the lifting-invariance proof.

For a lifting `(W•, g)` of `Y•` along `π : W → X` (`IsFlagLifting F W π`, correction matrix
`g = flagLiftingCorrectionMatrix`), and a `θ`-psh potential `φ` on `X`,

* `flagValuation_comp_eq_vecMul`: `ν_{W•}(π^*φ) = ν_{Y•}(φ) g` (row vectors);
* `det_flagLiftingCorrectionMatrix`: `det g = 1` (the matrix is block upper unitriangular);
* `correctionMatrixReal_comp`: the real correction matrix of a composite lifting is the
  product;
* `flagValuation_eq_of_le_add`: two quasi-psh potentials differing by a bounded function have
  the same valuation (used for log resolutions, where `φ ∘ π = ψ_D + O(1)`).

The real matrix is written `fun i j => (g i j : ℝ)`, as in
`TranscendentalMain.LiftingInvarianceStatement`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalLifting

open Set Filter
open scoped Matrix Topology NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.TranscendentalCore

/-- The real correction matrix `g = cor(Y•, π)` of a lifting, acting on row vectors. -/
def correctionMatrixReal {n : ℕ} {F W : OriginalFlagGeometry.{u} n} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (flagLiftingCorrectionMatrix n F W π hπ i j : ℝ)

theorem correctionMatrixReal_eq_map {n : ℕ} {F W : OriginalFlagGeometry.{u} n}
    {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π) :
    correctionMatrixReal hπ =
      (Int.castRingHom ℝ).mapMatrix (flagLiftingCorrectionMatrix n F W π hπ) :=
  rfl

/-- The block form of the correction matrix of a lifting in positive dimension. -/
theorem flagLiftingCorrectionMatrix_succ_eq {m : ℕ}
    (F W : OriginalFlagGeometry.{u} (m + 1)) (π : W.carrier → F.carrier)
    (hπ : IsFlagLifting F W π) :
    flagLiftingCorrectionMatrix (m + 1) F W π hπ =
      Fin.cons (Fin.cons 1 (flagLiftingCorrectionRow hπ))
        (fun i => Fin.cons 0
          (flagLiftingCorrectionMatrix m F.tail W.tail hπ.tailMap hπ.tailMap_isFlagLifting i)) :=
  rfl

/-- **The correction matrix is unimodular**: `det cor(Y•, π) = 1`. It is block upper
triangular with first row `(1, c_π)`, first column `(1, 0, …, 0)` and lower right block the
correction matrix of the tail lifting. -/
theorem det_flagLiftingCorrectionMatrix :
    ∀ (n : ℕ) (F W : OriginalFlagGeometry.{u} n) (π : W.carrier → F.carrier)
      (hπ : IsFlagLifting F W π), (flagLiftingCorrectionMatrix n F W π hπ).det = 1 := by
  intro n
  induction n with
  | zero =>
      intro F W π hπ
      exact Matrix.det_isEmpty
  | succ m ih =>
      intro F W π hπ
      rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
      have hrest : ∀ i : Fin m, (-1 : ℤ) ^ ((i.succ : Fin (m + 1)) : ℕ) *
          flagLiftingCorrectionMatrix (m + 1) F W π hπ i.succ 0 *
          ((flagLiftingCorrectionMatrix (m + 1) F W π hπ).submatrix i.succ.succAbove
            Fin.succ).det = 0 := by
        intro i
        rw [flagLiftingCorrectionMatrix_succ_eq]
        simp
      rw [Finset.sum_eq_zero (fun i _ => hrest i), add_zero]
      have hsub : (flagLiftingCorrectionMatrix (m + 1) F W π hπ).submatrix
          (Fin.succAbove (0 : Fin (m + 1))) Fin.succ =
          flagLiftingCorrectionMatrix m F.tail W.tail hπ.tailMap hπ.tailMap_isFlagLifting := by
        ext i j
        rw [flagLiftingCorrectionMatrix_succ_eq]
        rfl
      rw [hsub, ih F.tail W.tail hπ.tailMap hπ.tailMap_isFlagLifting,
        flagLiftingCorrectionMatrix_succ_eq]
      simp

/-- The real correction matrix has determinant `1`. -/
theorem det_correctionMatrixReal {n : ℕ} {F W : OriginalFlagGeometry.{u} n}
    {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π) :
    (correctionMatrixReal hπ).det = 1 := by
  rw [correctionMatrixReal_eq_map, ← RingHom.map_det, det_flagLiftingCorrectionMatrix,
    map_one]

theorem isUnit_det_correctionMatrixReal {n : ℕ} {F W : OriginalFlagGeometry.{u} n}
    {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π) :
    IsUnit (correctionMatrixReal hπ).det := by
  rw [det_correctionMatrixReal]
  exact isUnit_one

/-- Right multiplication by the correction matrix can be undone. -/
theorem vecMul_correctionMatrixReal_inv {n : ℕ} {F W : OriginalFlagGeometry.{u} n}
    {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π) (x : Fin n → ℝ) :
    (x ᵥ* correctionMatrixReal hπ) ᵥ* (correctionMatrixReal hπ)⁻¹ = x := by
  rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (isUnit_det_correctionMatrixReal hπ),
    Matrix.vecMul_one]

/-- **Correction matrices multiply** (`okflag:actual-composable-correction-matrix-product`, real
form): `cor(Y•, π ∘ p) = cor(Y•, π) cor(W•, p)`. -/
theorem correctionMatrixReal_comp {n : ℕ} {F W V : OriginalFlagGeometry.{u} n}
    {π : W.carrier → F.carrier} {p : V.carrier → W.carrier}
    (hπ : IsFlagLifting F W π) (hp : IsFlagLifting W V p) (hπp : IsFlagLifting F V (π ∘ p)) :
    correctionMatrixReal hπp = correctionMatrixReal hπ * correctionMatrixReal hp := by
  have h := flagLiftingCorrectionMatrix_comp n F W V π p hπ hp
  rw [correctionMatrixReal_eq_map, correctionMatrixReal_eq_map, correctionMatrixReal_eq_map,
    ← map_mul, ← h]

/-- **Valuation of a pulled-back potential** (DRWNXZ Lemma 4.2, book `prop:cormatrix`):
`ν_{W•}(π^*φ) = ν_{Y•}(φ) g` for every `θ`-psh potential `φ`. -/
theorem flagValuation_comp_eq_vecMul {n : ℕ} {F W : OriginalFlagGeometry.{u} n}
    {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π)
    {θ : ClosedRealOneOneForm n F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) :
    flagValuation W (fun y => φ (π y)) = flagValuation F φ ᵥ* correctionMatrixReal hπ := by
  rw [flagValuation_eq
      (AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
        hπ.1 θ hφ),
    potentialFlagValuation_modification_eq_correctionNNReal n F W π hπ θ φ hφ,
    flagValuation_eq hφ]
  exact (flagLiftingCorrectionMatrix_vecMul_nnreal n F W π hπ (potentialFlagValuation F hφ)).symm

/-- **Bounded differences do not change the valuation**: if `φ ≤ χ + C` and `χ ≤ φ + C`, then
`ν(φ) = ν(χ)` (multiplier ideals only see the singularity type). -/
theorem flagValuation_eq_of_le_add {n : ℕ} {F : OriginalFlagGeometry.{u} n}
    {θ σ : ClosedRealOneOneForm n F.carrier} {φ χ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hχ : IsThetaPshPotential σ.val χ) {C : ℝ}
    (h₁ : ∀ x, φ x ≤ χ x + (C : EReal)) (h₂ : ∀ x, χ x ≤ φ x + (C : EReal)) :
    flagValuation F φ = flagValuation F χ :=
  flagValuation_eq_of_iEquivalent hφ hχ
    ⟨iOrderOnManifold_of_le_add hχ.quasiPshPotential.1 h₁,
      iOrderOnManifold_of_le_add hφ.quasiPshPotential.1 h₂⟩

/-- The valuation of `χ + b` for a bounded real `b` is that of `χ`. -/
theorem flagValuation_add_bounded {n : ℕ} {F : OriginalFlagGeometry.{u} n}
    {θ σ : ClosedRealOneOneForm n F.carrier} {χ : F.carrier → EReal} {b : F.carrier → ℝ}
    (hχ : IsThetaPshPotential σ.val χ)
    (hφ : IsThetaPshPotential θ.val (fun x => χ x + (b x : EReal))) {C : ℝ}
    (hb : ∀ x, |b x| ≤ C) :
    flagValuation F (fun x => χ x + (b x : EReal)) = flagValuation F χ := by
  refine flagValuation_eq_of_le_add hφ hχ (C := C) (fun x => ?_) (fun x => ?_)
  · exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_of_abs_le (hb x)))
  · calc χ x = χ x + (b x : EReal) + ((-b x : ℝ) : EReal) := by
          induction χ x using EReal.rec with
          | bot => simp
          | top => simp
          | coe r =>
              rw [← EReal.coe_add, ← EReal.coe_add]
              congr 1
              ring
      _ ≤ χ x + (b x : EReal) + (C : EReal) :=
          add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (by have := abs_le.mp (hb x); linarith))

end SGPT.Okounkov.TranscendentalLifting
