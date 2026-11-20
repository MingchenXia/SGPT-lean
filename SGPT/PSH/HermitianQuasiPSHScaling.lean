import SGPT.PSH.HermitianLocalPositivity
import SGPT.PSH.HermitianExtremalQuasiAlgebra
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshSmoothLocalization
import SGPT.Foundations.Analysis.Pending.SmoothDDCForm

/-!
# Small positive scalings of genuine quasi-PSH functions

On a compact complex manifold, finitely many genuine smooth local corrections
of a quasi-PSH function suffice. Each smooth correction is bounded below in
complex Hessian by a multiple of the supplied Hermitian form. A single positive
constant therefore puts every sufficiently small positive scaling in the actual
Hermitian-relative PSH class. Closedness of the Hermitian form is never used.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.Hermitian

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open GlobalQuasiPshSmoothLocalization SmoothDDCForm
open HermitianExtremalQuasiAlgebra

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [CompactSpace M]

/-- Every genuine local quasi-PSH potential has a uniform small-scaling
threshold for the actual, possibly nonclosed, Hermitian-relative PSH class. -/
theorem exists_pos_scaling_constant (omega : Background (m + 1) M)
    {u : M → EReal} (hu : IsGlobalQuasiPshPotential (n := m + 1) u) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → t * C ≤ 1 →
      IsHermitianPSH omega (fun x => (t : EReal) * u x) := by
  classical
  choose H hH S hS hxS hpS using
    (fun x : M => exists_chartSmooth_local_psh_correction hu.1 x)
  choose A hA hdom using fun x : M =>
    KahlerDomination.exists_isSemipositive_add_smul (ddcForm (H x) (hH x))
      omega.form omega.isHermitian
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover S hS
    (fun x _ => mem_iUnion.mpr ⟨x, hxS x⟩)
  let C : ℝ := 1 + ∑ x ∈ s, A x
  have hsum : 0 ≤ ∑ x ∈ s, A x := Finset.sum_nonneg fun x _ => (hA x).le
  have hC : 0 < C := by dsimp only [C]; linarith
  have hAC : ∀ x ∈ s, A x ≤ C := by
    intro x hx
    have hi := Finset.single_le_sum (fun y _ => (hA y).le) hx
    dsimp only [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro t ht htC
  have hqu := isGlobalQuasiPshPotential_nonneg_mul hu ht.le
  apply isFormPSH_of_approximate_local_psh omega.form omega.isTypeOneOne
    (fun x => (t : EReal) * u x) hqu
  intro e z hz ε hε
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hs (mem_univ (e.val.symm z)))
  obtain ⟨his, hzS⟩ := mem_iUnion.mp hi
  let W : Opens (ComplexModel (m + 1)) :=
    ⟨e.val.target ∩ e.val.symm ⁻¹' S i, e.val.isOpen_inter_preimage_symm (hS i)⟩
  have hW : W ≤ chartTarget e := inter_subset_left
  let q : ComplexModel (m + 1) → ℝ := fun y => (-t) • H i (e.val.symm y)
  have hHi : ContDiffOn ℝ ∞ (fun y => H i (e.val.symm y)) W :=
    (hH i e).mono inter_subset_left
  have hq : ContDiffOn ℝ ∞ q W := hHi.const_smul (-t)
  refine ⟨W, hW, q, ⟨hz, hzS⟩, hq, ?_, ?_⟩
  · intro y hy
    have hp := hpS i e y hy.1 hy.2
    apply (hp.const_mul ht).congr
    exact Eventually.of_forall fun a => by
      change (t : EReal) * (u (e.val.symm a) - (H i (e.val.symm a) : EReal)) =
        (t : EReal) * u (e.val.symm a) + (((-t) * H i (e.val.symm a) : ℝ) : EReal)
      rw [sub_eq_add_neg, ← EReal.coe_neg,
        EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr ht.le) (EReal.coe_ne_top t),
        ← EReal.coe_mul]
      congr 1
      congr 1
      ring
  · intro y hy v
    have hAi : t * A i ≤ 1 :=
      (mul_le_mul_of_nonneg_left (hAC i his) ht.le).trans htC
    have hwpos := omega.isSemipositive e y hy.1 v
    have hlower := hdom i e y hy.1 v
    change 0 ≤ smoothDDC (fun a => H i (e.val.symm a)) y ![v, Complex.I • v] +
      A i * omega.form.coeff e y ![v, Complex.I • v] at hlower
    have hmul := mul_nonneg ht.le hlower
    have hsmall := mul_le_mul_of_nonneg_right hAi hwpos
    have hqbound : smoothDDC q y ![v, Complex.I • v] ≤
        omega.form.coeff e y ![v, Complex.I • v] := by
      dsimp only [q]
      rw [smoothDDC_smul W.isOpen hHi (-t) hy]
      change (-t) * smoothDDC (fun a => H i (e.val.symm a)) y ![v, Complex.I • v] ≤
        omega.form.coeff e y ![v, Complex.I • v]
      nlinarith
    exact hqbound.trans (le_add_of_nonneg_right (mul_nonneg hε.le (sq_nonneg ‖v‖)))

/-- In particular, a strictly positive scaling always exists. -/
theorem exists_pos_mul_isHermitianPSH (omega : Background (m + 1) M)
    {u : M → EReal} (hu : IsGlobalQuasiPshPotential (n := m + 1) u) :
    ∃ t : ℝ, 0 < t ∧ IsHermitianPSH omega (fun x => (t : EReal) * u x) := by
  obtain ⟨C, hC, h⟩ := exists_pos_scaling_constant omega hu
  exact ⟨C⁻¹, inv_pos.mpr hC, h _ (inv_pos.mpr hC) (by rw [inv_mul_cancel₀ hC.ne'])⟩

end SGPT.PSH.Hermitian
