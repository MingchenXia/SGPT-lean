import SGPT.Foundations.Analysis.Pending.LocalCurrentDensityMatrix
import SGPT.Foundations.Analysis.Pending.RegularBranchKahlerJacobian

set_option autoImplicit false

/-! Actual local mollifier tests of an arbitrary original positive current
produce its full real (1,1) coefficient form. The full natural mathematical
statements and ENTIRE proofs precede this source. Common AE form/matrix/top
density convergence is produced, not passed as an input. No analytic type,
global regularization, uniform negative bound or finite mass is assumed. -/

noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology Distributions BigOperators ComplexOrder MatrixOrder

namespace SGPT.Foundations.Analysis.Pending.LocalPositiveCurrentMollifiedACForm
open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalCurrentLebesgue LocalCurrentSemicontinuity LocalCurrentDeterminant
  LocalCurrentDensityMatrix TopDegreeDensity

attribute [local instance] addCommGroupFormSpan

variable {m : ℕ} {U : Opens (ComplexModel (m + 1))}

private def mollifierTest (U : Opens (ComplexModel (m + 1))) (k : ℕ)
    (x : ComplexModel (m + 1)) : 𝓓(U, ℝ) := by
  classical
  exact if h : closedBall x (bump (m + 1) k).rOut ⊆ U then bumpTest U k x h else 0

private theorem mollifierTest_nonneg (k : ℕ) (x y : ComplexModel (m + 1)) :
    0 ≤ mollifierTest U k x y := by
  classical
  unfold mollifierTest
  split_ifs with h
  · exact mol_nonneg k x y
  · exact le_rfl

/-- The actual complementary-basis reconstruction from genuine mollifier tests,
with the zero test when the supporting ball is not contained in the domain. -/
def mollifiedForm (T : LocalProductCurrent (m + 1) U m) (k : ℕ)
    (x : ComplexModel (m + 1)) : RealForm (m + 1) 2 :=
  ∑ i, T (formBasis (m + 1) m i) (mollifierTest U k x) • dualForm m i

private def evaluation (T : LocalProductCurrent (m + 1) U m) (φ : 𝓓(U, ℝ)) :
    formSpan (m + 1) m →ₗ[ℝ] ℝ where
  toFun γ := T γ φ
  map_add' γ δ := by simp
  map_smul' c γ := by simp

private theorem mollifiedForm_rep (T : LocalProductCurrent (m + 1) U m)
    (k : ℕ) (x : ComplexModel (m + 1)) (γ : formSpan (m + 1) m) :
    T γ (mollifierTest U k x) =
      topDensity (coordinateWedge (γ : RealForm (m + 1) (2 * m))
        (mollifiedForm T k x)) := by
  classical
  have hexpand : T γ (mollifierTest U k x) =
      ∑ i, (formBasis (m + 1) m).repr γ i *
        T (formBasis (m + 1) m i) (mollifierTest U k x) := by
    change evaluation T (mollifierTest U k x) γ =
      ∑ i, (formBasis (m + 1) m).repr γ i *
        evaluation T (mollifierTest U k x) (formBasis (m + 1) m i)
    conv_lhs => rw [← (formBasis (m + 1) m).sum_repr γ,map_sum]
    simp only [map_smul,smul_eq_mul]
  rw [hexpand,← wedgeDensity_apply,mollifiedForm,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,wedgeDensity_apply,topDensity_dualForm,smul_eq_mul,mul_comm]

/-- Original positivity internally makes every actual mollified coefficient
form type (1,1) with a positive semidefinite normalized Hermitian matrix. -/
theorem mollifiedForm_isPositive {T : LocalProductCurrent (m + 1) U m}
    (hT : IsPositive T) (k : ℕ) (x : ComplexModel (m + 1)) :
    IsOneOne (mollifiedForm T k x) ∧
      (normalizedHermitianMatrix (mollifiedForm T k x)).PosSemidef := by
  classical
  have h11 : IsOneOne (mollifiedForm T k x) :=
    isOneOne_sum _ fun i _ => isOneOne_smul (isOneOne_dualForm i) _
  refine ⟨h11,posSemidef_of_nonneg (L := evaluation T (mollifierTest U k x)) ?_ h11 ?_⟩
  · intro γ hγ
    exact hT.positiveDistribution hγ _ (mollifierTest_nonneg k x)
  · exact mollifiedForm_rep T k x

/-- One internally produced full-measure set gives convergence of the actual
entire form, the actual normalized matrix, and genuine exterior-top density. -/
theorem ae_tendsto_mollifiedForm_matrix_density
    {T : LocalProductCurrent (m + 1) U m} (hT : IsPositive T) :
    ∀ᵐ x ∂volume, x ∈ U →
      Tendsto (fun k => mollifiedForm T k x) atTop (𝓝 (acForm hT x)) ∧
      Tendsto (fun k => normalizedHermitianMatrix (mollifiedForm T k x)) atTop
        (𝓝 (acMatrix hT x)) ∧
      Tendsto (fun k => actualTopPowerDensity (mollifiedForm T k x)) atTop
        (𝓝 (actualTopPowerDensity (acForm hT x))) := by
  classical
  have hall := ae_all_iff.mpr fun i =>
    ae_tendsto_apply_bumpTest hT (formBasis (m + 1) m i)
  filter_upwards [hall] with x hx hxU
  have hscalar (i : Fin (Module.finrank ℝ (formSpan (m + 1) m))) :
      Tendsto (fun k => T (formBasis (m + 1) m i) (mollifierTest U k x)) atTop
        (𝓝 (acWeight hT x * hT.density (formBasis (m + 1) m i) x)) := by
    have h := hx i hxU
    have hd : densityForm hT x (formBasis (m + 1) m i) =
        hT.density (formBasis (m + 1) m i) x := by
      simp [densityForm_apply,Finsupp.single_apply]
    rw [hd] at h
    refine h.congr' ?_
    filter_upwards [eventually_closedBall_subset hxU] with k hk
    rw [mollifierTest,dif_pos hk,apply_bumpTest hT]
  have hform : Tendsto (fun k => mollifiedForm T k x) atTop (𝓝 (acForm hT x)) := by
    rw [acForm_eq_sum hT]
    exact tendsto_finsetSum Finset.univ fun i _ => (hscalar i).smul_const (dualForm m i)
  have hmatrix : Continuous (normalizedHermitianMatrix : RealForm (m + 1) 2 →
      Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) := by
    unfold normalizedHermitianMatrix
    fun_prop
  exact ⟨hform,(hmatrix.tendsto _).comp hform,
    ((RegularBranchKahlerJacobian.RegularPatch.continuous_actualTopPowerDensity
      (m + 1)).tendsto _).comp hform⟩

end SGPT.Foundations.Analysis.Pending.LocalPositiveCurrentMollifiedACForm
