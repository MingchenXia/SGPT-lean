import SGPT.PSH.OriginalGlobalOneZeroForms

/-! Actual global complex scalar and (1,0)-tensor algebra on original atlases. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.ComplexCurrentBridge
open Set Filter Finset
open SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.ComplexCurrentDraft
open scoped Topology ContDiff
universe u
variable {X : Type u} [TopologicalSpace X] (A : VariableComplexAtlas X)

/-- Genuine complex-valued all-original-chart smooth scalar function. -/
def OriginalComplexSmooth (a : X → ℂ) : Prop :=
  ∀ i : A.Index,ContDiffOn ℝ ∞ (a ∘ (A.chart i).symm) (A.chart i).target

/-- Real and imaginary globally smooth functions supply a genuine smooth
complex scalar on the SAME original manifold, without an output flag. -/
theorem complex_smooth_of_real_pair (f g : X → ℝ)
    (hf : OriginalRealSmooth A f) (hg : OriginalRealSmooth A g) :
    OriginalComplexSmooth A (fun x => (f x : ℂ)+Complex.I*(g x : ℂ)) := by
  intro i
  exact ((Complex.ofRealCLM.contDiff.comp_contDiffOn (hf i)).add
    (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn (hg i))))

/-- Actual global source (1,0) form multiplication by a genuine smooth
GLOBAL complex scalar. All smoothness and tensor overlap fields are proved. -/
def smoothScalarOneZero (a : X → ℂ) (ha : OriginalComplexSmooth A a)
    (B : OriginalGlobalOneZeroForm A) : OriginalGlobalOneZeroForm A where
  coeff i z := a ((A.chart i).symm z) • B.coeff i z
  smooth i := (ha i).smul (B.smooth i)
  compatible i j z hz v := by
    have hj : (A.chart i).symm z∈(A.chart j).source := hz.2
    change a ((A.chart i).symm z)*B.coeff i z v=
      a ((A.chart j).symm ((A.chart j) ((A.chart i).symm z)))*
        B.coeff j (((A.chart i).symm.trans (A.chart j)) z)
          (fderiv ℝ ((A.chart i).symm.trans (A.chart j)) z v)
    rw [(A.chart j).left_inv hj,B.compatible i j z hz v]

/-- Exact physical coefficient of the actual scalar multiple. -/
theorem smoothScalarOneZero_coeff (a : X → ℂ) (ha : OriginalComplexSmooth A a)
    (B : OriginalGlobalOneZeroForm A) (i : A.Index) (z : ComplexModel (A.dimension i)) :
    (smoothScalarOneZero A a ha B).coeff i z=a ((A.chart i).symm z) • B.coeff i z := rfl

/-- Actual finite sum of original global covector fields. -/
def finiteSumOneZero {d : ℕ} (B : Fin d → OriginalGlobalOneZeroForm A) :
    OriginalGlobalOneZeroForm A where
  coeff i z := ∑ j, (B j).coeff i z
  smooth i := ContDiffOn.sum (fun j _ => (B j).smooth i)
  compatible i j z hz v := by
    simpa only [_root_.sum_apply] using
      (Finset.sum_congr rfl (fun a (_ : a∈Finset.univ) => (B a).compatible i j z hz v))

/-- Exact physical coefficient readback of finite actual tensor sums. -/
theorem finiteSumOneZero_coeff {d : ℕ} (B : Fin d → OriginalGlobalOneZeroForm A)
    (i : A.Index) (z : ComplexModel (A.dimension i)) :
    (finiteSumOneZero A B).coeff i z=∑ j,(B j).coeff i z := rfl

end SGPT.PSH.ComplexCurrentBridge
