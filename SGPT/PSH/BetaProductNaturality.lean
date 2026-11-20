import SGPT.PSH.SmoothVariableBetaTests
import SGPT.PSH.OriginalGlobalOneZeroForms

/-! ENTIRE actual derivative tensor naturality of source beta products. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.ComplexCurrentDraft
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
open SGPT.Foundations.Analysis.Pending.TopDegreeDensity
open SGPT.PSH.BookCurrent SGPT.PSH.VariableComplexAtlas

/-- Literal i beta wedge bar beta commutes with actual complex pullback. -/
theorem oneOneSquare_comp_complex {m n : ℕ} (b : ComplexModel n →L[ℂ] ℂ)
    (L : ComplexModel m →L[ℂ] ComplexModel n) :
    oneOneSquare (b.comp L)=(oneOneSquare b).compContinuousLinearMap (L.restrictScalars ℝ) := by
  ext v
  have hv : v=![v 0,v 1] := by ext j; fin_cases j <;> rfl
  rw [hv]
  change oneOneSquare (b.comp L) ![v 0,v 1]=oneOneSquare b (fun j => L (![v 0,v 1] j))
  have hvec : (fun j : Fin 2 => L (![v 0,v 1] j))=![L (v 0),L (v 1)] := by
    ext j
    fin_cases j <;> rfl
  rw [hvec]
  rw [oneOneSquare_apply,oneOneSquare_apply]
  rfl

/-- Full actual source product tensor pullback for EVERY degree and dimensions. -/
theorem betaProduct_comp_complex {m n : ℕ} : ∀ (p : ℕ)
    (beta : Fin p → ComplexModel n →L[ℂ] ℂ) (L : ComplexModel m →L[ℂ] ComplexModel n),
    betaProduct (fun j => (beta j).comp L)=
      (betaProduct beta).compContinuousLinearMap (L.restrictScalars ℝ)
  | 0,_,_ => by ext v; rfl
  | p+1,beta,L => by
    change coordinateWedge (betaProduct (fun j : Fin p => (beta j.castSucc).comp L))
        (oneOneSquare ((beta (Fin.last p)).comp L))=
      (coordinateWedge (betaProduct (fun j : Fin p => beta j.castSucc))
        (oneOneSquare (beta (Fin.last p)))).compContinuousLinearMap (L.restrictScalars ℝ)
    rw [betaProduct_comp_complex p,oneOneSquare_comp_complex,coordinateWedge_compContinuousLinearMap]

universe u
variable {X : Type u} [TopologicalSpace X] (A : VariableComplexAtlas X)

/-- Actual GLOBAL source beta fields give the ENTIRE beta-product tensor
transition law, proved from genuine holomorphic derivatives and wedge algebra. -/
theorem original_global_betaProduct_compatible {p : ℕ}
    (beta : Fin p → OriginalGlobalOneZeroForm A) (i j : A.Index)
    {z : ComplexModel (A.dimension i)}
    (hz : z∈((A.chart i).symm.trans (A.chart j)).source) :
    betaProduct (fun a => (beta a).coeff i z)=
      (betaProduct (fun a => (beta a).coeff j (((A.chart i).symm.trans (A.chart j)) z))).compContinuousLinearMap (fderiv ℝ ((A.chart i).symm.trans (A.chart j)) z) := by
  let F := (A.chart i).symm.trans (A.chart j)
  let L := fderiv ℂ F z
  have hRF : fderiv ℝ F z=L.restrictScalars ℝ :=
    ((A.holomorphic i j).differentiableAt (F.open_source.mem_nhds hz)).fderiv_restrictScalars ℝ
  have hbeta : (fun a => (beta a).coeff i z)=
      (fun a => ((beta a).coeff j (F z)).comp L) := by
    funext a
    ext v
    have h := (beta a).compatible i j z hz v
    rw [hRF] at h
    exact h
  rw [hbeta,betaProduct_comp_complex,hRF]

end SGPT.PSH.ComplexCurrentDraft
