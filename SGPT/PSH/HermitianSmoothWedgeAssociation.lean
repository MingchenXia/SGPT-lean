import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorWedgeAssociation
import SGPT.Foundations.Analysis.Pending.NaturalOriginalGradedExteriorProduct

/-! Associativity of the actual smooth-current wedge for arbitrary even degrees.
The forms may be nonclosed; their values have their indicated complex types. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianSmoothWedgeAssociation

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorSmooth LocalBedfordTaylorForms
  LocalCurrentLebesgue ConstantFormProducts ProductTestForms
  NaturalOriginalGradedExteriorProduct

variable {n : ℕ} {U : Opens (ComplexModel n)}

/-- The prescribed-degree exterior product is a continuous bilinear map. -/
def wedgeToCLM {p q m : ℕ} (h : p + q = m) :
    RealForm n p →L[ℝ] RealForm n q →L[ℝ] RealForm n m :=
  haveI := realForm_finiteDimensional (n := n) p
  haveI := realForm_finiteDimensional (n := n) q
  LinearMap.toContinuousLinearMap
    { toFun := fun A => LinearMap.toContinuousLinearMap (wedgeToBilin n h A)
      map_add' := fun A B => by ext C : 1; exact wedgeTo_add_left h A B C
      map_smul' := fun c A => by ext C : 1; exact wedgeTo_smul_left h c A C }

/-- Smooth forms have their actual smooth prescribed-degree exterior product. -/
theorem contDiffOn_wedgeTo {p q m : ℕ} (h : p + q = m)
    {α : ComplexModel n → RealForm n p} {β : ComplexModel n → RealForm n q}
    (hα : ContDiffOn ℝ ∞ α U) (hβ : ContDiffOn ℝ ∞ β U) :
    ContDiffOn ℝ ∞ (fun z => wedgeTo h (α z) (β z)) U :=
  (((wedgeToCLM h).contDiff.comp_contDiffOn hα).clm_apply hβ).congr fun _ _ => rfl

/-- Any two actual forms of even degree commute, including degree zero. -/
theorem wedgeTo_even_comm {k l m : ℕ} (h : 2*k+2*l=m) (h' : 2*l+2*k=m)
    (A : RealForm n (2*k)) (B : RealForm n (2*l)) :
    wedgeTo h A B = wedgeTo h' B A := by
  rw [wedgeTo_graded_comm h h']
  have he : (-1 : ℝ) ^ ((2*k)*(2*l)) = 1 := by
    rw [show (2*k)*(2*l) = 2*(k*(2*l)) by ring, pow_mul]
    norm_num
  rw [he, one_smul]

/-- Associativity of the genuine smooth-form wedge on arbitrary currents. -/
theorem wedgeForm_wedge {r k l m : ℕ} (h : r + l + k = m)
    (T : LocalProductCurrent n U m) {α : ComplexModel n → RealForm n (2 * k)}
    {β : ComplexModel n → RealForm n (2 * l)} (hα : ContDiffOn ℝ ∞ α U)
    (hβ : ContDiffOn ℝ ∞ β U) (hαS : ∀ x ∈ U, α x ∈ formSpan n k)
    (hβS : ∀ x ∈ U, β x ∈ formSpan n l) :
    wedgeForm rfl (wedgeForm h T hα) hβ =
      wedgeForm (by omega : r + (k + l) = m) T (contDiffOn_wedgeTo (by omega : 2*k+2*l=2*(k+l)) hα hβ) := by
  classical
  have h' : r + (k + l) = m := by omega
  have hηS : ∀ x ∈ U, wedgeTo (by omega : 2*k+2*l=2*(k+l)) (α x) (β x) ∈ formSpan n (k + l) :=
    fun x hx => wedgeTo_mem_formSpan (hαS x hx) (hβS x hx) (by omega)
  ext γ φ
  let X := fun p : Fin (Module.finrank ℝ (formSpan n l)) ×
      Fin (Module.finrank ℝ (formSpan n k)) =>
    wedgeSpan n h (wedgeSpan n rfl γ (formBasis n l p.1)) (formBasis n k p.2)
  let ψ := fun p : Fin (Module.finrank ℝ (formSpan n l)) ×
      Fin (Module.finrank ℝ (formSpan n k)) =>
    mulSmoothOnCLM (contDiffOn_formCoeff hα p.2)
      (mulSmoothOnCLM (contDiffOn_formCoeff hβ p.1) φ)
  let Y := fun i : Fin (Module.finrank ℝ (formSpan n (k + l))) =>
    wedgeSpan n h' γ (formBasis n (k + l) i)
  let χ := fun i : Fin (Module.finrank ℝ (formSpan n (k + l))) => mulSmoothOnCLM
    (contDiffOn_formCoeff (k := k + l) (contDiffOn_wedgeTo (by omega : 2*k+2*l=2*(k+l)) hα hβ) i) φ
  have hpoint : ∀ x ∈ U, ∑ p, ψ p x • (X p : RealForm n (2 * m)) =
      ∑ i, χ i x • (Y i : RealForm n (2 * m)) := by
    intro x hx
    have e := sum_mulSmoothOnCLM_smul_wedgeSpan h'
      (contDiffOn_wedgeTo (by omega : 2*k+2*l=2*(k+l)) hα hβ) hηS γ φ (by omega) hx
    change _ = ∑ i, mulSmoothOnCLM
      (contDiffOn_formCoeff (contDiffOn_wedgeTo (by omega : 2*k+2*l=2*(k+l)) hα hβ) i) φ x •
        (wedgeSpan n h' γ (formBasis n (k + l) i) : RealForm n (2 * m))
    rw [e, Fintype.sum_prod_type]
    have ei : ∀ j, ∑ i,
        mulSmoothOnCLM (contDiffOn_formCoeff hα i)
            (mulSmoothOnCLM (contDiffOn_formCoeff hβ j) φ) x •
          (wedgeSpan n h (wedgeSpan n rfl γ (formBasis n l j)) (formBasis n k i) :
            RealForm n (2 * m)) =
        mulSmoothOnCLM (contDiffOn_formCoeff hβ j) φ x •
          wedgeTo (by omega : 2 * (r + l) + 2 * k = 2 * m)
            (wedgeSpan n rfl γ (formBasis n l j) : RealForm n (2 * (r + l))) (α x) :=
      fun j => sum_mulSmoothOnCLM_smul_wedgeSpan h hα hαS
        (wedgeSpan n rfl γ (formBasis n l j))
        (mulSmoothOnCLM (contDiffOn_formCoeff hβ j) φ) (by omega) hx
    change (∑ j, ∑ i,
        mulSmoothOnCLM (contDiffOn_formCoeff hα i)
            (mulSmoothOnCLM (contDiffOn_formCoeff hβ j) φ) x •
          (wedgeSpan n h (wedgeSpan n rfl γ (formBasis n l j)) (formBasis n k i) :
            RealForm n (2 * m))) = _
    simp_rw [ei, ← wedgeTo_smul_left]
    rw [← wedgeTo_sum_left, sum_mulSmoothOnCLM_smul_wedgeSpan rfl hβ hβS γ φ (by omega) hx,
      wedgeTo_smul_left,
      wedgeTo_assoc (by omega : 2*r+2*l=2*(r+l))
        (by omega : 2*(r+l)+2*k=2*m) (by omega : 2*l+2*k=2*(k+l))
        (by omega : 2*r+2*(k+l)=2*m)]
    rw [wedgeTo_even_comm (by omega : 2*l+2*k=2*(k+l))
      (by omega : 2*k+2*l=2*(k+l)) (β x) (α x)]
    rw [wedgeTo_smul_left]
  have he := sum_apply_eq_of_forall T X ψ Y χ hpoint
  simpa only [X, ψ, Y, χ, Fintype.sum_prod_type, wedgeForm_apply] using he

end SGPT.PSH.HermitianSmoothWedgeAssociation
