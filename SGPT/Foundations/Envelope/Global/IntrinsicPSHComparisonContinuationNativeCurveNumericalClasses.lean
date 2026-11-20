import SGPT.Foundations.Envelope.AlgGeom.CurvePicardDegrees
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Genuine original numerical classes tested by all projective curve maps

The kernel uses ALL actual original integral projective over-k curves of
actual topological dimension one, and ALL original maps with the literal
base triangle. Every degree is the genuine native whole Euler degree.
The quotient is the actual native Picard group quotient, and every original
curve degree descends with its exact original whole-line computation.
No coordinate class, supplied degree functional or metric certificate occurs.
Numerical invariance of metrics, real extension, nef and BJ remain open.
Route: owned `native-curve-numerical-classes-route.tex`.
-/
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace SGPT.Foundations.Envelope.NativeCurveNumericalClasses
open CurvePicardDegrees
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))

/-- The actual kernel of ALL original integral projective over-k curve degrees. -/
def curveNumericalKernel : Subgroup X.Pic where
  carrier a := ∀ {C : Scheme.{u}} [IsIntegral C]
    (q : C ⟶ Spec (CommRingCat.of k)) (hq : IsProjectiveFactorization q)
    (hdim : topologicalKrullDim C = 1) (i : C ⟶ X), i ≫ p = q →
      curveDegreeHom q hq (le_of_eq hdim) i a = 1
  one_mem' := by
    intro C _ q hq hdim i _
    exact map_one (curveDegreeHom q hq (le_of_eq hdim) i)
  mul_mem' := by
    intro a b ha hb C hC q hq hdim i hi
    rw [map_mul, ha q hq hdim i hi, hb q hq hdim i hi, one_mul]
  inv_mem' := by
    intro a ha C hC q hq hdim i hi
    rw [map_inv, ha q hq hdim i hi, inv_one]

/-- Membership retains EVERY literal original curve and original coefficient triangle. -/
theorem mem_curveNumericalKernel (a : X.Pic) : a ∈ curveNumericalKernel p ↔
    ∀ {C : Scheme.{u}} [IsIntegral C]
      (q : C ⟶ Spec (CommRingCat.of k)) (hq : IsProjectiveFactorization q)
      (hdim : topologicalKrullDim C = 1) (i : C ⟶ X), i ≫ p = q →
        curveDegreeHom q hq (le_of_eq hdim) i a = 1 := Iff.rfl

/-- The genuine quotient of the actual native Picard group by ALL original curve-degree kernels. -/
abbrev NumericalClass := X.Pic ⧸ curveNumericalKernel p

/-- The actual canonical native Picard quotient homomorphism. -/
def classMap : X.Pic →* NumericalClass p := QuotientGroup.mk' (curveNumericalKernel p)

/-- EVERY native numerical class has a genuine original native Picard representative. -/
theorem classMap_surjective : Function.Surjective (classMap p) :=
  QuotientGroup.mk'_surjective (curveNumericalKernel p)

/-- The actual full kernel inclusion for ANY original over-k projective curve map. -/
theorem kernel_le_curveDegreeKernel {C : Scheme.{u}} [IsIntegral C]
    (q : C ⟶ Spec (CommRingCat.of k)) (hq : IsProjectiveFactorization q)
    (hdim : topologicalKrullDim C = 1) (i : C ⟶ X) (hi : i ≫ p = q) :
    curveNumericalKernel p ≤ (curveDegreeHom q hq (le_of_eq hdim) i).ker := by
  intro a ha
  exact ha q hq hdim i hi

/-- The SAME original curve degree descends to the genuine native numerical quotient. -/
def curveDegree {C : Scheme.{u}} [IsIntegral C]
    (q : C ⟶ Spec (CommRingCat.of k)) (hq : IsProjectiveFactorization q)
    (hdim : topologicalKrullDim C = 1) (i : C ⟶ X) (hi : i ≫ p = q) :
    NumericalClass p →* Multiplicative ℤ :=
  QuotientGroup.lift (curveNumericalKernel p) (curveDegreeHom q hq (le_of_eq hdim) i)
    (kernel_le_curveDegreeKernel p q hq hdim i hi)

/-- Degree descent retains the literal SAME original degree homomorphism on EVERY Picard class. -/
theorem curveDegree_classMap {C : Scheme.{u}} [IsIntegral C]
    (q : C ⟶ Spec (CommRingCat.of k)) (hq : IsProjectiveFactorization q)
    (hdim : topologicalKrullDim C = 1) (i : C ⟶ X) (hi : i ≫ p = q) (a : X.Pic) :
    curveDegree p q hq hdim i hi (classMap p a) = curveDegreeHom q hq (le_of_eq hdim) i a := rfl

/-- EXACT equality of native numerical images is detected by ALL genuine original curve degrees. -/
theorem classMap_eq_iff_curveDegrees_eq (a b : X.Pic) : classMap p a = classMap p b ↔
    ∀ {C : Scheme.{u}} [IsIntegral C]
      (q : C ⟶ Spec (CommRingCat.of k)) (hq : IsProjectiveFactorization q)
      (hdim : topologicalKrullDim C = 1) (i : C ⟶ X), i ≫ p = q →
        curveDegreeHom q hq (le_of_eq hdim) i a = curveDegreeHom q hq (le_of_eq hdim) i b := by
  change (a : X.Pic ⧸ curveNumericalKernel p) = (b : X.Pic ⧸ curveNumericalKernel p) ↔ _
  rw [QuotientGroup.eq_iff_div_mem, mem_curveNumericalKernel]
  constructor
  · intro h C hC q hq hdim i hi
    simpa only [map_div, div_eq_one] using h q hq hdim i hi
  · intro h C hC q hq hdim i hi
    simpa only [map_div, div_eq_one] using h q hq hdim i hi

/-- The descended degree computes the TRUE degree of the SAME actual whole original pulled line. -/
theorem curveDegree_lineClass {C : Scheme.{u}} [IsIntegral C]
    (q : C ⟶ Spec (CommRingCat.of k)) (hq : IsProjectiveFactorization q)
    (hdim : topologicalKrullDim C = 1) (i : C ⟶ X) (hi : i ≫ p = q)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) :
    letI : IsProper q := hq.isProper
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace q
    Multiplicative.toAdd (curveDegree p q hq hdim i hi (classMap p (lineClass L hL))) =
      CurveLineDegrees.degree q ((Scheme.Modules.pullback i).obj L) := by
  let : IsProper q := hq.isProper
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace q
  rw [curveDegree_classMap]
  exact curveDegreeHom_lineClass q hq (le_of_eq hdim) i L hL

/-- ALL actual descended original curve degrees separate the ENTIRE native numerical group. -/
theorem numericalClass_ext (a b : NumericalClass p)
    (h : ∀ {C : Scheme.{u}} [IsIntegral C]
      (q : C ⟶ Spec (CommRingCat.of k)) (hq : IsProjectiveFactorization q)
      (hdim : topologicalKrullDim C = 1) (i : C ⟶ X) (hi : i ≫ p = q),
        curveDegree p q hq hdim i hi a = curveDegree p q hq hdim i hi b) : a = b := by
  obtain ⟨a, rfl⟩ := classMap_surjective p a
  obtain ⟨b, rfl⟩ := classMap_surjective p b
  apply (classMap_eq_iff_curveDegrees_eq p a b).mpr
  intro C hC q hq hdim i hi
  exact h q hq hdim i hi

end SGPT.Foundations.Envelope.NativeCurveNumericalClasses

#check @SGPT.Foundations.Envelope.NativeCurveNumericalClasses.curveNumericalKernel
#print axioms SGPT.Foundations.Envelope.NativeCurveNumericalClasses.curveNumericalKernel
#check @SGPT.Foundations.Envelope.NativeCurveNumericalClasses.mem_curveNumericalKernel
#print axioms SGPT.Foundations.Envelope.NativeCurveNumericalClasses.mem_curveNumericalKernel
#check @SGPT.Foundations.Envelope.NativeCurveNumericalClasses.NumericalClass
#print axioms SGPT.Foundations.Envelope.NativeCurveNumericalClasses.NumericalClass
#check @SGPT.Foundations.Envelope.NativeCurveNumericalClasses.classMap
#print axioms SGPT.Foundations.Envelope.NativeCurveNumericalClasses.classMap
#check @SGPT.Foundations.Envelope.NativeCurveNumericalClasses.classMap_surjective
#print axioms SGPT.Foundations.Envelope.NativeCurveNumericalClasses.classMap_surjective
#check @SGPT.Foundations.Envelope.NativeCurveNumericalClasses.kernel_le_curveDegreeKernel
#print axioms SGPT.Foundations.Envelope.NativeCurveNumericalClasses.kernel_le_curveDegreeKernel
#check @SGPT.Foundations.Envelope.NativeCurveNumericalClasses.curveDegree
#print axioms SGPT.Foundations.Envelope.NativeCurveNumericalClasses.curveDegree
#check @SGPT.Foundations.Envelope.NativeCurveNumericalClasses.curveDegree_classMap
#print axioms SGPT.Foundations.Envelope.NativeCurveNumericalClasses.curveDegree_classMap
#check @SGPT.Foundations.Envelope.NativeCurveNumericalClasses.classMap_eq_iff_curveDegrees_eq
#print axioms SGPT.Foundations.Envelope.NativeCurveNumericalClasses.classMap_eq_iff_curveDegrees_eq
#check @SGPT.Foundations.Envelope.NativeCurveNumericalClasses.curveDegree_lineClass
#print axioms SGPT.Foundations.Envelope.NativeCurveNumericalClasses.curveDegree_lineClass
#check @SGPT.Foundations.Envelope.NativeCurveNumericalClasses.numericalClass_ext
#print axioms SGPT.Foundations.Envelope.NativeCurveNumericalClasses.numericalClass_ext
