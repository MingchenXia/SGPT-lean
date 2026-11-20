import SGPT.Toric.MonomialProjectiveCompactness
import SGPT.Foundations.Schemes.PolynomialProjectiveAnalyticCompactness
import SGPT.Foundations.Schemes.PolynomialProjectiveProper

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open scoped Topology
attribute [local instance] MvPolynomial.gradedAlgebra

variable (d : ℕ)
local notation "V" => Fin (d + 1) → ℂ
local notation "Vnz" => {v : V // v ≠ 0}
local notation "P" => Projectivization ℂ V
local notation "Q" => SchemeComplexPoint (polynomialProjStructureMap ℂ d)

@[instance_reducible] private def nativePointTopology : TopologicalSpace Q :=
  schemeAnalyticPointTopology (polynomialProjStructureMap ℂ d)
attribute [local instance] monomialProjectiveTopology nativePointTopology

/-- Actual scalar-related homogeneous vectors have the very same original
native scheme point, using its genuine coordinate chart/scaling mothers. -/
theorem nativeProjectiveVectorPoint_eq_of_smul (v w : Vnz) (c : ℂˣ)
    (h : c • v.val = w.val) :
    polynomialProjNonzeroVectorPoint d v = polynomialProjNonzeroVectorPoint d w := by
  obtain ⟨i, hi⟩ := polynomialProjVector_exists_nonzero_coordinate d v.val v.property
  have hc : (c : ℂ) • v.val = w.val := h
  have hwi : w.val i ≠ 0 := by
    rw [← hc]
    exact mul_ne_zero (Units.ne_zero c) hi
  rw [polynomialProjNonzeroVectorPoint_eq_chart d v i hi,
    polynomialProjNonzeroVectorPoint_eq_chart d w i hwi,
    ← hc, polynomialProjVectorChartPoint_smul d i v.val (c : ℂ) (Units.ne_zero c)]

private theorem nativeVectorPoint_coordinate_vanishing (v : Vnz) (j : Fin (d + 1)) :
    MvPolynomial.X j ∈ (schemeComplexPointImage (polynomialProjStructureMap ℂ d)
      (polynomialProjNonzeroVectorPoint d v)).asHomogeneousIdeal ↔ v.val j = 0 := by
  obtain ⟨i, hi⟩ := polynomialProjVector_exists_nonzero_coordinate d v.val v.property
  rw [polynomialProjNonzeroVectorPoint_eq_chart d v i hi]
  simpa only [MvPolynomial.eval_X] using
    polynomialProjVectorChartPoint_mem_homogeneous_positive d i v.val hi 1 (by decide)
      (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X ℂ j)

/-- Equality of actual native scheme points has precisely the original scalar
fiber relation. The shared affine denominator is produced before ratio readback. -/
theorem nativeProjectiveVectorPoint_eq_iff (v w : Vnz) :
    polynomialProjNonzeroVectorPoint d v = polynomialProjNonzeroVectorPoint d w ↔
      Projectivization.mk ℂ v.val v.property = Projectivization.mk ℂ w.val w.property := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := polynomialProjVector_exists_nonzero_coordinate d v.val v.property
    have hwi : w.val i ≠ 0 := by
      intro hzero
      have hv := nativeVectorPoint_coordinate_vanishing d v i
      rw [h] at hv
      exact hi (hv.mp ((nativeVectorPoint_coordinate_vanishing d w i).mpr hzero))
    have hchart : polynomialProjVectorChartPoint d i v.val = polynomialProjVectorChartPoint d i w.val := by
      simpa only [polynomialProjNonzeroVectorPoint_eq_chart d v i hi,
        polynomialProjNonzeroVectorPoint_eq_chart d w i hwi] using h
    have hval := congrArg Subtype.val hchart
    rw [polynomialProjVectorChartPoint_val, polynomialProjVectorChartPoint_val] at hval
    have hspec := (cancel_mono (polynomialProjCoordinateImmersion ℂ d i)).mp hval
    have hratio (j : Fin (d + 1)) : v.val j / v.val i = w.val j / w.val i := by
      have he := congrArg (fun f => (Spec.preimage f).hom (polynomialProjCoordinateRatio ℂ d i j)) hspec
      rw [Spec.preimage_map, Spec.preimage_map] at he
      change polynomialProjVectorChartAlgebraPoint d i v.val (polynomialProjCoordinateRatio ℂ d i j) =
        polynomialProjVectorChartAlgebraPoint d i w.val (polynomialProjCoordinateRatio ℂ d i j) at he
      rwa [polynomialProjVectorChartAlgebraPoint_ratio d i j v.val hi,
        polynomialProjVectorChartAlgebraPoint_ratio d i j w.val hwi] at he
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    refine ⟨v.val i / w.val i, ?_⟩
    funext j
    change (v.val i / w.val i) * w.val j = v.val j
    calc
      _ = v.val i * (w.val j / w.val i) := by ring
      _ = v.val i * (v.val j / v.val i) := by rw [← hratio j]
      _ = v.val j := by field_simp
  · intro h
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp h
    exact (nativeProjectiveVectorPoint_eq_of_smul d w v c hc).symm

/-- The existing literal native vector point descends through the ORIGINAL
nonzero-vector projectivization; no comparison map or fiber certificate is supplied. -/
def nativeProjectivePointComparison : P → Q :=
  fun p => Quotient.liftOn' p (polynomialProjNonzeroVectorPoint d) (by
    rintro v w ⟨c, hc⟩
    exact (nativeProjectiveVectorPoint_eq_of_smul d w v c hc).symm)

/-- The comparison is the SAME actual native scheme point on every original representative. -/
theorem nativeProjectivePointComparison_mk (v : Vnz) :
    nativeProjectivePointComparison d (Projectivization.mk ℂ v.val v.property) =
      polynomialProjNonzeroVectorPoint d v := rfl

/-- Actual native vector-point continuity descends through the original quotient topology. -/
theorem continuous_nativeProjectivePointComparison : Continuous (nativeProjectivePointComparison d) := by
  apply continuous_coinduced_dom.mpr
  exact polynomialProjNonzeroVectorPoint_continuous d

/-- Genuine shared-chart scalar fibers and existing native vector-point surjectivity
produce bijectivity of the original comparison map. -/
theorem nativeProjectivePointComparison_bijective : Function.Bijective (nativeProjectivePointComparison d) := by
  constructor
  · intro p q h
    induction p using Projectivization.ind with
    | h v hv =>
      induction q using Projectivization.ind with
      | h w hw =>
        exact (nativeProjectiveVectorPoint_eq_iff d ⟨v, hv⟩ ⟨w, hw⟩).mp h
  · intro q
    obtain ⟨v, hv⟩ := polynomialProjNonzeroVectorPoint_surjective d q
    exact ⟨Projectivization.mk ℂ v.val v.property, hv⟩

/-- The original quotient and actual native polynomial Proj analytic point space
are genuinely homeomorphic, using produced compactness and native separatedness. -/
def nativeProjectivePointHomeomorph : P ≃ₜ Q := by
  let : CompactSpace P := monomialProjectiveCompactSpace
  let : T2Space Q := schemeAnalyticPoint_t2Space (polynomialProjStructureMap ℂ d)
  exact (show Continuous (Equiv.ofBijective (nativeProjectivePointComparison d)
    (nativeProjectivePointComparison_bijective d)) from
      continuous_nativeProjectivePointComparison d).homeoOfEquivCompactToT2

/-- The final homeomorphism retains the original native vector-point readback. -/
theorem nativeProjectivePointHomeomorph_mk (v : Vnz) :
    nativeProjectivePointHomeomorph d (Projectivization.mk ℂ v.val v.property) =
      polynomialProjNonzeroVectorPoint d v := rfl

end SGPT.Toric
