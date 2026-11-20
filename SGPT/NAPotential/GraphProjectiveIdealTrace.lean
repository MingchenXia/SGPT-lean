import SGPT.NAPotential.ProjectiveGraphProjectiveHomeomorph
import SGPT.NAPotential.ProjectiveGraphAnalyticZero

/-! # The actual original projective homeomorphism preserves full ideal zero loci

Complete blueprint: `graph-projective-ideal-trace.tex`.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.NAPotential.GraphProjectiveIdealTrace

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes Set MvPolynomial
open SGPT.NAPotential.AlgPrimes3
open ProjectiveGraphProjectiveHomeomorph ProjectiveGraphProjectiveReadback
open ProjectiveGraphAnalyticZero ProjectiveGraphRelationCore
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
local instance nativeTopology (N : ℕ) : TopologicalSpace
    (SchemeComplexPoint (polynomialProjStructureMap ℂ N)) := schemeAnalyticPointTopology _

theorem originalProjectiveHomeomorph_mem_idealZeroLocus_iff (N : ℕ)
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin (N + 1)) ℂ))
    (q : SchemeComplexPoint (polynomialProjStructureMap ℂ N)) :
    originalProjectiveHomeomorph N q ∈ idealZeroLocus J.toIdeal ↔
      schemeComplexPointImage (polynomialProjStructureMap ℂ N) q ∈
        ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin (N + 1)) ℂ)
          (J.toIdeal : Set (MvPolynomial (Fin (N + 1)) ℂ)) := by
  obtain ⟨v, rfl⟩ := polynomialProjNonzeroVectorPoint_surjective N q
  obtain ⟨i, hi⟩ := polynomialProjVector_exists_nonzero_coordinate N v.val v.property
  rw [polynomialProjNonzeroVectorPoint_eq_chart N v i hi]
  have hx : originalProjectiveHomeomorph N (polynomialProjVectorChartPoint N i v.val) =
      mk v.val v.property := by
    rw [originalProjectiveHomeomorph_apply, nativeVectorPoint_projectivePoint N i v.val v.property hi]
  have hhom (F : MvPolynomial (Fin (N + 1)) ℂ) (n : ℕ) (hF : F.IsHomogeneous n) :
      MvPolynomial.eval (originalProjectiveHomeomorph N
        (polynomialProjVectorChartPoint N i v.val)).rep F = 0 ↔
        F ∈ (schemeComplexPointImage (polynomialProjStructureMap ℂ N)
          (polynomialProjVectorChartPoint N i v.val)).asHomogeneousIdeal :=
    (eval_rep_eq_zero_iff hF _ v.val v.property hx).trans
      (polynomialProjVectorChartPoint_mem_homogeneous N i v.val hi n F hF).symm
  rw [ProjectiveSpectrum.mem_zeroLocus]
  change _ ↔ J.toIdeal ≤ (schemeComplexPointImage (polynomialProjStructureMap ℂ N)
    (polynomialProjVectorChartPoint N i v.val)).asHomogeneousIdeal.toIdeal
  obtain ⟨S, hS, hspan⟩ := exists_finite_homogeneous_generators J
  constructor
  · intro h
    have hle : J.toIdeal ≤ (schemeComplexPointImage (polynomialProjStructureMap ℂ N)
        (polynomialProjVectorChartPoint N i v.val)).asHomogeneousIdeal.toIdeal := by
      rw [← hspan]
      apply Ideal.span_le.mpr
      intro F hF
      obtain ⟨⟨n, hn⟩, hm⟩ := hS F hF
      exact (hhom F n hn).mp (h F hm)
    exact hle
  · intro h
    have hle : J.toIdeal ≤ RingHom.ker (MvPolynomial.eval
        (originalProjectiveHomeomorph N (polynomialProjVectorChartPoint N i v.val)).rep) := by
      rw [← hspan]
      apply Ideal.span_le.mpr
      intro F hF
      obtain ⟨⟨n, hn⟩, hm⟩ := hS F hF
      exact (hhom F n hn).mpr (h hm)
    intro F hF
    exact hle hF

theorem inverse_mem_zeroLocus_iff (N : ℕ)
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin (N + 1)) ℂ))
    (x : ComplexProjectiveSpace N) :
    schemeComplexPointImage (polynomialProjStructureMap ℂ N)
        ((originalProjectiveHomeomorph N).symm x) ∈
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin (N + 1)) ℂ)
        (J.toIdeal : Set (MvPolynomial (Fin (N + 1)) ℂ)) ↔ x ∈ idealZeroLocus J.toIdeal := by
  simpa only [Homeomorph.apply_symm_apply] using
    (originalProjectiveHomeomorph_mem_idealZeroLocus_iff N J
      ((originalProjectiveHomeomorph N).symm x)).symm

end SGPT.NAPotential.GraphProjectiveIdealTrace
