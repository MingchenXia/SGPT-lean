import SGPT.Bergman.SourceCompactHolomorphicSections
import SGPT.Projective.SourceFiniteSectionMap
import SGPT.PSH.GlobalL2Correction

/-!
# A basis of the actual full section space

Actual fibre evaluation and actual native frame coefficients are linear
on the original full H0 space. Compactness supplies a finite basis; when
the full section space has no base points, its dimension is positive and
that basis is a genuine finite generating family for the native map.
Blueprint: `siu-kodaira-embedding.tex`, node `siu-kodaira:finite-family`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Bergman.SiuKodaira

open Set Filter Bundle
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle SGPT.PSH.GlobalL2

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] (E : HermitianHolomorphicLineBundle.{0, 0} n X)

/-- Evaluation in the actual original fibre of a genuine global section. -/
def sectionValueLinear (x : X) : HolomorphicSections (n := n) E.Fiber →ₗ[ℂ] E.Fiber x where
  toFun s := s x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual original frame coefficient, as a linear functional on full H0. -/
def sectionCoefficientLinear (e : AtlasFrame E) (x : X) :
    HolomorphicSections (n := n) E.Fiber →ₗ[ℂ] ℂ :=
  (e.val.continuousLinearMapAt ℂ x).toLinearMap.comp (sectionValueLinear E x)

/-- Every original section is the literal fibrewise sum in any finite basis. -/
theorem basis_value_expansion {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ (HolomorphicSections (n := n) E.Fiber))
    (s : HolomorphicSections (n := n) E.Fiber) (x : X) :
    s x = ∑ j, b.repr s j • b j x := by
  change sectionValueLinear E x s = ∑ j, b.repr s j • sectionValueLinear E x (b j)
  simpa only [map_sum, map_smul] using (congrArg (sectionValueLinear E x) (b.sum_repr s)).symm

/-- Exact homogeneous coefficient expansion of every original section. -/
theorem basis_coefficient_expansion {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ (HolomorphicSections (n := n) E.Fiber))
    (s : HolomorphicSections (n := n) E.Fiber) (e : AtlasFrame E) (x : X) :
    e.val.continuousLinearMapAt ℂ x (s x) =
      ∑ j, b.repr s j * e.val.continuousLinearMapAt ℂ x (b j x) := by
  change sectionCoefficientLinear E e x s = ∑ j, b.repr s j * sectionCoefficientLinear E e x (b j)
  simpa only [map_sum, map_smul, smul_eq_mul] using
    (congrArg (sectionCoefficientLinear E e x) (b.sum_repr s)).symm

/-- Compactness produces a finite basis of positive length, consisting of
actual globally generating sections in the original fibres. -/
theorem exists_finite_basis_generating [CompactSpace X] [Nonempty X]
    (hgen : ∀ x : X, ∃ s : HolomorphicSections (n := n) E.Fiber, s x ≠ 0) :
    ∃ (N : ℕ) (b : Module.Basis (Fin (N + 1)) ℂ (HolomorphicSections (n := n) E.Fiber)),
      ∀ x : X, ∃ j : Fin (N + 1), b j x ≠ 0 := by
  classical
  let H := HolomorphicSections (n := n) E.Fiber
  let _ : FiniteDimensional ℂ H := holomorphicSections_finiteDimensional (n := n) E.Fiber
  let p : X := Classical.choice inferInstance
  obtain ⟨s, hs⟩ := hgen p
  have hs0 : s ≠ 0 := by
    intro h
    apply hs
    rw [h]
    rfl
  let _ : Nontrivial H := nontrivial_of_ne s 0 hs0
  have hr : 0 < Module.finrank ℂ H := Module.finrank_pos
  obtain ⟨N, hN⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  let b : Module.Basis (Fin (N + 1)) ℂ H := (Module.finBasis ℂ H).reindex (finCongr hN)
  refine ⟨N, b, fun x => ?_⟩
  by_contra hbad
  push Not at hbad
  obtain ⟨t, ht⟩ := hgen x
  apply ht
  calc t x = ∑ j, b.repr t j • b j x := basis_value_expansion E b t x
    _ = 0 := Finset.sum_eq_zero fun j _ => by rw [hbad j, smul_zero]

end SGPT.Bergman.SiuKodaira
