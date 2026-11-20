import SGPT.Bergman.SiuKodairaFiniteSections
import SGPT.Bergman.SiuKodairaGermSpan

/-!
# Native finite-section projective coordinates and point injectivity

The homogeneous vectors consist of the actual original native frame
coefficients.  The original projective map is read in any actual frame,
and a full H0 basis retains the proved separation of original points.
Blueprint: `siu-kodaira-embedding.tex`, node `siu-kodaira:section-map`.
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
open SGPT.Bergman.AnalyticSectionProducts
open HermitianHolomorphicLineBundle SGPT.PSH.GlobalL2
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace

variable {n N : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] (E : HermitianHolomorphicLineBundle.{0, 0} n X)

/-- The genuine homogeneous vector in an actual original native line frame. -/
def sectionVector (s : Fin (N + 1) → HolomorphicSections (n := n) E.Fiber)
    (e : AtlasFrame E) (x : X) : Fin (N + 1) → ℂ :=
  fun j => e.val.continuousLinearMapAt ℂ x (s j x)

/-- Actual fibrewise generation gives a nonzero actual homogeneous vector. -/
theorem sectionVector_ne_zero
    (s : Fin (N + 1) → HolomorphicSections (n := n) E.Fiber)
    (hgen : ∀ x : X, ∃ j : Fin (N + 1), s j x ≠ 0)
    (e : AtlasFrame E) (x : X) (hx : x ∈ e.val.baseSet) : sectionVector E s e x ≠ 0 := by
  let := e.property
  intro hz
  obtain ⟨j, hj⟩ := hgen x
  have hzero : e.val.continuousLinearMapAt ℂ x (s j x) = 0 := congrFun hz j
  have h := trivialization_eq_coef_smul_frame e.val hx (s j x)
  rw [hzero, zero_smul] at h
  exact hj h

/-- Exact readback of the original projective map through every native
continuous-linear atlas coefficient. -/
theorem nativeSectionMap_frame
    (s : Fin (N + 1) → HolomorphicSections (n := n) E.Fiber)
    (hgen : ∀ x : X, ∃ j : Fin (N + 1), s j x ≠ 0)
    (e : AtlasFrame E) (x : X) (hx : x ∈ e.val.baseSet) :
    sourceNativeFiniteSectionProjectiveMap E s hgen x =
      ComplexProjectiveSpace.mk (sectionVector E s e x) (sectionVector_ne_zero E s hgen e x hx) := by
  let := e.property
  have hvec : sectionVector E s e x = fun j => (e.val ⟨x, s j x⟩).2 := by
    funext j
    exact Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e.val hx _
  simpa only [hvec] using sourceNativeFiniteSectionProjectiveMap_frame E s hgen e x hx

/-- The actual affine projective coordinates are the actual section ratios. -/
theorem nativeSectionMap_affineChart
    (s : Fin (N + 1) → HolomorphicSections (n := n) E.Fiber)
    (hgen : ∀ x : X, ∃ j : Fin (N + 1), s j x ≠ 0)
    (e : AtlasFrame E) (i : Fin (N + 1)) {x : X} (hx : x ∈ e.val.baseSet)
    (hi : sectionVector E s e x i ≠ 0) :
    sourceNativeFiniteSectionProjectiveMap E s hgen x ∈ (affineChart i).source ∧
      affineChart i (sourceNativeFiniteSectionProjectiveMap E s hgen x) =
        affineRatio i (sectionVector E s e x) := by
  rw [nativeSectionMap_frame E s hgen e x hx]
  exact ⟨(mk_mem_affineChart_source_iff i (sectionVector_ne_zero E s hgen e x hx)).mpr hi,
    affineChart_mk i (sectionVector_ne_zero E s hgen e x hx) hi⟩

/-- The actual full section basis retains point separation in the actual
original projectivization; no projective embedding output is assumed. -/
theorem nativeBasisSectionMap_injective
    (b : Module.Basis (Fin (N + 1)) ℂ (HolomorphicSections (n := n) E.Fiber))
    (hgen : ∀ x : X, ∃ j : Fin (N + 1), b j x ≠ 0)
    (hsep : ∀ p q : X, p ≠ q → ∃ s : HolomorphicSections (n := n) E.Fiber,
      s p = 0 ∧ s q ≠ 0) :
    Function.Injective (sourceNativeFiniteSectionProjectiveMap E b hgen) := by
  classical
  intro p q hmap
  by_contra hpq
  obtain ⟨t, htp, htq⟩ := hsep p q hpq
  let e := prefFrame E p
  let f := prefFrame E q
  let := e.property
  let := f.property
  have hp : p ∈ e.val.baseSet := mem_prefFrame E p
  have hq : q ∈ f.val.baseSet := mem_prefFrame E q
  rw [nativeSectionMap_frame E b hgen e p hp, nativeSectionMap_frame E b hgen f q hq] at hmap
  obtain ⟨a, -, hv⟩ := exists_eq_smul_of_mk_eq hmap
  have hcoord : ∀ j, f.val.continuousLinearMapAt ℂ q (b j q) =
      a * e.val.continuousLinearMapAt ℂ p (b j p) := by
    intro j
    simpa only [sectionVector, Pi.smul_apply, smul_eq_mul] using congrFun hv j
  have htpcoef : e.val.continuousLinearMapAt ℂ p (t p) = 0 := by rw [htp, map_zero]
  have htqcoef : f.val.continuousLinearMapAt ℂ q (t q) ≠ 0 := by
    intro hz
    have h := trivialization_eq_coef_smul_frame f.val hq (t q)
    rw [hz, zero_smul] at h
    exact htq h
  apply htqcoef
  calc f.val.continuousLinearMapAt ℂ q (t q) =
      ∑ j, b.repr t j * f.val.continuousLinearMapAt ℂ q (b j q) :=
        basis_coefficient_expansion E b t f q
    _ = ∑ j, b.repr t j * (a * e.val.continuousLinearMapAt ℂ p (b j p)) :=
      Finset.sum_congr rfl fun j _ => by rw [hcoord j]
    _ = a * ∑ j, b.repr t j * e.val.continuousLinearMapAt ℂ p (b j p) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    _ = a * e.val.continuousLinearMapAt ℂ p (t p) := by rw [← basis_coefficient_expansion E b t e p]
    _ = 0 := by rw [htpcoef, mul_zero]

end SGPT.Bergman.SiuKodaira
