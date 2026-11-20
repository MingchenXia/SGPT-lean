import SGPT.Toric.TropicalBedfordTaylor
import SGPT.Convex.MixedAlexandrovFunctional
import SGPT.Foundations.Analysis.Pending.LocalCanonicalMixedSubsetExpansion
import SGPT.Foundations.Analysis.Pending.PolarizationAlgebra

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set Filter MeasureTheory TopologicalSpace SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.LocalCanonicalMixedSubsetExpansion
open SGPT.Foundations.Analysis.Pending.PolarizationAlgebra
open scoped Topology BigOperators RealInnerProductSpace CompactlySupported

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "D" => tropicalSmoothDomain n

/-- The independently constructed canonical positive mixed BT product of the
literal finite convex tropical tuple. -/
def tropicalCanonicalMixedBTMeasure (F : Fin n → RealConvexFunction E) :
    Measure (ComplexModel n) :=
  canonicalMixedBedfordTaylorMeasure D (fun i z => (F i).val (tropicalization z))
    (fun i => isLocallyBoundedPshOn_tropicalConvexProfile (F i).property)

/-- The actual canonical product vanishes outside the same geometric torus. -/
theorem tropicalCanonicalMixedBTMeasure_compl (F : Fin n → RealConvexFunction E) :
    tropicalCanonicalMixedBTMeasure F (complexTorus n)ᶜ = 0 :=
  canonicalMixedBedfordTaylorMeasure_compl D _ _

/-- Genuine compact torus lifts internally supply compact finiteness of the
actual mapped mixed product; no total-mass premise is assumed. -/
theorem isFiniteMeasureOnCompacts_map_tropicalCanonicalMixedBTMeasure
    (F : Fin n → RealConvexFunction E) :
    IsFiniteMeasureOnCompacts
      (Measure.map tropicalization (tropicalCanonicalMixedBTMeasure F)) := by
  obtain ⟨hT, _⟩ := exists_compact_tropical_torus_lift (n := n) isCompact_empty
  have hm : ∀ᵐ z ∂tropicalCanonicalMixedBTMeasure F, z ∈ complexTorus n :=
    ae_iff.mpr (tropicalCanonicalMixedBTMeasure_compl F)
  refine ⟨?_⟩
  intro K hK
  obtain ⟨_, L, hL, hLD, hcover⟩ := exists_compact_tropical_torus_lift hK
  rw [Measure.map_apply hT hK.measurableSet]
  apply lt_of_le_of_lt
    (measure_mono_ae (hm.mono (fun z hz hpre => hcover z hz hpre)))
  exact canonicalMixedBedfordTaylorMeasure_finiteOnCompacts
    (fun i => isLocallyBoundedPshOn_tropicalConvexProfile (F i).property) hL hLD

/-- Every genuine continuous compact real test is integrable after the SAME
tropical pullback, including every selected tuple and the empty tuple. -/
theorem integrable_comp_tropicalCanonicalMixedBTMeasure
    (F : Fin n → RealConvexFunction E) {φ : E → ℝ}
    (hφ : Continuous φ) (hK : HasCompactSupport φ) :
    Integrable (fun z => φ (tropicalization z)) (tropicalCanonicalMixedBTMeasure F) := by
  let := isFiniteMeasureOnCompacts_map_tropicalCanonicalMixedBTMeasure F
  obtain ⟨hT, _⟩ := exists_compact_tropical_torus_lift (n := n) isCompact_empty
  have hi : Integrable φ (Measure.map tropicalization (tropicalCanonicalMixedBTMeasure F)) :=
    hφ.integrable_of_hasCompactSupport hK
  exact (integrable_map_measure hφ.aestronglyMeasurable hT.aemeasurable).mp hi

private theorem tropicalMixedBT_subset_integral
    (F : Fin n → RealConvexFunction E) (S : Finset (Fin n))
    {φ : E → ℝ} (hφ : Continuous φ) (hK : HasCompactSupport φ) :
    (∫ a, φ a ∂alexandrovMeasure (innerₗ E) volume
      (fun a => ((finiteConvexSubsetSum F S).val a : EReal))) =
      ∑ g : Fin n → Fin n with ∀ j, g j ∈ S,
        ∫ z, φ (tropicalization z) ∂tropicalCanonicalMixedBTMeasure (fun j => F (g j)) := by
  classical
  obtain ⟨hS, eS⟩ := canonicalScalar_subsetSum_eq_sum_selected
    (fun i => isLocallyBoundedPshOn_tropicalConvexProfile (F i).property) S
  have ed : tropicalCanonicalBTMeasure (finiteConvexSubsetSum F S).property =
      SGPT.Foundations.Analysis.Pending.MongeAmpere.canonicalBedfordTaylorMeasure D
        (fun z => ∑ i ∈ S, (F i).val (tropicalization z)) hS := by
    exact canonicalMixedBedfordTaylorMeasure_diagonal D _ hS
  calc
    _ = ∫ z, φ (tropicalization z)
        ∂tropicalCanonicalBTMeasure (finiteConvexSubsetSum F S).property :=
      (integral_tropicalCanonicalBT_source_test
        (finiteConvexSubsetSum F S).property hφ hK).symm
    _ = ∫ z, φ (tropicalization z) ∂∑ g : Fin n → Fin n with ∀ j, g j ∈ S,
        tropicalCanonicalMixedBTMeasure (fun j => F (g j)) := by rw [ed, eS]; rfl
    _ = _ := integral_finsetSum_measure
      (fun g _ => integrable_comp_tropicalCanonicalMixedBTMeasure (fun j => F (g j)) hφ hK)

/-- Actual positive subset expansion and unchanged finite inclusion-exclusion
algebra give the signed compact-test polarization of the canonical mixed product. -/
theorem integral_tropicalCanonicalMixedBT_normalized_polarization
    (F : Fin n → RealConvexFunction E) {φ : E → ℝ}
    (hφ : Continuous φ) (hK : HasCompactSupport φ) :
    (∫ z, φ (tropicalization z) ∂tropicalCanonicalMixedBTMeasure F) =
      (n.factorial : ℝ)⁻¹ * ∑ S : Finset (Fin n), (-1 : ℝ) ^ (n - S.card) *
        ∫ a, φ a ∂alexandrovMeasure (innerₗ E) volume
          (fun a => ((finiteConvexSubsetSum F S).val a : EReal)) := by
  classical
  let d : (Fin n → Fin n) → ℝ := fun g =>
    ∫ z, φ (tropicalization z) ∂tropicalCanonicalMixedBTMeasure (fun j => F (g j))
  have hd (σ : Equiv.Perm (Fin n)) : d σ = d id := by
    have ep := canonicalMixedBedfordTaylorMeasure_perm
      (fun i => isLocallyBoundedPshOn_tropicalConvexProfile (F i).property) σ
      (fun i => isLocallyBoundedPshOn_tropicalConvexProfile (F (σ i)).property)
    exact congrArg (fun μ : Measure (ComplexModel n) =>
      ∫ z, φ (tropicalization z) ∂μ) ep
  have hp := sum_powerset_signed_eq_factorial_mul d hd
  have hs (S : Finset (Fin n)) := tropicalMixedBT_subset_integral F S hφ hK
  simp_rw [hs]
  change d id = (n.factorial : ℝ)⁻¹ * ∑ S : Finset (Fin n),
    (-1 : ℝ) ^ (n - S.card) * ∑ g : Fin n → Fin n with ∀ j, g j ∈ S, d g
  rw [hp, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero n), one_mul]

/-- The signed compact-test functional is that of the existing ORIGINAL
Euclidean mixed Alexandrov Riesz measure, retaining its actual Haar normalization. -/
theorem integral_tropicalCanonicalMixedBT_source_test
    (F : Fin n → RealConvexFunction E) {φ : E → ℝ}
    (hφ : Continuous φ) (hK : HasCompactSupport φ) :
    (∫ z, φ (tropicalization z) ∂tropicalCanonicalMixedBTMeasure F) =
      ∫ a, φ a ∂mixedAlexandrovMeasure volume (EuclideanSpace.basisFun (Fin n) ℝ) F := by
  let test : C_c(E, ℝ) := ⟨⟨φ, hφ⟩, hK⟩
  rw [integral_tropicalCanonicalMixedBT_normalized_polarization F hφ hK]
  exact (mixedAlexandrovFunctional_apply volume F test).symm.trans
    (integral_mixedAlexandrovMeasure volume (EuclideanSpace.basisFun (Fin n) ℝ) F test).symm

/-- Equality of the actual positive measures follows from manufactured compact
finiteness and ALL continuous compact signed tests. Singular parts and n=0 persist. -/
theorem tropicalization_canonicalMixedBTMeasure_eq_mixedAlexandrov
    (F : Fin n → RealConvexFunction E) :
    Measure.map tropicalization (tropicalCanonicalMixedBTMeasure F) =
      mixedAlexandrovMeasure volume (EuclideanSpace.basisFun (Fin n) ℝ) F := by
  obtain ⟨hT, _⟩ := exists_compact_tropical_torus_lift (n := n) isCompact_empty
  let := isFiniteMeasureOnCompacts_map_tropicalCanonicalMixedBTMeasure F
  let := isLocallyFiniteMeasure_mixedAlexandrovMeasure volume
    (EuclideanSpace.basisFun (Fin n) ℝ) F
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  exact (integral_map hT.aemeasurable φ.continuous.aestronglyMeasurable).trans
    (integral_tropicalCanonicalMixedBT_source_test F φ.continuous φ.hasCompactSupport)

end SGPT.Toric
