import SGPT.PSH.CartierStalkCoefficient
import SGPT.PSH.CartierOpenRestriction

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending RelativePrincipalizationSpan
open scoped Topology Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- BOTH entire original stalk inclusions are retained by the genuine
FULL ideal-image restriction to ANY original open submanifold. -/
theorem cartierOpenRestriction_stalk_ideal_eq (D E : EffectiveDivisor n M)
    (U : Opens M) (y : U) (hideal : ∀ b, D.ideal.mem (y : M) b ↔ E.ideal.mem (y : M) b)
    (b : U → ℂ) :
    (cartierOpenRestriction D U).ideal.mem y b ↔ (cartierOpenRestriction E U).ideal.mem y b := by
  rw [cartierOpenRestriction_ideal, cartierOpenRestriction_ideal]
  constructor
  · intro hb
    apply GermIdeal.mem_pullback_iff.mpr
    apply IsInSpanAt.mono _ (GermIdeal.mem_pullback_iff.mp hb)
    rintro s ⟨a, ha, rfl⟩
    exact ⟨a, (hideal a).mp ha, rfl⟩
  · intro hb
    apply GermIdeal.mem_pullback_iff.mpr
    apply IsInSpanAt.mono _ (GermIdeal.mem_pullback_iff.mp hb)
    rintro s ⟨a, ha, rfl⟩
    exact ⟨a, (hideal a).mpr ha, rfl⟩

section Prime
variable {m : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]

/-- FULL original stalk equality reads the genuine coefficient at the
SAME prescribed point of the SAME actual open prime. -/
theorem cartierGeometricPrimeCoefficient_open_eq_of_stalk_ideal_eq
    (D E : EffectiveDivisor (m + 1) X) (U : Opens X)
    (A : GeometricPrimeCarrier (m + 1) U) (y : U) (hyA : y ∈ A.val)
    (hideal : ∀ b, D.ideal.mem (y : X) b ↔ E.ideal.mem (y : X) b) :
    cartierGeometricPrimeCoefficient (cartierOpenRestriction D U) A =
      cartierGeometricPrimeCoefficient (cartierOpenRestriction E U) A :=
  cartierGeometricPrimeCoefficient_eq_of_stalk_ideal_eq _ _ A y hyA
    (cartierOpenRestriction_stalk_ideal_eq D E U y hideal)

/-- FULL original ideal equality on any original set internally gives
coefficient equality on EVERY actual open prime meeting that set. -/
theorem cartierGeometricPrimeCoefficient_open_eq_of_ideal_eq_on
    (D E : EffectiveDivisor (m + 1) X) (V : Set X)
    (hideal : ∀ x ∈ V, ∀ b, D.ideal.mem x b ↔ E.ideal.mem x b)
    (U : Opens X) (A : GeometricPrimeCarrier (m + 1) U)
    (hA : (A.val ∩ (Subtype.val : U → X) ⁻¹' V).Nonempty) :
    cartierGeometricPrimeCoefficient (cartierOpenRestriction D U) A =
      cartierGeometricPrimeCoefficient (cartierOpenRestriction E U) A := by
  obtain ⟨y, hyA, hyV⟩ := hA
  exact cartierGeometricPrimeCoefficient_open_eq_of_stalk_ideal_eq D E U A y hyA (hideal y hyV)

end Prime
end SGPT.PSH
