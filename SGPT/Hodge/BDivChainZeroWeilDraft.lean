import SGPT.Hodge.BDivChainZeroNativeDraft
import SGPT.Hodge.BDivChainZeroModels
import SGPT.BDivisor.BlowupModelVolume

/-!
# Original modelwise pseudo-effectivity and b-divisor volume in dimension zero

All families contain real Bott--Chern classes on the actual
model system. The predicates below reproduce the existing modelwise definitions;
there is no claim yet that this constructs `D(T)` or proves a source theorem.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.NativeDraft

open Set SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.BDivisor
open scoped ENNReal

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X] [ConnectedSpace X]

/-- The literal modelwise source pseudo-effectivity predicate. -/
def IsPseudoeffectiveAny {S : ModelSystem n X} (D : WeilFamilyAny S) : Prop :=
  ∀ π : S.Model, ClassPseudoeffectiveViaPotentials (D.val π)

/-- The existing conditional infimum of the actual model class volumes. -/
def volumeAny {S : ModelSystem n X} (D : WeilFamilyAny S) : ℝ≥0∞ := by
  classical
  exact if IsPseudoeffectiveAny D then ⨅ π : S.Model, Modification.classVolume π.1 (D.val π)
    else 0

omit [ConnectedSpace X] in
/-- Positive-dimensional pseudo-effectivity is the already-defined notion. -/
theorem isPseudoeffectiveAny_iff_existing {S : ModelSystem n X} (hn : 0 < n)
    (D : WeilFamilyAny S) : IsPseudoeffectiveAny D ↔ (toExisting S hn D).IsPseudoeffective := by
  rw [WeilBDivisorOn.isPseudoeffective_iff]
  rfl

/-- Positive-dimensional volume is the existing volume of the same family. -/
theorem volumeAny_eq_existing {S : ModelSystem n X} (hn : 0 < n)
    (D : WeilFamilyAny S) : volumeAny D = (toExisting S hn D).vol := by
  classical
  unfold volumeAny WeilBDivisorOn.vol
  rw [isPseudoeffectiveAny_iff_existing hn D]
  rfl

end SGPT.Hodge.BDivChain.NativeDraft

namespace SGPT.Hodge.BDivChain.NativeDraft

open Set SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.BDivisor
open scoped ENNReal

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel 0) X]
  [IsComplexManifold 0 X] [CompactSpace X] [ConnectedSpace X]

omit [CompactSpace X] [ConnectedSpace X] in
/-- The zero class has an actual zero theta-psh potential in dimension zero. -/
theorem classPseudoeffective_of_dim_zero
    (α : RealBottChern 0 X) : ClassPseudoeffectiveViaPotentials α := by
  rw [realBottChern_eq_zero_of_dim_zero α, ← RealBottChern.ofRepresentative_zero,
    classPseudoeffectiveViaPotentials_ofRepresentative]
  refine ⟨fun _ => (0 : EReal), ?_⟩
  exact RooftopDimZero.isThetaPshPotential_of_dim_zero rfl
    (LocalPotentials.closedRealOneOne_hasLocalPotentials (0 : ClosedRealOneOneForm 0 X))
    (fun _ => EReal.coe_ne_top 0) (fun _ => EReal.coe_ne_bot 0)

omit [ConnectedSpace X] in
/-- Every dimension-zero compatible family is the zero family of actual
model Bott--Chern classes. -/
theorem weilFamily_eq_zero_of_dim_zero {S : ModelSystem 0 X} (D : WeilFamilyAny S) :
    D = 0 := by
  apply Subtype.ext
  funext π
  exact modelClass_eq_zero S D π

omit [CompactSpace X] [ConnectedSpace X] in
/-- The actual class is nef with respect to any actual supplied Kähler
background. This does not assert existence of such a background. -/
theorem classNefWithRespectTo_of_dim_zero (ω : KahlerBackground 0 X)
    (α : RealBottChern 0 X) : ClassNefWithRespectTo ω α := by
  rw [realBottChern_eq_zero_of_dim_zero α]
  exact classNefWithRespectTo_zero ω

omit [ConnectedSpace X] in
/-- Every actual model class is pseudo-effective: the witness above is
constructed on that actual connected compact model. -/
theorem isPseudoeffectiveAny_of_dim_zero {S : ModelSystem 0 X} (D : WeilFamilyAny S) :
    IsPseudoeffectiveAny D := by
  intro π
  exact classPseudoeffective_of_dim_zero (D.val π)

/-- The original conditional model-volume infimum is one in dimension zero. -/
theorem volumeAny_eq_one_of_dim_zero {S : ModelSystem 0 X} (D : WeilFamilyAny S) :
    volumeAny D = 1 := by
  classical
  unfold volumeAny
  rw [if_pos (isPseudoeffectiveAny_of_dim_zero D)]
  simp only [modelClassVolume_eq_one_of_dim_zero]
  simp

end SGPT.Hodge.BDivChain.NativeDraft
