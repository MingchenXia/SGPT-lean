import SGPT.Hodge.BDivChainZeroWeilDraft
import SGPT.BDivisor.BlowupModelNef

/-!
# Realization and nefness for dimension-uniform actual model-class families

Definitions retain actual model pullback, actual Kähler
backgrounds, actual Bott--Chern classes and actual modelwise Euclidean
convergence. The proofs below compare the existing positive-dimensional book
predicates. Identification with
the complete book's source formulation in all dimensions also requires review.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.NativeDraft

open Filter SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending SGPT.BDivisor
open scoped Topology

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

/-- Exactly the existing realization condition, on dimension-uniform families. -/
def IsRealizationAny {S : ModelSystem n X} (D : WeilFamilyAny S)
    (π : S.Model) (α : RealBottChern n π.1.carrier) : Prop :=
  ∀ (π' : S.Model) (h : π ≤ π'),
    D.val π' = Modification.classPullbackOfLE (show π.1 ≤ π'.1 from h) α

/-- Exactly the existing nef Cartier existence condition, on actual models. -/
def IsNefCartierAny {S : ModelSystem n X} (D : WeilFamilyAny S) : Prop :=
  ∃ (π : S.Model) (α : RealBottChern n π.1.carrier), IsRealizationAny D π α ∧
    ∃ κ : KahlerBackground n π.1.carrier, ClassNefWithRespectTo κ α

/-- Actual Euclidean convergence on every actual model class. -/
def ConvergesAny {S : ModelSystem n X} {ι : Type*} (l : Filter ι)
    (D : ι → WeilFamilyAny S) (D₀ : WeilFamilyAny S) : Prop :=
  ∀ π : S.Model, Tendsto (fun i => (D i).val π) l
    (@nhds _ (euclideanTopology (RealBottChern n π.1.carrier)) (D₀.val π))

/-- The original net criterion with actual nef Cartier classes and actual
modelwise convergence. -/
def IsNefAny {S : ModelSystem n X} (D₀ : WeilFamilyAny S) : Prop :=
  ∃ (ι : Type (u + 1)) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
    (D : ι → WeilFamilyAny S), (∀ i, IsNefCartierAny (D i)) ∧ ConvergesAny atTop D D₀

/-- On positive-dimensional systems, realization uses precisely the existing
predicate on the same family and model. -/
theorem isRealizationAny_iff_existing {S : ModelSystem n X} (hn : 0 < n)
    (D : WeilFamilyAny S) (π : S.Model) (α : RealBottChern n π.1.carrier) :
    IsRealizationAny D π α ↔ (toExisting S hn D).IsRealization π α := Iff.rfl

/-- Positive-dimensional nef Cartier is the existing original predicate. -/
theorem isNefCartierAny_iff_existing {S : ModelSystem n X} (hn : 0 < n)
    (D : WeilFamilyAny S) :
    IsNefCartierAny D ↔ (toExisting S hn D).IsNefCartier := Iff.rfl

/-- A nef Cartier family is nef through the original constant-net condition. -/
theorem isNefAny_of_isNefCartierAny {S : ModelSystem n X} {D : WeilFamilyAny S}
    (hD : IsNefCartierAny D) : IsNefAny D := by
  refine ⟨PUnit, inferInstance, inferInstance, inferInstance, fun _ => D, fun _ => hD, ?_⟩
  intro π
  let : TopologicalSpace (RealBottChern n π.1.carrier) := euclideanTopology _
  exact tendsto_const_nhds

end SGPT.Hodge.BDivChain.NativeDraft

namespace SGPT.Hodge.BDivChain.NativeDraft

open Filter SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending SGPT.BDivisor
open scoped Topology

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel 0) X]
  [IsComplexManifold 0 X] [CompactSpace X] [ConnectedSpace X]

/-- The actual zero form is Kähler in complex dimension zero: positivity is
vacuous because every complex tangent vector is zero. -/
def kahlerBackgroundZero : KahlerBackground 0 X := by
  refine ⟨0, ?_⟩
  refine ⟨?_, ?_⟩
  · intro e z hz
    refine ⟨?_, ?_⟩
    · intro v w
      simp
    · intro v hv
      exact False.elim (hv (Subsingleton.elim v 0))
  · exact (0 : ClosedRealOneOneForm 0 X).property.1

omit [ConnectedSpace X] in
/-- Every actual zero-dimensional family is realized on every actual model
by every actual model class; all classes vanish, independently of root choice. -/
theorem isRealizationAny_zero {S : ModelSystem 0 X} (D : WeilFamilyAny S)
    (π : S.Model) (α : RealBottChern 0 π.1.carrier) : IsRealizationAny D π α := by
  intro π' h
  exact (realBottChern_eq_zero_of_dim_zero _).trans
    (realBottChern_eq_zero_of_dim_zero _).symm

omit [ConnectedSpace X] in
/-- The zero-dimensional actual family is nef Cartier, with the actual zero
Kähler form on the root as an explicit witness. -/
theorem isNefCartierAny_zero {S : ModelSystem 0 X} (D : WeilFamilyAny S) :
    IsNefCartierAny D := by
  let π : S.Model := ModelSystem.Model.root
  let κ : KahlerBackground 0 π.1.carrier := kahlerBackgroundZero
  refine ⟨π, 0, isRealizationAny_zero D π 0, κ, ?_⟩
  exact classNefWithRespectTo_zero κ

omit [ConnectedSpace X] in
/-- The same actual family satisfies the literal directed-net nef criterion. -/
theorem isNefAny_zero {S : ModelSystem 0 X} (D : WeilFamilyAny S) : IsNefAny D :=
  isNefAny_of_isNefCartierAny (isNefCartierAny_zero D)

end SGPT.Hodge.BDivChain.NativeDraft

namespace SGPT.Hodge.BDivChain.NativeDraft

open Filter SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending SGPT.BDivisor
open scoped Topology

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

/-- The directed-net nef condition agrees with the existing one in positive
dimension: both directions explicitly transport each actual model class and
each original nef Cartier witness along the family equivalence. -/
theorem isNefAny_iff_existing {S : ModelSystem n X} (hn : 0 < n)
    (D₀ : WeilFamilyAny S) : IsNefAny D₀ ↔ (toExisting S hn D₀).IsNef := by
  constructor
  · rintro ⟨ι, hp, hd, he, D, hD, hconv⟩
    let : Preorder ι := hp
    let : IsDirected ι (· ≤ ·) := hd
    let : Nonempty ι := he
    refine ⟨ι, hp, hd, he, fun i => toExisting S hn (D i),
      fun i => (isNefCartierAny_iff_existing hn (D i)).mp (hD i), ?_⟩
    intro π
    simpa only [toExisting_onModel] using hconv π
  · rintro ⟨ι, hp, hd, he, D, hD, hconv⟩
    let : Preorder ι := hp
    let : IsDirected ι (· ≤ ·) := hd
    let : Nonempty ι := he
    refine ⟨ι, hp, hd, he, fun i => fromExisting S hn (D i), ?_, ?_⟩
    · intro i
      apply (isNefCartierAny_iff_existing hn (fromExisting S hn (D i))).mpr
      simpa only [toExisting_fromExisting] using hD i
    · intro π
      simpa only [fromExisting_onModel, toExisting_onModel] using hconv π

end SGPT.Hodge.BDivChain.NativeDraft
