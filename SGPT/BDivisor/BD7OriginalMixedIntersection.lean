import SGPT.BDivisor.BD7CommonModelMixedDegree
import SGPT.BDivisor.BD7OriginalNefLimits
import SGPT.BDivisor.BD7MixedDegreeNaturality

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.BDivisor.BD7

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes MeasureTheory SGPT.Okounkov
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.BDivisor.DangFavre SGPT.BDivisor.DFAlg
open SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.SourceNefIntersectionDraft
open scoped Manifold ContDiff

local instance originalMixedTopology {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g

local instance originalMixedCharts {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] : ChartedSpace (ComplexModel d) (SchemeComplexPoint g) :=
  schemeAnalyticTNChartedSpace g d

local instance originalMixedManifold {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold d (SchemeComplexPoint g) := schemeAnalyticTN_isComplexManifold g d

variable {Z : Scheme.{0}} {f : Z ⟶ Spec (.of ℂ)} {m : ℕ}
    [IsIntegral Z] [SmoothOfRelativeDimension (m + 1) f]
    [IsSeparated f] [QuasiCompact f] [CompactSpace (SchemeComplexPoint f)]
    [ConnectedSpace (SchemeComplexPoint f)] (E : ClosedProjectiveEmbedding f)

local notation "M" => SmoothAlgebraicModel f (m + 1)
local notation "N" => SmoothModelNumericalClasses (f := f) (d := m + 1)
local notation "Book" => BookBlowupModel (f := f) (d := m + 1)
local notation "Chosen" => fun π : Book => chooseBookModelAlgebraization E π
local notation "AlgebraicWeil" => compatibleLinearFamilies (R := ℝ) (I := M) (E := N)
    (smoothModelOriginalCyclePushforward E)
local notation "Read" => canonicalOriginalNumericalWeilEquiv E

/-- The ordinary multilinear degree of determining Cartier divisors on a common
original algebraic model. The representatives and the line used in the finite
differences are quantified independently. -/
def IsOriginalMixedTopDegree (C : Fin (m + 1) → AlgebraicWeil) (x : ℝ) : Prop :=
  ∃ (A : M) (B : IntrinsicLineBundle A.V) (v : Fin (m + 1) → CartierCombinations A.V),
    (∀ i, IsOriginalNumericallyDeterminedOn (C i) A
      ((originalIntegralCurveDegreeRelations_bd7 (A.p ≫ f) A.embedding).mkQ (v i))) ∧
    x = originalRealMixedEuler (A.p ≫ f) A.embedding (m + 1) B v

/-- A common nef realization lifts to genuine algebraic determining Cartier
divisors. Their ordinary top degree is the scalar of the realization. -/
theorem isOriginalMixedTopDegree_of_realization (C : Fin (m + 1) → AlgebraicWeil)
    (r : CommonNefRealization (fun i => (Read (C i)).val)) :
    IsOriginalMixedTopDegree E C r.intersection := by
  classical
  let A := ((Chosen) r.model).A
  let Q := originalIntegralCurveDegreeRelations_bd7 (A.p ≫ f) A.embedding
  let w (i : Fin (m + 1)) := (C i).val A
  choose v hv using fun i => Q.mkQ_surjective (w i)
  have hclass (i : Fin (m + 1)) : (bookModelNumericalChern Chosen r.model (w i)).val =
      (Read (C i)).val.val r.model :=
    (canonicalOriginalNumericalWeilEquiv_apply E (C i) r.model).symm
  have hdet (i : Fin (m + 1)) : IsOriginalNumericallyDeterminedOn (C i) A (w i) := by
    apply canonicalOriginalDetermination_of_bookRealization E (C i) r.model (w i)
    rw [hclass, r.realizes i r.model le_rfl, Modification.classPullbackOfLE_refl]
    exact r.realizes i
  refine ⟨A, trivialIntrinsicLineBundle A.V, v, fun i => ?_, ?_⟩
  · change IsOriginalNumericallyDeterminedOn (C i) A (Q.mkQ (v i))
    rw [hv i]
    exact hdet i
  · have hC (i : Fin (m + 1)) :
        (bookModelNumericalChern Chosen r.model (Q.mkQ (v i))).val =
          (Read (C i)).val.val r.model := by
      exact (congrArg (fun z : N A => (bookModelNumericalChern Chosen r.model z).val)
        (hv i)).trans (hclass i)
    exact commonNefRealization_intersection_eq_originalMixedDegree_bd7 f E Chosen r
      (trivialIntrinsicLineBundle A.V) v hC

/-- The ordinary mixed top degree is independent of all original choices of
determining algebraic model and of Cartier representatives. -/
theorem IsOriginalMixedTopDegree.unique {C : Fin (m + 1) → AlgebraicWeil} {x y : ℝ}
    (hx : IsOriginalMixedTopDegree E C x) (hy : IsOriginalMixedTopDegree E C y) : x = y := by
  classical
  obtain ⟨A, LA, a, ha, rfl⟩ := hx
  obtain ⟨B, LB, b, hb, rfl⟩ := hy
  obtain ⟨P, hAP, hBP⟩ := smoothAlgebraicModel_directed E A B
  let Q := originalIntegralCurveDegreeRelations_bd7 (P.p ≫ f) P.embedding
  let LP := trivialIntrinsicLineBundle P.V
  choose p hp using fun i => Q.mkQ_surjective ((C i).val P)
  have hA := originalMixedDegree_eq_of_numerical_pullback_bd7 f E hAP LA LP a p (by
    intro i
    change smoothModelNumericalCartierPullback hAP
      ((originalIntegralCurveDegreeRelations_bd7 (A.p ≫ f) A.embedding).mkQ (a i)) = Q.mkQ (p i)
    exact (ha i P hAP).symm.trans (hp i).symm)
  have hB := originalMixedDegree_eq_of_numerical_pullback_bd7 f E hBP LB LP b p (by
    intro i
    change smoothModelNumericalCartierPullback hBP
      ((originalIntegralCurveDegreeRelations_bd7 (B.p ≫ f) B.embedding).mkQ (b i)) = Q.mkQ (p i)
    exact (hb i P hBP).symm.trans (hp i).symm)
  exact hA.symm.trans hB

/-- The independent ordinary top degree of an original nef Cartier tuple is the
book's top product for its Chern classes. -/
theorem IsOriginalMixedTopDegree.eq_book {C : Fin (m + 1) → AlgebraicWeil} {x : ℝ}
    (hx : IsOriginalMixedTopDegree E C x) (hC : ∀ i, IsOriginalNefCartier E (C i)) :
    x = (nefIntersection (fun i => (Read (C i)).val)).toReal := by
  letI : MeasurableSpace (SchemeComplexPoint f) := borel _
  letI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  let κ := SGPT.Okounkov.schemeProjectiveTNKahlerBackground f (m + 1) E
  obtain ⟨r⟩ := nonempty_commonNefRealization κ (fun i => (Read (C i)).val)
    (fun i => ((originalNefCartier_iff_book E (C i)).mp (hC i)).isNefCartierAny)
  exact (hx.unique E (isOriginalMixedTopDegree_of_realization E C r)).trans (r.intersection_eq κ)

end SGPT.BDivisor.BD7
