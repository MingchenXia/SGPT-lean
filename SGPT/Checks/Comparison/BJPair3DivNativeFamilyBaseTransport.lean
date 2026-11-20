import SGPT.Checks.Comparison.BJPair3DivNativeOriginalFamilyValuation

-- Lane BJ-PAIR (R5/thm:pshdetbydiv bridge): ported from `SGPT.Checks.Literature/SGPT.Checks.Literature/BJDivisorial/NativeFamilyBaseTransport.lean`
-- (that library pins another SGPT.Foundations.Envelope revision and cannot be imported here); only the
-- imports, the `Alterations` namespace (now `SGPT.Support.Alterations`) and this file's namespace
-- (`Divisorial` -> `Pair3Div`, `ExternalClassStability` -> `Pair3ClassStability`) are changed.

/-! # Canonical original base transport retains the whole generic valuation
The Segre structure equals the source structure by the actual geometric
morphism theorem. Equality transport retains the SAME original support and
the SAME field valuation; no equivalence or GAGA assumption is supplied.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial SGPT.Support.Alterations
open scoped Classical NNReal

namespace SGPT.NAPotential.BJ.Pair3Div
open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.Berkovich

universe u
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  {r : ℕ} {d : Fin (r+1) → ℕ}
  (q : ∀ c, X ⟶ projectiveSpace k (d c)) (p : X ⟶ Spec (.of k))
  (hp : ∀ c, q c ≫ projectiveSpaceStructure k (d c) = p)
  [IsClosedImmersion (q 0)]

/-- Equality transport along the actual original base morphism equality. -/
def familyBaseChange (b : X ⟶ Spec (.of k))
    (hb : ∀ c, q c ≫ projectiveSpaceStructure k (d c) = b) (h : b = p) :
    (letI := b.stalkAlgebra (genericPoint X); (FiniteProjectiveNativeFieldModels.model q b hb).an) ≃ₜ
      (letI := p.stalkAlgebra (genericPoint X); (FiniteProjectiveNativeFieldModels.model q p hp).an) := by
  cases h
  exact Homeomorph.refl _

/-- Genuine whole generic support is preserved by this actual equality transport. -/
theorem familyBaseChange_hasGenericSupport (b : X ⟶ Spec (.of k))
    (hb : ∀ c, q c ≫ projectiveSpaceStructure k (d c) = b) (h : b = p)
    (v : letI := b.stalkAlgebra (genericPoint X); (FiniteProjectiveNativeFieldModels.model q b hb).an) :
    (letI := b.stalkAlgebra (genericPoint X);
      (FiniteProjectiveNativeFieldModels.model q b hb).HasGenericSupport v.1) ↔
    (letI := p.stalkAlgebra (genericPoint X);
      (FiniteProjectiveNativeFieldModels.model q p hp).HasGenericSupport
        (familyBaseChange q p hp b hb h v).1) := by
  cases h
  rfl

/-- Every original field fraction keeps its value under the actual base equality. -/
theorem familyBaseChange_fieldVal (b : X ⟶ Spec (.of k))
    (hb : ∀ c, q c ≫ projectiveSpaceStructure k (d c) = b) (h : b = p)
    (v : letI := b.stalkAlgebra (genericPoint X); (FiniteProjectiveNativeFieldModels.model q b hb).an)
    (hg : letI := b.stalkAlgebra (genericPoint X);
      (FiniteProjectiveNativeFieldModels.model q b hb).HasGenericSupport v.1) :
    (letI := b.stalkAlgebra (genericPoint X);
      (FiniteProjectiveNativeFieldModels.model q b hb).fieldVal v hg) =
    (letI := p.stalkAlgebra (genericPoint X);
      (FiniteProjectiveNativeFieldModels.model q p hp).fieldVal
        (familyBaseChange q p hp b hb h v)
        ((familyBaseChange_hasGenericSupport q p hp b hb h v).mp hg)) := by
  cases h
  rfl

private abbrev f := FiniteSegreOriginalProjectiveMaps.morphism d q p hp
private abbrev b := f q p hp ≫ projectiveSpaceStructure k (FiniteSegreOriginalProjectiveMaps.dimension d)
private abbrev hb := fun c => (hp c).trans (FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp).symm
private abbrev P := letI := p.stalkAlgebra (genericPoint X); FiniteProjectiveNativeFieldModels.model q p hp
private abbrev e := OriginalProjectiveDiagonalNativeComparison.originalNativeModelHomeomorph q p hp

/-- The canonical public all-point homeomorphism uses exactly this equality
transport of the SAME original Segre point map. -/
theorem canonicalFamilyHomeomorph_factor :
    e q p hp =
      (OriginalProjectiveDiagonalNativeComparison.originalNativeSegreBaseModelHomeomorph q p hp).trans
        (familyBaseChange q p hp (b q p hp) (hb q p hp)
          (FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp)) := rfl

/-- Native generic support DERIVES actual generic support under the exact
canonical public original/native finite-family homeomorphism. -/
theorem canonical_original_generic_support
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p)
    (hg : letI := p.stalkAlgebra (genericPoint X);
      (P q p hp).HasGenericSupport (e q p hp y).1) :
    y.1.point = genericPoint X := by
  let := (b q p hp).stalkAlgebra (genericPoint X)
  let yb : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (b q p hp) :=
    (Homeomorph.setCongr (by rw [show b q p hp = p from
      FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp])) y
  have hgb : (FiniteProjectiveNativeFieldModels.model q (b q p hp) (hb q p hp)).HasGenericSupport
      (OriginalProjectiveFamilyNativeChartValues.homeomorph q p hp yb).1 := by
    apply (familyBaseChange_hasGenericSupport q p hp (b q p hp) (hb q p hp)
      (FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp) _).mpr
    exact hg
  exact family_original_generic_support q p hp yb hgb

/-- At the SAME canonical point, the original whole K(X) valuation is the
actual native model fieldVal on every fraction. -/
theorem canonical_original_genericValuation_eq
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p)
    (hg : letI := p.stalkAlgebra (genericPoint X);
      (P q p hp).HasGenericSupport (e q p hp y).1) :
    letI := p.stalkAlgebra (genericPoint X)
    SchemeValuedPoint.genericValuation y.1 (canonical_original_generic_support q p hp y hg) =
      (P q p hp).fieldVal (e q p hp y) hg := by
  let := (b q p hp).stalkAlgebra (genericPoint X)
  let yb : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (b q p hp) :=
    (Homeomorph.setCongr (by rw [show b q p hp = p from
      FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp])) y
  have hgb : (FiniteProjectiveNativeFieldModels.model q (b q p hp) (hb q p hp)).HasGenericSupport
      (OriginalProjectiveFamilyNativeChartValues.homeomorph q p hp yb).1 := by
    apply (familyBaseChange_hasGenericSupport q p hp (b q p hp) (hb q p hp)
      (FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp) _).mpr
    exact hg
  exact (family_original_genericValuation_eq q p hp yb hgb).trans
    (familyBaseChange_fieldVal q p hp (b q p hp) (hb q p hp)
      (FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp) _ hgb)

end SGPT.NAPotential.BJ.Pair3Div
