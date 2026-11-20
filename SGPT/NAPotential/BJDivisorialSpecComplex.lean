import SGPT.NAPotential.BJDivisorialZero

/-!
# The corrected determining set on the actual complex point

Source: SGPT revision 69360cfd, chapter_NApotential.tex:909 and
`thm:pshdetbydiv`. The revised source includes the actual trivial valuation
in its divisorial test set. We keep the existing strict `divisorialSet`
unchanged and define the revised source set explicitly. The actual complex
point comparison and uniqueness follow from its residue-field geometry.
This does not assert the all-dimensional BJ theorem or identify the
projective and proper model presentations needed at that import boundary.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.Berkovich

open Set AlgebraicGeometry CategoryTheory

/-- The revised source convention: include the trivial valuation together
with the project's strict positive-rational divisorial points. -/
def sourceDivisorialSet {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) [IrreducibleSpace X] :
    Set (BerkovichPoint f) :=
  insert (BerkovichPoint.trivial f) (divisorialSet f)

/-- The new source convention is exactly the already constructed augmented
formal set; this is not a projective/proper model comparison. -/
theorem sourceDivisorialSet_eq_bjDivisorialSet {X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) [IrreducibleSpace X] :
    sourceDivisorialSet f = bjDivisorialSet f := rfl

/-- The trivial point belongs to the revised determining set. -/
theorem trivial_mem_sourceDivisorialSet {X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) [IrreducibleSpace X] :
    BerkovichPoint.trivial f ∈ sourceDivisorialSet f := by
  exact Set.mem_insert _ _

/-- The old strict divisorial points are retained by the revised source. -/
theorem divisorialSet_subset_sourceDivisorialSet {X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) [IrreducibleSpace X] :
    divisorialSet f ⊆ sourceDivisorialSet f := by
  intro v hv
  exact Set.mem_insert_of_mem _ hv


/-- The revised real-scaled source set also contains the trivial valuation. -/
def sourceDivisorialSetReal {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) [IrreducibleSpace X] :
    Set (BerkovichPoint f) :=
  insert (BerkovichPoint.trivial f) (divisorialSetReal f)

theorem mem_sourceDivisorialSet_iff {X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) [IrreducibleSpace X] (v : BerkovichPoint f) :
    v ∈ sourceDivisorialSet f ↔ v = BerkovichPoint.trivial f ∨ v ∈ divisorialSet f := Iff.rfl

theorem mem_sourceDivisorialSetReal_iff {X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) [IrreducibleSpace X] (v : BerkovichPoint f) :
    v ∈ sourceDivisorialSetReal f ↔
      v = BerkovichPoint.trivial f ∨ v ∈ divisorialSetReal f := Iff.rfl

theorem trivial_mem_sourceDivisorialSetReal {X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) [IrreducibleSpace X] :
    BerkovichPoint.trivial f ∈ sourceDivisorialSetReal f := by
  exact Set.mem_insert _ _

theorem divisorialSetReal_subset_sourceDivisorialSetReal {X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) [IrreducibleSpace X] :
    divisorialSetReal f ⊆ sourceDivisorialSetReal f := by
  intro v hv
  exact Set.mem_insert_of_mem _ hv

theorem sourceDivisorialSet_subset_real {X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) [IrreducibleSpace X] :
    sourceDivisorialSet f ⊆ sourceDivisorialSetReal f := by
  intro v hv
  rcases hv with hv | hv
  · rw [hv]
    exact trivial_mem_sourceDivisorialSetReal f
  · exact Set.mem_insert_of_mem _ (divisorialSet_subset_real f hv)

/-- The actual structure morphism of the book's complex-point example. -/
abbrev complexPointStructure : Spec (.of ℂ) ⟶ Spec (.of ℂ) := 𝟙 _

-- Make all source-geometric hypotheses of the previously checked theorem
-- visible here; none is a comparison or an output assumption.
example : Subsingleton (Spec (.of ℂ)) := inferInstance
example : IrreducibleSpace (Spec (.of ℂ)) := inferInstance
example : LocallyOfFiniteType complexPointStructure := inferInstance

/-- The actual Berkovich analytification of `Spec ℂ` has its trivial point
as its only point. -/
theorem specComplex_point_eq_trivial (v : BerkovichPoint complexPointStructure) :
    v = BerkovichPoint.trivial complexPointStructure :=
  berkovichPoint_eq_trivial_of_singleton complexPointStructure
    (residueComplexHom_surjective_of_singleton complexPointStructure) v

/-- The augmented test set is literally the whole analytification of
`Spec ℂ`, independently of whether the strict divisorial set has been
separately proved empty. -/
theorem specComplex_augmentedDivisorialSet_eq_univ :
    bjDivisorialSet complexPointStructure = Set.univ := by
  ext v
  simp only [Set.mem_univ, iff_true]
  rw [specComplex_point_eq_trivial v]
  exact trivial_mem_bjDivisorialSet complexPointStructure

/-- On the actual complex point, the corrected comparison works for arbitrary
preorder-valued functions and therefore in particular does not need an extra
usc or psh hypothesis. -/
theorem specComplex_le_of_augmentedDivisorial_le {α : Type*} [Preorder α]
    (φ ψ : BerkovichPoint complexPointStructure → α)
    (h : ∀ v ∈ bjDivisorialSet complexPointStructure, φ v ≤ ψ v) :
    ∀ v, φ v ≤ ψ v :=
  le_of_bjDivisorialSet_le_of_finiteType_singleton complexPointStructure φ ψ h


/-- The revised book's determining set is the entire analytification of
its actual complex-point example. -/
theorem specComplex_sourceDivisorialSet_eq_univ :
    sourceDivisorialSet complexPointStructure = Set.univ := by
  rw [sourceDivisorialSet_eq_bjDivisorialSet]
  exact specComplex_augmentedDivisorialSet_eq_univ

/-- The real-scaled revised test set is also the whole analytification
of the actual complex point. -/
theorem specComplex_sourceDivisorialSetReal_eq_univ :
    sourceDivisorialSetReal complexPointStructure = Set.univ := by
  ext v
  simp only [Set.mem_univ, iff_true]
  rw [specComplex_point_eq_trivial v]
  exact trivial_mem_sourceDivisorialSetReal complexPointStructure

/-- Revised source comparison on the actual complex point; the only
comparison input is on the source's stated determining set. -/
theorem specComplex_le_of_sourceDivisorial_le {α : Type*} [Preorder α]
    (φ ψ : BerkovichPoint complexPointStructure → α)
    (h : ∀ v ∈ sourceDivisorialSet complexPointStructure, φ v ≤ ψ v) :
    ∀ v, φ v ≤ ψ v := by
  apply specComplex_le_of_augmentedDivisorial_le φ ψ
  exact h

/-- A function on the actual complex point is determined by its restriction
to the revised source divisorial set. No order or psh assumption is needed. -/
theorem specComplex_eq_of_eqOn_sourceDivisorial {α : Type*}
    (φ ψ : BerkovichPoint complexPointStructure → α)
    (h : Set.EqOn φ ψ (sourceDivisorialSet complexPointStructure)) : φ = ψ := by
  funext v
  apply h
  rw [specComplex_sourceDivisorialSet_eq_univ]
  trivial


end SGPT.NAPotential.Berkovich
