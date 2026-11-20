import SGPT.BDivisor.BD7BirationalProjection
import SGPT.BDivisor.BD7GAGA
import SGPT.Okounkov.SchemeNativeOpenJacobian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.BDivisor.BD7

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open scoped Manifold ContDiff

/-- An algebraic model in the sense of Dang--Favre, Section 1.2.
The projection is a literal proper birational morphism over the base. Since both varieties are
projective, its graph in the product also realizes it as a projective morphism. -/
structure SmoothAlgebraicModel {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (d : ℕ) where
  V : Scheme.{0}
  [integral : IsIntegral V]
  p : V ⟶ X
  [smooth : SmoothOfRelativeDimension d (p ≫ f)]
  embedding : ClosedProjectiveEmbedding (p ≫ f)
  [proper : IsProper p]
  [birational : IsIso (p.stalkMap (genericPoint V))]

attribute [instance] SmoothAlgebraicModel.integral SmoothAlgebraicModel.smooth
  SmoothAlgebraicModel.proper SmoothAlgebraicModel.birational

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {d : ℕ}

instance : Preorder (SmoothAlgebraicModel f d) where
  le A B := ∃ q : B.V ⟶ A.V, q ≫ A.p = B.p
  le_refl A := ⟨𝟙 A.V, Category.id_comp A.p⟩
  le_trans A B C := by
    rintro ⟨q, hq⟩ ⟨r, hr⟩
    exact ⟨r ≫ q, by rw [Category.assoc, hq, hr]⟩

local instance dfIndexPointTopology {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) :=
  schemeAnalyticPointTopology g

local instance dfIndexPointCharts {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] :
    ChartedSpace (ComplexModel n) (SchemeComplexPoint g) :=
  schemeAnalyticTNChartedSpace g n

local instance dfIndexPointManifold {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold n (SchemeComplexPoint g) :=
  schemeAnalyticTN_isComplexManifold g n

section SmoothBase

variable [IsIntegral X] [SmoothOfRelativeDimension d f]
  (E : ClosedProjectiveEmbedding f)

/-- The actual map of the algebraic model on complex points is proper bimeromorphic. -/
theorem SmoothAlgebraicModel.analyticModification (A : SmoothAlgebraicModel f d) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI := A.embedding.isSeparated
    letI := A.embedding.quasiCompact
    IsAnalyticModification (n := d) (schemeComplexPointMap (A.p ≫ f) f A.p rfl) := by
  let : LocallyOfFiniteType f := E.locallyOfFiniteType
  let : LocallyOfFiniteType (A.p ≫ f) := A.embedding.locallyOfFiniteType
  let : LocallyOfFiniteType A.p := locallyOfFiniteType_of_comp A.p f
  let : IsSeparated (A.p ≫ f) := A.embedding.isSeparated
  let : IsSeparated A.p := IsSeparated.of_comp (f := A.p) (g := f)
  obtain ⟨U, hU, hIso⟩ := exists_isIso_morphismRestrict_of_isIso_stalkMap A.p
  let := hIso
  exact isAnalyticModification_of_birational f E A.p A.embedding U hU

include E in
/-- A morphism over the base is unique. This is equality of the actual scheme morphisms. -/
theorem SmoothAlgebraicModel.homOver_ext {A B : SmoothAlgebraicModel f d}
    {q r : B.V ⟶ A.V} (hq : q ≫ A.p = B.p) (hr : r ≫ A.p = B.p) : q = r := by
  let := E.isSeparated
  let := E.quasiCompact
  let := A.embedding.isSeparated
  let := A.embedding.quasiCompact
  let := B.embedding.isSeparated
  let := B.embedding.quasiCompact
  let := A.embedding.locallyOfFiniteType
  let := B.embedding.locallyOfFiniteType
  let hqf : q ≫ (A.p ≫ f) = B.p ≫ f := by rw [← Category.assoc, hq]
  let hrf : r ≫ (A.p ≫ f) = B.p ≫ f := by rw [← Category.assoc, hr]
  let A' : Modification d (SchemeComplexPoint f) :=
    ⟨SchemeComplexPoint (A.p ≫ f), schemeComplexPointMap (A.p ≫ f) f A.p rfl,
      A.analyticModification E⟩
  let B' : Modification d (SchemeComplexPoint f) :=
    ⟨SchemeComplexPoint (B.p ≫ f), schemeComplexPointMap (B.p ≫ f) f B.p rfl,
      B.analyticModification E⟩
  have hcomm (a : B.V ⟶ A.V) (ha : a ≫ A.p = B.p)
      (haf : a ≫ (A.p ≫ f) = B.p ≫ f) :
      A'.map ∘ schemeComplexPointMap (B.p ≫ f) (A.p ≫ f) a haf = B'.map := by
    funext z
    change schemeComplexPointMap (A.p ≫ f) f A.p rfl
      (schemeComplexPointMap (B.p ≫ f) (A.p ≫ f) a haf z) =
        schemeComplexPointMap (B.p ≫ f) f B.p rfl z
    rw [← schemeComplexPointMap_comp (B.p ≫ f) (A.p ≫ f) f a haf A.p rfl]
    apply Subtype.ext
    change z.val ≫ (a ≫ A.p) = z.val ≫ B.p
    rw [ha]
  have hqH := NativeOpenJacobian.schemeComplexPointMap_contMDiff_of_structure
    (A.p ≫ f) (B.p ≫ f) q hqf d ∞
  have hrH := NativeOpenJacobian.schemeComplexPointMap_contMDiff_of_structure
    (A.p ≫ f) (B.p ≫ f) r hrf d ∞
  exact hom_ext_of_schemeComplexPointMap_eq (B.p ≫ f) (A.p ≫ f) hqf hrf
    (congrFun (Modification.Dominates.unique (π' := B') (π := A')
      hqH hrH (hcomm q hq hqf) (hcomm r hr hrf)))

/-- The unique algebraic transition for a domination. -/
def SmoothAlgebraicModel.homOfLE (A : SmoothAlgebraicModel f d) {B : SmoothAlgebraicModel f d}
    (h : A ≤ B) : B.V ⟶ A.V := Classical.choose h

omit [IsIntegral X] [SmoothOfRelativeDimension d f] in
theorem SmoothAlgebraicModel.homOfLE_over (A : SmoothAlgebraicModel f d)
    {B : SmoothAlgebraicModel f d} (h : A ≤ B) :
    A.homOfLE h ≫ A.p = B.p :=
  Classical.choose_spec h

include E in
theorem SmoothAlgebraicModel.homOfLE_refl (A : SmoothAlgebraicModel f d) :
    A.homOfLE (le_refl A) = 𝟙 A.V :=
  SmoothAlgebraicModel.homOver_ext E (A.homOfLE_over (le_refl A)) (Category.id_comp A.p)

include E in
theorem SmoothAlgebraicModel.homOfLE_trans {A B C : SmoothAlgebraicModel f d}
    (h : A ≤ B) (k : B ≤ C) :
    A.homOfLE (h.trans k) = B.homOfLE k ≫ A.homOfLE h :=
  SmoothAlgebraicModel.homOver_ext E (A.homOfLE_over (h.trans k))
    (by rw [Category.assoc, A.homOfLE_over h, B.homOfLE_over k])

variable [IsSeparated f] [QuasiCompact f] [CompactSpace (SchemeComplexPoint f)]

abbrev BookBlowupModel := (ModelSystem.blowup d (SchemeComplexPoint f)).Model

/-- A chosen algebraization records the exact projection and identification of complex points. -/
structure BookModelAlgebraization (π : BookBlowupModel (f := f) (d := d)) where
  A : SmoothAlgebraicModel f d
  e : letI := A.embedding.isSeparated
      letI := A.embedding.quasiCompact
      SchemeComplexPoint (A.p ≫ f) ≃ₘ⟮𝓘(ℂ, ComplexModel d), 𝓘(ℂ, ComplexModel d)⟯ π.1.carrier
  point_eq : ∀ z, schemeComplexPointMap (A.p ≫ f) f A.p rfl z = π.1.map (e z)

include E in
theorem nonempty_bookModelAlgebraization (π : BookBlowupModel (f := f) (d := d)) :
    Nonempty (BookModelAlgebraization π) := by
  obtain ⟨V, hV, p, hs, EV, hp, hb, e, he⟩ :=
    exists_proper_birational_projection_of_isBlowupSequence f d E π.2
  let A : SmoothAlgebraicModel f d :=
    { V := V
      integral := hV
      p := p
      smooth := hs
      embedding := EV
      proper := hp
      birational := hb }
  exact ⟨{ A := A, e := e, point_eq := congrFun he }⟩

/-- Use a proper birational algebraization for every tower of the book's system. -/
def chooseBookModelAlgebraization (E : ClosedProjectiveEmbedding f)
    (π : BookBlowupModel (f := f) (d := d)) : BookModelAlgebraization π :=
  Classical.choice (nonempty_bookModelAlgebraization E π)

variable (alg : ∀ π : BookBlowupModel (f := f) (d := d), BookModelAlgebraization π)

include E in
omit [IsIntegral X] in
theorem bookModelAlgebraization_monotone : Monotone (fun π => (alg π).A) := by
  intro π τ h
  let a := alg π
  let b := alg τ
  obtain ⟨q, _, _, hq⟩ :=
    exists_algebraic_domination f E gagaMorphismsSmooth h
      (a.A.p ≫ f) (b.A.p ≫ f) a.A.embedding b.A.embedding
      a.e b.e a.A.p rfl b.A.p rfl a.point_eq b.point_eq
  exact ⟨q, hq⟩

/-- The chosen algebraic transition induces exactly the dominating map of the book towers. -/
theorem bookModelAlgebraization_transition
    {π τ : BookBlowupModel (f := f) (d := d)} (h : π ≤ τ) :
    let a := alg π
    let b := alg τ
    let hA := bookModelAlgebraization_monotone E alg h
    let q := a.A.homOfLE hA
    let hq : q ≫ (a.A.p ≫ f) = b.A.p ≫ f :=
      (Category.assoc q a.A.p f).symm.trans (congrArg (fun p => p ≫ f) (a.A.homOfLE_over hA))
    ∀ z, a.e (schemeComplexPointMap (b.A.p ≫ f) (a.A.p ≫ f) q hq z) =
      Modification.homOfLE (show π.1 ≤ τ.1 from h) (b.e z) := by
  dsimp only
  obtain ⟨q, _, hmap, hq⟩ :=
    exists_algebraic_domination f E gagaMorphismsSmooth h
      ((alg π).A.p ≫ f) ((alg τ).A.p ≫ f)
      (alg π).A.embedding (alg τ).A.embedding (alg π).e (alg τ).e
      (alg π).A.p rfl (alg τ).A.p rfl (alg π).point_eq (alg τ).point_eq
  have heq := SmoothAlgebraicModel.homOver_ext E
    ((alg π).A.homOfLE_over (bookModelAlgebraization_monotone E alg h)) hq
  cases heq
  exact hmap

include E in
/-- Cofinality of any compatible choices of algebraizations of the book's towers. -/
theorem bookModelAlgebraization_cofinal (A : SmoothAlgebraicModel f d) :
    ∃ π : BookBlowupModel (f := f) (d := d), A ≤ (alg π).A := by
  let : LocallyOfFiniteType f := E.locallyOfFiniteType
  let : LocallyOfFiniteType (A.p ≫ f) := A.embedding.locallyOfFiniteType
  let : LocallyOfFiniteType A.p := locallyOfFiniteType_of_comp A.p f
  let : IsSeparated (A.p ≫ f) := A.embedding.isSeparated
  let : IsSeparated A.p := IsSeparated.of_comp (f := A.p) (g := f)
  obtain ⟨U, hU, hIso⟩ := exists_isIso_morphismRestrict_of_isIso_stalkMap A.p
  let := hIso
  obtain ⟨π, γ, hγ, hprojection, _⟩ :=
    exists_blowupModel_dominates f E (d := d) A.p A.embedding U hU
  let B := alg π
  let := B.A.embedding.locallyOfFiniteType
  obtain ⟨q, hq, hmap⟩ := gagaMorphismsSmooth B.A.V A.V
    (B.A.p ≫ f) (A.p ≫ f) d d B.A.embedding A.embedding (γ ∘ B.e)
    (hγ.comp B.e.contMDiff)
  refine ⟨π, q, ?_⟩
  apply hom_ext_of_schemeComplexPointMap_eq (B.A.p ≫ f) f
    (show (q ≫ A.p) ≫ f = B.A.p ≫ f by rw [Category.assoc, hq]) rfl
  intro z
  rw [schemeComplexPointMap_comp (B.A.p ≫ f) (A.p ≫ f) f q hq A.p rfl, hmap z]
  exact (congrFun hprojection (B.e z)).trans (B.point_eq z).symm

include E in
/-- Any two smooth algebraic models are dominated by a third such model. -/
theorem smoothAlgebraicModel_directed (A B : SmoothAlgebraicModel f d) :
    ∃ C : SmoothAlgebraicModel f d, A ≤ C ∧ B ≤ C := by
  let alg := chooseBookModelAlgebraization (d := d) E
  obtain ⟨π, hA⟩ := bookModelAlgebraization_cofinal E alg A
  obtain ⟨τ, hB⟩ := bookModelAlgebraization_cofinal E alg B
  obtain ⟨σ, hπ, hτ⟩ := ModelSystem.Model.exists_le_le π τ
  exact ⟨(alg σ).A, hA.trans (bookModelAlgebraization_monotone E alg hπ),
    hB.trans (bookModelAlgebraization_monotone E alg hτ)⟩

end SmoothBase
end SGPT.BDivisor.BD7
