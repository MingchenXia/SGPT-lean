import SGPT.Checks.LiteratureBridge.BJValuation
import SGPT.Foundations.PublishedEnvelope.Berkovich.SchemeRelativeValuedPoints

/-! # Underlying points of the two actual Berkovich spaces

This dictionary fixes the same scheme support point and compares its two
residue-valued descriptions. The relative condition is derived from the actual
structure morphism rather than imposed as a separate certificate.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory Opposite
open SGPT.NAPotential.Berkovich
open SGPT.Foundations.PublishedEnvelope.Berkovich
open scoped NNReal

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))

/-- The canonical residue-field point evaluates global functions at the
original scheme point. This is the foundational calculation also used by
`SchemeValuedPoint.fromSpecResidueField_appTop`, independent of proper centers. -/
private theorem fromSpecResidueField_appTop (x : X) :
    (X.fromSpecResidueField x).appTop ≫ (Scheme.ΓSpecIso (X.residueField x)).hom =
      X.Γevaluation x := by
  rw [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop,
    Category.assoc, Scheme.ΓSpecIso_naturality]
  rw [Scheme.fromSpecStalk_appTop]
  simp only [homOfLE_refl, op_id]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.comp_id, Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- The source's residue-field coefficient map is the actual evaluation of the
structure morphism on global sections. -/
theorem residueComplexHom_eq_evaluation (x : X) :
    residueComplexHom f x =
      (Scheme.ΓSpecIso (.of ℂ)).inv ≫ f.appTop ≫ X.Γevaluation x := by
  have h := Scheme.ΓSpecIso_naturality (residueComplexHom f x)
  rw [spec_map_residueComplexHom, Scheme.Hom.comp_appTop, Category.assoc,
    fromSpecResidueField_appTop] at h
  apply (cancel_epi (Scheme.ΓSpecIso (.of ℂ)).hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h.symm

/-- Evaluation of a complex coefficient agrees with evaluation after mapping
the actual valued point to the native affine base. -/
theorem eval_residueComplexHom (y : SchemeValuedPoint X) (c : ℂ) :
    y.residueVal ((residueComplexHom f y.point).hom c) =
      SchemeValuedPoint.eval (SchemeValuedPoint.map f y) ⊤ trivial
        ((Scheme.ΓSpecIso (.of ℂ)).inv c) := by
  rw [SchemeValuedPoint.evalTop_map, residueComplexHom_eq_evaluation]
  rfl

/-- The native relative locus over the trivial complex valuation is exactly
triviality on the source's canonical complex subfield. -/
theorem mem_trivialRelativeLocus_iff (y : SchemeValuedPoint X) :
    y ∈ SchemeValuedPoint.relativeLocus (1 : Valuation ℂ ℝ≥0) f ↔
      ∀ c : ℂ, c ≠ 0 → y.residueVal ((residueComplexHom f y.point).hom c) = 1 := by
  constructor
  · intro hy c hc
    have h := congrArg (fun z : SchemeValuedPoint (Spec (.of ℂ)) =>
      SchemeValuedPoint.eval z ⊤ trivial ((Scheme.ΓSpecIso (.of ℂ)).inv c)) hy
    rw [SchemeValuedPoint.basePoint_eval, Valuation.one_apply_of_ne_zero hc] at h
    exact (eval_residueComplexHom f y c).trans h
  · intro hy
    change SchemeValuedPoint.map f y = SchemeValuedPoint.basePoint (1 : Valuation ℂ ℝ≥0)
    apply (SchemeValuedPoint.spectrumHomeomorph (A := ℂ)).injective
    apply Spectrum.ext_val
    intro c
    rw [SchemeValuedPoint.spectrumHomeomorph_val_apply,
      SchemeValuedPoint.spectrumHomeomorph_val_apply,
      SchemeValuedPoint.basePoint_eval, ← eval_residueComplexHom f y c]
    by_cases hc : c = 0
    · subst c
      simp
    · rw [hy c hc, Valuation.one_apply_of_ne_zero hc]

/-- Convert the book's valuation into the native relative point on the same
actual support point and residue field. -/
def toNative (v : BerkovichPoint f) : RelativeSchemeValuedPoint (1 : Valuation ℂ ℝ≥0) f := by
  letI := residueComplexAlgebra f v.support
  refine ⟨⟨v.support, SourceRealValuation.toNNRealValuation v.val⟩, ?_⟩
  apply (mem_trivialRelativeLocus_iff f _).mpr
  intro c hc
  exact SourceRealValuation.toNNRealValuation_complex v.val c hc

/-- Convert the native residue valuation back by negative logarithm. -/
def ofNative (v : RelativeSchemeValuedPoint (1 : Valuation ℂ ℝ≥0) f) : BerkovichPoint f := by
  letI := residueComplexAlgebra f v.1.point
  refine ⟨v.1.point, SourceRealValuation.ofNNRealValuation v.1.residueVal ?_⟩
  exact (mem_trivialRelativeLocus_iff f v.1).mp v.2

@[simp] theorem toNative_point (v : BerkovichPoint f) : (toNative f v).1.point = v.support := rfl
@[simp] theorem ofNative_support (v : RelativeSchemeValuedPoint (1 : Valuation ℂ ℝ≥0) f) :
    (ofNative f v).support = v.1.point := rfl

/-- The two residue-field descriptions define the same points over the
trivially valued base, without projectivity or an auxiliary choice. -/
def pointEquiv : BerkovichPoint f ≃ RelativeSchemeValuedPoint (1 : Valuation ℂ ℝ≥0) f where
  toFun := toNative f
  invFun := ofNative f
  left_inv v := by
    cases v with
    | mk x val =>
      let : Algebra ℂ (X.residueField x) := residueComplexAlgebra f x
      dsimp only [ofNative,toNative]
      congr 1
      apply SourceRealValuation.ext
      intro g
      exact negLogNN_expNegNN (val g)
  right_inv v := by
    apply Subtype.ext
    rcases v with ⟨⟨x, w⟩, hw⟩
    dsimp only [toNative,ofNative]
    congr 1
    apply Valuation.ext
    intro g
    exact expNegNN_negLogNN (w g)

/-- The correspondence retains the actual support, not merely its closure. -/
@[simp] theorem pointEquiv_point (v : BerkovichPoint f) :
    (pointEquiv f v).1.point = v.support := rfl

/-- Every element of the common residue field retains its true value under
the additive-to-multiplicative conversion. -/
theorem pointEquiv_residueVal (v : BerkovichPoint f) (g : X.residueField v.support) :
    ((pointEquiv f v).1.residueVal g : ℝ) = BerkovichPoint.expNeg (v.valAt g) := rfl

/-- Actual evaluation of every regular section is preserved, including zero. -/
theorem pointEquiv_eval (v : BerkovichPoint f) (U : X.Opens) (hv : v.support ∈ U)
    (s : Γ(X, U)) :
    (SchemeValuedPoint.eval (pointEquiv f v).1 U hv s : ℝ) =
      BerkovichPoint.expNeg (v.sectionVal U hv s) := rfl

end SGPT.NAPotential.BJ
