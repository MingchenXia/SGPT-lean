import SGPT.NAPotential.ProjectiveGraphAnalyticMap

/-!
# Actual smooth-open points evaluate the literal original graph algebra

Blueprint: `projective-graph-open-membership.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphPointEvaluation

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open SGPT.Okounkov
open ProjectiveGraphRegularEvaluation ProjectiveGraphProjection ProjectiveGraphAnalyticMap
open SGPT.Foundations.Analysis.FirstPass

/-- Original canonical global-section evaluation commutes with the actual original global pullback. -/
theorem sectionEvaluationHom_appTop {M Y : Scheme.{0}} (f : M ⟶ Spec (.of ℂ))
    (h : M ⟶ Y) (p : SchemeComplexPoint f) (r : Γ(Y, ⊤)) :
    sectionEvaluationHom f p (h.appTop r) =
      schemeComplexPointStalkEval f p (h.stalkMap (schemeComplexPointImage f p)
        (Y.presheaf.germ ⊤ (h (schemeComplexPointImage f p)) trivial r)) := by
  change schemeComplexPointStalkEval f p
    (M.presheaf.germ ⊤ (schemeComplexPointImage f p) trivial (h.appTop r)) = _
  rw [Scheme.Hom.germ_stalkMap_apply]
  rfl

/-- Canonical original evaluation of an actual spectrum global section is the actual native coefficient stalk evaluation. -/
theorem sectionEvaluationHom_spec {M : Scheme.{0}} (f : M ⟶ Spec (.of ℂ))
    (B : CommRingCat) (h : M ⟶ Spec B) (p : SchemeComplexPoint f) (b : B) :
    sectionEvaluationHom f p (h.appTop ((Scheme.ΓSpecIso B).inv b)) =
      schemeComplexPointStalkEval f p (h.stalkMap (schemeComplexPointImage f p)
        (StructureSheaf.toStalk B (h (schemeComplexPointImage f p)) b)) := by
  rw [sectionEvaluationHom_appTop]
  have hgerm : (Spec B).presheaf.germ ⊤ (h (schemeComplexPointImage f p)) trivial
      ((Scheme.ΓSpecIso B).inv b) = StructureSheaf.toStalk B (h (schemeComplexPointImage f p)) b :=
    StructureSheaf.algebraMap_germ_apply ⊤ _ trivial b
  rw [hgerm]

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)} {s : ℕ}
  (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U) (b : Fin s → X.functionField)
  (W : (Spec (.of (Algebra.adjoin Γ(X, U) (Set.range b)))).Opens)

/-- The actual original smooth-open point gives an actual ring homomorphism on the literal original graph algebra. -/
def graphPointEval (p : SchemeComplexPoint (openStructureMap (f := f) U hU b W)) :
    Algebra.adjoin Γ(X, U) (Set.range b) →+* ℂ :=
  (sectionEvaluationHom (openStructureMap (f := f) U hU b W) p).comp
    (W.ι.appTop.hom.comp (Scheme.ΓSpecIso (.of (Algebra.adjoin Γ(X, U) (Set.range b)))).inv.hom)

/-- Evaluation of the literal generator is exactly the actual global generator value in the original product map. -/
theorem graphPointEval_generator (p : SchemeComplexPoint (openStructureMap (f := f) U hU b W)) (i : Fin s) :
    graphPointEval (f := f) U hU b W p (⟨b i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ : Algebra.adjoin Γ(X, U) (Set.range b)) =
      sectionEvaluation (openStructureMap (f := f) U hU b W) (openGraphSection U b W i) p := rfl

/-- An actual point's original graph coefficient value is the exact actual native first-projection stalk value. -/
theorem graphPointEval_coefficient_stalk (p : SchemeComplexPoint (openStructureMap (f := f) U hU b W))
    (a : Γ(X, U)) :
    graphPointEval (f := f) U hU b W p (algebraMap Γ(X, U) (Algebra.adjoin Γ(X, U) (Set.range b)) a) =
      schemeComplexPointStalkEval (openStructureMap (f := f) U hU b W) p
        ((openProjection U hU b W).stalkMap
          (schemeComplexPointImage (openStructureMap (f := f) U hU b W) p)
          (X.presheaf.germ U (openProjection U hU b W
            (schemeComplexPointImage (openStructureMap (f := f) U hU b W) p))
            (projection_mem U hU b _) a)) := by
  change sectionEvaluationHom (openStructureMap (f := f) U hU b W) p
    (W.ι.appTop ((Scheme.ΓSpecIso (.of (Algebra.adjoin Γ(X, U) (Set.range b)))).inv
      (algebraMap Γ(X, U) (Algebra.adjoin Γ(X, U) (Set.range b)) a))) = _
  rw [sectionEvaluationHom_spec]
  rw [← projection_stalkMap_germ U hU b]
  congr 1
  dsimp only [openProjection]
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- Canonical original complex-point evaluation is exactly the original analytic value of an original regular section. -/
theorem canonical_value_original {Y : Scheme.{0}} (g : Y ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] (E : ClosedProjectiveEmbedding g)
    (V : Y.Opens) (r : Γ(Y, V)) (x : SchemeComplexPoint g) (hx : schemeComplexPointImage g x ∈ V) :
    schemeComplexPointStalkEval g x (Y.presheaf.germ V (schemeComplexPointImage g x) hx r) =
      schemeOpenRegularFunction g n E V r x := by
  let := E.isSeparated
  let := E.quasiCompact
  rw [schemeOpenRegularFunction_apply]
  exact (schemeNativeStalkGerm_eval g n x _).symm

/-- The literal graph coefficient evaluates to the actual original analytic section value at the actual first component. -/
theorem graphPointEval_coefficient (n : ℕ) [SmoothOfRelativeDimension n f]
    (E : ClosedProjectiveEmbedding f)
    (p : SchemeComplexPoint (openStructureMap (f := f) U hU b W)) (a : Γ(X, U)) :
    graphPointEval (f := f) U hU b W p (algebraMap Γ(X, U) (Algebra.adjoin Γ(X, U) (Set.range b)) a) =
      schemeOpenRegularFunction f n E U a
        (schemeComplexPointMap (openStructureMap (f := f) U hU b W) f (openProjection U hU b W) rfl p) := by
  rw [graphPointEval_coefficient_stalk]
  have h := schemeComplexPointStalkEval_comp (openStructureMap (f := f) U hU b W) f
    (openProjection U hU b W) rfl p
  refine (DFunLike.congr_fun h _).symm.trans ?_
  exact canonical_value_original f n E U a _ (projection_mem U hU b _)

/-- An original rational fraction identity holds in every actual original local stalk where both sections are regular. -/
theorem regular_fraction_value (n : ℕ) [SmoothOfRelativeDimension n f]
    (E : ClosedProjectiveEmbedding f) (V : X.Opens) (hV : genericPoint X ∈ V)
    (b₀ : X.functionField) (r : Γ(X, V))
    (hr : X.presheaf.germ V (genericPoint X) hV r = b₀)
    (d a : Γ(X, U)) (hrel : X.germToFunctionField U d * b₀ = X.germToFunctionField U a)
    (x : SchemeComplexPoint f) (hxU : schemeComplexPointImage f x ∈ U)
    (hxV : schemeComplexPointImage f x ∈ V) :
    schemeOpenRegularFunction f n E U d x * schemeOpenRegularFunction f n E V r x =
      schemeOpenRegularFunction f n E U a x := by
  let : Nonempty V := ⟨⟨genericPoint X, hV⟩⟩
  have hs : X.presheaf.germ U (schemeComplexPointImage f x) hxU d *
      X.presheaf.germ V (schemeComplexPointImage f x) hxV r =
        X.presheaf.germ U (schemeComplexPointImage f x) hxU a := by
    apply IsFractionRing.injective (X.presheaf.stalk (schemeComplexPointImage f x)) X.functionField
    rw [map_mul, Scheme.algebraMap_germ_eq_germToFunctionField,
      Scheme.algebraMap_germ_eq_germToFunctionField, Scheme.algebraMap_germ_eq_germToFunctionField]
    change X.germToFunctionField U d * X.presheaf.germ V (genericPoint X) hV r = _
    rw [hr]
    exact hrel
  have hpoint := congrArg (schemeComplexPointStalkEval f x) hs
  rw [map_mul, canonical_value_original f n E U d x hxU,
    canonical_value_original f n E V r x hxV, canonical_value_original f n E U a x hxU] at hpoint
  exact hpoint

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphPointEvaluation
