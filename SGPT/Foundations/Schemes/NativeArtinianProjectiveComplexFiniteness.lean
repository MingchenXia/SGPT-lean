import SGPT.Foundations.Schemes.NativeRegularProjectiveFlag
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.Jacobson.Artinian

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- At the actual top open, the original affine structural algebra is EXACTLY
that induced by the original global structural constants. -/
theorem affineChartAlgebra_top_eq {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) :
    affineChartAlgebra p ⊤ = (schemeGlobalConstants p).toAlgebra := by
  change (((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop ≫
    X.presheaf.map (⊤ : X.Opens).leTop.op).hom).toAlgebra =
      (((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom).toAlgebra
  have hi : (⊤ : X.Opens).leTop.op = 𝟙 (op (⊤ : X.Opens)) := Subsingleton.elim _ _
  rw [hi, X.presheaf.map_id, Category.comp_id]

/-- Actual projective Artinian geometry produces finite complex dimension
of the SAME actual global ring with ORIGINAL structural complex constants. -/
theorem ClosedProjectiveEmbedding.artinian_globalSections_finite
    {X : Scheme} {p : X ⟶ Spec (.of ℂ)} (P : ClosedProjectiveEmbedding p)
    [IsArtinianScheme X] :
    letI := (schemeGlobalConstants p).toAlgebra
    Module.Finite ℂ Γ(X, ⊤) := by
  let := (schemeGlobalConstants p).toAlgebra
  have := P.locallyOfFiniteType
  have : Algebra.FiniteType ℂ Γ(X, ⊤) := by
    have hf := affineChartAlgebra_finiteType p (isAffineOpen_top X)
    rw [affineChartAlgebra_top_eq p] at hf
    exact hf
  have : IsArtinianRing Γ(X, ⊤) :=
    IsLocallyArtinian.isArtinianRing_presheaf_obj ⟨⊤, isAffineOpen_top X⟩
  exact Module.finite_of_isArtinianRing ℂ Γ(X, ⊤)

/-- The ACTUAL terminal Fano zero-cut ring has finite complex dimension,
with no numerical length/coefficient certificate and no reducedness premise. -/
theorem SmoothProjectiveFano.nativeRegularProjectiveFlag_terminal_globalSections_finite
    {n : ℕ} (F : SmoothProjectiveFano n) :
    let T := F.nativeRegularProjectiveFlag n
    letI := (schemeGlobalConstants (T.val.hom ≫
      polynomialProjStructureMap ℂ F.projective.ambientDimension)).toAlgebra
    Module.Finite ℂ Γ(T.val.left, ⊤) := by
  let := F.nativeRegularProjectiveFlag_terminal_isArtinian
  exact (F.nativeRegularProjectiveFlag n).embedding.artinian_globalSections_finite

end
end SGPT.Foundations.Schemes
