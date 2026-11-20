import SGPT.Foundations.Schemes.DiscreteLineStalkSections

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- The LITERAL singleton germ preserves exact ORIGINAL structural constants
and yields an algebra equivalence with the SAME actual stalk. -/
def discreteSingletonGermAlgEquiv {K : Type u} [Field K] {X : Scheme.{u}}
    [DiscreteTopology X] (p : X ⟶ Spec (.of K)) (x : X) :
    letI := affineChartAlgebra p (discreteSingletonOpen X x)
    letI := schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants p) x
    Γ(X, discreteSingletonOpen X x) ≃ₐ[K] X.presheaf.stalk x := by
  letI := affineChartAlgebra p (discreteSingletonOpen X x)
  letI := schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants p) x
  refine { (discreteSingletonGermIso X x).commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro k
  change X.presheaf.germ (discreteSingletonOpen X x) x (Set.mem_singleton x)
    (X.presheaf.map (discreteSingletonOpen X x).leTop.op (schemeGlobalConstants p k)) =
      X.presheaf.Γgerm x (schemeGlobalConstants p k)
  exact X.presheaf.Γgerm_res_apply x (Set.mem_singleton x) _

/-- Genuine projective Artinian singleton rings and the LITERAL scalar-
preserving singleton germ PRODUCE finite complex dimension of each actual stalk. -/
theorem ClosedProjectiveEmbedding.artinian_stalk_finite
    {X : Scheme} {p : X ⟶ Spec (.of ℂ)} (P : ClosedProjectiveEmbedding p)
    [IsArtinianScheme X] (x : X) :
    letI := schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants p) x
    Module.Finite ℂ (X.presheaf.stalk x) := by
  let := schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants p) x
  let U := discreteSingletonOpen X x
  let := affineChartAlgebra p U
  have hU : IsAffineOpen U := IsAffineOpen.of_subsingleton Set.subsingleton_singleton
  have := P.locallyOfFiniteType
  have : Algebra.FiniteType ℂ Γ(X, U) := affineChartAlgebra_finiteType p hU
  have : IsArtinianRing Γ(X, U) :=
    IsLocallyArtinian.isArtinianRing_presheaf_obj ⟨U, hU⟩
  have : Module.Finite ℂ Γ(X, U) := Module.finite_of_isArtinianRing ℂ Γ(X, U)
  exact Module.Finite.equiv (discreteSingletonGermAlgEquiv p x).toLinearEquiv

/-- Actual stalk finiteness and algebraic closedness produce bijectivity of
the ACTUAL structural complex scalar map to the same stalk residue field. -/
theorem ClosedProjectiveEmbedding.artinian_stalk_residue_bijective
    {X : Scheme} {p : X ⟶ Spec (.of ℂ)} (P : ClosedProjectiveEmbedding p)
    [IsArtinianScheme X] (x : X) :
    letI := schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants p) x
    Function.Bijective (algebraMap ℂ (IsLocalRing.ResidueField (X.presheaf.stalk x))) := by
  let := schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants p) x
  have := P.artinian_stalk_finite x
  have : Module.Finite ℂ (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    Module.Finite.trans (X.presheaf.stalk x) (IsLocalRing.ResidueField (X.presheaf.stalk x))
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- The SAME actual stalk's genuine local module length equals its actual
complex dimension under the ORIGINAL structural scalars; no length input. -/
theorem ClosedProjectiveEmbedding.artinian_stalk_length_eq_finrank
    {X : Scheme} {p : X ⟶ Spec (.of ℂ)} (P : ClosedProjectiveEmbedding p)
    [IsArtinianScheme X] (x : X) :
    letI := schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants p) x
    Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) =
      (Module.finrank ℂ (X.presheaf.stalk x) : ℕ∞) := by
  let := schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants p) x
  have := P.artinian_stalk_finite x
  exact local_length_eq_finrank_of_residue_bijective
    (K := ℂ) (A := X.presheaf.stalk x) (M := X.presheaf.stalk x)
    (P.artinian_stalk_residue_bijective x)



end
end SGPT.Foundations.Schemes
