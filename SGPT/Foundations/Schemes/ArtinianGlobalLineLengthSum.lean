import SGPT.Foundations.Schemes.ArtinianProjectiveStalkLength
import SGPT.Foundations.Schemes.NativeFlagPowerCechComparison

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- Actual discrete singleton/stalk gluing and produced stalk finiteness
make the ORIGINAL global section module of ANY actual line atlas finiteℂ. -/
theorem ClosedProjectiveEmbedding.artinian_globalLine_finite
    {X : Scheme} {p : X ⟶ Spec (.of ℂ)} (P : ClosedProjectiveEmbedding p)
    [IsArtinianScheme X] {M : X.Modules} (a : LineBundleAtlas M) :
    Module.Finite ℂ (actualSchemeModuleBaseGlobalSections M (schemeGlobalConstants p)) := by
  classical
  let : Fintype X := Fintype.ofFinite X
  let : ∀ x : X, Algebra ℂ (X.presheaf.stalk x) :=
    fun x ↦ schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants p) x
  let : ∀ x : X, Module.Finite ℂ (X.presheaf.stalk x) := fun x ↦ P.artinian_stalk_finite x
  exact Module.Finite.equiv (a.discreteGlobalStalkCoefficientEquiv (schemeGlobalConstants p)).symm

/-- The ORIGINAL global line dimension equals the sum of genuine ACTUAL
stalk-ring lengths, preserving nonreduced local multiplicities and empty sums. -/
theorem ClosedProjectiveEmbedding.artinian_globalLine_finrank_eq_stalk_length_sum
    {X : Scheme} {p : X ⟶ Spec (.of ℂ)} (P : ClosedProjectiveEmbedding p)
    [IsArtinianScheme X] {M : X.Modules} (a : LineBundleAtlas M) :
    letI : Fintype X := Fintype.ofFinite X
    (Module.finrank ℂ (actualSchemeModuleBaseGlobalSections M (schemeGlobalConstants p)) : ℕ∞) =
      ∑ x : X, Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) := by
  classical
  let : Fintype X := Fintype.ofFinite X
  let : ∀ x : X, Algebra ℂ (X.presheaf.stalk x) :=
    fun x ↦ schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants p) x
  let : ∀ x : X, Module.Finite ℂ (X.presheaf.stalk x) := fun x ↦ P.artinian_stalk_finite x
  have h := (a.discreteGlobalStalkCoefficientEquiv (schemeGlobalConstants p)).finrank_eq
  calc
    (Module.finrank ℂ (actualSchemeModuleBaseGlobalSections M (schemeGlobalConstants p)) : ℕ∞) =
        ∑ x : X, (Module.finrank ℂ (X.presheaf.stalk x) : ℕ∞) := by
      rw [h, Module.finrank_pi_fintype]
      simp only [Nat.cast_sum]
    _ = ∑ x : X, Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (P.artinian_stalk_length_eq_finrank x).symm

/-- EVERY actual terminal native flag power has ORIGINAL global dimension
equal to the SAME actual terminal geometric stalk-length sum, with no value input. -/
theorem SmoothProjectiveFano.nativeRegularProjectiveFlag_terminal_power_global_length_sum
    {n : ℕ} (F : SmoothProjectiveFano n) (m : ℕ) :
    let T := F.nativeRegularProjectiveFlag n
    letI := F.nativeRegularProjectiveFlag_terminal_isArtinian
    letI : Fintype T.val.left := Fintype.ofFinite T.val.left
    (Module.finrank ℂ (actualSchemeModuleBaseGlobalSections (T.powerSheaf m)
      (schemeGlobalConstants (T.val.hom ≫ polynomialProjStructureMap ℂ F.projective.ambientDimension))) : ℕ∞) =
        ∑ x : T.val.left, Module.length (T.val.left.presheaf.stalk x) (T.val.left.presheaf.stalk x) := by
  let := F.nativeRegularProjectiveFlag_terminal_isArtinian
  exact (F.nativeRegularProjectiveFlag n).embedding.artinian_globalLine_finrank_eq_stalk_length_sum
    (((nativeProjectivePositiveLine ℂ F.projective.ambientDimension
      (F.nativeRegularProjectiveFlag n).val.hom).atlas.tensorPower 1).tensorPower m)

end
end SGPT.Foundations.Schemes
