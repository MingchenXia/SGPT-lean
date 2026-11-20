import SGPT.Projective.OriginalTwistedCartierEuler
import SGPT.Foundations.Schemes.DiscreteLineTrivialization
import SGPT.Foundations.Schemes.NativeFlagTerminalEulerLength

/-! Genuine ORIGINAL Artinian arbitrary-line Euler characteristic equals
the FULL actual local-ring length sum; nilpotents/empty schemes retained.
Blueprint: original-artinian-line-euler.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Opposite

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)

/-- True original sheaf isomorphisms preserve the SAME original chosen-cover
Euler characteristic, via the genuine actual section-complex isomorphism. -/
theorem originalProjectiveLineCechEuler_eq_of_iso {B C : X.Modules} (e : B ≅ C) :
    originalProjectiveLineCechEuler f E B = originalProjectiveLineCechEuler f E C :=
  cochain_homologyEulerChar_eq_of_iso
    (nonemptySubsetCechComplexIso (Functor.isoWhiskerLeft
      (nonemptySubsetInclusion (Fin (E.ambientDimension + 1)))
      (actualSchemeModuleBaseSubsetIso e
        (actualPolynomialProjectivePullbackCoordinateOpens E.map) (schemeGlobalConstants f))))

/-- Pure ORIGINAL full local-ring length sum, never defined by Euler/period. -/
def originalArtinianStalkLengthSum (Y : Scheme.{0}) [IsArtinianScheme Y] : ℕ∞ :=
  letI : Fintype Y := Fintype.ofFinite Y
  ∑ x : Y, Module.length (Y.presheaf.stalk x) (Y.presheaf.stalk x)

include f E in
/-- Actual original projectivity produces finiteness of the independent full
original length sum, retaining all nilpotents and the empty scheme. -/
theorem originalArtinianStalkLengthSum_ne_top [IsArtinianScheme X]
    {B : X.Modules} (b : LineBundleAtlas B) : originalArtinianStalkLengthSum X ≠ ⊤ := by
  have h := E.artinian_globalLine_finrank_eq_stalk_length_sum b
  change (_ : ℕ∞) = originalArtinianStalkLengthSum X at h
  rw [← h]
  exact ENat.natCast_ne_top _

/-- ANY genuine original line's SAME chosen-cover Euler characteristic is
the independent FULL original Artinian local-ring length sum, without an
Euler/global-H0/acyclicity/length comparison premise. -/
theorem originalArtinianLineCechEuler_eq_fullLength [IsArtinianScheme X]
    {B : X.Modules} (b : LineBundleAtlas B) :
    originalProjectiveLineCechEuler f E B =
      ((originalArtinianStalkLengthSum X).toNat : ℤ) := by
  let T : NativeClosedProjectiveStratum E.ambientDimension := ⟨Over.mk E.map, E.closedImmersion⟩
  let : IsArtinianScheme T.val.left := inferInstanceAs (IsArtinianScheme X)
  obtain ⟨m, hm⟩ := T.artinian_powerEuler_eventually_eq_stalk_length_sum
  let d : LineBundleAtlas (T.powerSheaf m) :=
    (((nativeProjectivePositiveLine ℂ E.ambientDimension E.map).atlas.tensorPower 1).tensorPower m)
  let e : B ≅ T.powerSheaf m := b.discreteTrivialization ≪≫ d.discreteTrivialization.symm
  have hT : originalProjectiveLineCechEuler f E (T.powerSheaf m) = T.powerEuler m := by
    change (subsetCechComplex (actualSchemeModuleBaseSubsetDiagram (T.powerSheaf m)
      (actualPolynomialProjectivePullbackCoordinateOpens E.map) (schemeGlobalConstants f))).homologyEulerChar =
      (subsetCechComplex (actualSchemeModuleBaseSubsetDiagram (T.powerSheaf m)
        (actualPolynomialProjectivePullbackCoordinateOpens E.map)
        (schemeGlobalConstants (E.map ≫ polynomialProjStructureMap ℂ E.ambientDimension)))).homologyEulerChar
    rw [E.over_base]
  calc
    originalProjectiveLineCechEuler f E B =
        originalProjectiveLineCechEuler f E (T.powerSheaf m) :=
      originalProjectiveLineCechEuler_eq_of_iso f E e
    _ = T.powerEuler m := hT
    _ = ((T.artinianStalkLengthSum).toNat : ℤ) := hm m le_rfl
    _ = ((originalArtinianStalkLengthSum X).toNat : ℤ) := rfl

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
