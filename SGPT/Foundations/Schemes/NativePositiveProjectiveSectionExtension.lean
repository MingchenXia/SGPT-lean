import SGPT.Foundations.Schemes.NativePolynomialPullbackPower
import SGPT.Foundations.Schemes.NativeTensorTwistTransport
import SGPT.Foundations.Schemes.NativeFanoConeProper
/-!
# NativePositiveProjectiveSectionExtension

Actual projective chart sections extend to genuine powers of the original line sheaf. True positivity, pullback-power and tensor comparisons produce full section-ring power sections, including the actual native Fano anticanonical spaces. No off-zero scheme isomorphism or original analytic Fano identification is inferred.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} (f : X ⟶ polynomialProj K n) (L : IntrinsicLineBundle X) (q : ℕ)
    (e : bundleTensorPower L.sheaf q ≅
      (Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K n).sheaf)

/-- Literal regrouping and genuine positivity give an actual isomorphism to the pulled-back projective power. -/
def nativePositiveProjectivePowerIso (d : ℕ) :
    bundleTensorPower L.sheaf (q * d) ≅
      (Scheme.Modules.pullback f).obj (bundleTensorPower (polynomialProjTwistingLine K n).sheaf d) :=
  nativeLineTensorPowerMulIso L.atlas q d ≪≫ nativeLineTensorPowerIso e d ≪≫
    (nativePolynomialPullbackPowerIso K n f d).symm

/-- The true positive-power coordinate frame is transported along the actual positivity and tensor comparisons. -/
def nativePositiveProjectivePowerFrame (d : ℕ) (i : Fin (n + 1)) :
    LocalBundleFrame (bundleTensorPower L.sheaf (q * d))
      (f ⁻¹ᵁ polynomialProjCoordinateOpen K n i) :=
  (SheafOfModules.overFunctor X.ringCatSheaf (f ⁻¹ᵁ polynomialProjCoordinateOpen K n i)).mapIso
    (nativePositiveProjectivePowerIso K n f L q e d) ≪≫
      nativePolynomialPowerPullbackFrame K n f d i

/-- Genuine projective chart sections extend to actual positive line-power tensor twists, with the prescribed true coefficient. -/
theorem nativePositiveProjectiveSection_extension [IsClosedImmersion f]
    {M : X.Modules} (a : LineBundleAtlas M) (i : Fin (n + 1))
    (s : bundleSections M (f ⁻¹ᵁ polynomialProjCoordinateOpen K n i)) :
    ∃ (d : ℕ) (t : bundleSections (bundleTensor (bundleTensorPower L.sheaf (q * d)) M) ⊤),
      (nativePositiveProjectivePowerFrame K n f L q e d i).tensorModuleCoefficients M (𝟙 _)
        ((bundleTensor (bundleTensorPower L.sheaf (q * d)) M).val.map
          (homOfLE le_top).op t) = s := by
  obtain ⟨d, t, ht⟩ := nativeClosedProjectiveCoordinateSection_pullbackExtension K n f a i s
  obtain ⟨w, hw⟩ := nativeTensorTwistExtension_transport
    (nativePositiveProjectivePowerIso K n f L q e d)
    (nativePolynomialPowerPullbackFrame K n f d i) s t ht
  exact ⟨d, w, hw⟩

/-- The produced extension is a genuine global section in the original full line section ring's actual power space. -/
theorem nativePositiveProjectivePowerSection_extension [IsClosedImmersion f]
    (r : ℕ) (i : Fin (n + 1))
    (s : bundleSections (bundleTensorPower L.sheaf r) (f ⁻¹ᵁ polynomialProjCoordinateOpen K n i)) :
    ∃ (d : ℕ) (t : bundlePowerGlobalSections L.sheaf (q * d + r)),
      (nativePositiveProjectivePowerFrame K n f L q e d i).tensorModuleCoefficients
        (bundleTensorPower L.sheaf r) (𝟙 _)
        ((nativeLineTensorPowerAddIso L.atlas (q * d) r).hom.val.app
          (.op (f ⁻¹ᵁ polynomialProjCoordinateOpen K n i))
          ((bundleTensorPower L.sheaf (q * d + r)).val.map (homOfLE le_top).op t)) = s := by
  obtain ⟨d, t, ht⟩ := nativePositiveProjectiveSection_extension K n f L q e
    (L.atlas.tensorPower r) i s
  let A := nativeLineTensorPowerAddIso L.atlas (q * d) r
  let w : bundlePowerGlobalSections L.sheaf (q * d + r) := A.inv.val.app (.op ⊤) t
  refine ⟨d, w, ?_⟩
  have hn := PresheafOfModules.naturality_apply A.hom.val
    (homOfLE (show f ⁻¹ᵁ polynomialProjCoordinateOpen K n i ≤ ⊤ from le_top)).op w
  have hi := congrArg (fun a ↦ a.val.app (.op ⊤) t) A.inv_hom_id
  change A.hom.val.app (.op ⊤) w = t at hi
  change A.hom.val.app (.op (f ⁻¹ᵁ polynomialProjCoordinateOpen K n i))
      ((bundleTensorPower L.sheaf (q * d + r)).val.map (homOfLE le_top).op w) =
    (bundleTensor (bundleTensorPower L.sheaf (q * d)) (bundleTensorPower L.sheaf r)).val.map
      (homOfLE le_top).op (A.hom.val.app (.op ⊤) w) at hn
  change (nativePositiveProjectivePowerFrame K n f L q e d i).tensorModuleCoefficients
    (bundleTensorPower L.sheaf r) (𝟙 _) (A.hom.val.app _ _) = s
  rw [hn, hi]
  exact ht

/-- Native smooth projective Fano data produce actual anticanonical full-ring sections extending every genuine projective-chart power section. -/
theorem SmoothProjectiveFano.nativeAnticanonicalPowerSection_extension {m : ℕ}
    (F : SmoothProjectiveFano m) (r : ℕ) (i : Fin (F.projective.ambientDimension + 1))
    (s : bundleSections (bundleTensorPower (anticanonicalLineSheaf F.structureMap m) r)
      (F.projective.map ⁻¹ᵁ polynomialProjCoordinateOpen ℂ F.projective.ambientDimension i)) :
    ∃ (d : ℕ) (t : bundlePowerGlobalSections (anticanonicalLineSheaf F.structureMap m)
      (F.anticanonicalPower * d + r)),
      (nativePositiveProjectivePowerFrame ℂ F.projective.ambientDimension F.projective.map
        (smoothAnticanonicalLineBundle F.structureMap m) F.anticanonicalPower F.positivityIso d i).tensorModuleCoefficients
        (bundleTensorPower (anticanonicalLineSheaf F.structureMap m) r) (𝟙 _)
        ((nativeLineTensorPowerAddIso (smoothAnticanonicalLineBundle F.structureMap m).atlas
          (F.anticanonicalPower * d) r).hom.val.app
          (.op (F.projective.map ⁻¹ᵁ polynomialProjCoordinateOpen ℂ F.projective.ambientDimension i))
          ((bundleTensorPower (anticanonicalLineSheaf F.structureMap m)
            (F.anticanonicalPower * d + r)).val.map (homOfLE le_top).op t)) = s :=
  nativePositiveProjectivePowerSection_extension ℂ F.projective.ambientDimension F.projective.map
    (smoothAnticanonicalLineBundle F.structureMap m) F.anticanonicalPower F.positivityIso r i s

end
end SGPT.Foundations.Schemes
