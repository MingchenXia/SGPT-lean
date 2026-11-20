import SGPT.Okounkov.SchemeNativeHolomorphicGerm
import SGPT.Okounkov.SchemeCoordinateSectionsGerm

/-!
# Actual function fields and sections in ORIGINAL analytic fractions

The genuine original native-germ equivalence extends through the existing
fraction-ring machinery. Its actual constant law preserves the exact original
complex actions, so the previously proved global field and section producers
compose into the actual original analytic fraction field. No field equality,
finite-dimensionality, original flag or rank claim is made.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry Algebra SGPT.Foundations.Schemes Filter
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Topology

/-- The existing fraction extension preserves any proved constant maps.
Keeping the rings abstract avoids unfolding the actual geometric atlas when
the native constant actions are normalized. -/
private def fractionAlgEquivOfConstantMaps
    {C R S : Type*} [CommRing C] [CommRing R] [CommRing S]
    (e : R ≃+* S) (cR : C →+* R) (cS : C →+* S)
    (hc : ∀ c, e (cR c) = cS c) :
    letI := ((algebraMap R (FractionRing R)).comp cR).toAlgebra
    letI := ((algebraMap S (FractionRing S)).comp cS).toAlgebra
    FractionRing R ≃ₐ[C] FractionRing S := by
  letI := ((algebraMap R (FractionRing R)).comp cR).toAlgebra
  letI := ((algebraMap S (FractionRing S)).comp cS).toAlgebra
  apply AlgEquiv.ofRingEquiv (f := IsFractionRing.ringEquivOfRingEquiv e)
  intro c
  change IsFractionRing.ringEquivOfRingEquiv e
    (algebraMap R (FractionRing R) (cR c)) = algebraMap S (FractionRing S) (cS c)
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, hc]

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance nativeFieldSchemeTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f

local instance nativeFieldSchemeCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

local instance nativeFieldSchemeManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable (p : SchemeComplexPoint f)

/-- The actual native fraction-ring extension of the SAME original-germ equivalence. -/
def schemeNativeFractionEquiv :
    FractionRing (HolGerm (Fin n → ℂ)) ≃+*
      FractionRing (NativeHolGerm n (SchemeComplexPoint f) p) :=
  IsFractionRing.ringEquivOfRingEquiv (schemeNativeCoordinateGermEquiv f n p)

/-- Whole genuine original-germ inclusion readback. -/
theorem schemeNativeFractionEquiv_algebraMap (g : HolGerm (Fin n → ℂ)) :
    schemeNativeFractionEquiv f n p
      (algebraMap _ (FractionRing (HolGerm (Fin n → ℂ))) g) =
        algebraMap _ (FractionRing (NativeHolGerm n (SchemeComplexPoint f) p))
          (schemeNativeCoordinateGermEquiv f n p g) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (schemeNativeCoordinateGermEquiv f n p) g

/-- Actual original constant germs give the actual native fraction scalar action. -/
@[instance_reducible] def schemeNativeFractionComplexAlgebra :
    Algebra ℂ (FractionRing (NativeHolGerm n (SchemeComplexPoint f) p)) :=
  ((algebraMap (NativeHolGerm n (SchemeComplexPoint f) p)
    (FractionRing (NativeHolGerm n (SchemeComplexPoint f) p))).comp
      (NativeHolGerm.constHom : ℂ →+* NativeHolGerm n (SchemeComplexPoint f) p)).toAlgebra

local instance nativeFieldCoordinateComplexAlgebra :
    Algebra ℂ (FractionRing (HolGerm (Fin n → ℂ))) :=
  schemeCoordinateFractionComplexAlgebra n

local instance nativeFieldOriginalComplexAlgebra :
    Algebra ℂ (FractionRing (NativeHolGerm n (SchemeComplexPoint f) p)) :=
  schemeNativeFractionComplexAlgebra f n p

/-- The actual inclusion and literal constant laws make the SAME fraction
equivalence complex-linear for the two actual constant-germ actions. -/
def schemeNativeFractionAlgEquiv :
    FractionRing (HolGerm (Fin n → ℂ)) ≃ₐ[ℂ]
      FractionRing (NativeHolGerm n (SchemeComplexPoint f) p) :=
  fractionAlgEquivOfConstantMaps (schemeNativeCoordinateGermEquiv f n p)
    HolGerm.constHom NativeHolGerm.constHom (schemeNativeCoordinateGermEquiv_const f n p)

variable [IsIntegral X]

/-- The actual global scheme function field embeds into the actual ORIGINAL
analytic fraction field; the two fields are not identified. -/
def schemeNativeFunctionFieldGerm :
    X.functionField →+* FractionRing (NativeHolGerm n (SchemeComplexPoint f) p) :=
  (schemeNativeFractionEquiv f n p).toRingHom.comp (schemeCoordinateFunctionFieldGerm f n p)

/-- Both actual constituent injections have already been manufactured. -/
theorem schemeNativeFunctionFieldGerm_injective :
    Function.Injective (schemeNativeFunctionFieldGerm f n p) :=
  (schemeNativeFractionEquiv f n p).injective.comp
    (schemeCoordinateFunctionFieldGerm_injective f n p)

/-- Every ORIGINAL scheme-stalk element has exactly its original native germ. -/
theorem schemeNativeFunctionFieldGerm_stalk
    (a : X.presheaf.stalk (schemeComplexPointImage f p)) :
    schemeNativeFunctionFieldGerm f n p (algebraMap _ X.functionField a) =
      algebraMap _ (FractionRing (NativeHolGerm n (SchemeComplexPoint f) p))
        (schemeNativeStalkGerm f n p a) := by
  change schemeNativeFractionEquiv f n p
    (schemeCoordinateFunctionFieldGerm f n p (algebraMap _ X.functionField a)) = _
  rw [schemeCoordinateFunctionFieldGerm_stalk, schemeNativeFractionEquiv_algebraMap]
  rfl

/-- Every actual affine regular element retains its whole ORIGINAL germ. -/
theorem schemeNativeFunctionFieldGerm_regular (a : SchemeCoordinateAffineRing f n p) :
    schemeNativeFunctionFieldGerm f n p (schemeCoordinateRegularFunctionField f n p a) =
      algebraMap _ (FractionRing (NativeHolGerm n (SchemeComplexPoint f) p))
        (schemeNativeRegularGerm f n p a) := by
  change schemeNativeFractionEquiv f n p
    (schemeCoordinateFunctionFieldGerm f n p (schemeCoordinateRegularFunctionField f n p a)) = _
  rw [schemeCoordinateFunctionFieldGerm_regular, schemeNativeFractionEquiv_algebraMap]
  rfl

/-- The SAME actual centered algebraic coordinates retain their true native germs. -/
theorem schemeNativeFunctionFieldGerm_centered (i : Fin n) :
    schemeNativeFunctionFieldGerm f n p
      (schemeCoordinateRegularFunctionField f n p (schemeCoordinateCenteredFreeGenerator f n p i)) =
        algebraMap _ (FractionRing (NativeHolGerm n (SchemeComplexPoint f) p))
          (schemeNativeCoordinateGermEquiv f n p
            (HolGerm.mk (fun z : Fin n → ℂ => z i)
              (Eventually.of_forall fun _ =>
                (ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).differentiableAt))) := by
  change schemeNativeFractionEquiv f n p
    (schemeCoordinateFunctionFieldGerm f n p (schemeCoordinateRegularFunctionField f n p
      (schemeCoordinateCenteredFreeGenerator f n p i))) = _
  rw [schemeCoordinateFunctionFieldGerm_centered, schemeNativeFractionEquiv_algebraMap]

/-- Every genuine original-stalk fraction has its whole actual native quotient. -/
theorem schemeNativeFunctionFieldGerm_mk'
    (a : X.presheaf.stalk (schemeComplexPointImage f p))
    (s : nonZeroDivisors (X.presheaf.stalk (schemeComplexPointImage f p))) :
    schemeNativeFunctionFieldGerm f n p (IsLocalization.mk' X.functionField a s) =
      algebraMap _ (FractionRing (NativeHolGerm n (SchemeComplexPoint f) p))
          (schemeNativeStalkGerm f n p a) /
        algebraMap _ (FractionRing (NativeHolGerm n (SchemeComplexPoint f) p))
          (schemeNativeStalkGerm f n p s) := by
  change schemeNativeFractionEquiv f n p
    (schemeCoordinateFunctionFieldGerm f n p (IsLocalization.mk' X.functionField a s)) = _
  rw [schemeCoordinateFunctionFieldGerm_mk', map_div₀,
    schemeNativeFractionEquiv_algebraMap, schemeNativeFractionEquiv_algebraMap]
  rfl

/-- The EXACT already derived structure-induced source action is retained. -/
def schemeNativeFunctionFieldAlgHom :
    letI := schemeFunctionFieldAlgebra f
    X.functionField →ₐ[ℂ] FractionRing (NativeHolGerm n (SchemeComplexPoint f) p) := by
  letI := schemeFunctionFieldAlgebra f
  exact (schemeNativeFractionAlgEquiv f n p).toAlgHom.comp
    (schemeCoordinateFunctionFieldAlgHom f n p)

/-- The bundled map has the SAME actual function on the actual function field. -/
theorem schemeNativeFunctionFieldAlgHom_apply (a : X.functionField) :
    schemeNativeFunctionFieldAlgHom f n p a = schemeNativeFunctionFieldGerm f n p a :=
  rfl

/-- Original structural complex constants map to actual ORIGINAL constant germs. -/
theorem schemeNativeFunctionFieldGerm_const (c : ℂ) :
    letI := schemeFunctionFieldAlgebra f
    schemeNativeFunctionFieldGerm f n p (algebraMap ℂ X.functionField c) =
      algebraMap ℂ (FractionRing (NativeHolGerm n (SchemeComplexPoint f) p)) c := by
  let := schemeFunctionFieldAlgebra f
  exact (schemeNativeFunctionFieldAlgHom f n p).commutes c

/-- Reuse the actual original faithful section map and actual complex-linear
fraction equivalence, retaining the EXACT original section scalar action. -/
def schemeNativeGlobalSectionsGerm {L : X.Modules} (a : LineBundleAtlas L) :
    letI := schemeGlobalSectionModule f L
    bundleSections L ⊤ →ₗ[ℂ] FractionRing (NativeHolGerm n (SchemeComplexPoint f) p) := by
  letI := schemeGlobalSectionModule f L
  exact (schemeNativeFractionAlgEquiv f n p).toLinearMap.comp
    (schemeCoordinateGlobalSectionsGerm f n p a)

/-- Actual original global sections are faithfully represented. -/
theorem schemeNativeGlobalSectionsGerm_injective {L : X.Modules} (a : LineBundleAtlas L) :
    Function.Injective (schemeNativeGlobalSectionsGerm f n p a) := by
  let := schemeGlobalSectionModule f L
  exact (schemeNativeFractionAlgEquiv f n p).injective.comp
    (schemeCoordinateGlobalSectionsGerm_injective f n p a)

/-- Each section is sent through its SAME previously chosen native generic coefficient. -/
theorem schemeNativeGlobalSectionsGerm_apply {L : X.Modules} (a : LineBundleAtlas L)
    (s : bundleSections L ⊤) :
    letI := schemeGlobalSectionModule f L
    letI := schemeFunctionFieldAlgebra f
    schemeNativeGlobalSectionsGerm f n p a s =
      schemeNativeFunctionFieldGerm f n p (a.genericEvaluationOverBase f s) :=
  rfl

end SGPT.Okounkov
