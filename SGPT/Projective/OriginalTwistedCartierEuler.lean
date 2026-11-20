import SGPT.Projective.OriginalTwistedCartierExact
import SGPT.Projective.OriginalLineProjectionFormula
import SGPT.Foundations.Schemes.NativeProjectiveLineCechEuler
import SGPT.Foundations.Schemes.ActualSectionDiagramIsomorphisms
import SGPT.Foundations.Schemes.SchemeModulePushforwardCech

/-! Genuine arbitrary original line-twisted Cartier Euler sequences on the
UNCHANGED original projective coordinate cover. All homology finiteness and
geometric restriction readback are manufactured, not supplied.
Blueprint: original-twisted-cartier-euler.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace Opposite

variable {X : Scheme.{0}} {L B : X.Modules}

/-- The actual original short complex for arbitrary distinct cutting/testing
lines, on any specified original open family. -/
def originalTwistedCartierCechShortComplex (a : LineBundleAtlas L) (b : LineBundleAtlas B)
    (s : Γ(L, ⊤))
    (hinj : ∀ V : X.Opens, Function.Injective (sectionZeroEvaluation L s V))
    {I : Type} [LinearOrder I] (U : I → X.Opens)
    {K : Type} [CommRing K] (c : K →+* Γ(X, ⊤)) :
    ShortComplex (CochainComplex (ModuleCat K) ℕ) :=
  actualNonemptySubsetCechShortComplex
    (actualSchemeModuleNonemptyBaseSubsetMap (sectionTensorRightMap B L s) U c)
    (actualSchemeModuleNonemptyBaseSubsetMap
      (sectionZeroTensorRestriction a s (bundleTensor B L)) U c)
    (fun S ↦ originalTwistedCartier_exact a b s hinj (actualSchemeSubsetOpen U S.val))

/-- Actual original Cartier regularity and affine intersections produce the
TRUE short exact original complexes without frames on the specified cover. -/
theorem originalTwistedCartierCechShortComplex_shortExact
    (a : LineBundleAtlas L) (b : LineBundleAtlas B) (s : Γ(L, ⊤))
    (hinj : ∀ V : X.Opens, Function.Injective (sectionZeroEvaluation L s V))
    {I : Type} [LinearOrder I] (U : I → X.Opens)
    (hU : ∀ S : {S : Finset I // S.Nonempty}, IsAffineOpen (actualSchemeSubsetOpen U S.val))
    {K : Type} [CommRing K] (c : K →+* Γ(X, ⊤)) :
    (originalTwistedCartierCechShortComplex a b s hinj U c).ShortExact := by
  unfold originalTwistedCartierCechShortComplex
  apply actualNonemptySubsetCechShortComplex_shortExact
  · intro S
    exact originalTensorRightMap_injective a b s hinj _
  · intro S
    exact sectionZeroAffineTensorRestriction_surjective_unframed a s (b.tensor a) (hU S)

variable (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)

/-- PURE original actual chosen-projective-cover line complex. -/
def originalProjectiveLineCechComplex (C : X.Modules) : CochainComplex (ModuleCat ℂ) ℕ :=
  subsetCechComplex (actualSchemeModuleBaseSubsetDiagram C
    (actualPolynomialProjectivePullbackCoordinateOpens E.map) (schemeGlobalConstants f))

/-- PURE original chosen-cover Euler characteristic. No metric/native-period definition. -/
def originalProjectiveLineCechEuler (C : X.Modules) : ℤ :=
  (originalProjectiveLineCechComplex f E C).homologyEulerChar

/-- The SAME full original section-zero scheme and literal original pulled
test sheaf, on the actual inverse-image of the UNCHANGED original cover. -/
def originalSectionZeroRestrictedCechComplex (a : LineBundleAtlas L) (s : Γ(L, ⊤))
    (C : X.Modules) : CochainComplex (ModuleCat ℂ) ℕ :=
  let g := sectionZeroι a s
  subsetCechComplex (actualSchemeModuleBaseSubsetDiagram
    ((Scheme.Modules.pullback g).obj C)
    (fun j ↦ g ⁻¹ᵁ actualPolynomialProjectivePullbackCoordinateOpens E.map j)
    (schemeGlobalConstants (g ≫ f)))

/-- The genuine arbitrary-line projection and actual source-scalar square
identify the FULL original quotient complex with the actual geometric
restriction complex. No positive power or alternative cover is substituted. -/
def originalSectionZeroQuotientCechIso (a : LineBundleAtlas L) (s : Γ(L, ⊤))
    (b : LineBundleAtlas B) :
    subsetCechComplex (actualSchemeModuleBaseSubsetDiagram
      (bundleTensor B (sectionZeroPushforwardStructure a s))
      (actualPolynomialProjectivePullbackCoordinateOpens E.map) (schemeGlobalConstants f)) ≅
      originalSectionZeroRestrictedCechComplex f E a s B := by
  let g := sectionZeroι a s
  let R := (Scheme.Modules.pullback g).obj B
  let U := actualPolynomialProjectivePullbackCoordinateOpens E.map
  let c := schemeGlobalConstants f
  let Φ := originalLineRestrictionIso g b
  let A := actualSchemeModuleBaseSubsetIso Φ U c
  let A' := nonemptySubsetCechComplexIso
    (Functor.isoWhiskerLeft (nonemptySubsetInclusion (Fin (E.ambientDimension + 1))) A)
  let P := actualSchemeModulePushforwardCechIso g R c U
  let C (d : ℂ →+* Γ(sectionZeroSubscheme a s, ⊤)) :=
    subsetCechComplex (actualSchemeModuleBaseSubsetDiagram R (fun j ↦ g ⁻¹ᵁ U j) d)
  have hc := actualSchemePushforwardSourceConstants_schemeGlobalConstants g f
  exact A' ≪≫ P ≪≫ eqToIso (congrArg C hc)

/-- Actual original closed projectivity produces every original test-line
homology finiteness input, for arbitrary original lines. -/
theorem originalProjectiveLineCech_homology_finite (b : LineBundleAtlas B) (j : ℕ) :
    Module.Finite ℂ ((originalProjectiveLineCechComplex f E B).homology j) :=
  closedPolynomialProjLineCech_homology_finite ℂ E.ambientDimension E.map b f E.over_base j

/-- Genuine arbitrary-line ORIGINAL Cartier Euler additivity. The RHS is the
literal pulled B tensor L on the ENTIRE SAME original zero scheme. Actual
projectivity manufactures all homology finiteness; regularity is primitive
original evaluation injectivity, not an exactness/Euler comparison input. -/
theorem originalTwistedCartierEuler_eq_restricted
    (a : LineBundleAtlas L) (b : LineBundleAtlas B) (s : Γ(L, ⊤))
    (hinj : ∀ V : X.Opens, Function.Injective (sectionZeroEvaluation L s V)) :
    originalProjectiveLineCechEuler f E (bundleTensor B L) =
      originalProjectiveLineCechEuler f E B +
        (originalSectionZeroRestrictedCechComplex f E a s (bundleTensor B L)).homologyEulerChar := by
  let U := actualPolynomialProjectivePullbackCoordinateOpens E.map
  let C := originalTwistedCartierCechShortComplex a b s hinj U (schemeGlobalConstants f)
  have hU (S : {S : Finset (Fin (E.ambientDimension + 1)) // S.Nonempty}) :
      IsAffineOpen (actualSchemeSubsetOpen U S.val) :=
    actualPolynomialProjectivePullbackSubsetOpen_isAffine ℂ E.ambientDimension E.map S.val S.property
  have hC : C.ShortExact := originalTwistedCartierCechShortComplex_shortExact
    a b s hinj U hU (schemeGlobalConstants f)
  let : ∀ j, Module.Finite ℂ (C.X₁.homology j) :=
    fun j ↦ originalProjectiveLineCech_homology_finite f E b j
  let : ∀ j, Module.Finite ℂ (C.X₂.homology j) :=
    fun j ↦ originalProjectiveLineCech_homology_finite f E (b.tensor a) j
  let : ∀ j, Module.Finite ℂ (C.X₃.homology j) :=
    fun j ↦ nativeCochainHomology_finite_dimensionShift C hC j
  have hEuler : C.X₂.homologyEulerChar = C.X₁.homologyEulerChar + C.X₃.homologyEulerChar := by
    apply boundedCochain_homologyEulerChar_additive C hC (E.ambientDimension + 1)
    all_goals
      intro j hj
      change IsZero ((subsetCechComplex _).homology j)
      exact subsetCechComplex_homology_isZero_of_card_le _ j (by simpa using hj)
  exact hEuler.trans (congrArg (fun z : ℤ ↦ C.X₁.homologyEulerChar + z)
    (cochain_homologyEulerChar_eq_of_iso (originalSectionZeroQuotientCechIso f E a s (b.tensor a))))

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
