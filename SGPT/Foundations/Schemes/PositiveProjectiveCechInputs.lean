import SGPT.Foundations.Schemes.LineSectionTwistedCechExactSequence
import SGPT.Foundations.Schemes.NativePositiveProjectiveCoordinateSections
import SGPT.Foundations.Schemes.PolynomialProjectiveSubsetCharts
import SGPT.Foundations.Schemes.SchemeModulePushforwardCech
import SGPT.Foundations.Schemes.BundleMorphismGluing
import Mathlib.AlgebraicGeometry.Morphisms.Affine

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type) [Field K] (N : ℕ)

/-- A genuine selected coordinate chart identifies each nonempty intersection
with its actual affine principal ratio-product open. -/
theorem polynomialProjSubsetCoordinateOpen_isAffine
    (S : Finset (Fin (N + 1))) (hS : S.Nonempty) :
    IsAffineOpen (polynomialProjSubsetCoordinateOpen K N S) := by
  obtain ⟨j, hj⟩ := hS
  rw [← polynomialProjCoordinateImmersion_image_subsetOpen K N j S hj,
    Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion]
  exact IsAffineOpen.Spec_basicOpen _

/-- Actual affine morphisms produce affine original pullback intersections. -/
theorem actualPolynomialProjectivePullbackSubsetOpen_isAffine
    {X : Scheme} (f : X ⟶ polynomialProj K N) [IsAffineHom f]
    (S : Finset (Fin (N + 1))) (hS : S.Nonempty) :
    IsAffineOpen (actualSchemeSubsetOpen (actualPolynomialProjectivePullbackCoordinateOpens f) S) := by
  change IsAffineOpen (actualSchemeSubsetOpen
    (fun j ↦ f ⁻¹ᵁ polynomialProjCoordinateOpen K N j) S)
  rw [← actualSchemePushforwardSubsetOpen_eq f (polynomialProjCoordinateOpen K N) S]
  exact (polynomialProjSubsetCoordinateOpen_isAffine K N S hS).preimage f

variable {X : Scheme} (f : X ⟶ polynomialProj K N) (L : IntrinsicLineBundle X)
    (q : ℕ) (e : bundleTensorPower L.sheaf q ≅
      (Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K N).sheaf)

/-- Genuine positivity and actual restriction produce every source intersection frame. -/
def nativePositiveProjectiveSubsetFrame
    (S : {S : Finset (Fin (N + 1)) // S.Nonempty}) :
    LocalBundleFrame (bundleTensorPower L.sheaf q)
      (actualSchemeSubsetOpen (actualPolynomialProjectivePullbackCoordinateOpens f) S.val) := by
  classical
  let j := S.property.choose
  have hj : j ∈ S.val := S.property.choose_spec
  have h : actualSchemeSubsetOpen (actualPolynomialProjectivePullbackCoordinateOpens f) S.val ≤
      f ⁻¹ᵁ polynomialProjCoordinateOpen K N j := Finset.inf_le hj
  exact bundleHomRestrictionIso (bundleTensorPower L.sheaf q)
    (SheafOfModules.unit X.ringCatSheaf) (homOfLE h)
    (nativePositiveProjectiveCoordinateFrame K N f L q e j)

include e in
/-- Original positive coordinates produce an actual nonzero degree-q section. -/
theorem nativePositiveProjectiveCoordinateSection_exists_ne_zero [IsIntegral X] :
    ∃ s : bundlePowerGlobalSections L.sheaf q, s ≠ 0 := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have hx : x ∈ iSup (actualPolynomialProjectivePullbackCoordinateOpens f) := by
    rw [actualPolynomialProjectivePullbackCoordinateOpens_covers]
    trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
  refine ⟨nativePositiveProjectiveCoordinateSection K N f L q e j, ?_⟩
  intro hz
  let U := actualPolynomialProjectivePullbackCoordinateOpens f j
  let : Nonempty U := ⟨⟨x, hj⟩⟩
  have hc := nativePositiveProjectiveCoordinateSection_coefficients K N f L q e j (𝟙 U)
  rw [hz, map_zero, map_zero] at hc
  change (0 : Γ(X, U)) = 1 at hc
  exact zero_ne_one hc

/-- Produced actual affinity and frames instantiate the genuine original
normalized twisted Cech short complex, without extra cover certificates. -/
abbrev nativePositiveProjectiveSectionZeroCechShortComplex [IsAffineHom f]
    (s : bundlePowerGlobalSections L.sheaf q) (c : K →+* Γ(X, ⊤)) (m : ℕ) :=
  sectionZeroPowerCechShortComplex (L.atlas.tensorPower q) s
    (actualPolynomialProjectivePullbackCoordinateOpens f)
    (fun S ↦ actualPolynomialProjectivePullbackSubsetOpen_isAffine K N f S.val S.property)
    (nativePositiveProjectiveSubsetFrame K N f L q e) c m

/-- Actual integral geometry, positivity and affine morphism produce true
ShortExact original twisted complexes, retaining the original base map. -/
theorem nativePositiveProjectiveSectionZeroCechShortComplex_shortExact
    [IsIntegral X] [IsAffineHom f] (s : bundlePowerGlobalSections L.sheaf q)
    (hs : s ≠ 0) (c : K →+* Γ(X, ⊤)) (m : ℕ) :
    (nativePositiveProjectiveSectionZeroCechShortComplex K N f L q e s c m).ShortExact :=
  sectionZeroPowerCechShortComplex_shortExact (L.atlas.tensorPower q) s hs
    (actualPolynomialProjectivePullbackCoordinateOpens f)
    (fun S ↦ actualPolynomialProjectivePullbackSubsetOpen_isAffine K N f S.val S.property)
    (nativePositiveProjectiveSubsetFrame K N f L q e) c m

end
end SGPT.Foundations.Schemes
