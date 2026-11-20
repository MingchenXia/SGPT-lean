import SGPT.Foundations.Schemes.LineSectionTwistedAffineExactness
import SGPT.Foundations.Schemes.NonemptySubsetCechExactSequence

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
variable {X : Scheme.{u}} {L : X.Modules}

/-- Genuine affine framed intersections supply primitive exactness of actual
maps, hence a true short complex of ORIGINAL normalized section complexes. -/
def sectionZeroPowerCechShortComplex (a : LineBundleAtlas L) (s : Γ(L, ⊤))
    {I : Type u} [LinearOrder I] (U : I → X.Opens)
    (hU : ∀ S : {S : Finset I // S.Nonempty}, IsAffineOpen (actualSchemeSubsetOpen U S.val))
    (e : ∀ S : {S : Finset I // S.Nonempty}, LocalBundleFrame L (actualSchemeSubsetOpen U S.val))
    {K : Type u} [CommRing K] (c : K →+* Γ(X, ⊤)) (m : ℕ) :
    ShortComplex (CochainComplex (ModuleCat.{u} K) ℕ) :=
  actualNonemptySubsetCechShortComplex
    (actualSchemeModuleNonemptyBaseSubsetMap (sectionPowerMultiplication L s m) U c)
    (actualSchemeModuleNonemptyBaseSubsetMap
      (sectionZeroTensorRestriction a s (bundleTensorPower L (m + 1))) U c)
    (by
      intro S
      change Function.Exact
        ((sectionTensorRightMap (bundleTensorPower L m) L s).app (actualSchemeSubsetOpen U S.val))
        ((sectionZeroTensorRestriction a s (bundleTensorPower L (m + 1))).app
          (actualSchemeSubsetOpen U S.val))
      exact sectionZeroAffineTensor_exact a s ⟨_, hU S⟩
        ((e S).tensorPower m) (e S) (𝟙 _))

/-- Actual integral geometry/nonzero section and actual affine frame cover
produce ShortExact original twisted complexes, with no empty/global Gamma epi. -/
theorem sectionZeroPowerCechShortComplex_shortExact [IsIntegral X]
    (a : LineBundleAtlas L) (s : Γ(L, ⊤)) (hs : s ≠ 0)
    {I : Type u} [LinearOrder I] (U : I → X.Opens)
    (hU : ∀ S : {S : Finset I // S.Nonempty}, IsAffineOpen (actualSchemeSubsetOpen U S.val))
    (e : ∀ S : {S : Finset I // S.Nonempty}, LocalBundleFrame L (actualSchemeSubsetOpen U S.val))
    {K : Type u} [CommRing K] (c : K →+* Γ(X, ⊤)) (m : ℕ) :
    (sectionZeroPowerCechShortComplex a s U hU e c m).ShortExact := by
  unfold sectionZeroPowerCechShortComplex
  apply actualNonemptySubsetCechShortComplex_shortExact
  · intro S
    change Function.Injective
      ((sectionTensorRightMap (bundleTensorPower L m) L s).app (actualSchemeSubsetOpen U S.val))
    exact sectionTensorRightMap_injective a s hs ((e S).tensorPower m) (e S) (𝟙 _)
  · intro S
    change Function.Surjective
      ((sectionZeroTensorRestriction a s (bundleTensorPower L (m + 1))).app
        (actualSchemeSubsetOpen U S.val))
    exact sectionZeroAffineTensorRestriction_surjective a s ⟨_, hU S⟩
      ((e S).tensorPower (m + 1)) (𝟙 _)

/-- The actual LES of the produced twisted short exact sequence gives finite
quotient homology from finite neighboring original homology modules. -/
theorem sectionZeroPowerCech_quotient_homology_finite [IsIntegral X]
    (a : LineBundleAtlas L) (s : Γ(L, ⊤)) (hs : s ≠ 0)
    {I : Type u} [LinearOrder I] (U : I → X.Opens)
    (hU : ∀ S : {S : Finset I // S.Nonempty}, IsAffineOpen (actualSchemeSubsetOpen U S.val))
    (e : ∀ S : {S : Finset I // S.Nonempty}, LocalBundleFrame L (actualSchemeSubsetOpen U S.val))
    {K : Type u} [CommRing K] [IsNoetherianRing K] (c : K →+* Γ(X, ⊤)) (m p : ℕ)
    [Module.Finite K ((sectionZeroPowerCechShortComplex a s U hU e c m).X₂.homology p)]
    [Module.Finite K ((sectionZeroPowerCechShortComplex a s U hU e c m).X₁.homology (p + 1))] :
    Module.Finite K ((sectionZeroPowerCechShortComplex a s U hU e c m).X₃.homology p) :=
  nativeCochainHomology_finite_dimensionShift (sectionZeroPowerCechShortComplex a s U hU e c m)
    (sectionZeroPowerCechShortComplex_shortExact a s hs U hU e c m) p

/-- The ACTUAL finite open family and produced short exact maps give the true
homology Euler difference. Only first/middle finite homology is assumed;
the genuine LES produces quotient finiteness before dimensions are used. -/
theorem sectionZeroPowerCechEuler_additive
    {Y : Scheme} [IsIntegral Y] {A : Y.Modules}
    (a : LineBundleAtlas A) (s : Γ(A, ⊤)) (hs : s ≠ 0)
    {I : Type} [LinearOrder I] [Fintype I] (U : I → Y.Opens)
    (hU : ∀ S : {S : Finset I // S.Nonempty}, IsAffineOpen (actualSchemeSubsetOpen U S.val))
    (e : ∀ S : {S : Finset I // S.Nonempty}, LocalBundleFrame A (actualSchemeSubsetOpen U S.val))
    {K : Type} [Field K] (c : K →+* Γ(Y, ⊤)) (m : ℕ)
    [∀ p, Module.Finite K ((sectionZeroPowerCechShortComplex a s U hU e c m).X₁.homology p)]
    [∀ p, Module.Finite K ((sectionZeroPowerCechShortComplex a s U hU e c m).X₂.homology p)] :
    (sectionZeroPowerCechShortComplex a s U hU e c m).X₂.homologyEulerChar =
      (sectionZeroPowerCechShortComplex a s U hU e c m).X₁.homologyEulerChar +
        (sectionZeroPowerCechShortComplex a s U hU e c m).X₃.homologyEulerChar := by
  let C := sectionZeroPowerCechShortComplex a s U hU e c m
  have hC : C.ShortExact := sectionZeroPowerCechShortComplex_shortExact a s hs U hU e c m
  let : ∀ p, Module.Finite K (C.X₃.homology p) :=
    fun p ↦ nativeCochainHomology_finite_dimensionShift C hC p
  apply boundedCochain_homologyEulerChar_additive C hC (Fintype.card I)
  all_goals
    intro p hp
    change IsZero ((subsetCechComplex _).homology p)
    exact subsetCechComplex_homology_isZero_of_card_le _ p hp

end
end SGPT.Foundations.Schemes
