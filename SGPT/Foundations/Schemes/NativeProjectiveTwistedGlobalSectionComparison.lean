import SGPT.Foundations.Schemes.PolynomialTwistedAllDegreeSubsetComparison
import SGPT.Foundations.Schemes.FiniteGradedPolynomialAugmentedVanishing

/-! # Canonical eventual global sections of one genuine projective graded span

The same chart-generated finite span is used in every degree. Its actual
localization augmentation, genuine nonempty-subset evaluation, and actual
sheaf gluing construct the comparison before eventual bijectivity is applied.
-/

open CategoryTheory AlgebraicGeometry

namespace SGPT.Foundations.Schemes
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

section NonemptyZeroCocycles
universe u
variable {K I : Type u} [CommRing K] [LinearOrder I]
  {F G : Finset I ⥤ ModuleCat.{u} K}

/-- Actual nonempty-subset components preserve the genuine cardinal-one cocycle kernel. -/
def nonemptySubsetCechZeroCocyclesMap
    (α : nonemptySubsetDiagram F ⟶ nonemptySubsetDiagram G) :
    LinearMap.ker (subsetCechCardDifferential F 1) →ₗ[K]
      LinearMap.ker (subsetCechCardDifferential G 1) :=
  ((nonemptySubsetCechCardMap α 1).comp
    (LinearMap.ker (subsetCechCardDifferential F 1)).subtype).codRestrict _ (by
      intro z
      apply Subtype.ext
      change subsetCechDifferential G (nonemptySubsetCechCubeMap α z.val.val) = 0
      rw [← nonemptySubsetCechCubeMap_comm α 0 z.val]
      have hz : subsetCechDifferential F z.val.val = 0 := congrArg Subtype.val z.property
      rw [hz, map_zero])

/-- Actual inverse nonempty-subset components are inverse on the actual zero-cocycle kernels. -/
theorem nonemptySubsetCechZeroCocyclesMap_inverse
    (e : nonemptySubsetDiagram F ≅ nonemptySubsetDiagram G)
    (z : LinearMap.ker (subsetCechCardDifferential F 1)) :
    nonemptySubsetCechZeroCocyclesMap e.inv (nonemptySubsetCechZeroCocyclesMap e.hom z) = z := by
  apply Subtype.ext
  exact nonemptySubsetCechCardMap_inverse e 0 z.val

/-- A genuine nonempty natural isomorphism transports actual zero cocycles without an empty component. -/
def nonemptySubsetCechZeroCocyclesEquiv
    (e : nonemptySubsetDiagram F ≅ nonemptySubsetDiagram G) :
    LinearMap.ker (subsetCechCardDifferential F 1) ≃ₗ[K]
      LinearMap.ker (subsetCechCardDifferential G 1) :=
  { nonemptySubsetCechZeroCocyclesMap e.hom with
    invFun := nonemptySubsetCechZeroCocyclesMap e.inv
    left_inv := nonemptySubsetCechZeroCocyclesMap_inverse e
    right_inv := nonemptySubsetCechZeroCocyclesMap_inverse e.symm }

end NonemptyZeroCocycles

section ActualProjective
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type) [Field K] (n : ℕ) (M : (polynomialProj K n).Modules)
  [∀ j, Module.Finite (polynomialProjCoordinateRing K n j) Γ(polynomialProjModuleChart M j, ⊤)]
  [∀ j, (polynomialProjModuleChart M j).IsQuasicoherent]

/-- The actual induced homogeneous pieces of the one fixed chart-generated finite span. -/
abbrev polynomialProjChartGeneratedTwistedPiece :=
  polynomialProjTwistedFiniteSpanPiece K n M
    (polynomialProjFiniteChartGeneratorDegree K n M) (polynomialProjFiniteChartGeneratorTwist K n M)

/-- The actual homogeneous product-localization diagram of the same fixed span in each degree. -/
abbrev polynomialProjChartGeneratedTwistedCoordinateDiagram (m : ℕ) :
    Finset (Fin (n + 1)) ⥤ ModuleCat K :=
  homogeneousCoordinateSubsetDiagram
    (polynomialIntegralGrading (K := K) (I := Fin (n + 1)))
    (polynomialProjChartGeneratedTwistedPiece K n M)
    (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) polynomialCoordinate_X_degree (m : ℤ)

/-- Actual global sheaf gluing and genuine subset evaluation identify sections with true graded cocycles. -/
def polynomialProjChartGeneratedTwistedZeroCocyclesEquiv (m : ℕ) :
    actualSchemeModuleBaseGlobalSections (polynomialProjModuleTensorTwist K n M m)
      (schemeConstantMap (polynomialProjStructureMap K n)) ≃ₗ[K]
    LinearMap.ker (subsetCechCardDifferential (polynomialProjChartGeneratedTwistedCoordinateDiagram K n M m) 1) := by
  have hcover : iSup (polynomialProjCoordinateOpen K n) = ⊤ :=
    Proj.iSup_basicOpen_eq_top _ _ homogeneousPolynomial_irrelevant_le_coordinates
  exact (actualSchemeModuleBaseGlobalZeroCocyclesIso (polynomialProjModuleTensorTwist K n M m)
    (polynomialProjCoordinateOpen K n) (schemeConstantMap (polynomialProjStructureMap K n))
    hcover).toLinearEquiv.trans
      (nonemptySubsetCechZeroCocyclesEquiv
        (polynomialProjChartGeneratedTwistedAllDegreeNonemptySubsetIso K n M m)).symm

/-- The actual localization augmentation and inverse genuine sheaf gluing produce the canonical global section. -/
def polynomialProjChartGeneratedTwistedDegreeToGlobalSections (m : ℕ) :
    polynomialProjChartGeneratedTwistedPiece K n M (m : ℤ) →ₗ[K]
      actualSchemeModuleBaseGlobalSections (polynomialProjModuleTensorTwist K n M m)
        (schemeConstantMap (polynomialProjStructureMap K n)) :=
  (polynomialProjChartGeneratedTwistedZeroCocyclesEquiv K n M m).symm.toLinearMap.comp
    (homogeneousCoordinateDegreeToCocycles
      (polynomialIntegralGrading (K := K) (I := Fin (n + 1)))
      (polynomialProjChartGeneratedTwistedPiece K n M)
      (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) polynomialCoordinate_X_degree (m : ℤ))

/-- The canonical global section has precisely its actual graded localization cocycle as readback. -/
theorem polynomialProjChartGeneratedTwistedDegreeToGlobalSections_readback (m : ℕ)
    (v : polynomialProjChartGeneratedTwistedPiece K n M (m : ℤ)) :
    polynomialProjChartGeneratedTwistedZeroCocyclesEquiv K n M m
      (polynomialProjChartGeneratedTwistedDegreeToGlobalSections K n M m v) =
    homogeneousCoordinateDegreeToCocycles
      (polynomialIntegralGrading (K := K) (I := Fin (n + 1)))
      (polynomialProjChartGeneratedTwistedPiece K n M)
      (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) polynomialCoordinate_X_degree (m : ℤ) v :=
  LinearEquiv.apply_symm_apply _ _

/-- One bound for the same genuine finite span gives actual canonical global-section bijectivity in every later twist. -/
theorem polynomialProjChartGeneratedTwistedDegreeToGlobalSections_eventually_bijective :
    ∃ b : ℕ, ∀ m : ℕ, b ≤ m →
      Function.Bijective (polynomialProjChartGeneratedTwistedDegreeToGlobalSections K n M m) := by
  obtain ⟨c, hc⟩ := finiteGradedPolynomialCoordinateDegreeToCocycles_eventually_bijective
    (K := K) (I := Fin (n + 1)) (polynomialProjChartGeneratedTwistedPiece K n M)
  refine ⟨c.toNat, fun m hm => ?_⟩
  have hcm : c ≤ (m : ℤ) := by omega
  exact (polynomialProjChartGeneratedTwistedZeroCocyclesEquiv K n M m).symm.bijective.comp (hc _ hcm)

/-- The single genuine comparison threshold is chosen before the twist varies. -/
def polynomialProjChartGeneratedTwistedGlobalSectionComparisonBound : ℕ :=
  (polynomialProjChartGeneratedTwistedDegreeToGlobalSections_eventually_bijective K n M).choose

/-- Every twist beyond the one fixed bound has the true canonical localization/gluing bijection. -/
theorem polynomialProjChartGeneratedTwistedDegreeToGlobalSections_bijective (m : ℕ)
    (hm : polynomialProjChartGeneratedTwistedGlobalSectionComparisonBound K n M ≤ m) :
    Function.Bijective (polynomialProjChartGeneratedTwistedDegreeToGlobalSections K n M m) :=
  (polynomialProjChartGeneratedTwistedDegreeToGlobalSections_eventually_bijective K n M).choose_spec m hm

/-- Actual twisted global sections are canonically equivalent to the actual piece of the same fixed graded span. -/
def polynomialProjChartGeneratedTwistedGlobalSectionsEquiv (m : ℕ)
    (hm : polynomialProjChartGeneratedTwistedGlobalSectionComparisonBound K n M ≤ m) :
    actualSchemeModuleBaseGlobalSections (polynomialProjModuleTensorTwist K n M m)
      (schemeConstantMap (polynomialProjStructureMap K n)) ≃ₗ[K]
      polynomialProjChartGeneratedTwistedPiece K n M (m : ℤ) :=
  (LinearEquiv.ofBijective (polynomialProjChartGeneratedTwistedDegreeToGlobalSections K n M m)
    (polynomialProjChartGeneratedTwistedDegreeToGlobalSections_bijective K n M m hm)).symm

/-- The inverse eventual section equivalence is exactly the genuine localization/gluing map. -/
theorem polynomialProjChartGeneratedTwistedGlobalSectionsEquiv_symm_apply (m : ℕ)
    (hm : polynomialProjChartGeneratedTwistedGlobalSectionComparisonBound K n M ≤ m)
    (v : polynomialProjChartGeneratedTwistedPiece K n M (m : ℤ)) :
    (polynomialProjChartGeneratedTwistedGlobalSectionsEquiv K n M m hm).symm v =
      polynomialProjChartGeneratedTwistedDegreeToGlobalSections K n M m v := rfl

end ActualProjective
end
end SGPT.Foundations.Schemes
