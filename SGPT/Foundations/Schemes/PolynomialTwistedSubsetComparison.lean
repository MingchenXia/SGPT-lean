import SGPT.Foundations.Schemes.PolynomialTwistedSubsetNaturality
import SGPT.Foundations.Schemes.PolynomialHomogeneousSubsetLocalization

/-! # Genuine chart-to-intersection evaluation and localization comparisons -/

open CategoryTheory Opposite AlgebraicGeometry

namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
variable (M : (polynomialProj K n).Modules) (i : Fin (n + 1))
  (S : Finset (Fin (n + 1))) (hi : i ∈ S)

/-- Actual selected-chart restriction is linear for the genuine common-frame polynomial action. -/
def polynomialTwistedSubsetCoordinateRestriction :
    bundleSections M (polynomialProjCoordinateOpen K n i) →ₗ[MvPolynomial (Fin (n + 1)) K]
      polynomialTwistedSubsetSections K n M i S hi where
  toFun := M.presheaf.map (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi)).op
  map_add' := by intro x y; simp
  map_smul' p x := by
    change M.presheaf.map (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi)).op
      (polynomialTwistedCoordinatePolynomialMap K n i p • x) =
        polynomialTwistedSubsetPolynomialMap K n i S hi p •
          M.presheaf.map (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi)).op x
    rw [Scheme.Modules.map_smul]
    rfl

/-- The normalized selected coordinate acts by its actual identity on actual intersection sections. -/
theorem polynomialTwistedSubsetCoordinateLocalizationUnits :
    ∀ s : Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K),
      IsUnit (algebraMap (MvPolynomial (Fin (n + 1)) K)
        (Module.End (MvPolynomial (Fin (n + 1)) K)
          (polynomialTwistedSubsetSections K n M i S hi)) s) := by
  intro s
  obtain ⟨q, hq⟩ := s.property
  have he : algebraMap (MvPolynomial (Fin (n + 1)) K)
      (Module.End (MvPolynomial (Fin (n + 1)) K)
        (polynomialTwistedSubsetSections K n M i S hi)) s = 1 := by
    apply LinearMap.ext
    intro t
    change polynomialTwistedSubsetPolynomialMap K n i S hi s.val • t = t
    rw [← hq, map_pow]
    change ((polynomialProj K n).presheaf.map
      (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi)).op
        (polynomialTwistedCoordinatePolynomialMap K n i (MvPolynomial.X i))) ^ q • t = t
    rw [polynomialTwistedCoordinatePolynomialMap_self, map_one, one_pow, one_smul]
  rw [he]
  exact isUnit_one

/-- Genuine Xi-localized coefficient evaluation commutes with true product restriction. -/
theorem polynomialTwistedSubsetCoordinateEvaluation_restrict :
    (polynomialTwistedSubsetLocalizedEvaluation K n M i S hi).comp
      (actualLocalizedModuleDivisorRestriction
        (M := polynomialProjTwistedSectionModule K n M) (MvPolynomial.X i)
        (polynomialHomogeneousSubsetProduct K n S)
        ⟨polynomialHomogeneousSubsetProduct K n (S.erase i),
          polynomialHomogeneousSubsetProduct_factor K n i S hi⟩) =
      (polynomialTwistedSubsetCoordinateRestriction K n M i S hi).comp
        (polynomialTwistedLocalizedCoordinateEvaluation K n M i) := by
  apply IsLocalizedModule.ext (Submonoid.powers (MvPolynomial.X i))
    (LocalizedModule.mkLinearMap _ (polynomialProjTwistedSectionModule K n M))
    (polynomialTwistedSubsetCoordinateLocalizationUnits K n M i S hi)
  rw [LinearMap.comp_assoc, actualLocalizedModuleDivisorRestriction_comp,
    polynomialTwistedSubsetLocalizedEvaluation, LocalizedModule.lift_comp,
    LinearMap.comp_assoc, polynomialTwistedLocalizedCoordinateEvaluation, LocalizedModule.lift_comp]
  rfl

/-- Genuine selected-chart degree-zero restriction has the literal true sheaf coefficient square. -/
theorem polynomialTwistedSubsetDegreeZeroMap_chartRestriction
    (z : polynomialTwistedCoordinateDegreeZero K n M i) :
    polynomialTwistedSubsetDegreeZeroMap K n M i S hi
      (polynomialHomogeneousSubsetChartRestrictionK K n
        (polynomialProjTwistedSectionPiece K n M) i S hi 0 z) =
      M.presheaf.map (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi)).op
        (polynomialTwistedCoordinateDegreeZeroMap K n M i z) :=
  LinearMap.congr_fun (polynomialTwistedSubsetCoordinateEvaluation_restrict K n M i S hi) z.val

/-- Actual intersection sections carry their genuine restricted native chart-ring action. -/
def polynomialTwistedSubsetNativeSections : ModuleCat (polynomialProjCoordinateRing K n i) := by
  letI := Module.compHom (bundleSections M (polynomialProjSubsetCoordinateOpen K n S))
    (polynomialProjSubsetRegularMap K n i S hi)
  exact ModuleCat.of (polynomialProjCoordinateRing K n i)
    (bundleSections M (polynomialProjSubsetCoordinateOpen K n S))

/-- The actual subset section isomorphism preserves the true native chart-ring action. -/
def polynomialTwistedSubsetNativeSectionsMap :
    Γ(polynomialProjModuleChart M i,
      PrimeSpectrum.basicOpen (polynomialProjSubsetRatioProduct K n i S)) →ₗ[polynomialProjCoordinateRing K n i]
        polynomialTwistedSubsetNativeSections K n M i S hi where
  toFun := (polynomialProjChartSubsetSectionsIso K n M i S hi).hom
  map_add' := by intro x y; simp
  map_smul' := polynomialProjChartSubsetSectionsIso_smul K n M i S hi

/-- Genuine affine principal-open sections and true intersection sections are natively linearly equivalent. -/
def polynomialTwistedSubsetNativeSectionsEquiv :
    Γ(polynomialProjModuleChart M i,
      PrimeSpectrum.basicOpen (polynomialProjSubsetRatioProduct K n i S)) ≃ₗ[polynomialProjCoordinateRing K n i]
        polynomialTwistedSubsetNativeSections K n M i S hi :=
  LinearEquiv.ofBijective (polynomialTwistedSubsetNativeSectionsMap K n M i S hi)
    (ConcreteCategory.bijective_of_isIso (polynomialProjChartSubsetSectionsIso K n M i S hi).hom)

/-- The true native chart-to-intersection map is literal affine restriction followed by actual section transport. -/
def polynomialTwistedSubsetNativeRestriction :
    Γ(polynomialProjModuleChart M i, ⊤) →ₗ[polynomialProjCoordinateRing K n i]
      polynomialTwistedSubsetNativeSections K n M i S hi :=
  (polynomialTwistedSubsetNativeSectionsMap K n M i S hi).comp
    (polynomialProjChartSubsetRestriction K n M i S)

/-- Actual affine quasicoherence makes the genuine chart-to-intersection map a true ratio-product localization. -/
theorem polynomialTwistedSubsetNativeRestriction_isLocalized
    [(polynomialProjModuleChart M i).IsQuasicoherent] :
    IsLocalizedModule.Away (polynomialProjSubsetRatioProduct K n i S)
      (polynomialTwistedSubsetNativeRestriction K n M i S hi) := by
  apply (IsLocalizedModule.comp_iff_of_bijective_left
    (Submonoid.powers (polynomialProjSubsetRatioProduct K n i S))
    (polynomialTwistedSubsetNativeSectionsMap K n M i S hi)
    (polynomialTwistedSubsetNativeSectionsEquiv K n M i S hi).bijective).mpr
  exact polynomialProjChartSubsetRestriction_isLocalized K n M i S

end
end SGPT.Foundations.Schemes
