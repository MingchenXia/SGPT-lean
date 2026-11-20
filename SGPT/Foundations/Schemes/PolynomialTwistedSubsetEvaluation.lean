import SGPT.Foundations.Schemes.PolynomialProjectiveSubsetCharts

/-! # Actual normalized twisted-section evaluation on coordinate intersections

True coordinate ratios act on actual intersection sections. Their genuine
invertibility descends actual global coefficient evaluation through the
native module localization, retaining its actual torsion relations.
-/

open CategoryTheory Opposite AlgebraicGeometry
open scoped DirectSum

namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
variable (M : (polynomialProj K n).Modules) (i : Fin (n + 1))
  (S : Finset (Fin (n + 1))) (hi : i ∈ S)

/-- The actual normalized polynomial scalar map on an actual selected intersection. -/
def polynomialTwistedSubsetPolynomialMap :
    MvPolynomial (Fin (n + 1)) K →+*
      Γ(polynomialProj K n, polynomialProjSubsetCoordinateOpen K n S) :=
  ((polynomialProj K n).presheaf.map
    (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi)).op).hom.comp
      (polynomialTwistedCoordinatePolynomialMap K n i)

/-- Actual intersection sections with the genuine normalized polynomial action. -/
def polynomialTwistedSubsetSections : ModuleCat (MvPolynomial (Fin (n + 1)) K) := by
  letI := Module.compHom (bundleSections M (polynomialProjSubsetCoordinateOpen K n S))
    (polynomialTwistedSubsetPolynomialMap K n i S hi)
  exact ModuleCat.of (MvPolynomial (Fin (n + 1)) K)
    (bundleSections M (polynomialProjSubsetCoordinateOpen K n S))

/-- These actual sections retain their original action by actual regular intersection sections. -/
instance polynomialTwistedSubsetSectionsRegularModule :
    Module Γ(polynomialProj K n, polynomialProjSubsetCoordinateOpen K n S)
      (polynomialTwistedSubsetSections K n M i S hi) := by
  unfold polynomialTwistedSubsetSections
  infer_instance

/-- Every genuine global coefficient sum restricts to actual intersection sections. -/
def polynomialTwistedSubsetCoefficientMap :
    polynomialProjTwistedSectionModule K n M →ₗ[MvPolynomial (Fin (n + 1)) K]
      polynomialTwistedSubsetSections K n M i S hi where
  toFun x := M.presheaf.map (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi)).op
    (polynomialTwistedCoordinateCoefficientSum K n M i x)
  map_add' x y := by simp
  map_smul' p x := by
    change M.presheaf.map _ (polynomialTwistedCoordinateCoefficientSum K n M i (p • x)) =
      polynomialTwistedSubsetPolynomialMap K n i S hi p • _
    rw [polynomialTwistedCoordinateCoefficientSum_smul, Scheme.Modules.map_smul]
    rfl

/-- Polynomial constants on the actual intersection are its true restricted structural constants. -/
theorem polynomialTwistedSubsetPolynomialMap_C (c : K) :
    polynomialTwistedSubsetPolynomialMap K n i S hi (MvPolynomial.C c) =
      polynomialProjSubsetConstants K n S c := by
  change (polynomialProj K n).presheaf.map _
    (polynomialTwistedCoordinatePolynomialMap K n i (MvPolynomial.C c)) = _
  simp only [polynomialTwistedCoordinatePolynomialMap, MvPolynomial.eval₂Hom_C]
  change (polynomialProj K n).presheaf.map _
    ((polynomialProj K n).presheaf.map _ (schemeConstantMap (polynomialProjStructureMap K n) c)) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The actual polynomial coordinate product evaluates to the literal restricted native ratio product. -/
theorem polynomialTwistedSubsetPolynomialMap_product :
    polynomialTwistedSubsetPolynomialMap K n i S hi
      (homogeneousCoordinateSubsetProduct (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) S) =
    polynomialProjSubsetRegularMap K n i S hi (polynomialProjSubsetRatioProduct K n i S) := by
  change (polynomialProj K n).presheaf.map _
    (polynomialTwistedCoordinatePolynomialMap K n i
      (∏ j ∈ S, MvPolynomial.X j)) =
    (polynomialProj K n).presheaf.map _
      (homogeneousPolynomialBasicOpenAwayEquiv i (∏ j ∈ S, polynomialProjCoordinateRatio K n i j))
  congr 1
  simp [polynomialTwistedCoordinatePolynomialMap, map_prod]

/-- The actual denominator product acts invertibly on true intersection sections. -/
theorem polynomialTwistedSubsetLocalizationUnits :
    ∀ s : Submonoid.powers
      (homogeneousCoordinateSubsetProduct (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) S),
      IsUnit (algebraMap (MvPolynomial (Fin (n + 1)) K)
        (Module.End (MvPolynomial (Fin (n + 1)) K)
          (polynomialTwistedSubsetSections K n M i S hi)) s) := by
  intro s
  obtain ⟨q, hq⟩ := s.property
  rw [← hq, map_pow]
  apply IsUnit.pow
  rw [Module.End.isUnit_iff]
  change Function.Bijective (fun t : bundleSections M (polynomialProjSubsetCoordinateOpen K n S) =>
    polynomialTwistedSubsetPolynomialMap K n i S hi
      (homogeneousCoordinateSubsetProduct (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) S) • t)
  rw [polynomialTwistedSubsetPolynomialMap_product]
  exact (polynomialProjSubsetRegularRatioProduct_isUnit K n i S hi).smul_bijective

/-- The native actual product localization descends the genuine intersection coefficient map. -/
def polynomialTwistedSubsetLocalizedEvaluation :
    LocalizedModule (Submonoid.powers
      (homogeneousCoordinateSubsetProduct (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) S))
      (polynomialProjTwistedSectionModule K n M) →ₗ[MvPolynomial (Fin (n + 1)) K]
        polynomialTwistedSubsetSections K n M i S hi :=
  LocalizedModule.lift _ (polynomialTwistedSubsetCoefficientMap K n M i S hi)
    (polynomialTwistedSubsetLocalizationUnits K n M i S hi)

/-- The literal native localized degree-zero Γ-star piece for the actual coordinate product. -/
abbrev polynomialTwistedSubsetDegreeZero :=
  localizedHomogeneousModulePiece
    (polynomialIntegralGrading (K := K) (I := Fin (n + 1)))
    (polynomialProjTwistedSectionPiece K n M)
    (homogeneousCoordinateSubsetProduct (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) S)
    (S.card : ℤ) (homogeneousCoordinateSubsetProduct_degree polynomialIntegralGrading
      (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K))
      (polynomialCoordinate_X_degree) S) 0

/-- Actual normalized degree-zero evaluation has the genuine structural field action of the actual sheaf diagram. -/
def polynomialTwistedSubsetDegreeZeroMap :
    polynomialTwistedSubsetDegreeZero K n M S →ₗ[K]
      (actualSchemeModuleBaseSubsetDiagram M (polynomialProjCoordinateOpen K n)
        (schemeConstantMap (polynomialProjStructureMap K n))).obj S where
  toFun z := polynomialTwistedSubsetLocalizedEvaluation K n M i S hi z.val
  map_add' x y := by simp
  map_smul' c z := by
    change polynomialTwistedSubsetLocalizedEvaluation K n M i S hi (c • z.val) =
      polynomialProjSubsetConstants K n S c •
        polynomialTwistedSubsetLocalizedEvaluation K n M i S hi z.val
    rw [← IsScalarTower.algebraMap_smul (R := K) (MvPolynomial (Fin (n + 1)) K) c z.val,
      LinearMap.map_smul]
    change polynomialTwistedSubsetPolynomialMap K n i S hi (MvPolynomial.C c) •
      polynomialTwistedSubsetLocalizedEvaluation K n M i S hi z.val =
      polynomialProjSubsetConstants K n S c • polynomialTwistedSubsetLocalizedEvaluation K n M i S hi z.val
    rw [polynomialTwistedSubsetPolynomialMap_C]

/-- Every genuine product fraction satisfies the literal true denominator-clearing evaluation formula. -/
theorem polynomialTwistedSubsetLocalizedEvaluation_mk (q : ℕ)
    (x : polynomialProjTwistedSectionModule K n M) :
    (polynomialProjSubsetRegularMap K n i S hi (polynomialProjSubsetRatioProduct K n i S)) ^ q •
      (polynomialTwistedSubsetLocalizedEvaluation K n M i S hi
        (LocalizedModule.mk x (homogeneousPowerDenominator
          (homogeneousCoordinateSubsetProduct (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) S) q))) =
    M.presheaf.map (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi)).op
      (polynomialTwistedCoordinateCoefficientSum K n M i x) := by
  rw [polynomialTwistedSubsetLocalizedEvaluation, LocalizedModule.lift_mk]
  have h := Module.End.isUnit_apply_inv_apply_of_isUnit
    (polynomialTwistedSubsetLocalizationUnits K n M i S hi
      (homogeneousPowerDenominator _ q))
    (polynomialTwistedSubsetCoefficientMap K n M i S hi x)
  change polynomialTwistedSubsetPolynomialMap K n i S hi
    ((homogeneousCoordinateSubsetProduct (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) S) ^ q) •
      ((polynomialTwistedSubsetLocalizationUnits K n M i S hi (homogeneousPowerDenominator _ q)).unit.inv
        (polynomialTwistedSubsetCoefficientMap K n M i S hi x)) =
      polynomialTwistedSubsetCoefficientMap K n M i S hi x at h
  rw [map_pow, polynomialTwistedSubsetPolynomialMap_product] at h
  exact h

/-- Every true product degree-zero fraction has a genuine global twist of its literal numerator degree. -/
theorem polynomialTwistedSubsetDegreeZero_fraction_exists
    (z : polynomialTwistedSubsetDegreeZero K n M S) :
    ∃ (q : ℕ) (t : bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M (q * S.card)),
      LocalizedModule.mk ((polynomialProjTwistingLine K n).ofTwistedSection M (q * S.card) t)
        (homogeneousPowerDenominator
          (homogeneousCoordinateSubsetProduct (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) S) q) = z.val := by
  obtain ⟨q, x, hx, he⟩ := z.property
  have hx' : x ∈ polynomialProjTwistedSectionPiece K n M ((q * S.card : ℕ) : ℤ) := by
    simpa only [zero_add, Nat.cast_mul] using hx
  let y : ⨁ d : ℕ, bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M d := x
  have hs : x = (polynomialProjTwistingLine K n).ofTwistedSection M (q * S.card) (y (q * S.card)) :=
    nonnegativeDirectSumPiece_eq_single K
      (bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M) (q * S.card) ⟨y, hx'⟩
  exact ⟨q, y (q * S.card), hs ▸ he⟩

/-- The actual line-frame transition unit between two genuinely selected coordinate frames. -/
def polynomialTwistedSubsetTransitionUnit (j : Fin (n + 1)) (hj : j ∈ S) :
    Γ(polynomialProj K n, polynomialProjSubsetCoordinateOpen K n S)ˣ :=
  localBundleFrameTransition ((polynomialProjTwistingLine K n).atlas.frame i)
    ((polynomialProjTwistingLine K n).atlas.frame j)
    (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi))
    (homOfLE (polynomialProjSubsetCoordinateOpen_le K n j S hj))

/-- Every genuine twisted global numerator obeys its actual frame-change power law on the true intersection. -/
theorem polynomialTwistedSubsetCoefficient_transition (j : Fin (n + 1)) (hj : j ∈ S)
    (d : ℕ) (t : bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M d) :
    M.presheaf.map (homOfLE (polynomialProjSubsetCoordinateOpen_le K n j S hj)).op
      (atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M d j t) =
    (polynomialTwistedSubsetTransitionUnit K n i S hi j hj :
      Γ(polynomialProj K n, polynomialProjSubsetCoordinateOpen K n S)) ^ d •
      M.presheaf.map (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi)).op
        (atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M d i t) :=
  LocalBundleFrame.twisted_global_coefficients_transition _ _ M _ _ d t

/-- Actual coordinate ratios on the true intersection obey the literal degree-one frame-change law. -/
theorem polynomialTwistedSubsetRatio_transition (j : Fin (n + 1)) (hj : j ∈ S)
    (a : Fin (n + 1)) :
    polynomialProjSubsetRegularMap K n j S hj (polynomialProjCoordinateRatio K n j a) =
    (polynomialTwistedSubsetTransitionUnit K n i S hi j hj :
      Γ(polynomialProj K n, polynomialProjSubsetCoordinateOpen K n S)) *
      polynomialProjSubsetRegularMap K n i S hi (polynomialProjCoordinateRatio K n i a) := by
  have h := LocalBundleFrame.global_coefficients_transition
    ((polynomialProjTwistingLine K n).atlas.frame i) ((polynomialProjTwistingLine K n).atlas.frame j)
    (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi))
    (homOfLE (polynomialProjSubsetCoordinateOpen_le K n j S hj)) 1
    (polynomialProjTwistedGlobalCoordinate K n a)
  change (polynomialProj K n).sheaf.obj.map
    (homOfLE (polynomialProjSubsetCoordinateOpen_le K n j S hj)).op
    (atlasPowerGlobalCoefficients (polynomialProjTwistingLine K n).atlas 1 j
      (polynomialProjTwistedGlobalCoordinate K n a)) =
    (localBundleFrameTransition
      ((polynomialProjTwistingLine K n).atlas.frame i) ((polynomialProjTwistingLine K n).atlas.frame j)
      (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi))
      (homOfLE (polynomialProjSubsetCoordinateOpen_le K n j S hj)) :
      (polynomialProj K n).sheaf.obj.obj (op (polynomialProjSubsetCoordinateOpen K n S))) ^ 1 *
      (polynomialProj K n).sheaf.obj.map
        (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi)).op
        (atlasPowerGlobalCoefficients (polynomialProjTwistingLine K n).atlas 1 i
          (polynomialProjTwistedGlobalCoordinate K n a)) at h
  erw [polynomialProjTwistedGlobalCoordinate_coefficient,
    polynomialProjTwistedGlobalCoordinate_coefficient, pow_one] at h
  exact h

/-- The literal denominator product transforms by exactly its actual cardinal degree. -/
theorem polynomialTwistedSubsetRatioProduct_transition (j : Fin (n + 1)) (hj : j ∈ S) :
    polynomialProjSubsetRegularMap K n j S hj (polynomialProjSubsetRatioProduct K n j S) =
    (polynomialTwistedSubsetTransitionUnit K n i S hi j hj :
      Γ(polynomialProj K n, polynomialProjSubsetCoordinateOpen K n S)) ^ S.card *
      polynomialProjSubsetRegularMap K n i S hi (polynomialProjSubsetRatioProduct K n i S) := by
  classical
  rw [polynomialProjSubsetRatioProduct, map_prod, polynomialProjSubsetRatioProduct, map_prod]
  simp_rw [polynomialTwistedSubsetRatio_transition K n i S hi j hj]
  rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- Actual normalized degree-zero evaluation satisfies the real numerator-coefficient formula for every genuine fraction. -/
theorem polynomialTwistedSubsetDegreeZeroMap_cleared (q : ℕ)
    (t : bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M (q * S.card))
    (z : polynomialTwistedSubsetDegreeZero K n M S)
    (ht : LocalizedModule.mk ((polynomialProjTwistingLine K n).ofTwistedSection M (q * S.card) t)
      (homogeneousPowerDenominator
        (homogeneousCoordinateSubsetProduct (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) S) q) = z.val) :
    (polynomialProjSubsetRegularMap K n i S hi (polynomialProjSubsetRatioProduct K n i S)) ^ q •
      (show bundleSections M (polynomialProjSubsetCoordinateOpen K n S) from
        polynomialTwistedSubsetDegreeZeroMap K n M i S hi z) =
    M.presheaf.map (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi)).op
      (atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M (q * S.card) i t) := by
  change (polynomialProjSubsetRegularMap K n i S hi (polynomialProjSubsetRatioProduct K n i S)) ^ q •
      polynomialTwistedSubsetLocalizedEvaluation K n M i S hi z.val = _
  erw [← ht, polynomialTwistedSubsetLocalizedEvaluation_mk,
    polynomialTwistedCoordinateCoefficientSum_of]

/-- Genuine numerator and denominator transition powers cancel, so actual evaluation is independent of the selected chart. -/
theorem polynomialTwistedSubsetDegreeZeroMap_independent (j : Fin (n + 1)) (hj : j ∈ S)
    (z : polynomialTwistedSubsetDegreeZero K n M S) :
    polynomialTwistedSubsetDegreeZeroMap K n M i S hi z =
      polynomialTwistedSubsetDegreeZeroMap K n M j S hj z := by
  obtain ⟨q, t, ht⟩ := polynomialTwistedSubsetDegreeZero_fraction_exists K n M S z
  change (show bundleSections M (polynomialProjSubsetCoordinateOpen K n S) from
      polynomialTwistedSubsetDegreeZeroMap K n M i S hi z) =
    (show bundleSections M (polynomialProjSubsetCoordinateOpen K n S) from
      polynomialTwistedSubsetDegreeZeroMap K n M j S hj z)
  apply ((polynomialProjSubsetRegularRatioProduct_isUnit K n j S hj).pow q).smul_bijective.injective
  dsimp only
  rw [polynomialTwistedSubsetDegreeZeroMap_cleared K n M j S hj q t z ht,
    polynomialTwistedSubsetCoefficient_transition K n M i S hi j hj]
  rw [polynomialTwistedSubsetRatioProduct_transition K n i S hi j hj, mul_pow,
    ← pow_mul, Nat.mul_comm S.card q, mul_smul,
    polynomialTwistedSubsetDegreeZeroMap_cleared K n M i S hi q t z ht]

end
end SGPT.Foundations.Schemes
