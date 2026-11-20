import SGPT.Foundations.Schemes.PolynomialHomogeneousSubsetLocalization
import SGPT.Foundations.Schemes.PolynomialTwistedSubsetComparison

/-! # Actual native selected-chart scalars on intersection evaluation

The scalar actions are the true homogeneous chart restriction and the true
regular-section restriction. Native localization produces a chart-linear
extension, and literal denominator clearing identifies it with the genuine
normalized subset evaluation.
-/

open CategoryTheory Opposite AlgebraicGeometry
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

variable {V W : Type} [AddCommGroup V] [AddCommGroup W]
  [Module K V] [Module K W]
  [Module (MvPolynomial (Fin (n + 1)) K) V]
  [Module (MvPolynomial (Fin (n + 1)) K) W]
  [IsScalarTower K (MvPolynomial (Fin (n + 1)) K) V]
  [IsScalarTower K (MvPolynomial (Fin (n + 1)) K) W]
  (ℳ : ℤ → Submodule K V) (𝒩 : ℤ → Submodule K W)
  [SetLike.GradedSMul (polynomialIntegralGrading (K := K) (I := Fin (n + 1))) ℳ]
  [SetLike.GradedSMul (polynomialIntegralGrading (K := K) (I := Fin (n + 1))) 𝒩]

/-- Every genuine homogeneous map respects the literal actual product-chart scalar action. -/
theorem polynomialHomogeneousSubsetPieceMap_smul
    (f : V →ₗ[MvPolynomial (Fin (n + 1)) K] W)
    (hf : ∀ k v, v ∈ ℳ k → f v ∈ 𝒩 k)
    (S : Finset (Fin (n + 1))) (k : ℤ)
    (r : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (polynomialHomogeneousSubsetProduct K n S))
    (z : polynomialHomogeneousSubsetPiece K n ℳ S k) :
    localizedHomogeneousModuleMap polynomialIntegralGrading ℳ 𝒩 f hf
      (polynomialHomogeneousSubsetProduct K n S) (S.card : ℤ)
      (homogeneousCoordinateSubsetProduct_degree _ _ polynomialCoordinate_X_degree S) k (r • z) =
    r • localizedHomogeneousModuleMap polynomialIntegralGrading ℳ 𝒩 f hf
      (polynomialHomogeneousSubsetProduct K n S) (S.card : ℤ)
      (homogeneousCoordinateSubsetProduct_degree _ _ polynomialCoordinate_X_degree S) k z := by
  apply Subtype.ext
  obtain ⟨a, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _
    (polynomialHomogeneousSubsetProduct_degree K n S) r
  obtain ⟨b, v, hv, he⟩ := z.property
  change actualLocalizedModuleMap (Submonoid.powers (polynomialHomogeneousSubsetProduct K n S)) f
    ((HomogeneousLocalization.Away.mk _ (polynomialHomogeneousSubsetProduct_degree K n S)
      a p hp).val • z.val) =
    (HomogeneousLocalization.Away.mk _ (polynomialHomogeneousSubsetProduct_degree K n S)
      a p hp).val •
      actualLocalizedModuleMap (Submonoid.powers (polynomialHomogeneousSubsetProduct K n S)) f z.val
  rw [← he, HomogeneousLocalization.Away.val_mk, LocalizedModule.mk_smul_mk,
    actualLocalizedModuleMap_mk, actualLocalizedModuleMap_mk, map_smul,
    LocalizedModule.mk_smul_mk]

/-- Genuine homogeneous maps give genuine linear maps over the actual product chart ring. -/
def polynomialHomogeneousSubsetPieceMap
    (f : V →ₗ[MvPolynomial (Fin (n + 1)) K] W)
    (hf : ∀ k v, v ∈ ℳ k → f v ∈ 𝒩 k)
    (S : Finset (Fin (n + 1))) (k : ℤ) :
    polynomialHomogeneousSubsetPiece K n ℳ S k →ₗ[
      HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
        (polynomialHomogeneousSubsetProduct K n S)] polynomialHomogeneousSubsetPiece K n 𝒩 S k where
  toAddHom := (localizedHomogeneousModuleMap polynomialIntegralGrading ℳ 𝒩 f hf
    (polynomialHomogeneousSubsetProduct K n S) (S.card : ℤ)
    (homogeneousCoordinateSubsetProduct_degree _ _ polynomialCoordinate_X_degree S) k).toAddHom
  map_smul' := polynomialHomogeneousSubsetPieceMap_smul K n ℳ 𝒩 f hf S k

/-- Genuine homogeneous maps give genuine linear maps for a selected true coordinate-chart ring. -/
def polynomialHomogeneousSubsetChartPieceMap
    (f : V →ₗ[MvPolynomial (Fin (n + 1)) K] W)
    (hf : ∀ k v, v ∈ ℳ k → f v ∈ 𝒩 k)
    (i : Fin (n + 1)) (S : Finset (Fin (n + 1))) (hi : i ∈ S) (k : ℤ) :
    letI := polynomialHomogeneousSubsetChartModule K n ℳ i S hi k
    letI := polynomialHomogeneousSubsetChartModule K n 𝒩 i S hi k
    polynomialHomogeneousSubsetPiece K n ℳ S k →ₗ[polynomialProjCoordinateRing K n i]
      polynomialHomogeneousSubsetPiece K n 𝒩 S k := by
  letI := polynomialHomogeneousSubsetChartModule K n ℳ i S hi k
  letI := polynomialHomogeneousSubsetChartModule K n 𝒩 i S hi k
  refine { toFun := polynomialHomogeneousSubsetPieceMap K n ℳ 𝒩 f hf S k
           map_add' := (polynomialHomogeneousSubsetPieceMap K n ℳ 𝒩 f hf S k).map_add
           map_smul' := ?_ }
  intro r z
  exact polynomialHomogeneousSubsetPieceMap_smul K n ℳ 𝒩 f hf S k
    (polynomialHomogeneousSubsetChartRingMap K n i S hi r) z

variable (M : (polynomialProj K n).Modules) (i : Fin (n + 1))
  (S : Finset (Fin (n + 1))) (hi : i ∈ S)

/-- Actual native intersection sections retain their original true regular-section action. -/
instance polynomialTwistedSubsetNativeSectionsRegularModule :
    Module Γ(polynomialProj K n, polynomialProjSubsetCoordinateOpen K n S)
      (polynomialTwistedSubsetNativeSections K n M i S hi) := by
  unfold polynomialTwistedSubsetNativeSections
  infer_instance

/-- True native coordinate coefficients restrict linearly to actual intersection sections. -/
def polynomialTwistedSubsetNativeCoefficientMap :
    polynomialTwistedCoordinateDegreeZero K n M i →ₗ[polynomialProjCoordinateRing K n i]
      polynomialTwistedSubsetNativeSections K n M i S hi := by
  refine { toFun := fun z => M.presheaf.map
             (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi)).op
               (polynomialTwistedCoordinateNativeMap K n i M z)
           map_add' := by intro x y; simp
           map_smul' := ?_ }
  intro r z
  rw [map_smul]
  exact Scheme.Modules.map_smul _ _ _ _

/-- Powers of the true restricted ratio product act invertibly on the actual intersection sections. -/
theorem polynomialTwistedSubsetNativeLocalizationUnits :
    ∀ s : Submonoid.powers (polynomialProjSubsetRatioProduct K n i S),
      IsUnit (algebraMap (polynomialProjCoordinateRing K n i)
        (Module.End (polynomialProjCoordinateRing K n i)
          (polynomialTwistedSubsetNativeSections K n M i S hi)) s) := by
  intro s
  obtain ⟨q, hq⟩ := s.property
  rw [← hq, map_pow]
  apply IsUnit.pow
  rw [Module.End.isUnit_iff]
  change Function.Bijective (fun t : bundleSections M (polynomialProjSubsetCoordinateOpen K n S) =>
    polynomialProjSubsetRegularMap K n i S hi (polynomialProjSubsetRatioProduct K n i S) • t)
  exact (polynomialProjSubsetRegularRatioProduct_isUnit K n i S hi).smul_bijective

/-- Actual module localization produces an actual native chart-linear evaluation extension. -/
def polynomialTwistedSubsetNativeEvaluation :
    letI := polynomialHomogeneousSubsetChartModule K n (polynomialProjTwistedSectionPiece K n M) i S hi 0
    polynomialTwistedSubsetDegreeZero K n M S →ₗ[polynomialProjCoordinateRing K n i]
      polynomialTwistedSubsetNativeSections K n M i S hi := by
  letI := polynomialHomogeneousSubsetChartModule K n (polynomialProjTwistedSectionPiece K n M) i S hi 0
  letI := polynomialHomogeneousSubsetChartRestriction_isLocalized K n
    (polynomialProjTwistedSectionPiece K n M) i S hi 0
  exact IsLocalizedModule.lift (Submonoid.powers (polynomialProjSubsetRatioProduct K n i S))
    (polynomialHomogeneousSubsetChartRestriction K n (polynomialProjTwistedSectionPiece K n M) i S hi 0)
    (polynomialTwistedSubsetNativeCoefficientMap K n M i S hi)
    (polynomialTwistedSubsetNativeLocalizationUnits K n M i S hi)

/-- The genuine native evaluation extension agrees with actual coefficients on every true source chart fraction. -/
theorem polynomialTwistedSubsetNativeEvaluation_apply
    (z : polynomialTwistedCoordinateDegreeZero K n M i) :
    polynomialTwistedSubsetNativeEvaluation K n M i S hi
      (polynomialHomogeneousSubsetChartRestriction K n (polynomialProjTwistedSectionPiece K n M) i S hi 0 z) =
        polynomialTwistedSubsetNativeCoefficientMap K n M i S hi z := by
  let _instPiece := polynomialHomogeneousSubsetChartModule K n (polynomialProjTwistedSectionPiece K n M) i S hi 0
  let _instLocalization := polynomialHomogeneousSubsetChartRestriction_isLocalized K n
    (polynomialProjTwistedSectionPiece K n M) i S hi 0
  exact IsLocalizedModule.lift_apply _ _ _ _ z

/-- The true native chart-linear extension is exactly the actual normalized product-fraction evaluation. -/
theorem polynomialTwistedSubsetNativeEvaluation_eq_degreeZeroMap
    (z : polynomialTwistedSubsetDegreeZero K n M S) :
    polynomialTwistedSubsetNativeEvaluation K n M i S hi z =
      (show polynomialTwistedSubsetNativeSections K n M i S hi from
        polynomialTwistedSubsetDegreeZeroMap K n M i S hi z) := by
  let _instPiece := polynomialHomogeneousSubsetChartModule K n (polynomialProjTwistedSectionPiece K n M) i S hi 0
  obtain ⟨q, t, ht⟩ := polynomialTwistedSubsetDegreeZero_fraction_exists K n M S z
  let v := (polynomialProjTwistingLine K n).ofTwistedSection M (q * S.card) t
  have hv : v ∈ polynomialProjTwistedSectionPiece K n M
      (0 + ((q * S.card : ℕ) : ℤ) * 1) := by
    simpa only [zero_add, mul_one] using polynomialProjTwistedSectionPiece_ofTwistedSection K n M (q * S.card) t
  let w : polynomialTwistedCoordinateDegreeZero K n M i :=
    ⟨LocalizedModule.mk v (homogeneousPowerDenominator (MvPolynomial.X i) (q * S.card)),
      q * S.card, v, hv, rfl⟩
  have hpow : polynomialProjSubsetRatioProduct K n i S ^ q • z =
      polynomialHomogeneousSubsetChartRestriction K n (polynomialProjTwistedSectionPiece K n M) i S hi 0 w := by
    apply Subtype.ext
    rw [polynomialHomogeneousSubsetChartRestriction_fraction K n
      (polynomialProjTwistedSectionPiece K n M) i S hi 0 (q * S.card) v hv]
    change ((polynomialHomogeneousSubsetChartRingMap K n i S hi)
      (polynomialProjSubsetRatioProduct K n i S ^ q)).val • z.val = _
    rw [← ht, map_pow, polynomialProjSubsetRatioProduct_eq_mk]
    change (HomogeneousLocalization.awayMap _
      (polynomialHomogeneousSubsetProduct_degree K n (S.erase i))
      (polynomialHomogeneousSubsetProduct_factor K n i S hi)
      (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X K i) S.card
        (polynomialHomogeneousSubsetProduct K n S) _) ^ q).val • _ = _
    rw [HomogeneousLocalization.val_pow, HomogeneousLocalization.awayMap_mk,
      HomogeneousLocalization.Away.val_mk, Localization.mk_pow, LocalizedModule.mk_smul_mk]
    apply LocalizedModule.mk_eq.mpr
    refine ⟨1, ?_⟩
    simp only [Submonoid.smul_def, Submonoid.coe_mul, SubmonoidClass.coe_pow,
      homogeneousPowerDenominator, smul_smul]
    congr 1
    simp only [mul_pow, pow_mul]
    ring
  apply ((polynomialProjSubsetRegularRatioProduct_isUnit K n i S hi).pow q).smul_bijective.injective
  dsimp only
  rw [polynomialTwistedSubsetDegreeZeroMap_cleared K n M i S hi q t z ht, ← map_pow]
  change (polynomialProjSubsetRatioProduct K n i S ^ q) •
      polynomialTwistedSubsetNativeEvaluation K n M i S hi z = _
  rw [← map_smul, hpow, polynomialTwistedSubsetNativeEvaluation_apply]
  change M.presheaf.map (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi)).op
    (polynomialTwistedCoordinateDegreeZeroMap K n M i w) = _
  congr 1
  exact polynomialTwistedCoordinateDegreeZeroMap_fraction K n M i (q * S.card) t

/-- Actual normalized product evaluation preserves the true selected-chart scalar action. -/
theorem polynomialTwistedSubsetDegreeZeroMap_native_smul
    (r : polynomialProjCoordinateRing K n i) (z : polynomialTwistedSubsetDegreeZero K n M S) :
    letI := polynomialHomogeneousSubsetChartModule K n (polynomialProjTwistedSectionPiece K n M) i S hi 0
    polynomialTwistedSubsetDegreeZeroMap K n M i S hi (r • z) =
      (show (actualSchemeModuleBaseSubsetDiagram M (polynomialProjCoordinateOpen K n)
        (schemeConstantMap (polynomialProjStructureMap K n))).obj S from
        polynomialProjSubsetRegularMap K n i S hi r •
          (show bundleSections M (polynomialProjSubsetCoordinateOpen K n S) from
            polynomialTwistedSubsetDegreeZeroMap K n M i S hi z)) := by
  let _instPiece := polynomialHomogeneousSubsetChartModule K n (polynomialProjTwistedSectionPiece K n M) i S hi 0
  change (show polynomialTwistedSubsetNativeSections K n M i S hi from
      polynomialTwistedSubsetDegreeZeroMap K n M i S hi (r • z)) =
    r • (show polynomialTwistedSubsetNativeSections K n M i S hi from
      polynomialTwistedSubsetDegreeZeroMap K n M i S hi z)
  rw [← polynomialTwistedSubsetNativeEvaluation_eq_degreeZeroMap,
    ← polynomialTwistedSubsetNativeEvaluation_eq_degreeZeroMap, map_smul]


end
end SGPT.Foundations.Schemes
