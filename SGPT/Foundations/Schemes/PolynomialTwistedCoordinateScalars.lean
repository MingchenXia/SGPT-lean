import SGPT.Foundations.Schemes.PolynomialTwistedCoordinateLocalization

/-! # Native chart-ring scalars on actual homogeneous coordinate localization

The chart-ring action below is the restriction of the actual ordinary
localization action. Its preservation of degree zero is proved from literal
homogeneous fractions. Normalized evaluation respects these native scalars.
-/

open CategoryTheory Opposite AlgebraicGeometry
open scoped DirectSum

namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Native nonnegative homogeneous degrees are the same literal integral degrees. -/
theorem polynomialHomogeneous_mem_integral (a : ℕ)
    (p : MvPolynomial (Fin (n + 1)) K)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K a) :
    p ∈ polynomialIntegralGrading (a : ℤ) := by
  classical
  intro e he
  have h : Finsupp.weight (fun _ : Fin (n + 1) => (1 : ℕ)) e = a := hp he
  change Finsupp.weight (fun _ : Fin (n + 1) => (1 : ℤ)) e = (a : ℤ)
  rw [Finsupp.weight_eq_sum]
  rw [Finsupp.weight_eq_sum] at h
  simpa only [nsmul_eq_mul, mul_one, Nat.cast_id, ← Nat.cast_sum] using congrArg (fun z : ℕ => (z : ℤ)) h

variable {V : Type} [AddCommGroup V] [Module K V]
  [Module (MvPolynomial (Fin (n + 1)) K) V]
  [IsScalarTower K (MvPolynomial (Fin (n + 1)) K) V]
  (ℳ : ℤ → Submodule K V) [SetLike.GradedSMul (polynomialIntegralGrading (K := K) (I := Fin (n + 1))) ℳ]
  (i : Fin (n + 1))

/-- Actual chart scalars act by their native values in the actual ordinary localization. -/
instance polynomialCoordinateLocalizedModuleScalars :
    Module (polynomialProjCoordinateRing K n i)
      (LocalizedModule (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K)) V) :=
  Module.compHom _ (algebraMap (polynomialProjCoordinateRing K n i)
    (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K)))

/-- Native degree-zero chart fractions preserve every actual integral localized degree. -/
theorem polynomialCoordinateLocalized_smul_mem (k : ℤ)
    (r : polynomialProjCoordinateRing K n i)
    (z : LocalizedModule (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K)) V)
    (hz : z ∈ localizedHomogeneousModulePiece (polynomialIntegralGrading (K := K) (I := Fin (n + 1))) ℳ
      (MvPolynomial.X i) 1 (polynomialCoordinate_X_degree i) k) :
    r • z ∈ localizedHomogeneousModulePiece (polynomialIntegralGrading (K := K) (I := Fin (n + 1))) ℳ
      (MvPolynomial.X i) 1 (polynomialCoordinate_X_degree i) k := by
  obtain ⟨a, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _
    (MvPolynomial.isHomogeneous_X K i) r
  obtain ⟨b, v, hv, rfl⟩ := hz
  refine ⟨a + b, p • v, ?_, ?_⟩
  · have hp' := polynomialHomogeneous_mem_integral K n a p (by simpa using hp)
    convert SetLike.GradedSMul.smul_mem hp' hv using 1
    congr 1
    simp only [vadd_eq_add, Nat.cast_add]
    ring
  · change LocalizedModule.mk (p • v) (homogeneousPowerDenominator (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) (a + b)) =
      (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.isHomogeneous_X K i) a p hp).val • LocalizedModule.mk v (homogeneousPowerDenominator (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) b)
    rw [HomogeneousLocalization.Away.val_mk, LocalizedModule.mk_smul_mk]
    congr 1
    exact homogeneousPowerDenominator_add _ _ _

/-- The actual localized degree piece carries the literal restricted native chart action. -/
instance polynomialCoordinateLocalizedPieceSMul (k : ℤ) :
    SMul (polynomialProjCoordinateRing K n i)
      (localizedHomogeneousModulePiece (polynomialIntegralGrading (K := K) (I := Fin (n + 1))) ℳ
        (MvPolynomial.X i) 1 (polynomialCoordinate_X_degree i) k) where
  smul r z := ⟨r • z.val, polynomialCoordinateLocalized_smul_mem K n ℳ i k r z.val z.property⟩

/-- Native module laws restrict to the genuine localized degree piece. -/
instance polynomialCoordinateLocalizedPieceModule (k : ℤ) :
    Module (polynomialProjCoordinateRing K n i)
      (localizedHomogeneousModulePiece (polynomialIntegralGrading (K := K) (I := Fin (n + 1))) ℳ
        (MvPolynomial.X i) 1 (polynomialCoordinate_X_degree i) k) :=
  Subtype.coe_injective.module _
    (localizedHomogeneousModulePiece (polynomialIntegralGrading (K := K) (I := Fin (n + 1))) ℳ
      (MvPolynomial.X i) 1 (polynomialCoordinate_X_degree i) k).subtype.toAddMonoidHom
    (fun _ _ => rfl)

/-- Native homogeneous chart constants preserve the original genuine field action on every localized degree. -/
instance polynomialCoordinateLocalizedPieceScalarTower (k : ℤ) :
    IsScalarTower K (polynomialProjCoordinateRing K n i)
      (localizedHomogeneousModulePiece polynomialIntegralGrading ℳ
        (MvPolynomial.X i) 1 (polynomialCoordinate_X_degree i) k) := by
  constructor
  intro c r z
  apply Subtype.ext
  change (c • r).val • z.val = c • (r.val • z.val)
  rw [HomogeneousLocalization.val_smul]
  obtain ⟨a, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _
    (MvPolynomial.isHomogeneous_X K i) r
  obtain ⟨b, v, hv, he⟩ := z.property
  rw [← he, HomogeneousLocalization.Away.val_mk, Localization.smul_mk,
    LocalizedModule.mk_smul_mk, LocalizedModule.mk_smul_mk, LocalizedModule.smul'_mk]
  congr 1
  exact smul_assoc c p v

/-- A true chart scalar multiplies genuine fractions by literal homogeneous numerator multiplication. -/
theorem polynomialCoordinateLocalizedPiece_smul_fraction (k : ℤ) (a b : ℕ)
    (p : MvPolynomial (Fin (n + 1)) K)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K a)
    (v : V) (hv : v ∈ ℳ (k + (b : ℤ) * 1)) :
    ((HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.isHomogeneous_X K i) a p
      (by simpa using hp)) •
      (⟨LocalizedModule.mk v (homogeneousPowerDenominator (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) b),
        b, v, hv, rfl⟩ : localizedHomogeneousModulePiece (polynomialIntegralGrading (K := K) (I := Fin (n + 1))) ℳ
          (MvPolynomial.X i) 1 (polynomialCoordinate_X_degree i) k)).val =
    LocalizedModule.mk (p • v) (homogeneousPowerDenominator (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) (a + b)) := by
  change (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
    (MvPolynomial.isHomogeneous_X K i) a p (by simpa using hp)).val •
    LocalizedModule.mk v (homogeneousPowerDenominator (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) b) = _
  rw [HomogeneousLocalization.Away.val_mk, LocalizedModule.mk_smul_mk]
  congr 1
  exact (homogeneousPowerDenominator_add _ _ _).symm

variable {W : Type} [AddCommGroup W] [Module K W]
  [Module (MvPolynomial (Fin (n + 1)) K) W]
  [IsScalarTower K (MvPolynomial (Fin (n + 1)) K) W]
  (𝒩 : ℤ → Submodule K W)
  [SetLike.GradedSMul (polynomialIntegralGrading (K := K) (I := Fin (n + 1))) 𝒩]

/-- Every actual homogeneous linear map preserves the genuine native chart scalar action. -/
theorem polynomialCoordinateLocalizedPieceMap_smul
    (f : V →ₗ[MvPolynomial (Fin (n + 1)) K] W)
    (hf : ∀ k v, v ∈ ℳ k → f v ∈ 𝒩 k) (k : ℤ)
    (r : polynomialProjCoordinateRing K n i)
    (z : localizedHomogeneousModulePiece polynomialIntegralGrading ℳ
      (MvPolynomial.X i) 1 (polynomialCoordinate_X_degree i) k) :
    localizedHomogeneousModuleMap polynomialIntegralGrading ℳ 𝒩 f hf
      (MvPolynomial.X i) 1 (polynomialCoordinate_X_degree i) k (r • z) =
    r • localizedHomogeneousModuleMap polynomialIntegralGrading ℳ 𝒩 f hf
      (MvPolynomial.X i) 1 (polynomialCoordinate_X_degree i) k z := by
  apply Subtype.ext
  obtain ⟨a, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _
    (MvPolynomial.isHomogeneous_X K i) r
  obtain ⟨b, v, hv, he⟩ := z.property
  change actualLocalizedModuleMap (Submonoid.powers (MvPolynomial.X i)) f
    ((HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (MvPolynomial.isHomogeneous_X K i) a p hp).val • z.val) =
    (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (MvPolynomial.isHomogeneous_X K i) a p hp).val •
      actualLocalizedModuleMap (Submonoid.powers (MvPolynomial.X i)) f z.val
  rw [← he, HomogeneousLocalization.Away.val_mk, LocalizedModule.mk_smul_mk,
    actualLocalizedModuleMap_mk, actualLocalizedModuleMap_mk, map_smul,
    LocalizedModule.mk_smul_mk]

/-- Actual homogeneous maps induce actual native chart-ring linear maps between their literal localized degrees. -/
def polynomialCoordinateLocalizedPieceMap
    (f : V →ₗ[MvPolynomial (Fin (n + 1)) K] W)
    (hf : ∀ k v, v ∈ ℳ k → f v ∈ 𝒩 k) (k : ℤ) :
    localizedHomogeneousModulePiece polynomialIntegralGrading ℳ
      (MvPolynomial.X i) 1 (polynomialCoordinate_X_degree i) k →ₗ[polynomialProjCoordinateRing K n i]
    localizedHomogeneousModulePiece polynomialIntegralGrading 𝒩
      (MvPolynomial.X i) 1 (polynomialCoordinate_X_degree i) k where
  toAddHom := (localizedHomogeneousModuleMap polynomialIntegralGrading ℳ 𝒩 f hf
    (MvPolynomial.X i) 1 (polynomialCoordinate_X_degree i) k).toAddHom
  map_smul' := polynomialCoordinateLocalizedPieceMap_smul K n ℳ i 𝒩 f hf k

/-- The true structural constants on a coordinate open are its native chart-ring constants. -/
theorem polynomialTwistedCoordinateConstants_native (c : K) :
    polynomialTwistedCoordinateConstants K n i c =
      homogeneousPolynomialBasicOpenAwayEquiv i
        (algebraMap K (polynomialProjCoordinateRing K n i) c) := by
  have htop : (polynomialProjCoordinateImmersion K n i).appTop ≫
      ((polynomialProjCoordinateImmersion K n i).appIso ⊤).inv ≫
      (polynomialProj K n).presheaf.map
        (eqToHom (polynomialProjCoordinateImmersion_image_top K n i).symm).op =
      (polynomialProj K n).presheaf.map (homOfLE le_top).op := by
    change (polynomialProjCoordinateImmersion K n i).appLE ⊤ ⊤ le_top ≫ _ ≫ _ = _
    erw [Scheme.Hom.appLE_appIso_inv_assoc]
    rw [← Functor.map_comp]
    congr 1
  have h := polynomialProjChartTopScalar_transport K n i
  have hc := congrArg (fun q => CommRingCat.ofHom
      (algebraMap K (polynomialProjCoordinateRing K n i)) ≫ q) h
  rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc] at hc
  change (Scheme.ΓSpecIso (.of K)).inv ≫
      (affineStructuralMap K (.of (polynomialProjCoordinateRing K n i))).appTop ≫
      ((polynomialProjCoordinateImmersion K n i).appIso ⊤).inv ≫
      (polynomialProj K n).presheaf.map _ = _ at hc
  rw [← polynomialProjCoordinateImmersion_structure K n i] at hc
  simp only [Scheme.Hom.comp_appTop, Category.assoc] at hc
  erw [htop] at hc
  exact congrArg (fun q => q.hom c) hc

/-- Every actual ordered dehomogenized variable reconstructs its actual homogeneous ratio. -/
theorem polynomialProjRatioMap_dehomVariable (j : Fin (n + 1)) :
    polynomialProjRatioMap K n i (polynomialProjDehomogenizationVariable K n i j) =
      polynomialProjCoordinateRatio K n i j := by
  refine Fin.succAboveCases i ?_ (fun a => ?_) j
  · rw [polynomialProjDehomogenizationVariable_self, map_one, polynomialProjCoordinateRatio_self]
  · simp [polynomialProjDehomogenizationVariable_succAbove, polynomialProjRatioMap]

/-- The true normalized polynomial scalar map is literal dehomogenization followed by actual ratios. -/
theorem polynomialTwistedCoordinatePolynomialMap_native :
    polynomialTwistedCoordinatePolynomialMap K n i =
      (homogeneousPolynomialBasicOpenAwayEquiv i).toRingHom.comp
        ((polynomialProjRatioMap K n i).comp (polynomialProjDehomogenization K n i)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [polynomialTwistedCoordinatePolynomialMap, MvPolynomial.eval₂Hom_C]
    change polynomialTwistedCoordinateConstants K n i c =
      homogeneousPolynomialBasicOpenAwayEquiv i
        (polynomialProjRatioMap K n i (polynomialProjDehomogenization K n i (MvPolynomial.C c)))
    erw [(polynomialProjDehomogenization K n i).commutes c,
      (polynomialProjRatioMap K n i).commutes c]
    exact polynomialTwistedCoordinateConstants_native K n i c
  · intro j
    simp only [polynomialTwistedCoordinatePolynomialMap, MvPolynomial.eval₂Hom_X']
    change homogeneousPolynomialBasicOpenAwayEquiv i (polynomialProjCoordinateRatio K n i j) =
      homogeneousPolynomialBasicOpenAwayEquiv i
        (polynomialProjRatioMap K n i (polynomialProjDehomogenization K n i (MvPolynomial.X j)))
    rw [polynomialProjDehomogenization, MvPolynomial.aeval_X, polynomialProjRatioMap_dehomVariable]

/-- Every genuine homogeneous polynomial acts by its literal native homogeneous fraction. -/
theorem polynomialTwistedCoordinatePolynomialMap_homogeneous (a : ℕ)
    (p : MvPolynomial (Fin (n + 1)) K)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K a) :
    polynomialTwistedCoordinatePolynomialMap K n i p =
      homogeneousPolynomialBasicOpenAwayEquiv i
        (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
          (MvPolynomial.isHomogeneous_X K i) a p (by simpa using hp)) := by
  rw [polynomialTwistedCoordinatePolynomialMap_native]
  change homogeneousPolynomialBasicOpenAwayEquiv i
    (polynomialProjRatioMap K n i (polynomialProjDehomogenization K n i p)) = _
  rw [← polynomialProjCoordinateDehomogenization_mk K n i a p hp,
    polynomialProjRatioMap_coordinateDehomogenization]

variable (M : (polynomialProj K n).Modules)

/-- Actual coordinate sections carry their native chart-ring action through the actual regular-section equivalence. -/
instance polynomialTwistedCoordinateSectionsNativeModule :
    Module (polynomialProjCoordinateRing K n i)
      (bundleSections M (polynomialProjCoordinateOpen K n i)) :=
  Module.compHom _ (homogeneousPolynomialBasicOpenAwayEquiv i).toRingHom

/-- Genuine normalized evaluation preserves the actual native chart-ring scalar multiplication. -/
theorem polynomialTwistedCoordinateDegreeZeroMap_native_smul
    (r : polynomialProjCoordinateRing K n i)
    (z : polynomialTwistedCoordinateDegreeZero K n M i) :
    polynomialTwistedCoordinateDegreeZeroMap K n M i (r • z) =
      r • polynomialTwistedCoordinateDegreeZeroMap K n M i z := by
  obtain ⟨a, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _
    (MvPolynomial.isHomogeneous_X K i) r
  obtain ⟨b, v, hv, he⟩ := z.property
  change polynomialTwistedLocalizedCoordinateEvaluation K n M i
    ((HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (MvPolynomial.isHomogeneous_X K i) a p hp).val • z.val) =
    homogeneousPolynomialBasicOpenAwayEquiv i
      (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X K i) a p hp) •
        polynomialTwistedLocalizedCoordinateEvaluation K n M i z.val
  erw [← he, HomogeneousLocalization.Away.val_mk, LocalizedModule.mk_smul_mk]
  change polynomialTwistedLocalizedCoordinateEvaluation K n M i
    (LocalizedModule.mk (p • v) (homogeneousPowerDenominator (MvPolynomial.X i) a *
      homogeneousPowerDenominator (MvPolynomial.X i) b)) = _
  erw [← homogeneousPowerDenominator_add]
  rw [polynomialTwistedLocalizedCoordinateEvaluation_mk,
    polynomialTwistedLocalizedCoordinateEvaluation_mk,
    polynomialTwistedCoordinateCoefficientSum_smul,
    polynomialTwistedCoordinatePolynomialMap_homogeneous K n i a p (by simpa using hp)]

/-- Native normalized evaluation is genuinely linear over the actual homogeneous coordinate ring. -/
def polynomialTwistedCoordinateNativeMap :
    polynomialTwistedCoordinateDegreeZero K n M i →ₗ[polynomialProjCoordinateRing K n i]
      bundleSections M (polynomialProjCoordinateOpen K n i) where
  toAddHom := (polynomialTwistedCoordinateDegreeZeroMap K n M i).toAddHom
  map_smul' := polynomialTwistedCoordinateDegreeZeroMap_native_smul K n i M

/-- True normalized degree-zero localization maps natively and linearly to actual affine-chart top sections. -/
def polynomialTwistedCoordinateChartMap :
    polynomialTwistedCoordinateDegreeZero K n M i →ₗ[polynomialProjCoordinateRing K n i]
      Γ(polynomialProjModuleChart M i, ⊤) where
  toFun z := (polynomialProjChartTopSectionsIso M i).inv
    (polynomialTwistedCoordinateNativeMap K n i M z)
  map_add' x y := by simp
  map_smul' r z := by
    apply (ConcreteCategory.bijective_of_isIso (polynomialProjChartTopSectionsIso M i).hom).injective
    rw [polynomialProjChartTopSectionsIso_smul]
    simp only [Iso.inv_hom_id_apply, map_smul]
    rfl

/-- Actual quasicoherence and true extension identify the native localized module with the actual affine chart module. -/
def polynomialTwistedCoordinateChartEquiv
    [∀ j : Fin (n + 1), (polynomialProjModuleChart M j).IsQuasicoherent] :
    polynomialTwistedCoordinateDegreeZero K n M i ≃ₗ[polynomialProjCoordinateRing K n i]
      Γ(polynomialProjModuleChart M i, ⊤) :=
  LinearEquiv.ofBijective (polynomialTwistedCoordinateChartMap K n i M) (by
    change Function.Bijective (fun z => (polynomialProjChartTopSectionsIso M i).inv
      (polynomialTwistedCoordinateDegreeZeroMap K n M i z))
    exact (ConcreteCategory.bijective_of_isIso (polynomialProjChartTopSectionsIso M i).inv).comp
      ⟨polynomialTwistedCoordinateDegreeZeroMap_injective K n M i,
        polynomialTwistedCoordinateDegreeZeroMap_surjective K n M i⟩)

/-- An actual homogeneous twisted-section fraction has exactly its actual normalized affine-chart coefficient. -/
theorem polynomialTwistedCoordinateChartMap_fraction (d : ℕ)
    (t : bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M d) :
    polynomialTwistedCoordinateChartMap K n i M
      ⟨LocalizedModule.mk ((polynomialProjTwistingLine K n).ofTwistedSection M d t)
        (homogeneousPowerDenominator (MvPolynomial.X i) d),
        d, (polynomialProjTwistingLine K n).ofTwistedSection M d t,
        (by simpa using polynomialProjTwistedSectionPiece_ofTwistedSection K n M d t), rfl⟩ =
    (polynomialProjChartTopSectionsIso M i).inv
      (atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M d i t) :=
  congrArg (polynomialProjChartTopSectionsIso M i).inv
    (polynomialTwistedCoordinateDegreeZeroMap_fraction K n M i d t)


end
end SGPT.Foundations.Schemes
