import SGPT.Foundations.Schemes.PolynomialTwistedCoordinateScalars
import SGPT.Foundations.Schemes.SchemeSubsetCechSections
import SGPT.Foundations.Schemes.PolynomialProjectiveTwistingTransition

/-! # Actual affine chart models of nonempty coordinate intersections

Finite coordinate intersections are literal principal ratio opens in each
selected native chart. Section comparisons and scalar maps are the true
restriction and open-immersion maps of the actual scheme module.
-/

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual finite intersection of actual projective coordinate opens. -/
abbrev polynomialProjSubsetCoordinateOpen (S : Finset (Fin (n + 1))) :
    (polynomialProj K n).Opens :=
  actualSchemeSubsetOpen (polynomialProjCoordinateOpen K n) S

/-- The literal product of actual coordinate ratios in the actual chart ring. -/
def polynomialProjSubsetRatioProduct (i : Fin (n + 1)) (S : Finset (Fin (n + 1))) :
    polynomialProjCoordinateRing K n i :=
  ∏ j ∈ S, polynomialProjCoordinateRatio K n i j

/-- The actual intersection lies in every genuinely selected coordinate chart. -/
theorem polynomialProjSubsetCoordinateOpen_le (i : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (hi : i ∈ S) :
    polynomialProjSubsetCoordinateOpen K n S ≤ polynomialProjCoordinateOpen K n i :=
  Finset.inf_le hi

/-- Every true coordinate intersection pulls back to the literal principal ratio-product open. -/
theorem polynomialProjCoordinateImmersion_preimage_subsetOpen (i : Fin (n + 1))
    (S : Finset (Fin (n + 1))) :
    polynomialProjCoordinateImmersion K n i ⁻¹ᵁ polynomialProjSubsetCoordinateOpen K n S =
      PrimeSpectrum.basicOpen (polynomialProjSubsetRatioProduct K n i S) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [polynomialProjSubsetCoordinateOpen, actualSchemeSubsetOpen,
      polynomialProjSubsetRatioProduct, PrimeSpectrum.basicOpen_one]
  | @insert j S hj hS =>
      simp only [polynomialProjSubsetCoordinateOpen, actualSchemeSubsetOpen,
        Finset.inf_insert, polynomialProjSubsetRatioProduct, Finset.prod_insert hj,
        PrimeSpectrum.basicOpen_mul]
      change (polynomialProjCoordinateImmersion K n i ⁻¹ᵁ polynomialProjCoordinateOpen K n j) ⊓
        (polynomialProjCoordinateImmersion K n i ⁻¹ᵁ polynomialProjSubsetCoordinateOpen K n S) = _
      rw [polynomialProjCoordinateImmersion_preimage_coordinateOpen, hS]
      rfl

/-- A selected chart sends its actual principal ratio-product open onto the actual full intersection. -/
theorem polynomialProjCoordinateImmersion_image_subsetOpen (i : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (hi : i ∈ S) :
    polynomialProjCoordinateImmersion K n i ''ᵁ
      PrimeSpectrum.basicOpen (polynomialProjSubsetRatioProduct K n i S) =
        polynomialProjSubsetCoordinateOpen K n S := by
  rw [← polynomialProjCoordinateImmersion_preimage_subsetOpen,
    Scheme.Hom.image_preimage_eq_opensRange_inf]
  have hrange : (polynomialProjCoordinateImmersion K n i).opensRange =
      polynomialProjCoordinateOpen K n i := by
    rw [← Scheme.Hom.image_top_eq_opensRange, polynomialProjCoordinateImmersion_image_top]
  rw [hrange]
  exact inf_eq_right.mpr (polynomialProjSubsetCoordinateOpen_le K n i S hi)

variable (M : (polynomialProj K n).Modules) (i : Fin (n + 1))
  (S : Finset (Fin (n + 1))) (hi : i ∈ S)

/-- Actual affine ratio-product sections identify with actual sections on the true coordinate intersection. -/
def polynomialProjChartSubsetSectionsIso :
    Γ(polynomialProjModuleChart M i,
      PrimeSpectrum.basicOpen (polynomialProjSubsetRatioProduct K n i S)) ≅
        Γ(M, polynomialProjSubsetCoordinateOpen K n S) :=
  M.restrictAppIso (polynomialProjCoordinateImmersion K n i) _ ≪≫
    M.presheaf.mapIso (eqToIso (polynomialProjCoordinateImmersion_image_subsetOpen K n i S hi).symm).op

/-- The genuine affine restriction to a ratio-product principal open. -/
def polynomialProjChartSubsetRestriction :
    Γ(polynomialProjModuleChart M i, ⊤) →ₗ[polynomialProjCoordinateRing K n i]
      Γ(polynomialProjModuleChart M i,
        PrimeSpectrum.basicOpen (polynomialProjSubsetRatioProduct K n i S)) :=
  affineSectionRestriction (polynomialProjModuleChart M i) (polynomialProjSubsetRatioProduct K n i S)

/-- Native affine quasicoherence makes the true intersection restriction an actual localization. -/
theorem polynomialProjChartSubsetRestriction_isLocalized
    [(polynomialProjModuleChart M i).IsQuasicoherent] :
    IsLocalizedModule.Away (polynomialProjSubsetRatioProduct K n i S)
      (polynomialProjChartSubsetRestriction K n M i S) :=
  affineSectionRestriction_isLocalized (polynomialProjModuleChart M i)
    (polynomialProjSubsetRatioProduct K n i S)

/-- The native principal restriction is exactly true sheaf restriction to the actual finite intersection. -/
theorem polynomialProjChartSubsetRestriction_actual
    (s : Γ(polynomialProjModuleChart M i, ⊤)) :
    (polynomialProjChartSubsetSectionsIso K n M i S hi).hom
      (polynomialProjChartSubsetRestriction K n M i S s) =
    M.presheaf.map (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi)).op
      ((polynomialProjChartTopSectionsIso M i).hom s) := by
  change M.presheaf.map
    (eqToHom (polynomialProjCoordinateImmersion_image_subsetOpen K n i S hi).symm).op
    (M.presheaf.map (homOfLE ((polynomialProjCoordinateImmersion K n i).image_mono le_top)).op s) =
    M.presheaf.map (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi)).op
      (M.presheaf.map (eqToHom (polynomialProjCoordinateImmersion_image_top K n i).symm).op s)
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp]
  congr 2

/-- Actual native chart scalars on the intersection are literal restrictions of actual regular homogeneous fractions. -/
theorem polynomialProjChartSubsetScalar_transport :
    affineCoordinateMap (.of (polynomialProjCoordinateRing K n i))
        (.op (PrimeSpectrum.basicOpen (polynomialProjSubsetRatioProduct K n i S))) ≫
      ((polynomialProjCoordinateImmersion K n i).appIso _).inv ≫
      (polynomialProj K n).presheaf.map
        (eqToHom (polynomialProjCoordinateImmersion_image_subsetOpen K n i S hi).symm).op =
    (Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X K i) (by decide)).hom ≫
      (polynomialProj K n).presheaf.map
        (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi)).op := by
  unfold affineCoordinateMap
  rw [Category.assoc, Scheme.Hom.appIso_inv_naturality_assoc]
  rw [← polynomialProjChartTopScalar_transport K n i]
  simp only [Category.assoc]
  congr 2

/-- True intersection sections retain native scalar multiplication by actual restricted homogeneous chart fractions. -/
theorem polynomialProjChartSubsetSectionsIso_smul
    (r : polynomialProjCoordinateRing K n i)
    (s : Γ(polynomialProjModuleChart M i,
      PrimeSpectrum.basicOpen (polynomialProjSubsetRatioProduct K n i S))) :
    (polynomialProjChartSubsetSectionsIso K n M i S hi).hom (r • s) =
      (polynomialProj K n).presheaf.map
        (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi)).op
        (homogeneousPolynomialBasicOpenAwayEquiv i r) •
          (polynomialProjChartSubsetSectionsIso K n M i S hi).hom s := by
  have hs : r • s = affineCoordinateMap (.of (polynomialProjCoordinateRing K n i))
      (.op (PrimeSpectrum.basicOpen (polynomialProjSubsetRatioProduct K n i S))) r • s := rfl
  change M.presheaf.map
    (eqToHom (polynomialProjCoordinateImmersion_image_subsetOpen K n i S hi).symm).op
    ((M.restrictAppIso (polynomialProjCoordinateImmersion K n i) _).hom (r • s)) = _
  rw [hs, Scheme.Modules.smul_restrictAppIso_hom_apply, Scheme.Modules.map_smul]
  congr 1
  exact congr($(polynomialProjChartSubsetScalar_transport K n i S hi).hom r)

/-- Literal native ratio-product sections carry their actual restricted chart-ring action. -/
def polynomialProjSubsetRegularMap :
    polynomialProjCoordinateRing K n i →+* Γ(polynomialProj K n, polynomialProjSubsetCoordinateOpen K n S) :=
  ((polynomialProj K n).presheaf.map
    (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi)).op).hom.comp
      (homogeneousPolynomialBasicOpenAwayEquiv i).toRingHom

/-- A genuine selected coordinate ratio is invertible on the actual full intersection. -/
theorem polynomialProjSubsetRegularRatio_isUnit (j : Fin (n + 1)) (hj : j ∈ S) :
    IsUnit (polynomialProjSubsetRegularMap K n i S hi (polynomialProjCoordinateRatio K n i j)) := by
  let l : polynomialProjSubsetCoordinateOpen K n S ⟶ polynomialProjCoordinateOpen K n j :=
    homOfLE (polynomialProjSubsetCoordinateOpen_le K n j S hj)
  let r : polynomialProjSubsetCoordinateOpen K n S ⟶ polynomialProjCoordinateOpen K n i :=
    homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi)
  have h := polynomialProjTwistingFrame_transition_ratio K n j i 1 l r
  rw [pow_one] at h
  change IsUnit ((polynomialProj K n).presheaf.map r.op
    (homogeneousPolynomialBasicOpenAwayEquiv i (polynomialProjCoordinateRatio K n i j)))
  erw [polynomialProjCoordinateRegularRatio, ← polynomialProjCoordinateSectionMap_equiv K n i] at h
  exact h ▸ (localBundleFrameTransition _ _ l r).isUnit

/-- The genuine ratio product is invertible on its actual intersection. -/
theorem polynomialProjSubsetRegularRatioProduct_isUnit :
    IsUnit (polynomialProjSubsetRegularMap K n i S hi (polynomialProjSubsetRatioProduct K n i S)) := by
  rw [polynomialProjSubsetRatioProduct, map_prod]
  let f := fun j => polynomialProjSubsetRegularMap K n i S hi (polynomialProjCoordinateRatio K n i j)
  have h : ∀ T : Finset (Fin (n + 1)), (∀ j ∈ T, IsUnit (f j)) → IsUnit (∏ j ∈ T, f j) := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; simp
    | @insert j T hj hT =>
        intro hu
        rw [Finset.prod_insert hj]
        exact (hu j (Finset.mem_insert_self _ _)).mul
          (hT (fun k hk => hu k (Finset.mem_insert_of_mem hk)))
  exact h S (fun j hj => polynomialProjSubsetRegularRatio_isUnit K n i S hi j hj)

/-- The actual finite-intersection constants are the actual restricted structural constants. -/
def polynomialProjSubsetConstants :
    K →+* Γ(polynomialProj K n, polynomialProjSubsetCoordinateOpen K n S) :=
  ((polynomialProj K n).presheaf.map (homOfLE le_top).op).hom.comp
    (schemeConstantMap (polynomialProjStructureMap K n))

/-- True native chart constants restrict to the true structural constants of the actual intersection. -/
theorem polynomialProjSubsetRegularMap_constants (c : K) :
    polynomialProjSubsetRegularMap K n i S hi
      (algebraMap K (polynomialProjCoordinateRing K n i) c) =
        polynomialProjSubsetConstants K n S c := by
  change (polynomialProj K n).presheaf.map
    (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi)).op
    (homogeneousPolynomialBasicOpenAwayEquiv i (algebraMap K (polynomialProjCoordinateRing K n i) c)) = _
  rw [← polynomialTwistedCoordinateConstants_native]
  change (polynomialProj K n).presheaf.map _
    ((polynomialProj K n).presheaf.map _ (schemeConstantMap (polynomialProjStructureMap K n) c)) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The identity-pullback structural morphism is the true polynomial projective structural morphism. -/
theorem polynomialProj_identityPullback_structure :
    actualPolynomialProjectivePullbackStructureMap (𝟙 (polynomialProj K n)) =
      polynomialProjStructureMap K n := by
  simp [actualPolynomialProjectivePullbackStructureMap, polynomialProjStructureMap]

/-- The true identity-pullback section diagram uses the same genuine structural field constants. -/
theorem polynomialProj_identityPullback_constants :
    schemeGlobalConstants (actualPolynomialProjectivePullbackStructureMap (𝟙 (polynomialProj K n))) =
      schemeConstantMap (polynomialProjStructureMap K n) := by
  rw [polynomialProj_identityPullback_structure]
  rfl

end
end SGPT.Foundations.Schemes
