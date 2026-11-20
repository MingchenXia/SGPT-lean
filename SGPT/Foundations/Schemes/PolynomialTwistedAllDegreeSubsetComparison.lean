import SGPT.Foundations.Schemes.PolynomialHomogeneousSubsetDegreeShift
import SGPT.Foundations.Schemes.PolynomialTwistedFiniteSpanSubsetComparison

/-! # One genuine homogeneous span represents every nonnegative tensor twist

All degrees use the same true chart-generated finite span. Actual normalized
evaluation and the inverse tensor-power frame produce the actual sections.
-/

open CategoryTheory Opposite AlgebraicGeometry
open scoped DirectSum

namespace SGPT.Foundations.Schemes
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable (K : Type) [Field K] (n : ℕ) (M : (polynomialProj K n).Modules)
attribute [local instance] MvPolynomial.gradedAlgebra
variable (i : Fin (n + 1)) (S : Finset (Fin (n + 1))) (hi : i ∈ S)

/-- The genuine tensor twist by the actual projective O(1) line. -/
abbrev polynomialProjModuleTensorTwist (m : ℕ) : (polynomialProj K n).Modules :=
  bundleTensor (bundleTensorPower (polynomialProjTwistingLine K n).sheaf m) M

/-- The actual tensor-power frame coefficient map retains the structural field action. -/
def polynomialTwistedSubsetTensorCoefficients (m : ℕ) :
    (actualSchemeModuleBaseSubsetDiagram (polynomialProjModuleTensorTwist K n M m)
      (polynomialProjCoordinateOpen K n) (schemeConstantMap (polynomialProjStructureMap K n))).obj S →ₗ[K]
    (actualSchemeModuleBaseSubsetDiagram M (polynomialProjCoordinateOpen K n)
      (schemeConstantMap (polynomialProjStructureMap K n))).obj S where
  toFun := (((polynomialProjTwistingLine K n).atlas.frame i).tensorPower m).tensorModuleCoefficients M
    (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi))
  map_add' x y := by simp
  map_smul' c x := by
    change (((polynomialProjTwistingLine K n).atlas.frame i).tensorPower m).tensorModuleCoefficients M
      (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi))
      (polynomialProjSubsetConstants K n S c •
        (show bundleSections (polynomialProjModuleTensorTwist K n M m)
          (polynomialProjSubsetCoordinateOpen K n S) from x)) =
        polynomialProjSubsetConstants K n S c •
          (((polynomialProjTwistingLine K n).atlas.frame i).tensorPower m).tensorModuleCoefficients M
            (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi)) x
    exact LinearEquiv.map_smul _ _ _

/-- Actual inverse tensor frames give genuine structurally linear section equivalences. -/
def polynomialTwistedSubsetTensorCoefficientsEquiv (m : ℕ) :
    (actualSchemeModuleBaseSubsetDiagram (polynomialProjModuleTensorTwist K n M m)
      (polynomialProjCoordinateOpen K n) (schemeConstantMap (polynomialProjStructureMap K n))).obj S ≃ₗ[K]
    (actualSchemeModuleBaseSubsetDiagram M (polynomialProjCoordinateOpen K n)
      (schemeConstantMap (polynomialProjStructureMap K n))).obj S :=
  LinearEquiv.ofBijective (polynomialTwistedSubsetTensorCoefficients K n M i S hi m)
    ((((polynomialProjTwistingLine K n).atlas.frame i).tensorPower m).tensorModuleCoefficients M
      (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi))).bijective

/-- The literal degree-m product localization of the actual Gamma-star module. -/
abbrev polynomialTwistedSubsetDegree (m : ℕ) :=
  polynomialHomogeneousSubsetPiece K n (polynomialProjTwistedSectionPiece K n M) S (m : ℤ)

/-- Actual localized evaluation in any nonnegative degree retains structural field scalars. -/
def polynomialTwistedSubsetDegreeCoefficientMap (m : ℕ) :
    polynomialTwistedSubsetDegree K n M S m →ₗ[K]
      (actualSchemeModuleBaseSubsetDiagram M (polynomialProjCoordinateOpen K n)
        (schemeConstantMap (polynomialProjStructureMap K n))).obj S where
  toFun z := polynomialTwistedSubsetLocalizedEvaluation K n M i S hi z.val
  map_add' x y := by simp
  map_smul' c z := by
    change polynomialTwistedSubsetLocalizedEvaluation K n M i S hi (c • z.val) =
      polynomialProjSubsetConstants K n S c • polynomialTwistedSubsetLocalizedEvaluation K n M i S hi z.val
    rw [← IsScalarTower.algebraMap_smul (R := K) (MvPolynomial (Fin (n + 1)) K) c z.val,
      LinearMap.map_smul]
    change polynomialTwistedSubsetPolynomialMap K n i S hi (MvPolynomial.C c) •
      polynomialTwistedSubsetLocalizedEvaluation K n M i S hi z.val =
        polynomialProjSubsetConstants K n S c • polynomialTwistedSubsetLocalizedEvaluation K n M i S hi z.val
    rw [polynomialTwistedSubsetPolynomialMap_C]

/-- Genuine all-degree evaluation uses the inverse actual tensor-power frame. -/
def polynomialTwistedSubsetAllDegreeMap (m : ℕ) :
    polynomialTwistedSubsetDegree K n M S m →ₗ[K]
      (actualSchemeModuleBaseSubsetDiagram (polynomialProjModuleTensorTwist K n M m)
        (polynomialProjCoordinateOpen K n) (schemeConstantMap (polynomialProjStructureMap K n))).obj S :=
  (polynomialTwistedSubsetTensorCoefficientsEquiv K n M i S hi m).symm.toLinearMap.comp
    (polynomialTwistedSubsetDegreeCoefficientMap K n M i S hi m)

/-- Every true degree-m fraction has an actual global numerator in its literal nonnegative degree. -/
theorem polynomialTwistedSubsetDegree_fraction_exists (m : ℕ)
    (z : polynomialTwistedSubsetDegree K n M S m) :
    ∃ (q : ℕ) (t : bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M (m + q * S.card)),
      LocalizedModule.mk ((polynomialProjTwistingLine K n).ofTwistedSection M (m + q * S.card) t)
        (homogeneousPowerDenominator (polynomialHomogeneousSubsetProduct K n S) q) = z.val := by
  obtain ⟨q, x, hx, he⟩ := z.property
  have hx' : x ∈ polynomialProjTwistedSectionPiece K n M ((m + q * S.card : ℕ) : ℤ) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using hx
  let y : ⨁ d : ℕ, bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M d := x
  have hs : x = (polynomialProjTwistingLine K n).ofTwistedSection M (m + q * S.card) (y (m + q * S.card)) :=
    nonnegativeDirectSumPiece_eq_single K
      (bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M) (m + q * S.card) ⟨y, hx'⟩
  exact ⟨q, y (m + q * S.card), hs ▸ he⟩

/-- The true all-degree coefficient map obeys the literal denominator-clearing formula. -/
theorem polynomialTwistedSubsetDegreeCoefficientMap_cleared (m q : ℕ)
    (t : bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M (m + q * S.card))
    (z : polynomialTwistedSubsetDegree K n M S m)
    (ht : LocalizedModule.mk ((polynomialProjTwistingLine K n).ofTwistedSection M (m + q * S.card) t)
      (homogeneousPowerDenominator (polynomialHomogeneousSubsetProduct K n S) q) = z.val) :
    (polynomialProjSubsetRegularMap K n i S hi (polynomialProjSubsetRatioProduct K n i S)) ^ q •
      (show bundleSections M (polynomialProjSubsetCoordinateOpen K n S) from
        polynomialTwistedSubsetDegreeCoefficientMap K n M i S hi m z) =
    M.presheaf.map (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi)).op
      (atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M (m + q * S.card) i t) := by
  change _ • polynomialTwistedSubsetLocalizedEvaluation K n M i S hi z.val = _
  erw [← ht, polynomialTwistedSubsetLocalizedEvaluation_mk,
    polynomialTwistedCoordinateCoefficientSum_of]

/-- Actual all-degree normalized coefficients change by exactly the tensor-power transition. -/
theorem polynomialTwistedSubsetDegreeCoefficientMap_transition (j : Fin (n + 1)) (hj : j ∈ S)
    (m : ℕ) (z : polynomialTwistedSubsetDegree K n M S m) :
    (show bundleSections M (polynomialProjSubsetCoordinateOpen K n S) from
      polynomialTwistedSubsetDegreeCoefficientMap K n M j S hj m z) =
    (polynomialTwistedSubsetTransitionUnit K n i S hi j hj :
      Γ(polynomialProj K n, polynomialProjSubsetCoordinateOpen K n S)) ^ m •
      (show bundleSections M (polynomialProjSubsetCoordinateOpen K n S) from
        polynomialTwistedSubsetDegreeCoefficientMap K n M i S hi m z) := by
  obtain ⟨q, t, ht⟩ := polynomialTwistedSubsetDegree_fraction_exists K n M S m z
  apply ((polynomialProjSubsetRegularRatioProduct_isUnit K n j S hj).pow q).smul_bijective.injective
  dsimp only
  rw [polynomialTwistedSubsetDegreeCoefficientMap_cleared K n M j S hj m q t z ht,
    polynomialTwistedSubsetCoefficient_transition K n M i S hi j hj]
  rw [polynomialTwistedSubsetRatioProduct_transition K n i S hi j hj, mul_pow,
    ← pow_mul, Nat.mul_comm S.card q, mul_smul]
  rw [smul_comm
    ((polynomialProjSubsetRegularMap K n i S hi (polynomialProjSubsetRatioProduct K n i S)) ^ q)
    ((polynomialTwistedSubsetTransitionUnit K n i S hi j hj :
      Γ(polynomialProj K n, polynomialProjSubsetCoordinateOpen K n S)) ^ m),
    polynomialTwistedSubsetDegreeCoefficientMap_cleared K n M i S hi m q t z ht,
    pow_add, mul_smul, smul_comm]

/-- Applying the genuine tensor-power coefficient map recovers the actual localized coefficient. -/
theorem polynomialTwistedSubsetAllDegreeMap_coefficients (m : ℕ)
    (z : polynomialTwistedSubsetDegree K n M S m) :
    polynomialTwistedSubsetTensorCoefficientsEquiv K n M i S hi m
      (polynomialTwistedSubsetAllDegreeMap K n M i S hi m z) =
    polynomialTwistedSubsetDegreeCoefficientMap K n M i S hi m z :=
  LinearEquiv.apply_symm_apply _ _

/-- Actual tensor-power transition laws make all-degree section evaluation independent of the selected coordinate. -/
theorem polynomialTwistedSubsetAllDegreeMap_independent (j : Fin (n + 1)) (hj : j ∈ S)
    (m : ℕ) (z : polynomialTwistedSubsetDegree K n M S m) :
    polynomialTwistedSubsetAllDegreeMap K n M i S hi m z =
      polynomialTwistedSubsetAllDegreeMap K n M j S hj m z := by
  apply (polynomialTwistedSubsetTensorCoefficientsEquiv K n M j S hj m).injective
  have h := LocalBundleFrame.tensorModuleCoefficients_transition
    (((polynomialProjTwistingLine K n).atlas.frame i).tensorPower m)
    (((polynomialProjTwistingLine K n).atlas.frame j).tensorPower m) M
    (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi))
    (homOfLE (polynomialProjSubsetCoordinateOpen_le K n j S hj))
    (polynomialTwistedSubsetAllDegreeMap K n M i S hi m z)
  rw [localBundleFrameTransition_tensorPower, Units.val_pow_eq_pow_val] at h
  change (show bundleSections M (polynomialProjSubsetCoordinateOpen K n S) from
    polynomialTwistedSubsetTensorCoefficientsEquiv K n M j S hj m
      (polynomialTwistedSubsetAllDegreeMap K n M i S hi m z)) =
    (polynomialTwistedSubsetTransitionUnit K n i S hi j hj :
      Γ(polynomialProj K n, polynomialProjSubsetCoordinateOpen K n S)) ^ m •
      (show bundleSections M (polynomialProjSubsetCoordinateOpen K n S) from
        polynomialTwistedSubsetTensorCoefficientsEquiv K n M i S hi m
          (polynomialTwistedSubsetAllDegreeMap K n M i S hi m z)) at h
  rw [polynomialTwistedSubsetAllDegreeMap_coefficients] at h
  rw [polynomialTwistedSubsetAllDegreeMap_coefficients]
  exact h.trans (polynomialTwistedSubsetDegreeCoefficientMap_transition K n M i S hi j hj m z).symm

/-- The full native localization restriction identity remains valid on every actual degree. -/
theorem polynomialTwistedSubsetDegreeCoefficientMap_restrict
    (T : Finset (Fin (n + 1))) (hST : S ⊆ T) (m : ℕ)
    (z : polynomialTwistedSubsetDegree K n M S m) :
    polynomialTwistedSubsetDegreeCoefficientMap K n M i T (hST hi) m
      (homogeneousCoordinateSubsetRestriction
        (polynomialIntegralGrading (K := K) (I := Fin (n + 1)))
        (polynomialProjTwistedSectionPiece K n M)
        (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K))
        polynomialCoordinate_X_degree hST (m : ℤ) z) =
    (actualSchemeModuleBaseSubsetDiagram M (polynomialProjCoordinateOpen K n)
      (schemeConstantMap (polynomialProjStructureMap K n))).map (homOfLE hST)
        (polynomialTwistedSubsetDegreeCoefficientMap K n M i S hi m z) :=
  LinearMap.congr_fun (polynomialTwistedSubsetLocalizedEvaluation_restrict K n M i S T hi hST) z.val

/-- The inverse actual tensor frame and true homogeneous restriction give the genuine all-degree naturality square. -/
theorem polynomialTwistedSubsetAllDegreeMap_restrict
    (T : Finset (Fin (n + 1))) (hST : S ⊆ T) (m : ℕ)
    (z : polynomialTwistedSubsetDegree K n M S m) :
    polynomialTwistedSubsetAllDegreeMap K n M i T (hST hi) m
      (homogeneousCoordinateSubsetRestriction
        (polynomialIntegralGrading (K := K) (I := Fin (n + 1)))
        (polynomialProjTwistedSectionPiece K n M)
        (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K))
        polynomialCoordinate_X_degree hST (m : ℤ) z) =
    (actualSchemeModuleBaseSubsetDiagram (polynomialProjModuleTensorTwist K n M m)
      (polynomialProjCoordinateOpen K n) (schemeConstantMap (polynomialProjStructureMap K n))).map (homOfLE hST)
        (polynomialTwistedSubsetAllDegreeMap K n M i S hi m z) := by
  apply (polynomialTwistedSubsetTensorCoefficientsEquiv K n M i T (hST hi) m).injective
  rw [polynomialTwistedSubsetAllDegreeMap_coefficients,
    polynomialTwistedSubsetDegreeCoefficientMap_restrict]
  have h := LocalBundleFrame.tensorModuleCoefficients_restrict
    (((polynomialProjTwistingLine K n).atlas.frame i).tensorPower m) M
    (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi))
    (homOfLE (actualSchemeSubsetOpen_antitone (polynomialProjCoordinateOpen K n) hST))
    (polynomialTwistedSubsetAllDegreeMap K n M i S hi m z)
  change polynomialTwistedSubsetTensorCoefficientsEquiv K n M i T (hST hi) m
    ((actualSchemeModuleBaseSubsetDiagram (polynomialProjModuleTensorTwist K n M m)
      (polynomialProjCoordinateOpen K n) (schemeConstantMap (polynomialProjStructureMap K n))).map
        (homOfLE hST) (polynomialTwistedSubsetAllDegreeMap K n M i S hi m z)) =
      (actualSchemeModuleBaseSubsetDiagram M (polynomialProjCoordinateOpen K n)
        (schemeConstantMap (polynomialProjStructureMap K n))).map (homOfLE hST)
          (polynomialTwistedSubsetTensorCoefficientsEquiv K n M i S hi m
            (polynomialTwistedSubsetAllDegreeMap K n M i S hi m z)) at h
  rw [polynomialTwistedSubsetAllDegreeMap_coefficients] at h
  exact h.symm

/-- Actual frame-independent evaluation defines a genuine natural map in every nonnegative degree. -/
def polynomialTwistedAllDegreeNonemptySubsetEvaluation (m : ℕ) :
    nonemptySubsetDiagram (homogeneousCoordinateSubsetDiagram
      (polynomialIntegralGrading (K := K) (I := Fin (n + 1)))
      (polynomialProjTwistedSectionPiece K n M)
      (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) polynomialCoordinate_X_degree (m : ℤ)) ⟶
    nonemptySubsetDiagram (actualSchemeModuleBaseSubsetDiagram (polynomialProjModuleTensorTwist K n M m)
      (polynomialProjCoordinateOpen K n) (schemeConstantMap (polynomialProjStructureMap K n))) where
  app S := @ModuleCat.ofHom K _ (polynomialTwistedSubsetDegree K n M S.val m)
    ((actualSchemeModuleBaseSubsetDiagram (polynomialProjModuleTensorTwist K n M m)
      (polynomialProjCoordinateOpen K n) (schemeConstantMap (polynomialProjStructureMap K n))).obj S.val) _ _ _ _
    (polynomialTwistedSubsetAllDegreeMap K n M S.property.choose S.val S.property.choose_spec m)
  naturality {S T} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change polynomialTwistedSubsetAllDegreeMap K n M T.property.choose T.val T.property.choose_spec m
      (homogeneousCoordinateSubsetRestriction
        (polynomialIntegralGrading (K := K) (I := Fin (n + 1)))
        (polynomialProjTwistedSectionPiece K n M)
        (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K))
        polynomialCoordinate_X_degree (leOfHom f) (m : ℤ) z) =
      (actualSchemeModuleBaseSubsetDiagram (polynomialProjModuleTensorTwist K n M m)
        (polynomialProjCoordinateOpen K n) (schemeConstantMap (polynomialProjStructureMap K n))).map
          (homOfLE (leOfHom f))
          (polynomialTwistedSubsetAllDegreeMap K n M S.property.choose S.val S.property.choose_spec m z)
    rw [polynomialTwistedSubsetAllDegreeMap_independent K n M T.property.choose T.val
      T.property.choose_spec S.property.choose ((leOfHom f) S.property.choose_spec)]
    exact polynomialTwistedSubsetAllDegreeMap_restrict K n M S.property.choose S.val
      S.property.choose_spec T.val (leOfHom f) m z

/-- The selected true coordinate has normalized value one on the actual intersection. -/
theorem polynomialTwistedSubsetPolynomialMap_self :
    polynomialTwistedSubsetPolynomialMap K n i S hi (MvPolynomial.X i) = 1 := by
  change (polynomialProj K n).presheaf.map
    (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi)).op
    (polynomialTwistedCoordinatePolynomialMap K n i (MvPolynomial.X i)) = 1
  rw [polynomialTwistedCoordinatePolynomialMap_self]
  exact map_one _

section ActualFamily
variable {A : Type} [Fintype A] [DecidableEq A] (d : A → ℕ)
  (t : ∀ a, bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M (d a))

/-- The same actual finite homogeneous span evaluates in every nonnegative degree. -/
def polynomialTwistedFiniteSpanAllDegreeSubsetMap (m : ℕ) :
    polynomialHomogeneousSubsetPiece K n (polynomialProjTwistedFiniteSpanPiece K n M d t) S (m : ℤ) →ₗ[K]
      (actualSchemeModuleBaseSubsetDiagram (polynomialProjModuleTensorTwist K n M m)
        (polynomialProjCoordinateOpen K n) (schemeConstantMap (polynomialProjStructureMap K n))).obj S :=
  (polynomialTwistedSubsetAllDegreeMap K n M i S hi m).comp
    ((polynomialTwistedFiniteSpanSubsetInclusion K n M d t (m : ℤ)).app S).hom

omit [Fintype A] [DecidableEq A] in
/-- Actual coordinate degree multiplication evaluates identically in its actual normalized frame. -/
theorem polynomialTwistedFiniteSpanAllDegreeSubsetMap_multiply (m : ℕ)
    (z : polynomialHomogeneousSubsetPiece K n (polynomialProjTwistedFiniteSpanPiece K n M d t) S 0) :
    polynomialTwistedSubsetTensorCoefficientsEquiv K n M i S hi m
      (polynomialTwistedFiniteSpanAllDegreeSubsetMap K n M i S hi d t m
        (polynomialHomogeneousSubsetDegreeMultiply K n (polynomialProjTwistedFiniteSpanPiece K n M d t) i S m z)) =
      polynomialTwistedFiniteSpanSubsetMap K n M d t i S hi z := by
  change polynomialTwistedSubsetTensorCoefficientsEquiv K n M i S hi m
    (polynomialTwistedSubsetAllDegreeMap K n M i S hi m _) = _
  rw [polynomialTwistedSubsetAllDegreeMap_coefficients]
  change polynomialTwistedSubsetLocalizedEvaluation K n M i S hi
    (actualLocalizedModuleMap (Submonoid.powers (polynomialHomogeneousSubsetProduct K n S))
      (polynomialProjTwistedFiniteSpan K n M d t).subtype
      ((MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) ^ m • z.val)) =
    polynomialTwistedSubsetLocalizedEvaluation K n M i S hi
      (actualLocalizedModuleMap (Submonoid.powers (polynomialHomogeneousSubsetProduct K n S))
        (polynomialProjTwistedFiniteSpan K n M d t).subtype z.val)
  rw [LinearMap.map_smul, LinearMap.map_smul]
  change polynomialTwistedSubsetPolynomialMap K n i S hi ((MvPolynomial.X i) ^ m) •
    polynomialTwistedSubsetLocalizedEvaluation K n M i S hi
      (actualLocalizedModuleMap (Submonoid.powers (polynomialHomogeneousSubsetProduct K n S))
        (polynomialProjTwistedFiniteSpan K n M d t).subtype z.val) = _
  rw [map_pow, polynomialTwistedSubsetPolynomialMap_self, one_pow, one_smul]

omit [Fintype A] [DecidableEq A] in
/-- Genuine degree-zero chart generation gives bijective evaluation in every nonnegative degree of the same span. -/
theorem polynomialTwistedFiniteSpanAllDegreeSubsetMap_bijective
    [∀ j, (polynomialProjModuleChart M j).IsQuasicoherent] (m : ℕ)
    (hgen : Submodule.span (polynomialProjCoordinateRing K n i)
      (Set.range (fun a => (polynomialProjChartTopSectionsIso M i).inv
        (atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M (d a) i (t a)))) = ⊤) :
    Function.Bijective (polynomialTwistedFiniteSpanAllDegreeSubsetMap K n M i S hi d t m) := by
  let D := polynomialHomogeneousSubsetDegreeNormalizeEquiv K n
    (polynomialProjTwistedFiniteSpanPiece K n M d t) i S hi m
  let E := LinearEquiv.ofBijective (polynomialTwistedFiniteSpanSubsetMap K n M d t i S hi)
    (polynomialTwistedFiniteSpanSubsetMap_bijective K n M d t i S hi hgen)
  let F := (polynomialTwistedSubsetTensorCoefficientsEquiv K n M i S hi m).symm
  have heq : ∀ z, polynomialTwistedFiniteSpanAllDegreeSubsetMap K n M i S hi d t m z = F (E (D z)) := by
    intro z
    apply (polynomialTwistedSubsetTensorCoefficientsEquiv K n M i S hi m).injective
    have hz : polynomialHomogeneousSubsetDegreeMultiply K n
        (polynomialProjTwistedFiniteSpanPiece K n M d t) i S m (D z) = z :=
      polynomialHomogeneousSubsetDegreeMultiply_normalize K n
        (polynomialProjTwistedFiniteSpanPiece K n M d t) i S hi m z
    calc
      polynomialTwistedSubsetTensorCoefficientsEquiv K n M i S hi m
          (polynomialTwistedFiniteSpanAllDegreeSubsetMap K n M i S hi d t m z) =
        polynomialTwistedSubsetTensorCoefficientsEquiv K n M i S hi m
          (polynomialTwistedFiniteSpanAllDegreeSubsetMap K n M i S hi d t m
            (polynomialHomogeneousSubsetDegreeMultiply K n
              (polynomialProjTwistedFiniteSpanPiece K n M d t) i S m (D z))) :=
        congrArg (fun w => polynomialTwistedSubsetTensorCoefficientsEquiv K n M i S hi m
          (polynomialTwistedFiniteSpanAllDegreeSubsetMap K n M i S hi d t m w)) hz.symm
      _ = polynomialTwistedFiniteSpanSubsetMap K n M d t i S hi (D z) :=
        polynomialTwistedFiniteSpanAllDegreeSubsetMap_multiply K n M i S hi d t m (D z)
      _ = polynomialTwistedSubsetTensorCoefficientsEquiv K n M i S hi m (F (E (D z))) :=
        (LinearEquiv.apply_symm_apply (polynomialTwistedSubsetTensorCoefficientsEquiv K n M i S hi m)
          (E (D z))).symm
  have hf : (fun z => polynomialTwistedFiniteSpanAllDegreeSubsetMap K n M i S hi d t m z) =
      (fun z => F (E (D z))) := funext heq
  change Function.Bijective (fun z => polynomialTwistedFiniteSpanAllDegreeSubsetMap K n M i S hi d t m z)
  rw [hf]
  exact F.bijective.comp (E.bijective.comp D.bijective)

/-- The same true finite span evaluates naturally in every nonnegative twist. -/
def polynomialTwistedFiniteSpanAllDegreeNonemptySubsetEvaluation (m : ℕ) :
    nonemptySubsetDiagram (homogeneousCoordinateSubsetDiagram
      (polynomialIntegralGrading (K := K) (I := Fin (n + 1)))
      (polynomialProjTwistedFiniteSpanPiece K n M d t)
      (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) polynomialCoordinate_X_degree (m : ℤ)) ⟶
    nonemptySubsetDiagram (actualSchemeModuleBaseSubsetDiagram (polynomialProjModuleTensorTwist K n M m)
      (polynomialProjCoordinateOpen K n) (schemeConstantMap (polynomialProjStructureMap K n))) :=
  Functor.whiskerLeft (nonemptySubsetInclusion (Fin (n + 1)))
    (polynomialTwistedFiniteSpanSubsetInclusion K n M d t (m : ℤ)) ≫
      polynomialTwistedAllDegreeNonemptySubsetEvaluation K n M m

/-- Actual chart generation supplies the genuine natural isomorphism for every degree of the same fixed span. -/
def polynomialTwistedFiniteSpanAllDegreeNonemptySubsetIso
    [∀ j, (polynomialProjModuleChart M j).IsQuasicoherent] (m : ℕ)
    (hgen : ∀ i, Submodule.span (polynomialProjCoordinateRing K n i)
      (Set.range (fun a => (polynomialProjChartTopSectionsIso M i).inv
        (atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M (d a) i (t a)))) = ⊤) :
    nonemptySubsetDiagram (homogeneousCoordinateSubsetDiagram
      (polynomialIntegralGrading (K := K) (I := Fin (n + 1)))
      (polynomialProjTwistedFiniteSpanPiece K n M d t)
      (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) polynomialCoordinate_X_degree (m : ℤ)) ≅
    nonemptySubsetDiagram (actualSchemeModuleBaseSubsetDiagram (polynomialProjModuleTensorTwist K n M m)
      (polynomialProjCoordinateOpen K n) (schemeConstantMap (polynomialProjStructureMap K n))) := by
  let α := polynomialTwistedFiniteSpanAllDegreeNonemptySubsetEvaluation K n M d t m
  letI : ∀ S, IsIso (α.app S) := fun S => by
    have he : Function.Bijective (α.app S).hom := by
      change Function.Bijective (polynomialTwistedFiniteSpanAllDegreeSubsetMap K n M
        S.property.choose S.val S.property.choose_spec d t m)
      exact polynomialTwistedFiniteSpanAllDegreeSubsetMap_bijective K n M S.property.choose S.val
        S.property.choose_spec d t m (hgen S.property.choose)
    change IsIso ((LinearEquiv.ofBijective (α.app S).hom he).toModuleIso.hom)
    infer_instance
  letI : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α

end ActualFamily

section GenuineChartGenerators
variable [∀ j, Module.Finite (polynomialProjCoordinateRing K n j)
  Γ(polynomialProjModuleChart M j, ⊤)]
  [∀ j, (polynomialProjModuleChart M j).IsQuasicoherent]

/-- The one genuine chart-generated finite span represents all nonnegative twists without reselecting generators. -/
def polynomialProjChartGeneratedTwistedAllDegreeNonemptySubsetIso (m : ℕ) :
    nonemptySubsetDiagram (homogeneousCoordinateSubsetDiagram
      (polynomialIntegralGrading (K := K) (I := Fin (n + 1)))
      (polynomialProjTwistedFiniteSpanPiece K n M
        (polynomialProjFiniteChartGeneratorDegree K n M) (polynomialProjFiniteChartGeneratorTwist K n M))
      (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) polynomialCoordinate_X_degree (m : ℤ)) ≅
    nonemptySubsetDiagram (actualSchemeModuleBaseSubsetDiagram (polynomialProjModuleTensorTwist K n M m)
      (polynomialProjCoordinateOpen K n) (schemeConstantMap (polynomialProjStructureMap K n))) :=
  polynomialTwistedFiniteSpanAllDegreeNonemptySubsetIso K n M
    (polynomialProjFiniteChartGeneratorDegree K n M) (polynomialProjFiniteChartGeneratorTwist K n M) m
    (polynomialProjFiniteChartGeneratorCoefficients_span K n M)

end GenuineChartGenerators

end
end SGPT.Foundations.Schemes
