import SGPT.Foundations.Schemes.PolynomialProjectiveCanonical
import SGPT.Foundations.Schemes.AffineChartSectionExtension

/-! # Actual projective coordinate overlaps and section denominators

The overlap of genuine polynomial-Proj charts is the principal affine open
defined by the literal ratio `X_j / X_i`.  All section maps below are native
restrictions of actual scheme modules.  The denominator conclusions follow
from native affine quasicoherence; no graded representation or extension
conclusion is an input.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopCat TopologicalSpace

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual distinguished-coordinate open of polynomial Proj. -/
abbrev polynomialProjCoordinateOpen (i : Fin (n + 1)) : (polynomialProj K n).Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X i)

/-- The actual affine overlap localization element is the literal coordinate ratio. -/
theorem polynomialProjCoordinateRatio_eq_localizationElem (i j : Fin (n + 1)) :
    polynomialProjCoordinateRatio K n i j =
      HomogeneousLocalization.Away.isLocalizationElem
        (MvPolynomial.isHomogeneous_X K i) (MvPolynomial.isHomogeneous_X K j) := by
  apply HomogeneousLocalization.val_injective
  simp only [polynomialProjCoordinateRatio, HomogeneousLocalization.Away.isLocalizationElem,
    HomogeneousLocalization.Away.val_mk, pow_one]

/-- The inverse image of a true coordinate open is the actual principal ratio open. -/
theorem polynomialProjCoordinateImmersion_preimage_coordinateOpen (i j : Fin (n + 1)) :
    polynomialProjCoordinateImmersion K n i ⁻¹ᵁ polynomialProjCoordinateOpen K n j =
      PrimeSpectrum.basicOpen (polynomialProjCoordinateRatio K n i j) := by
  exact (Proj.awayι_preimage_basicOpen
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
    (show MvPolynomial.X i ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K 1
      from MvPolynomial.isHomogeneous_X K i) (by decide)
    (show MvPolynomial.X j ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K 1
      from MvPolynomial.isHomogeneous_X K j) (by decide)).trans
    (congrArg PrimeSpectrum.basicOpen (polynomialProjCoordinateRatio_eq_localizationElem K n i j).symm)

/-- The image of the actual affine principal ratio open is the actual chart intersection. -/
theorem polynomialProjCoordinateImmersion_image_ratioOpen (i j : Fin (n + 1)) :
    polynomialProjCoordinateImmersion K n i ''ᵁ
        PrimeSpectrum.basicOpen (polynomialProjCoordinateRatio K n i j) =
      polynomialProjCoordinateOpen K n i ⊓ polynomialProjCoordinateOpen K n j := by
  rw [← polynomialProjCoordinateImmersion_preimage_coordinateOpen,
    Scheme.Hom.image_preimage_eq_opensRange_inf]
  simp only [polynomialProjCoordinateImmersion, Proj.opensRange_awayι]

/-- The actual affine chart's whole image is the actual coordinate open. -/
theorem polynomialProjCoordinateImmersion_image_top (i : Fin (n + 1)) :
    polynomialProjCoordinateImmersion K n i ''ᵁ ⊤ =
      polynomialProjCoordinateOpen K n i := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  exact Proj.opensRange_awayι _ _ (MvPolynomial.isHomogeneous_X K i) (by decide)

/-- Each actual coordinate open is affine by its genuine homogeneous localization. -/
theorem polynomialProjCoordinateOpen_isAffine (i : Fin (n + 1)) :
    IsAffineOpen (polynomialProjCoordinateOpen K n i) :=
  Proj.isAffineOpen_basicOpen _ _ (MvPolynomial.isHomogeneous_X K i) (by decide)

/-- Actual pair intersections are affine, using the genuine homogeneous product chart. -/
theorem polynomialProjCoordinateOverlap_isAffine (i j : Fin (n + 1)) :
    IsAffineOpen (polynomialProjCoordinateOpen K n i ⊓ polynomialProjCoordinateOpen K n j) := by
  rw [polynomialProjCoordinateOpen, polynomialProjCoordinateOpen, ← Proj.basicOpen_mul]
  exact Proj.isAffineOpen_basicOpen _ _
    (SetLike.mul_mem_graded (MvPolynomial.isHomogeneous_X K i)
      (MvPolynomial.isHomogeneous_X K j)) (by decide)

variable {K n}

/-- Restriction of the genuine scheme module to its actual affine coordinate chart. -/
abbrev polynomialProjModuleChart (M : (polynomialProj K n).Modules) (i : Fin (n + 1)) :=
  M.restrict (polynomialProjCoordinateImmersion K n i)

/-- The actual affine section action is the native action of its actual chart ring. -/
instance polynomialProjModuleChartSectionsModule (M : (polynomialProj K n).Modules)
    (i : Fin (n + 1))
    (U : (Spec (.of (polynomialProjCoordinateRing K n i))).Opens) :
    Module (polynomialProjCoordinateRing K n i) Γ(polynomialProjModuleChart M i, U) :=
  @Scheme.Modules.instModuleCarrierCarrierObjOppositeOpensCarrierCarrierCommRingCatSpecAbPresheafOp
    (CommRingCat.of (polynomialProjCoordinateRing K n i)) (polynomialProjModuleChart M i) U

/-- Actual whole-chart sections identify with actual sections on the coordinate open. -/
def polynomialProjChartTopSectionsIso (M : (polynomialProj K n).Modules)
    (i : Fin (n + 1)) :
    Γ(polynomialProjModuleChart M i, ⊤) ≅ Γ(M, polynomialProjCoordinateOpen K n i) :=
  M.restrictAppIso (polynomialProjCoordinateImmersion K n i) ⊤ ≪≫
    M.presheaf.mapIso (eqToIso (polynomialProjCoordinateImmersion_image_top K n i).symm).op

/-- Actual principal-chart sections identify with actual sections on the true overlap. -/
def polynomialProjChartOverlapSectionsIso (M : (polynomialProj K n).Modules)
    (i j : Fin (n + 1)) :
    Γ(polynomialProjModuleChart M i,
        PrimeSpectrum.basicOpen (polynomialProjCoordinateRatio K n i j)) ≅
      Γ(M, polynomialProjCoordinateOpen K n i ⊓ polynomialProjCoordinateOpen K n j) :=
  M.restrictAppIso (polynomialProjCoordinateImmersion K n i) _ ≪≫
    M.presheaf.mapIso
      (eqToIso (polynomialProjCoordinateImmersion_image_ratioOpen K n i j).symm).op

/-- The actual principal-overlap restriction, with its native coordinate-ring action. -/
def polynomialProjChartOverlapRestriction (M : (polynomialProj K n).Modules)
    (i j : Fin (n + 1)) :
    Γ(polynomialProjModuleChart M i, ⊤) →ₗ[polynomialProjCoordinateRing K n i]
      Γ(polynomialProjModuleChart M i,
        PrimeSpectrum.basicOpen (polynomialProjCoordinateRatio K n i j)) :=
  affineSectionRestriction (polynomialProjModuleChart M i)
    (polynomialProjCoordinateRatio K n i j)

/-- The affine localization restriction is precisely the actual projective sheaf restriction. -/
theorem polynomialProjChartOverlapRestriction_actual
    (M : (polynomialProj K n).Modules) (i j : Fin (n + 1))
    (s : Γ(polynomialProjModuleChart M i, ⊤)) :
    (polynomialProjChartOverlapSectionsIso M i j).hom
        (polynomialProjChartOverlapRestriction M i j s) =
      M.presheaf.map (homOfLE inf_le_left).op ((polynomialProjChartTopSectionsIso M i).hom s) := by
  change M.presheaf.map
      (eqToHom (polynomialProjCoordinateImmersion_image_ratioOpen K n i j).symm).op
      (M.presheaf.map
        (homOfLE ((polynomialProjCoordinateImmersion K n i).image_mono le_top)).op s) =
    M.presheaf.map (homOfLE inf_le_left).op
      (M.presheaf.map
        (eqToHom (polynomialProjCoordinateImmersion_image_top K n i).symm).op s)
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp]
  congr 2

/-- Actual affine quasicoherence makes the actual projective overlap restriction localization. -/
theorem polynomialProjChartOverlapRestriction_isLocalized
    (M : (polynomialProj K n).Modules) (i j : Fin (n + 1))
    [(polynomialProjModuleChart M i).IsQuasicoherent] :
    IsLocalizedModule.Away (polynomialProjCoordinateRatio K n i j)
      (polynomialProjChartOverlapRestriction M i j) :=
  affineSectionRestriction_isLocalized (polynomialProjModuleChart M i)
    (polynomialProjCoordinateRatio K n i j)

/-- Any actual overlap section clears a true ratio denominator on the actual affine chart. -/
theorem polynomialProjChartOverlap_clearDenominator
    (M : (polynomialProj K n).Modules) (i j : Fin (n + 1))
    [(polynomialProjModuleChart M i).IsQuasicoherent]
    (s : Γ(polynomialProjModuleChart M i,
      PrimeSpectrum.basicOpen (polynomialProjCoordinateRatio K n i j))) :
    ∃ (d : ℕ) (t : Γ(polynomialProjModuleChart M i, ⊤)),
      polynomialProjChartOverlapRestriction M i j t =
        polynomialProjCoordinateRatio K n i j ^ d • s :=
  affineSection_clearDenominator (polynomialProjModuleChart M i)
    (polynomialProjCoordinateRatio K n i j) s

/-- Actual affine sections agreeing on the genuine overlap agree after a true ratio power. -/
theorem polynomialProjChartOverlap_eq_after_power
    (M : (polynomialProj K n).Modules) (i j : Fin (n + 1))
    [(polynomialProjModuleChart M i).IsQuasicoherent]
    {s t : Γ(polynomialProjModuleChart M i, ⊤)}
    (h : polynomialProjChartOverlapRestriction M i j s =
      polynomialProjChartOverlapRestriction M i j t) :
    ∃ d : ℕ, polynomialProjCoordinateRatio K n i j ^ d • s =
      polynomialProjCoordinateRatio K n i j ^ d • t :=
  affineSection_eq_after_power (polynomialProjModuleChart M i)
    (polynomialProjCoordinateRatio K n i j) h

/-- Finitely many true overlap sections share one genuine chart denominator power. -/
theorem polynomialProjChartOverlaps_clearDenominators {A : Type} [Fintype A]
    (M : (polynomialProj K n).Modules) (i j : Fin (n + 1))
    [(polynomialProjModuleChart M i).IsQuasicoherent]
    (s : A → Γ(polynomialProjModuleChart M i,
      PrimeSpectrum.basicOpen (polynomialProjCoordinateRatio K n i j))) :
    ∃ (d : ℕ) (t : A → Γ(polynomialProjModuleChart M i, ⊤)), ∀ a,
      polynomialProjChartOverlapRestriction M i j (t a) =
        polynomialProjCoordinateRatio K n i j ^ d • s a :=
  affineSections_clearDenominators (polynomialProjModuleChart M i)
    (polynomialProjCoordinateRatio K n i j) s

/-- Finitely many equalities on the true overlap share one genuine annihilating power. -/
theorem polynomialProjChartOverlaps_eq_after_power {A : Type} [Fintype A]
    (M : (polynomialProj K n).Modules) (i j : Fin (n + 1))
    [(polynomialProjModuleChart M i).IsQuasicoherent]
    (s t : A → Γ(polynomialProjModuleChart M i, ⊤))
    (h : ∀ a, polynomialProjChartOverlapRestriction M i j (s a) =
      polynomialProjChartOverlapRestriction M i j (t a)) :
    ∃ d : ℕ, ∀ a, polynomialProjCoordinateRatio K n i j ^ d • s a =
      polynomialProjCoordinateRatio K n i j ^ d • t a :=
  affineSections_eq_after_power (polynomialProjModuleChart M i)
    (polynomialProjCoordinateRatio K n i j) s t h

/-- Finitely many actual overlap errors killed by restriction share one killing power. -/
theorem polynomialProjChartOverlaps_zero_after_power {A : Type} [Fintype A]
    (M : (polynomialProj K n).Modules) (i j : Fin (n + 1))
    [(polynomialProjModuleChart M i).IsQuasicoherent]
    (s : A → Γ(polynomialProjModuleChart M i, ⊤))
    (h : ∀ a, polynomialProjChartOverlapRestriction M i j (s a) = 0) :
    ∃ d : ℕ, ∀ a, polynomialProjCoordinateRatio K n i j ^ d • s a = 0 :=
  affineSections_zero_after_power (polynomialProjModuleChart M i)
    (polynomialProjCoordinateRatio K n i j) s h

end

end SGPT.Foundations.Schemes
