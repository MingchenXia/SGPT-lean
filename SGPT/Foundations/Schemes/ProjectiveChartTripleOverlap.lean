import SGPT.Foundations.Schemes.PolynomialTwistedSectionUniqueness
import SGPT.Foundations.Schemes.AffineSectionAnnihilation

/-! # Genuine triple overlaps and actual coordinate annihilation

The true affine double-ratio open maps to the literal triple projective
intersection.  Native quasicoherence then kills actual overlap sections
vanishing on that true triple overlap by a real coordinate-ratio power.
-/

open CategoryTheory Opposite AlgebraicGeometry

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual product-ratio principal open is the literal genuine triple chart intersection. -/
theorem polynomialProjCoordinateImmersion_image_productRatioOpen
    (j k i : Fin (n + 1)) :
    polynomialProjCoordinateImmersion K n j ''ᵁ
      PrimeSpectrum.basicOpen (polynomialProjCoordinateRatio K n j k *
        polynomialProjCoordinateRatio K n j i) =
      polynomialProjCoordinateOpen K n j ⊓
        (polynomialProjCoordinateOpen K n k ⊓ polynomialProjCoordinateOpen K n i) := by
  rw [PrimeSpectrum.basicOpen_mul,
    ← polynomialProjCoordinateImmersion_preimage_coordinateOpen,
    ← polynomialProjCoordinateImmersion_preimage_coordinateOpen,
    ← Scheme.Hom.preimage_inf, Scheme.Hom.image_preimage_eq_opensRange_inf]
  simp only [polynomialProjCoordinateImmersion, Proj.opensRange_awayι]

/-- Actual sections on the double-ratio affine principal open identify with true triple-overlap sections. -/
def polynomialProjChartTripleSectionsIso (M : (polynomialProj K n).Modules)
    (j k i : Fin (n + 1)) :
    Γ(polynomialProjModuleChart M j,
      PrimeSpectrum.basicOpen (polynomialProjCoordinateRatio K n j k *
        polynomialProjCoordinateRatio K n j i)) ≅
      Γ(M, polynomialProjCoordinateOpen K n j ⊓
        (polynomialProjCoordinateOpen K n k ⊓ polynomialProjCoordinateOpen K n i)) :=
  M.restrictAppIso (polynomialProjCoordinateImmersion K n j) _ ≪≫
    M.presheaf.mapIso
      (eqToIso (polynomialProjCoordinateImmersion_image_productRatioOpen K n j k i).symm).op

/-- The real native double principal-open restriction is precisely the actual sheaf restriction to the triple overlap. -/
theorem polynomialProjChartTripleRestriction_actual (M : (polynomialProj K n).Modules)
    (j k i : Fin (n + 1))
    (s : Γ(polynomialProjModuleChart M j,
      PrimeSpectrum.basicOpen (polynomialProjCoordinateRatio K n j k))) :
    (polynomialProjChartTripleSectionsIso K n M j k i).hom
      (affinePrincipalRestriction (polynomialProjModuleChart M j)
        (polynomialProjCoordinateRatio K n j k) (polynomialProjCoordinateRatio K n j i) s) =
      M.presheaf.map (homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_left))).op
        ((polynomialProjChartOverlapSectionsIso M j k).hom s) := by
  change M.presheaf.map
      (eqToHom (polynomialProjCoordinateImmersion_image_productRatioOpen K n j k i).symm).op
      (M.presheaf.map
        (homOfLE ((polynomialProjCoordinateImmersion K n j).image_mono
          (PrimeSpectrum.basicOpen_mul_le_left _ _))).op s) =
    M.presheaf.map (homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_left))).op
      (M.presheaf.map
        (eqToHom (polynomialProjCoordinateImmersion_image_ratioOpen K n j k).symm).op s)
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp]
  congr 2

/-- A genuine projective overlap section vanishing on the true triple overlap is killed by an actual ratio power. -/
theorem polynomialProjChartOverlap_zero_after_ratio_power
    (M : (polynomialProj K n).Modules) (j k i : Fin (n + 1))
    [(polynomialProjModuleChart M j).IsQuasicoherent]
    (s : Γ(M, polynomialProjCoordinateOpen K n j ⊓ polynomialProjCoordinateOpen K n k))
    (h : M.presheaf.map
      (homOfLE (show polynomialProjCoordinateOpen K n j ⊓
          (polynomialProjCoordinateOpen K n k ⊓ polynomialProjCoordinateOpen K n i) ≤
          polynomialProjCoordinateOpen K n j ⊓ polynomialProjCoordinateOpen K n k from
        le_inf inf_le_left (inf_le_right.trans inf_le_left))).op s = 0) :
    ∃ N : ℕ,
      ((polynomialProj K n).presheaf.map (homOfLE (inf_le_left :
        polynomialProjCoordinateOpen K n j ⊓ polynomialProjCoordinateOpen K n k ≤
          polynomialProjCoordinateOpen K n j)).op
        (homogeneousPolynomialBasicOpenAwayEquiv j (polynomialProjCoordinateRatio K n j i))) ^ N •
          s = 0 := by
  let t := (polynomialProjChartOverlapSectionsIso M j k).inv s
  have ht : affinePrincipalRestriction (polynomialProjModuleChart M j)
      (polynomialProjCoordinateRatio K n j k) (polynomialProjCoordinateRatio K n j i) t = 0 := by
    apply (ConcreteCategory.bijective_of_isIso
      (polynomialProjChartTripleSectionsIso K n M j k i).hom).injective
    rw [map_zero, polynomialProjChartTripleRestriction_actual,
      Iso.inv_hom_id_apply, h]
  obtain ⟨N, hN⟩ := affinePrincipalSection_zero_after_power (polynomialProjModuleChart M j)
    (polynomialProjCoordinateRatio K n j k) (polynomialProjCoordinateRatio K n j i) ht
  refine ⟨N, ?_⟩
  have hh := congrArg (polynomialProjChartOverlapSectionsIso M j k).hom hN
  rw [polynomialProjChartOverlapSectionsIso_pow_smul, map_zero, Iso.inv_hom_id_apply] at hh
  exact hh

end

end SGPT.Foundations.Schemes
