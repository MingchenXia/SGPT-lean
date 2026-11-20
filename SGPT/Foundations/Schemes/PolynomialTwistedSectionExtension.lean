import SGPT.Foundations.Schemes.PolynomialTwistedSectionUniqueness
import SGPT.Foundations.Schemes.NativeProjectivePushforward

/-! # Actual coordinate-power extension of projective module sections

Local lifts and their powers are produced by true affine quasicoherence and
native localization.  They are actual sections on the genuine coordinate
charts, with their true overlap restrictions.
-/

open CategoryTheory Opposite AlgebraicGeometry

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Finitely many genuine affine chart-overlap sections admit one common true denominator power. -/
theorem polynomialProjAcrossCharts_clearDenominators
    (M : (polynomialProj K n).Modules)
    [∀ j, (polynomialProjModuleChart M j).IsQuasicoherent]
    (i : Fin (n + 1))
    (s : ∀ j, Γ(polynomialProjModuleChart M j,
      PrimeSpectrum.basicOpen (polynomialProjCoordinateRatio K n j i))) :
    ∃ (N : ℕ) (t : ∀ j, Γ(polynomialProjModuleChart M j, ⊤)), ∀ j,
      polynomialProjChartOverlapRestriction M j i (t j) =
        polynomialProjCoordinateRatio K n j i ^ N • s j := by
  classical
  choose e u hu using fun j => polynomialProjChartOverlap_clearDenominator M j i (s j)
  let N := Finset.univ.sup e
  refine ⟨N, fun j => polynomialProjCoordinateRatio K n j i ^ (N - e j) • u j, ?_⟩
  intro j
  have hj : e j ≤ N := Finset.le_sup (Finset.mem_univ j)
  rw [LinearMap.map_smul, hu j, smul_smul, ← pow_add, Nat.sub_add_cancel hj]

/-- A true section on one coordinate chart has actual lifts on every chart after a common coordinate power. -/
theorem polynomialProjCoordinateSection_actualLocalLifts
    (M : (polynomialProj K n).Modules)
    [∀ j, (polynomialProjModuleChart M j).IsQuasicoherent]
    (i : Fin (n + 1)) (s : Γ(M, polynomialProjCoordinateOpen K n i)) :
    ∃ (N : ℕ) (t : ∀ j, Γ(M, polynomialProjCoordinateOpen K n j)), ∀ j,
      M.presheaf.map (homOfLE (inf_le_left : polynomialProjCoordinateOpen K n j ⊓
          polynomialProjCoordinateOpen K n i ≤ polynomialProjCoordinateOpen K n j)).op (t j) =
        ((polynomialProj K n).presheaf.map (homOfLE (inf_le_left :
          polynomialProjCoordinateOpen K n j ⊓ polynomialProjCoordinateOpen K n i ≤
            polynomialProjCoordinateOpen K n j)).op
          (homogeneousPolynomialBasicOpenAwayEquiv j (polynomialProjCoordinateRatio K n j i))) ^ N •
          M.presheaf.map (homOfLE (inf_le_right : polynomialProjCoordinateOpen K n j ⊓
            polynomialProjCoordinateOpen K n i ≤ polynomialProjCoordinateOpen K n i)).op s := by
  let v : ∀ j, Γ(polynomialProjModuleChart M j,
      PrimeSpectrum.basicOpen (polynomialProjCoordinateRatio K n j i)) := fun j =>
    (polynomialProjChartOverlapSectionsIso M j i).inv
      (M.presheaf.map (homOfLE (inf_le_right : polynomialProjCoordinateOpen K n j ⊓
        polynomialProjCoordinateOpen K n i ≤ polynomialProjCoordinateOpen K n i)).op s)
  obtain ⟨N, t, ht⟩ := polynomialProjAcrossCharts_clearDenominators K n M i v
  refine ⟨N, fun j => (polynomialProjChartTopSectionsIso M j).hom (t j), ?_⟩
  intro j
  rw [← polynomialProjChartOverlapRestriction_actual, ht j,
    polynomialProjChartOverlapSectionsIso_pow_smul]
  exact congrArg (fun z =>
    ((polynomialProj K n).presheaf.map (homOfLE inf_le_left).op
      (homogeneousPolynomialBasicOpenAwayEquiv j (polynomialProjCoordinateRatio K n j i))) ^ N • z)
    ((polynomialProjChartOverlapSectionsIso M j i).inv_hom_id_apply _)

end

end SGPT.Foundations.Schemes
