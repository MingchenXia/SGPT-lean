import SGPT.NAPotential.AffineGeneratorsAtCenter
import SGPT.NAPotential.OriginalDivisorGerm
import SGPT.NAPotential.DivisorValuationCenter
import SGPT.NAPotential.ProjectiveGraphProjection

/-!
# Actual native graph prime image equals the original divisor centre

Complete blueprint: `graph-prime-center-image.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.GraphPrimeCenterImage

open AlgebraicGeometry CategoryTheory IsLocalRing
open SGPT.NAPotential.Berkovich OpenDivisorOrderTransport
open SGPT.NAPotential.AlgPrimes3

variable {X : Scheme.{0}} [IsIntegral X] (D : PrimeDivisorOver X)
  (U : X.Opens) [Nonempty U] (hUa : IsAffineOpen U) (hpU : D.π D.point ∈ U)
  {s : ℕ} (b : Fin s → X.functionField)
  (i : Algebra.adjoin Γ(X, U) (Set.range b) →+* D.Y.presheaf.stalk D.point)
  (hi : ∀ v : Algebra.adjoin Γ(X, U) (Set.range b),
    algebraMap (D.Y.presheaf.stalk D.point) D.Y.functionField (i v) =
      D.pullback ((originalFunctionFieldEquiv D).symm v))

include hi in
/-- The constructed native graph coefficient map is the original actual local pullback
on EVERY original affine coefficient. -/
theorem coefficient_to_original_stalk (a : Γ(X, U)) :
    i (algebraMap Γ(X, U) (Algebra.adjoin Γ(X, U) (Set.range b)) a) =
      (D.π.stalkMap D.point) (X.presheaf.germ U (D.π D.point) hpU a) := by
  let h := (genericPoint_specializes D.point).map D.π.continuous
  let g := X.presheaf.germ U (D.π D.point) hpU a
  have he := OriginalDivisorGerm.originalFunctionFieldEquiv_specialization D (D.π D.point) h g
  have hg : algebraMap (X.presheaf.stalk (D.π D.point)) X.functionField g =
      X.germToFunctionField U a := X.algebraMap_germ_eq_germToFunctionField hpU a
  have heA := he.trans hg
  have hinv : (originalFunctionFieldEquiv D).symm (X.germToFunctionField U a) =
      (BerkovichPoint.specializationMap h).hom g := by
    apply (originalFunctionFieldEquiv D).injective
    rw [(originalFunctionFieldEquiv D).apply_symm_apply, heA]
  apply IsFractionRing.injective (D.Y.presheaf.stalk D.point) D.Y.functionField
  rw [hi]
  change D.pullback ((originalFunctionFieldEquiv D).symm (X.germToFunctionField U a)) = _
  rw [hinv]
  exact DivisorValuationCenter.pullback_specializationMap D g

include hpU hi in
/-- The ACTUAL contracted graph prime projects to the SAME original divisor centre. -/
theorem projection_contractedPrime :
    ProjectiveGraphProjection.projection U hUa b
      ⟨(maximalIdeal (D.Y.presheaf.stalk D.point)).comap i, inferInstance⟩ = D.π D.point := by
  let c := D.π D.point
  let B := Algebra.adjoin Γ(X, U) (Set.range b)
  let p : Ideal B := (maximalIdeal (D.Y.presheaf.stalk D.point)).comap i
  let z : Spec (.of B) := ⟨p, inferInstance⟩
  have hA : ProjectiveGraphProjection.affineProjection U b z =
      hUa.primeIdealOf ⟨c, hpU⟩ := by
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro a
    change i (algebraMap Γ(X, U) B a) ∈ maximalIdeal (D.Y.presheaf.stalk D.point) ↔
      a ∈ (hUa.primeIdealOf ⟨c, hpU⟩).asIdeal
    rw [coefficient_to_original_stalk (D := D) (U := U) (hpU := hpU)
      (b := b) (i := i) (hi := hi) a]
    let : Algebra Γ(X, U) (X.presheaf.stalk c) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨c, hpU⟩
    let : IsLocalization.AtPrime (X.presheaf.stalk c) (hUa.primeIdealOf ⟨c, hpU⟩).asIdeal :=
      hUa.isLocalization_stalk ⟨c, hpU⟩
    have hm : (D.π.stalkMap D.point).hom (algebraMap Γ(X, U) (X.presheaf.stalk c) a) ∈
        maximalIdeal (D.Y.presheaf.stalk D.point) ↔
        algebraMap Γ(X, U) (X.presheaf.stalk c) a ∈ maximalIdeal (X.presheaf.stalk c) := by
      change algebraMap Γ(X, U) (X.presheaf.stalk c) a ∈
          (maximalIdeal (D.Y.presheaf.stalk D.point)).comap (D.π.stalkMap D.point).hom ↔ _
      rw [IsLocalRing.maximalIdeal_comap]
    exact hm.trans (IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk c)
      (hUa.primeIdealOf ⟨c, hpU⟩).asIdeal a)
  change hUa.fromSpec (ProjectiveGraphProjection.affineProjection U b z) = c
  rw [hA]
  exact hUa.fromSpec_primeIdealOf ⟨c, hpU⟩

/-- The original divisor produces a native DVR graph on a PRESCRIBED original affine
centre chart, with original coefficient square AND the ACTUAL projection centre image. -/
theorem exists_nativePrime_center_on {X : Scheme.{0}} [IsIntegral X]
    (D : PrimeDivisorOver X) (U : X.Opens) (hUa : IsAffineOpen U)
    (hpU : D.π D.point ∈ U) :
    ∃ (_hU : D.π (genericPoint D.Y) ∈ U) (s : ℕ)
      (b : Fin s → X.residueField (D.π (genericPoint D.Y))),
      letI : Nonempty U := ⟨⟨D.π D.point, hpU⟩⟩
      let bX := fun k => originalFunctionFieldEquiv D (b k)
      ∃ iX : Algebra.adjoin Γ(X, U) (Set.range bX) →+* D.Y.presheaf.stalk D.point,
        (∀ v : Algebra.adjoin Γ(X, U) (Set.range bX),
          algebraMap (D.Y.presheaf.stalk D.point) D.Y.functionField (iX v) =
            D.pullback ((originalFunctionFieldEquiv D).symm v)) ∧
        letI := iX.toAlgebra
        IsLocalization.AtPrime (D.Y.presheaf.stalk D.point) ((maximalIdeal _).comap iX) ∧
          IsDiscreteValuationRing (Localization.AtPrime ((maximalIdeal _).comap iX)) ∧
          ProjectiveGraphProjection.projection U hUa bX
            ⟨(maximalIdeal (D.Y.presheaf.stalk D.point)).comap iX, inferInstance⟩ = D.π D.point := by
  obtain ⟨hU, s, b, iX, hiX, hloc, hDVR⟩ :=
    AffineGeneratorsAtCenter.exists_nativePrimeLocalization_on D U hUa hpU
  refine ⟨hU, s, b, ?_⟩
  let : Nonempty U := ⟨⟨D.π D.point, hpU⟩⟩
  let bX := fun k => originalFunctionFieldEquiv D (b k)
  refine ⟨iX, hiX, ?_⟩
  let : Algebra (Algebra.adjoin Γ(X, U) (Set.range bX)) (D.Y.presheaf.stalk D.point) := iX.toAlgebra
  exact ⟨hloc, hDVR, projection_contractedPrime D U hUa hpU bX iX hiX⟩

end SGPT.NAPotential.GraphPrimeCenterImage
