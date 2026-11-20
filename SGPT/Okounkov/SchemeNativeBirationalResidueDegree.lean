import SGPT.NAPotential.AlgPrimes2Normal
import SGPT.NAPotential.ProjectiveGraphStalkNaturality
import SGPT.Projective.AlgebraicArtinianCycleDegree
import SGPT.Projective.BDivNov16LocalValuationFractionMap

/-! A birational morphism to an integral scheme has residue degree one over valuation stalks. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry
open SGPT.NAPotential.AlgPrimes3.ProjectiveGraphStalkNaturality
open SGPT.Projective.BDivNov16
open SGPT.Projective.NumEq.AlgebraicCurveDegree

variable {V X : Scheme.{0}} [IsIntegral V] [IsIntegral X] (p : V ⟶ X)
  (hη : p (genericPoint V) = genericPoint X) [IsIso (p.stalkMap (genericPoint V))]
  (v : V)

include hη

/-- The actual local map of a birational morphism is bijective over a valuation stalk. -/
theorem nativeBirational_stalkMap_bijective_of_valuation
    [ValuationRing (X.presheaf.stalk (p v))] :
    Function.Bijective (p.stalkMap v).hom := by
  let R : Type := X.presheaf.stalk (p v)
  let S : Type := V.presheaf.stalk v
  let K : Type := V.functionField
  let φ : R →+* S := (p.stalkMap v).hom
  let ψ : S →+* K := algebraMap S K
  let : Algebra R S := φ.toAlgebra
  let : Algebra R K := (ψ.comp φ).toAlgebra
  let : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq' rfl
  let c := X.presheaf.stalkCongr (.of_eq hη.symm)
  have hbij : Function.Bijective (genericPullback p hη) :=
    ConcreteCategory.bijective_of_isIso (c.hom ≫ p.stalkMap (genericPoint V))
  let e : X.functionField ≃+* K := RingEquiv.ofBijective (genericPullback p hη) hbij
  let eR : X.functionField ≃ₐ[R] K :=
    { e with commutes' := fun a => genericPullback_stalk p hη v a }
  let : IsFractionRing R K := IsFractionRing.of_algEquiv eR
  let : IsLocalHom (algebraMap R S) := by
    change IsLocalHom (p.stalkMap v).hom
    infer_instance
  exact actual_local_valuation_fraction_map_bijective (R := R) (S := S) (K := K)

/-- The residue extension of the actual map over a valuation stalk has degree one. -/
theorem nativeBirational_residueDegree_eq_one_of_valuation
    [ValuationRing (X.presheaf.stalk (p v))] : p.residueDegree v = 1 := by
  have hbij : Function.Bijective (p.residueFieldMap v) := by
    refine ⟨(p.residueFieldMap v).hom.injective, ?_⟩
    intro c
    obtain ⟨t, ht⟩ := V.residue_surjective v c
    obtain ⟨s, hs⟩ := (nativeBirational_stalkMap_bijective_of_valuation p hη v).surjective t
    refine ⟨X.residue (p v) s, ?_⟩
    have h := congrArg (fun q => q s) (Scheme.residue_residueFieldMap p v)
    change p.residueFieldMap v (X.residue (p v) s) = V.residue v (p.stalkMap v s) at h
    rwa [hs, ht] at h
  let := (p.residueFieldMap v).hom.toAlgebra
  exact Module.finrank_of_bijective_algebraMap hbij

/-- Over a smooth codimension-one point the actual algebraic residue degree is one. -/
theorem nativeBirational_residueDegree_eq_one_of_smooth_codimOne
    (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
    [IsSeparated f] [QuasiCompact f] [IsLocallyNoetherian X]
    (hv : Order.coheight (p v) = 1) : p.residueDegree v = 1 := by
  let : IsDiscreteValuationRing (X.presheaf.stalk (p v)) :=
    SGPT.NAPotential.AlgPrimes2.isDiscreteValuationRing_stalk f n hv
  exact nativeBirational_residueDegree_eq_one_of_valuation p hη v

/-- For equal point dimensions the prime-cycle coefficient is its residue degree. -/
theorem nativeBirational_mapCoeff_eq_one_of_smooth_codimOne
    (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
    [IsSeparated f] [QuasiCompact f] [IsLocallyNoetherian X]
    (hv : Order.coheight (p v) = 1)
    (hdim : pointDimension V v = pointDimension X (p v)) :
    AlgebraicCycle.mapCoeff p (pointDimension V) (pointDimension X) v = 1 := by
  rw [AlgebraicCycle.mapCoeff, if_pos hdim,
    nativeBirational_residueDegree_eq_one_of_smooth_codimOne p hη v f n hv]

end SGPT.Okounkov
