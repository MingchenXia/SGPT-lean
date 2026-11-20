import SGPT.Okounkov.OF12NormalResolution
import SGPT.NAPotential.ProjectiveGraphStalkNaturality
import SGPT.Projective.OriginalCharacteristicZeroResidue

/-! The original field pullback is an equivalence when a proper complex morphism is
bijective on complex points over a nonempty algebraic open. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SGPT.Okounkov.OF12

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set TopologicalSpace
open SGPT.NAPotential.AlgPrimes3.ProjectiveGraphStalkNaturality
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

private theorem genericPoint_eq_of_denseRange {A B : Scheme.{0}}
    [IsIntegral A] [IsIntegral B] (q : A ⟶ B) (hq : DenseRange q) :
    q (genericPoint A) = genericPoint B := by
  apply ((genericPoint_spec B).eq _).symm
  simpa only [image_univ, hq.closure_range] using (genericPoint_spec A).image q.continuous

private theorem genericPoint_open_ι {A : Scheme.{0}}
    [IsIntegral A] (U : A.Opens) [Nonempty U] [IsIntegral U.toScheme] :
    U.ι (genericPoint U.toScheme) = genericPoint A := by
  apply genericPoint_eq_of_denseRange
  change Dense (range U.ι)
  rw [Scheme.Opens.range_ι]
  exact U.isOpen.dense (Set.nonempty_coe_sort.mp (inferInstanceAs (Nonempty U)))

private theorem isIso_genericStalkMap_of_surjective_universallyInjective
    {A B : Scheme.{0}} [IsIntegral A] [IsIntegral B]
    (g : B ⟶ A) (f : A ⟶ Spec (.of ℂ)) [Surjective g] [UniversallyInjective g] :
    IsIso (g.stalkMap (genericPoint B)) := by
  let y := genericPoint B
  have hpoint : g y = genericPoint A := genericPoint_eq_of_denseRange g g.surjective.denseRange
  let : IsIso (g.residueFieldMap y) := originalResidueFieldMap_isIso_of_universallyInjective g f y
  have hA : IsIso (A.residue (g y)) := by
    rw [hpoint]
    exact (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨(A.residue _).hom.injective, A.residue_surjective _⟩
  let : IsIso (A.residue (g y)) := hA
  let : IsIso (B.residue y) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨(B.residue _).hom.injective, B.residue_surjective _⟩
  have hcomp : IsIso (g.stalkMap y ≫ B.residue y) := by
    rw [← Scheme.residue_residueFieldMap]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hcomp

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

/-- The actual field pullback agrees with every original stalk map. Complex-point
bijectivity on a nonempty algebraic open suffices to prove it is an equivalence. -/
theorem birationalData_of_restrict_complexPoint_bijective
    (f : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType f] (ρ : Y ⟶ X) [IsProper ρ]
    (U : X.Opens) [Nonempty U]
    (hbij : Function.Bijective
      (schemeComplexPointMap ((ρ ∣_ U) ≫ (U.ι ≫ f)) (U.ι ≫ f) (ρ ∣_ U) rfl)) :
    IsIso (ρ.stalkMap (genericPoint Y)) ∧
      ∃ e : X.functionField ≃+* Y.functionField, IsStalkCompatible ρ e.toRingHom := by
  let g := ρ ∣_ U
  let W := ρ ⁻¹ᵁ U
  let : IsProper g := inferInstanceAs (IsProper (ρ ∣_ U))
  obtain ⟨_hfinite, hinjective, hsurjective⟩ :=
    originalFiniteUniversalBijection_of_complexPoint_bijective g (U.ι ≫ f) hbij
  let := hinjective
  let := hsurjective
  let : Nonempty W := Nonempty.map (fun z : U.toScheme => (g.surjective z).choose) inferInstance
  let : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  let : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  let z := genericPoint W.toScheme
  have hz : W.ι z = genericPoint Y := genericPoint_open_ι W
  have hgz : g z = genericPoint U.toScheme :=
    genericPoint_eq_of_denseRange g g.surjective.denseRange
  have hρη : ρ (genericPoint Y) = genericPoint X := by
    have hs := congrArg (fun q : W.toScheme ⟶ X => q z) (morphismRestrict_ι ρ U)
    change U.ι (g z) = ρ (W.ι z) at hs
    rw [hgz, genericPoint_open_ι U, hz] at hs
    exact hs.symm
  have hres : IsIso (g.stalkMap z) :=
    isIso_genericStalkMap_of_surjective_universallyInjective g (U.ι ≫ f)
  have hresLE : IsIso ((ρ.resLE U W le_rfl).stalkMap z) := by
    rw [ρ.resLE_eq_morphismRestrict]
    exact hres
  have hρz : IsIso (ρ.stalkMap (W.ι z)) :=
    (Arrow.isIso_hom_iff_isIso_of_isIso
      (ρ.resLEStalkMap (le_rfl : W ≤ ρ ⁻¹ᵁ U) z).hom).mp hresLE
  have hρ : IsIso (ρ.stalkMap (genericPoint Y)) := hz ▸ hρz
  let := hρ
  let c := X.presheaf.stalkCongr (.of_eq hρη.symm)
  let e := (asIso (c.hom ≫ ρ.stalkMap (genericPoint Y))).commRingCatIsoToRingEquiv
  exact ⟨hρ, e, genericPullback_stalk ρ hρη⟩

/-- The function-field equivalence from complex-point bijectivity on an algebraic open. -/
theorem exists_stalkCompatible_fieldEquiv_of_restrict_complexPoint_bijective
    (f : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType f] (ρ : Y ⟶ X) [IsProper ρ]
    (U : X.Opens) [Nonempty U]
    (hbij : Function.Bijective
      (schemeComplexPointMap ((ρ ∣_ U) ≫ (U.ι ≫ f)) (U.ι ≫ f) (ρ ∣_ U) rfl)) :
    ∃ e : X.functionField ≃+* Y.functionField, IsStalkCompatible ρ e.toRingHom :=
  (birationalData_of_restrict_complexPoint_bijective f ρ U hbij).2

end SGPT.Okounkov.OF12
