import SGPT.Foundations.Envelope.AlgGeom.FiniteFibrePrincipalOrders
import SGPT.Foundations.Envelope.AlgGeom.SchemeFinitePrincipalDegrees
import SGPT.Foundations.Envelope.SchemeAffinizationFactor

/-! # Intrinsic native finite-fibre orders on the SAME actual original affine curves -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
namespace SGPT.Foundations.Envelope.AffineFiniteFibreOrders
open FlatGlobalSections AffineSchemeLocalDegrees FiniteClosedIdealLocalDegrees
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}} [IsAffine X] (g : Y ⟶ X)

/-- The actual entire original affine identification retains EVERY original section coefficient. -/
theorem coefficientMap_isoSpec :
    ProperBirationalSections.coefficientMap (g ≫ X.isoSpec.hom) = g.appTop.hom := by
  unfold ProperBirationalSections.coefficientMap
  rw [Scheme.Hom.comp_appTop]
  change ((Scheme.ΓSpecIso Γ(X, ⊤)).inv ≫ X.toSpecΓ.appTop ≫ g.appTop).hom = _
  rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id_assoc]

/-- The actual source field structure induced by the original section ring
is the SAME original composite, as an equality of whole scheme morphisms. -/
theorem sourceFieldStructure_eq {k : Type u} [Field k] (q : X ⟶ Spec (.of k)) :
    let := structureSectionsAlgebra q
    FiniteFibrePrincipalOrders.sourceFieldStructure (k := k) (g ≫ X.isoSpec.hom) = g ≫ q := by
  let := structureSectionsAlgebra q
  change (g ≫ X.toSpecΓ) ≫ SchemeAffinizationFactor.coefficientProjection q = g ≫ q
  rw [Category.assoc, SchemeAffinizationFactor.toSpecΓ_comp_coefficientProjection]

/-- Native affine stalk localization sends EVERY same original section
to its SAME original coefficient fraction. -/
theorem stalkLocalizationAlgEquiv_germ {k : Type u} [Field k]
    (q : X ⟶ Spec (.of k)) (x : X) (c : Γ(X, ⊤)) :
    let := structureSectionsAlgebra q
    let := stalkAlgebra q x
    stalkLocalizationAlgEquiv q x (X.presheaf.germ ⊤ x trivial c) =
      algebraMap Γ(X, ⊤)
        (Localization.AtPrime ((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal) c := by
  let := structureSectionsAlgebra q
  let := stalkAlgebra q x
  let := X.presheaf.algebra_section_stalk (⟨x, trivial⟩ : (⊤ : X.Opens))
  let := (isAffineOpen_top X).isLocalization_stalk ⟨x, trivial⟩
  exact (IsLocalization.algEquiv
    ((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl
    (X.presheaf.stalk x)
    (Localization.AtPrime ((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal)).commutes c

variable [IsIntegral X] [IsIntegral Y] [IsFinite g] [IsDominant g]

/-- The original whole affine section generic rank is the degree of the
SAME native original dominant function-field map, not a chosen field match. -/
theorem genericRank_eq_functionFieldDegree :
    let := sectionsAlgebra (g ≫ X.isoSpec.hom)
    let := (DominantFunctionFieldMaps.functionFieldMap g).hom.toAlgebra
    Module.finrank Γ(X, ⊤) Γ(Y, ⊤) = Module.finrank X.functionField Y.functionField := by
  let : IsAffine Y := isAffine_of_isAffineHom g
  let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  let : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  let := sectionsAlgebra (g ≫ X.isoSpec.hom)
  let := (DominantFunctionFieldMaps.functionFieldMap g).hom.toAlgebra
  let := functionField_isFractionRing_of_isAffineOpen X ⊤ (isAffineOpen_top X)
  let := functionField_isFractionRing_of_isAffineOpen Y ⊤ (isAffineOpen_top Y)
  let : Algebra Γ(X, ⊤) Y.functionField :=
    ((Y.germToFunctionField ⊤).hom.comp g.appTop.hom).toAlgebra
  let : IsScalarTower Γ(X, ⊤) Γ(Y, ⊤) Y.functionField :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      change Y.germToFunctionField ⊤ (g.appTop r) =
        Y.germToFunctionField ⊤ (ProperBirationalSections.coefficientMap (g ≫ X.isoSpec.hom) r)
      rw [coefficientMap_isoSpec])
  let : Nonempty (g ⁻¹ᵁ ⊤) := ⟨⟨genericPoint Y, trivial⟩⟩
  let : IsScalarTower Γ(X, ⊤) X.functionField Y.functionField :=
    IsScalarTower.of_algebraMap_eq (fun r =>
      (DominantFunctionFieldMaps.functionFieldMap_section g ⊤ r).symm)
  exact (IsFractionRing.finrank_eq Γ(X, ⊤) X.functionField Γ(Y, ⊤) Y.functionField).symm

variable [IsLocallyNoetherian X]

omit [IsIntegral Y] [IsFinite g] [IsDominant g] [IsLocallyNoetherian X] in
/-- The SAME actual original nongeneric affine point gives a genuinely nonzero original prime. -/
theorem prime_ne_zero (x : X) (hx : x ≠ genericPoint X) :
    (isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩ ≠ ⊥ := by
  let : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  let : IsDomain Γ(X, ⊤) := IsIntegral.component_integral ⊤
  have he : X.isoSpec.hom x = (isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩ := pointPrimeEquiv_eq x
  have hη : X.isoSpec.hom (genericPoint X) = (⊥ : PrimeSpectrum Γ(X, ⊤)) := by
    rw [DominantFunctionFieldMaps.genericPoint_map X.isoSpec.hom, genericPoint_eq_bot_of_affine]
  intro hz
  exact hx (X.isoSpec.hom.isEmbedding.injective ((he.trans hz).trans hη.symm))

omit [IsIntegral Y] [IsFinite g] [IsDominant g] in
/-- The SAME original affine stalk and residue fields compute the TRUE
weighted native original regular-section order. -/
theorem weightedOrder_eq_localization {k : Type u} [Field k]
    (q : X ⟶ Spec (.of k)) (hdim : topologicalKrullDim X ≤ 1)
    (x : X) (hx : x ≠ genericPoint X) (c : Γ(X, ⊤)) (hc : c ≠ 0) :
    let := structureSectionsAlgebra q
    SchemeRegularSectionOrders.weightedOrder q c x =
      ((Ring.ord (Localization.AtPrime ((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal)
        (algebraMap Γ(X, ⊤)
          (Localization.AtPrime ((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal) c)).toNat : ℤ) *
        (Module.finrank k (IsLocalRing.ResidueField
          (Localization.AtPrime ((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal)) : ℤ) := by
  let := structureSectionsAlgebra q
  let := stalkAlgebra q x
  let := residueAlgebra q x
  rw [SchemeRegularSectionOrders.weightedOrder_eq_stalk q hdim c hc x hx]
  have ho := SemilinearPrincipalLengths.ord_ringEquiv
    (stalkLocalizationAlgEquiv q x).toRingEquiv (X.presheaf.germ ⊤ x trivial c)
  change Ring.ord (X.presheaf.stalk x) (X.presheaf.germ ⊤ x trivial c) =
    Ring.ord (Localization.AtPrime ((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal)
      (stalkLocalizationAlgEquiv q x (X.presheaf.germ ⊤ x trivial c)) at ho
  rw [stalkLocalizationAlgEquiv_germ] at ho
  rw [ho, (residueLocalizationAlgEquiv q x).toLinearEquiv.finrank_eq]

/-- TRUE weighted native original orders over the ENTIRE original finite
fibre, allowing a singular/nonflat original target curve. -/
theorem finsum_fibre_eq_functionFieldDegree {k : Type u} [Field k]
    (q : X ⟶ Spec (.of k)) (hdimX : topologicalKrullDim X ≤ 1)
    (hdimY : topologicalKrullDim Y ≤ 1) (x : X) (hx : x ≠ genericPoint X)
    (hres : letI := residueAlgebra q x; Module.Finite k (X.residueField x))
    (c : Γ(X, ⊤)) (hc : c ≠ 0) :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
    let := (DominantFunctionFieldMaps.functionFieldMap g).hom.toAlgebra
    (∑ᶠ y : {y : Y // g y = x}, SchemeRegularSectionOrders.weightedOrder
      (g ≫ q) (g.appTop c) y.1) =
      (Module.finrank X.functionField Y.functionField : ℤ) *
        SchemeRegularSectionOrders.weightedOrder q c x := by
  let := structureSectionsAlgebra q
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  let := (DominantFunctionFieldMaps.functionFieldMap g).hom.toAlgebra
  let A := Γ(X, ⊤)
  let f := g ≫ X.isoSpec.hom
  let p := (isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩
  let : IsDomain A := IsIntegral.component_integral ⊤
  let : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  let : Ring.KrullDimLE 1 A := SchemeFinitePrincipalDegrees.sections_krullDimLE hdimX ⟨⊤, isAffineOpen_top X⟩
  let := residueAlgebra q x
  let : Module.Finite k (X.residueField x) := hres
  let : Module.Finite k (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) :=
    Module.Finite.equiv (residueLocalizationAlgEquiv q x).toLinearEquiv
  have he : X.isoSpec.hom x = p := pointPrimeEquiv_eq x
  let e : {y : Y // g y = x} ≃ {y : Y // f y = p} :=
    { toFun := fun y => ⟨y.1, by change X.isoSpec.hom (g y.1) = p; rw [y.2]; exact he⟩
      invFun := fun y => ⟨y.1, by apply X.isoSpec.hom.isEmbedding.injective; exact y.2.trans he.symm⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hs := FiniteFibrePrincipalOrders.finsum_fibre_principal_orders (k := k) f p hdimY
    (prime_ne_zero x hx) c hc
  rw [sourceFieldStructure_eq, coefficientMap_isoSpec, genericRank_eq_functionFieldDegree] at hs
  rw [weightedOrder_eq_localization q hdimX x hx c hc]
  calc
    _ = ∑ᶠ y : {y : Y // f y = p}, SchemeRegularSectionOrders.weightedOrder
        (g ≫ q) (g.appTop c) y.1 := by
      apply finsum_eq_of_bijective e e.bijective
      intro y
      rfl
    _ = _ := by simpa only [mul_assoc] using hs

end SGPT.Foundations.Envelope.AffineFiniteFibreOrders
