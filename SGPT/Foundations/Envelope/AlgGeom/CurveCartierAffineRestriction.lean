import SGPT.Foundations.Envelope.AlgGeom.CurveCartierStalkOrders
import SGPT.Foundations.Envelope.AlgGeom.DominantFunctionFieldNaturality

/-! # Genuine original Cartier equation/order and whole finite-fibre chart restriction -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
namespace SGPT.Foundations.Envelope.CurveCartierAffineRestriction
open CurveCartierLocalOrders CurveCartierStalkOrders
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}}

/-- The SAME actual original affine equation becomes its true global equation on the SAME original open scheme. -/
theorem equation_on_open (I : X.IdealSheafData) (U : X.affineOpens)
    (c : Γ(X, U.1)) (hgen : I.ideal U = Ideal.span {c}) :
    (I.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top U.1.toScheme⟩ = Ideal.span {U.1.topIso.inv c} := by
  rw [I.comap_ideal_of_affine_opens U.1.ι ⟨⊤, isAffineOpen_top U.1.toScheme⟩ U
    (by intro z _hz; exact z.property), hgen, Ideal.map_span, Set.image_singleton]
  congr 2
  have he : U.1.ι.appLE U.1 ⊤ (by intro z _hz; exact z.property) = U.1.topIso.inv := by
    rw [Scheme.Opens.ι_appLE]
    apply congrArg X.presheaf.map
    apply Subsingleton.elim
  exact ConcreteCategory.congr_hom he c

variable [IsIntegral X]

private instance openIntegral (U : X.Opens) [Nonempty U] : IsIntegral U.toScheme :=
  isIntegral_of_isOpenImmersion U.ι

private theorem openDominant (U : X.Opens) [Nonempty U] : IsDominant U.ι := by
  obtain ⟨z⟩ := (inferInstance : Nonempty U)
  exact Opens.isDominant_ι (U.isOpen.dense ⟨z.1, z.2⟩)

/-- The SAME original nongeneric Cartier point has its TRUE weighted order
on the actual original open scheme, through the genuine original inclusion. -/
theorem weightedLocalOrder_restrict [IsLocallyNoetherian X] {k : Type u} [Field k]
    (q : X ⟶ Spec (.of k)) (hdim : topologicalKrullDim X ≤ 1)
    (I : X.IdealSheafData) (hI : I.IsInvertible) (U : X.Opens) [Nonempty U]
    (z : U.toScheme) (hz : U.ι z ≠ genericPoint X) :
    letI : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian U.ι
    weightedLocalOrder q I hI (U.ι z) =
      weightedLocalOrder (U.ι ≫ q) (I.comap U.ι) (hI.comap_of_flat U.ι) z := by
  let : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian U.ι
  let : IsDominant U.ι := openDominant U
  have hz' : z ≠ genericPoint U.toScheme := by
    intro he
    exact hz (he ▸ DominantFunctionFieldMaps.genericPoint_map U.ι)
  exact weightedLocalOrder_comap_stalkIso U.ι q hdim
    (U.ι.isEmbedding.isInducing.topologicalKrullDim_le.trans hdim) I hI _ z hz' hz

omit [IsIntegral X] in
/-- The original restricted map retains the SAME original point image. -/
theorem restrict_apply {Y : Scheme.{u}} (g : Y ⟶ X) (U : X.Opens)
    (z : (g ⁻¹ᵁ U).toScheme) : ((g ∣_ U) z).1 = g z.1 := by
  rw [← Scheme.Hom.resLE_eq_morphismRestrict]
  exact Scheme.Hom.coe_resLE_apply g le_rfl z

omit [IsIntegral X] in
/-- The ENTIRE original fibre equals the ENTIRE fibre of the SAME actual original chart restriction. -/
def fibreEquiv {Y : Scheme.{u}} (g : Y ⟶ X) (U : X.Opens) (x : X) (hx : x ∈ U) :
    {y : Y // g y = x} ≃ {z : (g ⁻¹ᵁ U).toScheme // (g ∣_ U) z = ⟨x, hx⟩} where
  toFun y := ⟨⟨y.1, by change g y.1 ∈ U; rw [y.2]; exact hx⟩, by
    apply Subtype.ext
    exact (restrict_apply g U _).trans y.2⟩
  invFun z := ⟨z.1.1, (restrict_apply g U z.1).symm.trans (congrArg Subtype.val z.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The SAME original chart restriction is genuinely dominant, derived from the original map. -/
theorem restriction_isDominant {Y : Scheme.{u}} [IsIntegral Y]
    (g : Y ⟶ X) [IsDominant g] (U : X.Opens) [Nonempty U] : IsDominant (g ∣_ U) := by
  let : Nonempty (g ⁻¹ᵁ U) := SchemeFinitePrincipalDegrees.nonempty_preimage g U
  let : IsDominant (g ⁻¹ᵁ U).ι := openDominant (g ⁻¹ᵁ U)
  have : IsDominant ((g ∣_ U) ≫ U.ι) := by
    rw [morphismRestrict_ι]
    infer_instance
  exact IsDominant.of_comp_of_isOpenImmersion (g ∣_ U) U.ι

/-- The SAME actual original nonempty open restriction preserves the TRUE native original field degree. -/
theorem functionFieldDegree_restrict {Y : Scheme.{u}} [IsIntegral Y]
    (g : Y ⟶ X) [IsDominant g] (U : X.Opens) [Nonempty U] :
    letI : Nonempty (g ⁻¹ᵁ U) := SchemeFinitePrincipalDegrees.nonempty_preimage g U
    letI : IsIntegral (g ⁻¹ᵁ U).toScheme := isIntegral_of_isOpenImmersion (g ⁻¹ᵁ U).ι
    letI : IsDominant (g ∣_ U) := restriction_isDominant g U
    letI := (DominantFunctionFieldMaps.functionFieldMap g).hom.toAlgebra
    letI := (DominantFunctionFieldMaps.functionFieldMap (g ∣_ U)).hom.toAlgebra
    Module.finrank X.functionField Y.functionField =
      Module.finrank U.toScheme.functionField (g ⁻¹ᵁ U).toScheme.functionField := by
  let : Nonempty (g ⁻¹ᵁ U) := SchemeFinitePrincipalDegrees.nonempty_preimage g U
  let : IsIntegral (g ⁻¹ᵁ U).toScheme := isIntegral_of_isOpenImmersion (g ⁻¹ᵁ U).ι
  let : IsDominant U.ι := openDominant U
  let : IsDominant (g ⁻¹ᵁ U).ι := openDominant (g ⁻¹ᵁ U)
  let : IsDominant (g ∣_ U) := restriction_isDominant g U
  exact DominantFunctionFieldNaturality.finrank_eq_of_open_square g (g ∣_ U)
    (g ⁻¹ᵁ U).ι U.ι (morphismRestrict_ι g U).symm

end SGPT.Foundations.Envelope.CurveCartierAffineRestriction
