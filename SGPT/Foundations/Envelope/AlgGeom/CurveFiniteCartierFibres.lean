import SGPT.Foundations.Envelope.AlgGeom.CurveCartierAffineRestriction
import SGPT.Foundations.Envelope.AlgGeom.ProjectiveClosedPointResidueDegrees

/-! # TRUE entire original finite-fibre Cartier degrees on singular proper curves -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
namespace SGPT.Foundations.Envelope.CurveFiniteCartierFibres
open CurveCartierLocalOrders CurveCartierStalkOrders CurveCartierAffineRestriction
open AffineSchemeLocalDegrees
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem weighted_congr_ideal {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
    {k : Type u} [Field k] (q : T ⟶ Spec (.of k))
    (I J : T.IdealSheafData) (hI : I.IsInvertible) (hJ : J.IsInvertible)
    (he : I = J) (z : T) : weightedLocalOrder q I hI z = weightedLocalOrder q J hJ z := by
  subst J
  rfl

/-- EVERY original finite fibre of a Cartier ideal has its TRUE native
weighted-order sum scaled by the SAME original function-field degree.
Original proper geometry derives all point/residue/chart hypotheses;
no original target normality or finite-map flatness is required. -/
theorem finsum_fibre_comap {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    {k : Type u} [Field k] (g : Y ⟶ X) [IsFinite g] [IsDominant g]
    (q : X ⟶ Spec (.of k)) (hq : IsProjectiveFactorization q)
    (hdimX : topologicalKrullDim X ≤ 1) (hdimY : topologicalKrullDim Y ≤ 1)
    (I : X.IdealSheafData) (hI : I.IsInvertible) (x : X) (hx : x ≠ genericPoint X) :
    letI : IsProper q := hq.isProper
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
    letI := (DominantFunctionFieldMaps.functionFieldMap g).hom.toAlgebra
    (∑ᶠ y : {y : Y // g y = x}, weightedLocalOrder (g ≫ q) (I.comap g)
      (hI.comap_of_dominant_integral g) y.1) =
      (Module.finrank X.functionField Y.functionField : ℤ) * weightedLocalOrder q I hI x := by
  let : IsProper q := hq.isProper
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  let := (DominantFunctionFieldMaps.functionFieldMap g).hom.toAlgebra
  let U := equationChart I hI x
  have hxU : x ∈ U.1 := mem_equationChart I hI x
  let : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
  let V := g ⁻¹ᵁ U.1
  let : Nonempty V := SchemeFinitePrincipalDegrees.nonempty_preimage g U.1
  let : IsIntegral U.1.toScheme := isIntegral_of_isOpenImmersion U.1.ι
  let : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  let : IsLocallyNoetherian U.1.toScheme := LocallyOfFiniteType.isLocallyNoetherian U.1.ι
  let : IsLocallyNoetherian V.toScheme := LocallyOfFiniteType.isLocallyNoetherian V.ι
  let : IsAffine U.1.toScheme := U.2
  let f := g ∣_ U.1
  let : IsDominant f := restriction_isDominant g U.1
  let : IsFinite f := inferInstance
  let : IsAffine V.toScheme := isAffine_of_isAffineHom f
  let : IsDominant U.1.ι := Opens.isDominant_ι (U.1.isOpen.dense ⟨x, hxU⟩)
  let xu : U.1.toScheme := ⟨x, hxU⟩
  have hxu : xu ≠ genericPoint U.1.toScheme := by
    intro he
    have hh := congrArg U.1.ι he
    exact hx (hh.trans (DominantFunctionFieldMaps.genericPoint_map U.1.ι))
  let qu := U.1.ι ≫ q
  let Iu := I.comap U.1.ι
  let hIu : Iu.IsInvertible := hI.comap_of_flat U.1.ι
  let J := I.comap g
  let hJ : J.IsInvertible := hI.comap_of_dominant_integral g
  let c := equation I hI x
  let : IsDomain Γ(X, U.1) := IsIntegral.component_integral U.1
  have hc : c ≠ 0 := nonZeroDivisors.ne_zero (equation_mem_nonZeroDivisors I hI x)
  have hcu : U.1.topIso.inv c ≠ 0 := by
    simpa only [map_zero] using (ConcreteCategory.bijective_of_isIso U.1.topIso.inv).injective.ne hc
  have hresu : letI := residueAlgebra qu xu; Module.Finite k (U.1.toScheme.residueField xu) := by
    let := residueAlgebra q (U.1.ι xu)
    let := residueAlgebra qu xu
    have hclosed : IsClosed ({U.1.ι xu} : Set X) := by
      change IsClosed ({x} : Set X)
      exact CurveFiniteClosedSubschemes.isClosed_singleton hdimX x hx
    let : Module.Finite k (X.residueField (U.1.ι xu)) :=
      ProjectiveClosedPointResidueDegrees.residueField_finite q hq (U.1.ι xu) hclosed
    exact Module.Finite.equiv (SchemeStalkMapLocalOrders.residueFieldAlgEquiv U.1.ι xu q).toLinearEquiv
  have hdU := U.1.ι.isEmbedding.isInducing.topologicalKrullDim_le.trans hdimX
  have hdV := V.ι.isEmbedding.isInducing.topologicalKrullDim_le.trans hdimY
  let := (DominantFunctionFieldMaps.functionFieldMap f).hom.toAlgebra
  have hs := finsum_fibre_comap_of_global_equation f qu hdU hdV Iu hIu xu hxu hresu
    (U.1.topIso.inv c) hcu (equation_on_open I U c (equation_span I hI x))
  have hIdeals : Iu.comap f = J.comap V.ι := by
    change (I.comap U.1.ι).comap (g ∣_ U.1) = (I.comap g).comap (g ⁻¹ᵁ U.1).ι
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, morphismRestrict_ι]
  have hstruct : f ≫ qu = V.ι ≫ (g ≫ q) := by
    change (g ∣_ U.1) ≫ U.1.ι ≫ q = (g ⁻¹ᵁ U.1).ι ≫ g ≫ q
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  let e := fibreEquiv g U.1 x hxU
  calc
    _ = ∑ᶠ z : {z : V.toScheme // f z = xu},
        weightedLocalOrder (V.ι ≫ (g ≫ q)) (J.comap V.ι) (hJ.comap_of_flat V.ι) z.1 := by
      apply finsum_eq_of_bijective e e.bijective
      intro y
      have hy : y.1 ≠ genericPoint Y := by
        intro he
        have h := y.2
        rw [he, DominantFunctionFieldMaps.genericPoint_map g] at h
        exact hx h.symm
      exact weightedLocalOrder_restrict (g ≫ q) hdimY J hJ V (e y).1 hy
    _ = ∑ᶠ z : {z : V.toScheme // f z = xu},
        weightedLocalOrder (f ≫ qu) (Iu.comap f) (hIu.comap_of_dominant_integral f) z.1 := by
      apply finsum_congr
      intro z
      rw [hstruct]
      exact weighted_congr_ideal _ _ _ _ _ hIdeals.symm z.1
    _ = (Module.finrank U.1.toScheme.functionField V.toScheme.functionField : ℤ) *
        weightedLocalOrder qu Iu hIu xu := hs
    _ = _ := by
      rw [← functionFieldDegree_restrict g U.1]
      rw [← weightedLocalOrder_restrict q hdimX I hI U.1 xu hx]
      rfl

end SGPT.Foundations.Envelope.CurveFiniteCartierFibres
