import SGPT.Foundations.Envelope.AlgGeom.AffineFiniteFibreOrders
import SGPT.Foundations.Envelope.AlgGeom.CurveCartierLocalOrders
import SGPT.Foundations.Envelope.AlgGeom.DominantCartierPullback

/-! # SAME original Cartier stalk orders, actual affine equations and true finite-fibre sums -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
namespace SGPT.Foundations.Envelope.CurveCartierStalkOrders
open CurveCartierLocalOrders AffineSchemeLocalDegrees
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The TRUE native original Cartier order is the SAME actual original stalk-ideal quotient length. -/
theorem localOrder_eq_stalkQuotient (hdim : topologicalKrullDim X ≤ 1)
    (I : X.IdealSheafData) (hI : I.IsInvertible) (x : X) (hx : x ≠ genericPoint X) :
    localOrder I hI x = ((Module.length (X.presheaf.stalk x)
      ((X.presheaf.stalk x) ⧸ I.stalkIdeal x)).toNat : ℤ) := by
  let U := equationChart I hI x
  let : Nonempty U.1 := ⟨⟨x, mem_equationChart I hI x⟩⟩
  let : IsDomain Γ(X, U.1) := IsIntegral.component_integral U.1
  have hc : equation I hI x ≠ 0 := nonZeroDivisors.ne_zero (equation_mem_nonZeroDivisors I hI x)
  change X.ord (X.germToFunctionField U.1 (equation I hI x)) x = _
  rw [SchemeOrderLocalLength.ord_germToFunctionField_eq_stalk_length x
    (CurveFiniteClosedSubschemes.coheight_eq_one hdim x hx) U.1 (mem_equationChart I hI x) _ hc]
  rw [I.stalkIdeal_eq_map_germ U (mem_equationChart I hI x), equation_span,
    Ideal.map_span, Set.image_singleton]

/-- An actual native original stalk isomorphism preserves the SAME original
Cartier weighted order through the actual original comap ideal. -/
theorem weightedLocalOrder_comap_stalkIso {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    {k : Type u} [Field k] (g : Y ⟶ X) (q : X ⟶ Spec (.of k))
    (hdimX : topologicalKrullDim X ≤ 1) (hdimY : topologicalKrullDim Y ≤ 1)
    (I : X.IdealSheafData) (hI : I.IsInvertible) (hJ : (I.comap g).IsInvertible)
    (y : Y) [IsIso (g.stalkMap y)] (hy : y ≠ genericPoint Y) (hgy : g y ≠ genericPoint X) :
    weightedLocalOrder q I hI (g y) = weightedLocalOrder (g ≫ q) (I.comap g) hJ y := by
  let := residueAlgebra q (g y)
  let := residueAlgebra (g ≫ q) y
  unfold weightedLocalOrder
  rw [localOrder_eq_stalkQuotient hdimX I hI (g y) hgy,
    localOrder_eq_stalkQuotient hdimY (I.comap g) hJ y hy]
  obtain ⟨a, _ha, hgen⟩ := hI.exists_mem_nonZeroDivisors_stalkIdeal_eq_span (g y)
  rw [Scheme.IdealSheafData.stalkIdeal_comap, hgen, Ideal.map_span, Set.image_singleton]
  exact SchemeStalkMapLocalOrders.weightedOrder_stalkMap g y q a

/-- EVERY original affine global principal equation computes the SAME native original Cartier weight. -/
theorem weightedLocalOrder_eq_globalSection [IsAffine X] {k : Type u} [Field k]
    (q : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (hI : I.IsInvertible)
    (c : Γ(X, ⊤)) (hc : c ≠ 0) (hgen : I.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {c})
    (x : X) : weightedLocalOrder q I hI x = SchemeRegularSectionOrders.weightedOrder q c x := by
  let : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  unfold weightedLocalOrder SchemeRegularSectionOrders.weightedOrder
  rw [localOrder_eq_ord_of_local_equation I hI ⟨⊤, isAffineOpen_top X⟩ c hc hgen x trivial]

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- The actual original affine comap ideal retains the SAME original pulled global equation. -/
theorem comap_global_equation [IsAffine X] {Y : Scheme.{u}} [IsAffine Y]
    (g : Y ⟶ X) (I : X.IdealSheafData) (c : Γ(X, ⊤))
    (hgen : I.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {c}) :
    (I.comap g).ideal ⟨⊤, isAffineOpen_top Y⟩ = Ideal.span {g.appTop c} := by
  rw [I.comap_ideal_of_affine_opens g ⟨⊤, isAffineOpen_top Y⟩ ⟨⊤, isAffineOpen_top X⟩
    (by simp), hgen, Ideal.map_span, Set.image_singleton]
  congr 2
  have h : g.appLE (⊤ : X.Opens) (⊤ : Y.Opens) (by simp) = g.appTop := by
    simp [Scheme.Hom.appLE]
  exact ConcreteCategory.congr_hom h c

/-- ALL original finite-fibre Cartier orders genuinely scale by the SAME
native original function-field degree even for a singular/nonflat original target. -/
theorem finsum_fibre_comap_of_global_equation [IsAffine X]
    {Y : Scheme.{u}} [IsIntegral Y] {k : Type u} [Field k]
    (g : Y ⟶ X) [IsFinite g] [IsDominant g] (q : X ⟶ Spec (.of k))
    (hdimX : topologicalKrullDim X ≤ 1) (hdimY : topologicalKrullDim Y ≤ 1)
    (I : X.IdealSheafData) (hI : I.IsInvertible) (x : X) (hx : x ≠ genericPoint X)
    (hres : letI := residueAlgebra q x; Module.Finite k (X.residueField x))
    (c : Γ(X, ⊤)) (hc : c ≠ 0) (hgen : I.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {c}) :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
    letI := (DominantFunctionFieldMaps.functionFieldMap g).hom.toAlgebra
    (∑ᶠ y : {y : Y // g y = x}, weightedLocalOrder (g ≫ q) (I.comap g)
      (hI.comap_of_dominant_integral g) y.1) =
      (Module.finrank X.functionField Y.functionField : ℤ) * weightedLocalOrder q I hI x := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  let : IsAffine Y := isAffine_of_isAffineHom g
  let := (DominantFunctionFieldMaps.functionFieldMap g).hom.toAlgebra
  have hgc : g.appTop c ≠ 0 := by
    have hi := SchemeLocalizedFiniteAlgebras.coefficientMap_injective (g ≫ X.isoSpec.hom)
    rw [AffineFiniteFibreOrders.coefficientMap_isoSpec] at hi
    simpa only [map_zero] using hi.ne hc
  rw [weightedLocalOrder_eq_globalSection q I hI c hc hgen x]
  calc
    _ = ∑ᶠ y : {y : Y // g y = x}, SchemeRegularSectionOrders.weightedOrder (g ≫ q) (g.appTop c) y.1 := by
      apply finsum_congr
      intro y
      exact weightedLocalOrder_eq_globalSection (g ≫ q) (I.comap g)
        (hI.comap_of_dominant_integral g) (g.appTop c) hgc (comap_global_equation g I c hgen) y.1
    _ = _ := AffineFiniteFibreOrders.finsum_fibre_eq_functionFieldDegree g q hdimX hdimY x hx hres c hc

end SGPT.Foundations.Envelope.CurveCartierStalkOrders
