import SGPT.Okounkov.SchemeNativeBirationalPrimeCyclePushforward
import SGPT.Projective.BDivNativeHeightOnePointDimension

/-! The cycle classification reduces to the dimension of a source prime closure. -/
set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov

open AlgebraicGeometry CategoryTheory TopologicalSpace
open SGPT.Projective.BDivNov16 SGPT.Projective.NumEq.AlgebraicCurveDegree

private theorem pointDimension_add_coheight_le {X : Scheme.{0}} [IsIntegral X] (x : X) :
    (↑(pointDimension X x + Order.coheight x) : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  let e : X ≃o Specialization X :=
    { Specialization.toEquiv with map_rel_iff' := by intros; rfl }
  have he := Order.height_orderIso e x
  change pointDimension X x = Order.height x at he
  rw [he]
  change (↑(Order.height x + Order.coheight x) : WithBot ℕ∞) ≤
    Order.krullDim (IrreducibleCloseds X)
  rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X)),
    Order.krullDim_eq_iSup_height_add_coheight_of_nonempty, WithBot.coe_le_coe]
  exact le_iSup (fun z : X => Order.height z + Order.coheight z) x

/-- Once the source prime has dimension one below the target total dimension,
equality of actual point dimensions forces the target point to have codimension one. -/
theorem nativePrimeImage_codimOne_of_pointDimension_eq
    {V X : Scheme.{0}} [IsIntegral X] (p : V ⟶ X)
    (v : V) (f : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType (p ≫ f)]
    (hsource : (↑(pointDimension V v + 1) : WithBot ℕ∞) = topologicalKrullDim X)
    (heq : pointDimension X (p v) = pointDimension V v) :
    Order.coheight (p v) = 1 := by
  obtain ⟨n, hn, _⟩ := nativePointDimensionResidue (p ≫ f) v
  have hfin : pointDimension V v ≠ ⊤ := by
    rw [hn]
    exact ENat.natCast_ne_top n
  have hbound := pointDimension_add_coheight_le (p v)
  rw [heq, ← hsource, WithBot.coe_le_coe,
    ENat.add_le_add_iff_left hfin] at hbound
  have hpos : Order.coheight (p v) ≠ 0 := by
    intro hz
    have hg : p v = genericPoint X := by
      let e : X ≃o Specialization X :=
        { Specialization.toEquiv with map_rel_iff' := by intros; rfl }
      have hz' : Order.coheight (e (p v)) = 0 := (Order.coheight_orderIso e (p v)).trans hz
      have hmax : IsMax (e (p v)) := Order.coheight_eq_zero.mp hz'
      have hle : e (p v) ≤ e (genericPoint X) := e.monotone (show p v ≤ (⊤ : X) from le_top)
      exact e.injective (le_antisymm hle (hmax hle))
    have hgeneric : (↑(pointDimension X (genericPoint X)) : WithBot ℕ∞) =
        topologicalKrullDim X := by
      simpa using originalIntegralClosedImmersion_generic_pointDimension (𝟙 X)
    have impossible : (↑(pointDimension V v) : WithBot ℕ∞) =
        ↑(pointDimension V v + 1) := calc
      _ = ↑(pointDimension X (p v)) := congrArg (fun d : ℕ∞ => (d : WithBot ℕ∞)) heq.symm
      _ = topologicalKrullDim X := by rw [hg, hgeneric]
      _ = _ := hsource.symm
    exact (ne_of_lt ((ENat.lt_add_one_iff hfin).2 le_rfl)) (WithBot.coe_inj.mp impossible)
  exact le_antisymm hbound (Order.one_le_iff_ne_zero.mpr hpos)

/-- An isomorphism at the actual generic stalks identifies the total dimensions. -/
theorem nativeBirational_topologicalKrullDim_eq
    {V X : Scheme.{0}} [IsIntegral V] [IsIntegral X] (p : V ⟶ X)
    (hη : p (genericPoint V) = genericPoint X) [IsIso (p.stalkMap (genericPoint V))]
    (f : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType f] [LocallyOfFiniteType (p ≫ f)] :
    topologicalKrullDim V = topologicalKrullDim X := by
  have hV : (↑(pointDimension V (genericPoint V)) : WithBot ℕ∞) =
      topologicalKrullDim V := by
    simpa using originalIntegralClosedImmersion_generic_pointDimension (𝟙 V)
  have hX : (↑(pointDimension X (genericPoint X)) : WithBot ℕ∞) =
      topologicalKrullDim X := by
    simpa using originalIntegralClosedImmersion_generic_pointDimension (𝟙 X)
  have hres := nativeResidueFieldMap_bijective_of_stalkMap_surjective
    p (genericPoint V) (ConcreteCategory.bijective_of_isIso (p.stalkMap (genericPoint V))).surjective
  have hd := nativePointDimension_eq_of_residueFieldMap_bijective p f (genericPoint V) hres
  rw [hη] at hd
  exact hV.symm.trans ((congrArg (fun d : ℕ∞ => (d : WithBot ℕ∞)) hd).trans hX)

/-- The two algebraic outcomes are exhaustive once the source dimension formula holds.
The coefficient is computed by the already-checked native cycle theorems. -/
theorem nativeBirational_primeCycle_classification_of_source_dimension
    {V X : Scheme.{0}} [IsIntegral V] [IsIntegral X] (p : V ⟶ X) [IsProper p]
    (hη : p (genericPoint V) = genericPoint X) [IsIso (p.stalkMap (genericPoint V))]
    (v : V) (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
    [IsSeparated f] [QuasiCompact f] [IsLocallyNoetherian X]
    [LocallyOfFiniteType f] [LocallyOfFiniteType (p ≫ f)]
    (hsource : (↑(pointDimension V v + 1) : WithBot ℕ∞) = topologicalKrullDim V) :
    (pointDimension X (p v) < pointDimension V v ∧
      AlgebraicCycle.map p (pointDimension V) (pointDimension X) (schemePointCycle v 1) = 0) ∨
    (Order.coheight (p v) = 1 ∧ pointDimension X (p v) = pointDimension V v ∧
      AlgebraicCycle.map p (pointDimension V) (pointDimension X) (schemePointCycle v 1) =
        schemePointCycle (p v) 1) := by
  rcases lt_or_eq_of_le (nativePointDimension_image_le p f v) with hdrop | heq
  · exact Or.inl ⟨hdrop, schemePointCycle_map_single_eq_zero_of_dimension_drop p v hdrop⟩
  · have htotal := nativeBirational_topologicalKrullDim_eq p hη f
    have hx := nativePrimeImage_codimOne_of_pointDimension_eq p v f (hsource.trans htotal) heq
    refine Or.inr ⟨hx, heq, ?_⟩
    simp only [schemePointCycle_map_single,
      nativeBirational_mapCoeff_eq_one_of_smooth_codimOne_of_finiteType p hη v f n hx,
      Nat.cast_one, mul_one]

/-- A height-one source prime in a smooth birational transition either loses dimension
and pushes to zero or maps to a height-one prime with coefficient one. -/
theorem nativeBirational_primeCycle_classification
    {V X : Scheme.{0}} [IsIntegral V] [IsIntegral X] (p : V ⟶ X) [IsProper p]
    (hη : p (genericPoint V) = genericPoint X) [IsIso (p.stalkMap (genericPoint V))]
    (v : V) (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
    [IsSeparated f] [QuasiCompact f] [IsLocallyNoetherian X]
    [LocallyOfFiniteType f] [LocallyOfFiniteType (p ≫ f)]
    (hv : Order.coheight v = 1) :
    (pointDimension X (p v) < pointDimension V v ∧
      AlgebraicCycle.map p (pointDimension V) (pointDimension X) (schemePointCycle v 1) = 0) ∨
    (Order.coheight (p v) = 1 ∧ pointDimension X (p v) = pointDimension V v ∧
      AlgebraicCycle.map p (pointDimension V) (pointDimension X) (schemePointCycle v 1) =
        schemePointCycle (p v) 1) :=
  nativeBirational_primeCycle_classification_of_source_dimension p hη v f n
    (nativePointDimension_add_one_eq_topologicalKrullDim_of_coheight_one (p ≫ f) v hv)

end SGPT.Okounkov
