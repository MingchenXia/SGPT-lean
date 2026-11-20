import SGPT.Foundations.Schemes.NativeSmoothFunctionFieldDimension

/-!
# Actual smooth relative dimension from the original function field

Blueprint: `smooth-affine-dimension.tex`.  Every original standard-smooth
chart has the dimension forced by the same original function field.  Only
existing smooth-chart and fraction-field APIs are used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.SmoothAffineDimension

open AlgebraicGeometry CategoryTheory Opposite SGPT.Foundations.Schemes

private theorem germ_pointTransport {T : Scheme} {x y : T} (h : x = y)
    (V : T.Opens) (hx : x ∈ V) (hy : y ∈ V) (s : Γ(T, V)) :
    eqToHom (congrArg T.presheaf.stalk h) (T.presheaf.germ V x hx s) =
      T.presheaf.germ V y hy s := by
  cases h
  rfl

/-- Original generic-stalk pullback through an open immersion preserves the original
structural coefficients, rather than merely identifying the two abstract fields. -/
def openFunctionFieldAlgEquiv {k : Type} [Field k] {X Y : Scheme}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Spec (.of k)) (i : Y ⟶ X) [IsOpenImmersion i] :
    letI := schemeFunctionFieldAlgebra f
    letI := schemeFunctionFieldAlgebra (i ≫ f)
    X.functionField ≃ₐ[k] Y.functionField := by
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionFieldAlgebra (i ≫ f)
  let e : X.functionField ≅ Y.functionField :=
    eqToIso (congrArg X.presheaf.stalk (genericPoint_eq_of_isOpenImmersion i).symm) ≪≫
      asIso (i.stalkMap (genericPoint Y))
  refine { e.commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro c
  change i.stalkMap (genericPoint Y)
    (eqToHom (congrArg X.presheaf.stalk (genericPoint_eq_of_isOpenImmersion i).symm)
      (X.presheaf.germ ⊤ (genericPoint X) trivial (schemeGlobalConstants f c))) =
        Y.presheaf.germ ⊤ (genericPoint Y) trivial (schemeGlobalConstants (i ≫ f) c)
  rw [germ_pointTransport (genericPoint_eq_of_isOpenImmersion i).symm]
  refine (i.germ_stalkMap_apply ⊤ (genericPoint Y) trivial (schemeGlobalConstants f c)).trans ?_
  congr 1

/-- Every actual smooth chart has the dimension forced by the SAME original function field. -/
theorem smoothOfRelativeDimension_of_functionField_trdeg
    {k : Type} [Field k] {X : Scheme} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [Smooth f] (n : ℕ)
    (htr : letI := schemeFunctionFieldAlgebra f; Algebra.trdeg k X.functionField = n) :
    SmoothOfRelativeDimension n f := by
  let := schemeFunctionFieldAlgebra f
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hU, V, hV, hx, e, hstd⟩ := Smooth.exists_isStandardSmooth f x
  have hUtop : U = ⊤ := by
    apply top_unique
    intro y _
    exact (Subsingleton.elim y (f x)) ▸ e hx
  subst U
  let := affineChartAlgebra f V
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  have : IsScalarTower k Γ(X, V) X.functionField :=
    schemeFunctionField_affineChartScalarTower f V
  have : IsFractionRing Γ(X, V) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X V hV
  have hsConst : RingHom.IsStandardSmooth ((schemeConstantPresheafMap f).app (op V)).hom := by
    have he := RingHom.IsStandardSmoothOfRelativeDimension.equiv
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    exact hstd.comp (RingHom.IsStandardSmoothOfRelativeDimension.isStandardSmooth 0 _ he)
  have : Algebra.IsStandardSmooth k Γ(X, V) := hsConst
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := Algebra.IsStandardSmooth.out (R := k) (S := Γ(X, V))
  have : Algebra.IsStandardSmoothOfRelativeDimension P.dimension k Γ(X, V) :=
    P.isStandardSmoothOfRelativeDimension rfl
  have hd := nativeStandardSmoothFractionField_trdeg k Γ(X, V) X.functionField P.dimension
  have hdim : P.dimension = n := by
    exact_mod_cast hd.symm.trans htr
  have hstdn : Algebra.IsStandardSmoothOfRelativeDimension n k Γ(X, V) := by
    simpa only [hdim] using
      (inferInstance : Algebra.IsStandardSmoothOfRelativeDimension P.dimension k Γ(X, V))
  refine ⟨⊤, isAffineOpen_top _, V, hV, hx, e, ?_⟩
  have hconst : RingHom.IsStandardSmoothOfRelativeDimension n
      ((schemeConstantPresheafMap f).app (op V)).hom := hstdn
  have hcompose := hconst.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv)
  rw [Nat.add_zero] at hcompose
  change RingHom.IsStandardSmoothOfRelativeDimension n
    (((Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫
      (schemeConstantPresheafMap f).app (op V)).hom) at hcompose
  have hmap : (Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫
      (schemeConstantPresheafMap f).app (op V) = f.appLE ⊤ V e := by
    simp only [schemeConstantPresheafMap, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rfl
  rw [hmap] at hcompose
  exact hcompose

/-- The actual smooth open has the dimension of the SAME original full function field. -/
theorem smoothOpen_relativeDimension_of_functionField_trdeg
    {k : Type} [Field k] {X : Scheme} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (U : X.Opens) [Nonempty U] [Smooth (U.ι ≫ f)] (n : ℕ)
    (htr : letI := schemeFunctionFieldAlgebra f; Algebra.trdeg k X.functionField = n) :
    SmoothOfRelativeDimension n (U.ι ≫ f) := by
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionFieldAlgebra (U.ι ≫ f)
  let e := openFunctionFieldAlgEquiv f U.ι
  apply smoothOfRelativeDimension_of_functionField_trdeg (U.ι ≫ f) n
  exact e.trdeg_eq.symm.trans htr

/-- A smooth model of the original function field has the original smooth dimension. -/
theorem smoothOfRelativeDimension_of_functionField_equiv
    {k : Type} [Field k] {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) [Smooth f] (n : ℕ)
    [SmoothOfRelativeDimension n g]
    (e : letI := schemeFunctionFieldAlgebra f
      letI := schemeFunctionFieldAlgebra g
      X.functionField ≃ₐ[k] Y.functionField) : SmoothOfRelativeDimension n f := by
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionFieldAlgebra g
  apply smoothOfRelativeDimension_of_functionField_trdeg f n
  exact e.trdeg_eq.trans (nativeSmoothFunctionField_trdeg g n)

/-- The graph may be singular away from the chosen open: its SAME original field still
forces the smooth open to have the original variety's relative dimension. -/
theorem smoothOpen_relativeDimension_of_functionField_equiv
    {k : Type} [Field k] {G X : Scheme} [IsIntegral G] [IsIntegral X]
    (f : G ⟶ Spec (.of k)) (U : G.Opens) [Nonempty U] [Smooth (U.ι ≫ f)]
    (g : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n g]
    (e : letI := schemeFunctionFieldAlgebra f
      letI := schemeFunctionFieldAlgebra g
      G.functionField ≃ₐ[k] X.functionField) : SmoothOfRelativeDimension n (U.ι ≫ f) := by
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionFieldAlgebra g
  apply smoothOpen_relativeDimension_of_functionField_trdeg f U n
  exact e.trdeg_eq.trans (nativeSmoothFunctionField_trdeg g n)

end SGPT.NAPotential.SmoothAffineDimension
