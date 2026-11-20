import SGPT.NAPotential.GraphDivisorOrderTransport

/-!
# Original divisor order under native affine and open chart maps

Complete blueprint: `open-divisor-order-transport.tex`. All field maps
are constructed from the original structure-sheaf stalk maps.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.OpenDivisorOrderTransport

open AlgebraicGeometry CategoryTheory IsLocalRing WithZero
open SGPT.NAPotential.Berkovich GraphDivisorOrderTransport

/-- The native affine field coefficient map factors through every original stalk. -/
theorem spec_stalkFunctionField_scalarTower (B : CommRingCat) [IsDomain B]
    (z : Spec B) :
    letI : Algebra B ((Spec B).presheaf.stalk z) := StructureSheaf.stalkAlgebra B z
    IsScalarTower B ((Spec B).presheaf.stalk z) (Spec B).functionField := by
  let : Algebra B ((Spec B).presheaf.stalk z) := StructureSheaf.stalkAlgebra B z
  apply IsScalarTower.of_algebraMap_eq'
  exact congrArg CommRingCat.Hom.hom
    (StructureSheaf.toStalk_stalkSpecializes
      ((genericPoint_spec (Spec B)).specializes trivial)).symm

/-- The original order/fraction data manufacture the ACTUAL native affine centre,
its DVR stalk, and the normalized original divisor order on its actual function field. -/
theorem exists_specOrder_of_orderFractions {X : Scheme.{0}} (D : PrimeDivisorOver X)
    (B : Subring (X.residueField (D.π (genericPoint D.Y)))) [IsNoetherianRing B]
    (hB : ∀ g ∈ B, g ≠ 0 → 0 ≤ D.ord g)
    (hfrac : ∀ g : X.residueField (D.π (genericPoint D.Y)), g ≠ 0 → 0 ≤ D.ord g →
      ∃ a ∈ B, ∃ c ∈ B, c ≠ 0 ∧ D.ord c = 0 ∧ g * c = a) :
    ∃ i : B →+* D.Y.presheaf.stalk D.point,
      (∀ b : B, algebraMap (D.Y.presheaf.stalk D.point) D.Y.functionField (i b) =
        D.pullback b) ∧
      ∃ z : Spec (.of B), z.asIdeal = (maximalIdeal _).comap i ∧
        IsDiscreteValuationRing ((Spec (.of B)).presheaf.stalk z) ∧
        Order.coheight z = 1 ∧
        ∃ e : (Spec (.of B)).functionField ≃+* D.Y.functionField,
          (∀ b : B, e (StructureSheaf.toStalk B (genericPoint (Spec (.of B))) b) =
            D.pullback b) ∧
          ∀ g : X.residueField (D.π (genericPoint D.Y)),
            D.ord g = Scheme.ord (e.symm (D.pullback g)) z := by
  obtain ⟨i, hi, hloc⟩ := exists_primeLocalization_of_orderFractions D B hB hfrac
  let C : CommRingCat := .of B
  let : IsDomain C := inferInstanceAs (IsDomain B)
  let : IsNoetherianRing C := inferInstanceAs (IsNoetherianRing B)
  let : Algebra C (Spec C).functionField :=
    (StructureSheaf.toStalk C (genericPoint (Spec C))).hom.toAlgebra
  let : Algebra C (D.Y.presheaf.stalk D.point) := i.toAlgebra
  let : Algebra C D.Y.functionField := (D.pullback.comp B.subtype).toAlgebra
  let : IsScalarTower C (D.Y.presheaf.stalk D.point) D.Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun b => (hi b).symm
  let p : Ideal C := (maximalIdeal (D.Y.presheaf.stalk D.point)).comap i
  let : IsLocalization.AtPrime (D.Y.presheaf.stalk D.point) p := hloc
  let z : Spec C := ⟨p, inferInstance⟩
  let : Algebra C ((Spec C).presheaf.stalk z) := StructureSheaf.stalkAlgebra C z
  let : IsLocalization.AtPrime ((Spec C).presheaf.stalk z) p :=
    StructureSheaf.IsLocalization.to_stalk C z
  let : IsScalarTower C ((Spec C).presheaf.stalk z) (Spec C).functionField :=
    spec_stalkFunctionField_scalarTower C z
  obtain ⟨hDVR, hz, e, he, hord⟩ := exists_modelOrder D z p
  exact ⟨i, hi, z, rfl, hDVR, hz, e, he, hord⟩

section OpenImmersion

variable {S U : Scheme.{0}} [IsIntegral S] [IsIntegral U]
  (j : U ⟶ S) [IsOpenImmersion j]

/-- The original generic stalk map of an actual open immersion. -/
def openFunctionFieldEquiv : S.functionField ≃+* U.functionField :=
  (eqToIso (congrArg S.presheaf.stalk (genericPoint_eq_of_isOpenImmersion j).symm) ≪≫
    asIso (j.stalkMap (genericPoint U))).commRingCatIsoToRingEquiv

private theorem pointTransport_eq_stalkSpecializes {T : Scheme.{0}} {x y : T}
    (h : x = y) :
    eqToHom (congrArg T.presheaf.stalk h.symm) =
      T.presheaf.stalkSpecializes (specializes_of_eq h) := by
  cases h
  simp

/-- The full ORIGINAL stalk coefficient square is proved by specialization naturality. -/
theorem openFunctionField_stalkCoefficients (u : U) :
    CommRingCat.ofHom (algebraMap (S.presheaf.stalk (j u)) S.functionField) ≫
      CommRingCat.ofHom (openFunctionFieldEquiv j).toRingHom =
    j.stalkMap u ≫
      CommRingCat.ofHom (algebraMap (U.presheaf.stalk u) U.functionField) := by
  change S.presheaf.stalkSpecializes (genericPoint_specializes (j u)) ≫
    (eqToHom (congrArg S.presheaf.stalk (genericPoint_eq_of_isOpenImmersion j).symm) ≫
      j.stalkMap (genericPoint U)) =
    j.stalkMap u ≫ U.presheaf.stalkSpecializes (genericPoint_specializes u)
  rw [pointTransport_eq_stalkSpecializes (genericPoint_eq_of_isOpenImmersion j), ← Category.assoc,
    TopCat.Presheaf.stalkSpecializes_comp]
  exact j.stalkSpecializes_stalkMap (genericPoint U) u (genericPoint_specializes u)

/-- Every rational function, including zero, retains its normalized native scheme order
under the actual generic-stalk pullback to a nonempty open. -/
theorem ord_openFunctionFieldEquiv [IsLocallyNoetherian S] [IsLocallyNoetherian U]
    (u : U) (g : S.functionField) :
    Scheme.ord (openFunctionFieldEquiv j g) u = Scheme.ord g (j u) := by
  have hco : Order.coheight (j u) = Order.coheight u := coheight_eq_of_isOpenImmersion j
  by_cases hz : Order.coheight (j u) = 1
  · have hu : Order.coheight u = 1 := hco.symm.trans hz
    let : Ring.KrullDimLE 1 (S.presheaf.stalk (j u)) := krullDimLE_of_coheight_le hz.le
    let : Ring.KrullDimLE 1 (U.presheaf.stalk u) := krullDimLE_of_coheight_le hu.le
    let e := (asIso (j.stalkMap u)).commRingCatIsoToRingEquiv
    have hcoeff (a : S.presheaf.stalk (j u)) :
        openFunctionFieldEquiv j (algebraMap _ S.functionField a) =
          algebraMap _ U.functionField (e a) :=
      congrArg (fun f : S.presheaf.stalk (j u) ⟶ U.functionField => f a)
        (openFunctionField_stalkCoefficients j u)
    have hnorm := ordFrac_ringEquiv e (openFunctionFieldEquiv j).toRingHom hcoeff g
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hu,
      Scheme.ord_eq_ordHom_of_coheight_eq_one hz]
    exact congrArg (fun v : ℤᵐ⁰ => Multiplicative.toAdd (v.unzeroD 1)) hnorm
  · have hu : Order.coheight u ≠ 1 := by rwa [← hco]
    rw [Scheme.ord_eq_zero_of_coheight_neq_one hu, Scheme.ord_eq_zero_of_coheight_neq_one hz]

end OpenImmersion

/-- Original graph order/fraction data produce order comparison on EVERY native open
neighbourhood of the constructed centre, hence on the actual smooth principal open. -/
theorem exists_specOrder_on_open {X : Scheme.{0}} (D : PrimeDivisorOver X)
    (B : Subring (X.residueField (D.π (genericPoint D.Y)))) [IsNoetherianRing B]
    (hB : ∀ g ∈ B, g ≠ 0 → 0 ≤ D.ord g)
    (hfrac : ∀ g : X.residueField (D.π (genericPoint D.Y)), g ≠ 0 → 0 ≤ D.ord g →
      ∃ a ∈ B, ∃ c ∈ B, c ≠ 0 ∧ D.ord c = 0 ∧ g * c = a) :
    ∃ (i : B →+* D.Y.presheaf.stalk D.point) (z : Spec (.of B)),
      z.asIdeal = (maximalIdeal _).comap i ∧
      IsDiscreteValuationRing ((Spec (.of B)).presheaf.stalk z) ∧
      Order.coheight z = 1 ∧
      ∀ (V : (Spec (.of B)).Opens) (hzV : z ∈ V),
        letI : Nonempty V := ⟨⟨z, hzV⟩⟩
        ∃ eV : V.toScheme.functionField ≃+* D.Y.functionField,
          IsDiscreteValuationRing (V.toScheme.presheaf.stalk ⟨z, hzV⟩) ∧
          @Order.coheight V.toScheme (specializationPreorder V.toScheme) ⟨z, hzV⟩ = 1 ∧
          ∀ g : X.residueField (D.π (genericPoint D.Y)),
            D.ord g = Scheme.ord (eV.symm (D.pullback g)) (⟨z, hzV⟩ : V.toScheme) := by
  obtain ⟨i, -, z, hzi, hDVR, hz, e, -, hord⟩ :=
    exists_specOrder_of_orderFractions D B hB hfrac
  refine ⟨i, z, hzi, hDVR, hz, fun V hzV => ?_⟩
  let : Nonempty V := ⟨⟨z, hzV⟩⟩
  let u : V.toScheme := ⟨z, hzV⟩
  let : IsDiscreteValuationRing ((Spec (.of B)).presheaf.stalk z) := hDVR
  let : IsDiscreteValuationRing ((Spec (.of B)).presheaf.stalk (V.ι u)) := by
    change IsDiscreteValuationRing ((Spec (.of B)).presheaf.stalk z)
    exact hDVR
  let : IsDiscreteValuationRing (V.toScheme.presheaf.stalk u) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (asIso (V.ι.stalkMap u)).commRingCatIsoToRingEquiv
  let eV := (openFunctionFieldEquiv V.ι).symm.trans e
  refine ⟨eV, inferInstance, coheight_eq_one_of_stalk_dvr u, fun g => ?_⟩
  rw [hord g]
  exact (ord_openFunctionFieldEquiv V.ι u (e.symm (D.pullback g))).symm

section OriginalFieldDictionary

open SGPT.NAPotential.AlgPrimes3.PrimeDivisorOver'

variable {X : Scheme.{0}} [IsIntegral X] (D : PrimeDivisorOver X)

private def genericResidueEquiv : X.functionField ≃+* X.residueField (genericPoint X) :=
  RingEquiv.ofBijective (X.residue (genericPoint X)).hom
    ⟨(X.residue (genericPoint X)).hom.injective, X.residue_surjective _⟩

/-- Canonical dictionary between the ORIGINAL divisor residue field and the actual
function field used by the original global Segre graph. -/
def originalFunctionFieldEquiv :
    X.residueField (D.π (genericPoint D.Y)) ≃+* X.functionField :=
  (eqToIso (congrArg X.residueField D.isGenericPoint_image)).commRingCatIsoToRingEquiv.trans
    genericResidueEquiv.symm

private theorem residueGerm_pointTransport {T : Scheme.{0}} {x y : T} (h : x = y)
    (V : T.Opens) (hx : x ∈ V) (hy : y ∈ V) (a : Γ(T, V)) :
    eqToHom (congrArg T.residueField h)
        ((T.residue x).hom (T.presheaf.germ V x hx a)) =
      (T.residue y).hom (T.presheaf.germ V y hy a) := by
  cases h
  rfl

/-- The dictionary preserves EVERY original affine coefficient, including the sections
coming from the original structural complex constants. -/
theorem originalFunctionFieldEquiv_sectionToField
    (V : X.Opens) (hV : D.π (genericPoint D.Y) ∈ V) [Nonempty V] (a : Γ(X, V)) :
    originalFunctionFieldEquiv D (sectionToField D V hV a) =
      X.germToFunctionField V a := by
  apply genericResidueEquiv.injective
  change genericResidueEquiv
      (genericResidueEquiv.symm
        (eqToHom (congrArg X.residueField D.isGenericPoint_image)
          ((X.residue (D.π (genericPoint D.Y))).hom (X.presheaf.germ V _ hV a)))) = _
  rw [RingEquiv.apply_symm_apply]
  exact residueGerm_pointTransport D.isGenericPoint_image V hV
    (D.isGenericPoint_image ▸ hV) a

/-- The original field dictionary is an algebra isomorphism for the SAME original
affine section action on both actual fields. -/
def originalFunctionFieldAlgEquiv
    (V : X.Opens) (hV : D.π (genericPoint D.Y) ∈ V) [Nonempty V] :
    letI := (sectionToField D V hV).toAlgebra
    X.residueField (D.π (genericPoint D.Y)) ≃ₐ[Γ(X, V)] X.functionField := by
  let := (sectionToField D V hV).toAlgebra
  exact { originalFunctionFieldEquiv D with
    commutes' := originalFunctionFieldEquiv_sectionToField D V hV }

/-- The canonical ORIGINAL field dictionary restricts to the literal graph subalgebras
in the divisor residue field and the actual `X.functionField`, respectively. -/
def originalGraphAlgebraEquiv
    (V : X.Opens) (hV : D.π (genericPoint D.Y) ∈ V) [Nonempty V]
    {σ : Type} (b : σ → X.residueField (D.π (genericPoint D.Y))) :
    letI := (sectionToField D V hV).toAlgebra
    Algebra.adjoin Γ(X, V) (Set.range b) ≃ₐ[Γ(X, V)]
      Algebra.adjoin Γ(X, V) (Set.range fun i => originalFunctionFieldEquiv D (b i)) := by
  let := (sectionToField D V hV).toAlgebra
  let e := originalFunctionFieldAlgEquiv D V hV
  exact (Subalgebra.equivMapOfInjective _ e.toAlgHom e.injective).trans
    (Subalgebra.equivOfEq _ _ (by rw [AlgHom.map_adjoin, ← Set.range_comp']; rfl))

/-- The restricted graph-algebra map is literally the SAME original field map. -/
theorem originalGraphAlgebraEquiv_coe
    (V : X.Opens) (hV : D.π (genericPoint D.Y) ∈ V) [Nonempty V]
    {σ : Type} (b : σ → X.residueField (D.π (genericPoint D.Y))) :
    letI := (sectionToField D V hV).toAlgebra
    ∀ a : Algebra.adjoin Γ(X, V) (Set.range b),
      (originalGraphAlgebraEquiv D V hV b a : X.functionField) =
        originalFunctionFieldEquiv D a := by
  intro a
  rfl

omit [IsIntegral X] in
/-- The structural Noetherian hypothesis of the native graph order producer is proved
for the actual finitely generated adjoin over an original affine section ring. -/
theorem isNoetherian_graphAlgebra [IsLocallyNoetherian X]
    (V : X.Opens) (hVa : IsAffineOpen V) (hV : D.π (genericPoint D.Y) ∈ V)
    {σ : Type} [Finite σ] (b : σ → X.residueField (D.π (genericPoint D.Y))) :
    letI := (sectionToField D V hV).toAlgebra
    IsNoetherianRing (Algebra.adjoin Γ(X, V) (Set.range b)) := by
  let := (sectionToField D V hV).toAlgebra
  let : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hVa⟩
  let : Algebra.FiniteType Γ(X, V) (Algebra.adjoin Γ(X, V) (Set.range b)) :=
    Algebra.FiniteType.adjoin_of_finite (Set.finite_range b)
  exact Algebra.FiniteType.isNoetherianRing Γ(X, V) _

end OriginalFieldDictionary

end SGPT.NAPotential.OpenDivisorOrderTransport
