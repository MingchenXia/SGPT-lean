import SGPT.Projective.BDivNov16OriginalPointClosureHeight
import SGPT.Projective.BDivNov16FiniteTypeFractionDimension
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.Topology.KrullDimension

/-! The dimension of an actual point is read from its original residue field.
The proof uses the native vanishing-ideal subscheme of the point closure.
The finite-type dimension and point-closure arguments follow the existing
BDivNov16 producers, with the required scalar and closure constructions
written using Mathlib's scheme API. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.BDivNov16
universe u
open AlgebraicGeometry CategoryTheory Topology TopologicalSpace
open SGPT.Projective.NumEq.AlgebraicCurveDegree

section Scalars

variable {X Y : Scheme.{0}} {k : Type} [Field k]

/-- For `f : X ⟶ Spec k`, the `k`-algebra structure on the sections of `X` over an open `U`, by
`k ≅ Γ(Spec k, ⊤) → Γ(X, U)` (`Scheme.ΓSpecIso` followed by `f.appLE ⊤ U`): the ring `S` of an
affine open `U = Spec S` becomes a `k`-algebra. Not an instance: the structure depends on `f`. -/
@[instance_reducible]
def nativeAffineChartAlgebra (f : X ⟶ Spec (.of k)) (U : X.Opens) :
    Algebra k Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top).hom.toAlgebra

private theorem algebraMap_sectionsAlgebra (f : X ⟶ Spec (.of k)) (U : X.Opens) :
    letI := nativeAffineChartAlgebra f U
    algebraMap k Γ(X, U) = ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top).hom :=
  rfl

/-- For `f : X ⟶ Spec k` locally of finite type and `U` an affine open, `Γ(X, U)` is a
`k`-algebra of finite type (for the structure `nativeAffineChartAlgebra`). -/
theorem nativeAffineChartAlgebra_finiteType (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    {U : X.Opens} (hU : IsAffineOpen U) :
    letI := nativeAffineChartAlgebra f U
    Algebra.FiniteType k Γ(X, U) := by
  let := nativeAffineChartAlgebra f U
  exact (f.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
    (RingHom.FiniteType.of_surjective (Scheme.ΓSpecIso (.of k)).inv.hom
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)

/-- The `k`-algebra structure on the stalk `𝒪_{X,x}` induced by `f : X ⟶ Spec k`, through
`k ≅ Γ(Spec k, ⊤) → Γ(X, f⁻¹ ⊤) → 𝒪_{X,x}`. Not an instance: it depends on `f`. -/
@[instance_reducible]
private def stalkAlgebra (f : X ⟶ Spec (.of k)) (x : X) :
    Algebra k (X.presheaf.stalk x) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.app ⊤ ≫
    X.presheaf.germ (f ⁻¹ᵁ ⊤) x (show f x ∈ (⊤ : (Spec (.of k)).Opens) from trivial)).hom.toAlgebra

private theorem algebraMap_stalkAlgebra (f : X ⟶ Spec (.of k)) (x : X) :
    letI := stalkAlgebra f x
    algebraMap k (X.presheaf.stalk x) = ((Scheme.ΓSpecIso (.of k)).inv ≫ f.app ⊤ ≫
      X.presheaf.germ (f ⁻¹ᵁ ⊤) x (show f x ∈ (⊤ : (Spec (.of k)).Opens) from trivial)).hom :=
  rfl

/-- Through any open `U ∋ x`, the `k`-algebra structure of `Γ(X, U)` followed by the germ map is
the `k`-algebra structure of the stalk. -/
private theorem germ_comp_algebraMap_sectionsAlgebra (f : X ⟶ Spec (.of k)) (U : X.Opens)
    {x : X} (hx : x ∈ U) :
    letI := nativeAffineChartAlgebra f U
    letI := stalkAlgebra f x
    (X.presheaf.germ U x hx).hom.comp (algebraMap k Γ(X, U)) =
      algebraMap k (X.presheaf.stalk x) := by
  rw [algebraMap_sectionsAlgebra, algebraMap_stalkAlgebra,
    ← CommRingCat.hom_comp]
  congr 1
  change (Scheme.ΓSpecIso (.of k)).inv ≫ (f.app ⊤ ≫ X.presheaf.map (homOfLE _).op) ≫
    X.presheaf.germ U x hx = _
  rw [Category.assoc, TopCat.Presheaf.germ_res]

/-- The scalar tower `k → Γ(X, U) → 𝒪_{X,x}` for the structures induced by `f`. -/
private theorem isScalarTower_sectionsAlgebra_stalk (f : X ⟶ Spec (.of k)) (U : X.Opens)
    {x : X} (hx : x ∈ U) :
    letI := nativeAffineChartAlgebra f U
    letI := stalkAlgebra f x
    letI := X.presheaf.algebra_section_stalk ⟨x, hx⟩
    IsScalarTower k Γ(X, U) (X.presheaf.stalk x) :=
  letI := nativeAffineChartAlgebra f U
  letI := stalkAlgebra f x
  letI := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  IsScalarTower.of_algebraMap_eq' (germ_comp_algebraMap_sectionsAlgebra f U hx).symm

/-- The `k`-algebra structure of `𝒪_{Y,y}` induced by `f ≫ fX` is the one of `𝒪_{X, f y}` induced
by `fX` followed by the stalk map of `f`. -/
private theorem stalkMap_comp_algebraMap_stalkAlgebra (fX : X ⟶ Spec (.of k)) (f : Y ⟶ X)
    (y : Y) :
    letI := stalkAlgebra fX (f y)
    letI := stalkAlgebra (f ≫ fX) y
    (f.stalkMap y).hom.comp (algebraMap k (X.presheaf.stalk (f y))) =
      algebraMap k (Y.presheaf.stalk y) := by
  refine RingHom.ext fun c => ?_
  exact Scheme.Hom.germ_stalkMap_apply f (fX ⁻¹ᵁ ⊤) y (show f y ∈ fX ⁻¹ᵁ ⊤ from trivial)
    (fX.app ⊤ ((Scheme.ΓSpecIso (.of k)).inv c))

end Scalars

/-- The residue-field algebra induced by the original structure morphism. -/
@[instance_reducible]
def nativeStructureResidueAlgebra {k : Type} [Field k] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of k)) (x : X) : Algebra k (X.residueField x) :=
  letI := stalkAlgebra f x
  ((X.residue x).hom.comp (algebraMap k (X.presheaf.stalk x))).toAlgebra

/-- The actual subscheme of a native vanishing ideal is reduced. -/
private theorem isReduced_vanishingIdeal_subscheme {X : Scheme.{u}}
    (Z : TopologicalSpace.Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  refine @IsReduced.of_openCover _ I.subschemeCover.openCover ?_
  intro U
  let V : X.affineOpens := U
  have hr : (I.ideal V).IsRadical := by
    dsimp only [I]
    rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  let : _root_.IsReduced (Γ(X, V.1) ⧸ I.ideal V) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp hr
  change IsReduced (Spec (.of (Γ(X, V.1) ⧸ I.ideal V)))
  infer_instance

/-- The canonical original subtype point on the literal reduced point closure. -/
private def pointClosureLift {X : Scheme.{u}} (eta : X) :
    (Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({eta} : Set X), isClosed_closure⟩ : TopologicalSpace.Closeds X)).subscheme :=
  ⟨eta, by
    change eta ∈ (↑(Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({eta} : Set X), isClosed_closure⟩ : TopologicalSpace.Closeds X)).support : Set X)
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    change eta ∈ closure ({eta} : Set X)
    exact subset_closure (Set.mem_singleton eta)⟩

/-- The native inclusion sends the canonical lift to the same original point. -/
private theorem pointClosureLift_image {X : Scheme.{u}} (eta : X) :
    (Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({eta} : Set X), isClosed_closure⟩ : TopologicalSpace.Closeds X)).subschemeι
        (pointClosureLift eta) = eta := rfl

/-- The same canonical lift is generic in the whole literal reduced point closure. -/
private theorem isGenericPoint_pointClosureLift {X : Scheme.{u}} (eta : X) :
    IsGenericPoint (pointClosureLift eta)
      (Set.univ : Set (Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ({eta} : Set X), isClosed_closure⟩ : TopologicalSpace.Closeds X)).subscheme) := by
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure ({eta} : Set X), isClosed_closure⟩ : TopologicalSpace.Closeds X)
  let z : I.support := pointClosureLift eta
  have hz : IsGenericPoint z (Set.univ : Set I.support) := by
    change closure ({z} : Set I.support) = Set.univ
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, Set.image_singleton]
    apply Set.eq_univ_of_forall
    intro y
    change y.val ∈ closure ({eta} : Set X)
    have hs : (↑I.support : Set X) = closure ({eta} : Set X) :=
      Scheme.IdealSheafData.coe_support_vanishingIdeal _
    have hy : y.val ∈ (↑I.support : Set X) := y.property
    exact Eq.mp (congrArg (fun S : Set X => y.val ∈ S) hs) hy
  exact hz

/-- The actual native reduced closure of any original point is integral. -/
private theorem isIntegral_pointClosure {X : Scheme.{u}} (eta : X) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({eta} : Set X), isClosed_closure⟩ : TopologicalSpace.Closeds X)).subscheme := by
  let := isReduced_vanishingIdeal_subscheme
    (⟨closure ({eta} : Set X), isClosed_closure⟩ : TopologicalSpace.Closeds X)
  let : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({eta} : Set X), isClosed_closure⟩ : TopologicalSpace.Closeds X)).subscheme :=
    (irreducibleSpace_def _).mpr (isGenericPoint_pointClosureLift eta).isIrreducible
  exact isIntegral_of_irreducibleSpace_of_isReduced _

private theorem actualAffineDimension {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (U : X.affineOpens) [Nonempty U.1] :
    letI := stalkAlgebra f (genericPoint X)
    ∃ n : ℕ, ringKrullDim Γ(X,U.1)=n ∧ Algebra.trdeg k X.functionField=n := by
  let := nativeAffineChartAlgebra f U.1
  let := stalkAlgebra f (genericPoint X)
  let : IsScalarTower k Γ(X,U.1) X.functionField :=
    isScalarTower_sectionsAlgebra_stalk f U.1
      (((genericPoint_spec X).mem_open_set_iff U.1.isOpen).mpr (by simpa using ‹Nonempty U.1›))
  let : Algebra.FiniteType k Γ(X,U.1) := nativeAffineChartAlgebra_finiteType f U.2
  let : IsFractionRing Γ(X,U.1) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  exact actualFiniteTypeFractionDimension k Γ(X,U.1) X.functionField

private theorem actualDimension_le_affine (X : Scheme.{0}) (d : ℕ)
    (h : ∀ U : X.affineOpens, Nonempty U.1 → ringKrullDim Γ(X,U.1) ≤ d) :
    topologicalKrullDim X ≤ d := by
  change Order.krullDim (IrreducibleCloseds X) ≤ d
  rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X)),
    Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun x => ?_
  obtain ⟨_,⟨U,hU,rfl⟩,hx,-⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (⊤ : X.Opens) from trivial)
      (⊤ : X.Opens).isOpen
  obtain ⟨z,hz⟩ : x ∈ Set.range hU.fromSpec := by rwa [hU.range_fromSpec]
  rw [←hz,coheight_eq_of_isOpenImmersion hU.fromSpec]
  have hdim : topologicalKrullDim (Spec Γ(X,U)) ≤ d := by
    change topologicalKrullDim (PrimeSpectrum Γ(X,U)) ≤ d
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact h ⟨U,hU⟩ ⟨⟨x,hx⟩⟩
  have ho : Order.krullDim (Spec Γ(X,U)) ≤ d := by
    rw [←Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Spec Γ(X,U)))]
    exact hdim
  exact (Order.coheight_le_krullDim z).trans ho

private theorem nativeFiniteTypeIntegralDimension {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    letI := stalkAlgebra f (genericPoint X)
    ∃ n : ℕ, topologicalKrullDim X=n ∧ Algebra.trdeg k X.functionField=n := by
  let := stalkAlgebra f (genericPoint X)
  obtain ⟨_,⟨U,hU,rfl⟩,hx,-⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show genericPoint X ∈ (⊤ : X.Opens) from trivial) (⊤ : X.Opens).isOpen
  let : Nonempty U := ⟨⟨genericPoint X,hx⟩⟩
  obtain ⟨n,hd,htr⟩ := actualAffineDimension f ⟨U,hU⟩
  refine ⟨n,le_antisymm ?_ ?_,htr⟩
  · apply actualDimension_le_affine X n
    intro V hV
    let := hV
    obtain ⟨m,hm,hmt⟩ := actualAffineDimension f V
    have hmn : m=n := by exact_mod_cast hmt.symm.trans htr
    exact (hm.trans (congrArg (fun a : ℕ => (a : WithBot ℕ∞)) hmn)).le
  · have hle := hU.fromSpec.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
    change topologicalKrullDim (PrimeSpectrum Γ(X,U)) ≤ topologicalKrullDim X at hle
    rwa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,hd] at hle

/-- Every nonempty affine chart of the original integral finite-type scheme has the total
dimension, using the common transcendence degree of its actual function field. -/
theorem nativeTopologicalKrullDim_eq_affine {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] {U : X.Opens}
    (hU : IsAffineOpen U) [Nonempty U] :
    topologicalKrullDim X = ringKrullDim Γ(X, U) := by
  let := stalkAlgebra f (genericPoint X)
  obtain ⟨n, hd, htr⟩ := nativeFiniteTypeIntegralDimension f
  obtain ⟨m, hdU, htrU⟩ := actualAffineDimension f ⟨U, hU⟩
  have he : n = m := by exact_mod_cast htr.symm.trans htrU
  rw [hd, hdU, he]

/-- The map of original residue fields is linear over the base field. -/
def nativeResidueAlgHom {Z X : Scheme.{0}} (i : Z ⟶ X)
    {k : Type} [Field k] (f : X ⟶ Spec (.of k)) (z : Z) :
    letI := nativeStructureResidueAlgebra f (i z)
    letI := nativeStructureResidueAlgebra (i ≫ f) z
    X.residueField (i z) →ₐ[k] Z.residueField z := by
  letI := nativeStructureResidueAlgebra f (i z)
  letI := nativeStructureResidueAlgebra (i ≫ f) z
  refine { (i.residueFieldMap z).hom with commutes' := ?_ }
  intro c
  let := stalkAlgebra f (i z)
  let := stalkAlgebra (i ≫ f) z
  change i.residueFieldMap z (X.residue (i z) (algebraMap k (X.presheaf.stalk (i z)) c)) =
    Z.residue z (algebraMap k (Z.presheaf.stalk z) c)
  have h := congrArg (fun q => q (algebraMap k (X.presheaf.stalk (i z)) c))
    (Scheme.residue_residueFieldMap i z)
  have hs := RingHom.congr_fun (stalkMap_comp_algebraMap_stalkAlgebra f i z) c
  change i.stalkMap z (algebraMap k (X.presheaf.stalk (i z)) c) =
    algebraMap k (Z.presheaf.stalk z) c at hs
  change i.residueFieldMap z (X.residue (i z) (algebraMap k (X.presheaf.stalk (i z)) c)) =
    Z.residue z (i.stalkMap z (algebraMap k (X.presheaf.stalk (i z)) c)) at h
  exact h.trans (congrArg (Z.residue z) hs)

def nativeResidueAlgEquivOfBijective {Z X : Scheme.{0}} (i : Z ⟶ X)
    {k : Type} [Field k] (f : X ⟶ Spec (.of k)) (z : Z)
    (hb : Function.Bijective (i.residueFieldMap z)) :
    letI := nativeStructureResidueAlgebra f (i z)
    letI := nativeStructureResidueAlgebra (i ≫ f) z
    X.residueField (i z) ≃ₐ[k] Z.residueField z := by
  letI := nativeStructureResidueAlgebra f (i z)
  letI := nativeStructureResidueAlgebra (i ≫ f) z
  let α := nativeResidueAlgHom i f z
  exact { RingEquiv.ofBijective α.toRingHom hb with commutes' := α.commutes }

/-- Surjectivity on the actual stalk gives an isomorphism on the actual residue fields. -/
theorem nativeResidueFieldMap_bijective_of_stalkMap_surjective
    {Z X : Scheme.{0}} (i : Z ⟶ X) (z : Z)
    (hsurj : Function.Surjective (i.stalkMap z).hom) :
    Function.Bijective (i.residueFieldMap z) := by
  refine ⟨(i.residueFieldMap z).hom.injective, ?_⟩
  intro c
  obtain ⟨t, ht⟩ := Z.residue_surjective z c
  obtain ⟨a, ha⟩ := hsurj t
  refine ⟨X.residue (i z) a, ?_⟩
  have h := congrArg (fun q => q a) (Scheme.residue_residueFieldMap i z)
  change i.residueFieldMap z (X.residue (i z) a) = Z.residue z (i.stalkMap z a) at h
  rwa [ha, ht] at h

private def genericFieldResidueAlgEquiv {Z : Scheme.{0}} [IsIntegral Z]
    {k : Type} [Field k] (g : Z ⟶ Spec (.of k)) :
    letI := stalkAlgebra g (genericPoint Z)
    letI := nativeStructureResidueAlgebra g (genericPoint Z)
    Z.functionField ≃ₐ[k] Z.residueField (genericPoint Z) := by
  letI := stalkAlgebra g (genericPoint Z)
  letI := nativeStructureResidueAlgebra g (genericPoint Z)
  refine {RingEquiv.ofBijective (Z.residue (genericPoint Z)).hom
    ⟨(Z.residue (genericPoint Z)).hom.injective,Z.residue_surjective (genericPoint Z)⟩
    with commutes' := ?_}
  intro c
  rfl

theorem nativePointDimensionResidue {k : Type} [Field k] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X) :
    letI := nativeStructureResidueAlgebra f x
    ∃ n : ℕ, pointDimension X x=n ∧ Algebra.trdeg k (X.residueField x)=n := by
  let := nativeStructureResidueAlgebra f x
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure ({x} : Set X),isClosed_closure⟩ : Closeds X)
  let : IsIntegral I.subscheme := isIntegral_pointClosure x
  have hg : genericPoint I.subscheme =
      pointClosureLift x :=
    (genericPoint_spec I.subscheme).eq
      (isGenericPoint_pointClosureLift x)
  have hx : I.subschemeι (genericPoint I.subscheme) = x := by
    rw [hg]
    exact pointClosureLift_image x
  let g := I.subschemeι ≫ f
  let := stalkAlgebra g (genericPoint I.subscheme)
  let : LocallyOfFiniteType g := by dsimp only [g]; infer_instance
  obtain ⟨n,hd,htr⟩ := nativeFiniteTypeIntegralDimension g
  have hp := originalIntegralClosedImmersion_generic_pointDimension I.subschemeι
  have hpd : pointDimension X x=n := by
    rw [hx,hd] at hp
    exact_mod_cast hp
  let := nativeStructureResidueAlgebra g (genericPoint I.subscheme)
  let := nativeStructureResidueAlgebra f (I.subschemeι (genericPoint I.subscheme))
  have hres := ((genericFieldResidueAlgEquiv g).trans
    (nativeResidueAlgEquivOfBijective I.subschemeι f (genericPoint I.subscheme)
      (nativeResidueFieldMap_bijective_of_stalkMap_surjective I.subschemeι _
        (I.subschemeι.stalkMap_surjective _))).symm).trdeg_eq
  have ht : Algebra.trdeg k (X.residueField (I.subschemeι (genericPoint I.subscheme)))=n :=
    hres.symm.trans htr
  refine ⟨n,hpd,?_⟩
  have transport (a b : X) (h : a=b) :
      (letI := nativeStructureResidueAlgebra f a
       Algebra.trdeg k (X.residueField a)=n) →
      (letI := nativeStructureResidueAlgebra f b
       Algebra.trdeg k (X.residueField b)=n) := by
    cases h
    exact id
  exact transport _ _ hx ht

/-- A residue-field isomorphism over the base field preserves actual point dimension. -/
theorem nativePointDimension_eq_of_residueFieldMap_bijective
    {k : Type} [Field k] {Z X : Scheme.{0}} (i : Z ⟶ X) (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [LocallyOfFiniteType (i ≫ f)] (z : Z)
    (hb : Function.Bijective (i.residueFieldMap z)) :
    pointDimension Z z = pointDimension X (i z) := by
  let := nativeStructureResidueAlgebra f (i z)
  let := nativeStructureResidueAlgebra (i ≫ f) z
  obtain ⟨m, hm, hmt⟩ := nativePointDimensionResidue (i ≫ f) z
  obtain ⟨n, hn, hnt⟩ := nativePointDimensionResidue f (i z)
  have ht := (nativeResidueAlgEquivOfBijective i f z hb).trdeg_eq
  have he : m = n := by exact_mod_cast hmt.symm.trans (ht.symm.trans hnt)
  rw [hm, hn, he]

/-- The original residue field of the image embeds over the original base field,
so point dimension cannot increase under the map. -/
theorem nativePointDimension_image_le {k : Type} [Field k] {Z X : Scheme.{0}}
    (i : Z ⟶ X) (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [LocallyOfFiniteType (i ≫ f)] (z : Z) :
    pointDimension X (i z) ≤ pointDimension Z z := by
  let := nativeStructureResidueAlgebra f (i z)
  let := nativeStructureResidueAlgebra (i ≫ f) z
  obtain ⟨m, hm, hmt⟩ := nativePointDimensionResidue (i ≫ f) z
  obtain ⟨n, hn, hnt⟩ := nativePointDimensionResidue f (i z)
  have ht := trdeg_le_of_injective (nativeResidueAlgHom i f z)
    (nativeResidueAlgHom i f z).injective
  rw [hnt, hmt] at ht
  rw [hn, hm]
  have hnm : n ≤ m := by exact_mod_cast ht
  exact_mod_cast hnm

/-- The vanishing ideal of the closure of a point `η`, on an affine open containing `η`, is the
prime ideal of `η`. -/
private theorem vanishingIdeal_closure_singleton_ideal {X : Scheme.{0}} (η : X) {U : X.Opens} (hU : IsAffineOpen U)
    (hη : η ∈ U) :
    (Scheme.IdealSheafData.vanishingIdeal ⟨closure {η}, isClosed_closure⟩).ideal ⟨U, hU⟩ =
      (hU.primeIdealOf ⟨η, hη⟩).asIdeal := by
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
  have hpre : hU.fromSpec ⁻¹' {η} = {hU.primeIdealOf ⟨η, hη⟩} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hz
      apply hU.fromSpec.isOpenEmbedding.injective
      rw [hz, IsAffineOpen.fromSpec_primeIdealOf]
    · rintro rfl
      exact IsAffineOpen.fromSpec_primeIdealOf hU ⟨η, hη⟩
  have h1 : hU.fromSpec ⁻¹' closure {η} = closure {hU.primeIdealOf ⟨η, hη⟩} := by
    rw [hU.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      hU.fromSpec.continuous, hpre]
  have h2 : PrimeSpectrum.vanishingIdeal (closure {hU.primeIdealOf ⟨η, hη⟩} :
      Set (PrimeSpectrum Γ(X, U))) = (hU.primeIdealOf ⟨η, hη⟩).asIdeal := by
    rw [PrimeSpectrum.vanishingIdeal_closure, PrimeSpectrum.vanishingIdeal_singleton]
  exact (congrArg PrimeSpectrum.vanishingIdeal h1).trans h2

/-- The point dimension is the dimension of its actual prime quotient on each affine chart
containing the point. -/
theorem nativePointDimension_eq_affine_quotient {k : Type} [Field k] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X) {U : X.Opens}
    (hU : IsAffineOpen U) (hx : x ∈ U) :
    (↑(pointDimension X x) : WithBot ℕ∞) =
      ringKrullDim (Γ(X, U) ⧸ (hU.primeIdealOf ⟨x, hx⟩).asIdeal) := by
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure ({x} : Set X), isClosed_closure⟩ : Closeds X)
  let : IsIntegral I.subscheme := isIntegral_pointClosure x
  let g := I.subschemeι ≫ f
  let : LocallyOfFiniteType g := by dsimp only [g]; infer_instance
  have hg : genericPoint I.subscheme = pointClosureLift x :=
    (genericPoint_spec I.subscheme).eq (isGenericPoint_pointClosureLift x)
  have hpoint := originalIntegralClosedImmersion_generic_pointDimension I.subschemeι
  rw [hg, pointClosureLift_image] at hpoint
  let : Nonempty (I.subschemeι ⁻¹ᵁ U) :=
    ⟨⟨pointClosureLift x, show I.subschemeι (pointClosureLift x) ∈ U from
      (pointClosureLift_image x).symm ▸ hx⟩⟩
  have hd := nativeTopologicalKrullDim_eq_affine g (hU.preimage I.subschemeι)
  have hi := ringKrullDim_eq_of_ringEquiv (I.subschemeObjIso ⟨U, hU⟩).commRingCatIsoToRingEquiv
  refine hpoint.trans (hd.trans (hi.trans ?_))
  rw [vanishingIdeal_closure_singleton_ideal x hU hx]

end SGPT.Projective.BDivNov16
