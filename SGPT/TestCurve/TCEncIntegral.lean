import SGPT.TestCurve.TCEncSeparating
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# The total space of a test configuration is integral

Source: [BHJ17, §2.1] (a test configuration of a variety is a variety): if `X` is integral and
locally noetherian, the total space `𝓧` of a test configuration is integral. Indeed
`𝓧 ∖ 𝓧₀ ≅ X × 𝔾_m` is integral (`𝔾_m` is geometrically integral over `ℂ`) and, `π` being flat, it
is scheme-theoretically dense in `𝓧` (scheme-theoretic dominance of `𝔾_m ⊆ 𝔸¹` is stable under
the flat base change `π`); so `𝓧` is reduced and irreducible.

## Main results

* `geometricallyIntegral_affineLineToBase`, `geometricallyIntegral_gmToBase`: `𝔸¹` and `𝔾_m` are
  geometrically integral over `ℂ`.
* `TestConfiguration.isIntegral_offCentral`: `𝓧 ∖ 𝓧₀` is integral.
* `TestConfiguration.isIntegral_space`: `𝓧` is integral.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.TCEnc

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle
open Opposite MorphismProperty

/-- `ℂ[X] ≅ ℂ[PUnit]`, the polynomial ring of Mathlib's affine line. -/
def polyEquiv : MvPolynomial PUnit ℂ ≃+* Polynomial ℂ :=
  (MvPolynomial.uniqueAlgEquiv ℂ PUnit).toRingEquiv

instance :
    IsIso (Spec.map (CommRingCat.ofHom (polyEquiv : MvPolynomial PUnit ℂ →+* Polynomial ℂ))) := by
  have : IsIso (CommRingCat.ofHom (polyEquiv : MvPolynomial PUnit ℂ →+* Polynomial ℂ)) :=
    (polyEquiv.toCommRingCatIso).isIso_hom
  infer_instance

/-- `𝔸¹ ⟶ Spec ℂ` is the structure morphism of Mathlib's affine space `𝔸(PUnit; Spec ℂ)` up to
isomorphisms. -/
theorem affineLineToBase_eq : affineLineToBase =
    Spec.map (CommRingCat.ofHom (polyEquiv : MvPolynomial PUnit ℂ →+* Polynomial ℂ)) ≫
      (AffineSpace.SpecIso PUnit (.of ℂ)).inv ≫ (𝔸(PUnit; Spec (.of ℂ)) ↘ Spec (.of ℂ)) := by
  rw [AffineSpace.SpecIso_inv_over, affineLineToBase, ← Spec.map_comp]
  congr 1
  ext c
  simp [polyEquiv]

/-- `𝔸¹ = Spec ℂ[t]` is geometrically integral over `ℂ` (Mathlib's affine space). -/
instance geometricallyIntegral_affineLineToBase : GeometricallyIntegral affineLineToBase := by
  rw [affineLineToBase_eq,
    MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyIntegral),
    MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyIntegral)]
  infer_instance

instance : LocallyOfFinitePresentation affineLineToBase := by
  rw [affineLineToBase_eq,
    MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFinitePresentation),
    MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFinitePresentation)]
  infer_instance

/-- `𝔾_m` is geometrically integral over `ℂ`: its base changes are nonempty open subschemes of
the integral base changes of `𝔸¹`. -/
instance geometricallyIntegral_gmToBase : GeometricallyIntegral gmToBase := by
  constructor
  intro K _ y Z fst snd h
  have hW : IsIntegral (pullback affineLineToBase y) :=
    GeometricallyIntegral.geometrically_isIntegral (f := affineLineToBase) y
      (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  let φ : Z ⟶ pullback affineLineToBase y :=
    pullback.lift (fst ≫ gmOpen.ι) snd (by rw [Category.assoc]; exact h.w)
  have hs : IsPullback fst (φ ≫ pullback.snd affineLineToBase y)
      (gmOpen.ι ≫ affineLineToBase) y := by
    rw [pullback.lift_snd]
    exact h
  have hpb : IsPullback fst φ gmOpen.ι (pullback.fst affineLineToBase y) :=
    IsPullback.of_bot hs (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback _ _)
  have : IsOpenImmersion φ := MorphismProperty.of_isPullback hpb inferInstance
  have hsnd : Surjective snd := MorphismProperty.of_isPullback h inferInstance
  have : Nonempty Z := by
    obtain ⟨z, -⟩ := hsnd.surj (IsLocalRing.closedPoint K)
    exact ⟨z⟩
  exact isIntegral_of_isOpenImmersion φ

instance : UniversallyOpen gmToBase := UniversallyOpen.of_flat _

instance : IsDominant gmOpen.ι :=
  ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact gmOpen.isOpen.dense ⟨_, gmPoint.2⟩⟩

instance : IsSchemeTheoreticallyDominant gmOpen.ι :=
  IsSchemeTheoreticallyDominant.of_isDominant _

instance : QuasiCompact gmOpen.ι :=
  HasAffineProperty.iff_of_isAffine (P := @QuasiCompact).mpr inferInstance

namespace TestConfiguration

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}
  (T : TestConfiguration f a)

instance nonempty_offCentral [Nonempty X] : Nonempty (offCentral T.toLine).toScheme := by
  obtain ⟨j, y, hy⟩ := T.exists_nonempty_overOpen
  exact ⟨⟨y, overOpen_le_offCentral T.coord (a.opens j) hy⟩⟩

/-- **`𝓧 ∖ 𝓧₀ ≅ X × 𝔾_m` is integral** (`𝔾_m` is geometrically integral over `ℂ`). -/
theorem isIntegral_offCentral [IsIntegral X] [IsLocallyNoetherian X] :
    IsIntegral (offCentral T.toLine).toScheme := by
  have := T.coord_isIso
  exact isIntegral_of_isOpenImmersion (pullback.lift (f := f) (g := gmToBase) T.coord
    (toGm T.toLine) (by rw [T.coord_over, ← Category.assoc, ← toGm_comp_ι, Category.assoc]))

/-- **The total space of a test configuration of an integral locally noetherian `X` is
integral**: `𝓧 ∖ 𝓧₀` is integral and, by flatness of `π`, scheme-theoretically dense. -/
theorem isIntegral_space [IsIntegral X] [IsLocallyNoetherian X] : IsIntegral T.space := by
  have hU := T.isIntegral_offCentral
  let e : pullback T.toLine gmOpen.ι ≅ (offCentral T.toLine).toScheme :=
    pullbackRestrictIsoRestrict T.toLine gmOpen ≪≫ Scheme.isoOfEq _ (offCentral_eq T.toLine).symm
  have : Nonempty ↥(pullback T.toLine gmOpen.ι) := ⟨e.inv (Classical.arbitrary _)⟩
  have : IsIntegral (pullback T.toLine gmOpen.ι) := isIntegral_of_isOpenImmersion e.hom
  have : IsReduced T.space :=
    IsSchemeTheoreticallyDominant.isReduced (pullback.fst T.toLine gmOpen.ι)
  have : IrreducibleSpace T.space := by
    rw [irreducibleSpace_def]
    have hd := (pullback.fst T.toLine gmOpen.ι).denseRange
    have hirr : IsIrreducible (Set.range (pullback.fst T.toLine gmOpen.ι).base) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _
        (pullback.fst T.toLine gmOpen.ι).base.hom.continuous.continuousOn
    have := hirr.closure
    rwa [hd.closure_range] at this
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end TestConfiguration

end SGPT.TestCurve.TCEnc
