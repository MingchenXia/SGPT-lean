import SGPT.Unibranch.NativeNov16NormalizationExistence
import SGPT.Unibranch.NativeNov16NormalizationKahlerResolution
import SGPT.Unibranch.NativeNov16AmbientFormRestriction
import SGPT.Unibranch.KSSubmanifoldModel
import SGPT.Unibranch.KSUnibranchIEnvelope
import SGPT.Foundations.Analysis.Pending.HironakaResolutionSpaceSingular
import SGPT.Foundations.Analysis.Pending.StrictTransformSubvarietySequence
import SGPT.Foundations.Analysis.Pending.PureDimension

/-!
# The normalization `Ỹ` of an irreducible analytic subset of a compact Kähler manifold

Lane KS (infrastructure for the trace chapter, `chapter_trace.tex` §`sec:trace_def`: "Let `X` be
a connected compact Kähler manifold and `Y ⊆ X` an irreducible analytic subset … `Ỹ` the
normalization of `Y` … a normal Kähler space [GK20, Prop. 3.6] … we refer to `chap:unibranch` for
the pluripotential theory on unibranch Kähler spaces").

For a closed analytic subset `C` of a complex manifold `M` (the book's `Y`):

* `normalization C hC` (`Ỹ`) and `normalizationMap C hC : Ỹ → (C, 𝒪/𝓘_C)` are the existing
  normalization of PR #273 (`NativeNov16NormalizationSpace`): normal stalks
  (`normalization_normal`), hence unibranch (`normalization_isUnibranch`); the map is proper
  bimeromorphic with finite fibres and surjective; `Ỹ` is compact when `M` is.
* `restrictForm C hC θ` (`θ|_Ỹ`): the pull-back of a smooth form `θ` of `M` to `Ỹ`, a `SpaceForm`
  (smooth form on a complex space through local embeddings, `def:unibranch:L105`), closed and of
  type `(1,1)` when `θ` is.
* `PSH(Ỹ, θ|_Ỹ)` is `(normalization C hC).IsThetaPSH (restrictForm C hC θ)` (the book's
  `def:unibranch:L105`, no new notion).
* `manifoldPullback_restrictForm`: on a manifold `V` with a morphism `F : V → Ỹ` lying over a
  holomorphic `ι : V → M`, the manifold form `F^*(θ|_Ỹ)` is `ι^*θ`.
* `exists_kahlerResolution`: for `Y` an irreducible analytic subset of a compact Kähler manifold,
  a resolution of `Ỹ` by a connected compact Kähler manifold `V` of dimension `dim Y`
  (the strict transform of `Y` under the embedded resolution, with the restricted Kähler form),
  lying over `σ|_V : V → M`.  It is the `KahlerResolution` required by `def:unibranch:L212`.
* `existsUnique_isUnibranchIEnvelope_normalization`: `def:unibranch:L212` on `Ỹ` (well-definedness
  of `P_θ[φ]_𝓘`), from the reverse-descent half of `cor:PSH`.

Warning (recorded in the lane notes): the pull-back `p^*ω` of a Kähler form along the
normalization map is in general NOT a Kähler form on `Ỹ` (cusp `w² = z³`); the Kähler form of
[GK20, Prop. 3.6] is `p^*(Aω) + ddᶜ Σ χ_j |w_j|²`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.HironakaResolutionSpace
  SGPT.Foundations.Analysis.Pending.HironakaResolutionSpaceComplex

namespace SGPT.Unibranch.KSNormalizedSubvariety

open SourceReducedComplexSpace OriginalNativeModification KSManifoldForm KSUnibranchIEnvelope

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

section Normalization

variable (C : Set M) (hC : IsComplexAnalyticSubset (n := n) C)

/-- **`Ỹ`, the normalization** of the reduced complex space `(C, 𝒪_M/𝓘_C)`. -/
abbrev normalization : SourceReducedComplexSpace :=
  NativeNov16NormalizationSpace.source (ofClosedAnalytic C hC)

/-- The normalization map `p : Ỹ → (C, 𝒪_M/𝓘_C)`. -/
abbrev normalizationMap : normalization C hC ⟶ ofClosedAnalytic C hC :=
  NativeNov16NormalizationSpace.projection (ofClosedAnalytic C hC)

/-- `Ỹ` is normal: its local rings are integrally closed domains. -/
theorem normalization_normal (y : (normalization C hC).obj.left) :
    IsDomain ((normalization C hC).obj.left.presheaf.stalk y).carrier ∧
      IsIntegrallyClosed ((normalization C hC).obj.left.presheaf.stalk y).carrier :=
  (NativeNov16NormalizationSpace.normal_proper_finite_surjective (ofClosedAnalytic C hC)).1 y

/-- `Ỹ` is unibranch (`def:unibranch:L21`). -/
theorem normalization_isUnibranch : (normalization C hC).IsUnibranch :=
  isUnibranch_of_normal_stalks _ (fun y => (normalization_normal C hC y).1)
    (fun y => (normalization_normal C hC y).2)

theorem normalizationMap_isProperBimeromorphic :
    IsProperBimeromorphic (normalizationMap C hC) :=
  NativeNov16NormalizationExistence.projection_proper_bimeromorphic (ofClosedAnalytic C hC)

theorem normalizationMap_isProperMap :
    IsProperMap (normalizationMap C hC).hom.left.base :=
  (NativeNov16NormalizationSpace.normal_proper_finite_surjective (ofClosedAnalytic C hC)).2.1

theorem normalizationMap_finite_fibres (x : (ofClosedAnalytic C hC).obj.left) :
    ((normalizationMap C hC).hom.left.base ⁻¹' {x}).Finite :=
  (NativeNov16NormalizationSpace.normal_proper_finite_surjective (ofClosedAnalytic C hC)).2.2.1 x

theorem normalizationMap_surjective :
    Function.Surjective (normalizationMap C hC).hom.left.base :=
  (NativeNov16NormalizationSpace.normal_proper_finite_surjective (ofClosedAnalytic C hC)).2.2.2

/-- `Ỹ` is compact when `M` is. -/
theorem normalization_compactSpace [CompactSpace M] :
    CompactSpace (normalization C hC).obj.left := by
  have hCc : CompactSpace (ofClosedAnalytic C hC).obj.left :=
    isCompact_iff_compactSpace.mp hC.isClosed.isCompact
  apply isCompact_univ_iff.mp
  simpa only [preimage_univ] using
    (normalizationMap_isProperMap C hC).isCompact_preimage (isCompact_univ :
      IsCompact (univ : Set (ofClosedAnalytic C hC).obj.left))

end Normalization

/-! ### Smooth forms of `M` on `C` and on `Ỹ` -/

section Forms

variable (C : Set M) (hC : IsComplexAnalyticSubset (n := n) C)

theorem ofClosedAnalytic_isClosed {k : ℕ} {θ : SmoothRealForm n M k} (hθ : θ.IsClosed) :
    (SpaceForm.ofClosedAnalytic C hC θ).IsClosed := by
  intro c
  exact ⟨LocalEmbedding.ofChart C hC c.val, mem_range_chartModelMap (n := n) C c.property,
    θ.coeff (complexChartAt c.val), θ.smooth (complexChartAt c.val),
    fun z hz => hθ (complexChartAt c.val) z hz, SpaceForm.ofClosedAnalytic_restrictsTo C hC θ c.val⟩

theorem ofClosedAnalytic_isOneOne {θ : SmoothRealForm n M 2} (hθ : θ.IsTypeOneOne) :
    (SpaceForm.ofClosedAnalytic C hC θ).IsOneOne := by
  intro c
  exact ⟨LocalEmbedding.ofChart C hC c.val, mem_range_chartModelMap (n := n) C c.property,
    θ.coeff (complexChartAt c.val), θ.smooth (complexChartAt c.val),
    fun z hz a b => hθ (complexChartAt c.val) z hz a b,
    SpaceForm.ofClosedAnalytic_restrictsTo C hC θ c.val⟩

/-- **`θ|_Ỹ`**: the pull-back of a smooth form `θ` of `M` to the normalization `Ỹ`. -/
def restrictForm {k : ℕ} (θ : SmoothRealForm n M k) : SpaceForm (normalization C hC) k :=
  SpaceForm.pullback (SpaceForm.ofClosedAnalytic C hC θ) (normalizationMap C hC)

theorem restrictForm_isClosed {k : ℕ} {θ : SmoothRealForm n M k} (hθ : θ.IsClosed) :
    (restrictForm C hC θ).IsClosed :=
  (ofClosedAnalytic_isClosed C hC hθ).pullback _

theorem restrictForm_isOneOne {θ : SmoothRealForm n M 2} (hθ : θ.IsTypeOneOne) :
    (restrictForm C hC θ).IsOneOne :=
  (ofClosedAnalytic_isOneOne C hC hθ).pullback _

variable {d : ℕ} {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel d) V]
  [IsComplexManifold d V]

/-- On a manifold `V` mapping to `(C, 𝒪/𝓘_C)` over a holomorphic map `ι : V → M`, the manifold
pull-back of `θ|_C` is `ι^*θ`. -/
theorem manifoldPullback_ofClosedAnalytic {k : ℕ} (θ : SmoothRealForm n M k)
    (F : wholeModel (n := d) V ⟶ ofClosedAnalytic C hC) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hF : ∀ y : V, (F.hom.left.base ⟨y, mem_univ y⟩).val = ι y) :
    (manifoldPullback (SpaceForm.ofClosedAnalytic C hC θ) F).GeometricallyEq
      (SmoothRealForm.pullback hι θ) := by
  intro e z hz
  let x : M := ι (e.val.symm z)
  let d' : ComplexChart n M := complexChartAt (n := n) x
  have hzd : z ∈ coordinateDomain ι e d' := ⟨hz, mem_complexChartAt_source _⟩
  rw [manifoldPullback_coeff _ F e hz, SmoothRealForm.pullback_coeff hι θ e d' hzd]
  have hfac : ∀ c : (univ : Set (KSManifoldForm.chartTarget e)),
      c.val.val ∈ coordinateDomain ι e d' →
      ∃ b : (LocalEmbedding.ofChart C hC x).carrier, b.val.val = coordinateMap ι e d' c.val.val ∧
        (LocalEmbedding.ofChart C hC x).toPoint b = (chartInverse e ≫ F).hom.left.base c := by
    intro c hc
    have hsrc : ι (e.val.symm c.val.val) ∈ d'.val.source := hc.2
    have hmemC : ι (e.val.symm c.val.val) ∈ C := by
      rw [← hF]
      exact (F.hom.left.base ⟨e.val.symm c.val.val, mem_univ _⟩).property
    have hu : coordinateMap ι e d' c.val.val ∈ (chartImage (n := n) x : Set (ComplexModel n)) :=
      coordinateMap_mem_target hc
    let u : chartImage (n := n) x := ⟨coordinateMap ι e d' c.val.val, hu⟩
    refine ⟨⟨u, ?_⟩, rfl, ?_⟩
    · show (chartAt (ComplexModel n) x).symm (coordinateMap ι e d' c.val.val) ∈ C
      change d'.val.symm (d'.val (ι (e.val.symm c.val.val))) ∈ C
      rw [d'.val.left_inv hsrc]
      exact hmemC
    · apply Subtype.ext
      show d'.val.symm (coordinateMap ι e d' c.val.val) =
        (F.hom.left.base ⟨e.val.symm c.val.val, mem_univ _⟩).val
      rw [hF]
      exact d'.val.left_inv hsrc
  exact SpaceForm.pullbackToDomain_eq_of_restrictsTo _ (chartInverse e ≫ F)
    (SpaceForm.ofClosedAnalytic_restrictsTo C hC θ x) (coordinateDomain_isOpen hι e d')
    (fun w hw => hw.1) ((coordinateMap_contDiffOn hι e d').differentiableOn (by simp)) hfac hzd

/-- **The manifold pull-back of `θ|_Ỹ`.** On a manifold `V` with a morphism `F : V → Ỹ` lying over
a holomorphic `ι : V → M` (`p ∘ F = ι` on points), `F^*(θ|_Ỹ) = ι^*θ`. -/
theorem manifoldPullback_restrictForm {k : ℕ} (θ : SmoothRealForm n M k)
    (F : wholeModel (n := d) V ⟶ normalization C hC) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hF : ∀ y : V,
      ((normalizationMap C hC).hom.left.base (F.hom.left.base ⟨y, mem_univ y⟩)).val = ι y) :
    (manifoldPullback (restrictForm C hC θ) F).GeometricallyEq (SmoothRealForm.pullback hι θ) :=
  (manifoldPullback_pullback _ _ F).trans
    (manifoldPullback_ofClosedAnalytic C hC θ (F ≫ normalizationMap C hC) hι hF)

end Forms

/-! ### A Kähler resolution of `Ỹ` -/

section KahlerResolution

private theorem singularSet_eq_singularLocus (Y : ClosedIrreducibleAnalyticSubvariety n M) :
    HironakaEmbeddedAnalytic.singularSet (n := n) Y.carrier = singularLocus Y := by
  ext x
  rw [HironakaEmbeddedAnalytic.mem_singularSet_iff]
  constructor
  · rintro ⟨hx, hreg⟩
    exact ⟨hx, hreg Y.dim⟩
  · rintro ⟨hx, hreg⟩
    refine ⟨hx, fun k hk => hreg ?_⟩
    have hkd := PureDimension.eq_dim_of_regularAtDim Y hk
    rw [hkd] at hk
    exact hk

/-- **A resolution of `Ỹ` by a connected compact Kähler manifold**, for `Y` an irreducible
analytic subset of a compact Kähler manifold `M`: the strict transform `V` of `Y` under the
embedded resolution `σ : M' → M` (a manifold of dimension `dim Y`, with the restriction of a
Kähler form of `M'`), with the resolution `V → Ỹ` lifting `σ|_V` through the normalization. -/
theorem exists_kahlerResolution [CompactSpace M] (omega : KahlerBackground n M)
    (Y : ClosedIrreducibleAnalyticSubvariety n M) :
    ∃ (R : KahlerResolution Y.dim (normalization Y.carrier Y.analytic)) (ι : R.Y → M)
      (_ : ContMDiff 𝓘(ℂ, ComplexModel Y.dim) 𝓘(ℂ, ComplexModel n) ∞ ι),
      ∀ y : R.Y, ((normalizationMap Y.carrier Y.analytic).hom.left.base
        (R.map.hom.left.base ⟨y, mem_univ y⟩)).val = ι y := by
  have hWa : IsComplexAnalyticSubset (n := n) Y.carrier := Y.analytic
  have hpure : AnalyticDimensionBasics.IsPureDim (n := n) Y.carrier Y.dim :=
    fun _ _ hy => PureDimension.eq_dim_of_regularAtDim Y hy
  obtain ⟨M', _, _, _, σ, E, h, hreg, _omega', hCM, hcpt, l, hl, -, htri, -, omegaR, -⟩ :=
    NativeNov16NormalizationKahlerResolution.exists_kahler_resolution_of_normalization hWa hpure
      Y.dim_le omega
  let := SubmanifoldChartedSpace.chartedSpace Y.dim_le hreg
  have hExcS : σ '' exceptionalLocus n σ ⊆ singularLocus Y := by
    rintro _ ⟨y, hy, rfl⟩
    by_contra hx
    have hc : σ y ∈ (HironakaEmbeddedAnalytic.singularSet (n := n) Y.carrier)ᶜ := by
      rw [singularSet_eq_singularLocus]
      exact hx
    exact Set.disjoint_left.mp h.isIsomorphismOver.2 hc hy
  have hconn := StrictTransformSubvarietySequence.isConnected_strictTransform_of_isBlowupSequence
    h.isBlowupSequence Y hExcS
  have : ConnectedSpace (strictTransform n σ Y.carrier) := isConnected_iff_connectedSpace.mp hconn
  have hval := SubmanifoldChartedSpace.contMDiff_val Y.dim_le hreg
  let K := KSSubmanifoldModel.wholeModelIso (d := Y.dim) h.isClosedSubmanifold hval
    (KSSubmanifoldModel.flattening_codRestrict Y.dim_le hreg)
  let R : KahlerResolution Y.dim (normalization Y.carrier Y.analytic) :=
    { Y := strictTransform n σ Y.carrier
      isComplexManifold := hCM
      compactSpace := hcpt
      kahler := omegaR
      map := K.hom ≫ l
      isProperBimeromorphic := hl.2.precomp_iso K }
  refine ⟨R, σ ∘ Subtype.val, h.contMDiff.comp hval, ?_⟩
  intro y
  have hpt := congrArg (fun F => F.hom.left.base (K.hom.hom.left.base ⟨y, mem_univ y⟩)) htri
  change ((l ≫ NativeNov16NormalizationSpace.projection _).hom.left.base
    (K.hom.hom.left.base ⟨y, mem_univ y⟩)).val = σ y.val
  rw [hpt]
  rfl

/-- **A resolution of `(Y, 𝒪_M/𝓘_Y)` by a connected compact Kähler manifold**, for `Y` an
irreducible analytic subset of a compact Kähler manifold `M` (the strict transform under the
embedded resolution, lying over `σ|_V`). -/
theorem exists_kahlerResolution_ofClosedAnalytic [CompactSpace M] (omega : KahlerBackground n M)
    (Y : ClosedIrreducibleAnalyticSubvariety n M) :
    ∃ (R : KahlerResolution Y.dim (ofClosedAnalytic Y.carrier Y.analytic)) (ι : R.Y → M)
      (_ : ContMDiff 𝓘(ℂ, ComplexModel Y.dim) 𝓘(ℂ, ComplexModel n) ∞ ι),
      ∀ y : R.Y, (R.map.hom.left.base ⟨y, mem_univ y⟩).val = ι y := by
  have hWa : IsComplexAnalyticSubset (n := n) Y.carrier := Y.analytic
  have hpure : AnalyticDimensionBasics.IsPureDim (n := n) Y.carrier Y.dim :=
    fun _ _ hy => PureDimension.eq_dim_of_regularAtDim Y hy
  obtain ⟨M', _, _, _, σ, E, h, hreg, _omega', hCM, hcpt, hres, -, omegaW, -⟩ :=
    exists_kahler_resolution_ofClosedAnalytic hWa hpure Y.dim_le omega
  let := SubmanifoldChartedSpace.chartedSpace Y.dim_le hreg
  have hExcS : σ '' exceptionalLocus n σ ⊆ singularLocus Y := by
    rintro _ ⟨y, hy, rfl⟩
    by_contra hx
    have hc : σ y ∈ (HironakaEmbeddedAnalytic.singularSet (n := n) Y.carrier)ᶜ := by
      rw [singularSet_eq_singularLocus]
      exact hx
    exact Set.disjoint_left.mp h.isIsomorphismOver.2 hc hy
  have hconn := StrictTransformSubvarietySequence.isConnected_strictTransform_of_isBlowupSequence
    h.isBlowupSequence Y hExcS
  have : ConnectedSpace (strictTransform n σ Y.carrier) := isConnected_iff_connectedSpace.mp hconn
  have hval := SubmanifoldChartedSpace.contMDiff_val Y.dim_le hreg
  let K := KSSubmanifoldModel.wholeModelIso (d := Y.dim) h.isClosedSubmanifold hval
    (KSSubmanifoldModel.flattening_codRestrict Y.dim_le hreg)
  let R : KahlerResolution Y.dim (ofClosedAnalytic Y.carrier Y.analytic) :=
    { Y := strictTransform n σ Y.carrier
      isComplexManifold := hCM
      compactSpace := hcpt
      kahler := omegaW
      map := K.hom ≫ resolutionMorphism hWa h
      isProperBimeromorphic := hres.2.precomp_iso K }
  exact ⟨R, σ ∘ Subtype.val, h.contMDiff.comp hval, fun _ => rfl⟩

end KahlerResolution

/-! ### `def:unibranch:L212` on `Ỹ` -/

/-- **`def:unibranch:L212` on the normalization `Ỹ`** of an irreducible analytic subset `Y` of a
compact Kähler manifold: for every closed smooth `(1,1)`-form `θ` on `Ỹ` and `φ ∈ PSH(Ỹ, θ)` there
is exactly one function with the defining property of `P_θ[φ]_𝓘`, given the reverse-descent half
of `cor:PSH` along the Kähler resolutions of `Ỹ` (hypothesis named after `cor:PSH`). -/
theorem existsUnique_isUnibranchIEnvelope_normalization [CompactSpace M]
    (omega : KahlerBackground n M) (Y : ClosedIrreducibleAnalyticSubvariety n M)
    (θ : SpaceForm (normalization Y.carrier Y.analytic) 2) (hθc : θ.IsClosed)
    (hθ : θ.IsOneOne) {φ : (normalization Y.carrier Y.analytic).obj.left → EReal}
    (hφ : (normalization Y.carrier Y.analytic).IsThetaPSH θ φ)
    (hcorPSH : ∀ R : KahlerResolution Y.dim (normalization Y.carrier Y.analytic),
      CorPSHDescentAlong R.map θ) :
    ∃! ψ, IsUnibranchIEnvelope Y.dim (normalization Y.carrier Y.analytic) θ φ ψ := by
  obtain ⟨R, -, -, -⟩ := exists_kahlerResolution omega Y
  exact existsUnique_isUnibranchIEnvelope (normalization_isUnibranch _ _) θ hθc hθ hφ R
    (hcorPSH R)

/-- **`def:unibranch:L212` on a unibranch irreducible analytic subset** `Y` of a compact Kähler
manifold, viewed as the complex space `(Y, 𝒪_M/𝓘_Y)`, given the reverse-descent half of
`cor:PSH` along its Kähler resolutions. -/
theorem existsUnique_isUnibranchIEnvelope_ofClosedAnalytic [CompactSpace M]
    (omega : KahlerBackground n M) (Y : ClosedIrreducibleAnalyticSubvariety n M)
    (hX : (ofClosedAnalytic Y.carrier Y.analytic).IsUnibranch)
    (θ : SpaceForm (ofClosedAnalytic Y.carrier Y.analytic) 2) (hθc : θ.IsClosed)
    (hθ : θ.IsOneOne) {φ : (ofClosedAnalytic Y.carrier Y.analytic).obj.left → EReal}
    (hφ : (ofClosedAnalytic Y.carrier Y.analytic).IsThetaPSH θ φ)
    (hcorPSH : ∀ R : KahlerResolution Y.dim (ofClosedAnalytic Y.carrier Y.analytic),
      CorPSHDescentAlong R.map θ) :
    ∃! ψ, IsUnibranchIEnvelope Y.dim (ofClosedAnalytic Y.carrier Y.analytic) θ φ ψ := by
  obtain ⟨R, -, -, -⟩ := exists_kahlerResolution_ofClosedAnalytic omega Y
  exact existsUnique_isUnibranchIEnvelope hX θ hθc hθ hφ R (hcorPSH R)

end SGPT.Unibranch.KSNormalizedSubvariety
