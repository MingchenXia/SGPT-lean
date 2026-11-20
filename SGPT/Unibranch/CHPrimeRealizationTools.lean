import SGPT.PSH.PrimeNov16OriginalHypersurfaceDictionary
import SGPT.PSH.PrimeNov16OriginalStrictTransform
import SGPT.Unibranch.HironakaG11ModificationCalculus
import SGPT.Foundations.Analysis.Pending.HironakaG11IntrinsicRegularOpenImmersion

/-!
# native pieces of original smooth spaces (tools for `cor:primerealization`)

Source `cor:primerealization` (`appendix_unibranch.tex`). The proof of the corollary over a
singular compact base modifies one connected component of a smooth complex space by a native
blowup sequence of manifolds and extends the result to the whole space
(`HironakaG10GenDisjointModification.exists_modification_extension`). The extended space `Y₂`
contains the blown-up manifold `N'` through an open immersion `j : wholeModel N' ⟶ Y₂` with closed
range. This file proves the three facts about such a configuration that the corollary needs:

* `isSmooth_of_openImmersion_of_isIsoOver` — `Y₂` is smooth: points in the range of `j` are
  regular because `N'` is a manifold, the other points because `ρ : Y₂ ⟶ Y₁` is an isomorphism
  over their image and `Y₁` is smooth;
* `isOriginalHypersurface_image` — a closed connected submanifold of codimension one of `N'` is
  carried by `j` to a prime divisor on `Y₂` (`IsOriginalHypersurface`, the hypersurface part of
  `def:primdiv`);
* `originalStrictTransform_eq_image` — the strict-transform comparison: if a morphism
  `F : S ⟶ Y` restricts over an open and closed piece to a native analytic modification
  `h : N → M`, then the original strict transform (`originalStrictTransform`, the closure of the
  singleton-fibre part of the preimage) of a set `A` in the piece is the image of the native
  differential strict transform `strictTransform n h`.

No compactness, connectedness or irreducibility is assumed. Blueprint: `blueprint/src/ch.tex`.
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.CHPrimeRealization

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences HironakaResolutionSpaceComplex
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceManifoldCharts
  HironakaEmbeddedNativeMorphism HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaG11IntrinsicRegularOpenImmersion AnalyticModificationLocalDiscrepancy
open SGPT.Unibranch SourceReducedComplexSpace OriginalNativeModification OriginalSmoothSourceAnalytic
open SGPT.PSH PrimeNov16OriginalHypersurface PrimeNov16OriginalStrictTransform

variable {n : ℕ} {N : Type} [TopologicalSpace N] [ChartedSpace (ComplexModel n) N]
  [IsComplexManifold n N]

/-- The point map of an open immersion with closed range out of a whole native model is a closed
embedding. -/
theorem isClosedEmbedding_pointMap {Y : SourceReducedComplexSpace}
    (j : wholeModel (n := n) N ⟶ Y) (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left)
    (hjc : IsClosed (range j.hom.left.base)) : Topology.IsClosedEmbedding (pointMap j) := by
  have h₁ : Topology.IsClosedEmbedding j.hom.left.base := ⟨hj.base_open.isEmbedding, hjc⟩
  exact h₁.comp (Homeomorph.Set.univ N).symm.isClosedEmbedding

/-- **Smoothness of an extension.** Let `ρ : Y₂ ⟶ Y₁` with `Y₁` smooth, `R ⊆ Y₁`, and
`j : wholeModel N ⟶ Y₂` an open immersion from a complex manifold with range `ρ⁻¹ R`, such that
`ρ` is an isomorphism over `Rᶜ`. Then `Y₂` is smooth. -/
theorem isSmooth_of_openImmersion_of_isIsoOver {Y₁ Y₂ : SourceReducedComplexSpace}
    (hY₁ : Y₁.IsSmooth) (j : wholeModel (n := n) N ⟶ Y₂)
    (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) (ρ : Y₂ ⟶ Y₁) (R : Set Y₁.obj.left)
    (hrange : range j.hom.left.base = ρ.hom.left.base ⁻¹' R) (hiso : IsIsoOver ρ Rᶜ) :
    Y₂.IsSmooth := by
  intro y
  change y ∈ intrinsicRegularLocus Y₂.obj
  by_cases hy : ρ.hom.left.base y ∈ R
  · have hyr : y ∈ range j.hom.left.base := by
      rw [hrange]
      exact hy
    obtain ⟨v, rfl⟩ := hyr
    have hcomm : j.hom.left ≫ Y₂.obj.hom = 𝟙 _ ≫ (wholeModel (n := n) N).obj.hom := by
      rw [Category.id_comp]
      exact Over.w j.hom
    exact (mem_intrinsicRegularLocus_iff_of_openImmersions (A := Y₂.obj)
      (B := (wholeModel (n := n) N).obj) j.hom.left (𝟙 _) hj inferInstance hcomm v).mpr
      (isSmooth_wholeModel (n := n) (M := N) v)
  · exact (IsIsoOver.mem_intrinsicRegularLocus_iff hiso hy).mpr (hY₁ _)

/-- **Native hypersurfaces through an open immersion are original prime divisors.** Let
`J : wholeModel N ⟶ Y` be an open immersion with closed range into a smooth complex space and
`D ⊆ N` a closed connected submanifold of dimension `k` with `k + 1 = n`. Then `J(D)` is an
original hypersurface of `Y` (`IsOriginalHypersurface`, the prime divisors of `def:primdiv`). -/
theorem isOriginalHypersurface_image {Y : SourceReducedComplexSpace} (hY : Y.IsSmooth)
    (J : wholeModel (n := n) N ⟶ Y) (hJ : LocallyRingedSpace.IsOpenImmersion J.hom.left)
    (hJc : IsClosed (range J.hom.left.base)) (D : Set N) (k : ℕ)
    (hD : IsClosedConnectedSubmanifold n D k) (hk : k + 1 = n) :
    IsOriginalHypersurface Y (pointMap J '' D) := by
  let E := pointMap J '' D
  have hJce := isClosedEmbedding_pointMap J hJ hJc
  have hEclosed : IsClosed E := hJce.isClosedMap D hD.1
  have hEconn : IsConnected E := hD.2.1.image (pointMap J) (continuous_pointMap J).continuousOn
  let Q := actualSubspaceUnivIso (n := n) (M := N)
  let i₀ := Q.inv ≫ J.hom.left
  have hi₀ : LocallyRingedSpace.IsOpenImmersion i₀ :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ Q.inv (by dsimp only [Q]; infer_instance)
      J.hom.left hJ
  have hp₀ : i₀ ≫ Y.obj.hom = ambientPointMap n N := by
    change (Q.inv ≫ J.hom.left) ≫ Y.obj.hom = _
    calc
      (Q.inv ≫ J.hom.left) ≫ Y.obj.hom = Q.inv ≫ (J.hom.left ≫ Y.obj.hom) :=
        Category.assoc _ _ _
      _ = Q.inv ≫ (wholeModel (n := n) N).obj.hom :=
        congrArg (fun f => Q.inv ≫ f) (Over.w J.hom)
      _ = _ := actualSubspaceUnivIso_inv_point
  have hpoint : ∀ x : N, i₀.base x = pointMap J x := by
    intro x
    have hQ : (Q.inv.base x).val = x := congrArg (fun f => f.base x) Q.inv_hom_id
    exact congrArg J.hom.left.base (Subtype.ext hQ)
  have heq : ((fun x : N => i₀.base x) ⁻¹' E) = D := by
    ext z
    change i₀.base z ∈ E ↔ z ∈ D
    rw [hpoint z]
    constructor
    · rintro ⟨w, hw, hval⟩
      exact hJce.injective hval ▸ hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  refine ⟨hEclosed, hEconn, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨m, U, i, hi, hp, u, hu⟩ := hY (pointMap J z)
  obtain ⟨hdim, hiff⟩ :=
    PrimeNov16OriginalLocalChartComparison.dimension_and_regularity_of_original_charts
      i₀ i hi₀ hi hp₀ hp z u ((hpoint z).trans hu.symm) E k
  have hreg₀ : RegularAtDim (n := n) ((fun x : N => i₀.base x) ⁻¹' E) z k :=
    heq.symm ▸ hD.2.2 z hz
  have hreg := hiff.mp hreg₀
  have hm : m = k + 1 := hdim.symm.trans hk.symm
  cases hm
  exact ⟨k, U, i, hi, hp, u, hu, hreg⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **The strict-transform comparison.** Let `F : S ⟶ Y` be a morphism of complex spaces,
`j : wholeModel N ⟶ S` an open immersion with closed range, `K : wholeModel M ⟶ Y` with injective
point map, and `h : N → M` a native analytic modification with `F ∘ j = K ∘ h`, such that
`F⁻¹(range K) ⊆ range j`. Then for every `A ⊆ range K` the original strict transform of `A` under
`F` is the image under `j` of the native strict transform of `K⁻¹ A` under `h`. -/
theorem originalStrictTransform_eq_image {S Y : SourceReducedComplexSpace} (F : S ⟶ Y)
    (j : wholeModel (n := n) N ⟶ S) (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left)
    (hjc : IsClosed (range j.hom.left.base)) (K : wholeModel (n := n) M ⟶ Y)
    (hK : Function.Injective (pointMap K)) {h : N → M} (hh : IsAnalyticModification (n := n) h)
    (hsq : ∀ z : N, F.hom.left.base (pointMap j z) = pointMap K (h z))
    (hpre : F.hom.left.base ⁻¹' range (pointMap K) ⊆ range (pointMap j))
    (A : Set Y.obj.left) (hA : A ⊆ range (pointMap K)) :
    originalStrictTransform F A = pointMap j '' strictTransform n h (pointMap K ⁻¹' A) := by
  have hjce := isClosedEmbedding_pointMap j hj hjc
  have hgood : F.hom.left.base ⁻¹' A ∩ singletonLocus F =
      pointMap j '' (h ⁻¹' (pointMap K ⁻¹' A) \ exceptionalLocus n h) := by
    ext t
    constructor
    · rintro ⟨htA, hts⟩
      obtain ⟨w, rfl⟩ := hpre (hA htA)
      refine ⟨w, ⟨?_, ?_⟩, rfl⟩
      · change pointMap K (h w) ∈ A
        rw [← hsq]
        exact htA
      · apply AnalyticModificationSingletonFibreInverse.not_mem_exceptionalLocus_of_unique_fibre hh w
        intro z hz
        apply hjce.injective
        apply hts
        rw [hsq, hsq, hz]
    · rintro ⟨w, ⟨hwA, hwe⟩, rfl⟩
      have hFt : F.hom.left.base (pointMap j w) ∈ A := by
        rw [hsq]
        exact hwA
      refine ⟨hFt, ?_⟩
      intro t ht
      have htA : F.hom.left.base t ∈ A := by
        rw [ht]
        exact hFt
      obtain ⟨z, rfl⟩ := hpre (hA htA)
      have hz : h z = h w := hK (by rw [← hsq, ← hsq]; exact ht)
      rw [AnalyticModificationExceptionalFibres.eq_of_apply_eq_of_not_mem_exceptionalLocus hh hwe hz]
  change closure (F.hom.left.base ⁻¹' A ∩ singletonLocus F) = _
  rw [hgood, hjce.closure_image_eq]
  rfl

end SGPT.Unibranch.CHPrimeRealization
