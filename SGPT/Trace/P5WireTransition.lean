import SGPT.Trace.RIsoBResolutionVolume
import SGPT.Trace.DirectImgFibre
import SGPT.Foundations.Analysis.Pending.ProperMappingTheorem
import SGPT.Foundations.Analysis.Pending.HironakaEmbeddedCommonComponent

/-!
# Two resolutions of `Y` are biholomorphic over a common dense Zariski open subset

Source: the book reads the trace along an irreducible analytic subset `Y` on the normalization
`Ỹ`, i.e. on any resolution of `Y` (`chapter_trace.tex`, `def:traceop`, and
`def:NApotential:L623`: "independent of the choice of the resolution"). Comparing the readings on
two resolution targets `(Y'₁, ι₁)`, `(Y'₂, ι₂)` of `Y` (`Trace2Resolution.ResolutionTarget`) needs a
resolution dominating both (SGPT.Foundations.Analysis goal P5). The common-resolution construction
of TN (`HironakaEmbeddedCommon`) takes as input a biholomorphism between the parts of `Y'₂` and
`Y'₁` lying over the complement of a closed analytic subset `B` of the ambient manifold, compatible
with the maps to `X`. This file produces that input for two arbitrary resolution targets.

`IsResolutionOf` only asks `ι` to be injective over the complement of an analytic `B ⊇ Y_sing`
(with dense preimage). We enlarge `B` by the images `ιᵢ(Cᵢ)` of the non-immersion loci
`Cᵢ = {rank dιᵢ < dim Y}` (analytic by the rank-degeneracy theorem of TN, their images analytic by
Remmert's proper mapping theorem, `ProperMappingTheorem.isComplexAnalyticSubset_image`). Over the
complement of the enlarged set both maps are injective immersions, hence have local holomorphic
left inverses (`exists_local_retraction`, inverse function theorem), and the transition
`ι₁⁻¹ ∘ ι₂` is a biholomorphism (`exists_goodTransition`). The enlarged set still has nowhere dense
preimages because the non-immersion loci are nowhere dense (a resolution is generically an
immersion, `RIsoB.exists_injective_fderiv`).

## Main declarations

* `nonImmersionLocus`, `mem_nonImmersionLocus_iff`, `isComplexAnalyticSubset_nonImmersionLocus`;
* `exists_local_retraction`: an immersion has a local holomorphic left inverse;
* `interior_nonImmersionLocus`: the non-immersion locus of a resolution target is nowhere dense;
* `transition`, `transitionDiffeomorph`: the transition between the good loci;
* `exists_goodTransition`: the common good locus and the transition biholomorphism.
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace SGPT.Trace.P5Wire

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
  SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.RankDegeneracy
open SGPT.Trace.Trace2Resolution

/-! ### The non-immersion locus and local retractions -/

section Immersion

variable {k n : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V] {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

variable (k n) in
/-- The **non-immersion locus** of a holomorphic map `ι : V → X` from a `k`-dimensional manifold:
the points where `rank dι < k` (the rank-degeneracy set `S_k(ι, V)` of TN). -/
def nonImmersionLocus (ι : V → X) : Set V :=
  rankDegeneracyLocus k n ι univ k k

/-- A point is outside the non-immersion locus iff the differential (read in the preferred
charts) is injective. -/
theorem mem_nonImmersionLocus_iff {ι : V → X} {v : V} :
    v ∈ nonImmersionLocus k n ι ↔
      ¬ Function.Injective
        (chartDeriv (complexChartAt (n := k) v) (complexChartAt (n := n) (ι v)) ι v) := by
  have hreg : v ∈ regularLocus (n := k) (univ : Set V) k :=
    AnalyticIrreducibleComponents.regularAtDim_univ v
  have hrank := SGPT.Trace.DirectImg.rankAt_univ_eq (n := k) (m := n) (f := ι) v
  set D := chartDeriv (complexChartAt (n := k) v) (complexChartAt (n := n) (ι v)) ι v with hD
  have hrk := LinearMap.finrank_range_add_finrank_ker
    (D : ComplexModel k →ₗ[ℂ] ComplexModel n)
  rw [finrank_euclideanSpace_fin] at hrk
  constructor
  · rintro (⟨-, hn⟩ | ⟨-, hlt⟩)
    · exact absurd hreg hn
    · intro hinj
      have hker : LinearMap.ker (D : ComplexModel k →ₗ[ℂ] ComplexModel n) = ⊥ :=
        LinearMap.ker_eq_bot.mpr hinj
      rw [hker, finrank_bot] at hrk
      rw [hrank] at hlt
      omega
  · intro hninj
    refine Or.inr ⟨hreg, ?_⟩
    rw [hrank]
    by_contra hge
    apply hninj
    have h0 : Module.finrank ℂ (LinearMap.ker (D : ComplexModel k →ₗ[ℂ] ComplexModel n)) = 0 := by
      omega
    exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp h0)

/-- The non-immersion locus is analytic. -/
theorem isComplexAnalyticSubset_nonImmersionLocus {ι : V → X}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι) :
    IsComplexAnalyticSubset (n := k) (nonImmersionLocus k n ι) :=
  isComplexAnalyticSubset_rankDegeneracyLocus isComplexAnalyticSubset_univ
    (fun _ _ hy => AnalyticIrreducibleComponents.eq_of_regularAtDim_univ hy)
    (hι.mdifferentiable (by simp)) k

/-- **An immersion has a local holomorphic left inverse.** At a point `v` outside the
non-immersion locus of `ι`, there is a map `r : X → V`, holomorphic at `ι v`, with `r ∘ ι = id`
near `v`. (Compose the chart reading of `ι` with a linear left inverse of its differential and
invert the resulting local biholomorphism of `ℂ^k`.) -/
theorem exists_local_retraction {ι : V → X}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι) {v : V}
    (hv : v ∉ nonImmersionLocus k n ι) :
    ∃ r : X → V, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel k) ∞ r (ι v) ∧
      ∀ᶠ v' in 𝓝 v, r (ι v') = v' := by
  classical
  rw [mem_nonImmersionLocus_iff, not_not] at hv
  set e := complexChartAt (n := k) v with he
  set d := complexChartAt (n := n) (ι v) with hd
  set p := e.val v with hp
  set F := coordinateMap ι e d with hF
  have hD : IsOpen (coordinateDomain ι e d) := coordinateDomain_isOpen hι e d
  have hve : v ∈ e.val.source := mem_complexChartAt_source v
  have hpD : p ∈ coordinateDomain ι e d := ⟨e.val.map_source hve, by
    show ι (e.val.symm (e.val v)) ∈ d.val.source
    rw [e.val.left_inv hve]; exact mem_complexChartAt_source _⟩
  have hFc : ContDiffAt ℂ ∞ F p :=
    (coordinateMap_contDiffOn hι e d).contDiffAt (hD.mem_nhds hpD)
  set L : ComplexModel k →L[ℂ] ComplexModel n := fderiv ℂ F p with hL
  have hLinj : Function.Injective L := hv
  obtain ⟨Pl, hPl⟩ := LinearMap.exists_leftInverse_of_injective
    (L : ComplexModel k →ₗ[ℂ] ComplexModel n) (LinearMap.ker_eq_bot.mpr hLinj)
  set P : ComplexModel n →L[ℂ] ComplexModel k := LinearMap.toContinuousLinearMap Pl with hP
  have hPL : P.comp L = ContinuousLinearMap.id ℂ (ComplexModel k) := by
    ext1 w
    exact congrArg (fun f : ComplexModel k →ₗ[ℂ] ComplexModel k => f w) hPl
  set G : ComplexModel k → ComplexModel k := fun w => P (F w) with hG
  have hGs : HasStrictFDerivAt G
      ((ContinuousLinearEquiv.refl ℂ (ComplexModel k) : ComplexModel k ≃L[ℂ] ComplexModel k) :
        ComplexModel k →L[ℂ] ComplexModel k) p := by
    have h := P.hasStrictFDerivAt.comp p (hFc.hasStrictFDerivAt (by simp))
    rw [← hL, hPL] at h
    exact h
  set Φ := hGs.toOpenPartialHomeomorph G with hΦ
  have hΦcoe : ⇑Φ = G := rfl
  have hpΦ : p ∈ Φ.source := hGs.mem_toOpenPartialHomeomorph_source
  have hFp : F p = d.val (ι v) := by
    show d.val (ι (e.val.symm (e.val v))) = _
    rw [e.val.left_inv hve]
  have hGp : G p = P (d.val (ι v)) := by rw [hG]; simp only [hFp]
  have hsym : Φ.symm (P (d.val (ι v))) = p := by
    rw [← hGp, ← hΦcoe]; exact Φ.left_inv hpΦ
  have hGt : P (d.val (ι v)) ∈ Φ.target := by
    rw [← hGp, ← hΦcoe]; exact Φ.map_source hpΦ
  refine ⟨fun x => e.val.symm (Φ.symm (P (d.val x))), ?_, ?_⟩
  · have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ d.val (ι v) :=
      (contMDiffOn_chart (n := ∞)).contMDiffAt
        (d.val.open_source.mem_nhds (mem_complexChartAt_source _))
    have hGc : ContDiffAt ℂ ∞ G p := P.contDiff.contDiffAt.comp p hFc
    have hΦs : ContDiffAt ℂ ∞ Φ.symm (P (d.val (ι v))) := by
      refine Φ.contDiffAt_symm hGt (f₀' := ContinuousLinearEquiv.refl ℂ (ComplexModel k)) ?_ ?_
      · rw [hsym, hΦcoe]; exact hGs.hasFDerivAt
      · rw [hsym, hΦcoe]; exact hGc
    have h2 : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel k) ∞
        (fun x => Φ.symm (P (d.val x))) (ι v) :=
      (hΦs.comp (d.val (ι v)) P.contDiff.contDiffAt).contMDiffAt.comp (ι v) h1
    have h3 : ContMDiffAt 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ e.val.symm
        (Φ.symm (P (d.val (ι v)))) := by
      rw [hsym]
      exact (contMDiffOn_chart_symm (n := ∞)).contMDiffAt
        (e.val.open_target.mem_nhds (e.val.map_source hve))
    exact h3.comp (ι v) h2
  · have hcont : ContinuousAt (fun z' => e.val z') v := e.val.continuousAt hve
    have hιc : ContinuousAt ι v := hι.continuous.continuousAt
    filter_upwards [e.val.open_source.mem_nhds hve, hcont.eventually (Φ.open_source.mem_nhds hpΦ),
      hιc.eventually (d.val.open_source.mem_nhds (mem_complexChartAt_source (ι v)))]
      with v' hv'e hv'Φ hv'd
    show e.val.symm (Φ.symm (P (d.val (ι v')))) = v'
    have hGv : G (e.val v') = P (d.val (ι v')) := by
      show P (d.val (ι (e.val.symm (e.val v')))) = _
      rw [e.val.left_inv hv'e]
    rw [← hGv, ← hΦcoe, Φ.left_inv hv'Φ, e.val.left_inv hv'e]

/-- An analytic subset of a connected manifold missing one point has empty interior. -/
theorem interior_eq_empty_of_not_mem [ConnectedSpace V] {A : Set V}
    (hA : IsComplexAnalyticSubset (n := k) A) {v : V} (hv : v ∉ A) : interior A = ∅ := by
  by_contra h
  exact hv ((hA.eq_univ_of_interior_nonempty (nonempty_iff_ne_empty.mpr h)).symm ▸ mem_univ v)

/-- A set with empty interior in a nonempty space misses some point. -/
theorem exists_not_mem_of_interior_eq_empty {Z : Type*} [TopologicalSpace Z] [Nonempty Z]
    {A : Set Z} (h : interior A = ∅) : ∃ z, z ∉ A := by
  by_contra hall
  push Not at hall
  have hA : A = univ := eq_univ_of_forall hall
  rw [hA, interior_univ] at h
  exact univ_nonempty.ne_empty h

end Immersion

/-! ### Resolution targets are generically immersions -/

section Target

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : ClosedIrreducibleAnalyticSubvariety n X}

/-- Some point of a resolution target is outside the non-immersion locus. -/
theorem exists_not_mem_nonImmersionLocus (R : ResolutionTarget Y) :
    ∃ v, v ∉ nonImmersionLocus Y.dim n R.ι := by
  obtain ⟨e, d, z, hz, hinj⟩ := SGPT.Trace.RIsoB.exists_injective_fderiv R
  set v := e.val.symm z with hvdef
  have hve : v ∈ e.val.source := e.val.map_target hz.1
  have hvd : R.ι v ∈ d.val.source := hz.2
  have hmd : MDifferentiableAt 𝓘(ℂ, ComplexModel Y.dim) 𝓘(ℂ, ComplexModel n) R.ι v :=
    (R.contMDiff v).mdifferentiableAt (by simp)
  have hreg := AnalyticIrreducibleComponents.regularAtDim_univ (n := Y.dim) v
  have hT : tangentSpaceIn e (univ : Set R.V) v = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_tangentSpaceIn_of_regularAtDim e hve hreg, finrank_euclideanSpace_fin]
  have hFd : DifferentiableAt ℂ (coordinateMap R.ι e d) z :=
    ((coordinateMap_contDiffOn R.contMDiff e d).contDiffAt
      ((coordinateDomain_isOpen R.contMDiff e d).mem_nhds hz)).differentiableAt (by simp)
  have hcd : chartDeriv e d R.ι v = fderiv ℂ (coordinateMap R.ι e d) z := by
    unfold chartDeriv
    rw [hvdef, e.val.right_inv hz.1]
    rfl
  have hinjC : Function.Injective
      ((chartDeriv e d R.ι v : ComplexModel Y.dim →L[ℂ] ComplexModel n) :
        ComplexModel Y.dim →ₗ[ℂ] ComplexModel n) := by
    intro a b hab
    apply hinj
    rw [hFd.fderiv_restrictScalars ℝ]
    change (chartDeriv e d R.ι v) a = (chartDeriv e d R.ι v) b at hab
    rw [hcd] at hab
    exact hab
  refine ⟨v, fun hv => ?_⟩
  have hlt : rankAt (n := Y.dim) (n' := n) R.ι univ v < Y.dim := by
    rcases hv with ⟨-, hn⟩ | ⟨-, hlt⟩
    · exact absurd hreg hn
    · exact hlt
  rw [rankAt_eq_rankIn e d univ hve hvd hmd] at hlt
  unfold rankIn at hlt
  rw [hT, Submodule.map_top, LinearMap.finrank_range_of_inj hinjC,
    finrank_euclideanSpace_fin] at hlt
  exact lt_irrefl _ hlt

/-- **A resolution is generically an immersion**: the non-immersion locus of a resolution target
is a nowhere dense analytic subset. -/
theorem interior_nonImmersionLocus (R : ResolutionTarget Y) :
    interior (nonImmersionLocus Y.dim n R.ι) = ∅ := by
  obtain ⟨v, hv⟩ := exists_not_mem_nonImmersionLocus R
  exact interior_eq_empty_of_not_mem (isComplexAnalyticSubset_nonImmersionLocus R.contMDiff) hv

/-- The image of the non-immersion locus of a resolution target is analytic (Remmert). -/
theorem isComplexAnalyticSubset_image_nonImmersionLocus (R : ResolutionTarget Y) :
    IsComplexAnalyticSubset (n := n) (R.ι '' nonImmersionLocus Y.dim n R.ι) := by
  have hC := isComplexAnalyticSubset_nonImmersionLocus R.contMDiff
  refine ProperMappingTheorem.isComplexAnalyticSubset_image R.contMDiff hC fun K hK => ?_
  exact (hC.isClosed.inter (hK.isClosed.preimage R.contMDiff.continuous)).isCompact

end Target

/-! ### The transition between the good loci of two maps -/

section Transition

open HironakaEmbeddedCommon

variable {k n : ℕ} {V₁ V₂ X : Type u}
  [TopologicalSpace V₁] [ChartedSpace (ComplexModel k) V₁] [IsComplexManifold k V₁]
  [CompactSpace V₁]
  [TopologicalSpace V₂] [ChartedSpace (ComplexModel k) V₂] [IsComplexManifold k V₂]
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {ι₁ : V₁ → X} {ι₂ : V₂ → X}
  (hι₁ : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι₁)
  (hι₂ : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι₂)
  {B : Set X} (hB : IsClosed B) (hrange : ∀ w, ∃ v, ι₁ v = ι₂ w)

/-- The **transition** `ι₁⁻¹ ∘ ι₂` from the part of `V₂` over `X \ B` to the part of `V₁` over
`X \ B` (a choice of preimage; unique when `ι₁` is injective over `X \ B`). -/
def transition (y : goodOpen ι₂ hι₂ B hB) : goodOpen ι₁ hι₁ B hB :=
  ⟨Classical.choose (hrange y.val), by
    show ι₁ (Classical.choose (hrange y.val)) ∈ Bᶜ
    rw [Classical.choose_spec (hrange y.val)]
    exact y.2⟩

omit [IsComplexManifold k V₁] [CompactSpace V₁] [IsComplexManifold k V₂] [IsComplexManifold n X] in
theorem transition_spec (y : goodOpen ι₂ hι₂ B hB) :
    ι₁ (transition hι₁ hι₂ hB hrange y).val = ι₂ y.val :=
  Classical.choose_spec (hrange y.val)

omit [IsComplexManifold k V₁] [IsComplexManifold k V₂] in
/-- The transition is continuous: `ι₁` restricted over `X \ B` is a closed embedding. -/
theorem continuous_transition (hinj : InjOn ι₁ (ι₁ ⁻¹' Bᶜ)) :
    Continuous (transition hι₁ hι₂ hB hrange) := by
  have hcl : IsClosedMap (fun v : goodOpen ι₁ hι₁ B hB => (⟨ι₁ v.val, v.2⟩ : (Bᶜ : Set X))) :=
    hι₁.continuous.isClosedMap.restrictPreimage Bᶜ
  have hcont : Continuous (fun v : goodOpen ι₁ hι₁ B hB => (⟨ι₁ v.val, v.2⟩ : (Bᶜ : Set X))) :=
    (hι₁.continuous.comp continuous_subtype_val).subtype_mk _
  have hinj' : Function.Injective
      (fun v : goodOpen ι₁ hι₁ B hB => (⟨ι₁ v.val, v.2⟩ : (Bᶜ : Set X))) := by
    intro a b hab
    exact Subtype.ext (hinj a.2 b.2 (congrArg Subtype.val hab))
  have hemb := (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap hcont hinj'
    hcl).isEmbedding
  rw [hemb.continuous_iff]
  have hcomp : ((fun v : goodOpen ι₁ hι₁ B hB => (⟨ι₁ v.val, v.2⟩ : (Bᶜ : Set X))) ∘
      transition hι₁ hι₂ hB hrange) = fun y => ⟨ι₂ y.val, y.2⟩ :=
    funext fun y => Subtype.ext (transition_spec hι₁ hι₂ hB hrange y)
  rw [hcomp]
  exact (hι₂.continuous.comp continuous_subtype_val).subtype_mk _

omit [IsComplexManifold k V₂] in
/-- The transition is holomorphic when `ι₁` is an immersion over `X \ B`. -/
theorem contMDiff_transition (hinj : InjOn ι₁ (ι₁ ⁻¹' Bᶜ))
    (himm : ∀ v, ι₁ v ∉ B → v ∉ nonImmersionLocus k n ι₁) :
    ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ (transition hι₁ hι₂ hB hrange) := by
  have hval : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞
      (fun y : goodOpen ι₂ hι₂ B hB => (transition hι₁ hι₂ hB hrange y).val) := by
    intro y
    obtain ⟨r, hr, hev⟩ := exists_local_retraction hι₁
      (himm _ (transition hι₁ hι₂ hB hrange y).2)
    have hc : ContinuousAt
        (fun y' : goodOpen ι₂ hι₂ B hB => (transition hι₁ hι₂ hB hrange y').val) y :=
      (continuous_subtype_val.comp (continuous_transition hι₁ hι₂ hB hrange hinj)).continuousAt
    have hev' : (fun y' : goodOpen ι₂ hι₂ B hB => (transition hι₁ hι₂ hB hrange y').val) =ᶠ[𝓝 y]
        fun y' => r (ι₂ y'.val) := by
      filter_upwards [hc.eventually hev] with y' hy'
      rw [← transition_spec hι₁ hι₂ hB hrange y']
      exact hy'.symm
    have hrr : ContMDiffAt 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞
        (fun y' : goodOpen ι₂ hι₂ B hB => r (ι₂ y'.val)) y := by
      have h := hr
      rw [transition_spec hι₁ hι₂ hB hrange y] at h
      exact h.comp y ((hι₂.comp contMDiff_subtype_val) y)
    exact hrr.congr_of_eventuallyEq hev'
  exact BlowupRestrictOpen.contMDiff_opens_mk hval fun y => (transition hι₁ hι₂ hB hrange y).2

end Transition

/-- Two maps with the same image: every value of the second is a value of the first. -/
theorem exists_eq_of_range_eq {V₁ V₂ X : Type*} {ι₁ : V₁ → X} {ι₂ : V₂ → X}
    (hrange : range ι₁ = range ι₂) (w : V₂) : ∃ v, ι₁ v = ι₂ w := by
  have h : ι₂ w ∈ range ι₁ := by rw [hrange]; exact mem_range_self w
  exact h

/-- **The transition biholomorphism.** If `ι₁`, `ι₂` have the same image, are injective
immersions over `X \ B`, then `ι₁⁻¹ ∘ ι₂` is a biholomorphism between their good loci. -/
def transitionDiffeomorph {k n : ℕ} {V₁ V₂ X : Type u}
    [TopologicalSpace V₁] [ChartedSpace (ComplexModel k) V₁] [IsComplexManifold k V₁]
    [CompactSpace V₁]
    [TopologicalSpace V₂] [ChartedSpace (ComplexModel k) V₂] [IsComplexManifold k V₂]
    [CompactSpace V₂]
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {ι₁ : V₁ → X} {ι₂ : V₂ → X}
    (hι₁ : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι₁)
    (hι₂ : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι₂)
    {B : Set X} (hB : IsClosed B) (hrange : range ι₁ = range ι₂)
    (hinj₁ : InjOn ι₁ (ι₁ ⁻¹' Bᶜ)) (hinj₂ : InjOn ι₂ (ι₂ ⁻¹' Bᶜ))
    (himm₁ : ∀ v, ι₁ v ∉ B → v ∉ nonImmersionLocus k n ι₁)
    (himm₂ : ∀ v, ι₂ v ∉ B → v ∉ nonImmersionLocus k n ι₂) :
    HironakaEmbeddedCommon.goodOpen ι₂ hι₂ B hB ≃ₘ⟮𝓘(ℂ, ComplexModel k), 𝓘(ℂ, ComplexModel k)⟯
      HironakaEmbeddedCommon.goodOpen ι₁ hι₁ B hB :=
  let h₁₂ : ∀ w, ∃ v, ι₁ v = ι₂ w := exists_eq_of_range_eq hrange
  let h₂₁ : ∀ w, ∃ v, ι₂ v = ι₁ w := exists_eq_of_range_eq hrange.symm
  { toFun := transition hι₁ hι₂ hB h₁₂
    invFun := transition hι₂ hι₁ hB h₂₁
    left_inv := fun y => Subtype.ext (hinj₂ (transition hι₂ hι₁ hB h₂₁ _).2 y.2
      (by rw [transition_spec hι₂ hι₁ hB h₂₁, transition_spec hι₁ hι₂ hB h₁₂]))
    right_inv := fun y => Subtype.ext (hinj₁ (transition hι₁ hι₂ hB h₁₂ _).2 y.2
      (by rw [transition_spec hι₁ hι₂ hB h₁₂, transition_spec hι₂ hι₁ hB h₂₁]))
    contMDiff_toFun := contMDiff_transition hι₁ hι₂ hB h₁₂ hinj₁ himm₁
    contMDiff_invFun := contMDiff_transition hι₂ hι₁ hB h₂₁ hinj₂ himm₂ }

theorem transitionDiffeomorph_spec {k n : ℕ} {V₁ V₂ X : Type u}
    [TopologicalSpace V₁] [ChartedSpace (ComplexModel k) V₁] [IsComplexManifold k V₁]
    [CompactSpace V₁]
    [TopologicalSpace V₂] [ChartedSpace (ComplexModel k) V₂] [IsComplexManifold k V₂]
    [CompactSpace V₂]
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {ι₁ : V₁ → X} {ι₂ : V₂ → X}
    (hι₁ : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι₁)
    (hι₂ : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι₂)
    {B : Set X} (hB : IsClosed B) (hrange : range ι₁ = range ι₂)
    (hinj₁ : InjOn ι₁ (ι₁ ⁻¹' Bᶜ)) (hinj₂ : InjOn ι₂ (ι₂ ⁻¹' Bᶜ))
    (himm₁ : ∀ v, ι₁ v ∉ B → v ∉ nonImmersionLocus k n ι₁)
    (himm₂ : ∀ v, ι₂ v ∉ B → v ∉ nonImmersionLocus k n ι₂)
    (y : HironakaEmbeddedCommon.goodOpen ι₂ hι₂ B hB) :
    ι₁ (transitionDiffeomorph hι₁ hι₂ hB hrange hinj₁ hinj₂ himm₁ himm₂ y).val = ι₂ y.val :=
  transition_spec hι₁ hι₂ hB (exists_eq_of_range_eq hrange) y

end SGPT.Trace.P5Wire
