import SGPT.Unibranch.KS3KahlerResolution

/-!
# `def:unibranch:L212` on an irreducible unibranch compact Kähler space

Source `def:unibranch:L212` (`appendix_unibranch.tex`, §`sec:unib_ext`): `X` is an
irreducible unibranch compact Kähler space, `θ` a closed real smooth `(1,1)`-form on `X`,
`φ ∈ PSH(X, θ)`; `P_θ[φ]_𝓘 ∈ PSH(X, θ)` is *the unique element* with
`π^* P_θ[φ]_𝓘 = P_{π^*θ}[π^*φ]_𝓘` for every proper bimeromorphic `π : Y → X` from a compact
Kähler manifold `Y`; "it follows from `cor:PSH` and `prop:Ienvelopebimero` that `P_θ[φ]_𝓘` is
independent of the choice of `π` and is well-defined".

Lane KS proved the well-definedness for unibranch `X` given a resolution of `X` by a connected
compact Kähler manifold and `cor:PSH` along it.  Here the resolution is produced for the book's
`X` (`KS3KahlerResolution.exists_kahlerResolution_of_kahlerBlowupStep`, from `G11` and Kähler
preservation under blowups with smooth centres), so the theorem is stated in the book's
generality:

* `connectedSpace_of_isIrreducible`: an irreducible complex space is connected (clopen sets are
  analytic);
* `existsUnique_isUnibranchIEnvelope_of_isIrreducible`: for `X` irreducible, unibranch, compact,
  Kähler (`IsKahlerSpace`), `θ` closed `(1,1)`, `φ` `θ`-psh, exactly one `ψ` satisfies the
  defining property `IsUnibranchIEnvelopeAnyDim` (compact Kähler manifolds `Y` of every
  dimension), given `cor:PSH` (reverse descent along proper bimeromorphic maps,
  `KSUnibranchIEnvelope.CorPSHDescentAlong`) and `KahlerBlowupStep`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.IEnvelope

namespace SGPT.Unibranch.KS3UnibranchIEnvelope

open SourceReducedComplexSpace KSUnibranchIEnvelope KS3KahlerResolution

/-- Clopen subsets of a complex space are analytic. -/
theorem isAnalyticSubset_of_isClopen {X : SourceReducedComplexSpace} {U : Set X.obj.left}
    (hU : IsClopen U) : X.IsAnalyticSubset U := by
  intro x
  let e := LocalEmbedding.ofPoint X x
  refine ⟨e, LocalEmbedding.mem_range_ofPoint X x,
    (Subtype.val : e.carrier → e.ambient) '' (e.toPoint ⁻¹' U), ?_, ?_⟩
  · set K : Set e.ambient := (Subtype.val : e.carrier → e.ambient) '' (e.toPoint ⁻¹' U)
    have hKc : IsClosed K := by
      have hcl : IsClosed (e.toPoint ⁻¹' U) :=
        hU.1.preimage e.isOpenEmbedding_toPoint.continuous
      exact e.analytic.isClosed.isClosedEmbedding_subtypeVal.isClosedMap _ hcl
    apply SGPT.Foundations.Analysis.Pending.AnalyticSubsetOpens.isComplexAnalyticSubset_of_forall_opens
    intro u
    by_cases hu : u ∈ K
    · obtain ⟨c, hc, rfl⟩ := hu
      have hop : IsOpen (e.toPoint ⁻¹' U) := hU.2.preimage e.isOpenEmbedding_toPoint.continuous
      obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp hop
      refine ⟨⟨O, hO⟩, by change c.val ∈ O; rw [← mem_preimage, hOeq]; exact hc, ?_⟩
      have heq : ((↑) ⁻¹' K : Set (⟨O, hO⟩ : Opens e.ambient)) =
          (↑) ⁻¹' e.carrier := by
        ext w
        constructor
        · rintro ⟨c', -, hc'⟩
          change w.val ∈ e.carrier
          rw [← hc']
          exact c'.property
        · intro hw
          refine ⟨⟨w.val, hw⟩, ?_, rfl⟩
          change (⟨w.val, hw⟩ : e.carrier) ∈ e.toPoint ⁻¹' U
          rw [← hOeq]
          exact w.property
      rw [heq]
      exact SGPT.Foundations.Analysis.Pending.AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val
        e.analytic ⟨O, hO⟩
    · refine ⟨⟨Kᶜ, hKc.isOpen_compl⟩, hu, ?_⟩
      have heq : ((↑) ⁻¹' K : Set (⟨Kᶜ, hKc.isOpen_compl⟩ : Opens e.ambient)) = ∅ := by
        ext w
        simp only [mem_preimage, mem_empty_iff_false, iff_false]
        exact w.property
      rw [heq]
      exact isComplexAnalyticSubset_empty
  · exact (preimage_image_eq _ Subtype.val_injective).symm

/-- **An irreducible complex space is connected.** -/
theorem connectedSpace_of_isIrreducible {X : SourceReducedComplexSpace}
    (hirr : X.IsIrreducibleAnalyticSubset univ) : ConnectedSpace X.obj.left := by
  obtain ⟨-, ⟨x, -⟩, hsplit⟩ := hirr
  refine connectedSpace_iff_univ.mpr ⟨⟨x, mem_univ x⟩, ?_⟩
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed isClosed_univ]
  intro u v hu hv huv hdisj
  have hv' : v = uᶜ := by
    ext w
    constructor
    · intro hw hwu
      exact (Set.disjoint_left.mp hdisj) hwu hw
    · intro hw
      exact ((huv (mem_univ w)).resolve_left hw)
  have huo : IsOpen u := by rw [← isClosed_compl_iff, ← hv']; exact hv
  have hcl : IsClopen u := ⟨hu, huo⟩
  have hcl' : IsClopen uᶜ := hcl.compl
  rcases hsplit u uᶜ (isAnalyticSubset_of_isClopen hcl) (isAnalyticSubset_of_isClopen hcl')
      (subset_univ _) (subset_univ _) (union_compl_self u).symm with h | h
  · left; rw [← h]
  · right; rw [hv', ← h]

/-- **Source `def:unibranch:L212`, well-definedness, on an irreducible unibranch compact Kähler
space.**  Let `X` be an irreducible unibranch compact Kähler space, `θ` a closed smooth real
`(1,1)`-form on `X` and `φ ∈ PSH(X, θ)`.  There is exactly one `ψ` such that `ψ ∈ PSH(X, θ)` and
`π^*ψ = P_{π^*θ}[π^*φ]_𝓘` for every proper bimeromorphic `π : Y → X` from a compact Kähler
manifold `Y` (`IsUnibranchIEnvelopeAnyDim`).

Hypotheses beyond the book's: `cor:PSH` (its reverse-descent half, `hcorPSH`; lane PD) and Kähler
preservation under blowups with smooth centres (`hstep`). -/
theorem existsUnique_isUnibranchIEnvelope_of_isIrreducible (hstep : KahlerBlowupStep)
    {X : SourceReducedComplexSpace} [CompactSpace X.obj.left]
    (hirr : X.IsIrreducibleAnalyticSubset univ) (hX : X.IsUnibranch) (hK : X.IsKahlerSpace)
    (θ : SpaceForm X 2) (hθc : θ.IsClosed) (hθ : θ.IsOneOne)
    {φ : X.obj.left → EReal} (hφ : X.IsThetaPSH θ φ)
    (hcorPSH : ∀ (Y : SourceReducedComplexSpace) (π : Y ⟶ X), IsProperBimeromorphic π →
      CorPSHDescentAlong π θ) :
    ∃! ψ : X.obj.left → EReal, IsUnibranchIEnvelopeAnyDim X θ φ ψ := by
  have := connectedSpace_of_isIrreducible hirr
  obtain ⟨n, ⟨R⟩⟩ := exists_kahlerResolution_of_kahlerBlowupStep hstep X hX hK
  exact existsUnique_isUnibranchIEnvelopeAnyDim hX θ hθc hθ hφ R
    (hcorPSH _ R.map R.isProperBimeromorphic)

end SGPT.Unibranch.KS3UnibranchIEnvelope
