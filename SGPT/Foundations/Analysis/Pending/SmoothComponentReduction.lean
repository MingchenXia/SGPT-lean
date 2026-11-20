import SGPT.Foundations.Analysis.FirstPass.BlowupSequences
import SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolume
import SGPT.Foundations.Analysis.FirstPass.ClosedFormPullback
import SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
import SGPT.Foundations.Analysis.Pending.BlowupConnected
import SGPT.Foundations.Analysis.Pending.EmbeddedResolution
import SGPT.Foundations.Analysis.Pending.IrreducibleComponentFilling
import SGPT.Foundations.Analysis.Pending.NonKahlerLocusPoleSet
import SGPT.Foundations.Analysis.Pending.StrictTransformSequenceLocus

set_option autoImplicit false

/-!
# Reduction to a smooth component

Source: Copy-4, `lem:resolution` and the standing assumptions of `sec:setup`
(`transcendental-nakamaye-copy4-20260911`); blueprint `ana:resolution`.

Let `X` be a connected compact Kähler manifold, `α = {θ}` big, and `V` a
positive-dimensional irreducible component of `E_nK(α)` with `V ⊄ E_nn(α)`.  There
is a modification `μ : X̃ → X`, an isomorphism over `X \ V_sing`, whose strict
transform `Ṽ` is a closed connected smooth submanifold, such that the triple
`(X̃, μ^* α, Ṽ)` satisfies the standing assumptions: `X̃` is a connected compact
Kähler manifold, `μ^* α` is big, `Ṽ` is an irreducible component of
`E_nK(μ^* α)` of dimension `dim V`, not contained in `E_nn(μ^* α)`, and
`⟨(μ^* α)^k⟩_{X̃|Ṽ} = ⟨α^k⟩_{X|V}`.

Encoding notes.  A modification is an `IsBlowupSequence`.  The class `μ^* α` is
represented by `μ^* θ`.  The non-nef locus and restricted volume are independent
of the Kähler form (compare `ε ω'` with `C ε ω`), so they are asserted for every
Kähler form on `X̃`.

PROOF.  Everything here is now derived from one named classical input and the modification
lemmas that the workspace already proves:

* `Pending.EmbeddedResolution.exists_embeddedResolution` (Hironaka) supplies `μ`, the
  isomorphism over `X \ V_sing`, and the smoothness of the strict transform.  It is the
  purely geometric half, isolated as human decision I-0198 requires.

Remmert's proper mapping theorem is NOT used (human decision I-0739, item 1, for the bypass of
I-0660): the maximality half of `IsIrreducibleComponent` is transported from `X` up to `X̃` by
`Pending.IrreducibleComponentFilling.isIrreducibleComponent_of_preimage`, which never forms
the image of a subvariety.

`ConnectedSpace X̃` is NOT assumed: `Pending.BlowupConnected.connectedSpace_of_isBlowupSequence`
is sorry-free.

Everything else is proved: compactness and the Kähler background and bigness of `μ^* α` from
`Pending.LocusProperties`, `E_nK(μ^* α) = μ⁻¹ E_nK(α) ∪ Exc μ` and
`E_nn(μ^* α) = μ⁻¹ E_nn(α)` likewise, the restricted-volume identity from birational
invariance, and the clause `Ṽ ⊄ E_nn(μ^* α)` from
`Pending.StrictTransformSequenceLocus.not_strictTransform_subset_nonNefLocus`.

The maximality argument.  Let `Z ⊇ Ṽ` be irreducible with `Z ⊆ E_nK(μ^* α) = μ⁻¹ E_nK(α) ∪ Exc μ`.
`E_nK(α)` is analytic, and an irreducible component fills it near some of its points: there is
an open `U` with `E_nK(α) ∩ U ⊆ V` containing a point `x` at which `V` is regular of dimension
`dim V` (`IrreducibleComponentFilling.exists_mem_regularLocus_isOpen_inter_subset`).  Since `μ`
is an isomorphism over `X \ V_sing`, `x ∉ μ(Exc μ)`, so `x = μ(y)` with `y ∈ Ṽ \ Exc μ`.  On the
open set `N = μ⁻¹ U \ Exc μ ∋ y`, every `z ∈ Z` has `μ z ∈ E_nK(α) ∩ U ⊆ V`, so
`z ∈ μ⁻¹ V \ Exc μ ⊆ Ṽ`; thus `Z ∩ N` is a nonempty relatively open part of `Z` inside the
analytic set `Ṽ`, whence `Z ⊆ Ṽ` (`StrictTransformLocus.subset_of_inter_isOpen_subset`).
-/

open Set

universe u

namespace SGPT.Foundations.Analysis.Pending.SmoothComponentReduction

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.NumericalRestrictedVolume FirstPass.BlowupSequences

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **Reduction to a smooth component** (Copy-4, `lem:resolution`). -/
theorem exists_modification_smooth_component [CompactSpace X] [ConnectedSpace X]
    (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (V : ClosedIrreducibleAnalyticSubvariety n X) (hdim_pos : 0 < V.dim)
    (hcomponent :
      IsIrreducibleComponent V (nonKahlerLocus (RealBottChern.ofRepresentative θ)))
    (hnonNef : ¬ V.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ)) :
    ∃ (Xt : Type u) (_ : TopologicalSpace Xt) (_ : ChartedSpace (ComplexModel n) Xt)
      (_ : IsComplexManifold n Xt) (μ : Xt → X) (hμ : IsBlowupSequence n X Xt μ),
      IsIsomorphismOver n μ (singularLocus V)ᶜ ∧
      CompactSpace Xt ∧ ConnectedSpace Xt ∧ Nonempty (KahlerBackground n Xt) ∧
      IsBigClass (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hμ.contMDiff θ)) ∧
      ∃ Vt : ClosedIrreducibleAnalyticSubvariety n Xt,
        Vt.carrier = strictTransform n μ V.carrier ∧
        IsClosedConnectedSubmanifold n Vt.carrier Vt.dim ∧
        Vt.dim = V.dim ∧
        IsIrreducibleComponent Vt (nonKahlerLocus (RealBottChern.ofRepresentative
          (ClosedRealOneOneForm.pullback hμ.contMDiff θ))) ∧
        ∀ omegaT : KahlerBackground n Xt,
          ¬ Vt.carrier ⊆ nonNefLocus omegaT (RealBottChern.ofRepresentative
            (ClosedRealOneOneForm.pullback hμ.contMDiff θ)) ∧
          numericalRestrictedVolume omegaT (RealBottChern.ofRepresentative
              (ClosedRealOneOneForm.pullback hμ.contMDiff θ)) Vt =
            numericalRestrictedVolume omega (RealBottChern.ofRepresentative θ) V := by
  have hn : 0 < n := hdim_pos.trans_le V.dim_le
  obtain ⟨Xt, _instXt, _chartXt, _mfdXt, μ, hμ, hiso, hsmooth⟩ :=
    EmbeddedResolution.exists_embeddedResolution V
  obtain ⟨hcompactXt, hsurj⟩ :=
    StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hμ
  have := hcompactXt
  have hconnXt : ConnectedSpace Xt :=
    BlowupConnected.connectedSpace_of_isBlowupSequence μ hμ
  obtain ⟨-, hkahlerXt⟩ :=
    LocusProperties.compactSpace_and_kahler_of_isBlowupSequence ⟨omega⟩ μ hμ
  have hbigXt : IsBigClass (RealBottChern.ofRepresentative
      (ClosedRealOneOneForm.pullback hμ.contMDiff θ)) :=
    LocusProperties.isBigClass_pullback ⟨omega⟩ θ hbig μ hμ
  -- The exceptional set of the resolution sits over the singular locus of `V`.
  have hExcS : μ '' exceptionalLocus n μ ⊆ singularLocus V := by
    rintro _ ⟨z, hz, rfl⟩
    by_contra hc
    exact Set.disjoint_left.mp hiso.2 (show z ∈ μ ⁻¹' (singularLocus V)ᶜ from hc) hz
  have hregV : ∀ x ∈ regularLocus (n := n) V.carrier V.dim,
      x ∈ V.carrier ∧ x ∉ μ '' exceptionalLocus n μ := by
    intro x hx
    exact ⟨regularLocus_subset _ _ hx, fun h => (hExcS h).2 hx⟩
  have hVnotExc : ¬ V.carrier ⊆ μ '' exceptionalLocus n μ := by
    obtain ⟨x, hx⟩ := V.regularLocus_nonempty
    exact fun h => (hregV x hx).2 (h (hregV x hx).1)
  -- The strict transform, with its dimension and its restricted volume.
  obtain ⟨Vt, hVc, hVd, hVvol⟩ :=
    LocusProperties.exists_strictTransform_numericalRestrictedVolume_eq ⟨omega⟩ θ hbig μ hμ
      V hdim_pos hVnotExc
  have hstSub : strictTransform n μ V.carrier ⊆ μ ⁻¹' V.carrier :=
    closure_minimal Set.sdiff_subset (V.isClosed_carrier.preimage hμ.contMDiff.continuous)
  have hnk := LocusProperties.nonKahlerLocus_pullback ⟨omega⟩ θ hbig μ hμ
  -- `Ṽ` is an irreducible component of the non-Kähler locus upstairs (no image is formed).
  have hA : IsComplexAnalyticSubset (n := n) (nonKahlerLocus (RealBottChern.ofRepresentative θ)) :=
    NonKahlerLocusPoleSet.isComplexAnalyticSubset_nonKahlerLocus hn _ hbig
  have hcomponentT : IsIrreducibleComponent Vt
      (nonKahlerLocus (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hμ.contMDiff θ))) := by
    refine IrreducibleComponentFilling.isIrreducibleComponent_of_preimage
      hμ.contMDiff.continuous hA hcomponent
      (StrictTransformSequenceLocus.isClosed_exceptionalLocus hμ.contMDiff) hnk.le Vt ?_ ?_ ?_
    · rw [hVc, hnk]
      exact fun y hy => Or.inl (hcomponent.1 (hstSub hy))
    · rw [hVc]
      exact subset_closure
    · intro x hx
      obtain ⟨z, hz, hzx⟩ := StrictTransformSequenceLocus.mem_image_strictTransform_of_not_mem
        hsurj (hregV x hx).1 (hregV x hx).2
      exact ⟨z, hVc ▸ hz, fun hzE => (hregV x hx).2 ⟨z, hzE, hzx⟩, hzx⟩
  refine ⟨Xt, _instXt, _chartXt, _mfdXt, μ, hμ, hiso, hcompactXt, hconnXt, hkahlerXt,
    hbigXt, Vt, hVc, ?_, hVd, hcomponentT, fun omegaT => ⟨?_, hVvol omega omegaT⟩⟩
  · rw [hVc, hVd]
    exact hsmooth
  · rw [hVc]
    exact StrictTransformSequenceLocus.not_strictTransform_subset_nonNefLocus hn omega omegaT
      θ hbig hμ V hVnotExc hnonNef

end

end SGPT.Foundations.Analysis.Pending.SmoothComponentReduction
