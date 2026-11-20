import SGPT.Foundations.Analysis.Pending.StrictTransformLocus
import SGPT.Foundations.Analysis.Pending.LocusProperties

set_option autoImplicit false

/-!
# Strict transforms along a whole modification

Source: CT22, Lemma 4.3 and its use in Lemma 4.4; blueprint `ana:rv-birational-blowup`.

`Pending.StrictTransformLocus` proves, for ONE blowup `g : Z → Y` with smooth centre, that a
subvariety `W ⊄ g(Exc g)` has `W̃ ⊄ E_nn(g^* α)` whenever `W ⊄ E_nn(α)`.  The reduction to a
smooth component needs the same statement for a whole sequence of blowups.

The one-blowup proof uses only three properties of `g`: surjectivity, closedness of
`g(Exc g)`, and the transformation rule `E_nn(g^* α) = g⁻¹ E_nn(α)`.  All three hold for a
sequence (`StrictTransformComposition.IsBlowupSequence.compactSpace_surjective`,
`StrictTransformComposition.isOpen_compl_exceptionalLocus`, and
`LocusProperties.nonNefLocus_pullback`), so the argument is repeated here at that level rather
than being run through an induction over `IsBlowupSequence`.

Everything in this file is proved.
-/

open Set
open scoped Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.StrictTransformSequenceLocus

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.BlowupSequences
  StrictTransformLocus

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  {Xt : Type u} [TopologicalSpace Xt] [ChartedSpace (ComplexModel n) Xt]
  [IsComplexManifold n Xt]

/-- The exceptional locus of a holomorphic map is closed. -/
theorem isClosed_exceptionalLocus {μ : Xt → X}
    (hμ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ μ) :
    IsClosed (exceptionalLocus n μ) :=
  isOpen_compl_iff.mp (StrictTransformComposition.isOpen_compl_exceptionalLocus hμ)

/-- The image of the exceptional locus of a modification is closed. -/
theorem isClosed_image_exceptionalLocus [CompactSpace X] {μ : Xt → X}
    (hμ : IsBlowupSequence n X Xt μ) : IsClosed (μ '' exceptionalLocus n μ) := by
  obtain ⟨hcompact, -⟩ :=
    StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hμ
  have := hcompact
  exact ((isClosed_exceptionalLocus hμ.contMDiff).isCompact.image
    hμ.contMDiff.continuous).isClosed

omit [IsComplexManifold n X] [IsComplexManifold n Xt] in
/-- Off the image of the exceptional locus, a set lies in the image of its strict transform.
Only surjectivity of the map is used. -/
theorem mem_image_strictTransform_of_not_mem {μ : Xt → X} (hsurj : Function.Surjective μ)
    {W : Set X} {w : X} (hwW : w ∈ W) (hwE : w ∉ μ '' exceptionalLocus n μ) :
    ∃ z ∈ strictTransform n μ W, μ z = w := by
  obtain ⟨z, rfl⟩ := hsurj w
  exact ⟨z, subset_closure ⟨hwW, fun hz => hwE ⟨z, hz, rfl⟩⟩, rfl⟩

/-- A strict transform contained in the preimage of an analytic set forces the subvariety into
that set. -/
theorem not_strictTransform_subset_preimage [CompactSpace X] {μ : Xt → X}
    (hμ : IsBlowupSequence n X Xt μ) (W : ClosedIrreducibleAnalyticSubvariety n X)
    (hW : ¬ W.carrier ⊆ μ '' exceptionalLocus n μ) {A : Set X}
    (hA : IsComplexAnalyticSubset (n := n) A) (h : ¬ W.carrier ⊆ A) :
    ¬ strictTransform n μ W.carrier ⊆ μ ⁻¹' A := by
  obtain ⟨-, hsurj⟩ := StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hμ
  intro hsub
  refine h (subset_of_inter_isOpen_subset W hA
    (isClosed_image_exceptionalLocus hμ).isOpen_compl ?_ ?_)
  · obtain ⟨w, hwW, hwE⟩ := not_subset.mp hW
    exact ⟨w, hwW, hwE⟩
  · rintro w ⟨hwW, hwE⟩
    obtain ⟨z, hz, rfl⟩ := mem_image_strictTransform_of_not_mem hsurj hwW hwE
    exact hsub hz

/-- **The strict transform of a subvariety not contained in `E_nn(α)` is not contained in
`E_nn(μ^* α)`**, for a whole modification `μ`. -/
theorem not_strictTransform_subset_nonNefLocus [CompactSpace X] (hn : 0 < n)
    (omega : KahlerBackground n X) (omegaT : KahlerBackground n Xt)
    (θ : ClosedRealOneOneForm n X) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {μ : Xt → X} (hμ : IsBlowupSequence n X Xt μ)
    (W : ClosedIrreducibleAnalyticSubvariety n X)
    (hW : ¬ W.carrier ⊆ μ '' exceptionalLocus n μ)
    (h : ¬ W.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ)) :
    ¬ strictTransform n μ W.carrier ⊆ nonNefLocus omegaT
      (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hμ.contMDiff θ)) := by
  obtain ⟨-, hsurj⟩ := StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hμ
  intro hsub
  rw [LocusProperties.nonNefLocus_pullback omega θ hbig μ hμ omegaT] at hsub
  set alpha := RealBottChern.ofRepresentative θ with halpha
  let A : ℕ → Set X := fun m =>
    nonKahlerLocus (alpha + ((1 : ℝ) / ((m : ℝ) + 1)) • RealBottChern.ofRepresentative omega.form)
  have hpos : ∀ m : ℕ, (0 : ℝ) < 1 / ((m : ℝ) + 1) := fun m => Nat.one_div_pos_of_nat
  have hA : ∀ m, IsComplexAnalyticSubset (n := n) (A m) := by
    intro m
    obtain ⟨T⟩ := hbig
    exact NonKahlerLocusPoleSet.isComplexAnalyticSubset_nonKahlerLocus hn _
      ⟨T.addSmulKahler omega (hpos m)⟩
  have hAsub : ∀ m, A m ⊆ nonNefLocus omega alpha := fun m x hx =>
    mem_nonNefLocus.mpr ⟨⟨_, hpos m⟩, hx⟩
  have hunion : W.carrier ∩ (μ '' exceptionalLocus n μ)ᶜ ⊆ ⋃ m, A m := by
    rintro w ⟨hwW, hwE⟩
    obtain ⟨z, hz, rfl⟩ := mem_image_strictTransform_of_not_mem hsurj hwW hwE
    obtain ⟨epsilon, hx⟩ := mem_nonNefLocus.mp (hsub hz)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt epsilon.2
    refine mem_iUnion.mpr ⟨m, fun T => ?_⟩
    have hd : (0 : ℝ) < (epsilon : ℝ) - 1 / ((m : ℝ) + 1) := sub_pos.mpr hm
    have hclass : alpha + ((1 : ℝ) / ((m : ℝ) + 1)) • RealBottChern.ofRepresentative omega.form +
        ((epsilon : ℝ) - 1 / ((m : ℝ) + 1)) • RealBottChern.ofRepresentative omega.form =
        alpha + (epsilon : ℝ) • RealBottChern.ofRepresentative omega.form := by
      module
    exact hx (NonNefLocusKahlerIndependence.KahlerCurrent.ofEq hclass (T.addSmulKahler omega hd))
  obtain ⟨m, hm⟩ := exists_subset_of_inter_isOpen_subset_iUnion W hA
    (isClosed_image_exceptionalLocus hμ).isOpen_compl
    (by obtain ⟨w, hwW, hwE⟩ := not_subset.mp hW; exact ⟨w, hwW, hwE⟩) hunion
  exact h (hm.trans (hAsub m))

end

end SGPT.Foundations.Analysis.Pending.StrictTransformSequenceLocus
