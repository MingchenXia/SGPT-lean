import SGPT.PSH.CompactPrimeOver
import SGPT.Foundations.Analysis.Pending.HironakaChowLemma
import SGPT.Foundations.Analysis.Pending.EmbeddedResolution
import SGPT.Foundations.Analysis.Pending.StrictTransformComposition

/-!
# Realizing a prime divisor over a compact complex manifold on a modification

Source `cor:primerealization` (`appendix_unibranch.tex`): *let `X` be an irreducible compact
complex space and `E` a prime divisor over `X`; then there is a modification `π : Y → X` such
that `Y` is smooth and `E` can be realized as a prime divisor on `Y`.*

The book's proof: choose a smooth model `X' → X` on which `E` is realized; by Hironaka's Chow
lemma (`thm:HironakaChow`) it is dominated by a modification `Y → X`; after a further embedded
resolution, the strict transform of `E` on `Y` is smooth, and it realizes the same prime
divisor.

This file formalizes this argument when `X` is a compact complex manifold (prime divisors over
`X` are `SGPT.PSH.CompactPrimeOver.PrimePresentation`s, equivalence is
`commonResolutionRelation`, modifications are finite compositions of blowups with smooth centres,
`IsBlowupSequence`). Hironaka's Chow lemma for compact complex manifolds is **not** proved in
this project; it enters as the named hypothesis
`SGPT.Foundations.Analysis.Pending.HironakaChowLemma.HironakaChowLemmaManifold`. The embedded
resolution of the strict transform is the project's
`SGPT.Foundations.Analysis.Pending.EmbeddedResolution.exists_embeddedResolution`.

Main declaration: `exists_blowupSequence_realization_of_chow`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Unibranch.PrimeRealization

open Set
open scoped Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.BlowupTowers
  AnalyticModificationLocalDiscrepancy SGPT.PSH.CompactPrimeOver

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

omit [IsComplexManifold n X] in
/-- The identity has empty exceptional locus. -/
theorem exceptionalLocus_id : exceptionalLocus n (id : X → X) = ∅ := by
  ext x
  simp only [exceptionalLocus, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_not]
  rw [mfderiv_id]
  exact Function.bijective_id

omit [IsComplexManifold n X] in
/-- The strict transform of a closed set under the identity is the set itself. -/
theorem strictTransform_id_of_isClosed {A : Set X} (hA : IsClosed A) :
    strictTransform n (id : X → X) A = A := by
  rw [strictTransform, exceptionalLocus_id, sdiff_empty, preimage_id]
  exact hA.closure_eq

/-- **`cor:primerealization` for a compact complex manifold, conditional on Hironaka's Chow
lemma.** Assume Hironaka's Chow lemma for compact complex manifolds
(`HironakaChowLemmaManifold`, the manifold case of `thm:HironakaChow`). Let `X` be a compact
complex manifold and `p` a prime divisor over `X`. Then there is a prime divisor `q` over `X`,
equivalent to `p` (`commonResolutionRelation p q`), which is realized on a modification of `X`:
its model `q.model → X` is a finite composition of blowups with smooth centres (in particular
`q.model` is smooth), and its divisor is a smooth connected hypersurface of `q.model`. -/
theorem exists_blowupSequence_realization_of_chow
    (hChow : HironakaChowLemma.HironakaChowLemmaManifold.{u}) [CompactSpace X]
    (p : PrimePresentation n X) :
    ∃ q : PrimePresentation n X,
      IsBlowupSequence n X q.model q.projection ∧ commonResolutionRelation p q := by
  classical
  obtain ⟨X', tX', cX', mX', σ, g, hσ, hg, hcomm⟩ :=
    hChow n X p.model p.projection p.modification
  let := tX'
  let := cX'
  let := mX'
  have hσmod : IsAnalyticModification (n := n) σ :=
    HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hσ
  have hgmod : IsAnalyticModification (n := n) g :=
    AnalyticModelDomination.isAnalyticModification_of_holomorphic_over
      p.modification hσmod hg hcomm
  let : CompactSpace X' :=
    AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification hσmod
  obtain ⟨VD, hVD, hdimD⟩ :=
    SourceGenericSubmanifoldMinimum.exists_subvariety_carrier_eq_of_submanifold p.smooth
  have hcodim : VD.dim + 1 = n := by rw [hdimD]; exact p.codimension_one
  obtain ⟨VL, hVL, hdimL, -, -⟩ :=
    AnalyticModificationDivisorStrictTransform.exists_strictTransform_reader hgmod VD hcodim
  obtain ⟨Xt, tXt, cXt, mXt, μ, hμ, hres⟩ := EmbeddedResolution.exists_embeddedResolution VL
  let := tXt
  let := cXt
  let := mXt
  have hμmod : IsAnalyticModification (n := n) μ :=
    HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hμ
  let S : Set Xt := strictTransform n μ VL.carrier
  have hS : IsClosedConnectedSubmanifold n S VL.dim := hres.2
  let q : PrimePresentation n X :=
    { model := CMfd.of Xt
      projection := σ ∘ μ
      modification := AnalyticModificationComposition.isAnalyticModification_comp hσmod hμmod
      divisor := S
      divisorDimension := VL.dim
      smooth := hS
      codimension_one := by rw [hdimL]; exact hcodim }
  have hq : IsBlowupSequence n X Xt (σ ∘ μ) := HironakaChowLemma.isBlowupSequence_comp hσ hμ
  refine ⟨q, hq, ⟨?_⟩⟩
  refine
    { model := CMfd.of Xt
      left := g ∘ μ
      right := id
      left_modification := AnalyticModificationComposition.isAnalyticModification_comp hgmod hμmod
      right_modification := HironakaChowLemma.isAnalyticModification_id
      over_base := ?_
      strict_equal := ?_ }
  · change p.projection ∘ (g ∘ μ) = (σ ∘ μ) ∘ id
    rw [← Function.comp_assoc, hcomm]
    rfl
  · change strictTransform n (g ∘ μ) p.divisor = strictTransform n (id : Xt → Xt) S
    rw [strictTransform_id_of_isClosed hS.1,
      StrictTransformComposition.strictTransform_comp hg hμ.contMDiff, ← hVD, ← hVL]

end SGPT.Unibranch.PrimeRealization
