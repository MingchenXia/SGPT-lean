import SGPT.Okounkov.OriginalFlagGeometry
import SGPT.Foundations.Analysis.Pending.EmbeddedResolution
import SGPT.Foundations.Analysis.Pending.LocusProperties
import SGPT.Foundations.Analysis.Pending.SourceGenericSubmanifoldMinimum
import SGPT.Foundations.Analysis.Pending.AnalyticModificationDivisorStrictTransform
import SGPT.Foundations.Analysis.Pending.SubmanifoldCodRestrict

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set
open scoped Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy

/-- Actual embedded resolution, Blanchard compactness/Kählerness, and the
whole strict-transform image, without a supplied resolved carrier. -/
theorem exists_compactKahler_smoothStrictTransform
    {n : ℕ} {Z : Type u} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z] [CompactSpace Z]
    (omegaZ : KahlerBackground n Z)
    (V : ClosedIrreducibleAnalyticSubvariety n Z) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : ChartedSpace (ComplexModel n) W)
      (_ : IsComplexManifold n W) (_ : CompactSpace W) (_ : KahlerBackground n W)
      (q : W → Z) (S : Set W),
      IsBlowupSequence n Z W q ∧ IsClosedConnectedSubmanifold n S V.dim ∧
      S = strictTransform n q V.carrier ∧
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ q ∧
      IsProperMap q ∧ q '' S = V.carrier := by
  obtain ⟨W, topW, chartsW, complexW, q, hq, hres⟩ :=
    EmbeddedResolution.exists_embeddedResolution V
  let := topW
  let := chartsW
  let := complexW
  obtain ⟨compactW, ⟨omegaW⟩⟩ :=
    LocusProperties.compactSpace_and_kahler_of_isBlowupSequence ⟨omegaZ⟩ q hq
  let := compactW
  have hproper : IsProperMap q := hq.contMDiff.continuous.isProperMap
  obtain ⟨VS, hVS, _⟩ :=
    SourceGenericSubmanifoldMinimum.exists_subvariety_carrier_eq_of_submanifold hres.2
  have himage : q '' strictTransform n q V.carrier = V.carrier := by
    simpa only [hVS] using
      RawProperStrictTransformLelongReader.image_eq_of_strictTransform
        hq.contMDiff hproper V VS hVS
  exact ⟨W, topW, chartsW, complexW, compactW, omegaW, q,
    strictTransform n q V.carrier, hq, hres.2, rfl, hq.contMDiff, hproper, himage⟩

/-- The SAME original first divisor is internally lifted and resolved.
The restriction uses the actual inherited submanifold atlases. This is
the first smooth Kähler step, not the remaining nested flag construction. -/
theorem exists_resolved_originalFirstDivisor
    {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z]
    [IsComplexManifold (m + 1) Z] (omegaZ : KahlerBackground (m + 1) Z)
    {π : Z → F.carrier} (hπ : IsAnalyticModification (n := m + 1) π) :
    ∃ (W : Type u) (_ : TopologicalSpace W)
      (_ : ChartedSpace (ComplexModel (m + 1)) W)
      (_ : IsComplexManifold (m + 1) W) (_ : CompactSpace W)
      (_ : KahlerBackground (m + 1) W) (q : W → Z) (S : Set W)
      (hS : IsClosedConnectedSubmanifold (m + 1) S m),
      IsBlowupSequence (m + 1) Z W q ∧
      S = strictTransform (m + 1) (π ∘ q) (F.flag (1 : Fin (m + 2))) ∧
      q '' S = strictTransform (m + 1) π (F.flag (1 : Fin (m + 2))) ∧
      (π ∘ q) '' S = F.flag (1 : Fin (m + 2)) ∧
      ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ (π ∘ q) ∧
      IsProperMap (π ∘ q) ∧
      ∃ hi : ∀ s ∈ S, (π ∘ q) s ∈ F.flag (1 : Fin (m + 2)),
        letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) F.firstDivisor.2.2
        letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) hS.2.2
        let r1 : S → F.flag (1 : Fin (m + 2)) :=
          fun s => ⟨(π ∘ q) s, hi s s.2⟩
        ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞ r1 ∧
          IsProperMap r1 ∧ Function.Surjective r1 ∧ CompactSpace S := by
  obtain ⟨VY, hVY, hdimY⟩ :=
    SourceGenericSubmanifoldMinimum.exists_subvariety_carrier_eq_of_submanifold F.firstDivisor
  have hcodim : VY.dim + 1 = m + 1 := by rw [hdimY]
  obtain ⟨VZ, hVZ, hdimZ, himageZ, _⟩ :=
    AnalyticModificationDivisorStrictTransform.exists_strictTransform_reader hπ VY hcodim
  let : CompactSpace Z :=
    AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification hπ
  obtain ⟨W, topW, chartsW, complexW, compactW, omegaW, q, S,
    hq, hS, hstrict, hqhol, hqproper, himageS⟩ :=
    exists_compactKahler_smoothStrictTransform omegaZ VZ
  let := topW
  let := chartsW
  let := complexW
  let := compactW
  have hSm : IsClosedConnectedSubmanifold (m + 1) S m := by
    simpa only [hdimZ, hdimY] using hS
  have hqimage : q '' S = strictTransform (m + 1) π (F.flag (1 : Fin (m + 2))) := by
    rw [himageS, hVZ, hVY]
  have hrhol : ContMDiff 𝓘(ℂ, ComplexModel (m + 1))
      𝓘(ℂ, ComplexModel (m + 1)) ∞ (π ∘ q) := hπ.1.comp hqhol
  have hrproper : IsProperMap (π ∘ q) := hrhol.continuous.isProperMap
  have hrstrict : S = strictTransform (m + 1) (π ∘ q)
      (F.flag (1 : Fin (m + 2))) := by
    rw [hstrict, hVZ, hVY, StrictTransformComposition.strictTransform_comp hπ.1 hqhol]
  have hrimage : (π ∘ q) '' S = F.flag (1 : Fin (m + 2)) := by
    change (fun x => π (q x)) '' S = F.flag (1 : Fin (m + 2))
    rw [← image_image π q S, himageS, himageZ, hVY]
  have hi : ∀ s ∈ S, (π ∘ q) s ∈ F.flag (1 : Fin (m + 2)) := by
    intro s hs
    rw [← hrimage]
    exact mem_image_of_mem (π ∘ q) hs
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) F.firstDivisor.2.2
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) hSm.2.2
  let : CompactSpace S := isCompact_iff_compactSpace.mp hSm.1.isCompact
  let r1 : S → F.flag (1 : Fin (m + 2)) := fun s => ⟨(π ∘ q) s, hi s s.2⟩
  have hr1hol : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞ r1 :=
    SubmanifoldCodRestrict.contMDiff_restrictPreimage
      (Nat.le_succ m) F.firstDivisor.2.2 (Nat.le_succ m) hSm.2.2 hrhol hi
  have hr1proper : IsProperMap r1 := hr1hol.continuous.isProperMap
  have hr1surj : Function.Surjective r1 := by
    intro y
    have hy : y.1 ∈ (π ∘ q) '' S := by rw [hrimage]; exact y.2
    obtain ⟨s, hs, hsy⟩ := hy
    exact ⟨⟨s, hs⟩, Subtype.ext hsy⟩
  exact ⟨W, topW, chartsW, complexW, compactW, omegaW, q, S, hSm,
    hq, hrstrict, hqimage, hrimage, hrhol, hrproper, hi,
    hr1hol, hr1proper, hr1surj, inferInstance⟩

end SGPT.Okounkov
