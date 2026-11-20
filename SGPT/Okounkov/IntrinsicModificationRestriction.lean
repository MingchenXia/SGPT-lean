import SGPT.Okounkov.FirstAdaptedDivisor
import SGPT.Okounkov.FlagLelong
import SGPT.Foundations.Analysis.Pending.PrescribedBlowupDomination
import SGPT.Foundations.Analysis.Pending.AnalyticModificationComposition
import SGPT.Foundations.Analysis.Pending.AnalyticModificationExceptionalImageCodimension
import SGPT.Foundations.Analysis.Pending.HolomorphicLocalInverse
import SGPT.Foundations.Analysis.Pending.AnalyticSubsetPreimage
import SGPT.Foundations.Analysis.FirstPass.AnalyticSubsetTopology

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set
open scoped Manifold ContDiff Topology
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy

/-- The original finite predicate supplies the entire modification record. -/
theorem isAnalyticModification_of_isBlowupSequence
    {n : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) X] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n X] [IsComplexManifold n Y]
    {q : Y → X} (hq : IsBlowupSequence n X Y q) :
    IsAnalyticModification (n := n) q := by
  induction hq with
  | refl => exact isAnalyticModification_identity
  | step f C g _hf hg ih =>
      exact AnalyticModificationComposition.isAnalyticModification_comp ih
        (PrescribedBlowupDomination.isAnalyticModification_of_isBlowupAlong hg)

/-- The full intrinsic modification on the literal smooth strict divisor.
Neither an inverse nor any exceptional-set certificate is supplied. -/
theorem exists_intrinsicModification_strictDivisor
    {m : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) X]
    [ChartedSpace (ComplexModel (m + 1)) Y]
    [IsComplexManifold (m + 1) X] [IsComplexManifold (m + 1) Y]
    {φ : Y → X} (hφ : IsAnalyticModification (n := m + 1) φ)
    {N : Set X} {S : Set Y}
    (hN : IsClosedConnectedSubmanifold (m + 1) N m)
    (hS : IsClosedConnectedSubmanifold (m + 1) S m)
    (hstrict : S = strictTransform (m + 1) φ N) :
    ∃ hi : ∀ y ∈ S, φ y ∈ N,
      letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) hN.2.2
      letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ m) hN.2.2
      letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) hS.2.2
      letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ m) hS.2.2
      IsAnalyticModification (n := m)
        (fun y : S => (⟨φ y, hi y y.2⟩ : N)) := by
  classical
  obtain ⟨VN, hVN, hdimN⟩ :=
    SourceGenericSubmanifoldMinimum.exists_subvariety_carrier_eq_of_submanifold hN
  obtain ⟨VS, hVS, _⟩ :=
    SourceGenericSubmanifoldMinimum.exists_subvariety_carrier_eq_of_submanifold hS
  have hVSstrict : VS.carrier = strictTransform (m + 1) φ VN.carrier := by
    rw [hVS, hVN, hstrict]
  have himage : φ '' S = N := by
    simpa only [hVS, hVN] using
      RawProperStrictTransformLelongReader.image_eq_of_strictTransform
        hφ.1 hφ.2.1 VN VS hVSstrict
  have hi : ∀ y ∈ S, φ y ∈ N := by
    intro y hy
    rw [← himage]
    exact mem_image_of_mem φ hy
  refine ⟨hi, ?_⟩
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) hN.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ m) hN.2.2
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) hS.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ m) hS.2.2
  let : ConnectedSpace N := isConnected_iff_connectedSpace.mp hN.2.1
  let : ConnectedSpace S := isConnected_iff_connectedSpace.mp hS.2.1
  let r : S → N := fun y => ⟨φ y, hi y y.2⟩
  have hrhol : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞ r :=
    SubmanifoldCodRestrict.contMDiff_restrictPreimage
      (Nat.le_succ m) hN.2.2 (Nat.le_succ m) hS.2.2 hφ.1 hi
  have hrproper : IsProperMap r :=
    isProperMap_of_comp_of_inj hrhol.continuous continuous_subtype_val
      (hφ.2.1.restrict hS.1) Subtype.val_injective
  have hrsurj : Function.Surjective r := by
    intro x
    have hx : x.1 ∈ φ '' S := by rw [himage]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
  let T : Set X := φ '' exceptionalLocus (m + 1) φ
  let B : Set N := (Subtype.val : N → X) ⁻¹' T
  let A : Set S := r ⁻¹' B
  have hTa : IsComplexAnalyticSubset (n := m + 1) T :=
    AnalyticModificationExceptionalImageCodimension.isComplexAnalyticSubset_image_exceptionalLocus hφ
  have hBa : IsComplexAnalyticSubset (n := m) B :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
      (SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ m) hN.2.2) hTa
  have hAa : IsComplexAnalyticSubset (n := m) A :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hrhol hBa
  have hcodim : VN.dim + 1 = m + 1 := by rw [hdimN]
  obtain ⟨x0, hx0, hx0T⟩ := not_subset.mp
    (AnalyticModificationExceptionalImageCodimension.not_subset_image_exceptionalLocus_of_codim_one
      hφ VN hcodim)
  have hx0N : x0 ∈ N := by rwa [hVN] at hx0
  let x : N := ⟨x0, hx0N⟩
  have hxB : x ∉ B := hx0T
  obtain ⟨y0, hy0⟩ := hrsurj x
  have hy0A : y0 ∉ A := by
    change r y0 ∉ B
    rwa [hy0]
  have hBi : interior B = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hBu := hBa.eq_univ_of_interior_nonempty ⟨z, hz⟩
    exact hxB (hBu.symm ▸ mem_univ x)
  have hAi : interior A = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hAu := hAa.eq_univ_of_interior_nonempty ⟨z, hz⟩
    exact hy0A (hAu.symm ▸ mem_univ y0)
  let s : N → S := fun x => Classical.choose (hrsurj x)
  have hrs : ∀ x, r (s x) = x := fun x => Classical.choose_spec (hrsurj x)
  have hnon {y : Y} (hy : φ y ∉ T) : y ∉ exceptionalLocus (m + 1) φ := by
    intro hyE
    exact hy ⟨y, hyE, rfl⟩
  have hsr : ∀ y ∉ A, s (r y) = y := by
    intro y hy
    apply Subtype.ext
    apply AnalyticModificationExceptionalFibres.eq_of_apply_eq_of_not_mem_exceptionalLocus
      hφ (hnon hy)
    exact congrArg Subtype.val (hrs (r y))
  have hsOn : ContMDiffOn 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞ s Bᶜ := by
    intro x hx
    have hφsx : φ (s x).1 = x.1 := congrArg Subtype.val (hrs x)
    have hsxE : (s x).1 ∉ exceptionalLocus (m + 1) φ :=
      hnon (by rw [hφsx]; exact hx)
    obtain ⟨V, a, hVo, hVx, _hay, hφa, haHol, _halocal⟩ :=
      HolomorphicLocalInverse.exists_localInverse hφ.1 hsxE
    have hxV : x.1 ∈ V := by rwa [hφsx] at hVx
    let U : TopologicalSpace.Opens N :=
      ⟨(Subtype.val : N → X) ⁻¹' (V ∩ Tᶜ),
        (hVo.inter hTa.isClosed.isOpen_compl).preimage continuous_subtype_val⟩
    have hxU : x ∈ U := ⟨hxV, hx⟩
    have haS : ∀ z : U, a z.1.1 ∈ S := by
      intro z
      have hzV : z.1.1 ∈ V := z.2.1
      have hzT : z.1.1 ∉ T := z.2.2
      have haz : φ (a z.1.1) = z.1.1 := hφa _ hzV
      rw [hstrict]
      apply subset_closure
      exact ⟨by change φ (a z.1.1) ∈ N; rw [haz]; exact z.1.2,
        hnon (by rw [haz]; exact hzT)⟩
    have haUhol : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel (m + 1)) ∞
        (fun z : U => a z.1.1) := by
      intro z
      exact (haHol _ z.2.1).comp z
        ((SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ m) hN.2.2).contMDiffAt.comp z
          contMDiff_subtype_val.contMDiffAt)
    have hacore : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞
        (fun z : U => (⟨a z.1.1, haS z⟩ : S)) :=
      SubmanifoldCodRestrict.contMDiff_codRestrict (Nat.le_succ m) hS.2.2 haUhol haS
    have heq : (fun z : U => (⟨a z.1.1, haS z⟩ : S)) = fun z : U => s z.1 := by
      funext z
      have hsz : φ (s z.1).1 = z.1.1 := congrArg Subtype.val (hrs z.1)
      have hszE : (s z.1).1 ∉ exceptionalLocus (m + 1) φ :=
        hnon (by rw [hsz]; exact z.2.2)
      apply Subtype.ext
      apply AnalyticModificationExceptionalFibres.eq_of_apply_eq_of_not_mem_exceptionalLocus
        hφ hszE
      exact (hφa _ z.2.1).trans (congrArg Subtype.val (hrs z.1)).symm
    rw [heq] at hacore
    exact (contMDiffAt_subtype_iff.mp (hacore ⟨x, hxU⟩)).contMDiffWithinAt
  exact ⟨hrhol, hrproper, A, B, s, hAa.isClosed, hAa, hAi,
    hBa.isClosed, hBa, hBi, rfl, hsOn, (fun x _hx => hrs x), hsr⟩

/-- Retain all actual first-resolution witnesses and add the three full
modification properties, including the intrinsic restriction. -/
theorem exists_resolved_originalFirstDivisor_modification
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
      IsAnalyticModification (n := m + 1) q ∧
      IsAnalyticModification (n := m + 1) (π ∘ q) ∧
      ∃ hi : ∀ s ∈ S, (π ∘ q) s ∈ F.flag (1 : Fin (m + 2)),
        letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) F.firstDivisor.2.2
        letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
          (Nat.le_succ m) F.firstDivisor.2.2
        letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) hS.2.2
        letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ m) hS.2.2
        let r1 : S → F.flag (1 : Fin (m + 2)) :=
          fun s => ⟨(π ∘ q) s, hi s s.2⟩
        ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞ r1 ∧
          IsProperMap r1 ∧ Function.Surjective r1 ∧ CompactSpace S ∧
          IsAnalyticModification (n := m) r1 := by
  obtain ⟨W, topW, chartsW, complexW, compactW, omegaW, q, S, hS,
    hq, hstrict, hqimage, hrimage, hrhol, hrproper, hi,
    hr1hol, hr1proper, hr1surj, compactS⟩ :=
    exists_resolved_originalFirstDivisor F omegaZ hπ
  let := topW
  let := chartsW
  let := complexW
  let := compactW
  have hqmod := isAnalyticModification_of_isBlowupSequence hq
  have hrmod := AnalyticModificationComposition.isAnalyticModification_comp hπ hqmod
  obtain ⟨hi', hr1mod⟩ :=
    exists_intrinsicModification_strictDivisor hrmod F.firstDivisor hS hstrict
  exact ⟨W, topW, chartsW, complexW, compactW, omegaW, q, S, hS,
    hq, hstrict, hqimage, hrimage, hrhol, hrproper, hqmod, hrmod, hi,
    hr1hol, hr1proper, hr1surj, compactS, hr1mod⟩

end SGPT.Okounkov
