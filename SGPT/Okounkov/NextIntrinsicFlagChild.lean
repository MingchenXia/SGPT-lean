import SGPT.Okounkov.NestedAncestorBlowupTower
import SGPT.Okounkov.OriginalFlagGeometry
import SGPT.Foundations.Analysis.Pending.SubmanifoldKahlerRestriction

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy

/-- Equality transport of a chart and its dependent complex structure. -/
private theorem nextChild_castComplexManifold
    {a b : ℕ} {V : Type u} [TopologicalSpace V]
    (chartsV : ChartedSpace (ComplexModel a) V)
    (complexV : @IsComplexManifold a V _ chartsV) (hab : a = b) :
    @IsComplexManifold b V _ (hab ▸ chartsV) := by
  subst b
  exact complexV

/-- Equality transport of the SAME inherited atlas and original finite predicate. -/
private theorem nextChild_castInheritedFinite
    {n a b : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {N : Set X} (ha : a ≤ n) (hb : b ≤ n)
    (hNa : ∀ x ∈ N, RegularAtDim N x a) (hNb : ∀ x ∈ N, RegularAtDim N x b)
    {V : Type u} [TopologicalSpace V]
    (chartsV : ChartedSpace (ComplexModel a) V)
    (complexV : @IsComplexManifold a V _ chartsV) (hab : a = b) {q : V → N}
    (hq : letI := chartsV
      letI := complexV
      letI := SubmanifoldChartedSpace.chartedSpace ha hNa
      letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace ha hNa
      IsBlowupSequence a N V q) :
    letI : ChartedSpace (ComplexModel b) V := hab ▸ chartsV
    letI := nextChild_castComplexManifold chartsV complexV hab
    letI := SubmanifoldChartedSpace.chartedSpace hb hNb
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hb hNb
    IsBlowupSequence b N V q := by
  subst b
  exact hq

/-- Inverse dimension transport returns the original holomorphic endpoint maps. -/
private theorem nextChild_castInheritedHolomorphicPair
    {n a b : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {N : Set X} (ha : a ≤ n) (hb : b ≤ n)
    (hNa : ∀ x ∈ N, RegularAtDim N x a) (hNb : ∀ x ∈ N, RegularAtDim N x b)
    {V : Type u} [TopologicalSpace V]
    (chartsV : ChartedSpace (ComplexModel a) V) (hab : a = b)
    (e : V → N) (f : N → V)
    (he : letI : ChartedSpace (ComplexModel b) V := hab ▸ chartsV
      letI := SubmanifoldChartedSpace.chartedSpace hb hNb
      ContMDiff 𝓘(ℂ, ComplexModel b) 𝓘(ℂ, ComplexModel b) ∞ e)
    (hf : letI : ChartedSpace (ComplexModel b) V := hab ▸ chartsV
      letI := SubmanifoldChartedSpace.chartedSpace hb hNb
      ContMDiff 𝓘(ℂ, ComplexModel b) 𝓘(ℂ, ComplexModel b) ∞ f) :
    letI := chartsV
    letI := SubmanifoldChartedSpace.chartedSpace ha hNa
    ContMDiff 𝓘(ℂ, ComplexModel a) 𝓘(ℂ, ComplexModel a) ∞ e ∧
      ContMDiff 𝓘(ℂ, ComplexModel a) 𝓘(ℂ, ComplexModel a) ∞ f := by
  subst b
  exact ⟨he, hf⟩

/-- Resolve the SAME prescribed intrinsic smooth divisor over the actual
modification. Resolution, compactness, Kählerness and the whole intrinsic
modification are produced by the genuine existing parents. -/
theorem exists_resolved_prescribedDivisor_modification
    {k : ℕ} {B L : Type u} [TopologicalSpace B] [TopologicalSpace L]
    [ChartedSpace (ComplexModel (k + 1)) B]
    [ChartedSpace (ComplexModel (k + 1)) L]
    [IsComplexManifold (k + 1) B] [IsComplexManifold (k + 1) L]
    [CompactSpace B] (omegaL : KahlerBackground (k + 1) L)
    {D : Set B} (hD : IsClosedConnectedSubmanifold (k + 1) D k)
    {r : L → B} (hr : IsAnalyticModification (n := k + 1) r) :
    ∃ (V : Type u) (_ : TopologicalSpace V)
      (_ : ChartedSpace (ComplexModel (k + 1)) V)
      (_ : IsComplexManifold (k + 1) V) (_ : CompactSpace V)
      (_ : KahlerBackground (k + 1) V) (q : V → L) (C : Set V)
      (hC : IsClosedConnectedSubmanifold (k + 1) C k),
      IsBlowupSequence (k + 1) L V q ∧
      IsAnalyticModification (n := k + 1) q ∧
      IsAnalyticModification (n := k + 1) (r ∘ q) ∧
      C = strictTransform (k + 1) (r ∘ q) D ∧
      q '' C = strictTransform (k + 1) r D ∧ (r ∘ q) '' C = D ∧
      ∃ hi : ∀ z ∈ C, (r ∘ q) z ∈ D,
        letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ k) hD.2.2
        letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
          (Nat.le_succ k) hD.2.2
        letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ k) hC.2.2
        letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
          (Nat.le_succ k) hC.2.2
        IsAnalyticModification (n := k)
          (fun z : C => (⟨(r ∘ q) z, hi z z.2⟩ : D)) := by
  obtain ⟨VD, hVD, hdimD⟩ :=
    SourceGenericSubmanifoldMinimum.exists_subvariety_carrier_eq_of_submanifold hD
  obtain ⟨VL, hVL, hdimL, himageL, _⟩ :=
    AnalyticModificationDivisorStrictTransform.exists_strictTransform_reader
      hr VD (by rw [hdimD])
  let : CompactSpace L :=
    AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification hr
  obtain ⟨V, topV, chartsV, complexV, compactV, omegaV, q, C,
    hq, hC, hstrict, hqhol, _hqproper, himageC⟩ :=
    exists_compactKahler_smoothStrictTransform omegaL VL
  let := topV
  let := chartsV
  let := complexV
  let := compactV
  have hCk : IsClosedConnectedSubmanifold (k + 1) C k := by
    simpa only [hdimL, hdimD] using hC
  have hqmod := isAnalyticModification_of_isBlowupSequence hq
  have hrq := AnalyticModificationComposition.isAnalyticModification_comp hr hqmod
  have hstrictD : C = strictTransform (k + 1) (r ∘ q) D := by
    rw [hstrict, hVL, hVD, StrictTransformComposition.strictTransform_comp hr.1 hqhol]
  have hqimage : q '' C = strictTransform (k + 1) r D := by
    rw [himageC, hVL, hVD]
  have hrqimage : (r ∘ q) '' C = D := by
    change (fun z => r (q z)) '' C = D
    rw [← image_image r q C, himageC, himageL, hVD]
  obtain ⟨hi, hmod⟩ := exists_intrinsicModification_strictDivisor hrq hD hCk hstrictD
  exact ⟨V, topV, chartsV, complexV, compactV, omegaV, q, C, hCk,
    hq, hqmod, hrq, hstrictD, hqimage, hrqimage, hi, hmod⟩

/-- The manufactured ancestor prefix followed by its manufactured child is
the extended partial flag. Every original restriction and whole image is
retained. The child is resolved in the CURRENT intrinsic lowest component,
including when its ambient original carrier is in the exceptional image. -/
theorem exists_nextIntrinsicFlagChild
    {k r : ℕ} (F : OriginalFlagGeometry.{u} (k + 1 + r))
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (k + 1 + r)) X]
    [IsComplexManifold (k + 1 + r) X] [CompactSpace X]
    (omegaX : KahlerBackground (k + 1 + r) X)
    {κ : X → F.carrier} (hκ : IsAnalyticModification (n := k + 1 + r) κ)
    (N : Fin (r + 1) → Set X) (hNa : Antitone N) (hN0 : N 0 = univ)
    (hN : ∀ (j : Fin (r + 1)), IsClosedConnectedSubmanifold (k + 1 + r) (N j)
      (k + 1 + r - (j : ℕ)))
    (hκi : ∀ (j : Fin (r + 1)), ∀ x ∈ N j, κ x ∈ F.flag ⟨(j : ℕ), by omega⟩)
    (hκlevels : ∀ (j : Fin (r + 1)),
      letI := SubmanifoldChartedSpace.chartedSpace
        (Nat.sub_le (k + 1 + r) (j : ℕ)) (hN j).2.2
      letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
        (Nat.sub_le (k + 1 + r) (j : ℕ)) (hN j).2.2
      letI := F.componentCharts ⟨(j : ℕ), by omega⟩
      letI := F.componentComplex ⟨(j : ℕ), by omega⟩
      IsAnalyticModification (n := k + 1 + r - (j : ℕ))
        (fun x : N j => (⟨κ x, hκi j x x.2⟩ : F.flag ⟨(j : ℕ), by omega⟩))) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y)
      (_ : ChartedSpace (ComplexModel (k + 1 + r)) Y)
      (_ : IsComplexManifold (k + 1 + r) Y) (_ : CompactSpace Y)
      (_ : ConnectedSpace Y) (_ : KahlerBackground (k + 1 + r) Y)
      (a : Y → X) (S : Fin (r + 1) → Set Y),
      IsBlowupSequence (k + 1 + r) X Y a ∧
      IsAnalyticModification (n := k + 1 + r) (κ ∘ a) ∧
      (∀ (j : Fin (r + 1)), S j = strictTransform (k + 1 + r) a (N j)) ∧
      Antitone S ∧ S 0 = univ ∧
      ∃ hS : ∀ (j : Fin (r + 1)), IsClosedConnectedSubmanifold (k + 1 + r) (S j)
          (k + 1 + r - (j : ℕ)),
        ∃ hi : ∀ (j : Fin (r + 1)), ∀ y ∈ S j, a y ∈ N j,
          (∀ (j : Fin (r + 1)),
            letI := SubmanifoldChartedSpace.chartedSpace
              (Nat.sub_le (k + 1 + r) (j : ℕ)) (hN j).2.2
            letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
              (Nat.sub_le (k + 1 + r) (j : ℕ)) (hN j).2.2
            letI := SubmanifoldChartedSpace.chartedSpace
              (Nat.sub_le (k + 1 + r) (j : ℕ)) (hS j).2.2
            letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
              (Nat.sub_le (k + 1 + r) (j : ℕ)) (hS j).2.2
            IsBlowupSequence (k + 1 + r - (j : ℕ)) (N j) (S j)
              (fun y => (⟨a y, hi j y y.2⟩ : N j))) ∧
          (∀ (j : Fin (r + 1)),
            letI := SubmanifoldChartedSpace.chartedSpace
              (Nat.sub_le (k + 1 + r) (j : ℕ)) (hS j).2.2
            letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
              (Nat.sub_le (k + 1 + r) (j : ℕ)) (hS j).2.2
            letI := F.componentCharts ⟨(j : ℕ), by omega⟩
            letI := F.componentComplex ⟨(j : ℕ), by omega⟩
            IsAnalyticModification (n := k + 1 + r - (j : ℕ))
              (fun y : S j => (⟨κ (a y), hκi j (a y) (hi j y y.2)⟩ :
                F.flag ⟨(j : ℕ), by omega⟩))) ∧
          (∀ (j : Fin (r + 1)), (κ ∘ a) '' S j = F.flag ⟨(j : ℕ), by omega⟩) ∧
          ∃ (C : Set Y) (hC : IsClosedConnectedSubmanifold (k + 1 + r) C k)
            (hFnext : IsClosedConnectedSubmanifold (k + 1 + r)
              (F.flag ⟨r + 1, by omega⟩) k),
            C ⊆ S (Fin.last r) ∧ (κ ∘ a) '' C = F.flag ⟨r + 1, by omega⟩ ∧
            ∃ hc : ∀ y ∈ C, κ (a y) ∈ F.flag ⟨r + 1, by omega⟩,
              letI := SubmanifoldChartedSpace.chartedSpace (show k ≤ k + 1 + r by omega)
                hC.2.2
              letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
                (show k ≤ k + 1 + r by omega) hC.2.2
              letI := SubmanifoldChartedSpace.chartedSpace (show k ≤ k + 1 + r by omega)
                hFnext.2.2
              letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
                (show k ≤ k + 1 + r by omega) hFnext.2.2
              IsAnalyticModification (n := k)
                (fun y : C => (⟨κ (a y), hc y y.2⟩ : F.flag ⟨r + 1, by omega⟩)) := by
  classical
  let last : Fin (r + 1) := Fin.last r
  let fr : Fin (k + 1 + r + 1) := ⟨r, by omega⟩
  let fn : Fin (k + 1 + r + 1) := ⟨r + 1, by omega⟩
  have hNr : IsClosedConnectedSubmanifold (k + 1 + r) (N last) (k + 1) := by
    simpa only [last, Fin.val_last, Nat.add_sub_cancel] using hN last
  have hFr : IsClosedConnectedSubmanifold (k + 1 + r) (F.flag fr) (k + 1) := by
    simpa only [fr, Fin.val_mk, Nat.add_sub_cancel] using F.smooth.2.2 fr
  have hFn : IsClosedConnectedSubmanifold (k + 1 + r) (F.flag fn) k := by
    simpa only [fn, Fin.val_mk, show k + 1 + r - (r + 1) = k by omega]
      using F.smooth.2.2 fn
  have hFnFr : F.flag fn ⊆ F.flag fr := F.smooth.2.1 (by change r ≤ r + 1; omega)
  let := SubmanifoldChartedSpace.chartedSpace (show k + 1 ≤ k + 1 + r by omega) hNr.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
    (show k + 1 ≤ k + 1 + r by omega) hNr.2.2
  let := SubmanifoldChartedSpace.chartedSpace (show k + 1 ≤ k + 1 + r by omega) hFr.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
    (show k + 1 ≤ k + 1 + r by omega) hFr.2.2
  let : CompactSpace (N last) := isCompact_iff_compactSpace.mp hNr.1.isCompact
  let : CompactSpace (F.flag fr) := isCompact_iff_compactSpace.mp hFr.1.isCompact
  let omegaNr := SubmanifoldKahlerRestriction.kahlerBackground
    (show k + 1 ≤ k + 1 + r by omega) hNr.2.2 omegaX
  let D : Set (F.flag fr) := Subtype.val ⁻¹' F.flag fn
  have hD : IsClosedConnectedSubmanifold (k + 1) D k :=
    isClosedConnectedSubmanifold_subtype_of_nested hFr hFn hFnFr (Nat.le_succ k)
  let kr : N last → F.flag fr := fun x => ⟨κ x, hκi last x x.2⟩
  have hkr : IsAnalyticModification (n := k + 1) kr := by
    apply (isAnalyticModification_inherited_dimension_congr
      (show k + 1 + r - r = k + 1 by omega)
      (Nat.sub_le (k + 1 + r) r) (show k + 1 ≤ k + 1 + r by omega)
      (F.smooth.2.2 fr).2.2 (hN last).2.2 hFr.2.2 hNr.2.2 kr).mp
    simpa only [last, fr, Fin.val_last] using hκlevels last
  obtain ⟨V, topV, chartsV, complexV, compactV, omegaV, q, C, hC,
    hq, _hqmod, _hkrqmod, _hCstrict, _hqimage, _hkrqimage, hρi, hρmod⟩ :=
    exists_resolved_prescribedDivisor_modification omegaNr hD hkr
  let := topV
  let := chartsV
  let := complexV
  let := compactV
  have hdim : k + 1 + r - (last : ℕ) = k + 1 := by dsimp [last]; omega
  let chartsVd : ChartedSpace (ComplexModel (k + 1 + r - (last : ℕ))) V :=
    hdim.symm ▸ chartsV
  let := chartsVd
  let complexVd : IsComplexManifold (k + 1 + r - (last : ℕ)) V :=
    nextChild_castComplexManifold chartsV complexV hdim.symm
  let := complexVd
  have hq' :
      let hk : ∀ j : Fin (r + 1), k + 1 + r - (j : ℕ) ≤ k + 1 + r :=
        fun j => Nat.sub_le _ _
      letI := SubmanifoldChartedSpace.chartedSpace (hk last) (hN last).2.2
      letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hk last) (hN last).2.2
      IsBlowupSequence (k + 1 + r - (last : ℕ)) (N last) V q := by
    exact nextChild_castInheritedFinite (show k + 1 ≤ k + 1 + r by omega)
      (Nat.sub_le (k + 1 + r) (last : ℕ)) hNr.2.2 (hN last).2.2
      chartsV complexV hdim.symm hq
  obtain ⟨Y, topY, chartsY, complexY, compactY, connectedY, omegaY,
    a, S, ha, hstrict, hSa, hS0, hS, hi, hprops, e, f, he, hf, hfe, hef, hcomm⟩ :=
    exists_ambientTower_preserving_smoothAncestors omegaX N
      (fun j => k + 1 + r - (j : ℕ)) hNa (by intro i j hij; dsimp; omega)
      hN0 (by simp) hN (Nt := V) (q := q) hq'
  let := topY
  let := chartsY
  let := complexY
  let := compactY
  let := connectedY
  have hSr : IsClosedConnectedSubmanifold (k + 1 + r) (S last) (k + 1) := by
    simpa only [last, Fin.val_last, Nat.add_sub_cancel] using hS last
  let := SubmanifoldChartedSpace.chartedSpace (show k + 1 ≤ k + 1 + r by omega) hSr.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
    (show k + 1 ≤ k + 1 + r by omega) hSr.2.2
  obtain ⟨he', hf'⟩ := nextChild_castInheritedHolomorphicPair
    (show k + 1 ≤ k + 1 + r by omega) (Nat.sub_le (k + 1 + r) (last : ℕ))
    hSr.2.2 (hS last).2.2 chartsV hdim.symm e f he hf
  have hfe' : ∀ z : V, f (e z) = z := fun z => by
    simpa only [Function.comp_apply, id_eq] using congrFun hfe z
  have hef' : ∀ z : S last, e (f z) = z := fun z => by
    simpa only [Function.comp_apply, id_eq] using congrFun hef z
  let H : S last ≃ₜ V := {
    toFun := f
    invFun := e
    left_inv := hef'
    right_inv := hfe'
    continuous_toFun := hf'.continuous
    continuous_invFun := he'.continuous }
  let Cp : Set (S last) := f ⁻¹' C
  have hCp : IsClosedConnectedSubmanifold (k + 1) Cp k := by
    refine ⟨hC.1.preimage hf'.continuous, H.isConnected_preimage.mpr hC.2.1, ?_⟩
    intro z hz
    exact RegularAtDimTransport.regularAtDim_of_preimage hf'
      (MarkedIdealBiholomorphism.notMem_exceptionalLocus_of_inverse hf' he'
        hfe' hef' z)
      isOpen_univ (mem_univ z) (fun _ _ => Iff.rfl) (hC.2.2 (f z) hz)
  let E : Set Y := Subtype.val '' Cp
  have hE : IsClosedConnectedSubmanifold (k + 1 + r) E k :=
    isClosedConnectedSubmanifold_ambientImage
      (show k + 1 ≤ k + 1 + r by omega) hSr.1 hSr.2.2 hCp
  have hES : E ⊆ S last := by rintro _ ⟨z, _, rfl⟩; exact z.2
  let γ : E ≃ₜ C := {
    toFun := fun z => ⟨f ⟨z.val, hES z.2⟩, by
      rcases z.2 with ⟨t, ht, htval⟩
      have ht' : (⟨z.val, hES z.2⟩ : S last) = t := Subtype.ext htval.symm
      rw [ht']; exact ht⟩
    invFun := fun z => ⟨(e z.val).val, ⟨e z.val, by
      change f (e z.val) ∈ C
      rw [hfe' z.val]; exact z.2, rfl⟩⟩
    left_inv := fun z => by
      apply Subtype.ext
      change (e (f (⟨z.val, hES z.2⟩ : S last))).val = z.val
      rw [hef']
    right_inv := fun z => by
      apply Subtype.ext
      change f (e z.val) = z.val
      exact hfe' z.val
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact hf'.continuous.comp
        (continuous_subtype_val.subtype_mk (fun z : E => hES z.2))
    continuous_invFun := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp (he'.continuous.comp continuous_subtype_val) }
  let := SubmanifoldChartedSpace.chartedSpace (show k ≤ k + 1 + r by omega) hE.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
    (show k ≤ k + 1 + r by omega) hE.2.2
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ k) hC.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ k) hC.2.2
  have hγ : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ γ := by
    have hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel (k + 1)) ∞
        (fun z : E => (⟨z.val, hES z.2⟩ : S last)) :=
      SubmanifoldCodRestrict.contMDiff_codRestrict
        (show k + 1 ≤ k + 1 + r by omega) hSr.2.2
        (SubmanifoldChartedSpace.contMDiff_val (show k ≤ k + 1 + r by omega) hE.2.2)
        (fun z => hES z.2)
    exact SubmanifoldCodRestrict.contMDiff_codRestrict
      (Nat.le_succ k) hC.2.2 (hf'.comp hι) (fun z => (γ z).2)
  have hγi : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ γ.symm := by
    have hraw : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel (k + 1 + r)) ∞
        (fun z : C => (e z.val).val) :=
      (SubmanifoldChartedSpace.contMDiff_val
        (show k + 1 ≤ k + 1 + r by omega) hSr.2.2).comp
          (he'.comp (SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ k) hC.2.2))
    exact SubmanifoldCodRestrict.contMDiff_codRestrict
      (show k ≤ k + 1 + r by omega) hE.2.2 hraw (fun z => (γ.symm z).2)
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ k) hD.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ k) hD.2.2
  let := SubmanifoldChartedSpace.chartedSpace (show k ≤ k + 1 + r by omega) hFn.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
    (show k ≤ k + 1 + r by omega) hFn.2.2
  let η : D ≃ₜ F.flag fn := nestedCarrierHomeomorph hFnFr
  have hη : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ η :=
    contMDiff_nestedCarrierHomeomorph
      (show k + 1 ≤ k + 1 + r by omega) (Nat.le_succ k) hFr hFn hFnFr
  have hηi : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ η.symm :=
    contMDiff_nestedCarrierHomeomorph_symm
      (show k + 1 ≤ k + 1 + r by omega) (Nat.le_succ k) hFr hFn hFnFr
  let ρ : C → D := fun z => ⟨(kr ∘ q) z.val, hρi z.val z.2⟩
  let : CompactSpace E := isCompact_iff_compactSpace.mp hE.1.isCompact
  have hchildmod : IsAnalyticModification (n := k) (η ∘ ρ ∘ γ) :=
    isAnalyticModification_biholomorphic_transport η.symm γ hηi hη hγ hγi hρmod
  have hchildvalue : ∀ z : E, ((η ∘ ρ ∘ γ) z).val = κ (a z.val) := by
    intro z
    have hc := congrFun hcomm (γ z).val
    change a (e (γ z).val).val = (q (γ z).val).val at hc
    have heγ : e (γ z).val = (⟨z.val, hES z.2⟩ : S last) := hef' _
    rw [heγ] at hc
    change κ (q (γ z).val).val = κ (a z.val)
    exact congrArg κ hc.symm
  have hc : ∀ y ∈ E, κ (a y) ∈ F.flag fn := by
    intro y hy
    rw [← hchildvalue ⟨y, hy⟩]
    exact ((η ∘ ρ ∘ γ) ⟨y, hy⟩).2
  have hchildliteral : IsAnalyticModification (n := k)
      (fun z : E => (⟨κ (a z), hc z z.2⟩ : F.flag fn)) := by
    have heq : (fun z : E => (⟨κ (a z), hc z z.2⟩ : F.flag fn)) = η ∘ ρ ∘ γ := by
      funext z; apply Subtype.ext; exact (hchildvalue z).symm
    rw [heq]; exact hchildmod
  have hchildimage : (κ ∘ a) '' E = F.flag fn := by
    apply Set.Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩; exact hc y hy
    · intro z hz
      obtain ⟨y, hy⟩ := AnalyticModificationStrongPullback.surjective_of_isAnalyticModification
        hchildliteral (⟨z, hz⟩ : F.flag fn)
      exact ⟨y, y.2, congrArg Subtype.val hy⟩
  have halevels : ∀ (j : Fin (r + 1)),
      letI := SubmanifoldChartedSpace.chartedSpace (Nat.sub_le (k + 1 + r) (j : ℕ)) (hN j).2.2
      letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
        (Nat.sub_le (k + 1 + r) (j : ℕ)) (hN j).2.2
      letI := SubmanifoldChartedSpace.chartedSpace (Nat.sub_le (k + 1 + r) (j : ℕ)) (hS j).2.2
      letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
        (Nat.sub_le (k + 1 + r) (j : ℕ)) (hS j).2.2
      IsBlowupSequence (k + 1 + r - (j : ℕ)) (N j) (S j)
        (fun y => (⟨a y, hi j y y.2⟩ : N j)) := fun j => (hprops j).1
  have hlevels : ∀ (j : Fin (r + 1)),
      letI := SubmanifoldChartedSpace.chartedSpace (Nat.sub_le (k + 1 + r) (j : ℕ)) (hS j).2.2
      letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
        (Nat.sub_le (k + 1 + r) (j : ℕ)) (hS j).2.2
      letI := F.componentCharts ⟨(j : ℕ), by omega⟩
      letI := F.componentComplex ⟨(j : ℕ), by omega⟩
      IsAnalyticModification (n := k + 1 + r - (j : ℕ))
        (fun y : S j => (⟨κ (a y), hκi j (a y) (hi j y y.2)⟩ :
          F.flag ⟨(j : ℕ), by omega⟩)) := by
    intro j
    let := SubmanifoldChartedSpace.chartedSpace (Nat.sub_le (k + 1 + r) (j : ℕ)) (hN j).2.2
    let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
      (Nat.sub_le (k + 1 + r) (j : ℕ)) (hN j).2.2
    let := SubmanifoldChartedSpace.chartedSpace (Nat.sub_le (k + 1 + r) (j : ℕ)) (hS j).2.2
    let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
      (Nat.sub_le (k + 1 + r) (j : ℕ)) (hS j).2.2
    let := F.componentCharts ⟨(j : ℕ), by omega⟩
    let := F.componentComplex ⟨(j : ℕ), by omega⟩
    exact AnalyticModificationComposition.isAnalyticModification_comp
      (hκlevels j) (isAnalyticModification_of_isBlowupSequence (halevels j))
  have himages : ∀ (j : Fin (r + 1)), (κ ∘ a) '' S j = F.flag ⟨(j : ℕ), by omega⟩ := by
    intro j
    let := SubmanifoldChartedSpace.chartedSpace (Nat.sub_le (k + 1 + r) (j : ℕ)) (hS j).2.2
    let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
      (Nat.sub_le (k + 1 + r) (j : ℕ)) (hS j).2.2
    let := F.componentCharts ⟨(j : ℕ), by omega⟩
    let := F.componentComplex ⟨(j : ℕ), by omega⟩
    apply Set.Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩; exact hκi j (a y) (hi j y hy)
    · intro z hz
      obtain ⟨y, hy⟩ := AnalyticModificationStrongPullback.surjective_of_isAnalyticModification
        (hlevels j) (⟨z, hz⟩ : F.flag ⟨(j : ℕ), by omega⟩)
      exact ⟨y, y.2, congrArg Subtype.val hy⟩
  exact ⟨Y, topY, chartsY, complexY, compactY, connectedY, omegaY, a, S,
    ha, AnalyticModificationComposition.isAnalyticModification_comp hκ
      (isAnalyticModification_of_isBlowupSequence ha), hstrict, hSa, hS0,
    hS, hi, halevels, hlevels, himages, E, hE, hFn, hES, hchildimage, hc, hchildliteral⟩

end SGPT.Okounkov
