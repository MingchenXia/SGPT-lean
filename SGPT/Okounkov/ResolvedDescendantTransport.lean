import SGPT.Okounkov.AmbientAncestorModificationTower
import SGPT.Okounkov.FirstAdaptedDivisor
import SGPT.Foundations.Analysis.Pending.SubmanifoldKahlerRestriction

set_option autoImplicit false

noncomputable section

universe u v

namespace SGPT.Okounkov

open Set
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy

/-- Resolve the exact already compiled producer name, including its numeric
private-name component, without changing its original body. -/
macro "existingIntrinsicRegularImageProducer" : term =>
  pure (Lean.mkIdent (.str (.str (.str
    (.num `_private.SGPT.Okounkov.ClosedSubmanifoldBlowupExtension 0)
    "SGPT") "Okounkov") "regularAtDim_image_submanifold"))

/-- Public bridge to the unchanged existing mixed-dimension regular-image
producer in ClosedSubmanifoldBlowupExtension. Its compiled private name and
whole original proof were inspected; the substantial descendant consumer
below reuses it rather than repeating the flattening proof. -/
theorem regularAtDim_ambientImage_of_intrinsic
    {n k : ℕ} {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {S : Set Y} (hk : k ≤ n) (hS : ∀ y ∈ S, RegularAtDim (n := n) S y k)
    {U : Set S} {s : S} {l : ℕ}
    (hU : letI := SubmanifoldChartedSpace.chartedSpace hk hS
      RegularAtDim (n := k) U s l) :
    RegularAtDim (n := n) (Subtype.val '' U) s.1 l := by
  exact existingIntrinsicRegularImageProducer hk hS hU

/-- The actual resolved lower carrier is transported by the whole comparison
biholomorphism and the real submanifold inclusion. It is a literal image,
without a false global ambient strict-transform assertion. -/
theorem isClosedConnectedSubmanifold_descendantComparisonImage
    {n k l : ℕ} {Y Nt : Type u}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    [TopologicalSpace Nt] [ChartedSpace (ComplexModel k) Nt] [IsComplexManifold k Nt]
    {S : Set Y} (hk : k ≤ n) (hSc : IsClosed S)
    (hS : ∀ y ∈ S, RegularAtDim (n := n) S y k)
    {e : Nt → S} {f : S → Nt}
    (he : letI := SubmanifoldChartedSpace.chartedSpace hk hS
      ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ e)
    (hf : letI := SubmanifoldChartedSpace.chartedSpace hk hS
      ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ f)
    (hfe : f ∘ e = id) (hef : e ∘ f = id)
    {T : Set Nt} (hT : IsClosedConnectedSubmanifold k T l) :
    IsClosedConnectedSubmanifold n (((Subtype.val : S → Y) ∘ e) '' T) l ∧
      (((Subtype.val : S → Y) ∘ e) '' T) ⊆ S ∧
      ((Subtype.val : S → Y) ∘ e) '' T = Subtype.val '' (f ⁻¹' T) := by
  let := SubmanifoldChartedSpace.chartedSpace hk hS
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hS
  have hUeq : f ⁻¹' T = e '' T := by
    ext s
    constructor
    · intro hs
      exact ⟨f s, hs, congrFun hef s⟩
    · rintro ⟨t, ht, rfl⟩
      change f (e t) ∈ T
      rw [show f (e t) = t from congrFun hfe t]
      exact ht
  have hUr : ∀ s ∈ f ⁻¹' T, RegularAtDim (n := k) (f ⁻¹' T) s l := by
    intro s hs
    exact RegularAtDimTransport.regularAtDim_of_preimage hf
      (MarkedIdealBiholomorphism.notMem_exceptionalLocus_of_inverse hf he
        (fun t => congrFun hfe t) (fun s => congrFun hef s) s)
      isOpen_univ (mem_univ s) (fun _ _ => Iff.rfl) (hT.2.2 (f s) hs)
  have hUc : IsClosed (f ⁻¹' T) := hT.1.preimage hf.continuous
  have hUconn : IsConnected (f ⁻¹' T) := by
    rw [hUeq]
    exact hT.2.1.image e he.continuous.continuousOn
  have hDeq : ((Subtype.val : S → Y) ∘ e) '' T = Subtype.val '' (f ⁻¹' T) := by
    rw [hUeq, image_image]
    rfl
  have hD : IsClosedConnectedSubmanifold n (Subtype.val '' (f ⁻¹' T)) l := by
    refine ⟨hSc.isClosedEmbedding_subtypeVal.isClosedMap _ hUc,
      hUconn.image Subtype.val continuous_subtype_val.continuousOn, ?_⟩
    rintro y ⟨s, hs, rfl⟩
    exact regularAtDim_ambientImage_of_intrinsic hk hS (hUr s hs)
  refine ⟨hDeq.symm ▸ hD, ?_, hDeq⟩
  rintro y ⟨t, _, rfl⟩
  exact (e t).2

/-- Genuine original embedded resolution, the same ambient ancestor tower,
and the literal lower comparison image are produced internally. The lower
carrier is not asserted to be a full ambient strict transform. -/
theorem exists_ambientAncestorTower_resolving_intrinsicDescendant
    {n k : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
    (omegaX : KahlerBackground n X) {N : Set X} (hk : k ≤ n) (hNc : IsClosed N)
    (hN : ∀ x ∈ N, RegularAtDim (n := n) N x k)
    {I : Type v} (A : I → Set X) (d : I → ℕ) (hd : ∀ i, d i ≤ n)
    (hNA : ∀ i, N ⊆ A i) (hAc : ∀ i, IsClosed (A i))
    (hA : ∀ i, ∀ x ∈ A i, RegularAtDim (n := n) (A i) x (d i))
    (V : letI := SubmanifoldChartedSpace.chartedSpace hk hN
      letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hN
      ClosedIrreducibleAnalyticSubvariety k N) :
    letI := SubmanifoldChartedSpace.chartedSpace hk hN
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hN
    ∃ (Nt : Type u) (_ : TopologicalSpace Nt) (_ : ChartedSpace (ComplexModel k) Nt)
      (_ : IsComplexManifold k Nt) (q : Nt → N),
      IsBlowupSequence k N Nt q ∧
      EmbeddedResolution.IsEmbeddedResolution V q ∧
      ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
        (_ : IsComplexManifold n Y) (_ : CompactSpace Y) (_ : KahlerBackground n Y)
        (p : Y → X) (S : Set Y) (hS : ∀ y ∈ S, RegularAtDim (n := n) S y k),
        IsBlowupSequence n X Y p ∧ IsClosed S ∧ S = strictTransform n p N ∧
        ∃ hA' : ∀ i, ∀ y ∈ strictTransform n p (A i),
            RegularAtDim (n := n) (strictTransform n p (A i)) y (d i),
          ((∀ i j, A i ⊆ A j → strictTransform n p (A i) ⊆ strictTransform n p (A j)) ∧
           ∀ i, IsClosed (strictTransform n p (A i)) ∧
             S ⊆ strictTransform n p (A i) ∧
             ∃ hi : ∀ y ∈ strictTransform n p (A i), p y ∈ A i,
               letI := SubmanifoldChartedSpace.chartedSpace (hd i) (hA i)
               letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hd i) (hA i)
               letI := SubmanifoldChartedSpace.chartedSpace (hd i) (hA' i)
               letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hd i) (hA' i)
               IsAnalyticModification (n := d i)
                 (fun y : strictTransform n p (A i) => (⟨p y.1, hi y.1 y.2⟩ : A i))) ∧
          letI := SubmanifoldChartedSpace.chartedSpace hk hS
          ∃ (e : Nt → S) (f : S → Nt),
            ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ e ∧
            ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ f ∧
            f ∘ e = id ∧ e ∘ f = id ∧
            p ∘ ((Subtype.val : S → Y) ∘ e) = (Subtype.val : N → X) ∘ q ∧
            ∃ D : Set Y, IsClosedConnectedSubmanifold n D V.dim ∧
              D = ((Subtype.val : S → Y) ∘ e) '' strictTransform k q V.carrier ∧
              D ⊆ S ∧ p '' D = (Subtype.val : N → X) '' V.carrier := by
  classical
  let := SubmanifoldChartedSpace.chartedSpace hk hN
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hN
  let : CompactSpace N := isCompact_iff_compactSpace.mp hNc.isCompact
  let omegaN := SubmanifoldKahlerRestriction.kahlerBackground hk hN omegaX
  obtain ⟨Nt, topNt, chartsNt, complexNt, q, hq, hres⟩ :=
    EmbeddedResolution.exists_embeddedResolution V
  let := topNt
  let := chartsNt
  let := complexNt
  obtain ⟨compactNt, ⟨_omegaNt⟩⟩ :=
    LocusProperties.compactSpace_and_kahler_of_isBlowupSequence ⟨omegaN⟩ q hq
  let := compactNt
  have hT := hres.2
  have hqproper : IsProperMap q := hq.contMDiff.continuous.isProperMap
  obtain ⟨VT, hVT, _hdimT⟩ :=
    SourceGenericSubmanifoldMinimum.exists_subvariety_carrier_eq_of_submanifold hT
  have hqimage : q '' strictTransform k q V.carrier = V.carrier := by
    simpa only [hVT] using
      RawProperStrictTransformLelongReader.image_eq_of_strictTransform
        hq.contMDiff hqproper V VT hVT
  obtain ⟨Y, topY, chartsY, complexY, compactY, omegaY, p, S, hS,
    hp, hSc, hSstrict, hA', ⟨e, f, he, hf, hfe, hef, hcomm⟩, hNest, hMods⟩ :=
    exists_ambientRealization_of_intrinsicBlowupSequence_withAncestorModifications
      omegaX hk hNc hN A d hd hNA hAc hA hq
  let := topY
  let := chartsY
  let := complexY
  let := compactY
  let := SubmanifoldChartedSpace.chartedSpace hk hS
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hS
  let D : Set Y := ((Subtype.val : S → Y) ∘ e) '' strictTransform k q V.carrier
  obtain ⟨hD, hDS, _hDpreimage⟩ :=
    isClosedConnectedSubmanifold_descendantComparisonImage hk hSc hS he hf hfe hef hT
  refine ⟨Nt, topNt, chartsNt, complexNt, q, hq, hres,
    Y, topY, chartsY, complexY, compactY, omegaY, p, S, hS, hp, hSc, hSstrict,
    hA', ⟨hNest, hMods⟩, e, f, he, hf, hfe, hef, hcomm, D, hD, rfl, hDS, ?_⟩
  calc
    p '' D = (p ∘ ((Subtype.val : S → Y) ∘ e)) '' strictTransform k q V.carrier :=
      image_image p ((Subtype.val : S → Y) ∘ e) (strictTransform k q V.carrier)
    _ = ((Subtype.val : N → X) ∘ q) '' strictTransform k q V.carrier :=
      congrArg (fun F => F '' strictTransform k q V.carrier) hcomm
    _ = (Subtype.val : N → X) '' (q '' strictTransform k q V.carrier) :=
      (image_image (Subtype.val : N → X) q (strictTransform k q V.carrier)).symm
    _ = (Subtype.val : N → X) '' V.carrier := by rw [hqimage]

end SGPT.Okounkov
