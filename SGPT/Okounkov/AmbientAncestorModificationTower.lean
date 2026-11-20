import SGPT.Okounkov.ClosedSmoothAncestorModification
import SGPT.Okounkov.FlagLelong
import SGPT.Foundations.Analysis.Pending.AnalyticModificationComposition

set_option autoImplicit false

noncomputable section

universe u v

namespace SGPT.Okounkov

open Set
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy

/-- The actual intrinsic sequence manufactures one compact Kähler ambient
tower, all simultaneous smooth strict ancestors and genuine analytic
modification records for every literal restricted projection on that same tower. -/
theorem exists_ambientRealization_of_intrinsicBlowupSequence_withAncestorModifications
    {n k : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
    (omegaX : KahlerBackground n X) {N : Set X} (hk : k ≤ n) (hNc : IsClosed N)
    (hN : ∀ x ∈ N, RegularAtDim (n := n) N x k)
    {I : Type v} (A : I → Set X) (d : I → ℕ) (hd : ∀ i, d i ≤ n)
    (hNA : ∀ i, N ⊆ A i) (hAc : ∀ i, IsClosed (A i))
    (hA : ∀ i, ∀ x ∈ A i, RegularAtDim (n := n) (A i) x (d i))
    {Nt : Type u} [TopologicalSpace Nt]
    [ChartedSpace (ComplexModel k) Nt] [IsComplexManifold k Nt]
    {q : Nt → N}
    (hq : letI := SubmanifoldChartedSpace.chartedSpace hk hN
      letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hN
      IsBlowupSequence k N Nt q) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (_ : CompactSpace Y) (_ : KahlerBackground n Y)
      (p : Y → X) (S : Set Y) (hS : ∀ y ∈ S, RegularAtDim (n := n) S y k),
      IsBlowupSequence n X Y p ∧ IsClosed S ∧ S = strictTransform n p N ∧
      ∃ hA' : ∀ i, ∀ y ∈ strictTransform n p (A i),
          RegularAtDim (n := n) (strictTransform n p (A i)) y (d i),
        (letI := SubmanifoldChartedSpace.chartedSpace hk hN
         letI := SubmanifoldChartedSpace.chartedSpace hk hS
         ∃ (e : Nt → S) (f : S → Nt),
           ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ e ∧
           ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ f ∧
           f ∘ e = id ∧ e ∘ f = id ∧
           p ∘ ((Subtype.val : S → Y) ∘ e) = (Subtype.val : N → X) ∘ q) ∧
        (∀ i j, A i ⊆ A j → strictTransform n p (A i) ⊆ strictTransform n p (A j)) ∧
        ∀ i, IsClosed (strictTransform n p (A i)) ∧
          S ⊆ strictTransform n p (A i) ∧
          ∃ hi : ∀ y ∈ strictTransform n p (A i), p y ∈ A i,
            letI := SubmanifoldChartedSpace.chartedSpace (hd i) (hA i)
            letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hd i) (hA i)
            letI := SubmanifoldChartedSpace.chartedSpace (hd i) (hA' i)
            letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hd i) (hA' i)
            IsAnalyticModification (n := d i)
              (fun y : strictTransform n p (A i) => (⟨p y.1, hi y.1 y.2⟩ : A i)) := by
  classical
  let := SubmanifoldChartedSpace.chartedSpace hk hN
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hN
  induction hq with
  | refl =>
      have hid : ∀ B : Set X, IsClosed B → strictTransform n (id : X → X) B = B := by
        intro B hBc
        simp only [strictTransform, exceptionalLocus_id, preimage_id, sdiff_empty,
          hBc.closure_eq]
      have hA' : ∀ i, ∀ y ∈ strictTransform n (id : X → X) (A i),
          RegularAtDim (n := n) (strictTransform n (id : X → X) (A i)) y (d i) := by
        intro i
        rw [hid (A i) (hAc i)]
        exact hA i
      refine ⟨X, inferInstance, inferInstance, inferInstance, inferInstance, omegaX,
        id, N, hN, IsBlowupSequence.refl, hNc, (hid N hNc).symm, hA',
        ⟨id, id, contMDiff_id, contMDiff_id, rfl, rfl, rfl⟩,
        fun i j hij => HironakaAdmissibleCalculus.strictTransform_mono id hij, ?_⟩
      intro i
      have hi : ∀ y ∈ strictTransform n (id : X → X) (A i), id y ∈ A i := by
        intro y hy
        rwa [hid (A i) (hAc i)] at hy
      refine ⟨isClosed_closure, ?_, hi, ?_⟩
      · rw [hid (A i) (hAc i)]
        exact hNA i
      · let := SubmanifoldChartedSpace.chartedSpace (hd i) (hA i)
        let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hd i) (hA i)
        have hm : ∀ (T : Set X)
            (hT : ∀ x ∈ T, RegularAtDim (n := n) T x (d i))
            (hiT : ∀ x ∈ T, id x ∈ A i), T = A i →
            letI := SubmanifoldChartedSpace.chartedSpace (hd i) hT
            letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hd i) hT
            IsAnalyticModification (n := d i)
              (fun x : T => (⟨id x.1, hiT x.1 x.2⟩ : A i)) := by
          intro T hT hiT heq
          subst T
          exact isAnalyticModification_identity
        exact hm _ (hA' i) hi (hid (A i) (hAc i))
  | @step N0 N1 topN0 chartsN0 complexN0 topN1 chartsN1 complexN1 q0 C b _ hb ih =>
      obtain ⟨W0, topW0, chartsW0, complexW0, compactW0, omegaW0, p0, S0, hS0,
        hp0, hS0c, hS0strict, hA0, ⟨e0, f0, he0, hf0, hfe0, hef0, hcomm0⟩,
        _hNest0, hMods0⟩ := ih
      let := topW0
      let := chartsW0
      let := complexW0
      let := compactW0
      let := SubmanifoldChartedSpace.chartedSpace hk hS0
      let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hS0
      have hb' : IsBlowupAlong k (f0 ⁻¹' C) (e0 ∘ b) :=
        MarkedIdealBiholomorphism.isBlowupAlong_comp_inverse hf0 he0
          (fun z => congrFun hfe0 z) (fun z => congrFun hef0 z) hb
      obtain ⟨W1, topW1, chartsW1, complexW1, compactW1, omegaW1, a, S1, hS1,
        ha, _haSequence, hS1c, _hS1geo, hS1strict, _hi1,
        e1, f1, he1, hf1, _hre1, _hqf1, hfe1, hef1, _himage1, hcomm1⟩ :=
        exists_ambientRealization_of_intrinsicBlowup omegaW0 hk hS0c hS0 (f0 ⁻¹' C) hb'
      let := topW1
      let := chartsW1
      let := complexW1
      let := compactW1
      let := SubmanifoldChartedSpace.chartedSpace hk hS1
      let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hS1
      have hp1 : IsBlowupSequence n X W1 (p0 ∘ a) :=
        IsBlowupSequence.step p0 (Subtype.val '' (f0 ⁻¹' C)) a hp0 ha
      have hstrict : S1 = strictTransform n (p0 ∘ a) N := by
        rw [StrictTransformComposition.strictTransform_comp hp0.contMDiff ha.contMDiff N,
          ← hS0strict]
        exact hS1strict
      have hcompA : ∀ i, strictTransform n (p0 ∘ a) (A i) =
          strictTransform n a (strictTransform n p0 (A i)) := fun i =>
        StrictTransformComposition.strictTransform_comp hp0.contMDiff ha.contMDiff (A i)
      have hS0A : ∀ i, S0 ⊆ strictTransform n p0 (A i) := by
        intro i
        rw [hS0strict]
        exact HironakaAdmissibleCalculus.strictTransform_mono p0 (hNA i)
      have hA1 : ∀ i, ∀ y ∈ strictTransform n (p0 ∘ a) (A i),
          RegularAtDim (n := n) (strictTransform n (p0 ∘ a) (A i)) y (d i) := by
        intro i
        have hreg := (regularAtDim_strictTransform_ancestor (hS0A i) isClosed_closure
          (hA0 i) (f0 ⁻¹' C) hb'.2.1 ha).2.1
        rw [hcompA]
        exact hreg
      have hcomm : (p0 ∘ a) ∘ ((Subtype.val : S1 → W1) ∘ e1) =
          (Subtype.val : N → X) ∘ (q0 ∘ b) := by
        calc
          (p0 ∘ a) ∘ ((Subtype.val : S1 → W1) ∘ e1) =
              p0 ∘ (a ∘ ((Subtype.val : S1 → W1) ∘ e1)) := rfl
          _ = p0 ∘ ((Subtype.val : S0 → W0) ∘ (e0 ∘ b)) :=
            congrArg (fun F => p0 ∘ F) hcomm1
          _ = (p0 ∘ ((Subtype.val : S0 → W0) ∘ e0)) ∘ b := rfl
          _ = (Subtype.val : N → X) ∘ (q0 ∘ b) :=
            congrArg (fun F => F ∘ b) hcomm0
      refine ⟨W1, topW1, chartsW1, complexW1, compactW1, omegaW1, p0 ∘ a, S1, hS1,
        hp1, hS1c, hstrict, hA1, ⟨e1, f1, he1, hf1, hfe1, hef1, hcomm⟩,
        fun i j hij => HironakaAdmissibleCalculus.strictTransform_mono (p0 ∘ a) hij, ?_⟩
      intro i
      have hSA : S1 ⊆ strictTransform n (p0 ∘ a) (A i) := by
        rw [hstrict]
        exact HironakaAdmissibleCalculus.strictTransform_mono (p0 ∘ a) (hNA i)
      have hi : ∀ y ∈ strictTransform n (p0 ∘ a) (A i), (p0 ∘ a) y ∈ A i :=
        fun _ hy => HironakaAdmissibleCalculus.strictTransform_subset_preimage
          hp1.contMDiff.continuous (hAc i) hy
      refine ⟨isClosed_closure, hSA, hi, ?_⟩
      let := SubmanifoldChartedSpace.chartedSpace (hd i) (hA i)
      let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hd i) (hA i)
      let := SubmanifoldChartedSpace.chartedSpace (hd i) (hA0 i)
      let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hd i) (hA0 i)
      obtain ⟨_, _, hi0, hmod0⟩ := hMods0 i
      obtain ⟨hAT1, hi1, hmod1⟩ := isAnalyticModification_strictAncestorRestriction
        (hd i) (hS0A i) isClosed_closure (hA0 i) (f0 ⁻¹' C) hb'.2.1 ha
      let := SubmanifoldChartedSpace.chartedSpace (hd i) hAT1
      let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hd i) hAT1
      have hm : ∀ (T : Set W1)
          (hT : ∀ x ∈ T, RegularAtDim (n := n) T x (d i))
          (hiT : ∀ x ∈ T, (p0 ∘ a) x ∈ A i),
          T = strictTransform n a (strictTransform n p0 (A i)) →
          letI := SubmanifoldChartedSpace.chartedSpace (hd i) hT
          letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hd i) hT
          IsAnalyticModification (n := d i)
            (fun x : T => (⟨(p0 ∘ a) x.1, hiT x.1 x.2⟩ : A i)) := by
        intro T hT hiT heq
        subst T
        exact AnalyticModificationComposition.isAnalyticModification_comp hmod0 hmod1
      exact hm _ (hA1 i) hi (hcompA i)

end SGPT.Okounkov
