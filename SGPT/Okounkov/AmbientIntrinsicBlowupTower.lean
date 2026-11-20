import SGPT.Okounkov.ClosedSubmanifoldBlowupExtension
import SGPT.Foundations.Analysis.Pending.MarkedIdealBiholomorphism
import SGPT.Foundations.Analysis.Pending.StrictTransformComposition

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending

/-- An actual finite intrinsic sequence has a compact Kähler ambient realization
with the same original projection and whole inverse comparison maps. -/
theorem exists_ambientRealization_of_intrinsicBlowupSequence
    {n k : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
    (omegaX : KahlerBackground n X) {N : Set X} (hk : k ≤ n) (hNc : IsClosed N)
    (hN : ∀ x ∈ N, RegularAtDim (n := n) N x k)
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
      letI := SubmanifoldChartedSpace.chartedSpace hk hN
      letI := SubmanifoldChartedSpace.chartedSpace hk hS
      ∃ (e : Nt → S) (f : S → Nt),
        ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ e ∧
        ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ f ∧
        f ∘ e = id ∧ e ∘ f = id ∧
        p ∘ ((Subtype.val : S → Y) ∘ e) = (Subtype.val : N → X) ∘ q := by
  classical
  let := SubmanifoldChartedSpace.chartedSpace hk hN
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hN
  induction hq with
  | refl =>
      refine ⟨X, inferInstance, inferInstance, inferInstance, inferInstance, omegaX,
        id, N, hN, IsBlowupSequence.refl, hNc, ?_, id, id,
        contMDiff_id, contMDiff_id, rfl, rfl, rfl⟩
      simp only [strictTransform, exceptionalLocus_id,
        preimage_id, sdiff_empty, hNc.closure_eq]
  | @step N0 N1 topN0 chartsN0 complexN0 topN1 chartsN1 complexN1 q0 C b _ hb ih =>
      obtain ⟨W0, topW0, chartsW0, complexW0, compactW0, omegaW0, p0, S0, hS0,
        hp0, hS0c, hS0strict, e0, f0, he0, hf0, hfe0, hef0, hcomm0⟩ := ih
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
        ha, _haSequence, hS1c, _hS1geo, hS1strict, hi1, e1, f1, he1, hf1,
        _hre1, _hqf1, hfe1, hef1, _himage1, hcomm1⟩ :=
        exists_ambientRealization_of_intrinsicBlowup omegaW0 hk hS0c hS0
          (f0 ⁻¹' C) hb'
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
      exact ⟨W1, topW1, chartsW1, complexW1, compactW1, omegaW1, p0 ∘ a, S1, hS1,
        hp1, hS1c, hstrict, e1, f1, he1, hf1, hfe1, hef1, hcomm⟩

end SGPT.Okounkov
