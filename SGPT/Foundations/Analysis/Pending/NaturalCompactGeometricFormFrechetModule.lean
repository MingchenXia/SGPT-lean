import SGPT.Foundations.Analysis.Pending.NaturalCompactGeometricFormLinearModel
import Mathlib.Topology.Algebra.Module.TransferInstance

/-!
# The original geometric quotient as a complete locally convex module

The proved closed supported linear model internally transports all operations
and uniformity to the original geometric quotient. The same localization is an
actual continuous linear equivalence with exact original coefficient readback.
Atlas independence and continuity of exterior operators are separate results.
-/

noncomputable section

open Set TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalCompactGeometricFormFrechetModule

open FirstPass NaturalCompactGeometricFormLinearModel

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A compact original manifold internally supplies the genuine complete global module. -/
theorem exists_complete_locally_convex_module [CompactSpace M] :
    ∃ (m : ℕ) (e : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ)
      (K : Fin m → Compacts (ComplexModel n)),
      (∀ i, ChartSmooth (n := n) (χ i)) ∧ (∀ i x, 0 ≤ χ i x) ∧
      (∀ i, tsupport (χ i) ⊆ (e i).val.source) ∧
      (∀ i, (K i : Set (ComplexModel n)) = (e i).val '' tsupport (χ i)) ∧
      (∀ x, ∑ i, χ i x = 1) ∧
      ∀ q : ℕ, ∃ S : Submodule ℝ
        (Π i : Fin m, 𝓓_{K i}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ)),
        IsClosed (S : Set (Π i : Fin m,
          𝓓_{K i}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ))) ∧
        ∃ g : AddCommGroup (GeometricRealForm n M q),
          let _ := g
          ∃ v : Module ℝ (GeometricRealForm n M q),
            let _ := v
            ∃ u : UniformSpace (GeometricRealForm n M q),
              let _ := u
              ∃ E : GeometricRealForm n M q ≃L[ℝ] S,
                CompleteSpace (GeometricRealForm n M q) ∧
                T2Space (GeometricRealForm n M q) ∧
                FirstCountableTopology (GeometricRealForm n M q) ∧
                IsTopologicalAddGroup (GeometricRealForm n M q) ∧
                ContinuousSMul ℝ (GeometricRealForm n M q) ∧
                LocallyConvexSpace ℝ (GeometricRealForm n M q) ∧
                ∀ (α : SmoothRealForm n M q) i z,
                  (E (GeometricRealForm.ofRepresentative α)).val i z =
                    (e i).val.target.indicator
                      (fun y => χ i ((e i).val.symm y) • α.coeff (e i) y) z := by
  classical
  obtain ⟨m, e, χ, K, hχ, hnonneg, hs, hK, h1, hE⟩ :=
    exists_closed_supported_linear_model (n := n) (M := M)
  refine ⟨m, e, χ, K, hχ, hnonneg, hs, hK, h1, fun q => ?_⟩
  obtain ⟨S, hS, E, hcomplete, hT2, hfc, hconvex, hread⟩ := hE q
  let _ := hcomplete
  let _ := hT2
  let _ := hfc
  let _ := hconvex
  let g : AddCommGroup (GeometricRealForm n M q) := E.addCommGroup
  let _ := g
  let v : Module ℝ (GeometricRealForm n M q) := E.module ℝ
  let _ := v
  let u : UniformSpace (GeometricRealForm n M q) :=
    UniformSpace.comap E (inferInstance : UniformSpace S)
  let _ := u
  let le : GeometricRealForm n M q ≃L[ℝ] S := E.continuousLinearEquiv ℝ
  have he : IsUniformEmbedding E := isUniformEmbedding_comap E.injective
  have hc : CompleteSpace (GeometricRealForm n M q) := by
    apply he.isUniformInducing.completeSpace
    rw [Set.range_eq_univ.mpr E.surjective]
    exact isComplete_univ
  have ht : T2Space (GeometricRealForm n M q) := he.isEmbedding.t2Space
  have hf : FirstCountableTopology (GeometricRealForm n M q) :=
    he.isEmbedding.firstCountableTopology
  have ha : IsTopologicalAddGroup (GeometricRealForm n M q) :=
    le.toContinuousAddEquiv.isTopologicalAddGroup (β := S)
  have hv : ContinuousSMul ℝ (GeometricRealForm n M q) := le.continuousSMul (β := S)
  have hl : LocallyConvexSpace ℝ (GeometricRealForm n M q) :=
    le.toHomeomorph.isInducing.locallyConvexSpace (f := le.toLinearMap)
  refine ⟨S, hS, g, v, u, le, hc, ht, hf, ha, hv, hl, ?_⟩
  intro α i z
  exact hread α i z

end SGPT.Foundations.Analysis.Pending.NaturalCompactGeometricFormFrechetModule
