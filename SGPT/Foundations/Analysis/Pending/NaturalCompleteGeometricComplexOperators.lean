import SGPT.Foundations.Analysis.Pending.NaturalCompleteGeometricExteriorOperator
import SGPT.Foundations.Analysis.Pending.NaturalGeometricComplexDifferentials

/-!
# The original normalized complex operators on the same complete global modules

All three degree structures come from one actual compact supported model
construction. Its exact original full readbacks internally construct the
literal original d, dc and ddc continuous linear maps with the original
normalization. No differential continuity or topology certificate is assumed.
-/

noncomputable section

open Set TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalCompleteGeometricComplexOperators

open FirstPass XiaoComplexDifferential NaturalGeometricComplexDifferentials
  NaturalGlobalExteriorDifferential NaturalCompactSmoothFormEmbedding
  NaturalCompactGeometricFormFrechetModule NaturalCompleteGeometricExteriorOperator

variable {n q m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Restrict the actual tensor twist to its internally proved invariant original model. -/
theorem exists_complexTwistCLM_in_model
    (e : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ)
    (_hχ : ∀ i, ChartSmooth (n := n) (χ i)) (hc : ∀ i, IsCompact (tsupport (χ i)))
    (hs : ∀ i, tsupport (χ i) ⊆ (e i).val.source)
    (S : Submodule ℝ (Π i : Fin m,
      𝓓_{chartSupport (e i) (χ i) (hc i) (hs i)}(ComplexModel n,
        (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ)))
    [AddCommGroup (GeometricRealForm n M q)] [Module ℝ (GeometricRealForm n M q)]
    [UniformSpace (GeometricRealForm n M q)]
    (E : GeometricRealForm n M q ≃L[ℝ] S)
    (hread : ∀ (α : SmoothRealForm n M q) i z,
      (E (GeometricRealForm.ofRepresentative α)).val i z =
        (e i).val.target.indicator
          (fun y => χ i ((e i).val.symm y) • α.coeff (e i) y) z) :
    ∃ T : GeometricRealForm n M q →L[ℝ] GeometricRealForm n M q,
      ∀ a, T a = geometricComplexTwist a := by
  let B := productPostcompCLM (q := q) (fun i => chartSupport (e i) (χ i) (hc i) (hs i))
    (ContinuousAlternatingMap.compContinuousLinearMapCLM (modelComplexStructure n))
  have hint (a : GeometricRealForm n M q) :
      (E (geometricComplexTwist a)).val = B (E a).val := by
    refine Quotient.inductionOn a ?_
    intro α
    funext i
    apply ContDiffMapSupportedIn.ext
    intro z
    change (E (GeometricRealForm.ofRepresentative (complexTwist α))).val i z =
      ((E (GeometricRealForm.ofRepresentative α)).val i z).compContinuousLinearMap
        (modelComplexStructure n)
    rw [hread, hread]
    by_cases hz : z ∈ (e i).val.target
    · simp only [indicator_of_mem hz, complexTwist_coeff]
      exact ((ContinuousAlternatingMap.compContinuousLinearMapCLM
        (modelComplexStructure n)).map_smul (χ i ((e i).val.symm z)) (α.coeff (e i) z)).symm
    · simp only [indicator_of_notMem hz]
      exact ((ContinuousAlternatingMap.compContinuousLinearMapCLM
        (modelComplexStructure n)).map_zero).symm
  have hstable (s : S) : B s.val ∈ S := by
    obtain ⟨a, rfl⟩ := E.surjective s
    rw [← hint]
    exact (E (geometricComplexTwist a)).property
  let Q : S →L[ℝ] S := B.restrict (fun s hs => hstable ⟨s, hs⟩)
  let T : GeometricRealForm n M q →L[ℝ] GeometricRealForm n M q :=
    E.symm.toContinuousLinearMap.comp (Q.comp E.toContinuousLinearMap)
  refine ⟨T, fun a => ?_⟩
  apply E.injective
  apply Subtype.ext
  change (E (E.symm (Q (E a)))).val = (E (geometricComplexTwist a)).val
  rw [E.apply_symm_apply]
  exact (hint a).symm

/-- The original quotient scalar action equals the scalar action on that very same model. -/
theorem geometricScalar_eq_smul_in_model
    (e : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ)
    (_hχ : ∀ i, ChartSmooth (n := n) (χ i)) (hc : ∀ i, IsCompact (tsupport (χ i)))
    (hs : ∀ i, tsupport (χ i) ⊆ (e i).val.source)
    (S : Submodule ℝ (Π i : Fin m,
      𝓓_{chartSupport (e i) (χ i) (hc i) (hs i)}(ComplexModel n,
        (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ)))
    [AddCommGroup (GeometricRealForm n M q)] [Module ℝ (GeometricRealForm n M q)]
    [UniformSpace (GeometricRealForm n M q)]
    (E : GeometricRealForm n M q ≃L[ℝ] S)
    (hread : ∀ (α : SmoothRealForm n M q) i z,
      (E (GeometricRealForm.ofRepresentative α)).val i z =
        (e i).val.target.indicator
          (fun y => χ i ((e i).val.symm y) • α.coeff (e i) y) z)
    (c : ℝ) (a : GeometricRealForm n M q) : geometricScalar c a = c • a := by
  refine Quotient.inductionOn a ?_
  intro α
  apply E.injective
  change E (GeometricRealForm.ofRepresentative (c • α)) =
    E (c • GeometricRealForm.ofRepresentative α)
  rw [map_smul]
  apply Subtype.ext
  funext i
  apply ContDiffMapSupportedIn.ext
  intro z
  change (E (GeometricRealForm.ofRepresentative (c • α))).val i z =
    c • (E (GeometricRealForm.ofRepresentative α)).val i z
  rw [hread, hread]
  by_cases hz : z ∈ (e i).val.target
  · simp only [indicator_of_mem hz, ProductTestForms.coeff_smul]
    exact smul_comm _ _ _
  · simp only [indicator_of_notMem hz, smul_zero]

/-- Compactness internally constructs one actual degree triple carrying the original operators. -/
theorem exists_complete_geometric_complex_operators [CompactSpace M] :
    ∃ (m : ℕ) (e : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ)
      (K : Fin m → Compacts (ComplexModel n)),
      (∀ i, ChartSmooth (n := n) (χ i)) ∧ (∀ i x, 0 ≤ χ i x) ∧
      (∀ i, tsupport (χ i) ⊆ (e i).val.source) ∧
      (∀ i, (K i : Set (ComplexModel n)) = (e i).val '' tsupport (χ i)) ∧
      (∀ x, ∑ i, χ i x = 1) ∧
      ∀ q : ℕ,
        ∃ (S0 : Submodule ℝ (Π i : Fin m,
          𝓓_{K i}(ComplexModel n, (ComplexModel n) [⋀^Fin (q)]→L[ℝ] ℝ)))
        (S1 : Submodule ℝ (Π i : Fin m,
          𝓓_{K i}(ComplexModel n, (ComplexModel n) [⋀^Fin (q + 1)]→L[ℝ] ℝ)))
        (S2 : Submodule ℝ (Π i : Fin m,
          𝓓_{K i}(ComplexModel n, (ComplexModel n) [⋀^Fin (q + 1 + 1)]→L[ℝ] ℝ))),
        IsClosed (S0 : Set (Π i : Fin m,
          𝓓_{K i}(ComplexModel n, (ComplexModel n) [⋀^Fin (q)]→L[ℝ] ℝ))) ∧
        IsClosed (S1 : Set (Π i : Fin m,
          𝓓_{K i}(ComplexModel n, (ComplexModel n) [⋀^Fin (q + 1)]→L[ℝ] ℝ))) ∧
        IsClosed (S2 : Set (Π i : Fin m,
          𝓓_{K i}(ComplexModel n, (ComplexModel n) [⋀^Fin (q + 1 + 1)]→L[ℝ] ℝ))) ∧
        ∃ g0 : AddCommGroup (GeometricRealForm n M (q)), let _ := g0
        ∃ v0 : Module ℝ (GeometricRealForm n M (q)), let _ := v0
        ∃ u0 : UniformSpace (GeometricRealForm n M (q)), let _ := u0
        ∃ g1 : AddCommGroup (GeometricRealForm n M (q + 1)), let _ := g1
        ∃ v1 : Module ℝ (GeometricRealForm n M (q + 1)), let _ := v1
        ∃ u1 : UniformSpace (GeometricRealForm n M (q + 1)), let _ := u1
        ∃ g2 : AddCommGroup (GeometricRealForm n M (q + 1 + 1)), let _ := g2
        ∃ v2 : Module ℝ (GeometricRealForm n M (q + 1 + 1)), let _ := v2
        ∃ u2 : UniformSpace (GeometricRealForm n M (q + 1 + 1)), let _ := u2
        ∃ (E0 : GeometricRealForm n M (q) ≃L[ℝ] S0)
        (E1 : GeometricRealForm n M (q + 1) ≃L[ℝ] S1)
        (E2 : GeometricRealForm n M (q + 1 + 1) ≃L[ℝ] S2),
          CompleteSpace (GeometricRealForm n M (q)) ∧ T2Space (GeometricRealForm n M (q)) ∧
          FirstCountableTopology (GeometricRealForm n M (q)) ∧
          IsTopologicalAddGroup (GeometricRealForm n M (q)) ∧
          ContinuousSMul ℝ (GeometricRealForm n M (q)) ∧
          LocallyConvexSpace ℝ (GeometricRealForm n M (q)) ∧
          CompleteSpace (GeometricRealForm n M (q + 1)) ∧ T2Space (GeometricRealForm n M (q + 1)) ∧
          FirstCountableTopology (GeometricRealForm n M (q + 1)) ∧
          IsTopologicalAddGroup (GeometricRealForm n M (q + 1)) ∧
          ContinuousSMul ℝ (GeometricRealForm n M (q + 1)) ∧
          LocallyConvexSpace ℝ (GeometricRealForm n M (q + 1)) ∧
          CompleteSpace (GeometricRealForm n M (q + 1 + 1)) ∧ T2Space (GeometricRealForm n M (q + 1 + 1)) ∧
          FirstCountableTopology (GeometricRealForm n M (q + 1 + 1)) ∧
          IsTopologicalAddGroup (GeometricRealForm n M (q + 1 + 1)) ∧
          ContinuousSMul ℝ (GeometricRealForm n M (q + 1 + 1)) ∧
          LocallyConvexSpace ℝ (GeometricRealForm n M (q + 1 + 1)) ∧
          (∀ (α : SmoothRealForm n M (q)) i z,
            (E0 (GeometricRealForm.ofRepresentative α)).val i z =
              (e i).val.target.indicator
                (fun y => χ i ((e i).val.symm y) • α.coeff (e i) y) z) ∧
          (∀ (α : SmoothRealForm n M (q + 1)) i z,
            (E1 (GeometricRealForm.ofRepresentative α)).val i z =
              (e i).val.target.indicator
                (fun y => χ i ((e i).val.symm y) • α.coeff (e i) y) z) ∧
          (∀ (α : SmoothRealForm n M (q + 1 + 1)) i z,
            (E2 (GeometricRealForm.ofRepresentative α)).val i z =
              (e i).val.target.indicator
                (fun y => χ i ((e i).val.symm y) • α.coeff (e i) y) z) ∧
          ∃ (D₀ : GeometricRealForm n M q →L[ℝ] GeometricRealForm n M (q + 1))
            (D₁ : GeometricRealForm n M (q + 1) →L[ℝ] GeometricRealForm n M (q + 1 + 1))
            (C₀ : GeometricRealForm n M q →L[ℝ] GeometricRealForm n M (q + 1))
            (C₁ : GeometricRealForm n M q →L[ℝ] GeometricRealForm n M (q + 1 + 1)),
              (∀ a, D₀ a = geometricExteriorDerivative a) ∧
              (∀ a, D₁ a = geometricExteriorDerivative a) ∧
              (∀ a, C₀ a = geometricDc a) ∧ (∀ a, C₁ a = geometricDdc a) := by
  classical
  obtain ⟨m, e, χ, K, hχ, hnonneg, hs, hK, h1, hE⟩ :=
    exists_complete_locally_convex_module (n := n) (M := M)
  let hc : ∀ i, IsCompact (tsupport (χ i)) := fun i => (isClosed_tsupport (χ i)).isCompact
  have hcanonical : K = fun i => chartSupport (e i) (χ i) (hc i) (hs i) := by
    funext i
    apply Compacts.ext
    exact hK i
  subst K
  refine ⟨m, e, χ, _, hχ, hnonneg, hs, hK, h1, fun q => ?_⟩
  obtain ⟨S0, hS0, g0, v0, u0, E0, hc0, ht0, hf0, ha0, hv0, hl0, hread0⟩ := hE (q)
  let _ := g0
  let _ := v0
  let _ := u0
  let _ := ha0
  let _ := hv0
  obtain ⟨S1, hS1, g1, v1, u1, E1, hc1, ht1, hf1, ha1, hv1, hl1, hread1⟩ := hE (q + 1)
  let _ := g1
  let _ := v1
  let _ := u1
  let _ := ha1
  let _ := hv1
  obtain ⟨S2, hS2, g2, v2, u2, E2, hc2, ht2, hf2, ha2, hv2, hl2, hread2⟩ := hE (q + 1 + 1)
  let _ := g2
  let _ := v2
  let _ := u2
  let _ := ha2
  let _ := hv2
  obtain ⟨D₀, hD₀⟩ := exists_exteriorDerivativeCLM_in_models e χ hχ hc hs h1
    S0 S1 E0 E1 hread0 hread1
  obtain ⟨D₁, hD₁⟩ := exists_exteriorDerivativeCLM_in_models e χ hχ hc hs h1
    S1 S2 E1 E2 hread1 hread2
  obtain ⟨T₀, hT₀⟩ := exists_complexTwistCLM_in_model e χ hχ hc hs S0 E0 hread0
  obtain ⟨T₁, hT₁⟩ := exists_complexTwistCLM_in_model e χ hχ hc hs S1 E1 hread1
  let c : ℝ := (-1 : ℝ) ^ (q + 1) / (4 * Real.pi)
  let C₀ : GeometricRealForm n M q →L[ℝ] GeometricRealForm n M (q + 1) :=
    c • (T₁.comp (D₀.comp T₀))
  have hC₀ (a : GeometricRealForm n M q) : C₀ a = geometricDc a := by
    change c • T₁ (D₀ (T₀ a)) = geometricDc a
    rw [hT₁, hD₀, hT₀]
    rw [← geometricScalar_eq_smul_in_model e χ hχ hc hs S1 E1 hread1 c]
    rw [geometricDc_factor]
    rfl
  let C₁ : GeometricRealForm n M q →L[ℝ] GeometricRealForm n M (q + 1 + 1) :=
    D₁.comp C₀
  have hC₁ (a : GeometricRealForm n M q) : C₁ a = geometricDdc a := by
    change D₁ (C₀ a) = geometricDdc a
    rw [hD₁, hC₀, geometricDdc_factor]
    rfl
  refine ⟨S0, S1, S2, hS0, hS1, hS2, g0, v0, u0, g1, v1, u1, g2, v2, u2,
    E0, E1, E2, hc0, ht0, hf0, ha0, hv0, hl0, hc1, ht1, hf1, ha1, hv1, hl1,
    hc2, ht2, hf2, ha2, hv2, hl2, hread0, hread1, hread2, D₀, D₁, C₀, C₁,
    hD₀, hD₁, hC₀, hC₁⟩

end SGPT.Foundations.Analysis.Pending.NaturalCompleteGeometricComplexOperators
