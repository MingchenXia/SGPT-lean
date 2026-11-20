import SGPT.Foundations.Analysis.Pending.NaturalGlobalExteriorDifferential
import SGPT.Foundations.Analysis.Pending.NaturalCompactGeometricFormFrechetModule
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# The literal original exterior operator on the genuine complete global modules

Natural compactness internally supplies the SAME original degree-pair module
structures and actual faithful supported models. The whole derivative factor
proves range invariance and the original continuous linear derivative; its
kernel is exactly the original geometrically closed forms, closed and complete.
-/

noncomputable section

open Set TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalCompleteGeometricExteriorOperator

open FirstPass NaturalGlobalExteriorDifferential NaturalCompactSmoothFormEmbedding
  NaturalCompactGeometricFormFrechetModule

variable {n q m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual restriction to the genuine model images, derived from their original full readbacks. -/
theorem exists_exteriorDerivativeCLM_in_models
    (e : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ)
    (hχ : ∀ i, ChartSmooth (n := n) (χ i)) (hc : ∀ i, IsCompact (tsupport (χ i)))
    (hs : ∀ i, tsupport (χ i) ⊆ (e i).val.source) (h1 : ∀ x, ∑ i, χ i x = 1)
    (S₀ : Submodule ℝ (Π i : Fin m,
      𝓓_{chartSupport (e i) (χ i) (hc i) (hs i)}(ComplexModel n,
        (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ)))
    (S₁ : Submodule ℝ (Π i : Fin m,
      𝓓_{chartSupport (e i) (χ i) (hc i) (hs i)}(ComplexModel n,
        (ComplexModel n) [⋀^Fin (q + 1)]→L[ℝ] ℝ)))
    [AddCommGroup (GeometricRealForm n M q)] [Module ℝ (GeometricRealForm n M q)]
    [UniformSpace (GeometricRealForm n M q)]
    [AddCommGroup (GeometricRealForm n M (q + 1))]
    [Module ℝ (GeometricRealForm n M (q + 1))]
    [UniformSpace (GeometricRealForm n M (q + 1))]
    (E₀ : GeometricRealForm n M q ≃L[ℝ] S₀)
    (E₁ : GeometricRealForm n M (q + 1) ≃L[ℝ] S₁)
    (hread₀ : ∀ (α : SmoothRealForm n M q) i z,
      (E₀ (GeometricRealForm.ofRepresentative α)).val i z =
        (e i).val.target.indicator
          (fun y => χ i ((e i).val.symm y) • α.coeff (e i) y) z)
    (hread₁ : ∀ (α : SmoothRealForm n M (q + 1)) i z,
      (E₁ (GeometricRealForm.ofRepresentative α)).val i z =
        (e i).val.target.indicator
          (fun y => χ i ((e i).val.symm y) • α.coeff (e i) y) z) :
    ∃ D : GeometricRealForm n M q →L[ℝ] GeometricRealForm n M (q + 1),
      ∀ a, D a = geometricExteriorDerivative a := by
  let B := localizedExteriorDerivativeCLM (q := q) e χ hχ hc hs
  have hint (a : GeometricRealForm n M q) :
      (E₁ (geometricExteriorDerivative a)).val = B (E₀ a).val := by
    refine Quotient.inductionOn a ?_
    intro α
    have h₀ : (E₀ (GeometricRealForm.ofRepresentative α)).val =
        fun i => localizedSupported (e i) (χ i) (hχ i) (hc i) (hs i) α := by
      funext i
      apply ContDiffMapSupportedIn.ext
      intro z
      exact hread₀ α i z
    have h₁ : (E₁ (GeometricRealForm.ofRepresentative α.exteriorDerivative)).val =
        fun i => localizedSupported (e i) (χ i) (hχ i) (hc i) (hs i) α.exteriorDerivative := by
      funext i
      apply ContDiffMapSupportedIn.ext
      intro z
      exact hread₁ α.exteriorDerivative i z
    change (E₁ (GeometricRealForm.ofRepresentative α.exteriorDerivative)).val =
      B (E₀ (GeometricRealForm.ofRepresentative α)).val
    rw [h₀, h₁]
    exact (localizedExteriorDerivativeCLM_localized e χ hχ hc hs h1 α).symm
  have hstable (s : S₀) : B s.val ∈ S₁ := by
    obtain ⟨a, rfl⟩ := E₀.surjective s
    rw [← hint]
    exact (E₁ (geometricExteriorDerivative a)).property
  let Q : S₀ →L[ℝ] S₁ := (B.domRestrict S₀).codRestrict S₁ hstable
  let D : GeometricRealForm n M q →L[ℝ] GeometricRealForm n M (q + 1) :=
    E₁.symm.toContinuousLinearMap.comp (Q.comp E₀.toContinuousLinearMap)
  refine ⟨D, fun a => ?_⟩
  apply E₁.injective
  apply Subtype.ext
  change (E₁ (E₁.symm (Q (E₀ a)))).val = (E₁ (geometricExteriorDerivative a)).val
  rw [E₁.apply_symm_apply]
  exact (hint a).symm

/-- Natural compactness internally supplies the original complete continuous operator and closed kernel. -/
theorem exists_complete_geometric_exterior_operator [CompactSpace M] :
    ∃ (m : ℕ) (e : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ)
      (K : Fin m → Compacts (ComplexModel n)),
      (∀ i, ChartSmooth (n := n) (χ i)) ∧ (∀ i x, 0 ≤ χ i x) ∧
      (∀ i, tsupport (χ i) ⊆ (e i).val.source) ∧
      (∀ i, (K i : Set (ComplexModel n)) = (e i).val '' tsupport (χ i)) ∧
      (∀ x, ∑ i, χ i x = 1) ∧
      ∀ q : ℕ, ∃ (S₀ : Submodule ℝ (Π i : Fin m,
          𝓓_{K i}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ)))
        (S₁ : Submodule ℝ (Π i : Fin m,
          𝓓_{K i}(ComplexModel n, (ComplexModel n) [⋀^Fin (q + 1)]→L[ℝ] ℝ))),
        IsClosed (S₀ : Set (Π i : Fin m,
          𝓓_{K i}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ))) ∧
        IsClosed (S₁ : Set (Π i : Fin m,
          𝓓_{K i}(ComplexModel n, (ComplexModel n) [⋀^Fin (q + 1)]→L[ℝ] ℝ))) ∧
        ∃ g₀ : AddCommGroup (GeometricRealForm n M q), let _ := g₀
        ∃ v₀ : Module ℝ (GeometricRealForm n M q), let _ := v₀
        ∃ u₀ : UniformSpace (GeometricRealForm n M q), let _ := u₀
        ∃ g₁ : AddCommGroup (GeometricRealForm n M (q + 1)), let _ := g₁
        ∃ v₁ : Module ℝ (GeometricRealForm n M (q + 1)), let _ := v₁
        ∃ u₁ : UniformSpace (GeometricRealForm n M (q + 1)), let _ := u₁
        ∃ (E₀ : GeometricRealForm n M q ≃L[ℝ] S₀)
          (E₁ : GeometricRealForm n M (q + 1) ≃L[ℝ] S₁),
          CompleteSpace (GeometricRealForm n M q) ∧ T2Space (GeometricRealForm n M q) ∧
          FirstCountableTopology (GeometricRealForm n M q) ∧
          IsTopologicalAddGroup (GeometricRealForm n M q) ∧
          ContinuousSMul ℝ (GeometricRealForm n M q) ∧
          LocallyConvexSpace ℝ (GeometricRealForm n M q) ∧
          CompleteSpace (GeometricRealForm n M (q + 1)) ∧ T2Space (GeometricRealForm n M (q + 1)) ∧
          FirstCountableTopology (GeometricRealForm n M (q + 1)) ∧
          IsTopologicalAddGroup (GeometricRealForm n M (q + 1)) ∧
          ContinuousSMul ℝ (GeometricRealForm n M (q + 1)) ∧
          LocallyConvexSpace ℝ (GeometricRealForm n M (q + 1)) ∧
          (∀ (α : SmoothRealForm n M q) i z,
            (E₀ (GeometricRealForm.ofRepresentative α)).val i z =
              (e i).val.target.indicator
                (fun y => χ i ((e i).val.symm y) • α.coeff (e i) y) z) ∧
          (∀ (α : SmoothRealForm n M (q + 1)) i z,
            (E₁ (GeometricRealForm.ofRepresentative α)).val i z =
              (e i).val.target.indicator
                (fun y => χ i ((e i).val.symm y) • α.coeff (e i) y) z) ∧
          ∃ D : GeometricRealForm n M q →L[ℝ] GeometricRealForm n M (q + 1),
            (∀ a, D a = geometricExteriorDerivative a) ∧
            (∀ a, a.IsClosed ↔ D a = 0) ∧
            IsClosed {a : GeometricRealForm n M q | a.IsClosed} ∧ CompleteSpace D.ker := by
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
  obtain ⟨S₀, hS₀, g₀, v₀, u₀, E₀, hc₀, ht₀, hf₀, ha₀, hv₀, hl₀, hread₀⟩ := hE q
  let _ := g₀
  let _ := v₀
  let _ := u₀
  obtain ⟨S₁, hS₁, g₁, v₁, u₁, E₁, hc₁, ht₁, hf₁, ha₁, hv₁, hl₁, hread₁⟩ := hE (q + 1)
  let _ := g₁
  let _ := v₁
  let _ := u₁
  let _ := hc₀
  let _ := ht₀
  let _ := hc₁
  let _ := ht₁
  obtain ⟨D, hD⟩ := exists_exteriorDerivativeCLM_in_models e χ hχ hc hs h1
    S₀ S₁ E₀ E₁ hread₀ hread₁
  have hzero : GeometricRealForm.ofRepresentative (SmoothRealForm.zero : SmoothRealForm n M (q + 1)) =
      (0 : GeometricRealForm n M (q + 1)) := by
    apply E₁.injective
    apply Subtype.ext
    funext i
    apply ContDiffMapSupportedIn.ext
    intro z
    rw [hread₁]
    simp [SmoothRealForm.zero]
  have hclosed (a : GeometricRealForm n M q) : a.IsClosed ↔ D a = 0 := by
    rw [hD, ← hzero]
    refine Quotient.inductionOn a ?_
    intro α
    change α.IsClosed ↔ GeometricRealForm.ofRepresentative α.exteriorDerivative =
      GeometricRealForm.ofRepresentative SmoothRealForm.zero
    rw [GeometricRealForm.ofRepresentative_eq_iff]
    exact α.isClosed_iff_exteriorDerivative_geometricallyEq_zero
  have hker : IsClosed (D.ker : Set (GeometricRealForm n M q)) := D.isClosed_ker
  have hclosedset : IsClosed {a : GeometricRealForm n M q | a.IsClosed} := by
    convert hker using 1
    ext a
    exact hclosed a
  refine ⟨S₀, S₁, hS₀, hS₁, g₀, v₀, u₀, g₁, v₁, u₁, E₀, E₁,
    hc₀, ht₀, hf₀, ha₀, hv₀, hl₀, hc₁, ht₁, hf₁, ha₁, hv₁, hl₁,
    hread₀, hread₁, D, hD, hclosed, hclosedset, hker.completeSpace_coe⟩

end SGPT.Foundations.Analysis.Pending.NaturalCompleteGeometricExteriorOperator
