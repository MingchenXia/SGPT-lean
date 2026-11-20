import SGPT.Foundations.Analysis.Pending.NaturalCompactSmoothFormClosedImage
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# A genuine closed real linear model of original geometric forms

Actual pointwise zero, sums and scalar multiples of original forms prove that
the same faithful localization image is a submodule. No linear model is supplied.
-/

noncomputable section

open Set TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalCompactGeometricFormLinearModel

open FirstPass NaturalCompactSmoothFormClosedImage

variable {n q m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private def addForm (α β : SmoothRealForm n M q) : SmoothRealForm n M q where
  coeff := fun e z => α.coeff e z + β.coeff e z
  smooth := fun e => (α.smooth e).add (β.smooth e)
  compatible := by
    intro e f z hz v
    simp only [ContinuousAlternatingMap.add_apply]
    rw [α.compatible e f z hz v, β.compatible e f z hz v]

private def smulForm (r : ℝ) (α : SmoothRealForm n M q) : SmoothRealForm n M q where
  coeff := fun e z => r • α.coeff e z
  smooth := fun e => (α.smooth e).const_smul r
  compatible := by
    intro e f z hz v
    simp only [ContinuousAlternatingMap.smul_apply]
    rw [α.compatible e f z hz v]

private def supportedRange (e : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ)
    (K : Fin m → Compacts (ComplexModel n))
    (J : GeometricRealForm n M q →
      Π i : Fin m, 𝓓_{K i}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ))
    (hread : ∀ (α : SmoothRealForm n M q) i z,
      J (GeometricRealForm.ofRepresentative α) i z =
        (e i).val.target.indicator (fun y => χ i ((e i).val.symm y) • α.coeff (e i) y) z) :
    Submodule ℝ (Π i : Fin m,
      𝓓_{K i}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ)) where
  carrier := range J
  zero_mem' := by
    refine ⟨GeometricRealForm.ofRepresentative SmoothRealForm.zero, ?_⟩
    funext i
    apply ContDiffMapSupportedIn.ext
    intro z
    rw [hread]
    simp [SmoothRealForm.zero]
  add_mem' := by
    rintro d d' ⟨a, rfl⟩ ⟨b, rfl⟩
    refine Quotient.inductionOn₂ a b ?_
    intro α β
    refine ⟨GeometricRealForm.ofRepresentative (addForm α β), ?_⟩
    funext i
    apply ContDiffMapSupportedIn.ext
    intro z
    change J (GeometricRealForm.ofRepresentative (addForm α β)) i z =
      J (GeometricRealForm.ofRepresentative α) i z + J (GeometricRealForm.ofRepresentative β) i z
    rw [hread, hread, hread]
    by_cases hz : z ∈ (e i).val.target
    · simp only [indicator_of_mem hz, addForm, smul_add]
    · simp only [indicator_of_notMem hz, zero_add]
  smul_mem' := by
    rintro r d ⟨a, rfl⟩
    refine Quotient.inductionOn a ?_
    intro α
    refine ⟨GeometricRealForm.ofRepresentative (smulForm r α), ?_⟩
    funext i
    apply ContDiffMapSupportedIn.ext
    intro z
    change J (GeometricRealForm.ofRepresentative (smulForm r α)) i z =
      r • J (GeometricRealForm.ofRepresentative α) i z
    rw [hread, hread]
    by_cases hz : z ∈ (e i).val.target
    · simp only [indicator_of_mem hz, smulForm]
      exact smul_comm _ _ _
    · simp only [indicator_of_notMem hz, smul_zero]

/-- Natural compactness internally supplies the actual closed locally convex linear model. -/
theorem exists_closed_supported_linear_model [CompactSpace M] :
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
        ∃ E : GeometricRealForm n M q ≃ S,
          CompleteSpace S ∧ T2Space S ∧ FirstCountableTopology S ∧ LocallyConvexSpace ℝ S ∧
          ∀ (α : SmoothRealForm n M q) i z,
            (E (GeometricRealForm.ofRepresentative α)).val i z =
              (e i).val.target.indicator (fun y => χ i ((e i).val.symm y) • α.coeff (e i) y) z := by
  classical
  obtain ⟨m, e, χ, K, hχ, hnonneg, hs, hK, h1, hJ⟩ :=
    exists_finite_supported_closed_embedding (n := n) (M := M)
  refine ⟨m, e, χ, K, hχ, hnonneg, hs, hK, h1, fun q => ?_⟩
  obtain ⟨J, hinj, hclosed, hcomplete, hread⟩ := hJ q
  let _ := hcomplete
  let S := supportedRange e χ K J hread
  have hS : IsClosed (S : Set (Π i : Fin m,
      𝓓_{K i}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ))) := hclosed
  let E : GeometricRealForm n M q ≃ S := Equiv.ofInjective J hinj
  have hfc : FirstCountableTopology S :=
    firstCountableTopology_induced S
      (Π i : Fin m, 𝓓_{K i}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ))
      (fun v => v.val)
  refine ⟨S, hS, E, hS.completeSpace_coe, inferInstance, hfc, inferInstance, ?_⟩
  intro α i z
  exact hread α i z

end SGPT.Foundations.Analysis.Pending.NaturalCompactGeometricFormLinearModel
