import SGPT.Foundations.Analysis.Pending.NaturalCompactSmoothFormEmbedding
import SGPT.Foundations.Analysis.Pending.NaturalSupportedChartFormExtension

/-!
# Closed supported-coordinate image of actual geometric forms

The actual image is characterized by literal weighted overlap equations.
A finite sum of genuinely zero-extended tensors reconstructs every solution.
No global topology, reconstruction certificate or Green operator is an input.
-/

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalCompactSmoothFormClosedImage

open FirstPass NaturalCompactSmoothFormEmbedding NaturalSupportedChartFormExtension

variable {n q m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Literal continuous weighted overlap equations on the original supported stages. -/
def Compatible (e : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ)
    (K : Fin m → Compacts (ComplexModel n))
    (d : Π i : Fin m, 𝓓_{K i}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ)) : Prop :=
  ∀ i j z, z ∈ (chartTransition (e j) (e i)).source →
    χ j ((e j).val.symm z) • (d i (chartTransition (e j) (e i) z)).compContinuousLinearMap
      (chartTransitionDerivative (e j) (e i) z) =
      χ i ((e j).val.symm z) • d j z

omit [IsComplexManifold n M] in
/-- Closedness is obtained from actual supported evaluation and fixed tensor-pullback continuity. -/
theorem isClosed_compatible (e : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ)
    (K : Fin m → Compacts (ComplexModel n)) :
    IsClosed {d : Π i : Fin m,
      𝓓_{K i}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) | Compatible e χ K d} := by
  simp only [Compatible, ofPred_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun z =>
    isClosed_iInter fun _ => ?_
  have hEval (l : Fin m) (w : ComplexModel n) :
      Continuous (fun d : Π i : Fin m,
        𝓓_{K i}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) => d l w) :=
    (continuous_apply l).eval_const w
  apply isClosed_eq
  · exact ((ContinuousAlternatingMap.compContinuousLinearMapCLM
        (chartTransitionDerivative (e j) (e i) z)).continuous.comp
        (hEval i (chartTransition (e j) (e i) z))).const_smul (χ j ((e j).val.symm z))
  · exact (hEval j z).const_smul (χ i ((e j).val.symm z))

private def sumExtensions (e : Fin m → ComplexChart n M)
    (K : Fin m → Compacts (ComplexModel n))
    (hK : ∀ i, (K i : Set (ComplexModel n)) ⊆ (e i).val.target)
    (d : Π i : Fin m, 𝓓_{K i}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ)) :
    SmoothRealForm n M q where
  coeff := fun f z => ∑ i,
    (extend (e i) (d i) (d i).contDiff (d i).hasCompactSupport.isCompact
      ((d i).tsupport_subset.trans (hK i))).coeff f z
  smooth := fun f => ContDiffOn.sum fun i _ =>
    (extend (e i) (d i) (d i).contDiff (d i).hasCompactSupport.isCompact
      ((d i).tsupport_subset.trans (hK i))).smooth f
  compatible := by
    intro f g z hz v
    simp only [ContinuousAlternatingMap.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact (extend (e i) (d i) (d i).contDiff (d i).hasCompactSupport.isCompact
      ((d i).tsupport_subset.trans (hK i))).compatible f g z hz v

/-- Every solution of the literal closed equations reconstructs an original global smooth form. -/
theorem exists_representative_of_compatible (e : Fin m → ComplexChart n M)
    (χ : Fin m → M → ℝ) (K : Fin m → Compacts (ComplexModel n))
    (hK : ∀ i, (K i : Set (ComplexModel n)) ⊆ (e i).val.target)
    (hs : ∀ i, tsupport (χ i) ⊆ (e i).val.source) (h1 : ∀ x, ∑ i, χ i x = 1)
    (d : Π i : Fin m, 𝓓_{K i}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ))
    (hd : Compatible e χ K d) :
    ∃ α : SmoothRealForm n M q, ∀ j z,
      (e j).val.target.indicator (fun y => χ j ((e j).val.symm y) • α.coeff (e j) y) z = d j z := by
  classical
  refine ⟨sumExtensions e K hK d, fun j z => ?_⟩
  by_cases hz : z ∈ (e j).val.target
  · rw [indicator_of_mem hz]
    let x := (e j).val.symm z
    have heach (i : Fin m) :
        χ j x • (extend (e i) (d i) (d i).contDiff (d i).hasCompactSupport.isCompact
          ((d i).tsupport_subset.trans (hK i))).coeff (e j) z = χ i x • d j z := by
      by_cases hx : x ∈ (e i).val.source
      · have ho : z ∈ (chartTransition (e j) (e i)).source := ⟨hz, hx⟩
        simpa only [extend, transportedCoeff, indicator_of_mem ho] using hd i j z ho
      · have hχ : χ i x = 0 := by
          by_contra h
          exact hx (hs i (subset_tsupport _ h))
        rw [extend_coeff_eq_zero (e i) (e j) (d i) (d i).contDiff
          (d i).hasCompactSupport.isCompact ((d i).tsupport_subset.trans (hK i)) hx,
          hχ, smul_zero, zero_smul]
    change χ j x • (∑ i,
      (extend (e i) (d i) (d i).contDiff (d i).hasCompactSupport.isCompact
        ((d i).tsupport_subset.trans (hK i))).coeff (e j) z) = d j z
    rw [Finset.smul_sum]
    simp only [heach, ← Finset.sum_smul, h1, one_smul]
  · rw [indicator_of_notMem hz]
    exact ((d j).zero_on_compl (fun hzK => hz (hK j hzK))).symm

private theorem compatible_of_readback (e : Fin m → ComplexChart n M)
    (χ : Fin m → M → ℝ) (K : Fin m → Compacts (ComplexModel n))
    (α : SmoothRealForm n M q)
    (d : Π i : Fin m, 𝓓_{K i}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ))
    (hread : ∀ i z, d i z = (e i).val.target.indicator
      (fun y => χ i ((e i).val.symm y) • α.coeff (e i) y) z) : Compatible e χ K d := by
  intro i j z hz
  have ht : chartTransition (e j) (e i) z ∈ (e i).val.target := (e i).val.map_source hz.2
  have hz' : z ∈ (e j).val.target := hz.1
  have hsymm : (e i).val.symm (chartTransition (e j) (e i) z) = (e j).val.symm z :=
    (e i).val.left_inv hz.2
  rw [hread i, hread j, indicator_of_mem ht, indicator_of_mem hz', hsymm]
  ext v
  change χ j ((e j).val.symm z) *
      (χ i ((e j).val.symm z) * α.coeff (e i) (chartTransition (e j) (e i) z)
        (fun l => chartTransitionDerivative (e j) (e i) z (v l))) =
    χ i ((e j).val.symm z) * (χ j ((e j).val.symm z) * α.coeff (e j) z v)
  rw [α.compatible (e j) (e i) z hz v]
  ring

/-- Compactness internally supplies the same faithful original localization with closed image. -/
theorem exists_finite_supported_closed_embedding [CompactSpace M] :
    ∃ (m : ℕ) (e : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ)
      (K : Fin m → Compacts (ComplexModel n)),
      (∀ i, ChartSmooth (n := n) (χ i)) ∧ (∀ i x, 0 ≤ χ i x) ∧
      (∀ i, tsupport (χ i) ⊆ (e i).val.source) ∧
      (∀ i, (K i : Set (ComplexModel n)) = (e i).val '' tsupport (χ i)) ∧
      (∀ x, ∑ i, χ i x = 1) ∧
      ∀ q : ℕ, ∃ J : GeometricRealForm n M q →
        Π i : Fin m, 𝓓_{K i}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ),
        Function.Injective J ∧ IsClosed (range J) ∧
        CompleteSpace (Π i : Fin m,
          𝓓_{K i}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ)) ∧
        ∀ (α : SmoothRealForm n M q) i z,
          J (GeometricRealForm.ofRepresentative α) i z =
            (e i).val.target.indicator (fun y => χ i ((e i).val.symm y) • α.coeff (e i) y) z := by
  classical
  obtain ⟨m, e, χ, K, hχ, hnonneg, hs, hK, h1, hJ⟩ :=
    exists_finite_supported_embedding (n := n) (M := M)
  have hKt (i : Fin m) : (K i : Set (ComplexModel n)) ⊆ (e i).val.target := by
    rw [hK i]
    rintro z ⟨x, hx, rfl⟩
    exact (e i).val.map_source (hs i hx)
  refine ⟨m, e, χ, K, hχ, hnonneg, hs, hK, h1, fun q => ?_⟩
  obtain ⟨J, hinj, hcomplete, hread⟩ := hJ q
  refine ⟨J, hinj, ?_, hcomplete, hread⟩
  have hrange : range J = {d | Compatible e χ K d} := by
    ext d
    constructor
    · rintro ⟨a, rfl⟩
      refine Quotient.inductionOn a ?_
      intro α
      exact compatible_of_readback e χ K α _ (hread α)
    · intro hd
      obtain ⟨α, hα⟩ := exists_representative_of_compatible e χ K hKt hs h1 d hd
      refine ⟨GeometricRealForm.ofRepresentative α, ?_⟩
      funext i
      apply ContDiffMapSupportedIn.ext
      intro z
      rw [hread]
      exact hα i z
  rw [hrange]
  exact isClosed_compatible e χ K

end SGPT.Foundations.Analysis.Pending.NaturalCompactSmoothFormClosedImage
