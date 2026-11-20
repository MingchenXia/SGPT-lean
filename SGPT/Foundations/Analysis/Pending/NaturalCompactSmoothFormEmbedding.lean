import SGPT.Foundations.Analysis.Pending.NaturalSupportedSmoothCompleteness
import SGPT.Foundations.Analysis.Pending.ActualWeightedGlobalFormChartTests
import SGPT.Foundations.Analysis.Pending.ChartPartition
import SGPT.Foundations.Analysis.FirstPass.GeometricForms

/-!
# Faithful finite supported coordinates of original geometric forms

Compactness internally supplies one original finite chart partition, before all degrees.
The actual whole localized coefficient maps embed the original geometric quotient faithfully
into complete compact-support smooth stages. Closed global image and Green theory remain separate.
-/

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalCompactSmoothFormEmbedding

open FirstPass ChartPartition ActualWeightedGlobalFormChartTests

variable {n q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual compact model image of the original cutoff support. -/
def chartSupport (e : ComplexChart n M) (χ : M → ℝ)
    (hc : IsCompact (tsupport χ)) (hs : tsupport χ ⊆ e.val.source) :
    Compacts (ComplexModel n) :=
  ⟨e.val '' tsupport χ, hc.image_of_continuousOn (e.val.continuousOn.mono hs)⟩

/-- The whole original weighted coefficient, as an actual fixed-support smooth map. -/
def localizedSupported (e : ComplexChart n M) (χ : M → ℝ)
    (hχ : ChartSmooth (n := n) χ) (hc : IsCompact (tsupport χ))
    (hs : tsupport χ ⊆ e.val.source) (α : SmoothRealForm n M q) :
    𝓓_{chartSupport e χ hc hs}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) where
  toFun := e.val.target.indicator (fun z => χ (e.val.symm z) • α.coeff e z)
  contDiff' := by
    obtain ⟨η, hη, -⟩ := exists_testForm e α χ hχ hc hs
    have hfun : (η : ComplexModel n → (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) =
        e.val.target.indicator (fun z => χ (e.val.symm z) • α.coeff e z) := funext hη
    rw [← hfun]
    exact η.contDiff
  zero_on_compl' := by
    obtain ⟨η, hη, hK⟩ := exists_testForm e α χ hχ hc hs
    intro z hz
    have hz' : z ∉ tsupport (η : ComplexModel n → (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) :=
      fun h => hz (hK h)
    rw [← hη z]
    exact image_eq_zero_of_notMem_tsupport hz'

private theorem localizedSupported_apply (e : ComplexChart n M) (χ : M → ℝ)
    (hχ : ChartSmooth (n := n) χ) (hc : IsCompact (tsupport χ))
    (hs : tsupport χ ⊆ e.val.source) (α : SmoothRealForm n M q) (z : ComplexModel n) :
    localizedSupported e χ hχ hc hs α z =
      e.val.target.indicator (fun y => χ (e.val.symm y) • α.coeff e y) z := rfl

/-- Localization ignores every arbitrary off-target extension of the representative. -/
theorem localizedSupported_congr (e : ComplexChart n M) (χ : M → ℝ)
    (hχ : ChartSmooth (n := n) χ) (hc : IsCompact (tsupport χ))
    (hs : tsupport χ ⊆ e.val.source) {α β : SmoothRealForm n M q}
    (h : α.GeometricallyEq β) :
    localizedSupported e χ hχ hc hs α = localizedSupported e χ hχ hc hs β := by
  apply ContDiffMapSupportedIn.ext
  intro z
  rw [localizedSupported_apply, localizedSupported_apply]
  by_cases hz : z ∈ e.val.target
  · simp only [indicator_of_mem hz, h e hz]
  · simp only [indicator_of_notMem hz]

private theorem geometricallyEq_of_localized {m : ℕ}
    (e : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ)
    (hχ : ∀ i, ChartSmooth (n := n) (χ i)) (hc : ∀ i, IsCompact (tsupport (χ i)))
    (hs : ∀ i, tsupport (χ i) ⊆ (e i).val.source) (h1 : ∀ x, ∑ i, χ i x = 1)
    {α β : SmoothRealForm n M q}
    (h : ∀ i, localizedSupported (e i) (χ i) (hχ i) (hc i) (hs i) α =
      localizedSupported (e i) (χ i) (hχ i) (hc i) (hs i) β) :
    α.GeometricallyEq β := by
  classical
  apply SmoothRealForm.geometricallyEq_iff.mpr
  intro f z hz v
  let x := f.val.symm z
  have hweighted (i : Fin m) :
      χ i x * α.coeff f z v = χ i x * β.coeff f z v := by
    by_cases hzero : χ i x = 0
    · simp only [hzero, zero_mul]
    · have hxi : x ∈ (e i).val.source := hs i (subset_tsupport _ hzero)
      have ht : z ∈ (chartTransition f (e i)).source := ⟨hz, hxi⟩
      let w : Fin q → ComplexModel n := fun j => chartTransitionDerivative f (e i) z (v j)
      have hr := congrArg (fun t => t ((e i).val x) w) (h i)
      rw [localizedSupported_apply, localizedSupported_apply,
        indicator_of_mem ((e i).val.map_source hxi),
        indicator_of_mem ((e i).val.map_source hxi)] at hr
      rw [(e i).val.left_inv hxi] at hr
      rw [α.compatible f (e i) z ht v, β.compatible f (e i) z ht v]
      exact hr
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl fun i _ => hweighted i
  simpa only [← Finset.sum_mul, h1, one_mul] using hsum

/-- Compactness supplies one faithful family of genuine completed local stages before all degrees. -/
theorem exists_finite_supported_embedding [CompactSpace M] :
    ∃ (m : ℕ) (e : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ)
      (K : Fin m → Compacts (ComplexModel n)),
      (∀ i, ChartSmooth (n := n) (χ i)) ∧ (∀ i x, 0 ≤ χ i x) ∧
      (∀ i, tsupport (χ i) ⊆ (e i).val.source) ∧
      (∀ i, (K i : Set (ComplexModel n)) = (e i).val '' tsupport (χ i)) ∧
      (∀ x, ∑ i, χ i x = 1) ∧
      ∀ q : ℕ, ∃ J : GeometricRealForm n M q →
        Π i : Fin m, 𝓓_{K i}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ),
        Function.Injective J ∧
        CompleteSpace (Π i : Fin m,
          𝓓_{K i}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ)) ∧
        ∀ (α : SmoothRealForm n M q) i z,
          J (GeometricRealForm.ofRepresentative α) i z =
            (e i).val.target.indicator (fun y => χ i ((e i).val.symm y) • α.coeff (e i) y) z := by
  classical
  obtain ⟨m, χ, idx, hχ, hnonneg, hs, hc, h1⟩ :=
    exists_chartSmooth_partitionOfUnity (n := n)
      (fun x : M => (⟨(complexChartAt (n := n) x).val.source,
        (complexChartAt (n := n) x).val.open_source⟩ : Opens M))
      (fun x => ⟨x, mem_complexChartAt_source x⟩)
  let e : Fin m → ComplexChart n M := fun i => complexChartAt (idx i)
  let K : Fin m → Compacts (ComplexModel n) := fun i => chartSupport (e i) (χ i) (hc i) (hs i)
  refine ⟨m, e, χ, K, hχ, hnonneg, hs, fun _ => rfl, h1, fun q => ?_⟩
  let J : GeometricRealForm n M q →
      Π i : Fin m, 𝓓_{K i}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) :=
    Quotient.lift (s := SmoothRealForm.geometricSetoid)
      (fun α i => localizedSupported (e i) (χ i) (hχ i) (hc i) (hs i) α)
      (fun α β h => funext fun i => localizedSupported_congr (e i) (χ i) (hχ i) (hc i) (hs i) h)
  refine ⟨J, ?_, inferInstance, ?_⟩
  · intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro α β heq
    apply Quotient.sound
    exact geometricallyEq_of_localized e χ hχ hc hs h1 (fun i => congrFun heq i)
  · intro α i z
    exact localizedSupported_apply (e i) (χ i) (hχ i) (hc i) (hs i) α z

end SGPT.Foundations.Analysis.Pending.NaturalCompactSmoothFormEmbedding
