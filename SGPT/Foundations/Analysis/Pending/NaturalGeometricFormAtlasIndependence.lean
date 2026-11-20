import SGPT.Foundations.Analysis.Pending.NaturalFiniteChartRelocalization
import Mathlib.Topology.UniformSpace.Basic

/-!
# Actual atlas-independent smooth geometric-form uniformity

Whole supported localization descends to the original geometric quotient.
The two internally constructed finite continuous linear comparisons imply
literal equality of comap uniformities, without caller topology or overlap
certificates. No topology is imposed on invisible raw coefficient extensions.
-/

noncomputable section

open Set TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalGeometricFormAtlasIndependence

open FirstPass NaturalCompactSmoothFormEmbedding NaturalFiniteChartRelocalization

variable {n q m l : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Whole supported localization on the original actual geometric quotient. -/
def geometricLocalization (e : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ)
    (hχ : ∀ i, ChartSmooth (n := n) (χ i)) (hc : ∀ i, IsCompact (tsupport (χ i)))
    (hs : ∀ i, tsupport (χ i) ⊆ (e i).val.source) :
    GeometricRealForm n M q →
      Π i : Fin m, 𝓓_{chartSupport (e i) (χ i) (hc i) (hs i)}(ComplexModel n,
        (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) :=
  Quotient.lift (s := SmoothRealForm.geometricSetoid)
    (fun α i => localizedSupported (e i) (χ i) (hχ i) (hc i) (hs i) α)
    (fun _ _ h => funext fun i => localizedSupported_congr
      (e i) (χ i) (hχ i) (hc i) (hs i) h)

/-- The actual quotient uniformity, constructed from original whole local stages. -/
@[instance_reducible] def localizationUniformity (e : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ)
    (hχ : ∀ i, ChartSmooth (n := n) (χ i)) (hc : ∀ i, IsCompact (tsupport (χ i)))
    (hs : ∀ i, tsupport (χ i) ⊆ (e i).val.source) : UniformSpace (GeometricRealForm n M q) :=
  UniformSpace.comap (geometricLocalization e χ hχ hc hs) inferInstance

/-- Exact actual quotient factorization, internally derived from the natural partition. -/
theorem geometricLocalization_factor (e : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ)
    (hχ : ∀ i, ChartSmooth (n := n) (χ i)) (hc : ∀ i, IsCompact (tsupport (χ i)))
    (hs : ∀ i, tsupport (χ i) ⊆ (e i).val.source) (h1 : ∀ x, ∑ i, χ i x = 1)
    (f : Fin l → ComplexChart n M) (ψ : Fin l → M → ℝ)
    (hψ : ∀ j, ChartSmooth (n := n) (ψ j)) (hcψ : ∀ j, IsCompact (tsupport (ψ j)))
    (hsψ : ∀ j, tsupport (ψ j) ⊆ (f j).val.source) :
    geometricLocalization (q := q) f ψ hψ hcψ hsψ =
      relocalizeCLM e χ hc hs f ψ hψ hcψ hsψ ∘ geometricLocalization e χ hχ hc hs := by
  funext a
  refine Quotient.inductionOn a ?_
  intro α
  exact (relocalizeCLM_localized e χ hχ hc hs h1 f ψ hψ hcψ hsψ α).symm

private theorem localizationUniformity_le (e : Fin m → ComplexChart n M)
    (χ : Fin m → M → ℝ) (hχ : ∀ i, ChartSmooth (n := n) (χ i))
    (hc : ∀ i, IsCompact (tsupport (χ i))) (hs : ∀ i, tsupport (χ i) ⊆ (e i).val.source)
    (h1 : ∀ x, ∑ i, χ i x = 1) (f : Fin l → ComplexChart n M) (ψ : Fin l → M → ℝ)
    (hψ : ∀ j, ChartSmooth (n := n) (ψ j)) (hcψ : ∀ j, IsCompact (tsupport (ψ j)))
    (hsψ : ∀ j, tsupport (ψ j) ⊆ (f j).val.source) :
    localizationUniformity (q := q) e χ hχ hc hs ≤ localizationUniformity f ψ hψ hcψ hsψ := by
  let R := relocalizeCLM (q := q) e χ hc hs f ψ hψ hcψ hsψ
  have hR := uniformContinuous_iff_le_comap.mp R.uniformContinuous
  have hle := UniformSpace.comap_mono (f := geometricLocalization e χ hχ hc hs) hR
  dsimp only [R] at hle
  rw [← UniformSpace.comap_comap,
    ← geometricLocalization_factor e χ hχ hc hs h1 f ψ hψ hcψ hsψ] at hle
  exact hle

/-- The genuine smooth geometric-form uniformity is independent of either natural finite atlas. -/
theorem localizationUniformity_eq (e : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ)
    (hχ : ∀ i, ChartSmooth (n := n) (χ i)) (hc : ∀ i, IsCompact (tsupport (χ i)))
    (hs : ∀ i, tsupport (χ i) ⊆ (e i).val.source) (h1 : ∀ x, ∑ i, χ i x = 1)
    (f : Fin l → ComplexChart n M) (ψ : Fin l → M → ℝ)
    (hψ : ∀ j, ChartSmooth (n := n) (ψ j)) (hcψ : ∀ j, IsCompact (tsupport (ψ j)))
    (hsψ : ∀ j, tsupport (ψ j) ⊆ (f j).val.source) (h2 : ∀ x, ∑ j, ψ j x = 1) :
    localizationUniformity (q := q) e χ hχ hc hs = localizationUniformity f ψ hψ hcψ hsψ :=
  le_antisymm (localizationUniformity_le e χ hχ hc hs h1 f ψ hψ hcψ hsψ)
    (localizationUniformity_le f ψ hψ hcψ hsψ h2 e χ hχ hc hs)

end SGPT.Foundations.Analysis.Pending.NaturalGeometricFormAtlasIndependence
