import SGPT.Foundations.Analysis.Pending.NaturalGlobalExteriorDifferential
import SGPT.Foundations.Analysis.Pending.XiaoComplexDifferential

/-!
# Original normalized complex differentials in the genuine global smooth uniformity

The actual real scalar and complex twists factor through original supported
localization. Their continuity and the proved original exterior continuity give
uniform continuity of the literal original normalized dc and ddc quotient maps.
-/

noncomputable section

open Set TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalGeometricComplexDifferentials

open FirstPass ProductTestForms XiaoComplexDifferential NaturalGlobalExteriorDifferential
  NaturalCompactSmoothFormEmbedding NaturalGeometricFormAtlasIndependence

variable {n q m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The literal scalar action on original geometric quotient forms. -/
def geometricScalar (c : ℝ) : GeometricRealForm n M q → GeometricRealForm n M q :=
  Quotient.lift (s := SmoothRealForm.geometricSetoid)
    (fun α => GeometricRealForm.ofRepresentative (c • α)) (by
      intro α β h
      apply Quotient.sound
      intro e z hz
      simp only [coeff_smul, h e hz])

/-- The literal original complex-structure twist on actual geometric forms. -/
def geometricComplexTwist : GeometricRealForm n M q → GeometricRealForm n M q :=
  Quotient.lift (s := SmoothRealForm.geometricSetoid)
    (fun α => GeometricRealForm.ofRepresentative (complexTwist α)) (by
      intro α β h
      apply Quotient.sound
      intro e z hz
      simp only [complexTwist_coeff, h e hz])

/-- Fixed actual tensor postcomposition on original supported products. -/
def productPostcompCLM (K : Fin m → Compacts (ComplexModel n))
    (L : ((ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) →L[ℝ]
      (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) :
    (Π i : Fin m, 𝓓_{K i}(ComplexModel n,
      (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ)) →L[ℝ]
      Π i : Fin m, 𝓓_{K i}(ComplexModel n,
        (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) :=
  ContinuousLinearMap.pi fun i =>
    (ContDiffMapSupportedIn.postcompCLM L).comp (ContinuousLinearMap.proj i)

/-- The actual whole scalar localization factor, including every off-target zero. -/
theorem geometricLocalization_scalar_factor (e : Fin m → ComplexChart n M)
    (χ : Fin m → M → ℝ) (hχ : ∀ i, ChartSmooth (n := n) (χ i))
    (hc : ∀ i, IsCompact (tsupport (χ i))) (hs : ∀ i, tsupport (χ i) ⊆ (e i).val.source)
    (c : ℝ) :
    geometricLocalization (q := q) e χ hχ hc hs ∘ geometricScalar c =
      productPostcompCLM (fun i => chartSupport (e i) (χ i) (hc i) (hs i))
        (c • ContinuousLinearMap.id ℝ _) ∘ geometricLocalization e χ hχ hc hs := by
  funext a
  refine Quotient.inductionOn a ?_
  intro α
  funext i
  apply ContDiffMapSupportedIn.ext
  intro z
  change (e i).val.target.indicator
    (fun y => χ i ((e i).val.symm y) • (c • α).coeff (e i) y) z =
      c • ((e i).val.target.indicator
        (fun y => χ i ((e i).val.symm y) • α.coeff (e i) y) z)
  by_cases hz : z ∈ (e i).val.target
  · simp only [indicator_of_mem hz, coeff_smul]
    exact smul_comm _ _ _
  · simp only [indicator_of_notMem hz, smul_zero]

/-- The actual whole complex-twist localization factor. -/
theorem geometricLocalization_complexTwist_factor (e : Fin m → ComplexChart n M)
    (χ : Fin m → M → ℝ) (hχ : ∀ i, ChartSmooth (n := n) (χ i))
    (hc : ∀ i, IsCompact (tsupport (χ i))) (hs : ∀ i, tsupport (χ i) ⊆ (e i).val.source) :
    geometricLocalization (q := q) e χ hχ hc hs ∘ geometricComplexTwist =
      productPostcompCLM (fun i => chartSupport (e i) (χ i) (hc i) (hs i))
        (ContinuousAlternatingMap.compContinuousLinearMapCLM (modelComplexStructure n)) ∘
          geometricLocalization e χ hχ hc hs := by
  funext a
  refine Quotient.inductionOn a ?_
  intro α
  funext i
  apply ContDiffMapSupportedIn.ext
  intro z
  change (e i).val.target.indicator
    (fun y => χ i ((e i).val.symm y) • (complexTwist α).coeff (e i) y) z =
      ((e i).val.target.indicator
        (fun y => χ i ((e i).val.symm y) • α.coeff (e i) y) z).compContinuousLinearMap
          (modelComplexStructure n)
  by_cases hz : z ∈ (e i).val.target
  · simp only [indicator_of_mem hz, complexTwist_coeff]
    exact ((ContinuousAlternatingMap.compContinuousLinearMapCLM (modelComplexStructure n)).map_smul
      (χ i ((e i).val.symm z)) (α.coeff (e i) z)).symm
  · simp only [indicator_of_notMem hz]
    exact ((ContinuousAlternatingMap.compContinuousLinearMapCLM
      (modelComplexStructure n)).map_zero).symm

private theorem uniformContinuous_of_factor (e : Fin m → ComplexChart n M)
    (χ : Fin m → M → ℝ) (hχ : ∀ i, ChartSmooth (n := n) (χ i))
    (hc : ∀ i, IsCompact (tsupport (χ i))) (hs : ∀ i, tsupport (χ i) ⊆ (e i).val.source)
    (P : GeometricRealForm n M q → GeometricRealForm n M q)
    (B : (Π i : Fin m, 𝓓_{chartSupport (e i) (χ i) (hc i) (hs i)}(ComplexModel n,
      (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ)) →L[ℝ]
        Π i : Fin m, 𝓓_{chartSupport (e i) (χ i) (hc i) (hs i)}(ComplexModel n,
          (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ))
    (hfactor : geometricLocalization e χ hχ hc hs ∘ P =
      B ∘ geometricLocalization e χ hχ hc hs) :
    @UniformContinuous (GeometricRealForm n M q) (GeometricRealForm n M q)
      (localizationUniformity e χ hχ hc hs) (localizationUniformity e χ hχ hc hs) P := by
  have hB := uniformContinuous_iff_le_comap.mp B.uniformContinuous
  have hle := UniformSpace.comap_mono (f := geometricLocalization e χ hχ hc hs) hB
  dsimp only at hle
  rw [← UniformSpace.comap_comap, ← hfactor, UniformSpace.comap_comap] at hle
  exact uniformContinuous_iff_le_comap.mpr hle

/-- Uniform continuity of every literal real scalar action, from its internal factor. -/
theorem geometricScalar_uniformContinuous (e : Fin m → ComplexChart n M)
    (χ : Fin m → M → ℝ) (hχ : ∀ i, ChartSmooth (n := n) (χ i))
    (hc : ∀ i, IsCompact (tsupport (χ i))) (hs : ∀ i, tsupport (χ i) ⊆ (e i).val.source)
    (c : ℝ) :
    @UniformContinuous (GeometricRealForm n M q) (GeometricRealForm n M q)
      (localizationUniformity e χ hχ hc hs) (localizationUniformity e χ hχ hc hs)
        (geometricScalar c) :=
  uniformContinuous_of_factor e χ hχ hc hs (geometricScalar c) _
    (geometricLocalization_scalar_factor e χ hχ hc hs c)

/-- Uniform continuity of the same original quotient complex twist, with internal whole factor. -/
theorem geometricComplexTwist_uniformContinuous (e : Fin m → ComplexChart n M)
    (χ : Fin m → M → ℝ) (hχ : ∀ i, ChartSmooth (n := n) (χ i))
    (hc : ∀ i, IsCompact (tsupport (χ i))) (hs : ∀ i, tsupport (χ i) ⊆ (e i).val.source) :
    @UniformContinuous (GeometricRealForm n M q) (GeometricRealForm n M q)
      (localizationUniformity e χ hχ hc hs) (localizationUniformity e χ hχ hc hs)
        geometricComplexTwist :=
  uniformContinuous_of_factor e χ hχ hc hs geometricComplexTwist _
    (geometricLocalization_complexTwist_factor e χ hχ hc hs)

/-- Descent of the literal original normalized complex differential. -/
def geometricDc : GeometricRealForm n M q → GeometricRealForm n M (q + 1) :=
  Quotient.lift (s := SmoothRealForm.geometricSetoid)
    (fun α => GeometricRealForm.ofRepresentative (dc α))
      (fun _ _ h => Quotient.sound (dc_geometricallyEq h))

/-- Descent of the literal original second normalized differential. -/
def geometricDdc : GeometricRealForm n M q → GeometricRealForm n M (q + 1 + 1) :=
  Quotient.lift (s := SmoothRealForm.geometricSetoid)
    (fun α => GeometricRealForm.ofRepresentative (ddc α))
      (fun _ _ h => Quotient.sound (ddc_geometricallyEq h))

/-- Exact original two-twist normalization, not an unrelated chosen operator. -/
theorem geometricDc_factor : (geometricDc : GeometricRealForm n M q → _) =
    geometricScalar ((-1 : ℝ) ^ (q + 1) / (4 * Real.pi)) ∘ geometricComplexTwist ∘
      geometricExteriorDerivative ∘ geometricComplexTwist := by
  funext a
  refine Quotient.inductionOn a ?_
  intro α
  rfl

/-- Exact original ddc composition on the original quotient. -/
theorem geometricDdc_factor : (geometricDdc : GeometricRealForm n M q → _) =
    geometricExteriorDerivative ∘ geometricDc := by
  funext a
  refine Quotient.inductionOn a ?_
  intro α
  rfl

/-- Uniform continuity of the literal original normalized dc in actual global smooth uniformities. -/
theorem geometricDc_uniformContinuous (e : Fin m → ComplexChart n M)
    (χ : Fin m → M → ℝ) (hχ : ∀ i, ChartSmooth (n := n) (χ i))
    (hc : ∀ i, IsCompact (tsupport (χ i))) (hs : ∀ i, tsupport (χ i) ⊆ (e i).val.source)
    (h1 : ∀ x, ∑ i, χ i x = 1) :
    @UniformContinuous (GeometricRealForm n M q) (GeometricRealForm n M (q + 1))
      (localizationUniformity e χ hχ hc hs) (localizationUniformity e χ hχ hc hs)
        geometricDc := by
  let : UniformSpace (GeometricRealForm n M q) := localizationUniformity e χ hχ hc hs
  let : UniformSpace (GeometricRealForm n M (q + 1)) := localizationUniformity e χ hχ hc hs
  rw [geometricDc_factor]
  exact (geometricScalar_uniformContinuous (q := q + 1) e χ hχ hc hs _).comp
    ((geometricComplexTwist_uniformContinuous (q := q + 1) e χ hχ hc hs).comp
      ((geometricExteriorDerivative_uniformContinuous (q := q) e χ hχ hc hs h1).comp
        (geometricComplexTwist_uniformContinuous (q := q) e χ hχ hc hs)))

/-- Uniform continuity of the same literal original ddc in its original global smooth uniformities. -/
theorem geometricDdc_uniformContinuous (e : Fin m → ComplexChart n M)
    (χ : Fin m → M → ℝ) (hχ : ∀ i, ChartSmooth (n := n) (χ i))
    (hc : ∀ i, IsCompact (tsupport (χ i))) (hs : ∀ i, tsupport (χ i) ⊆ (e i).val.source)
    (h1 : ∀ x, ∑ i, χ i x = 1) :
    @UniformContinuous (GeometricRealForm n M q) (GeometricRealForm n M (q + 1 + 1))
      (localizationUniformity e χ hχ hc hs) (localizationUniformity e χ hχ hc hs)
        geometricDdc := by
  let : UniformSpace (GeometricRealForm n M q) := localizationUniformity e χ hχ hc hs
  let : UniformSpace (GeometricRealForm n M (q + 1)) := localizationUniformity e χ hχ hc hs
  let : UniformSpace (GeometricRealForm n M (q + 1 + 1)) := localizationUniformity e χ hχ hc hs
  rw [geometricDdc_factor]
  exact (geometricExteriorDerivative_uniformContinuous (q := q + 1) e χ hχ hc hs h1).comp
    (geometricDc_uniformContinuous (q := q) e χ hχ hc hs h1)

end SGPT.Foundations.Analysis.Pending.NaturalGeometricComplexDifferentials
