import SGPT.Foundations.Analysis.Pending.NaturalSupportedExteriorDerivative
import SGPT.Foundations.Analysis.Pending.NaturalGeometricFormAtlasIndependence
import SGPT.Foundations.Analysis.FirstPass.ExteriorDerivative

/-!
# Continuity of the actual original geometric exterior differential

Exact derivative transport of original localized fields and their genuine
partition identity give a finite continuous supported-product factorization.
The same original quotient derivative is therefore uniformly continuous in the
actual atlas-independent global smooth uniformity, without caller certificates.
-/

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalGlobalExteriorDifferential

open FirstPass NaturalSupportedExteriorDerivative NaturalCompactSmoothFormEmbedding
  NaturalSupportedChartFormExtension NaturalFiniteChartRelocalization
  NaturalGeometricFormAtlasIndependence ProductTestForms

variable {n q m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The literal original derivative descends through actual geometric equality. -/
def geometricExteriorDerivative : GeometricRealForm n M q → GeometricRealForm n M (q + 1) :=
  Quotient.lift (s := SmoothRealForm.geometricSetoid)
    (fun α => GeometricRealForm.ofRepresentative α.exteriorDerivative)
    (fun _ _ h => Quotient.sound h.exteriorDerivative)

/-- Exact original representative readback, including off-target quotient descent. -/
theorem geometricExteriorDerivative_ofRepresentative (α : SmoothRealForm n M q) :
    geometricExteriorDerivative (GeometricRealForm.ofRepresentative α) =
      GeometricRealForm.ofRepresentative α.exteriorDerivative := rfl

/-- Genuine transported differentiated localized coefficients on every chart target. -/
theorem transported_derivative_localized (e f : ComplexChart n M) (χ : M → ℝ)
    (hχ : ChartSmooth (n := n) χ) (hc : IsCompact (tsupport χ))
    (hs : tsupport χ ⊆ e.val.source) (α : SmoothRealForm n M q)
    {z : ComplexModel n} (hz : z ∈ f.val.target) :
    transportedCoeff e f (extDeriv (localizedSupported e χ hχ hc hs α)) z =
      (smulFun χ hχ α).exteriorDerivative.coeff f z := by
  let τ := smulFun χ hχ α
  by_cases ho : z ∈ (chartTransition f e).source
  · have ht : chartTransition f e z ∈ e.val.target := e.val.map_source ho.2
    have heq : (localizedSupported e χ hχ hc hs α : ComplexModel n →
        (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) =ᶠ[𝓝 (chartTransition f e z)] τ.coeff e := by
      filter_upwards [e.val.open_target.mem_nhds ht] with y hy
      change e.val.target.indicator (fun y => χ (e.val.symm y) • α.coeff e y) y =
        χ (e.val.symm y) • α.coeff e y
      exact indicator_of_mem hy _
    simp only [transportedCoeff, indicator_of_mem ho, heq.extDeriv_eq]
    ext v
    exact (τ.exteriorDerivative.compatible f e z ho v).symm
  · have hx : f.val.symm z ∉ tsupport χ := fun h => ho ⟨hz, hs h⟩
    have hf : ContinuousAt f.val.symm z :=
      f.val.symm.continuousOn.continuousAt (f.val.open_target.mem_nhds hz)
    have hn : ∀ᶠ y in 𝓝 z, f.val.symm y ∉ tsupport χ :=
      hf.eventually ((isClosed_tsupport χ).isOpen_compl.mem_nhds hx)
    have heq : τ.coeff f =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [hn] with y hy
      change χ (f.val.symm y) • α.coeff f y = 0
      rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
    change _ = extDeriv (τ.coeff f) z
    rw [heq.extDeriv_eq]
    simp only [transportedCoeff, indicator_of_notMem ho, extDeriv, fderiv_const_apply]
    simpa only [ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply] using
      (map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ
        (ComplexModel n) ℝ (n := q))).symm

/-- The actual componentwise derivative on the original fixed-support products. -/
def productExteriorDerivativeCLM (K : Fin m → Compacts (ComplexModel n)) :
    (Π i : Fin m, 𝓓_{K i}(ComplexModel n,
      (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ)) →L[ℝ]
      Π i : Fin m, 𝓓_{K i}(ComplexModel n,
        (ComplexModel n) [⋀^Fin (q + 1)]→L[ℝ] ℝ) :=
  ContinuousLinearMap.pi fun i =>
    (stageExteriorDerivativeCLM (K i)).comp (ContinuousLinearMap.proj i)

theorem productExteriorDerivativeCLM_apply (K : Fin m → Compacts (ComplexModel n))
    (A : Π i : Fin m, 𝓓_{K i}(ComplexModel n,
      (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ)) (i : Fin m) (z : ComplexModel n) :
    productExteriorDerivativeCLM K A i z = extDeriv (A i) z :=
  stageExteriorDerivativeCLM_apply (K i) (A i) z

/-- Relocalize the actual componentwise differential in the same natural chart partition. -/
def localizedExteriorDerivativeCLM (e : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ)
    (hχ : ∀ i, ChartSmooth (n := n) (χ i)) (hc : ∀ i, IsCompact (tsupport (χ i)))
    (hs : ∀ i, tsupport (χ i) ⊆ (e i).val.source) :
    (Π i : Fin m, 𝓓_{chartSupport (e i) (χ i) (hc i) (hs i)}(ComplexModel n,
      (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ)) →L[ℝ]
      Π i : Fin m, 𝓓_{chartSupport (e i) (χ i) (hc i) (hs i)}(ComplexModel n,
        (ComplexModel n) [⋀^Fin (q + 1)]→L[ℝ] ℝ) :=
  (relocalizeCLM e χ hc hs e χ hχ hc hs).comp
    (productExteriorDerivativeCLM (fun i => chartSupport (e i) (χ i) (hc i) (hs i)))

/-- Exact whole-field factorization derived from actual cutoff transport and the partition identity. -/
theorem localizedExteriorDerivativeCLM_localized (e : Fin m → ComplexChart n M)
    (χ : Fin m → M → ℝ) (hχ : ∀ i, ChartSmooth (n := n) (χ i))
    (hc : ∀ i, IsCompact (tsupport (χ i))) (hs : ∀ i, tsupport (χ i) ⊆ (e i).val.source)
    (h1 : ∀ x, ∑ i, χ i x = 1) (α : SmoothRealForm n M q) :
    localizedExteriorDerivativeCLM e χ hχ hc hs
      (fun i => localizedSupported (e i) (χ i) (hχ i) (hc i) (hs i) α) =
        fun j => localizedSupported (e j) (χ j) (hχ j) (hc j) (hs j) α.exteriorDerivative := by
  classical
  funext j
  apply ContDiffMapSupportedIn.ext
  intro z
  rw [localizedExteriorDerivativeCLM, ContinuousLinearMap.comp_apply, relocalizeCLM_apply]
  simp only [productExteriorDerivativeCLM_apply]
  change (∑ i, _) = (e j).val.target.indicator
    (fun y => χ j ((e j).val.symm y) • α.exteriorDerivative.coeff (e j) y) z
  by_cases hz : z ∈ (e j).val.target
  · have heach (i : Fin m) :
        (chartTransition (e j) (e i)).source.indicator (fun y =>
          χ j ((e j).val.symm y) •
            (extDeriv (localizedSupported (e i) (χ i) (hχ i) (hc i) (hs i) α)
              (chartTransition (e j) (e i) y)).compContinuousLinearMap
                (chartTransitionDerivative (e j) (e i) y)) z =
        χ j ((e j).val.symm z) • (smulFun (χ i) (hχ i) α).exteriorDerivative.coeff (e j) z := by
      have h := congrArg (fun A => χ j ((e j).val.symm z) • A)
        (transported_derivative_localized (e i) (e j) (χ i) (hχ i) (hc i) (hs i) α hz)
      by_cases ho : z ∈ (chartTransition (e j) (e i)).source
      · simpa only [transportedCoeff, indicator_of_mem ho] using h
      · simpa only [transportedCoeff, indicator_of_notMem ho, smul_zero] using h
    have hfun : α.coeff (e j) =
        fun y => ∑ i, (smulFun (χ i) (hχ i) α).coeff (e j) y := by
      funext y
      simp only [smulFun_coeff, ← Finset.sum_smul, h1, one_smul]
    have hd : α.exteriorDerivative.coeff (e j) z =
        ∑ i, (smulFun (χ i) (hχ i) α).exteriorDerivative.coeff (e j) z := by
      change ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ (α.coeff (e j)) z) =
        ∑ i, ContinuousAlternatingMap.alternatizeUncurryFin
          (fderiv ℝ ((smulFun (χ i) (hχ i) α).coeff (e j)) z)
      rw [hfun, fderiv_fun_sum fun i _ =>
        (((smulFun (χ i) (hχ i) α).smooth (e j)).contDiffAt
          ((e j).val.open_target.mem_nhds hz)).differentiableAt (by simp)]
      exact map_sum (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ
        (ComplexModel n) ℝ) _ _
    rw [Finset.sum_congr rfl (fun i _ => heach i), indicator_of_mem hz, ← Finset.smul_sum, hd]
  · rw [indicator_of_notMem hz]
    apply Finset.sum_eq_zero
    intro i _
    exact indicator_of_notMem (fun h => hz h.1) _

/-- Exact original quotient factorization of exterior differentiation. -/
theorem geometricLocalization_exteriorDerivative_factor (e : Fin m → ComplexChart n M)
    (χ : Fin m → M → ℝ) (hχ : ∀ i, ChartSmooth (n := n) (χ i))
    (hc : ∀ i, IsCompact (tsupport (χ i))) (hs : ∀ i, tsupport (χ i) ⊆ (e i).val.source)
    (h1 : ∀ x, ∑ i, χ i x = 1) :
    geometricLocalization (q := q + 1) e χ hχ hc hs ∘ geometricExteriorDerivative =
      localizedExteriorDerivativeCLM (q := q) e χ hχ hc hs ∘
        geometricLocalization e χ hχ hc hs := by
  funext a
  refine Quotient.inductionOn a ?_
  intro α
  exact (localizedExteriorDerivativeCLM_localized e χ hχ hc hs h1 α).symm

/-- Uniform continuity of the actual original derivative in the genuine global all-jet uniformities. -/
theorem geometricExteriorDerivative_uniformContinuous (e : Fin m → ComplexChart n M)
    (χ : Fin m → M → ℝ) (hχ : ∀ i, ChartSmooth (n := n) (χ i))
    (hc : ∀ i, IsCompact (tsupport (χ i))) (hs : ∀ i, tsupport (χ i) ⊆ (e i).val.source)
    (h1 : ∀ x, ∑ i, χ i x = 1) :
    @UniformContinuous (GeometricRealForm n M q) (GeometricRealForm n M (q + 1))
      (localizationUniformity e χ hχ hc hs) (localizationUniformity e χ hχ hc hs)
        geometricExteriorDerivative := by
  let B := localizedExteriorDerivativeCLM (q := q) e χ hχ hc hs
  have hB := uniformContinuous_iff_le_comap.mp B.uniformContinuous
  have hle := UniformSpace.comap_mono (f := geometricLocalization e χ hχ hc hs) hB
  dsimp only [B] at hle
  rw [← UniformSpace.comap_comap,
    ← geometricLocalization_exteriorDerivative_factor e χ hχ hc hs h1] at hle
  rw [UniformSpace.comap_comap] at hle
  exact uniformContinuous_iff_le_comap.mpr hle

end SGPT.Foundations.Analysis.Pending.NaturalGlobalExteriorDifferential
