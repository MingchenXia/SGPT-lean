import SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
import SGPT.Foundations.Analysis.Pending.DivisorialChangeOfVariables
import SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps

/-!
# Pushing weighted integrals down along a modification

Plan `tok/RELGEN2/PLAN.md`, step P5 (blueprint `l2:pushdown`, chapter `claude-tok-l2`).

Let `π : Z → X` be an analytic modification (`IsAnalyticModification`: holomorphic, proper, with
closed nowhere dense analytic sets `A = π⁻¹ B ⊆ Z`, `B ⊆ X` and a holomorphic `s` on `X \ B` with
`π ∘ s = id` off `B`, `s ∘ π = id` off `A`). In charts `e` of `Z` and `d` of `X` write
`F = coordinateMap π e d = d ∘ π ∘ e⁻¹`.

* `complexJacobian_coordinateMap_ne_zero`: `det DF ≠ 0` at the points of `e(Z \ A)`; the chart
  expression of `s` is a holomorphic left inverse of `F` there.
* `injOn_coordinateMap`: `F` is injective off the null set `e(A)` (`volume_chart_image_eq_zero`).
* `lintegral_image_coordinateMap_eq`: `∫_{F(U)} u = ∫_U |J_F|² u ∘ F` for `U` open in the domain.
* `lintegral_multiplierDensity_coordinateMap_le`: the change of variables
  `∫_U |g ∘ F|² |J_F|² e^{-c w ∘ F} ≤ ∫_{F(U)} |g|² e^{-c w}` for `U` open in the domain of `F`
  (TN `DivisorialChangeOfVariables.lintegral_multiplierDensity_comp_le`).
-/

set_option autoImplicit false

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff ENNReal

noncomputable section

namespace SGPT.Okounkov.TranscendentalL2

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DivisorialChangeOfVariables

universe u

variable {n : ℕ} {X Z : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

omit [IsComplexManifold n X] in
/-- The chart image of a closed analytic subset with empty interior is Lebesgue-null. -/
theorem volume_chart_image_eq_zero {A : Set Z} (hA : IsComplexAnalyticSubset (n := n) A)
    (hint : interior A = ∅) (e : ComplexChart n Z) :
    volume (e.val '' (A ∩ e.val.source)) = 0 := by
  have hnull := (ModificationMassInvariance.manifoldLocallyPluripolar_of_isComplexAnalyticSubset
    hA hint).chart_measure_eq_zero e volume
  have heq : e.val '' (A ∩ e.val.source) = pluripolarChartSet A e := by
    ext z
    constructor
    · rintro ⟨y, ⟨hyA, hye⟩, rfl⟩
      exact ⟨e.val.map_source hye, by simpa only [mem_preimage, e.val.left_inv hye] using hyA⟩
    · intro hz
      exact ⟨e.val.symm z, ⟨hz.2, e.val.map_target hz.1⟩, e.val.right_inv hz.1⟩
  rwa [← heq] at hnull

/-- The chart expression of a map which is holomorphic at one point is complex differentiable
there. -/
theorem coordinateMap_differentiableAt_of_contMDiffAt {f : X → Z} (d : ComplexChart n X)
    (e : ComplexChart n Z) {z : ComplexModel n} (hz : z ∈ coordinateDomain f d e)
    (hf : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f (d.val.symm z)) :
    DifferentiableAt ℂ (coordinateMap f d e) z := by
  have h := (contMDiffAt_iff_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas d.property)
    (IsManifold.subset_maximalAtlas e.property)
    (d.val.map_target hz.1) hz.2).mp hf
  have h2 : ContDiffAt ℂ ∞ (coordinateMap f d e) z := by
    simpa [coordinateMap, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm, d.val.right_inv hz.1,
      contDiffWithinAt_univ] using h.2
  exact h2.differentiableAt (by simp)

/-- **The Jacobian of a modification does not vanish off the exceptional set** (plan P5): if
`s` is a holomorphic left inverse of `π` off `A = π⁻¹ B`, then `det D(d ∘ π ∘ e⁻¹) ≠ 0` at `e y`
for every `y ∉ A` in the charts. -/
theorem complexJacobian_coordinateMap_ne_zero {π : Z → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π) {A : Set Z} {B : Set X}
    {s : X → Z} (hAc : IsClosed A) (hBc : IsClosed B) (hpre : π ⁻¹' B = A)
    (hs : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s Bᶜ)
    (hleft : ∀ y ∉ A, s (π y) = y) (e : ComplexChart n Z) (d : ComplexChart n X) {y : Z}
    (hye : y ∈ e.val.source) (hyd : π y ∈ d.val.source) (hyA : y ∉ A) :
    complexJacobian (coordinateMap π e d) (e.val y) ≠ 0 := by
  set F := coordinateMap π e d with hF
  set S := coordinateMap s d e with hS
  have hyB : π y ∉ B := fun h ↦ hyA (hpre ▸ h)
  have hFy : F (e.val y) = d.val (π y) := coordinateMap_at hye
  -- differentiability
  have hFd : DifferentiableAt ℂ F (e.val y) :=
    ((coordinateMap_contDiffAt hπ e d (mem_coordinateDomain hye hyd)).differentiableAt (by simp))
  have hSdom : d.val (π y) ∈ coordinateDomain s d e := by
    refine mem_coordinateDomain hyd ?_
    rw [hleft y hyA]; exact hye
  have hSd : DifferentiableAt ℂ S (d.val (π y)) := by
    refine coordinateMap_differentiableAt_of_contMDiffAt d e hSdom ?_
    rw [d.val.left_inv hyd]
    exact hs.contMDiffAt (hBc.isOpen_compl.mem_nhds hyB)
  -- `S ∘ F = id` near `e y`
  have hO : IsOpen (e.val.target ∩ e.val.symm ⁻¹' (π ⁻¹' d.val.source ∩ Aᶜ)) :=
    e.val.isOpen_inter_preimage_symm ((d.val.open_source.preimage hπ.continuous).inter
      hAc.isOpen_compl)
  have hyO : e.val y ∈ e.val.target ∩ e.val.symm ⁻¹' (π ⁻¹' d.val.source ∩ Aᶜ) := by
    refine ⟨e.val.map_source hye, ?_⟩
    rw [mem_preimage, e.val.left_inv hye]
    exact ⟨hyd, hyA⟩
  have hid : (fun w ↦ S (F w)) =ᶠ[𝓝 (e.val y)] id := by
    filter_upwards [hO.mem_nhds hyO] with w hw
    obtain ⟨hwt, hwd, hwA⟩ := hw
    simp only [hS, hF, coordinateMap, Function.comp_apply, id]
    rw [d.val.left_inv hwd, hleft _ hwA, e.val.right_inv hwt]
  have hSd' : DifferentiableAt ℂ S (F (e.val y)) := hFy ▸ hSd
  have hcomp : HasFDerivAt (fun w ↦ S (F w))
      ((fderiv ℂ S (F (e.val y))).comp (fderiv ℂ F (e.val y))) (e.val y) :=
    hSd'.hasFDerivAt.comp (e.val y) hFd.hasFDerivAt
  have hcid : (fderiv ℂ S (F (e.val y))).comp (fderiv ℂ F (e.val y)) =
      ContinuousLinearMap.id ℂ (ComplexModel n) := by
    have h2 : HasFDerivAt (fun w ↦ S (F w)) (ContinuousLinearMap.id ℂ (ComplexModel n))
        (e.val y) := (hasFDerivAt_id (e.val y)).congr_of_eventuallyEq hid
    exact hcomp.unique h2
  intro hJ
  have hdet := congrArg ContinuousLinearMap.det hcid
  have hlin : (((fderiv ℂ S (F (e.val y))).comp (fderiv ℂ F (e.val y)) :
      ComplexModel n →L[ℂ] ComplexModel n) : ComplexModel n →ₗ[ℂ] ComplexModel n) =
      (fderiv ℂ S (F (e.val y)) : ComplexModel n →ₗ[ℂ] ComplexModel n).comp
        (fderiv ℂ F (e.val y) : ComplexModel n →ₗ[ℂ] ComplexModel n) := rfl
  have hidl : ((ContinuousLinearMap.id ℂ (ComplexModel n) : ComplexModel n →L[ℂ] ComplexModel n) :
      ComplexModel n →ₗ[ℂ] ComplexModel n) = LinearMap.id := rfl
  simp only [ContinuousLinearMap.det] at hdet
  rw [hlin, LinearMap.det_comp, hidl, LinearMap.det_id] at hdet
  have hJ' : LinearMap.det (fderiv ℂ F (e.val y) : ComplexModel n →ₗ[ℂ] ComplexModel n) = 0 := hJ
  rw [hJ', mul_zero] at hdet
  exact zero_ne_one hdet

omit [IsComplexManifold n X] [IsComplexManifold n Z] in
/-- **Injectivity of the chart expression off the exceptional set** (plan P5). -/
theorem injOn_coordinateMap {π : Z → X} {A : Set Z} (hinj : InjOn π Aᶜ)
    (e : ComplexChart n Z) (d : ComplexChart n X) :
    InjOn (coordinateMap π e d) (coordinateDomain π e d \ e.val '' (A ∩ e.val.source)) := by
  intro w hw w' hw' hww'
  have hnotA : ∀ {v}, v ∈ coordinateDomain π e d \ e.val '' (A ∩ e.val.source) →
      e.val.symm v ∉ A := fun {v} hv hvA ↦
    hv.2 ⟨e.val.symm v, ⟨hvA, e.val.map_target hv.1.1⟩, e.val.right_inv hv.1.1⟩
  simp only [coordinateMap, Function.comp_apply] at hww'
  have h1 : π (e.val.symm w) = π (e.val.symm w') :=
    d.val.injOn hw.1.2 hw'.1.2 hww'
  have h2 : e.val.symm w = e.val.symm w' := hinj (hnotA hw) (hnotA hw') h1
  rw [← e.val.right_inv hw.1.1, ← e.val.right_inv hw'.1.1, h2]

/-- **Change of variables along a modification** (plan P5, blueprint `l2:pushdown`): for `U` open
in the domain of `F = d ∘ π ∘ e⁻¹`,
`∫_U |g ∘ F|² |J_F|² e^{-c w ∘ F} ≤ ∫_{F(U)} |g|² e^{-c w}`. -/
theorem lintegral_multiplierDensity_coordinateMap_le {π : Z → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π)
    (e : ComplexChart n Z) (d : ComplexChart n X) {U : Set (ComplexModel n)} (hU : IsOpen U)
    (hUd : U ⊆ coordinateDomain π e d) (w : ComplexModel n → EReal) (c : ℝ)
    (g : ComplexModel n → ℂ) :
    ∫⁻ z in U, multiplierDensity (fun z => w (coordinateMap π e d z)) c
        (fun z => g (coordinateMap π e d z) * complexJacobian (coordinateMap π e d) z) z ≤
      ∫⁻ y in coordinateMap π e d '' U, multiplierDensity w c g y := by
  obtain ⟨A, -, hA, hint, hinj, -⟩ :=
    AnalyticModificationLocalDiscrepancy.exists_analytic_exceptional_set_of_isAnalyticModification
      hπ
  refine lintegral_multiplierDensity_comp_le hU
    ((coordinateMap_contDiffOn hπ.1 e d).differentiableOn (by simp) |>.mono hUd)
    (volume_chart_image_eq_zero hA hint e) ?_ w c g
  exact (injOn_coordinateMap hinj e d).mono (sdiff_subset_sdiff_left hUd)

/-- **Change of variables along a modification, equality form** (plan P5): for `U` open in the
domain of `F = d ∘ π ∘ e⁻¹` and `u ≥ 0`, `∫_{F(U)} u = ∫_U |J_F|² · u ∘ F`. -/
theorem lintegral_image_coordinateMap_eq {π : Z → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π)
    (e : ComplexChart n Z) (d : ComplexChart n X) {U : Set (ComplexModel n)} (hU : IsOpen U)
    (hUd : U ⊆ coordinateDomain π e d) (u : ComplexModel n → ℝ≥0∞) :
    ∫⁻ y in coordinateMap π e d '' U, u y =
      ∫⁻ z in U, ENNReal.ofReal (Complex.normSq (complexJacobian (coordinateMap π e d) z)) *
        u (coordinateMap π e d z) := by
  obtain ⟨A, -, hA, hint, hinj, -⟩ :=
    AnalyticModificationLocalDiscrepancy.exists_analytic_exceptional_set_of_isAnalyticModification
      hπ
  set F := coordinateMap π e d with hF
  set S := toMeasurable volume (e.val '' (A ∩ e.val.source)) with hSdef
  have hS0 : volume S = 0 := by
    rw [hSdef, measure_toMeasurable]; exact volume_chart_image_eq_zero hA hint e
  have hFd : DifferentiableOn ℂ F U :=
    ((coordinateMap_contDiffOn hπ.1 e d).differentiableOn (by simp)).mono hUd
  set s := U \ S with hs
  have hsm : MeasurableSet s := hU.measurableSet.diff (measurableSet_toMeasurable _ _)
  have hinj' : InjOn F s := (injOn_coordinateMap hinj e d).mono
    (sdiff_subset_sdiff hUd (subset_toMeasurable _ _))
  have hderiv : ∀ x ∈ s, HasFDerivWithinAt F ((fderiv ℂ F x).restrictScalars ℝ) s x :=
    fun x hx => ((hFd.differentiableAt (hU.mem_nhds hx.1)).hasFDerivAt.restrictScalars ℝ)
      |>.hasFDerivWithinAt
  have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hsm hderiv hinj' u
  -- the image of the null set `U ∩ S` is null
  have hnull : volume (F '' (U ∩ S)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      ((hFd.mono inter_subset_left).restrictScalars ℝ) (measure_mono_null inter_subset_right hS0)
  have himage : F '' U = F '' s ∪ F '' (U ∩ S) := by
    rw [← image_union, hs, sdiff_union_inter]
  calc ∫⁻ y in F '' U, u y = ∫⁻ y in F '' s, u y := by
        refine setLIntegral_congr ?_
        rw [himage]
        exact union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr hnull)
    _ = ∫⁻ x in s, ENNReal.ofReal |((fderiv ℂ F x).restrictScalars ℝ).det| * u (F x) := hcov
    _ = ∫⁻ x in U, ENNReal.ofReal (Complex.normSq (complexJacobian F x)) * u (F x) := by
        rw [setLIntegral_congr (sdiff_null_ae_eq_self hS0)]
        refine setLIntegral_congr_fun hU.measurableSet fun x _ => ?_
        rw [det_restrictScalars_eq_normSq, abs_of_nonneg (Complex.normSq_nonneg _)]
        rfl

end SGPT.Okounkov.TranscendentalL2
