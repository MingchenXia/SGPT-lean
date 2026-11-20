import SGPT.Okounkov.TranscendentalWNConv6Outer
import SGPT.Okounkov.TranscendentalWNConv6ChangeVar
import SGPT.Okounkov.TranscendentalWNConv6Algebra
import SGPT.Okounkov.TranscendentalWNConv6LineMeasure
import SGPT.Foundations.Analysis.Pending.ModificationMassInvariance
import SGPT.Foundations.Analysis.Pending.HolomorphicLocalInverse
import SGPT.Foundations.Analysis.Pending.CoordinateDensityLowDim
import SGPT.Foundations.Analysis.FirstPass.HolomorphicDDC
import SGPT.Foundations.Analysis.FirstPass.CoordinateWedgePullback
import SGPT.Foundations.Analysis.FirstPass.GlobalPotentialTransforms

/-!
# Product coordinates on `𝒳 \ (X₀ ∪ X_∞)` and the density bound

Blueprint `tok-wn-conv6:inner-density` and `tok-wn-conv6:inner` (chapter `claude-tok-wn-conv6`);
source WN21, proof of Proposition 6.4.

* `MCData.inv`: the inverse of `μ` over `X × ℙ¹ \ Z × {0}`, holomorphic there
  (`contMDiffAt_inv`, from TN's local holomorphic inverses of a blow-up off its exceptional
  locus), with `inv (x, [τ : 1]) = s_τ(x)` (`inv_affine`).
* `MCData.coord e`: `y = (z, w) ↦ inv (e⁻¹ z, [w : 1])` on `U_e = {z ∈ e.target, w ≠ 0}`
  (`coordDomain`), an injective holomorphic parametrization (`differentiableAt_coord`,
  `injOn_coord`).
* In these coordinates (read in any chart `f` of `𝒳`): `g_k ∘ coord = G_k ∘ p₂` with
  `G_k = χ(log |w|² + k) - k - log(1 + |w|²)`, so `coord^*(ddᶜ g_k) = p₂^* ddᶜG_k`
  (`chartPull_ddc_obstacle`); `ι^* coord^* θ̃ = s_τ^*θ̃` in the chart `e` (`chartPull_comp_inclFst`).
* `topDensity_chartPull_le` (`tok-wn-conv6:inner-density`): at a point of `D_k`,
  `(θ̃ + ddᶜg_k)^{n+1} ≤ θ̃^{n+1} + (n + 1) (s_τ^*θ̃)ⁿ · ω_k` as densities.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Foundations.Analysis.Pending.ProductMixedMeasure
open SGPT.Foundations.Analysis.Pending.TopDegreeDensity
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Toric
open SGPT.Okounkov.TranscendentalMain

theorem chart_false_symm_eq (w : ComplexModel 1) :
    (projectiveModelChart false).symm w = affineLinePoint (w 0) := by
  rw [projectiveModelChart_symm_eq_mk, affineLinePoint_eq_mk]
  congr 1

/-- `G_k = χ(log |w|² + k) - k - log(1 + |w|²)`, the obstacle in the affine chart. -/
def lineObstacle (χ : ℝ → ℝ) (k : ℕ) (w : ComplexModel 1) : ℝ :=
  cutoffLineProfile χ k w - k - projectiveFSPotential w

theorem contDiff_lineObstacle {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) (k : ℕ) :
    ContDiff ℝ ∞ (lineObstacle χ k) :=
  ((contDiff_cutoffLineProfile hχ k).sub contDiff_const).sub contDiff_projectiveFSPotential

theorem projectiveModelChart_target_eq (b : Bool) : (projectiveModelChart b).target = univ := by
  rw [projectiveModelChart, OpenPartialHomeomorph.trans_target, projectiveQuotientScalarChart_target]
  simp

theorem two_le_top' : ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl 2

/-- The density of `ddᶜG_k` is the density of `ω_k` minus that of `ω_FS`. -/
theorem actualTopPowerDensity_lineObstacle {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) (k : ℕ)
    (w : ComplexModel 1) :
    actualTopPowerDensity (smoothDDC (lineObstacle χ k) w) =
      cutoffLineDensity χ k w - smoothDensity projectiveFSPotential w := by
  have hΛ := (contDiff_cutoffLineProfile hχ k).contDiffOn (s := univ)
  have hFS := contDiff_projectiveFSPotential.contDiffOn (s := univ)
  have hc : ContDiffOn ℝ ∞ (fun _ : ComplexModel 1 => (k : ℝ)) univ := contDiffOn_const
  have e1 : smoothDDC (lineObstacle χ k) w =
      smoothDDC (fun y => cutoffLineProfile χ k y - (k : ℝ)) w - smoothDDC projectiveFSPotential w :=
    smoothDDC_sub (h := fun y => cutoffLineProfile χ k y - (k : ℝ)) (f := projectiveFSPotential)
      isOpen_univ (hΛ.sub hc) hFS (mem_univ w)
  have e2 : smoothDDC (fun y => cutoffLineProfile χ k y - (k : ℝ)) w =
      smoothDDC (cutoffLineProfile χ k) w := by
    rw [smoothDDC_sub (h := cutoffLineProfile χ k) (f := fun _ => (k : ℝ)) isOpen_univ hΛ hc
      (mem_univ w), GlobalPotentialTransforms.smoothDDC_const, sub_zero]
  rw [e1, e2, actualTopPowerDensity_one, ContinuousAlternatingMap.sub_apply,
    ← actualTopPowerDensity_one, ← actualTopPowerDensity_one,
    actualTopPowerDensity_eq_normalizedTopPowerDensity_one,
    actualTopPowerDensity_eq_normalizedTopPowerDensity_one,
    normalizedTopPowerDensity_smoothDDC ((contDiff_cutoffLineProfile hχ k).contDiffAt.of_le
      two_le_top'),
    normalizedTopPowerDensity_smoothDDC (contDiff_projectiveFSPotential.contDiffAt.of_le
      two_le_top')]
  rfl

theorem coordinateVector_zero_ne : (coordinateVector (0 : Fin 1) : ComplexModel 1) ≠ 0 := by
  intro h
  have := congrArg (fun v : ComplexModel 1 => v 0) h
  simp [coordinateVector] at this

theorem smoothDensity_projectiveFSPotential_nonneg (w : ComplexModel 1) :
    0 ≤ smoothDensity projectiveFSPotential w := by
  rw [← normalizedTopPowerDensity_smoothDDC (contDiff_projectiveFSPotential.contDiffAt.of_le
      two_le_top'), ← actualTopPowerDensity_eq_normalizedTopPowerDensity_one,
    actualTopPowerDensity_one]
  have h := projectiveNativeFSForm_isKahler.1 (projectiveNativeChart false) w
    (by rw [projectiveNativeChart_val, projectiveModelChart_target_eq]; exact mem_univ w)
  exact (h.2 _ coordinateVector_zero_ne).le

theorem affine_notMem_deformationCentre {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1)) {τ : ℂ}
    (hτ : τ ≠ 0) (x : F.carrier) : (x, affineLinePoint τ) ∉ deformationCentre F := fun h =>
  affineLinePoint_ne_projectiveZero hτ ((mem_deformationCentre_iff F).mp h).2

section Coordinates

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}



/-- The product chart of `X × ℙ¹` (a chart `e` of `X` and the affine chart of `ℙ¹`). -/
def pchart (e : ComplexChart (m + 1) F.carrier) :
    ComplexChart (m + 1 + 1) (F.carrier × ProjectiveLine) :=
  prodComplexChart e (projectiveNativeChart false)

/-- `(z, w)` of `y ∈ ℂⁿ⁺¹`. -/
def zc (y : ComplexModel (m + 1 + 1)) : ComplexModel (m + 1) := ((prodModelEquiv (m + 1) 1).symm y).1

def wc (y : ComplexModel (m + 1 + 1)) : ComplexModel 1 := ((prodModelEquiv (m + 1) 1).symm y).2

/-- `U_e = {z ∈ e.target, w ≠ 0}`. -/
def coordDomain (e : ComplexChart (m + 1) F.carrier) : Set (ComplexModel (m + 1 + 1)) :=
  {y | zc y ∈ e.val.target ∧ wc y 0 ≠ 0}

theorem pchart_symm (e : ComplexChart (m + 1) F.carrier) (y : ComplexModel (m + 1 + 1)) :
    (pchart e).val.symm y = (e.val.symm (zc y), affineLinePoint (wc y 0)) := by
  rw [pchart, prodComplexChart_val, prodChart_symm_apply]
  simp only [zc, wc, projectiveNativeChart_val, chart_false_symm_eq]

theorem isOpen_coordDomain (e : ComplexChart (m + 1) F.carrier) : IsOpen (coordDomain e) := by
  have hz : Continuous (zc (m := m)) := continuous_fst.comp (prodModelEquiv (m + 1) 1).symm.continuous
  have hw : Continuous fun y : ComplexModel (m + 1 + 1) => wc y 0 :=
    (EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).continuous.comp
      (continuous_snd.comp (prodModelEquiv (m + 1) 1).symm.continuous)
  exact (e.val.open_target.preimage hz).inter (isOpen_ne_fun hw continuous_const)

theorem mem_pchart_target {e : ComplexChart (m + 1) F.carrier} {y : ComplexModel (m + 1 + 1)}
    (hy : y ∈ coordDomain e) : y ∈ (pchart e).val.target := by
  rw [pchart, prodComplexChart_val, prodChart_target]
  refine ⟨hy.1, ?_⟩
  rw [projectiveNativeChart_val, projectiveModelChart_target_eq]
  exact mem_univ _

theorem pchart_symm_notMem {e : ComplexChart (m + 1) F.carrier} {y : ComplexModel (m + 1 + 1)}
    (hy : y ∈ coordDomain e) : (pchart e).val.symm y ∉ deformationCentre F := by
  rw [pchart_symm]; exact affine_notMem_deformationCentre F hy.2 _


end Coordinates

namespace MCData

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)} {𝒳 : Type u} [TopologicalSpace 𝒳]
  [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳] [IsComplexManifold (m + 1 + 1) 𝒳]
  (D : MCData F 𝒳) [Nonempty 𝒳]

/-- The inverse of `μ` over `X × ℙ¹ \ Z × {0}`. -/
def inv : F.carrier × ProjectiveLine → 𝒳 :=
  ModificationMassInvariance.invOver D.μ (deformationCentre F)ᶜ

theorem μ_inv {q : F.carrier × ProjectiveLine} (hq : q ∉ deformationCentre F) :
    D.μ (D.inv q) = q :=
  (ModificationMassInvariance.invOver_mem (isIsomorphismOver_normalCone F D.hμ) hq).2

theorem inv_μ {z : 𝒳} (hz : D.μ z ∉ deformationCentre F) : D.inv (D.μ z) = z :=
  ModificationMassInvariance.invOver_apply (isIsomorphismOver_normalCone F D.hμ) hz

theorem contMDiffAt_inv {q : F.carrier × ProjectiveLine} (hq : q ∉ deformationCentre F) :
    ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ D.inv q := by
  have hiso := isIsomorphismOver_normalCone F D.hμ
  obtain ⟨hyN, hyx⟩ := ModificationMassInvariance.invOver_mem hiso hq
  have hexc : D.inv q ∉ exceptionalLocus (m + 1 + 1) D.μ := fun h =>
    Set.disjoint_left.mp hiso.2 hyN h
  obtain ⟨V, s, hV, hxV, -, hπs, hsmooth, -⟩ :=
    HolomorphicLocalInverse.exists_localInverse D.hμ.contMDiff hexc
  have hxV' : q ∈ V := by
    have : D.μ (D.inv q) = q := hyx
    rwa [this] at hxV
  have hN : IsOpen (deformationCentre F)ᶜ := (isClosed_deformationCentre F).isOpen_compl
  have heq : s =ᶠ[𝓝 q] D.inv := by
    filter_upwards [hV.mem_nhds hxV', hN.mem_nhds hq] with x' hx'V hx'N
    have h1 : D.μ (s x') = x' := hπs x' hx'V
    have h2 : s x' ∈ D.μ ⁻¹' (deformationCentre F)ᶜ := by rw [mem_preimage, h1]; exact hx'N
    calc s x' = D.inv (D.μ (s x')) := (ModificationMassInvariance.invOver_apply hiso h2).symm
      _ = D.inv x' := by rw [h1]
  exact (hsmooth q hxV').congr_of_eventuallyEq heq.symm

omit [Nonempty 𝒳] in
theorem sec_congr {τ τ' : ℂ} (h : τ = τ') (hτ : τ ≠ 0) (hτ' : τ' ≠ 0) : D.sec hτ = D.sec hτ' := by
  subst h; rfl

theorem inv_affine {τ : ℂ} (hτ : τ ≠ 0) (x : F.carrier) :
    D.inv (x, affineLinePoint τ) = D.sec hτ x := by
  rw [← D.μ_sec hτ x, D.inv_μ (by rw [D.μ_sec hτ x]; exact affine_notMem_deformationCentre F hτ x)]

/-- `coord e (z, w) = inv (e⁻¹ z, [w : 1]) = s_w(e⁻¹ z)`. -/
def coord (e : ComplexChart (m + 1) F.carrier) (y : ComplexModel (m + 1 + 1)) : 𝒳 :=
  D.inv ((pchart e).val.symm y)

theorem coord_eq_sec {e : ComplexChart (m + 1) F.carrier} {y : ComplexModel (m + 1 + 1)}
    (hy : y ∈ coordDomain e) : D.coord e y = D.sec hy.2 (e.val.symm (zc y)) := by
  rw [coord, pchart_symm, D.inv_affine]

theorem μ_coord {e : ComplexChart (m + 1) F.carrier} {y : ComplexModel (m + 1 + 1)}
    (hy : y ∈ coordDomain e) : D.μ (D.coord e y) = (e.val.symm (zc y), affineLinePoint (wc y 0)) := by
  rw [coord, D.μ_inv (pchart_symm_notMem hy), pchart_symm]

theorem contMDiffAt_coord {e : ComplexChart (m + 1) F.carrier} {y : ComplexModel (m + 1 + 1)}
    (hy : y ∈ coordDomain e) :
    ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ (D.coord e) y :=
  (D.contMDiffAt_inv (pchart_symm_notMem hy)).comp y
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (pchart e).property)
      (mem_pchart_target hy))

theorem continuousOn_coord (e : ComplexChart (m + 1) F.carrier) :
    ContinuousOn (D.coord e) (coordDomain e) := fun _ hy =>
  (D.contMDiffAt_coord hy).continuousAt.continuousWithinAt

theorem differentiableAt_coord {e : ComplexChart (m + 1) F.carrier} (f : ComplexChart (m + 1 + 1) 𝒳)
    {y : ComplexModel (m + 1 + 1)} (hy : y ∈ coordDomain e) (hf : D.coord e y ∈ f.val.source) :
    DifferentiableAt ℂ (fun y' => f.val (D.coord e y')) y := by
  have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ f.val
      (D.coord e y) :=
    (contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas f.property)).contMDiffAt
      (f.val.open_source.mem_nhds hf)
  have h2 := contMDiffAt_iff_contDiffAt.mp (h1.comp y (D.contMDiffAt_coord hy))
  exact h2.differentiableAt (by simp)

theorem injOn_coord (e : ComplexChart (m + 1) F.carrier) : InjOn (D.coord e) (coordDomain e) := by
  intro a ha b hb hab
  have h := congrArg D.μ hab
  rw [coord, coord, D.μ_inv (pchart_symm_notMem ha), D.μ_inv (pchart_symm_notMem hb)] at h
  have := congrArg (pchart e).val h
  rwa [(pchart e).val.right_inv (mem_pchart_target ha),
    (pchart e).val.right_inv (mem_pchart_target hb)] at this

theorem contDiffAt_coord_chart {e : ComplexChart (m + 1) F.carrier} (f : ComplexChart (m + 1 + 1) 𝒳)
    {y : ComplexModel (m + 1 + 1)} (hy : y ∈ coordDomain e) (hf : D.coord e y ∈ f.val.source) :
    ContDiffAt ℂ ∞ (fun y' => f.val (D.coord e y')) y := by
  have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ f.val
      (D.coord e y) :=
    (contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas f.property)).contMDiffAt
      (f.val.open_source.mem_nhds hf)
  exact contMDiffAt_iff_contDiffAt.mp (h1.comp y (D.contMDiffAt_coord hy))

/-- **`g_k ∘ coord = G_k ∘ p₂`.** -/
theorem obstacle_coord {e : ComplexChart (m + 1) F.carrier} {y : ComplexModel (m + 1 + 1)}
    (hy : y ∈ coordDomain e) (k : ℕ) :
    D.obstacle k (D.coord e y) = lineObstacle D.χ k (wc y) := by
  rw [obstacle, cutoffObstacle, D.μ_coord hy, ← chart_false_symm_eq, cutoffObstacleLine_chart_false]
  rfl

theorem wc_eq_projSnd : (wc (m := m)) = ⇑(projSnd (m + 1) 1) := rfl

/-- **`coord^*(ddᶜ g_k) = p₂^* ddᶜG_k`**, in any chart `f`. -/
theorem chartPull_ddc_obstacle {e : ComplexChart (m + 1) F.carrier} (f : ComplexChart (m + 1 + 1) 𝒳)
    {y : ComplexModel (m + 1 + 1)} (hy : y ∈ coordDomain e) (hf : D.coord e y ∈ f.val.source)
    (k : ℕ) :
    ChangeVar.chartPull (ddcClosedForm (D.obstacle k) (D.chartSmooth_obstacle k)).val (D.coord e) f y =
      (smoothDDC (lineObstacle D.χ k) (wc y)).compContinuousLinearMap (projSnd (m + 1) 1) := by
  unfold ChangeVar.chartPull
  rw [ddcClosedForm_coeff]
  set V := coordDomain e ∩ D.coord e ⁻¹' f.val.source with hV
  have hVo : IsOpen V := (D.continuousOn_coord e).isOpen_inter_preimage (isOpen_coordDomain e)
    f.val.open_source
  have hyV : y ∈ V := ⟨hy, hf⟩
  have hFd : ContDiffOn ℂ ∞ (fun y' => f.val (D.coord e y')) V := fun y' hy' =>
    (D.contDiffAt_coord_chart f hy'.1 hy'.2).contDiffWithinAt
  have hρ : ContDiffOn ℝ ∞ (fun z => D.obstacle k (f.val.symm z)) f.val.target :=
    D.chartSmooth_obstacle k f
  have hmaps : MapsTo (fun y' => f.val (D.coord e y')) V f.val.target := fun y' hy' =>
    f.val.map_source hy'.2
  rw [← HolomorphicDDC.smoothDDC_comp hVo f.val.open_target hFd hρ hmaps hyV]
  have hev : (fun y' => D.obstacle k (f.val.symm (f.val (D.coord e y')))) =ᶠ[𝓝 y]
      fun y' => lineObstacle D.χ k (wc y') := by
    filter_upwards [hVo.mem_nhds hyV] with y' hy'
    rw [f.val.left_inv hy'.2, D.obstacle_coord hy'.1]
  rw [smoothDDC_congr hev]
  have hP : ContDiffOn ℂ ∞ (wc (m := m)) univ :=
    ((ContinuousLinearMap.snd ℂ (ComplexModel (m + 1)) (ComplexModel 1)).comp
      ((prodModelEquiv (m + 1) 1).symm : ComplexModel (m + 1 + 1) →L[ℂ] _)).contDiff.contDiffOn
  rw [HolomorphicDDC.smoothDDC_comp isOpen_univ isOpen_univ hP
    (contDiff_lineObstacle D.hχ k).contDiffOn (mapsTo_univ _ _) (mem_univ y), wc_eq_projSnd,
    ContinuousLinearMap.fderiv]

omit [Nonempty 𝒳] in
theorem chartPull_add {φ : ComplexModel (m + 1 + 1) → 𝒳} (α β : ClosedRealOneOneForm (m + 1 + 1) 𝒳)
    (f : ComplexChart (m + 1 + 1) 𝒳) (y : ComplexModel (m + 1 + 1)) :
    ChangeVar.chartPull (α + β).val φ f y =
      ChangeVar.chartPull α.val φ f y + ChangeVar.chartPull β.val φ f y := by
  ext v
  simp [ChangeVar.chartPull]

omit [Nonempty 𝒳] in
theorem topDensity_chartPull_formPow {φ : ComplexModel (m + 1 + 1) → 𝒳}
    (α : ClosedRealOneOneForm (m + 1 + 1) 𝒳) (f : ComplexChart (m + 1 + 1) 𝒳)
    (y : ComplexModel (m + 1 + 1)) :
    topDensity (ChangeVar.chartPull (ProductTestForms.formPow α.val (m + 1 + 1)) φ f y) =
      actualTopPowerDensity (ChangeVar.chartPull α.val φ f y) := by
  unfold ChangeVar.chartPull
  rw [ProductTestForms.formPow_coeff, topDensity_compContinuousLinearMap, topDensity_formPower,
    actualTopPowerDensity_compContinuousLinearMap]

theorem zc_pme (z : ComplexModel (m + 1)) (w : ComplexModel 1) :
    zc (prodModelEquiv (m + 1) 1 (z, w)) = z := by
  simp [zc]

theorem wc_pme (z : ComplexModel (m + 1)) (w : ComplexModel 1) :
    wc (prodModelEquiv (m + 1) 1 (z, w)) = w := by
  simp [wc]

theorem pme_zc_wc (y : ComplexModel (m + 1 + 1)) : prodModelEquiv (m + 1) 1 (zc y, wc y) = y := by
  simp [zc, wc]

/-- **`ι^* coord^* θ̃ = s_τ^* θ̃`** in the chart `e` (the zz-block). -/
theorem chartPull_comp_inclFst {e : ComplexChart (m + 1) F.carrier} (f : ComplexChart (m + 1 + 1) 𝒳)
    {y : ComplexModel (m + 1 + 1)} (hy : y ∈ coordDomain e) (hf : D.coord e y ∈ f.val.source)
    (α : ClosedRealOneOneForm (m + 1 + 1) 𝒳) :
    (ChangeVar.chartPull α.val (D.coord e) f y).compContinuousLinearMap (Algebra.inclFst (m + 1)) =
      (ClosedRealOneOneForm.pullback (D.contMDiff_sec hy.2) α).val.coeff e (zc y) := by
  set s := D.sec hy.2 with hs
  have hsy : s (e.val.symm (zc y)) = D.coord e y := (D.coord_eq_sec hy).symm
  have hz : zc y ∈ coordinateDomain s e f :=
    ⟨hy.1, by simp only [mem_preimage]; rw [hsy]; exact hf⟩
  rw [ClosedRealOneOneForm.pullback_val, SmoothRealForm.pullback_coeff _ α.val e f hz]
  have hcm : coordinateMap s e f (zc y) = f.val (D.coord e y) := by
    simp only [coordinateMap, Function.comp_apply, hsy]
  -- the coordinate map of `s` is `z ↦ f (coord e (z, w))`
  set w := wc y with hw
  have hev : coordinateMap s e f =ᶠ[𝓝 (zc y)]
      fun z' => f.val (D.coord e (prodModelEquiv (m + 1) 1 (z', w))) := by
    filter_upwards [e.val.open_target.mem_nhds hy.1] with z' hz'
    have hmem : prodModelEquiv (m + 1) 1 (z', w) ∈ coordDomain e := by
      refine ⟨by rw [zc_pme]; exact hz', by rw [wc_pme]; exact hy.2⟩
    simp only [coordinateMap, Function.comp_apply]
    rw [D.coord_eq_sec hmem, D.sec_congr (τ' := wc y 0) (by rw [wc_pme]) hmem.2 hy.2, zc_pme]
  have hlin : (fun z' : ComplexModel (m + 1) => prodModelEquiv (m + 1) 1 (z', w)) =
      fun z' => Algebra.inclFst (m + 1) z' + prodModelEquiv (m + 1) 1 (0, w) := by
    funext z'
    rw [Algebra.inclFst_apply, ← map_add, Prod.mk_add_mk, add_zero, zero_add]
  have hdl : HasFDerivAt (fun z' : ComplexModel (m + 1) => prodModelEquiv (m + 1) 1 (z', w))
      (Algebra.inclFst (m + 1)) (zc y) := by
    rw [hlin]; exact (Algebra.inclFst (m + 1)).hasFDerivAt.add_const _
  have hpt : prodModelEquiv (m + 1) 1 (zc y, w) = y := pme_zc_wc y
  have hdf : HasFDerivAt (fun y' => f.val (D.coord e y'))
      (fderiv ℝ (fun y' => f.val (D.coord e y')) y) (prodModelEquiv (m + 1) 1 (zc y, w)) := by
    rw [hpt]
    exact ((D.contDiffAt_coord_chart f hy hf).differentiableAt (by simp)).restrictScalars ℝ
      |>.hasFDerivAt
  have hcomp : HasFDerivAt (fun z' => f.val (D.coord e (prodModelEquiv (m + 1) 1 (z', w))))
      ((fderiv ℝ (fun y' => f.val (D.coord e y')) y).comp (Algebra.inclFst (m + 1))) (zc y) :=
    HasFDerivAt.comp (f := fun z' => prodModelEquiv (m + 1) 1 (z', w)) (zc y) hdf hdl
  rw [hev.fderiv_eq, hcomp.fderiv, hcm]
  unfold ChangeVar.chartPull
  ext v
  rfl

/-- **Semipositivity of the zz-block on the contact set.** -/
theorem coefficientSemipositive_zz [CompactSpace 𝒳] [ConnectedSpace 𝒳] {e : ComplexChart (m + 1) F.carrier}
    (f : ComplexChart (m + 1 + 1) 𝒳) {y : ComplexModel (m + 1 + 1)} (hy : y ∈ coordDomain e)
    (hf : D.coord e y ∈ f.val.source) {k : ℕ} (hD : D.coord e y ∈ D.contact k) :
    CoefficientSemipositive
      ((ChangeVar.chartPull D.form.val (D.coord e) f y).compContinuousLinearMap
        (Algebra.inclFst (m + 1))) := by
  have hpos := coefficientSemipositive_of_contact D.form (D.isThetaPshPotential_envelope k).1
    (D.chartSmooth_obstacle k) (Eventually.of_forall fun z => D.envelope_le_obstacle k z) hD f hf
  set L := fderiv ℝ (fun y' => f.val (D.coord e y')) y with hL
  have hLc : ∀ v, L (Complex.I • v) = Complex.I • L v := by
    intro v
    rw [hL, ((D.contDiffAt_coord_chart f hy hf).differentiableAt (by simp)).fderiv_restrictScalars ℝ]
    exact (fderiv ℂ (fun y' => f.val (D.coord e y')) y).map_smul Complex.I v
  intro v
  have h1 := hpos (L (Algebra.inclFst (m + 1) v))
  have hsplit : ChangeVar.chartPull (D.form + ddcClosedForm (D.obstacle k)
      (D.chartSmooth_obstacle k)).val (D.coord e) f y =
      ChangeVar.chartPull D.form.val (D.coord e) f y +
        (smoothDDC (lineObstacle D.χ k) (wc y)).compContinuousLinearMap (projSnd (m + 1) 1) := by
    rw [chartPull_add, D.chartPull_ddc_obstacle f hy hf k]
  have h2 := congrArg (fun A : (ComplexModel (m + 1 + 1)) [⋀^Fin 2]→L[ℝ] ℝ =>
    A ![Algebra.inclFst (m + 1) v, Algebra.inclFst (m + 1) (Complex.I • v)]) hsplit
  simp only [ChangeVar.chartPull, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.add_apply, comp_vec, Algebra.projSnd_inclFst,
    apply_vec_zero_left, add_zero] at h2
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, comp_vec, ChangeVar.chartPull]
  rw [← h2, Algebra.inclFst_smul, hLc]
  exact h1

/-- **`tok-wn-conv6:inner-density`**: at `y` with `coord e y ∈ D_k`,
`(θ̃ + ddᶜg_k)^{n+1} ≤ θ̃^{n+1} + (n + 1) (s_τ^*θ̃)ⁿ · ω_k` as densities in the coordinates `y`. -/
theorem topDensity_chartPull_le [CompactSpace 𝒳] [ConnectedSpace 𝒳] {e : ComplexChart (m + 1) F.carrier}
    (f : ComplexChart (m + 1 + 1) 𝒳) {y : ComplexModel (m + 1 + 1)} (hy : y ∈ coordDomain e)
    (hf : D.coord e y ∈ f.val.source) {k : ℕ} (hD : D.coord e y ∈ D.contact k) :
    topDensity (ChangeVar.chartPull (ProductTestForms.formPow
        (D.form + ddcClosedForm (D.obstacle k) (D.chartSmooth_obstacle k)).val (m + 1 + 1))
        (D.coord e) f y) ≤
      topDensity (ChangeVar.chartPull (ProductTestForms.formPow D.form.val (m + 1 + 1))
        (D.coord e) f y) +
      ((m + 1 + 1 : ℕ) : ℝ) * actualTopPowerDensity
        ((ClosedRealOneOneForm.pullback (D.contMDiff_sec hy.2) D.form).val.coeff e (zc y)) *
        cutoffLineDensity D.χ k (wc y) := by
  rw [topDensity_chartPull_formPow, topDensity_chartPull_formPow, chartPull_add,
    D.chartPull_ddc_obstacle f hy hf k, ← D.chartPull_comp_inclFst f hy hf]
  have hfz : f.val (D.coord e y) ∈ f.val.target := f.val.map_source hf
  set L := fderiv ℝ (fun y' => f.val (D.coord e y')) y with hL
  have hLc : ∀ v, L (Complex.I • v) = Complex.I • L v := by
    intro v
    rw [hL, ((D.contDiffAt_coord_chart f hy hf).differentiableAt (by simp)).fderiv_restrictScalars ℝ]
    exact (fderiv ℂ (fun y' => f.val (D.coord e y')) y).map_smul Complex.I v
  have hB : IsOneOne (ChangeVar.chartPull D.form.val (D.coord e) f y) :=
    ProductTestForms.isOneOne_compContinuousLinearMap (D.form.property.2 f _ hfz) L hLc
  have hG : IsOneOne (smoothDDC (lineObstacle D.χ k) (wc y)) :=
    fun u v => smoothDDC_isOneOne ((contDiff_lineObstacle D.hχ k).contDiffAt.of_le two_le_top') u v
  exact Algebra.actualTopPowerDensity_le _ _ hB hG (D.coefficientSemipositive_zz f hy hf hD)
    (smoothDensity_projectiveFSPotential_nonneg _) (actualTopPowerDensity_lineObstacle D.hχ k _)

end MCData

end SGPT.Okounkov.TranscendentalWN
