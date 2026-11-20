import SGPT.TestCurve.SkodaRWNPointExtension
import SGPT.IGood.DXMainSections

/-!
# The Skoda inclusion in multiplier-ideal form

The second analytic input of [RWN14, Proposition 7.11] in `SkodaRWNReduction` is `SkodaInclusion`,
stated with the global integrals `∫_X |σ|²_{h^k} e^{-kψ_τ} dμ`. On the compact manifold `X^{an}`
finiteness of this integral means `σ ∈ H⁰(X, L^k ⊗ 𝓘(kψ_τ))`. This file states the inclusion with
the project's section spaces (`SGPT.Okounkov.IsMultiplierSection`), which does not involve a
measure:

`SkodaInclusionIdeal 𝓕`: for `τ' < τ < τ(𝓕)` and `k ≥ k₀(τ, τ')`,
`H⁰(X, L^k ⊗ 𝓘(kψ_τ)) ⊆ 𝓕^{kτ'}_k`,

and proves that it implies `SkodaInclusion 𝓕` for every smooth positive volume.

## Main results

* `isMultiplierSection_of_lintegral_lt_top`: for a Borel weight `ψ` and `k > 0`, a section `σ` of
  `L^k` with `∫_X |σ|²_{h^k} e^{-kψ} dμ < ∞` lies in `H⁰(X, L^k ⊗ 𝓘(kψ))`.
* `skodaInclusion_of_ideal`: `SkodaInclusionIdeal 𝓕 → SkodaInclusion 𝓕 μ`.
* **`phongSturmRemark_of_sectionsAlgebraic_of_skodaInclusionIdeal`**: `rmk:PhongSturm` for a
  positively curved metric and `μ = (dd^c φ)ⁿ`, from GAGA for `H⁰(X, L^k)` (`k ≫ 0`) and the
  Skoda inclusion `H⁰(X, L^k ⊗ 𝓘(kψ_τ)) ⊆ 𝓕^{kτ'}_k` for the filtrations of the ample test
  configurations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.SkodaRWN

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set Metric SGPT.Okounkov
  SGPT.LineBundle SGPT.TestCurve.TestConfig
open MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.NAPotential.GAGAMult
open scoped Topology ENNReal

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  {E : ClosedProjectiveEmbedding f}

local instance skodaMulTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance skodaMulCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance skodaMulManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
local instance skodaMulMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance skodaMulBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

variable {L : X.Modules} {a : LineBundleAtlas L}

/-- **The Skoda inclusion in multiplier-ideal form** (statement): for `τ' < τ < τ(𝓕)` there is
`k₀` such that for `k ≥ k₀`, `H⁰(X, L^k ⊗ 𝓘(kψ_τ)) ⊆ 𝓕^{kτ'}_k`, where `ψ_τ` is the obstacle of
`ex:RWN` and `H⁰(X, L^k ⊗ 𝓘(kψ_τ))` consists of the sections whose coefficient in every local
frame lies in the multiplier ideal sheaf `𝓘(kψ_τ)` (`SGPT.Okounkov.IsMultiplierSection`).

For the finitely generated filtration of an ample test configuration this is the Skoda division
step of [RWN14, Proposition 7.11] ([RWN14, Theorem 7.10]). -/
def SkodaInclusionIdeal (F : SectionFiltration f a) (H : SchemeLineBundleMetric f n E L) : Prop :=
  ∀ τ' τ : ℝ, τ' < τ → (τ : EReal) < F.slope → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
    ∀ σ : SectionSpace f L k, IsMultiplierSection f n E (F.obstacle H τ) k σ →
      σ ∈ F.piece ((k : ℝ) * τ') k

/-- A section of `L^k` (`k > 0`) with finite weighted `L²` norm `∫_X |σ|²_{h^k} e^{-kψ} dμ`, for a
Borel weight `ψ` and a smooth positive volume `μ`, lies in `H⁰(X, L^k ⊗ 𝓘(kψ))`. -/
theorem isMultiplierSection_of_lintegral_lt_top (H : SchemeLineBundleMetric f n E L)
    {μ : Measure (SchemeComplexPoint f)}
    (hμ : letI := E.isSeparated; letI := E.quasiCompact; IsSmoothPositiveVolume (n := n) μ)
    {ψ : SchemeComplexPoint f → EReal} (hψ : Measurable ψ) {k : ℕ} (hk : 0 < k)
    (σ : SectionSpace f L k)
    (hfin : ∫⁻ y, ENNReal.ofReal (H.sectionNormSq a k σ y) *
      multiplierWeight (k : ℝ) (ψ y) ∂μ < ⊤) :
    IsMultiplierSection f n E ψ k σ := by
  let := E.isSeparated
  let := E.quasiCompact
  refine Or.inr fun U α p hp => ?_
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  set e := complexChartAt (n := n) p with he
  have hpe : p ∈ e.val.source := mem_complexChartAt_source p
  set G : ComplexModel n → ℂ := fun z => sectionFrameCoefficient f n E α k σ (e.val.symm z)
    with hG
  set w : ComplexModel n → ℝ := fun z => H.frameNormSq α (e.val.symm z) with hw
  set D : Set (ComplexModel n) :=
    e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U) with hD
  have hDopen : IsOpen D :=
    e.val.isOpen_inter_preimage_symm (U.isOpen.preimage (schemeComplexPointImage_continuous f))
  have hz0D : e.val p ∈ D := by
    refine ⟨e.val.map_source hpe, ?_⟩
    change schemeComplexPointImage f (e.val.symm (e.val p)) ∈ U
    rw [e.val.left_inv hpe]
    exact hp
  obtain ⟨r₀, hr₀, hr₀D⟩ := Metric.isOpen_iff.mp hDopen _ hz0D
  set r := r₀ / 2 with hr
  have hrpos : 0 < r := half_pos hr₀
  have hcb : closedBall (e.val p) r ⊆ D := fun z hz =>
    hr₀D (lt_of_le_of_lt (mem_closedBall.mp hz) (half_lt_self hr₀))
  obtain ⟨ρ, hρsmooth, hρpos, hmap⟩ := hμ e
  -- lower bounds of the frame weight and of the density on the closed ball
  have hwcont : ContinuousOn w D := (H.smooth α e).continuousOn
  have hwpos : ∀ z ∈ D, 0 < w z := fun z hz => H.positive α _ hz.2
  obtain ⟨zw, hzw, hwmin⟩ := (isCompact_closedBall (e.val p) r).exists_isMinOn
    (nonempty_closedBall.mpr hrpos.le) (hwcont.mono hcb)
  obtain ⟨zρ, hzρ, hρmin⟩ := (isCompact_closedBall (e.val p) r).exists_isMinOn
    (nonempty_closedBall.mpr hrpos.le)
    (hρsmooth.continuousOn.mono fun z hz => (hcb hz).1)
  set c : ℝ := ρ zρ * w zw ^ k with hc
  have hcpos : 0 < c := mul_pos (hρpos _ (hcb hzρ).1) (pow_pos (hwpos _ (hcb hzw)) k)
  -- the integrand on `X` and its density in the chart
  set fM : SchemeComplexPoint f → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (H.sectionNormSq a k σ y) * multiplierWeight (k : ℝ) (ψ y) with hfM
  have hWmeas : Measurable fun y => multiplierWeight (k : ℝ) (ψ y) :=
    (multiplierWeight_antitone hkR.le).measurable.comp hψ
  have hfMmeas : Measurable fM :=
    (ENNReal.continuous_ofReal.comp (continuous_sectionNormSq H a k σ)).measurable.mul hWmeas
  set dens := multiplierDensity (chartFunction ψ e) (k : ℝ) G with hdens
  have hbound : ∀ z ∈ closedBall (e.val p) r,
      dens z ≤ ENNReal.ofReal c⁻¹ * (ENNReal.ofReal (ρ z) * fM (e.val.symm z)) := by
    intro z hz
    have hzD := hcb hz
    have hN : H.sectionNormSq a k σ (e.val.symm z) = ‖G z‖ ^ 2 * w z ^ k := by
      rw [H.sectionNormSq_frame a α k σ _ hzD.2, Complex.normSq_eq_norm_sq]
      rfl
    have hρw : c ≤ ρ z * w z ^ k :=
      mul_le_mul (hρmin hz) (pow_le_pow_left₀ (hwpos _ (hcb hzw)).le (hwmin hz) k)
        (pow_pos (hwpos _ (hcb hzw)) k).le (hρpos _ hzD.1).le
    have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal c⁻¹ * ENNReal.ofReal (ρ z * w z ^ k) := by
      rw [← ENNReal.ofReal_mul (inv_pos.mpr hcpos).le, ← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [inv_mul_eq_div, le_div_iff₀ hcpos, one_mul]
      exact hρw
    have heq : ENNReal.ofReal c⁻¹ * (ENNReal.ofReal (ρ z) * fM (e.val.symm z)) =
        (ENNReal.ofReal c⁻¹ * ENNReal.ofReal (ρ z * w z ^ k)) * dens z := by
      simp only [hfM, hdens, multiplierDensity, chartFunction]
      rw [hN, ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul (hρpos _ hzD.1).le]
      ring
    rw [heq]
    calc dens z = 1 * dens z := (one_mul _).symm
      _ ≤ _ := mul_le_mul' hone le_rfl
  refine ⟨schemeOpenRegularFunction_holomorphicAt f n E U _ p hp, hkR, ball (e.val p) r,
    isOpen_ball, mem_ball_self hrpos, ?_, ?_, ?_⟩
  · intro z hz
    have hzD : z ∈ D := hcb (ball_subset_closedBall hz)
    exact (FactorizedWeightForm.differentiableAt_comp_chart_symm e hzD.1
      (schemeOpenRegularFunction_holomorphicAt f n E U _ _ hzD.2).self_of_nhds
      ).differentiableWithinAt
  · have hGc : ContinuousOn G (ball (e.val p) r) := by
      intro z hz
      have hzD : z ∈ D := hcb (ball_subset_closedBall hz)
      exact (FactorizedWeightForm.differentiableAt_comp_chart_symm e hzD.1
        (schemeOpenRegularFunction_holomorphicAt f n E U _ _ hzD.2).self_of_nhds
        ).continuousAt.continuousWithinAt
    have h1 : AEMeasurable (fun z => ENNReal.ofReal (‖G z‖ ^ 2))
        (volume.restrict (ball (e.val p) r)) :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        (((continuous_pow 2).comp_continuousOn (continuous_norm.comp_continuousOn hGc)).aemeasurable
          measurableSet_ball)
    have h2 : AEMeasurable (fun z => multiplierWeight (k : ℝ) (ψ (e.val.symm z)))
        (volume.restrict (ball (e.val p) r)) :=
      hWmeas.comp_aemeasurable ((e.val.continuousOn_symm.mono fun z hz =>
        (hcb (ball_subset_closedBall hz)).1).aemeasurable measurableSet_ball)
    exact h1.mul h2
  · calc (∫⁻ z in ball (e.val p) r, dens z)
        ≤ ∫⁻ z in closedBall (e.val p) r, dens z := lintegral_mono_set ball_subset_closedBall
      _ ≤ ∫⁻ z in closedBall (e.val p) r,
            ENNReal.ofReal c⁻¹ * (ENNReal.ofReal (ρ z) * fM (e.val.symm z)) :=
          setLIntegral_mono' isClosed_closedBall.measurableSet hbound
      _ = ENNReal.ofReal c⁻¹ *
            ∫⁻ z in closedBall (e.val p) r, ENNReal.ofReal (ρ z) * fM (e.val.symm z) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal c⁻¹ *
            ∫⁻ y in e.val.source ∩ e.val ⁻¹' closedBall (e.val p) r, fM y ∂μ := by
          rw [setLIntegral_source_inter_preimage e hρsmooth.continuousOn hmap
            (isCompact_closedBall _ _) (fun z hz => (hcb hz).1) hfMmeas]
      _ ≤ ENNReal.ofReal c⁻¹ * ∫⁻ y, fM y ∂μ :=
          mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

/-- The obstacle `ψ_τ` is Borel measurable (it is upper semicontinuous). -/
theorem measurable_obstacle (F : SectionFiltration f a) (H : SchemeLineBundleMetric f n E L)
    (τ : ℝ) : Measurable (F.obstacle H τ) :=
  (upperSemicontinuous_uscRegularization _).measurable

/-- The Skoda inclusion in multiplier-ideal form implies the Skoda inclusion with the weighted
`L²` norms of any smooth positive volume. -/
theorem skodaInclusion_of_ideal (F : SectionFiltration f a) (H : SchemeLineBundleMetric f n E L)
    (μ : Measure (SchemeComplexPoint f))
    (hμ : letI := E.isSeparated; letI := E.quasiCompact; IsSmoothPositiveVolume (n := n) μ)
    (h : SkodaInclusionIdeal F H) : SkodaInclusion F H μ := by
  intro τ' τ hτ' hτ
  obtain ⟨k₀, hk₀⟩ := h τ' τ hτ' hτ
  refine ⟨max k₀ 1, fun k hk σ hfin => ?_⟩
  exact hk₀ k ((le_max_left _ _).trans hk) σ
    (isMultiplierSection_of_lintegral_lt_top H hμ (measurable_obstacle F H τ)
      ((le_max_right _ _).trans hk) σ hfin)

variable [IsIntegral X]

/-- **[RWN14, Proposition 7.11] from GAGA and the Skoda inclusion** (multiplier-ideal form). -/
theorem rwnSkodaClause_of_sectionsAlgebraic_of_skodaInclusionIdeal (F : SectionFiltration f a)
    (H : SchemeLineBundleMetric f n E L)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hgaga : letI := E.isSeparated; letI := E.quasiCompact;
      ∀ᶠ j in atTop, SchemeSectionsAlgebraic f n E a H j)
    (hSI : SkodaInclusionIdeal F H) : RWNSkodaClause H F :=
  rwnSkodaClause_of_sectionsAlgebraic_of_skodaInclusion H a F (curvatureVolume H a hK)
    (isSmoothPositiveVolume_curvatureVolume H a hK) hK hgaga
    (skodaInclusion_of_ideal F H _ (isSmoothPositiveVolume_curvatureVolume H a hK) hSI)

/-- **`rmk:PhongSturm` from GAGA for `H⁰(X, L^k)` and the Skoda inclusion.** Let `L` be ample on
the smooth projective variety `X`, `h = e^{-φ}` a positively curved smooth metric on `L` and
`μ = (dd^c φ)ⁿ`. Assume

* GAGA for the sections of `L^k`, `k ≫ 0` (`SchemeSectionsAlgebraic`), and
* the Skoda inclusion `H⁰(X, L^k ⊗ 𝓘(kψ_τ)) ⊆ 𝓕^{kτ'}_k` (`τ' < τ < τ(𝓕)`, `k ≥ k₀(τ, τ')`) for the
  filtration `𝓕` of every ample test configuration of `(X, L)` (finitely generated normalized
  `ℤ`-filtration).

Then for every ample test configuration the geodesic ray `Γ^{𝓕*}` is the Phong–Sturm ray:
`Γ^{𝓕*}_t = Φ(t)` for all `t > 0` and every choice of adapted orthonormal bases
(`PhongSturmRemark`). -/
theorem phongSturmRemark_of_sectionsAlgebraic_of_skodaInclusionIdeal
    [Nonempty (SchemeComplexPoint f)] [CompactSpace (SchemeComplexPoint f)]
    (H : SchemeLineBundleMetric f n E L) (P : AmplePolarization f L)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hgaga : letI := E.isSeparated; letI := E.quasiCompact;
      ∀ᶠ j in atTop, SchemeSectionsAlgebraic f n E a H j)
    (hSI : ∀ (G : SectionZFiltration f a) (hG : G.IsFinitelyGenerated) (h0 : G.piece 0 0 = ⊤),
      SkodaInclusionIdeal (G.fgFiltration hG h0) H) :
    PhongSturmRemark H a (curvatureVolume H a hK) :=
  phongSturmRemark_of_sectionsAlgebraic_of_skodaInclusion H a P hK hgaga fun G hG h0 =>
    skodaInclusion_of_ideal (G.fgFiltration hG h0) H _
      (isSmoothPositiveVolume_curvatureVolume H a hK) (hSI G hG h0)

end SGPT.TestCurve.SkodaRWN
