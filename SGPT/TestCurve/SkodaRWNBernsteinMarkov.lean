import SGPT.TestCurve.TestConfigPhongSturm
import SGPT.Bergman.SourceVolumeBernsteinMarkov
import SGPT.IGood.DXLowTrace
import SGPT.Foundations.Analysis.Pending.KahlerVolumeSmoothPositive

/-!
# The Bernstein–Markov property of smooth volumes for algebraic sections

Input (b) of `rmk:PhongSturm` (chapter *Test curves*; Ross–Witt Nyström [RWN14, §7, §9]): for a
smooth Hermitian metric `h` on a line bundle `L` over a smooth projective complex variety `X`
and a smooth positive volume `μ` on `X^{an}` — in [RWN14, §9], `μ = (dd^c φ)^n` for `h = e^{-φ}`
positively curved — the `L²` norms of `μ` and the sup norms on `H⁰(X, L^k)` are equivalent up to
subexponential factors:

`sup_X |s|²_{h^k} ≤ C_ε e^{εk} ∫_X |s|²_{h^k} dμ` for all `k` and all `s ∈ H⁰(X, L^k)`

(`SGPT.TestCurve.TestConfig.IsBernsteinMarkov`).

The proof is the scheme-side version of `SGPT.Bergman.BernsteinMarkov.smoothPositiveVolume_bernsteinMarkov`
(which treats the holomorphic sections of a `HermitianHolomorphicLineBundle`): in a chart and an
algebraic frame `α` of `L` near a point, `|s|²_{h^k} = |F|² |α|^{2k}_h` with `F` holomorphic
(`SchemeLineBundleMetric.sectionNormSq_frame`, `schemeOpenRegularFunction_holomorphicAt`), the
local estimate is the submean inequality with the oscillation of `log |α|²_h` on a small ball
(`SGPT.Bergman.BernsteinMarkov.exists_local_exponential_point_bound`, uniform in the degree and
in the holomorphic function), and compactness of `X^{an}` gives one constant.

## Main results

* `exists_local_sectionNormSq_bound`, `exists_global_sectionNormSq_bound`: the local and global
  density bounds `|s|²_{h^k}(y) ≤ C e^{εk} ∫ |s|²_{h^k} dμ`, in `ℝ≥0∞`.
* **`isBernsteinMarkov_of_isSmoothPositiveVolume`**: every finite smooth positive volume has the
  Bernstein–Markov property with respect to every smooth metric on every line bundle.
* `isBernsteinMarkov_kahlerVolume`: in particular the Monge–Ampère volume `ωⁿ` of every Kähler
  form `ω` on `X^{an}`.
* `curvatureKahlerBackground`, `curvatureVolume`, **`isBernsteinMarkov_curvatureVolume`**: for a
  positively curved metric (`c₁(L, h)` Kähler), the measure `μ = c₁(L, h)ⁿ = (dd^c φ)ⁿ` of
  [RWN14, §9] is a finite measure charging the nonempty open sets and has the Bernstein–Markov
  property.
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
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1 SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open scoped Topology ContDiff ENNReal

variable {X : Scheme} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  {E : ClosedProjectiveEmbedding f}

local instance skodaBMTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance skodaBMCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance skodaBMManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
local instance skodaBMMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance skodaBMBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

variable {L : X.Modules} (H : SchemeLineBundleMetric f n E L) (a : LineBundleAtlas L)
  (μ : Measure (SchemeComplexPoint f))

/-! ### The local and the global density bounds -/

/-- **Local Bernstein–Markov bound**: near every point, with one neighbourhood and one constant
for all degrees and all sections, `|s|²_{h^k}(y) ≤ C e^{εk} ∫_X |s|²_{h^k} dμ`. -/
theorem exists_local_sectionNormSq_bound
    (hμ : letI := E.isSeparated; letI := E.quasiCompact; IsSmoothPositiveVolume (n := n) μ)
    (x : SchemeComplexPoint f) {ε : ℝ} (hε : 0 < ε) :
    ∃ W : Set (SchemeComplexPoint f), IsOpen W ∧ x ∈ W ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℕ) (s : SectionSpace f L k), ∀ y ∈ W,
        ENNReal.ofReal (H.sectionNormSq a k s y) ≤
          ENNReal.ofReal (C * Real.exp (ε * k)) *
            ∫⁻ z, ENNReal.ofReal (H.sectionNormSq a k s z) ∂μ := by
  let := E.isSeparated
  let := E.quasiCompact
  let c := complexChartAt (n := n) x
  let U := schemePointFrameOpen f x a
  let α := schemePointFrame f x a
  have hxU : schemeComplexPointImage f x ∈ U := schemePointFrame_mem f x a
  have hx : x ∈ c.val.source := mem_complexChartAt_source x
  let y₀ := c.val x
  have hy₀ : y₀ ∈ c.val.target := c.val.map_source hx
  have hinv : c.val.symm y₀ = x := c.val.left_inv hx
  let D := c.val.target ∩ c.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U)
  have hD : IsOpen D :=
    c.val.isOpen_inter_preimage_symm (U.isOpen.preimage (schemeComplexPointImage_continuous f))
  have hyD : y₀ ∈ D := ⟨hy₀, by
    change schemeComplexPointImage f (c.val.symm y₀) ∈ U
    rw [hinv]
    exact hxU⟩
  obtain ⟨R₀, hR₀, hR₀D⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds hyD)
  let R := R₀ / 2
  have hR : 0 < R := half_pos hR₀
  have hRD : closedBall y₀ R ⊆ D := (closedBall_subset_ball (half_lt_self hR₀)).trans hR₀D
  obtain ⟨ρ, hρsmooth, hρpos, hmap⟩ := hμ c
  -- the frame weight, its logarithm and the density of `μ` in the chart
  let w : ComplexModel n → ℝ := fun z => H.frameNormSq α (c.val.symm z)
  let β : ComplexModel n → ℝ := fun z => -Real.log (w z)
  let γ : ComplexModel n → ℝ := fun _ => 1
  have hwcont : ContinuousAt w y₀ :=
    ((H.smooth α c).continuousOn).continuousAt (hD.mem_nhds hyD)
  have hwpos : ∀ z ∈ D, 0 < w z := fun z hz => H.positive α _ hz.2
  have hβcont : ContinuousAt β y₀ := (hwcont.log (hwpos y₀ hyD).ne').neg
  have hρcont : ContinuousAt ρ y₀ :=
    hρsmooth.continuousOn.continuousAt (c.val.open_target.mem_nhds hy₀)
  obtain ⟨r, C, hr, hC, hrsub, hbound⟩ :=
    SGPT.Bergman.BernsteinMarkov.exists_local_exponential_point_bound
      (isOpen_ball (x := y₀) (ε := R)) (mem_ball_self hR) hβcont hρcont
      (continuousAt_const (y := (1 : ℝ)) (x := y₀)) (hρpos _ hy₀) hε
  let W := c.val.source ∩ c.val ⁻¹' ball y₀ (r / 2)
  have hW : IsOpen W := c.val.continuousOn.isOpen_inter_preimage c.val.open_source isOpen_ball
  have hxW : x ∈ W := ⟨hx, mem_ball_self (half_pos hr)⟩
  refine ⟨W, hW, hxW, C, hC, fun k s y hy => ?_⟩
  -- the holomorphic coefficient of `s` in the frame `α^k`, read in the chart
  let g : SchemeComplexPoint f → ℂ := schemeOpenRegularFunction f n E U
    ((α.tensorPower k).coefficients (𝟙 U) ((bundleTensorPower L k).val.map (homOfLE le_top).op s))
  let F : ComplexModel n → ℂ := fun z => g (c.val.symm z)
  have hF : DifferentiableOn ℂ F (ball y₀ R) := by
    intro z hz
    have hzD := hRD (ball_subset_closedBall hz)
    exact (FactorizedWeightForm.differentiableAt_comp_chart_symm c hzD.1
      (schemeOpenRegularFunction_holomorphicAt f n E U _ _ hzD.2).self_of_nhds).differentiableWithinAt
  -- the density of `|s|²` in the chart
  have hread : ∀ z ∈ D, ‖F z‖ ^ 2 * Real.exp (-((k : ℝ) * β z)) =
      H.sectionNormSq a k s (c.val.symm z) := by
    intro z hz
    rw [H.sectionNormSq_frame a α k s _ hz.2, Complex.normSq_eq_norm_sq]
    have he : Real.exp (-((k : ℝ) * β z)) = w z ^ k := by
      have h1 : -((k : ℝ) * β z) = (k : ℝ) * Real.log (w z) := by
        change -((k : ℝ) * -Real.log (w z)) = _
        ring
      rw [h1, Real.exp_nat_mul, Real.exp_log (hwpos z hz)]
    rw [he]
  have hpoint := hbound (k : ℝ) (Nat.cast_nonneg _) F hF (c.val y) hy.2
  have hyD' : c.val y ∈ D := hRD (ball_subset_closedBall
    (hrsub (ball_subset_closedBall ((ball_subset_ball (half_le_self hr.le)) hy.2))))
  have hpt : ‖F (c.val y)‖ ^ 2 * Real.exp (-((k : ℝ) * β (c.val y))) * γ (c.val y) =
      H.sectionNormSq a k s y := by
    rw [show γ (c.val y) = 1 from rfl, mul_one, hread _ hyD', c.val.left_inv hy.1]
  rw [hpt] at hpoint
  have hmeas : Measurable fun z => ENNReal.ofReal (H.sectionNormSq a k s z) :=
    (ENNReal.continuous_ofReal.comp (continuous_sectionNormSq H a k s)).measurable
  have hI : (∫⁻ z in ball y₀ R,
      ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-((k : ℝ) * β z)) * ρ z)) ≤
      ∫⁻ z, ENNReal.ofReal (H.sectionNormSq a k s z) ∂μ := by
    calc
      _ ≤ ∫⁻ z in closedBall y₀ R,
          ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-((k : ℝ) * β z)) * ρ z) :=
        lintegral_mono_set ball_subset_closedBall
      _ = ∫⁻ z in closedBall y₀ R, ENNReal.ofReal (ρ z) *
          ENNReal.ofReal (H.sectionNormSq a k s (c.val.symm z)) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet] with z hz
        have hzD := hRD hz
        rw [hread z hzD, ← ENNReal.ofReal_mul (hρpos _ hzD.1).le, mul_comm]
      _ = ∫⁻ z in c.val.source ∩ c.val ⁻¹' closedBall y₀ R,
          ENNReal.ofReal (H.sectionNormSq a k s z) ∂μ :=
        (setLIntegral_source_inter_preimage c hρsmooth.continuousOn hmap
          (isCompact_closedBall _ _) (fun z hz => (hRD hz).1) hmeas).symm
      _ ≤ _ := setLIntegral_le_lintegral _ _
  exact hpoint.trans (mul_le_mul' le_rfl hI)

/-- **Global Bernstein–Markov bound** in `ℝ≥0∞`: one constant for all degrees, sections and
points. -/
theorem exists_global_sectionNormSq_bound
    (hμ : letI := E.isSeparated; letI := E.quasiCompact; IsSmoothPositiveVolume (n := n) μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ (k : ℕ) (s : SectionSpace f L k) (x : SchemeComplexPoint f),
      ENNReal.ofReal (H.sectionNormSq a k s x) ≤
        ENNReal.ofReal (A * Real.exp (ε * k)) *
          ∫⁻ y, ENNReal.ofReal (H.sectionNormSq a k s y) ∂μ := by
  classical
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hlocal := fun x => exists_local_sectionNormSq_bound H a μ hμ x hε
  choose W hW hxW C hC hb using hlocal
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hW
    (fun x _ => mem_iUnion.mpr ⟨x, hxW x⟩)
  let A : ℝ := 1 + ∑ x ∈ t, C x
  have hsum : 0 ≤ ∑ x ∈ t, C x := Finset.sum_nonneg (fun x _ => (hC x).le)
  have hA : 0 < A := by dsimp only [A]; linarith
  refine ⟨A, hA, fun k s x => ?_⟩
  obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (ht (mem_univ x))
  have hCA : C y ≤ A := by
    have hle := Finset.single_le_sum (fun z (_ : z ∈ t) => (hC z).le) hyt
    dsimp only [A]
    linarith
  exact (hb y k s x hxy).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hCA (Real.exp_pos _).le)) le_rfl)

/-! ### The Bernstein–Markov property -/

/-- **Bernstein–Markov property of smooth volumes** (input (b) of `rmk:PhongSturm`;
[RWN14, §7]): a finite smooth positive volume `μ` on `X^{an}` satisfies
`sup_X |s|²_{h^k} ≤ C_ε e^{εk} ∫_X |s|²_{h^k} dμ` for every smooth metric `h` on every line
bundle `L`, every `k` and every `s ∈ H⁰(X, L^k)`. -/
theorem isBernsteinMarkov_of_isSmoothPositiveVolume [IsFiniteMeasure μ]
    (hμ : letI := E.isSeparated; letI := E.quasiCompact; IsSmoothPositiveVolume (n := n) μ) :
    IsBernsteinMarkov H a μ := by
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  intro ε hε
  obtain ⟨A, hA, hb⟩ := exists_global_sectionNormSq_bound H a μ hμ hε
  refine ⟨A, hA, fun k s q => ?_⟩
  have hint := integrable_sectionNormSq H a μ k s
  have hnn : 0 ≤ᵐ[μ] fun p => H.sectionNormSq a k s p :=
    Eventually.of_forall fun p => H.sectionNormSq_nonneg a k s p
  have h := hb k s q
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn,
    ← ENNReal.ofReal_mul (mul_pos hA (Real.exp_pos _)).le] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_pos hA (Real.exp_pos _)).le
    (integral_nonneg fun p => H.sectionNormSq_nonneg a k s p))).mp h

section Kahler

variable [IsSeparated f] [QuasiCompact f] [CompactSpace (SchemeComplexPoint f)]

/-- The Monge–Ampère volume `ωⁿ` of a Kähler form on `X^{an}` charges every nonempty open set. -/
instance isOpenPosMeasure_kahlerVolume (omega : KahlerBackground n (SchemeComplexPoint f)) :
    (kahlerVolume omega).IsOpenPosMeasure :=
  SGPT.IGood.DXLow.isOpenPosMeasure_of_isSmoothPositiveVolume
    (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega)

end Kahler

/-- The Monge–Ampère volume `ωⁿ` of every Kähler form `ω` on `X^{an}` has the Bernstein–Markov
property with respect to every smooth metric on every line bundle. -/
theorem isBernsteinMarkov_kahlerVolume
    (omega : letI := E.isSeparated; letI := E.quasiCompact;
      KahlerBackground n (SchemeComplexPoint f)) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    IsBernsteinMarkov H a (kahlerVolume omega) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  exact isBernsteinMarkov_of_isSmoothPositiveVolume H a (kahlerVolume omega)
    (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega)

/-! ### The measure `(dd^c φ)ⁿ` of a positively curved metric -/

/-- A positively curved metric (`c₁(L, h)` is a Kähler form) gives the Kähler background
`ω = c₁(L, h) = dd^c φ` of [RWN14, §9]. -/
def curvatureKahlerBackground
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler) :
    letI := E.isSeparated
    letI := E.quasiCompact
    KahlerBackground n (SchemeComplexPoint f) :=
  letI := E.isSeparated
  letI := E.quasiCompact
  ⟨H.curvature a, hK⟩

/-- The measure `μ = c₁(L, h)ⁿ = (dd^c φ)ⁿ` of a positively curved metric `h = e^{-φ}`, the
measure defining the `L²` products in [RWN14, §9]. -/
def curvatureVolume
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler) :
    Measure (SchemeComplexPoint f) :=
  letI := E.isSeparated
  letI := E.quasiCompact
  haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  kahlerVolume (curvatureKahlerBackground H a hK)

instance isFiniteMeasure_curvatureVolume
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler) :
    IsFiniteMeasure (curvatureVolume H a hK) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  exact inferInstanceAs (IsFiniteMeasure (kahlerVolume (curvatureKahlerBackground H a hK)))

instance isOpenPosMeasure_curvatureVolume
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler) :
    (curvatureVolume H a hK).IsOpenPosMeasure := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  exact isOpenPosMeasure_kahlerVolume (curvatureKahlerBackground H a hK)

/-- `(dd^c φ)ⁿ` is a smooth positive volume. -/
theorem isSmoothPositiveVolume_curvatureVolume
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler) :
    letI := E.isSeparated
    letI := E.quasiCompact
    IsSmoothPositiveVolume (n := n) (curvatureVolume H a hK) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  exact KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume
    (curvatureKahlerBackground H a hK)

/-- **Input (b) of `rmk:PhongSturm`** ([RWN14, §9]): for a positively curved metric `h = e^{-φ}`
on `L`, the measure `μ = (dd^c φ)ⁿ` has the Bernstein–Markov property with respect to `h`
(indeed with respect to every smooth metric `h'` on every line bundle `L'`). -/
theorem isBernsteinMarkov_curvatureVolume {L' : X.Modules} (H' : SchemeLineBundleMetric f n E L')
    (a' : LineBundleAtlas L')
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler) :
    IsBernsteinMarkov H' a' (curvatureVolume H a hK) :=
  isBernsteinMarkov_of_isSmoothPositiveVolume H' a' (curvatureVolume H a hK)
    (isSmoothPositiveVolume_curvatureVolume H a hK)

end SGPT.TestCurve.SkodaRWN
