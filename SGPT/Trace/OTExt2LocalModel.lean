import SGPT.Trace.TwistedL2YDensity
import SGPT.Trace.TwistedL2SingularRemoval
import SGPT.PSH.GlobalL2SectionsPosMass

/-!
# The twisted `L²` estimate and `L²` removability for functions on open sets of `ℂⁿ`

Blueprint `claude-ot-ext2.tex`, node `claude-ot-ext2:euclidean`.  The proof of FPT
`lem:local-critical-gain-extension` applies FPT `lem:twisted-kahler-line-estimate` on the
non-compact open set `D \ {w = 0} ⊆ ℂⁿ` to the trivial line bundle, and
`lem:l2-holomorphic-analytic-removal` across `{w = 0}`.  This file specializes the proved
manifold statements `TwistedL2CorrectionStatement n X` (`twistedL2CorrectionStatement_manifold`)
and `L2RemovableSingularityStatement n X` (`l2RemovableSingularityStatement`) to `X = ℂⁿ`, the
flat Kähler form, Lebesgue measure and the trivial bundle `unit` with its standard metric, where
sections are functions, the local weight is the weight itself and `σ = β + ddᶜ r` has the
quadratic form `‖v‖² + Levi(r)(v)/π`.

## Main results

* `flatModelKahler`, `kahlerQuad_flatModelKahler`: the flat Kähler background of `ℂⁿ`;
* `isSmoothPositiveVolume_volume`, `isChartDensity_volume_iff`: Lebesgue measure and its density;
* `euclideanTwistedCorrection`: the twisted `L²` estimate for functions on an open `U ⊆ ℂⁿ`;
* `euclideanRemovable`: `L²` removable singularities for functions.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.OTExt2

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle
open SGPT.Trace.TwistedL2

variable {n : ℕ}

/-! ### The flat model -/

/-- The flat Kähler background `β` of `ℂⁿ` (the fundamental form `Im ⟨u, v⟩`). -/
def flatModelKahler (n : ℕ) : KahlerBackground n (ComplexModel n) where
  form := ⟨flatKahlerForm n, (flatKahlerForm_isKahler n).2,
    fun e z hz => ((flatKahlerForm_isKahler n).1 e z hz).1⟩
  isKahler := flatKahlerForm_isKahler n

theorem kahlerQuad_flatModelKahler (c : ComplexChart n (ComplexModel n)) (z v : ComplexModel n) :
    kahlerQuad (flatModelKahler n) c z v = ‖v‖ ^ 2 := by
  show Kahler.fundamentalFormAlt ![v, Complex.I • v] = ‖v‖ ^ 2
  rw [Kahler.fundamentalFormAlt_apply]
  exact Kahler.fundamentalForm_complexStructure_self v

theorem modifiedKahlerQuad_flatModelKahler (r : ComplexModel n → ℝ)
    (c : ComplexChart n (ComplexModel n)) (z v : ComplexModel n) :
    modifiedKahlerQuad (flatModelKahler n) r c z v = ‖v‖ ^ 2 + leviForm r z v / Real.pi := by
  obtain rfl := chart_eq c
  rw [modifiedKahlerQuad, kahlerQuad_flatModelKahler]
  rfl

theorem chartSmoothOn_model {f : ComplexModel n → ℝ} {U : Set (ComplexModel n)}
    (hf : ContDiffOn ℝ ∞ f U) : SGPT.PSH.LineBundleMetric.ChartSmoothOn (n := n) f U := by
  intro e
  obtain rfl := chart_eq e
  exact hf.mono fun z hz => hz.2

theorem chartSmooth_model {f : ComplexModel n → ℝ} (hf : ContDiff ℝ ∞ f) :
    ChartSmooth (n := n) f := by
  intro e
  obtain rfl := chart_eq e
  simpa using hf.contDiffOn

/-- Lebesgue measure is a smooth positive volume on `ℂⁿ` (density `1`). -/
theorem isChartDensity_volume_one (c : ComplexChart n (ComplexModel n)) :
    IsChartDensity (volume : Measure (ComplexModel n)) c (fun _ => 1) := by
  obtain rfl := chart_eq c
  refine ⟨contDiffOn_const, fun _ _ => one_pos, ?_⟩
  simp only [chart0_source, chart0_target, Measure.restrict_univ, ENNReal.ofReal_one]
  rw [show (fun _ : ComplexModel n => (1 : ℝ≥0∞)) = 1 from rfl, withDensity_one]
  exact Measure.map_id

theorem isSmoothPositiveVolume_volume :
    IsSmoothPositiveVolume (n := n) (volume : Measure (ComplexModel n)) := fun c =>
  ⟨fun _ => 1, (isChartDensity_volume_one c).1, (isChartDensity_volume_one c).2.1,
    (isChartDensity_volume_one c).2.2⟩

theorem eq_one_of_isChartDensity_volume {c : ComplexChart n (ComplexModel n)}
    {ρ : ComplexModel n → ℝ} (h : IsChartDensity (volume : Measure (ComplexModel n)) c ρ) :
    ρ = fun _ => 1 :=
  chartDensity_unique h (isChartDensity_volume_one c)

/-! ### The trivial bundle on `ℂⁿ` -/

theorem unit_frame_eq (e : AtlasFrame (unit (n := n) (M := ComplexModel n))) :
    e.val = Bundle.Trivial.trivialization (ComplexModel n) ℂ :=
  Set.mem_singleton_iff.mp e.property.out

theorem frameNormSq_unit (e : AtlasFrame (unit (n := n) (M := ComplexModel n)))
    (x : ComplexModel n) : frameNormSq unit e x = 1 := by
  rw [frameNormSq, unit_frame_eq e]
  change ‖(Bundle.Trivial.trivialization (ComplexModel n) ℂ).symm x 1‖ ^ 2 = 1
  rw [Bundle.Trivial.trivialization_symm_apply, norm_one, one_pow]

/-- A function `ℂⁿ → ℂ` as a section of the trivial bundle. -/
def toUnitSection (G : ComplexModel n → ℂ) : (x : ComplexModel n) → (unit (n := n)).Fiber x :=
  fun x => G x

theorem chartCoeff_unit (c : ComplexChart n (ComplexModel n))
    (e : AtlasFrame (unit (n := n) (M := ComplexModel n))) (G : ComplexModel n → ℂ) :
    chartCoeff unit c e (toUnitSection G) = G := by
  obtain rfl := chart_eq c
  funext z
  rw [chartCoeff, frameCoeff]
  have he := unit_frame_eq e
  change (e.val ⟨z, G z⟩).2 = G z
  rw [he]
  rfl

theorem chartFrameDomain_unit (c : ComplexChart n (ComplexModel n))
    (e : AtlasFrame (unit (n := n) (M := ComplexModel n))) :
    chartFrameDomain unit c e = univ := by
  obtain rfl := chart_eq c
  rw [chartFrameDomain, unit_frame_eq e]
  simp

theorem localWeight_unit (c : ComplexChart n (ComplexModel n))
    (e : AtlasFrame (unit (n := n) (M := ComplexModel n))) (φ : ComplexModel n → ℝ) :
    localWeight unit c e (fun _ => 1) φ = φ := by
  obtain rfl := chart_eq c
  funext z
  rw [localWeight, frameNormSq_unit]
  simp

/-- The function of a section of the trivial bundle. -/
def ofUnitSection (S : (x : ComplexModel n) → (unit (n := n)).Fiber x) : ComplexModel n → ℂ :=
  fun x => S x

/-- Sections of the trivial bundle: holomorphic on an open set iff their function is. -/
theorem isHolomorphicSectionOn_unit_iff {U : Set (ComplexModel n)} (hU : IsOpen U)
    (S : (x : ComplexModel n) → (unit (n := n)).Fiber x) :
    SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) (unit (n := n)).Fiber S U ↔
      DifferentiableOn ℂ (ofUnitSection S) U := by
  set e := trivializationAt ℂ (unit (n := n) (M := ComplexModel n)).Fiber (0 : ComplexModel n)
  have he : e = Bundle.Trivial.trivialization (ComplexModel n) ℂ := unit_frame_eq ⟨e, inferInstance⟩
  have hb : U ⊆ e.baseSet := by rw [he]; simp
  have hcoef : (fun x => (e ⟨x, S x⟩).2) = ofUnitSection S := by
    funext x
    have h1 : e ⟨x, S x⟩ = (Bundle.Trivial.trivialization (ComplexModel n) ℂ) ⟨x, S x⟩ := by
      rw [he]
      rfl
    rw [h1]
    rfl
  unfold SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn
  rw [Trivialization.mdifferentiableOn_section_iff e hU hb, hcoef,
    mdifferentiableOn_iff_differentiableOn]

/-! ### The twisted estimate on open sets of `ℂⁿ` -/

/-- **The twisted `L²` estimate for functions on an open set `U ⊆ ℂⁿ`** (FPT
`lem:twisted-kahler-line-estimate`, trivial bundle, Lebesgue measure, `σ = β + ddᶜ r` complete
on `U`): for a smooth weight `φ`, smooth twist functions `a, b` bounded above and below by
positive constants with positive definite twisted curvature `H`, and a smooth `G` with
`|⟨∂̄G, v⟩|² ≤ D H(v)` and `|⟨∂̄G, v⟩|² ≤ D_σ σ(v)`, `∫_U D_σ e^{-φ} < ∞`, there is `S`
holomorphic on `U` with `∫_U |G - S|² e^{-φ} / (a + b) ≤ ∫_U D e^{-φ}`. -/
theorem euclideanTwistedCorrection {U : Set (ComplexModel n)} (hU : IsOpen U)
    {r : ComplexModel n → ℝ} (hr : ContDiffOn ℝ ∞ r U)
    (hrpos : ∀ z ∈ U, ∀ v : ComplexModel n, v ≠ 0 → 0 < ‖v‖ ^ 2 + leviForm r z v / Real.pi)
    (hcut : HasCompleteCutoffs (flatModelKahler n) r U)
    {φ a b : ComplexModel n → ℝ} (hφ : ContDiffOn ℝ ∞ φ U) (ha : ContDiffOn ℝ ∞ a U)
    (hb : ContDiffOn ℝ ∞ b U)
    (hab : ∃ m M : ℝ, 0 < m ∧ ∀ x ∈ U, m ≤ a x ∧ a x ≤ M ∧ m ≤ b x ∧ b x ≤ M)
    (hcurv : ∀ z ∈ U, ∀ v : ComplexModel n, v ≠ 0 → 0 < twistedCurvature a b φ z v)
    {G : ComplexModel n → ℂ} (hG : ContDiffOn ℝ ∞ G U) {D Dσ : ComplexModel n → ℝ}
    (hD : ∀ z ∈ U, ∀ v : ComplexModel n,
      ‖dbarPairing G z v‖ ^ 2 ≤ D z * twistedCurvature a b φ z v)
    (hDσ : ∀ z ∈ U, ∀ v : ComplexModel n,
      ‖dbarPairing G z v‖ ^ 2 ≤ Dσ z * (‖v‖ ^ 2 + leviForm r z v / Real.pi))
    (hint : ∫⁻ z in U, ENNReal.ofReal (Dσ z * Real.exp (-φ z)) < ⊤) :
    ∃ S : ComplexModel n → ℂ, DifferentiableOn ℂ S U ∧
      ∫⁻ z in U, ENNReal.ofReal (‖G z - S z‖ ^ 2 * Real.exp (-φ z) / (a z + b z)) ≤
        ∫⁻ z in U, ENNReal.ofReal (D z * Real.exp (-φ z)) := by
  have hmod : IsKahlerModificationOn (flatModelKahler n) r U := by
    refine ⟨chartSmoothOn_model hr, fun c z _ hzU v hv => ?_⟩
    obtain rfl := chart_eq c
    rw [modifiedKahlerQuad_flatModelKahler]
    exact hrpos z hzU v hv
  obtain ⟨S, hS, hle⟩ := twistedL2CorrectionStatement_manifold n (ComplexModel n)
    (flatModelKahler n) U hU r hmod hcut volume isSmoothPositiveVolume_volume unit
    SGPT.PSH.GlobalL2.isSourceSmoothHermitianMetric_unit φ a b (chartSmoothOn_model hφ)
    (chartSmoothOn_model ha) (chartSmoothOn_model hb) hab
    (fun c e ρ hρ z _ hzU v hv => by
      obtain rfl := chart_eq c
      obtain rfl := eq_one_of_isChartDensity_volume hρ
      rw [localWeight_unit]
      exact hcurv z hzU v hv)
    (toUnitSection G)
    (fun c e => by
      obtain rfl := chart_eq c
      rw [chartCoeff_unit, chartFrameDomain_unit]
      exact hG.mono fun z hz => hz.2)
    D Dσ
    (fun c e ρ hρ z _ hzU v => by
      obtain rfl := chart_eq c
      obtain rfl := eq_one_of_isChartDensity_volume hρ
      rw [localWeight_unit, chartCoeff_unit, frameNormSq_unit, mul_one]
      exact hD z hzU v)
    (fun c e z _ hzU v => by
      obtain rfl := chart_eq c
      rw [chartCoeff_unit, frameNormSq_unit, mul_one, modifiedKahlerQuad_flatModelKahler]
      exact hDσ z hzU v)
    hint
  exact ⟨ofUnitSection S, (isHolomorphicSectionOn_unit_iff hU S).mp hS, hle⟩

/-! ### Removable singularities for functions -/

/-- **`L²` removable singularities for functions** (FPT `lem:l2-holomorphic-analytic-removal`
on `ℂⁿ`). -/
theorem euclideanRemovable {U A : Set (ComplexModel n)} (hU : IsOpen U) (hA : IsClosed A)
    (hAn : IsLocallyAnalyticNull (n := n) A) {S : ComplexModel n → ℂ}
    (hS : DifferentiableOn ℂ S (U \ A))
    (hL2 : ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ U →
      ∫⁻ x in K \ A, ENNReal.ofReal (‖S x‖ ^ 2) < ⊤) :
    ∃ S' : ComplexModel n → ℂ, DifferentiableOn ℂ S' U ∧ ∀ x ∈ U \ A, S' x = S x := by
  obtain ⟨S', hS', heq⟩ := l2RemovableSingularityStatement n (ComplexModel n) volume
    isSmoothPositiveVolume_volume unit U A hU hA hAn (toUnitSection S)
    ((isHolomorphicSectionOn_unit_iff (hU.sdiff hA) _).mpr hS) hL2
  exact ⟨ofUnitSection S', (isHolomorphicSectionOn_unit_iff hU S').mp hS', heq⟩

end SGPT.Trace.OTExt2
