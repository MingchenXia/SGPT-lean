import SGPT.PSH.BookCurrentSpace
import SGPT.Projective.Hyperplane
import SGPT.Toric.ProjectiveLineSection
import SGPT.Foundations.Analysis.Pending.LelongPoincareDivisor
import SGPT.Foundations.Analysis.Pending.ActualCanonicalComplementaryCurrentCalibration

/-!
# `ν([0], 0) = 1` on the native `ℙ¹` (`ex:Lelongcurrent`)

Source `ex:Lelongcurrent` (chapter `chapter_pshfunctions.tex`): for `T = θ + ddᶜφ ∈ 𝒵₊(X)` one
sets `ν(T, x) = ν(φ, x)` (`SGPT.PSH.BookCurrent.currentLelong`, independent of the
presentation), and "the key example to keep in mind is `ν([0], 0) = 1`, where `[0]` is the
current of integration at `0 ∈ ℙ¹`".

Here `ℙ¹ = SGPT.Projective.ComplexProjectiveSpace 1` is the native compact complex manifold
(atlas: the affine charts `U₀ = {Z₀ ≠ 0}`, `U₁ = {Z₁ ≠ 0}`), `0 = [0 : 1]` is the origin of
the affine chart `U₁` with coordinate `z = Z₀ / Z₁` (the embedding `ℂ ⊂ ℙ¹`, `z ↦ [z : 1]`).

* `zeroDivisor`: the point `0` as a metered effective divisor (TN
  `MeteredEffectiveQDivisor`): weight `log (|Z₀|²/‖Z‖²)`, curvature `ω_FS`; on `U₁` the weight
  is `log |z|² - log (1 + |z|²)`, on `U₀` it is smooth.
* `zeroPointCurrent`: its integration current `[0]`.  It is the current of integration at
  the point `0`: in the chart `U₁` its coefficient is the Dirac current at `z = 0`
  (`zeroPointCurrent_apply_chartOne`: value `φ(0) · Im (v̄₀ w₀)` on the real directions
  `v, w` and the test function `φ`, i.e. `φ(0)` on the oriented basis `(1, i)`), in the chart
  `U₀` (which does not contain `0`) it vanishes (`zeroPointCurrent_coefficients_chartZero`),
  and these two readings determine it (`eq_zeroPointCurrent_of_readings`).
* `zeroCurrent : 𝒵₊(ℙ¹)`: `[0]` as a closed positive `(1,1)`-current; Lelong–Poincaré gives the
  presentation `[0] = ω_FS + ddᶜ log (|Z₀|²/‖Z‖²)` (`isPresentation_zeroCurrent`).
* `currentLelong_zeroCurrent`: `ν([0], 0) = 1`, read through `currentLelong`.
-/

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ComplexConjugate ENNReal Distributions

namespace SGPT.PSH.BookDeep2LelongCurrent

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HolomorphicIdealSheaves LelongPoincareDivisor GlobalCurrents CanonicalCurrentFrame
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.PSH.BookCurrent SGPT.PSH.VariableComplexAtlas

/-- `ℙ¹`, the native compact complex manifold of dimension `1`. -/
abbrev P1 : Type := ComplexProjectiveSpace 1

/-- The point `0 = [0 : 1] ∈ ℙ¹`: the origin of the affine chart `U₁ = {Z₁ ≠ 0}`. -/
def zero : P1 := affinePoint 1 0

theorem succAbove_one_zero : (1 : Fin 2).succAbove 0 = 0 := rfl

theorem zero_rep_zero : zero.rep 0 = 0 := by
  obtain ⟨c, -, hc⟩ := rep_smul zero (affineLift_ne_zero 1 0) rfl
  rw [hc, Pi.smul_apply, ← succAbove_one_zero, affineLift_succAbove]
  simp

theorem affineChart_one_zero : affineChart (N := 1) 1 zero = 0 := affineChart_affinePoint 1 0

/-! ### Chart computations -/

theorem chart_eq (e : ComplexChart 1 P1) : ∃ i : Fin 2, e.val = affineChart i :=
  (mem_atlas_iff e.val).mp e.property

theorem symm_mem_trans_source {i j : Fin 2} {z : ComplexModel 1}
    (hzU : (affineChart (N := 1) i).symm z ∈ (affineChart (N := 1) j).source) :
    z ∈ ((affineChart (N := 1) i).symm.trans (affineChart j)).source := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, affineChart_target]
  exact ⟨mem_univ z, hzU⟩

/-- The Fubini–Study potential of `U_j`, read in any chart, is smooth on the overlap. -/
theorem contDiffOn_fsPotential_chart (e : ComplexChart 1 P1) (j : Fin 2) :
    ContDiffOn ℝ ∞ (fun z => fsPotential (affineChart j (e.val.symm z)))
      (e.val.target ∩ e.val.symm ⁻¹' (affineChart (N := 1) j).source) := by
  obtain ⟨i, hi⟩ := chart_eq e
  rw [hi]
  set T := (affineChart (N := 1) i).symm.trans (affineChart j)
  have hT : ContDiffOn ℂ ∞ T T.source :=
    contDiffOn_of_differentiableOn_complex (differentiableOn_transition i j) T.open_source
  have hsrc : T.source =
      (affineChart (N := 1) i).target ∩ (affineChart (N := 1) i).symm ⁻¹'
        (affineChart (N := 1) j).source := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
  rw [← hsrc]
  exact contDiff_fsPotential.comp_contDiffOn (hT.restrict_scalars ℝ)

/-- `ω_FS = -ddᶜ(-log(1 + |z_j|²))` in every chart, on the overlap with `U_j`. -/
theorem fsForm_coeff_eq_neg_smoothDDC (e : ComplexChart 1 P1) (j : Fin 2)
    {z : ComplexModel 1} (hz : z ∈ e.val.target)
    (hzU : e.val.symm z ∈ (affineChart (N := 1) j).source) :
    (fsClosedForm (N := 1)).val.coeff e z =
      -smoothDDC (fun y => -fsPotential (affineChart j (e.val.symm y))) z := by
  change smoothDDC fsPotential z = _
  have hopen : IsOpen (e.val.target ∩ e.val.symm ⁻¹' (affineChart (N := 1) j).source) :=
    e.val.isOpen_inter_preimage_symm (affineChart j).open_source
  rw [smoothDDC_neg hopen (contDiffOn_fsPotential_chart e j) ⟨hz, hzU⟩, neg_neg]
  obtain ⟨i, hi⟩ := chart_eq e
  rw [hi] at hzU ⊢
  exact (smoothDDC_fsPotential_transition i j (symm_mem_trans_source hzU)).symm

/-- The affine coordinate `z = Z₀/Z₁` of `U₁`, as a function on `ℙ¹`. -/
def coordOne (q : P1) : ℂ := affineChart (N := 1) 1 q 0

theorem coordOne_mdifferentiableOn :
    MDifferentiableOn 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ℂ) coordOne (affineChart (N := 1) 1).source :=
  (EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).mdifferentiable.comp_mdifferentiableOn
    (mdifferentiableOn_atlas (affineChart_mem_atlas 1))

theorem coordOne_exists_ne_zero {W : Set P1} (hW : IsOpen W)
    (hWU : W ⊆ (affineChart (N := 1) 1).source) (hne : W.Nonempty) :
    ∃ y ∈ W, coordOne y ≠ 0 := by
  obtain ⟨y₀, hy₀⟩ := hne
  by_cases h₀ : coordOne y₀ = 0
  swap
  · exact ⟨y₀, hy₀, h₀⟩
  let V : Set (ComplexModel 1) :=
    (affineChart (N := 1) 1).target ∩ (affineChart (N := 1) 1).symm ⁻¹' W
  have hV : IsOpen V := (affineChart 1).isOpen_inter_preimage_symm hW
  have hz₀ : affineChart (N := 1) 1 y₀ ∈ V :=
    ⟨mem_univ _, by
      change (affineChart (N := 1) 1).symm (affineChart 1 y₀) ∈ W
      rw [(affineChart (N := 1) 1).left_inv (hWU hy₀)]
      exact hy₀⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV _ hz₀
  set z₁ : ComplexModel 1 :=
    affineChart (N := 1) 1 y₀ + ((ε / 2 : ℝ) : ℂ) • EuclideanSpace.single (0 : Fin 1) (1 : ℂ)
  have hz₁ : z₁ ∈ V := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [z₁, add_sub_cancel_left, norm_smul, PiLp.norm_single, norm_one, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity)]
    linarith
  have hz₁0 : z₁ 0 = coordOne y₀ + ((ε / 2 : ℝ) : ℂ) := by
    simp [z₁, coordOne]
  refine ⟨(affineChart (N := 1) 1).symm z₁, hz₁.2, ?_⟩
  change affineChart (N := 1) 1 ((affineChart (N := 1) 1).symm z₁) 0 ≠ 0
  rw [(affineChart (N := 1) 1).right_inv (mem_univ _), hz₁0, h₀, zero_add]
  exact Complex.ofReal_ne_zero.mpr (by positivity)

/-- On `U₁`: `log (|Z₀|²/‖Z‖²) = log |z|² - log (1 + |z|²)`. -/
theorem coordLog_eq_chartOne {y : P1} (hy : y ∈ (affineChart (N := 1) 1).source) :
    coordLog 0 y = (∑ _i : Fin 1, (((1 : ℚ) : ℝ) : EReal) *
        generatorLog (fun _ : Fin 1 => coordOne) y) +
      ((-fsPotential (affineChart (N := 1) 1 y) : ℝ) : EReal) := by
  set z := affineChart (N := 1) 1 y
  have hyz : y = affinePoint 1 z := ((affineChart (N := 1) 1).left_inv hy).symm
  have hlog : coordLog 0 y = logNormSq (z 0) - (fsPotential z : EReal) := by
    rw [hyz, ← succAbove_one_zero, coordLog_affinePoint_succAbove]
  have hgen : generatorLog (fun _ : Fin 1 => coordOne) y = logNormSq (z 0) := by
    rw [generatorLog_eq_log_sum, Fin.sum_univ_one]
    rfl
  rw [hlog, hgen, Fin.sum_univ_one, Rat.cast_one, EReal.coe_one, one_mul, EReal.coe_neg,
    sub_eq_add_neg]

/-- On `U₀`: `log (|Z₀|²/‖Z‖²) = -log (1 + |z|²)` is smooth. -/
theorem coordLog_eq_chartZero {y : P1} (hy : y ∈ (affineChart (N := 1) 0).source) :
    coordLog 0 y = (∑ i : Fin 0, (((Fin.elim0 i : ℚ) : ℝ) : EReal) *
        generatorLog (fun _ : Fin 1 => (Fin.elim0 i : P1 → ℂ)) y) +
      ((-fsPotential (affineChart (N := 1) 0 y) : ℝ) : EReal) := by
  have hyz : y = affinePoint 0 (affineChart (N := 1) 0 y) :=
    ((affineChart (N := 1) 0).left_inv hy).symm
  rw [Finset.univ_eq_empty, Finset.sum_empty, zero_add]
  conv_lhs => rw [hyz]
  exact coordLog_affinePoint_self 0 _

theorem mem_chartZero_of_not_mem_chartOne {x : P1} (hx : x ∉ (affineChart (N := 1) 1).source) :
    x ∈ (affineChart (N := 1) 0).source := by
  obtain ⟨i, hi⟩ := exists_mem_affineChart_source x
  fin_cases i
  · exact hi
  · exact absurd hi hx

/-! ### The divisor `0` and its integration current -/

/-- **The point `0 ∈ ℙ¹` as a metered effective divisor**: weight `log (|Z₀|²/‖Z‖²)`,
curvature `ω_FS`; on `U₁` the weight is `log |z|² + h` with `h = -log (1 + |z|²)` and
`ω_FS = -ddᶜ h`, on `U₀` it is the smooth function `-log (1 + |z|²)`. -/
def zeroDivisor : MeteredEffectiveQDivisor 1 P1 where
  weight := coordLog 0
  curvature := fsClosedForm
  local_presentation x := by
    by_cases hx : x ∈ (affineChart (N := 1) 1).source
    · exact ⟨_, (affineChart 1).open_source, hx, 1, fun _ => 1, fun _ => coordOne,
        fun q => -fsPotential (affineChart (N := 1) 1 q), fun _ => zero_le_one,
        fun _ => coordOne_mdifferentiableOn,
        fun _ _ hW hWU hne => coordOne_exists_ne_zero hW hWU hne,
        fun e => (contDiffOn_fsPotential_chart e 1).neg,
        fun _ hy => coordLog_eq_chartOne hy,
        fun e _ hz hzU => fsForm_coeff_eq_neg_smoothDDC e 1 hz hzU⟩
    · exact ⟨_, (affineChart 0).open_source, mem_chartZero_of_not_mem_chartOne hx, 0,
        Fin.elim0, Fin.elim0, fun q => -fsPotential (affineChart (N := 1) 0 q),
        fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
        fun e => (contDiffOn_fsPotential_chart e 0).neg,
        fun _ hy => coordLog_eq_chartZero hy,
        fun e _ hz hzU => fsForm_coeff_eq_neg_smoothDDC e 0 hz hzU⟩

/-- The presentation of `0` on `U₁`, with the single equation `z = 0`. -/
def presentationOne : LocalPresentation zeroDivisor where
  U := (affineChart (N := 1) 1).source
  isOpen := (affineChart 1).open_source
  N := 1
  a := fun _ => 1
  g := fun _ => coordOne
  h := fun q => -fsPotential (affineChart (N := 1) 1 q)
  a_nonneg := fun _ => zero_le_one
  g_holo := fun _ => coordOne_mdifferentiableOn
  g_ne := fun _ _ hW hWU hne => coordOne_exists_ne_zero hW hWU hne
  h_smooth := fun e => (contDiffOn_fsPotential_chart e 1).neg
  weight_eq := fun _ hy => coordLog_eq_chartOne hy
  curvature_eq := fun e _ hz hzU => fsForm_coeff_eq_neg_smoothDDC e 1 hz hzU

/-- The presentation on `U₀`, with no equation (`0 ∉ U₀`). -/
def presentationZero : LocalPresentation zeroDivisor where
  U := (affineChart (N := 1) 0).source
  isOpen := (affineChart 0).open_source
  N := 0
  a := Fin.elim0
  g := Fin.elim0
  h := fun q => -fsPotential (affineChart (N := 1) 0 q)
  a_nonneg := fun i => i.elim0
  g_holo := fun i => i.elim0
  g_ne := fun i => i.elim0
  h_smooth := fun e => (contDiffOn_fsPotential_chart e 0).neg
  weight_eq := fun _ hy => coordLog_eq_chartZero hy
  curvature_eq := fun e _ hz hzU => fsForm_coeff_eq_neg_smoothDDC e 0 hz hzU

/-- **The current of integration `[0]` at `0 ∈ ℙ¹`**: the integration current of the metered
divisor `zeroDivisor` (TN `integrationCurrent`, `ddᶜ ψ + Θ`). -/
def zeroPointCurrent : GlobalCurrent 1 P1 (degreeTwo (Nat.succ_pos 0)) :=
  integrationCurrent (canonicalBasis 1) (Nat.succ_pos 0) zeroDivisor

/-- The chart `U₁` as an atlas chart. -/
def chartOne : ComplexChart 1 P1 := affineComplexChart 1

/-- The chart `U₀` as an atlas chart. -/
def chartZero : ComplexChart 1 P1 := affineComplexChart 0

theorem presentationOne_chartG (z : ComplexModel 1) :
    presentationOne.chartG chartOne ⟨0, Nat.one_pos⟩ z = z 0 := by
  change affineChart (N := 1) 1 ((affineChart (N := 1) 1).symm z) 0 = z 0
  rw [(affineChart (N := 1) 1).right_inv (mem_univ z)]

/-- In the chart `U₁`, the coefficient of `[0]` (on the domain of the presentation, which is
the whole chart) is the integration current `[div z]` of the coordinate. -/
theorem zeroPointCurrent_restrict_chartOne :
    restrictForm ((zeroPointCurrent).coefficients (canonicalBasis 1) chartOne)
        (presentationOne.chartDomain_le chartOne) =
      DivisorIntegrationCurrent.divisorCurrent (presentationOne.differentiableOn_chartG chartOne ⟨0, Nat.one_pos⟩)
        (presentationOne.frequently_chartG_ne chartOne ⟨0, Nat.one_pos⟩) := by
  obtain ⟨-, -, -, -, -, hlocal⟩ :=
    LelongPoincareDivisor.lelongPoincare (canonicalBasis 1) (Nat.succ_pos 0) zeroDivisor
  rw [zeroPointCurrent, hlocal presentationOne chartOne,
    ActualCanonicalComplementaryCurrentCalibration.haarFactor_canonicalBasis]
  rw [NNReal.coe_one, one_smul]
  erw [Fin.sum_univ_one]
  simp only [presentationOne, Rat.cast_one]
  exact one_smul _ _

/-- In the chart `U₀` the coefficient of `[0]` vanishes (`0 ∉ U₀`). -/
theorem zeroPointCurrent_restrict_chartZero :
    restrictForm ((zeroPointCurrent).coefficients (canonicalBasis 1) chartZero)
        (presentationZero.chartDomain_le chartZero) = 0 := by
  obtain ⟨-, -, -, -, -, hlocal⟩ :=
    LelongPoincareDivisor.lelongPoincare (canonicalBasis 1) (Nat.succ_pos 0) zeroDivisor
  rw [zeroPointCurrent, hlocal presentationZero chartZero]
  change _ • (∑ i : Fin 0, _) = _
  rw [Finset.univ_eq_empty, Finset.sum_empty, smul_zero]

/-- The local equation of `0` in the chart `U₁` is the coordinate `z ↦ z₀`. -/
theorem presentationOne_chartG_eq :
    presentationOne.chartG chartOne ⟨0, Nat.one_pos⟩ =
      (SGPT.Toric.projectiveModelEquiv.symm : ComplexModel 1 → ℂ) := by
  funext z
  rw [presentationOne_chartG, SGPT.Toric.projectiveModelEquiv_symm_apply]

/-- **`[0]` is the current of integration at `0`**: in the chart `U₁`, on the real directions
`v, w` and a test function `φ`, the coefficient of `[0]` is `φ(0) · Im (v̄₀ w₀)` (the Dirac
mass at `z = 0` with the orientation form of `ℂ`). -/
theorem zeroPointCurrent_apply_chartOne (v w : ComplexModel 1)
    (φ : 𝓓(presentationOne.chartDomain chartOne, ℝ)) :
    restrictForm ((zeroPointCurrent).coefficients (canonicalBasis 1) chartOne)
        (presentationOne.chartDomain_le chartOne) ![v, w] φ =
      φ 0 * (conj (v 0) * w 0).im := by
  rw [zeroPointCurrent_restrict_chartOne, DivisorIntegrationCurrent.divisorCurrent_apply,
    presentationOne_chartG_eq]
  simp only [DivisorIntegrationCurrent.divisorDensity, SGPT.Toric.projectiveCoordinate_regularLocus]
  have heq : (fun x : ComplexModel 1 ↦ φ x * ({0} : Set (ComplexModel 1)).indicator
      (fun x ↦ (DivisorRegularLocus.divisorMult
        (SGPT.Toric.projectiveModelEquiv.symm : ComplexModel 1 → ℂ) x : ℝ) *
        DivisorRegularLocus.transverseForm
          (SGPT.Toric.projectiveModelEquiv.symm : ComplexModel 1 → ℂ) x v w) x) =
      ({0} : Set (ComplexModel 1)).indicator (fun x ↦ φ x *
        ((DivisorRegularLocus.divisorMult
          (SGPT.Toric.projectiveModelEquiv.symm : ComplexModel 1 → ℂ) x : ℝ) *
          DivisorRegularLocus.transverseForm
            (SGPT.Toric.projectiveModelEquiv.symm : ComplexModel 1 → ℂ) x v w)) := by
    funext x
    by_cases hx : x ∈ ({0} : Set (ComplexModel 1)) <;> simp [hx]
  rw [heq, integral_indicator (measurableSet_singleton 0), integral_singleton]
  simp [measureReal_def, Measure.euclideanHausdorffMeasure_zero,
    SGPT.Toric.projectiveCoordinate_divisorMult, SGPT.Toric.projectiveCoordinate_transverseForm]

theorem chartDomain_one_cover :
    ∀ x ∈ chartTarget chartOne, ∃ _i : Unit, x ∈ presentationOne.chartDomain chartOne := by
  intro x _
  exact ⟨(), mem_univ x, affinePoint_mem_source 1 x⟩

theorem chartDomain_zero_cover :
    ∀ x ∈ chartTarget chartZero, ∃ _i : Unit, x ∈ presentationZero.chartDomain chartZero := by
  intro x _
  exact ⟨(), mem_univ x, affinePoint_mem_source 0 x⟩

/-- The two chart readings determine `[0]`: a global current which is `[div z]` in `U₁` and
vanishes in `U₀` is `[0]`. -/
theorem eq_zeroPointCurrent_of_readings (T : GlobalCurrent 1 P1 (degreeTwo (Nat.succ_pos 0)))
    (h₁ : restrictForm (T.coefficients (canonicalBasis 1) chartOne)
        (presentationOne.chartDomain_le chartOne) =
      DivisorIntegrationCurrent.divisorCurrent
        (presentationOne.differentiableOn_chartG chartOne ⟨0, Nat.one_pos⟩)
        (presentationOne.frequently_chartG_ne chartOne ⟨0, Nat.one_pos⟩))
    (h₀ : restrictForm (T.coefficients (canonicalBasis 1) chartZero)
        (presentationZero.chartDomain_le chartZero) = 0) :
    T = zeroPointCurrent := by
  apply globalCurrent_ext (canonicalBasis 1)
  intro e
  obtain ⟨i, hi⟩ := chart_eq e
  have he : e = affineComplexChart i := Subtype.ext hi
  subst he
  ext v : 1
  fin_cases i
  · apply eq_of_forall_restrict_eq (fun _ : Unit => presentationZero.chartDomain chartZero)
      (fun _ => presentationZero.chartDomain_le chartZero) chartDomain_zero_cover
    intro _
    have h1 := congrArg (fun A => A v) h₀
    have h2 := congrArg (fun A => A v) zeroPointCurrent_restrict_chartZero
    simp only [restrictForm_apply'] at h1 h2
    exact h1.trans h2.symm
  · apply eq_of_forall_restrict_eq (fun _ : Unit => presentationOne.chartDomain chartOne)
      (fun _ => presentationOne.chartDomain_le chartOne) chartDomain_one_cover
    intro _
    have h1 := congrArg (fun A => A v) h₁
    have h2 := congrArg (fun A => A v) zeroPointCurrent_restrict_chartOne
    simp only [restrictForm_apply'] at h1 h2
    exact h1.trans h2.symm

/-! ### `[0] ∈ 𝒵₊(ℙ¹)` and `ν([0], 0) = 1` -/

/-- `log (|Z₀|²/‖Z‖²) ∈ PSH(ℙ¹, ω_FS)`. -/
theorem isThetaPshPotential_coordLog_zero :
    IsThetaPshPotential (fsBackground (N := 1)).form.val (coordLog 0) :=
  isThetaPshPotential_coordLog 0

/-- **Lelong–Poincaré for `0 ∈ ℙ¹`**: `[0] = ω_FS + ddᶜ log (|Z₀|²/‖Z‖²)`. -/
theorem zeroPointCurrent_eq_thetaPotentialCurrent :
    zeroPointCurrent = NaturalThetaPshGeometricCurrent.thetaPotentialCurrent
      (fsBackground (N := 1)).form.val (coordLog 0) isThetaPshPotential_coordLog_zero := by
  rw [zeroPointCurrent, integrationCurrent, NaturalThetaPshGeometricCurrent.thetaPotentialCurrent,
    add_comm]
  rfl

/-- **`[0] ∈ 𝒵₊(ℙ¹)`**: the current of integration at `0` as a closed positive
`(1,1)`-current. -/
def zeroCurrent : ClosedPositiveCurrent 0 P1 :=
  ⟨⟨zeroPointCurrent,
      isClosed_integrationCurrent (canonicalBasis 1) (Nat.succ_pos 0) zeroDivisor,
      isTypeOneOne_integrationCurrent (canonicalBasis 1) (Nat.succ_pos 0) zeroDivisor⟩,
    by
      have h := (thetaPositiveCurrent (fsBackground (N := 1)).form (coordLog 0)
        isThetaPshPotential_coordLog_zero).isPositive
      rw [thetaPositiveCurrent_current, ← zeroPointCurrent_eq_thetaPotentialCurrent] at h
      exact h⟩

@[simp] theorem zeroCurrent_current : zeroCurrent.current = zeroPointCurrent := rfl

/-- The presentation `[0] = ω_FS + ddᶜ log (|Z₀|²/‖Z‖²)` of `[0] ∈ 𝒵₊(ℙ¹)`. -/
theorem isPresentation_zeroCurrent :
    IsPresentation zeroCurrent (fsBackground (N := 1)).form (coordLog 0) :=
  ⟨isThetaPshPotential_coordLog_zero, zeroPointCurrent_eq_thetaPotentialCurrent⟩

/-- **`ν([0], 0) = 1`** (`ex:Lelongcurrent`): the Lelong number of the current of integration
`[0] ∈ 𝒵₊(ℙ¹)` at `0 ∈ ℙ¹`, read through the book's convention `ν(T, x) = ν(φ, x)`
(`currentLelong`, independent of the presentation `T = θ + ddᶜφ`). -/
theorem currentLelong_zeroCurrent : currentLelong zeroCurrent zero = 1 := by
  rw [currentLelong_eq_of_isPresentation isPresentation_zeroCurrent, sourceLelong_ofFixedModel_eq]
  have h := squaredLogLelongNumber_smul_coordLog (N := 1) (i := 0) zero_rep_zero
    (c := (1 : NNReal)) one_pos
  simpa using h

end SGPT.PSH.BookDeep2LelongCurrent
