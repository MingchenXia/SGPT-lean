import SGPT.Okounkov.TranscendentalWNDeformationStatement
import SGPT.Toric.ProjectiveLineFubiniStudy

/-!
# The projective line of the deformation: the affine coordinate and the weights `N₀`, `N₁`

Blueprint `tok-wn-def:exceptional-metric`, `tok-wn-def:centre-generators`
(`claude-tok-wn-def`).

On `ℙ¹ = ℙ(ℂ²)` with the native atlas of `SGPT.Toric` (the two affine charts):

* `chartAt_projectiveZero`: the preferred chart at `0 = [0 : 1]` is the finite affine chart, and
  `projectiveModelChart_false_apply`: on its domain the chart coordinate is the affine coordinate
  `τ = v₀ / v₁` (`projectiveAffine`);
* `projectiveWeight i [v₀ : v₁] = |vᵢ|² / (|v₀|² + |v₁|²)` (`N₀`, `N₁`), well defined
  (`projectiveWeight_mk`), with `N₀ + N₁ = 1`, `N₁ > 0` off `∞`, `N₀ = |τ|² N₁` off `∞`, smooth in
  both affine charts (`contDiffOn_projectiveWeight_chart`);
* `baseExceptionalWeight_eq`: `W(x, p) = |s_Z(x)|²_h N₁(p) + N₀(p)`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Toric

/-! ### The affine coordinate -/

theorem projectiveZero_eq_mk : projectiveZero = Projectivization.mk ℂ ![0, 1] (by simp) := rfl

theorem projectiveAffine_mk (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    projectiveAffine (Projectivization.mk ℂ v hv) = v 0 / v 1 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  unfold projectiveAffine
  rw [← ha]
  simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul]
  by_cases h1 : v 1 = 0
  · simp [h1]
  · field_simp

@[simp] theorem projectiveAffine_zero : projectiveAffine projectiveZero = 0 := by
  rw [projectiveZero_eq_mk, projectiveAffine_mk]
  simp

theorem projectiveLineHomeomorph_symm_mk (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    projectiveLineHomeomorph.symm (Projectivization.mk ℂ v hv) =
      if v 1 = 0 then OnePoint.infty else (((v 1)⁻¹ * v 0 : ℂ) : OnePoint ℂ) :=
  OnePoint.equivProjectivization_symm_apply_mk ℂ v hv

/-- The domain of the finite affine chart is `{v₁ ≠ 0}` (`τ ≠ ∞`). -/
theorem mem_projectiveModelChart_false_source {p : ProjectiveLine} :
    p ∈ (projectiveModelChart false).source ↔ p.rep 1 ≠ 0 := by
  rw [projectiveModelChart_source]
  change projectiveLineHomeomorph.symm p ∈ projectiveFiniteChart.source ↔ _
  rw [projectiveFiniteChart_source]
  conv_lhs => rw [← Projectivization.mk_rep p]
  rw [projectiveLineHomeomorph_symm_mk]
  by_cases h : p.rep 1 = 0
  · simp only [h, if_true, ne_eq, not_true_eq_false, iff_false]
    rintro ⟨z, hz⟩
    exact OnePoint.coe_ne_infty z hz
  · simp only [h, if_false, ne_eq, not_false_eq_true, iff_true]
    exact ⟨_, rfl⟩

/-- On the finite affine chart, the chart coordinate is the affine coordinate `τ`. -/
theorem projectiveModelChart_false_apply {p : ProjectiveLine}
    (hp : p ∈ (projectiveModelChart false).source) :
    projectiveModelChart false p 0 = projectiveAffine p := by
  have h1 : p.rep 1 ≠ 0 := mem_projectiveModelChart_false_source.mp hp
  change projectiveModelEquiv (projectiveFiniteChart (projectiveLineHomeomorph.symm p)) 0 = _
  conv_lhs => rw [← Projectivization.mk_rep p]
  rw [projectiveLineHomeomorph_symm_mk, if_neg h1, projectiveFiniteChart_coe,
    projectiveModelEquiv_apply_zero]
  unfold projectiveAffine
  field_simp

/-- **The preferred chart at `0` is the finite affine chart.** -/
theorem chartAt_projectiveZero :
    chartAt (ComplexModel 1) projectiveZero = projectiveModelChart false := by
  obtain ⟨b, hb⟩ := (mem_projectiveNativeAtlas_iff _).mp
    (chart_mem_atlas (ComplexModel 1) projectiveZero)
  have hmem := mem_chart_source (ComplexModel 1) projectiveZero
  rw [hb] at hmem ⊢
  cases b
  · rfl
  · exfalso
    rw [projectiveModelChart_source] at hmem
    change projectiveLineHomeomorph.symm projectiveZero ∈ projectiveInfinityChart.source at hmem
    rw [projectiveInfinityChart_source] at hmem
    apply hmem
    change projectiveLineHomeomorph.symm (projectiveLineHomeomorph ((0 : ℂ) : OnePoint ℂ)) = _
    rw [Homeomorph.symm_apply_apply]

theorem projectiveZero_mem_chart_source :
    projectiveZero ∈ (projectiveModelChart false).source := by
  rw [← chartAt_projectiveZero]
  exact mem_chart_source (ComplexModel 1) projectiveZero

/-! ### The weights `N₀`, `N₁` -/

/-- `Nᵢ([v₀ : v₁]) = |vᵢ|² / (|v₀|² + |v₁|²)`. -/
def projectiveWeight (i : Fin 2) (p : ProjectiveLine) : ℝ :=
  ‖p.rep i‖ ^ 2 / (‖p.rep 0‖ ^ 2 + ‖p.rep 1‖ ^ 2)

theorem normSq_add_pos (v : Fin 2 → ℂ) (hv : v ≠ 0) : 0 < ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 := by
  by_contra h
  push Not at h
  have h0 : ‖v 0‖ ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg ‖v 1‖]) (sq_nonneg _)
  have h1 : ‖v 1‖ ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg ‖v 0‖]) (sq_nonneg _)
  apply hv
  funext i
  fin_cases i
  · simpa using h0
  · simpa using h1

theorem projectiveWeight_mk (i : Fin 2) (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    projectiveWeight i (Projectivization.mk ℂ v hv) = ‖v i‖ ^ 2 / (‖v 0‖ ^ 2 + ‖v 1‖ ^ 2) := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  unfold projectiveWeight
  rw [← ha]
  simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul, norm_mul, mul_pow]
  have ha0 : ‖(a : ℂ)‖ ^ 2 ≠ 0 := by
    have : (a : ℂ) ≠ 0 := a.ne_zero
    positivity
  have hpos := normSq_add_pos v hv
  rw [← mul_add, mul_div_mul_left _ _ ha0]

theorem projectiveWeight_nonneg (i : Fin 2) (p : ProjectiveLine) : 0 ≤ projectiveWeight i p :=
  div_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem projectiveWeight_add (p : ProjectiveLine) :
    projectiveWeight 0 p + projectiveWeight 1 p = 1 := by
  unfold projectiveWeight
  rw [← add_div, div_self (normSq_add_pos _ p.rep_nonzero).ne']

theorem projectiveWeight_le_one (i : Fin 2) (p : ProjectiveLine) : projectiveWeight i p ≤ 1 := by
  have h := projectiveWeight_add p
  have h0 := projectiveWeight_nonneg 0 p
  have h1 := projectiveWeight_nonneg 1 p
  fin_cases i <;> simp <;> linarith

theorem projectiveWeight_one_pos {p : ProjectiveLine} (hp : p.rep 1 ≠ 0) :
    0 < projectiveWeight 1 p :=
  div_pos (by positivity) (normSq_add_pos _ p.rep_nonzero)

/-- `N₀ = |τ|² N₁` off `∞`. -/
theorem projectiveWeight_zero_eq {p : ProjectiveLine} (hp : p.rep 1 ≠ 0) :
    projectiveWeight 0 p = ‖projectiveAffine p‖ ^ 2 * projectiveWeight 1 p := by
  have h1 : ‖p.rep 1‖ ^ 2 ≠ 0 := by positivity
  have hD := (normSq_add_pos _ p.rep_nonzero).ne'
  unfold projectiveWeight projectiveAffine
  rw [norm_div, div_pow]
  field_simp

/-- `Nᵢ` in the affine chart `b`, at the chart coordinate `z`. -/
theorem projectiveWeight_chart_symm (i : Fin 2) (b : Bool) (z : ComplexModel 1) :
    projectiveWeight i ((projectiveModelChart b).symm z) =
      ‖projectiveAffineLift b z i‖ ^ 2 /
        (‖projectiveAffineLift b z 0‖ ^ 2 + ‖projectiveAffineLift b z 1‖ ^ 2) := by
  rw [projectiveModelChart_symm_eq_mk, projectiveWeight_mk]

/-- `Nᵢ` is smooth in both affine charts. -/
theorem contDiff_projectiveWeight_chart (i : Fin 2) (b : Bool) :
    ContDiff ℝ ∞ (fun z => projectiveWeight i ((projectiveModelChart b).symm z)) := by
  have hden : ∀ z : ComplexModel 1,
      ‖projectiveAffineLift b z 0‖ ^ 2 + ‖projectiveAffineLift b z 1‖ ^ 2 ≠ 0 := fun z =>
    (normSq_add_pos _ (projectiveAffineLift_ne_zero b z)).ne'
  have hc : ∀ j : Fin 2, ContDiff ℝ ∞ (fun z : ComplexModel 1 => ‖projectiveAffineLift b z j‖ ^ 2) := by
    intro j
    have hlin : ContDiff ℝ ∞ (fun z : ComplexModel 1 => projectiveAffineLift b z j) := by
      cases b <;> fin_cases j <;> simp [projectiveAffineLift] <;>
        first
        | exact contDiff_const
        | exact (projectiveModelEquiv.symm.toContinuousLinearMap.restrictScalars ℝ).contDiff
    exact hlin.norm_sq ℝ
  simp_rw [projectiveWeight_chart_symm]
  exact (hc i).div ((hc 0).add (hc 1)) hden

/-- `Nᵢ` is chart-smooth on the native atlas of `ℙ¹`. -/
theorem contDiffOn_projectiveWeight (i : Fin 2) (e : ComplexChart 1 ProjectiveLine) :
    ContDiffOn ℝ ∞ (fun z => projectiveWeight i (e.val.symm z)) e.val.target := by
  obtain ⟨b, hb⟩ := (mem_projectiveNativeAtlas_iff e.val).mp e.property
  rw [hb]
  exact (contDiff_projectiveWeight_chart i b).contDiffOn

/-! ### The base exceptional weight -/

/-- `W(x, p) = |s_Z(x)|²_h N₁(p) + N₀(p)`. -/
theorem baseExceptionalWeight_eq {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    (E : FirstPass.HolomorphicIdealSheaves.MeteredEffectiveQDivisor (m + 1) F.carrier)
    (q : F.carrier × ProjectiveLine) :
    baseExceptionalWeight F E q =
      (EReal.exp (E.weight q.1)).toReal * projectiveWeight 1 q.2 + projectiveWeight 0 q.2 := by
  unfold baseExceptionalWeight projectiveWeight
  rw [add_div, mul_div_assoc]

end SGPT.Okounkov.TranscendentalWN
