import SGPT.Foundations.Analysis.Pending.KahlerDomination
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.LocallyConvex.WithSeminorms

set_option autoImplicit false

/-! # Actual normalized tensor probes and the intrinsic directional C0 seminorm -/

open Set Filter
open scoped Topology BoundedContinuousFunction

namespace SGPT.Foundations.Analysis.Pending.XiaoFormC0Topology

open FirstPass FirstPass.PositiveClasses

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- An actual nonzero complex tangent probe at an actual chart target point. -/
structure LineProbe (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] where
  chart : ComplexChart n M
  point : ComplexModel n
  mem_target : point ∈ chart.val.target
  vector : ComplexModel n
  vector_ne_zero : vector ≠ 0

instance : TopologicalSpace (LineProbe n M) := ⊥
instance : DiscreteTopology (LineProbe n M) := ⟨rfl⟩

/-- Actual normalized directional evaluation against a genuine Kähler background. -/
def normalizedProbe (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (p : LineProbe n M) : ℝ :=
  θ.val.coeff p.chart p.point ![p.vector, Complex.I • p.vector] /
    w.form.val.coeff p.chart p.point ![p.vector, Complex.I • p.vector]

/-- The actual denominator at every nonzero tangent probe is strictly positive. -/
theorem probe_denominator_pos (w : KahlerBackground n M) (p : LineProbe n M) :
    0 < w.form.val.coeff p.chart p.point ![p.vector, Complex.I • p.vector] :=
  (w.isKahler.1 p.chart p.point p.mem_target).2 p.vector p.vector_ne_zero

variable [CompactSpace M]

/-- Actual compact Kähler domination bounds all genuine normalized tangent probes at once. -/
theorem exists_normalizedProbe_abs_bound (w : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : LineProbe n M, |normalizedProbe w θ p| ≤ C := by
  obtain ⟨A, hA, hlow⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul w θ
  obtain ⟨B, hB, hupp⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul w (-θ)
  refine ⟨max A B, (hA.le.trans (le_max_left _ _)), fun p => ?_⟩
  have hd := probe_denominator_pos w p
  have hl := hlow p.chart p.point p.mem_target p.vector
  have hu := hupp p.chart p.point p.mem_target p.vector
  simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
    ClosedRealOneOneForm.coeff_neg, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.neg_apply,
    smul_eq_mul] at hl hu
  apply abs_le.mpr
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith [mul_le_mul_of_nonneg_right (le_max_left A B) hd.le]
  · apply (div_le_iff₀ hd).mpr
    nlinarith [mul_le_mul_of_nonneg_right (le_max_right A B) hd.le]

private def boundedProbe (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) :
    LineProbe n M →ᵇ ℝ where
  toFun := normalizedProbe w θ
  continuous_toFun := continuous_of_discreteTopology
  map_bounded' := by
    obtain ⟨C, _, hC⟩ := exists_normalizedProbe_abs_bound w θ
    refine ⟨2 * C, fun p q => ?_⟩
    rw [Real.dist_eq]
    calc |normalizedProbe w θ p - normalizedProbe w θ q|
        ≤ |normalizedProbe w θ p| + |normalizedProbe w θ q| := abs_sub _ _
      _ ≤ 2 * C := by linarith [hC p, hC q]

/-- A genuine linear map into actual bounded functions; the topology is the supremum norm topology. -/
def probeLinearMap (w : KahlerBackground n M) :
    ClosedRealOneOneForm n M →ₗ[ℝ] (LineProbe n M →ᵇ ℝ) where
  toFun := boundedProbe w
  map_add' := by
    intro θ η
    ext p
    change normalizedProbe w (θ + η) p = normalizedProbe w θ p + normalizedProbe w η p
    simp only [normalizedProbe, ClosedRealOneOneForm.coeff_add,
      ContinuousAlternatingMap.add_apply, add_div]
  map_smul' := by
    intro c θ
    ext p
    change normalizedProbe w (c • θ) p = c * normalizedProbe w θ p
    simp only [normalizedProbe, ClosedRealOneOneForm.coeff_smul,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    exact mul_div_assoc c _ _

/-- The actual probe value is exactly the normalized genuine tensor evaluation. -/
theorem probeLinearMap_apply (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (p : LineProbe n M) : probeLinearMap w θ p = normalizedProbe w θ p := rfl

/-- The intrinsic actual directional C0 seminorm, obtained by pulling back the actual supremum norm. -/
def formC0Seminorm (w : KahlerBackground n M) : Seminorm ℝ (ClosedRealOneOneForm n M) :=
  (normSeminorm ℝ (LineProbe n M →ᵇ ℝ)).comp (probeLinearMap w)

/-- This is the supremum norm of actual normalized tensor probes. -/
theorem formC0Seminorm_eq (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) :
    formC0Seminorm w θ = ‖probeLinearMap w θ‖ := rfl

/-- Every actual normalized tensor evaluation is controlled by the actual directional C0 seminorm. -/
theorem abs_normalizedProbe_le (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (p : LineProbe n M) : |normalizedProbe w θ p| ≤ formC0Seminorm w θ := by
  exact (probeLinearMap w θ).norm_coe_le_norm p

/-- The actual C0 seminorm is exactly the genuine two-sided tensor order-unit bound. -/
theorem formC0Seminorm_le_iff (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {r : ℝ} (hr : 0 ≤ r) :
    formC0Seminorm w θ ≤ r ↔
      (r • w.form + θ).val.IsSemipositive ∧ (r • w.form - θ).val.IsSemipositive := by
  rw [formC0Seminorm_eq, BoundedContinuousFunction.norm_le hr]
  constructor
  · intro h
    constructor <;> intro e z hz v
    · rcases eq_or_ne v 0 with rfl | hv
      · simp
      · let p : LineProbe n M := ⟨e, z, hz, v, hv⟩
        have hp := h p
        have hd := probe_denominator_pos w p
        change |normalizedProbe w θ p| ≤ r at hp
        have hl := (abs_le.mp hp).1
        have hl' := (le_div_iff₀ hd).mp hl
        simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
          ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
        change -r * _ ≤ _ at hl'
        change 0 ≤ r * _ + _
        linarith
    · rcases eq_or_ne v 0 with rfl | hv
      · simp
      · let p : LineProbe n M := ⟨e, z, hz, v, hv⟩
        have hp := h p
        have hd := probe_denominator_pos w p
        change |normalizedProbe w θ p| ≤ r at hp
        have hu := (abs_le.mp hp).2
        have hu' := (div_le_iff₀ hd).mp hu
        simp only [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add,
          ClosedRealOneOneForm.coeff_smul, ClosedRealOneOneForm.coeff_neg,
          ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
          ContinuousAlternatingMap.neg_apply, smul_eq_mul]
        change _ ≤ r * _ at hu'
        change 0 ≤ r * _ + -_
        linarith
  · rintro ⟨hlow, hupp⟩ p
    have hd := probe_denominator_pos w p
    have hl := hlow p.chart p.point p.mem_target p.vector
    have hu := hupp p.chart p.point p.mem_target p.vector
    simp only [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add,
      ClosedRealOneOneForm.coeff_smul, ClosedRealOneOneForm.coeff_neg,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
      ContinuousAlternatingMap.neg_apply, smul_eq_mul] at hl hu
    change |normalizedProbe w θ p| ≤ r
    apply abs_le.mpr
    constructor
    · apply (le_div_iff₀ hd).mpr
      linarith
    · apply (div_le_iff₀ hd).mpr
      linarith

/-- The actual directional C0 topology is induced from the genuine supremum-normed probe space. -/
abbrev formC0Topology (w : KahlerBackground n M) : TopologicalSpace (ClosedRealOneOneForm n M) :=
  TopologicalSpace.induced (probeLinearMap w) inferInstance

/-- Actual addition and negation are continuous for the intrinsic directional C0 topology. -/
theorem formC0Topology_isTopologicalAddGroup (w : KahlerBackground n M) :
    @IsTopologicalAddGroup (ClosedRealOneOneForm n M) (formC0Topology w) inferInstance :=
  topologicalAddGroup_induced (probeLinearMap w)

/-- Actual real scalar multiplication is continuous for the intrinsic directional C0 topology. -/
theorem formC0Topology_continuousSMul (w : KahlerBackground n M) :
    @ContinuousSMul ℝ (ClosedRealOneOneForm n M) inferInstance inferInstance (formC0Topology w) :=
  continuousSMul_induced (probeLinearMap w)

/-- The genuine seminorm balls are actual open sets in the induced supremum-norm topology. -/
theorem isOpen_formC0Seminorm_ball (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (r : ℝ) :
    @IsOpen (ClosedRealOneOneForm n M) (formC0Topology w) ((formC0Seminorm w).ball θ r) := by
  let : TopologicalSpace (ClosedRealOneOneForm n M) := formC0Topology w
  have heq : (formC0Seminorm w).ball θ r =
      probeLinearMap w ⁻¹' Metric.ball (probeLinearMap w θ) r := by
    ext η
    simp only [Seminorm.mem_ball, mem_preimage, Metric.mem_ball,
      formC0Seminorm_eq, dist_eq_norm, map_sub]
  rw [heq]
  exact Metric.isOpen_ball.preimage continuous_induced_dom

/-- Every actual C0 neighborhood contains a genuine actual seminorm ball. -/
theorem exists_formC0Seminorm_ball_subset (w : KahlerBackground n M)
    {U : Set (ClosedRealOneOneForm n M)}
    (hU : @IsOpen (ClosedRealOneOneForm n M) (formC0Topology w) U)
    {θ : ClosedRealOneOneForm n M} (hθ : θ ∈ U) :
    ∃ r : ℝ, 0 < r ∧ (formC0Seminorm w).ball θ r ⊆ U := by
  let : TopologicalSpace (ClosedRealOneOneForm n M) := formC0Topology w
  have hnhds : U ∈ 𝓝 θ := hU.mem_nhds hθ
  obtain ⟨V, hV, hVU⟩ := (mem_nhds_induced (probeLinearMap w) θ U).mp hnhds
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨r, hr, fun η hη => hVU (hrV ?_)⟩
  change dist (probeLinearMap w η) (probeLinearMap w θ) < r
  simpa only [Seminorm.mem_ball, dist_eq_norm, ← map_sub, ← formC0Seminorm_eq] using hη

/-- The actual background has intrinsic directional C0 seminorm at most one, also on an empty manifold. -/
theorem formC0Seminorm_background_le_one (w : KahlerBackground n M) :
    formC0Seminorm w w.form ≤ 1 := by
  rw [formC0Seminorm_eq, BoundedContinuousFunction.norm_le zero_le_one]
  intro p
  change |normalizedProbe w w.form p| ≤ 1
  simp only [normalizedProbe, div_self (ne_of_gt (probe_denominator_pos w p)), abs_one, le_refl]

/-- Actual C0 closeness produces the actual pointwise tensor error needed by smooth nef approximation. -/
theorem isSemipositive_sub_add_smul_of_formC0_lt (w : KahlerBackground n M)
    (θ η : ClosedRealOneOneForm n M) {ε : ℝ}
    (hε : formC0Seminorm w (η - θ) < ε) :
    (θ - η + ε • w.form).val.IsSemipositive := by
  have hn : 0 ≤ formC0Seminorm w (η - θ) := norm_nonneg (probeLinearMap w (η - θ))
  have hε0 : 0 ≤ ε := hn.trans hε.le
  have hsemi := ((formC0Seminorm_le_iff w (η - θ) hε0).mp hε.le).2
  have heq : ε • w.form - (η - θ) = θ - η + ε • w.form := by module
  rw [heq] at hsemi
  exact hsemi

/-- Different genuine backgrounds give equivalent actual directional C0 seminorms. -/
theorem exists_formC0Seminorm_comparison (w w' : KahlerBackground n M) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : ClosedRealOneOneForm n M,
      formC0Seminorm w θ ≤ C * formC0Seminorm w' θ := by
  obtain ⟨C, hC, hdom⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul w (-w'.form)
  refine ⟨C, hC, fun θ => ?_⟩
  have hpn : 0 ≤ formC0Seminorm w' θ := norm_nonneg (probeLinearMap w' θ)
  rw [formC0Seminorm_eq w θ, BoundedContinuousFunction.norm_le (mul_nonneg hC.le hpn)]
  intro p
  have hd := probe_denominator_pos w p
  have hd' := probe_denominator_pos w' p
  have ha := abs_normalizedProbe_le w' θ p
  have hp := hdom p.chart p.point p.mem_target p.vector
  simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
    ClosedRealOneOneForm.coeff_neg, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.neg_apply,
    smul_eq_mul] at hp
  simp only [normalizedProbe, abs_div, abs_of_pos hd'] at ha
  have ha' := (div_le_iff₀ hd').mp ha
  change |normalizedProbe w θ p| ≤ C * formC0Seminorm w' θ
  simp only [normalizedProbe, abs_div, abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  have hdom' : w'.form.val.coeff p.chart p.point ![p.vector, Complex.I • p.vector] ≤
      C * w.form.val.coeff p.chart p.point ![p.vector, Complex.I • p.vector] := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hdom' hpn]

/-- The genuine intrinsic directional C0 topology is independent of the genuine Kähler background. -/
theorem formC0Topology_eq_of_background (w w' : KahlerBackground n M) :
    formC0Topology w = formC0Topology w' := by
  have hopen : ∀ (a b : KahlerBackground n M) (U : Set (ClosedRealOneOneForm n M)),
      @IsOpen (ClosedRealOneOneForm n M) (formC0Topology a) U →
      @IsOpen (ClosedRealOneOneForm n M) (formC0Topology b) U := by
    intro a b U hU
    let : TopologicalSpace (ClosedRealOneOneForm n M) := formC0Topology b
    apply isOpen_iff_mem_nhds.mpr
    intro θ hθ
    obtain ⟨C, hC, hbound⟩ := exists_formC0Seminorm_comparison a b
    obtain ⟨r, hr, hrU⟩ := exists_formC0Seminorm_ball_subset a hU hθ
    have hδ : 0 < r / C := div_pos hr hC
    have hball := (isOpen_formC0Seminorm_ball b θ (r / C)).mem_nhds
      ((formC0Seminorm b).mem_ball_self hδ)
    apply mem_of_superset hball
    intro η hη
    apply hrU
    change formC0Seminorm a (η - θ) < r
    change formC0Seminorm b (η - θ) < r / C at hη
    have hsmall := mul_lt_mul_of_pos_left hη hC
    rw [mul_div_cancel₀ _ hC.ne'] at hsmall
    exact (hbound (η - θ)).trans_lt hsmall
  ext U
  exact ⟨hopen w w' U, hopen w' w U⟩

end

end SGPT.Foundations.Analysis.Pending.XiaoFormC0Topology
