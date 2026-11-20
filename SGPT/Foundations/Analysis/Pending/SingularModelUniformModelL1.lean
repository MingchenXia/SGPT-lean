import SGPT.Foundations.Analysis.Pending.SingularModelMeasureKahlerDomination
import SGPT.Foundations.Analysis.Pending.ThetaPshUniformL1Bound
import SGPT.Foundations.Analysis.Pending.SmoothMixedMeasureDensity

set_option autoImplicit false

/-!
# Actual uniform global L1 bounds for normalized theta-psh potentials

Independent globalization of the existing chart Harnack bound, using the
actual smooth mixed density and a finite Harnack-ball cover. The actual
singular model measure domination then supplies the uniform integral used
in Xia SGPT PDF0164, Lemma 4.3.3. No global-integral, density-bound or
measure-domination certificate is an input; poles and dimension zero remain.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal BigOperators

namespace SGPT.Foundations.Analysis.Pending.SingularModelUniformModelL1

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar DiagonalMass
  IntegrationCurrent ThetaPshUniformL1Bound SmoothMixedMeasureDensity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

private theorem exists_uniform_lintegral_neg_on_harnack_ball
    (θ : ClosedRealOneOneForm n M) (Ω : KahlerBackground n M)
    (H : HarnackBall θ.val) (c : ℝ) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ v : M → EReal, ThetaPlurisubharmonic θ.val v →
      (∀ x, v x ≤ 0) → (∃ x0, ((-c : ℝ) : EReal) ≤ v x0) →
        ∫⁻ x in H.set, (-v x).toENNReal ∂kahlerVolume Ω ≤ B := by
  have hKt : closedBall H.z H.r ⊆ H.e.val.target :=
    (closedBall_subset_closedBall (by linarith [H.r_pos])).trans
      (H.closedBall_subset.trans H.potential.2.1)
  let D := chartDensity (fun _ : Fin n => Ω.form) H.e
  obtain ⟨z, hz, hDz⟩ := (isCompact_closedBall H.z H.r).exists_isMaxOn
    ⟨H.z, mem_closedBall_self H.r_pos.le⟩
    ((continuousOn_chartDensity (fun _ => Ω.form) H.e).mono hKt)
  have hDfin : D z < ⊤ := ENNReal.ofReal_lt_top
  obtain ⟨B, hB, hBv⟩ := H.exists_lintegral_le
    (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) c
  refine ⟨D z * B, ENNReal.mul_lt_top hDfin hB, ?_⟩
  intro v hv hv0 hvnorm
  have himage : H.set = H.e.val.symm '' ball H.z H.r := by
    ext x
    constructor
    · intro hx
      exact ⟨H.e.val x, hx.2, H.e.val.left_inv hx.1⟩
    · rintro ⟨y, hy, rfl⟩
      exact H.symm_mem_set hy
  have hmeas : Measurable (fun x => (-v x).toENNReal) :=
    hv.quasiPlurisubharmonic.upperSemicontinuous.measurable.neg.ereal_toENNReal
  have h0Ω : IsThetaPshPotential Ω.form.val (fun _ => (0 : EReal)) :=
    (LocalPotentials.isThetaPshPotential_zero_iff Ω.form).mpr Ω.isSemipositive
  rw [himage, kahlerVolume, diagonalPotentialMeasure,
    setLIntegral_image_eq (fun _ => h0Ω.1) H.e measurableSet_ball H.ball_subset_target hmeas]
  calc
    (∫⁻ y in ball H.z H.r, chartDensity (fun _ => Ω.form) H.e y *
        (-v (H.e.val.symm y)).toENNReal) ≤
      ∫⁻ y in ball H.z H.r, D z * (-v (H.e.val.symm y)).toENNReal := by
        apply lintegral_mono_ae
        exact (ae_restrict_iff' measurableSet_ball).mpr
          (Eventually.of_forall fun y hy =>
            mul_le_mul' (hDz (Metric.ball_subset_closedBall hy)) le_rfl)
    _ = D z * (∫⁻ y in ball H.z H.r, (-v (H.e.val.symm y)).toENNReal) :=
      lintegral_const_mul' _ _ hDfin.ne
    _ ≤ D z * B := mul_le_mul' le_rfl (hBv v hv hv0 hvnorm)

/-- Actual smooth chart density and a finite Harnack cover produce a global uniform volume integral. -/
theorem exists_uniform_lintegral_neg_le_kahlerVolume
    (θ : ClosedRealOneOneForm n M) (Ω : KahlerBackground n M) (c : ℝ) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ v : M → EReal, ThetaPlurisubharmonic θ.val v →
      (∀ x, v x ≤ 0) → (∃ x0, ((-c : ℝ) : EReal) ≤ v x0) →
        ∫⁻ x, (-v x).toENNReal ∂kahlerVolume Ω ≤ B := by
  classical
  have hθ := LocalPotentials.closedRealOneOne_hasLocalPotentials θ
  have hex : ∀ x : M, ∃ Hx : HarnackBall θ.val,
      Hx.e = complexChartAt (n := n) x ∧
        Hx.z = (complexChartAt (n := n) x).val x ∧ Hx.r < 1 := fun x =>
    exists_harnackBall hθ _ ((complexChartAt (n := n) x).val.map_source
      (mem_complexChartAt_source x)) one_pos
  choose Hx hHxe hHxz _ using hex
  have hmem : ∀ x, x ∈ (Hx x).set := by
    intro x
    refine ⟨by rw [hHxe]; exact mem_complexChartAt_source x, ?_⟩
    rw [mem_preimage, hHxe, ← hHxz]
    exact mem_ball_self (Hx x).r_pos
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (Hx x).set)
    (fun x => (Hx x).isOpen_set) (fun x _ => mem_iUnion.mpr ⟨x, hmem x⟩)
  choose B hB hBv using fun x => exists_uniform_lintegral_neg_on_harnack_ball θ Ω (Hx x) c
  refine ⟨∑ x ∈ s, B x, ENNReal.sum_lt_top.mpr (fun x _ => hB x), ?_⟩
  intro v hv hv0 hvnorm
  calc
    (∫⁻ x, (-v x).toENNReal ∂kahlerVolume Ω) =
        ∫⁻ x in univ, (-v x).toENNReal ∂kahlerVolume Ω := by simp
    _ ≤ ∫⁻ x in ⋃ a ∈ s, (Hx a).set, (-v x).toENNReal ∂kahlerVolume Ω :=
      lintegral_mono_set hs
    _ ≤ ∑ a ∈ s, ∫⁻ x in (Hx a).set, (-v x).toENNReal ∂kahlerVolume Ω :=
      ThetaPshUniformL1Bound.lintegral_biUnion_finset_le _ _ _ _
    _ ≤ ∑ a ∈ s, B a := Finset.sum_le_sum fun a _ => hBv a v hv hv0 hvnorm

/-- Actual enlarged smooth volume domination transfers the produced uniform integral to the model measure. -/
theorem exists_uniform_lintegral_neg_le_modelMeasure
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {φ : M → EReal} (hφ : IsModelPotential θ φ) (c : ℝ) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ v : M → EReal, ThetaPlurisubharmonic θ.val v →
      (∀ x, v x ≤ 0) → (∃ x0, ((-c : ℝ) : EReal) ≤ v x0) →
        ∫⁻ x, (-v x).toENNReal ∂diagonalPotentialMeasure θ φ hφ.plurisubharmonic ≤ B := by
  obtain ⟨A, hA, _, hdom⟩ :=
    SingularModelMeasureKahlerDomination.exists_pos_scaled_kahlerVolume_model_domination
      (hφ := hφ) omega
  obtain ⟨B, hB, hBv⟩ := exists_uniform_lintegral_neg_le_kahlerVolume θ
    (KahlerBackground.smul hA omega) c
  refine ⟨B, hB, fun v hv hv0 hvnorm => ?_⟩
  exact (lintegral_mono' hdom le_rfl).trans (hBv v hv hv0 hvnorm)

end

end SGPT.Foundations.Analysis.Pending.SingularModelUniformModelL1
