import SGPT.Foundations.Analysis.Pending.IEnvelopeAnalytic
import SGPT.Foundations.Analysis.Pending.POrderAffineRooftop
import SGPT.Foundations.Analysis.Pending.SingularModelUniformModelL1
import SGPT.Foundations.Analysis.Pending.KahlerVolumeSmoothPositive
import SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1

set_option autoImplicit false

/-! # Actual normalized I-envelopes and their vanishing global and chart-local L1 perturbations -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualIEnvelopeUniformL1Vanishing

open FirstPass FirstPass.IEnvelope FirstPass.PositiveClasses
  IntegrationCurrent ChartwiseGlobalL1

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M]

/-- A finite attained maximum produces a literal zero point of the actual I-envelope. -/
theorem exists_iSingularityEnvelope_eq_zero (θ : ClosedRealOneOneForm n M)
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u) :
    ∃ x : M, iSingularityEnvelope θ.val u x = 0 := by
  obtain ⟨x, m, hxm, hmax⟩ := hu.exists_max
  have hnorm : ∀ y, u y - (m : EReal) ≤ 0 := by
    intro y
    have h := add_le_add (hmax y) (le_refl ((-m : ℝ) : EReal))
    simpa only [sub_eq_add_neg, ← EReal.coe_neg, ← EReal.coe_add,
      add_neg_cancel, EReal.coe_zero] using h
  have hle := le_iSingularityEnvelope (hu.sub_const m) hnorm
    (iEquivalentOnManifold_sub_const u m)
  refine ⟨x, le_antisymm (iSingularityEnvelope_le_zero θ.val u x) ?_⟩
  have hx0 : u x - (m : EReal) = 0 := by
    rw [hxm, ← EReal.coe_sub, sub_self, EReal.coe_zero]
  simpa only [hx0] using hle x

private theorem canonicalAbsDiff_smul_zero {p : EReal} (hp : p ≤ 0)
    {a : ℝ} (ha : 0 < a) :
    canonicalERealAbsDiff ((a : EReal) * p) 0 =
      ENNReal.ofReal a * (-p).toENNReal := by
  induction p using EReal.rec with
  | bot =>
      simp [EReal.coe_mul_bot_of_pos ha, ENNReal.ofReal_pos.mpr ha |>.ne']
  | top => simp at hp
  | coe r =>
      have hr : r ≤ 0 := EReal.coe_le_coe_iff.mp hp
      rw [← EReal.coe_mul, ← EReal.coe_zero, canonicalERealAbsDiff_coe_coe,
        sub_zero, abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos ha.le hr),
        ← EReal.coe_neg, EReal.real_coe_toENNReal, neg_mul_eq_mul_neg,
        ENNReal.ofReal_mul ha.le]

/-- Internally normalized I-envelopes have uniformly controlled canonical L1 perturbations,
so arbitrary positive coefficients tending to zero give actual global and chart-local limits. -/
theorem tendsto_global_and_manifoldL1_iSingularityEnvelope_smul
    [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M]
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {I : Type*} (F : Filter I) (ψ : I → M → EReal)
    (hψ : ∀ i, IsThetaPshPotential θ.val (ψ i)) (ε : I → ℝ)
    (hεpos : ∀ i, 0 < ε i) (hε : Tendsto ε F (𝓝 0)) :
    Tendsto (fun i => globalL1EDistance (kahlerVolume omega)
      (fun x => (ε i : EReal) * iSingularityEnvelope θ.val (ψ i) x)
      (fun _ => 0)) F (𝓝 0) ∧
    ManifoldL1LocallyTendsto (n := n)
      (fun i x => (ε i : EReal) * iSingularityEnvelope θ.val (ψ i) x)
      F (fun _ => 0) := by
  have hpi : ∀ i, IsThetaPshPotential θ.val (iSingularityEnvelope θ.val (ψ i)) :=
    fun i => iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      (hψ i).1.hasSmoothLocalPotentials (ψ i) (hψ i)
  have hp0 : ∀ i x, iSingularityEnvelope θ.val (ψ i) x ≤ 0 :=
    fun i => iSingularityEnvelope_le_zero θ.val (ψ i)
  obtain ⟨B, hB, hBv⟩ :=
    SingularModelUniformModelL1.exists_uniform_lintegral_neg_le_kahlerVolume θ omega 0
  have hbound : ∀ i, globalL1EDistance (kahlerVolume omega)
      (fun x => (ε i : EReal) * iSingularityEnvelope θ.val (ψ i) x)
      (fun _ => 0) ≤ ENNReal.ofReal (ε i) * B := by
    intro i
    obtain ⟨x, hx⟩ := exists_iSingularityEnvelope_eq_zero θ (hψ i)
    have hnorm : ∃ x0, ((-0 : ℝ) : EReal) ≤ iSingularityEnvelope θ.val (ψ i) x0 :=
      ⟨x, by rw [hx]; simp⟩
    change (∫⁻ x, canonicalERealAbsDiff
      ((ε i : EReal) * iSingularityEnvelope θ.val (ψ i) x) 0
      ∂kahlerVolume omega) ≤ _
    simp_rw [canonicalAbsDiff_smul_zero (hp0 i _) (hεpos i)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul' le_rfl (hBv _ (hpi i).1 (hp0 i) hnorm)
  have hcoeff : Tendsto (fun i => ENNReal.ofReal (ε i)) F (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hε
  have hupper : Tendsto (fun i => ENNReal.ofReal (ε i) * B) F (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const hcoeff (Or.inr hB.ne)
  have hlim := tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper (fun _ => zero_le) hbound
  refine ⟨hlim, ?_⟩
  exact (manifoldL1LocallyTendsto_iff_tendsto_globalL1EDistance
    (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega)
    (fun i => (upperSemicontinuous_eReal_const_mul
      (hpi i).1.quasiPlurisubharmonic.upperSemicontinuous (hεpos i).le).measurable)
    measurable_const).mpr hlim

end

end SGPT.Foundations.Analysis.Pending.ActualIEnvelopeUniformL1Vanishing
