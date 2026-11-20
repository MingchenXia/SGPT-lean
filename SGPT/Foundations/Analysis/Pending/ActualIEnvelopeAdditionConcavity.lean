import SGPT.Foundations.Analysis.Pending.ActualMultiplierOrderAddition
import SGPT.Foundations.Analysis.Pending.ActualIEnvelopePositiveScaling

set_option autoImplicit false

/-! # Actual I-envelope addition and strict convex-combination inequalities -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualIEnvelopeAdditionConcavity

open FirstPass FirstPass.IEnvelope FirstPass.PositiveClasses
  MixedSummandCapacityDomination GlobalMultilinearExpansion ActualMultiplierOrderAddition
  ActualIEnvelopePositiveScaling

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem genuineAdd {θ σ : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v) :
    IsThetaPshPotential (θ + σ).val (fun x => u x + v x) := by
  classical
  let α : Bool → ClosedRealOneOneForm n M := fun b => if b then θ else σ
  let f : Bool → M → EReal := fun b => if b then u else v
  have hf (b : Bool) : IsThetaPshPotential (α b).val (f b) := by
    cases b
    · exact hv
    · exact hu
  have h := isThetaPshPotential_sumPot (T := Finset.univ)
    (w := fun _ : Bool => (1 : ℝ)) Finset.univ_nonempty (fun _ => zero_lt_one) hf
  have hQ : sumPot Finset.univ (fun _ : Bool => (1 : ℝ)) f = fun x => u x + v x := by
    funext x
    simp only [sumPot, Fintype.sum_bool, f, Bool.false_eq_true,
      ↓reduceIte, EReal.coe_one, one_mul]
  rw [hQ] at h
  simpa only [sumForm, Fintype.sum_bool, α, Bool.false_eq_true,
    ↓reduceIte, one_smul] using h

variable [CompactSpace M] [Nonempty M]

/-- A genuine normalized sum competitor is produced using the actual all-level
multiplier equivalence of the inputs and their I-envelopes. -/
theorem iSingularityEnvelope_add_le {θ σ : ClosedRealOneOneForm n M}
    {u v : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential σ.val v) :
    (fun x => iSingularityEnvelope θ.val u x + iSingularityEnvelope σ.val v x) ≤
      iSingularityEnvelope (θ + σ).val (fun x => u x + v x) := by
  have hp : IsThetaPshPotential θ.val (iSingularityEnvelope θ.val u) :=
    iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      hu.1.hasSmoothLocalPotentials u hu
  have hq : IsThetaPshPotential σ.val (iSingularityEnvelope σ.val v) :=
    iSingularityEnvelope_isThetaPshPotential σ.val σ.property.1 σ.property.2
      hv.1.hasSmoothLocalPotentials v hv
  have h0 : (fun x => iSingularityEnvelope θ.val u x +
      iSingularityEnvelope σ.val v x) ≤ 0 := by
    intro x
    exact (add_le_add (iSingularityEnvelope_le_zero θ.val u x)
      (iSingularityEnvelope_le_zero σ.val v x)).trans_eq (zero_add 0)
  have hIp := (iEquivalent_iSingularityEnvelope θ.val θ.property.1 θ.property.2
    hu.1.hasSmoothLocalPotentials u hu).symm
  have hIq := (iEquivalent_iSingularityEnvelope σ.val σ.property.1 σ.property.2
    hv.1.hasSmoothLocalPotentials v hv).symm
  exact le_iSingularityEnvelope (genuineAdd hp hq) h0
    (iEquivalentOnManifold_add hp hq hu hv hIp hIq)

/-- The actual positive scalar covariance and addition inequality give the
strict convex-combination inequality in the original background. -/
theorem iSingularityEnvelope_convexCombination_le {θ : ClosedRealOneOneForm n M}
    {u v : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (fun x => ((1 - t : ℝ) : EReal) * iSingularityEnvelope θ.val u x +
      (t : EReal) * iSingularityEnvelope θ.val v x) ≤
      iSingularityEnvelope θ.val
        (fun x => ((1 - t : ℝ) : EReal) * u x + (t : EReal) * v x) := by
  have ha : 0 < 1 - t := sub_pos.mpr ht1
  have hau : IsThetaPshPotential ((1 - t) • θ).val
      (fun x => ((1 - t : ℝ) : EReal) * u x) :=
    RestrictedApproximantComparison.isThetaPshPotential_smul hu ha
  have hbv : IsThetaPshPotential (t • θ).val
      (fun x => (t : EReal) * v x) :=
    RestrictedApproximantComparison.isThetaPshPotential_smul hv ht0
  have hθ : (1 - t) • θ + t • θ = θ := by
    rw [← add_smul, sub_add_cancel, one_smul]
  have h := iSingularityEnvelope_add_le hau hbv
  rw [hθ] at h
  simpa only [iSingularityEnvelope_smul θ hu ha,
    iSingularityEnvelope_smul θ hv ht0] using h

end

end SGPT.Foundations.Analysis.Pending.ActualIEnvelopeAdditionConcavity
