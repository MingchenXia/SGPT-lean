import SGPT.Foundations.Analysis.Pending.IncreasingPositiveMassAffineBarriers
import SGPT.Foundations.Analysis.Pending.ActualIEnvelopeAdditionConcavity
import SGPT.Foundations.Analysis.Pending.ActualIEnvelopeUniformL1Vanishing
import SGPT.Foundations.Analysis.Pending.ActualIEnvelopeOrderInfimum
import SGPT.Foundations.Analysis.Pending.ThetaPshL1Order
import SGPT.Foundations.Analysis.Pending.IncreasingMixedDirectedNets

set_option autoImplicit false

/-! # Literal I-envelope continuity at genuine positive increasing regularized limits -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.IEnvelopeIncreasingRegularizedSupremum

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.IEnvelope
  ThetaPshConvexCombination IncreasingPositiveMassAffineBarriers
  ActualIEnvelopeAdditionConcavity ActualIEnvelopeUniformL1Vanishing
  ActualIEnvelopeOrderInfimum IncreasingMixedDirectedNets ChartwiseGlobalL1
  ThetaPshL1Order DiagonalMass IntegrationCurrent

noncomputable section

/-- An actual normalized affine lower bound controls the canonical gap,
including common and one-sided negative-infinite poles. -/
theorem canonical_gap_le_scaled_normalized_lower
    {p h q : EReal} {t : ℝ} (hp0 : p ≤ 0) (hq0 : q ≤ 0)
    (hhp : h ≤ p) (ht0 : 0 < t)
    (hlow : (t : EReal) * q + ((1 - t : ℝ) : EReal) * p ≤ h) :
    canonicalERealAbsDiff h p ≤ canonicalERealAbsDiff ((t : EReal) * q) 0 := by
  induction p using EReal.rec with
  | bot =>
      have hh : h = ⊥ := le_bot_iff.mp hhp
      simp only [hh, canonicalERealAbsDiff_bot_bot]
      exact zero_le
  | top => simp at hp0
  | coe p =>
      induction q using EReal.rec with
      | bot =>
          rw [EReal.coe_mul_bot_of_pos ht0, canonicalERealAbsDiff_bot_left (by simp)]
          exact le_top
      | top => simp at hq0
      | coe q =>
          have hpr : p ≤ 0 := by exact_mod_cast hp0
          have hqr : q ≤ 0 := by exact_mod_cast hq0
          rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at hlow
          induction h using EReal.rec with
          | bot =>
              exact False.elim ((EReal.coe_ne_bot _) (le_bot_iff.mp hlow))
          | top => simp at hhp
          | coe h =>
              have hhr : h ≤ p := EReal.coe_le_coe_iff.mp hhp
              have hlr : t * q + (1 - t) * p ≤ h := EReal.coe_le_coe_iff.mp hlow
              rw [← EReal.coe_mul, ← EReal.coe_zero,
                canonicalERealAbsDiff_coe_coe, canonicalERealAbsDiff_coe_coe]
              apply ENNReal.ofReal_le_ofReal
              rw [sub_zero, abs_of_nonpos (sub_nonpos.mpr hhr),
                abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos ht0.le hqr)]
              nlinarith [mul_nonpos_of_nonneg_of_nonpos ht0.le hpr]


variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Genuine increasing positive limits commute literally with the actual
I-envelope; uniform canonical L1 and actual PSH order identify the functions. -/
theorem iSingularityEnvelope_regularized_iSup_eq
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {v : ℕ → M → EReal} {u : M → EReal}
    (hv : ∀ j, IsThetaPshPotential θ.val (v j)) (hmono : Monotone v)
    (hu : IsThetaPshPotential θ.val u) (hreg : uscRegularization (⨆ j, v j) = u)
    (hpos : HasPositivePotentialMass θ u hu) :
    uscRegularization (⨆ j, iSingularityEnvelope θ.val (v j)) =
      iSingularityEnvelope θ.val u := by
  let P : M → EReal := iSingularityEnvelope θ.val u
  let B : ℕ → M → EReal := fun j => iSingularityEnvelope θ.val (v j)
  let H : M → EReal := uscRegularization (⨆ j, B j)
  have hP : IsThetaPshPotential θ.val P :=
    iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      hu.1.hasSmoothLocalPotentials u hu
  have hB : ∀ j, IsThetaPshPotential θ.val (B j) := fun j =>
    iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      (hv j).1.hasSmoothLocalPotentials (v j) (hv j)
  have hH : IsThetaPshPotential θ.val H :=
    isThetaPshPotential_regularized_of_uniformlyBounded hB
      (fun j => iSingularityEnvelope_le_zero θ.val (v j))
  have hvu (j : ℕ) : v j ≤ u := by
    rw [← hreg]
    exact (le_iSup v j).trans (le_uscRegularization _)
  have hBP (j : ℕ) : B j ≤ P :=
    iSingularityEnvelope_le_of_iOrderOnManifold θ hu
      (iOrderOnManifold_of_le hu.1.quasiPlurisubharmonic (hvu j))
  have hHP : H ≤ P := uscRegularization_le
    hP.1.quasiPlurisubharmonic.upperSemicontinuous (iSup_le hBP)
  obtain ⟨N, _hN, ε, hε, η, hη, hbar⟩ :=
    exists_vanishing_affine_barriers_of_monotone_regularized
      omega θ hbig hv hmono hu hreg hpos
  have hlow (j : ℕ) :
      (fun x => ((ε j).val : EReal) * iSingularityEnvelope θ.val (η j) x +
        ((1 - (ε j).val : ℝ) : EReal) * P x) ≤ H := by
    have hconc := iSingularityEnvelope_convexCombination_le (hη j) hu
      (sub_pos.mpr (ε j).property.2) (sub_lt_self 1 (ε j).property.1)
    have heq : (fun x => ((1 - (1 - (ε j).val) : ℝ) : EReal) * η j x +
        ((1 - (ε j).val : ℝ) : EReal) * u x) = convexComb (ε j).val (η j) u := by
      funext x
      simp only [sub_sub_cancel, convexComb]
    rw [heq] at hconc
    have horder : iSingularityEnvelope θ.val (convexComb (ε j).val (η j) u) ≤ B (N j) :=
      iSingularityEnvelope_le_of_iOrderOnManifold θ (hv (N j))
        (iOrderOnManifold_of_le (hv (N j)).1.quasiPlurisubharmonic (hbar j))
    have hBH : B (N j) ≤ H := (le_iSup B (N j)).trans (le_uscRegularization _)
    intro x
    have hc := hconc x
    simp only [sub_sub_cancel] at hc
    exact hc.trans ((horder x).trans (hBH x))
  have hbound (j : ℕ) : globalL1EDistance (kahlerVolume omega) H P ≤
      globalL1EDistance (kahlerVolume omega)
        (fun x => ((ε j).val : EReal) * iSingularityEnvelope θ.val (η j) x)
        (fun _ => 0) := by
    apply lintegral_mono
    intro x
    exact canonical_gap_le_scaled_normalized_lower
      (iSingularityEnvelope_le_zero θ.val u x)
      (iSingularityEnvelope_le_zero θ.val (η j) x)
      (hHP x) (ε j).property.1 (hlow j x)
  have hupper := (tendsto_global_and_manifoldL1_iSingularityEnvelope_smul
    omega θ atTop η hη (fun j => (ε j).val) (fun j => (ε j).property.1) hε).1
  have hlim : Tendsto (fun _ : ℕ => globalL1EDistance (kahlerVolume omega) H P)
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hupper (fun _ => zero_le) hbound
  have hloc : ManifoldL1LocallyTendsto (n := n) (fun _ : ℕ => H) atTop P :=
    (manifoldL1LocallyTendsto_iff_tendsto_globalL1EDistance
      (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega)
      (fun _ => hH.1.quasiPlurisubharmonic.upperSemicontinuous.measurable)
      hP.1.quasiPlurisubharmonic.upperSemicontinuous.measurable).mpr hlim
  have hPH : P ≤ H := le_of_manifoldL1LocallyTendsto
    (fun _ => hH) hP hH hloc (fun _ => le_refl H)
  exact le_antisymm hHP hPH

end

end SGPT.Foundations.Analysis.Pending.IEnvelopeIncreasingRegularizedSupremum
