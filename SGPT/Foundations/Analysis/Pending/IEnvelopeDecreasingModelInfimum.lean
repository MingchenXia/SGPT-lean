import SGPT.Foundations.Analysis.Pending.IEnvelopeIncreasingRegularizedSupremum
import SGPT.Foundations.Analysis.Pending.ActualDecreasingModelInfimum

set_option autoImplicit false

/-! # Literal I-envelope commutation with positive decreasing model sequence infima -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.IEnvelopeDecreasingModelInfimum

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.IEnvelope
  ActualDecreasingModelInfimum PositiveCurrentRooftop DiagonalMass MixedMass
  ThetaPshConvexCombination ActualIEnvelopeAdditionConcavity
  ActualIEnvelopeUniformL1Vanishing ActualIEnvelopeOrderInfimum
  IEnvelopeIncreasingRegularizedSupremum ThetaPshDecreasingLimit
  ChartwiseGlobalL1 ThetaPshL1Order IntegrationCurrent

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Genuine positive decreasing model infima commute literally with the
actual I-envelope, by internal affine barriers and canonical local L1 order. -/
theorem iInf_iSingularityEnvelope_eq
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {v : ℕ → M → EReal} (hv : ∀ j, IsModelPotential θ (v j))
    (hanti : Antitone v)
    (hpos : HasPositivePotentialMass θ (⨅ j, v j)
      (isThetaPshPotential_iInf_of_antitone_model hv hanti)) :
    (⨅ j, iSingularityEnvelope θ.val (v j)) =
      iSingularityEnvelope θ.val (⨅ j, v j) := by
  classical
  let u : M → EReal := ⨅ j, v j
  have hu : IsThetaPshPotential θ.val u :=
    isThetaPshPotential_iInf_of_antitone_model hv hanti
  let P : M → EReal := iSingularityEnvelope θ.val u
  let B : ℕ → M → EReal := fun j => iSingularityEnvelope θ.val (v j)
  let H : M → EReal := ⨅ j, B j
  have hP : IsThetaPshPotential θ.val P :=
    iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      hu.1.hasSmoothLocalPotentials u hu
  have hB (j : ℕ) : IsThetaPshPotential θ.val (B j) :=
    iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      (hv j).plurisubharmonic.1.hasSmoothLocalPotentials (v j) (hv j).plurisubharmonic
  have huj (j : ℕ) : u ≤ v j := iInf_le v j
  have hPB (j : ℕ) : P ≤ B j :=
    iSingularityEnvelope_le_of_iOrderOnManifold θ (hv j).plurisubharmonic
      (iOrderOnManifold_of_le (hv j).plurisubharmonic.1.quasiPlurisubharmonic (huj j))
  have hPH : P ≤ H := le_iInf hPB
  have hBanti : Antitone B := by
    intro i j hij
    exact iSingularityEnvelope_le_of_iOrderOnManifold θ (hv i).plurisubharmonic
      (iOrderOnManifold_of_le (hv i).plurisubharmonic.1.quasiPlurisubharmonic (hanti hij))
  have hH : IsThetaPshPotential θ.val H := by
    constructor
    · have heq : H = (fun x => ⨅ j, B j x) := by
        funext x
        exact iInf_apply
      rw [heq]
      exact thetaPlurisubharmonic_iInf_of_antitone
        (fun j => (hB j).1) (fun x _ _ hij => hBanti hij x)
    · exact hP.2.mono hPH
  have hH0 : H ≤ 0 :=
    (iInf_le B 0).trans (iSingularityEnvelope_le_zero θ.val (v 0))
  let m : ℕ → ℝ≥0∞ := fun j => diagonalPotentialMass θ (v j) (hv j).plurisubharmonic
  let L : ℝ≥0∞ := diagonalPotentialMass θ u hu
  have hL : 0 < L := hpos
  have hLtop : L ≠ ⊤ := (globalMixedMass_lt_top omega
    (fun _ : Fin n => hu.1)).ne
  have hm : Tendsto m atTop (𝓝 L) :=
    tendsto_diagonalPotentialMass_iInf_of_antitone_model omega hv hanti hpos
  have hselect (r : ℕ) : ∃ j : ℕ, r ≤ j ∧
      ConvexCombEnvelopeMass.IsAdmissibleWeight n L (m j) ((r : ℝ) + 2) := by
    have ha : (1 : ℝ) < (r : ℝ) + 2 := by
      have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
      linarith
    have hadm := eventually_isAdmissibleWeight (n := n)
      (a := fun _ => L) hL hLtop (fun _ => le_refl L) hm ha
    exact ((eventually_ge_atTop r).and hadm).exists
  choose N _hN hAdm using hselect
  have hbar (r : ℕ) : ∃ η : M → EReal,
      IsThetaPshPotential θ.val η ∧
      convexComb ((r : ℝ) + 2)⁻¹ η (v (N r)) ≤ u :=
    exists_thetaPsh_convexCombBarrier_of_isBigClass omega θ hbig
      hu (hv (N r)).plurisubharmonic (huj (N r)) hL (hAdm r)
  choose η hη hbarη using hbar
  let ε : ℕ → Ioo (0 : ℝ) 1 := fun r => ⟨((r : ℝ) + 2)⁻¹, by
    constructor
    · positivity
    · exact inv_lt_one_of_one_lt₀ (by
        have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
        linarith)⟩
  have hε : Tendsto (fun r => (ε r).val) atTop (𝓝 (0 : ℝ)) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, ε, Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two, one_div] using hh
  have hlow (r : ℕ) : (fun x => ((ε r).val : EReal) *
      iSingularityEnvelope θ.val (η r) x +
      ((1 - (ε r).val : ℝ) : EReal) * H x) ≤ P := by
    have hc := iSingularityEnvelope_convexCombination_le
      (hη r) (hv (N r)).plurisubharmonic
      (sub_pos.mpr (ε r).property.2) (sub_lt_self 1 (ε r).property.1)
    have heq : (fun x => ((1 - (1 - (ε r).val) : ℝ) : EReal) * η r x +
        ((1 - (ε r).val : ℝ) : EReal) * v (N r) x) =
        convexComb (ε r).val (η r) (v (N r)) := by
      funext x
      simp only [sub_sub_cancel, convexComb]
    rw [heq] at hc
    have horder : iSingularityEnvelope θ.val
        (convexComb (ε r).val (η r) (v (N r))) ≤ P :=
      iSingularityEnvelope_le_of_iOrderOnManifold θ hu
        (iOrderOnManifold_of_le hu.1.quasiPlurisubharmonic (hbarη r))
    intro x
    have hHB : H x ≤ B (N r) x := iInf_le B (N r) x
    have hs : ((1 - (ε r).val : ℝ) : EReal) * H x ≤
        ((1 - (ε r).val : ℝ) : EReal) * B (N r) x :=
      mul_le_mul_of_nonneg_left hHB (by exact_mod_cast (sub_pos.mpr (ε r).property.2).le)
    have hh := hc x
    simp only [sub_sub_cancel] at hh
    exact (add_le_add (le_refl _) hs).trans (hh.trans (horder x))
  have hbound (r : ℕ) : globalL1EDistance (kahlerVolume omega) P H ≤
      globalL1EDistance (kahlerVolume omega)
        (fun x => ((ε r).val : EReal) * iSingularityEnvelope θ.val (η r) x)
        (fun _ => 0) := by
    apply lintegral_mono
    intro x
    exact canonical_gap_le_scaled_normalized_lower (hH0 x)
      (iSingularityEnvelope_le_zero θ.val (η r) x)
      (hPH x) (ε r).property.1 (hlow r x)
  have hupper := (tendsto_global_and_manifoldL1_iSingularityEnvelope_smul
    omega θ atTop η hη (fun r => (ε r).val) (fun r => (ε r).property.1) hε).1
  have hlim : Tendsto (fun _ : ℕ => globalL1EDistance (kahlerVolume omega) P H)
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hupper (fun _ => zero_le) hbound
  have hloc : ManifoldL1LocallyTendsto (n := n) (fun _ : ℕ => P) atTop H :=
    (manifoldL1LocallyTendsto_iff_tendsto_globalL1EDistance
      (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega)
      (fun _ => hP.1.quasiPlurisubharmonic.upperSemicontinuous.measurable)
      hH.1.quasiPlurisubharmonic.upperSemicontinuous.measurable).mpr hlim
  have hHP : H ≤ P := le_of_manifoldL1LocallyTendsto
    (fun _ => hP) hH hP hloc (fun _ => le_refl P)
  exact le_antisymm hHP hPH

end

end SGPT.Foundations.Analysis.Pending.IEnvelopeDecreasingModelInfimum
