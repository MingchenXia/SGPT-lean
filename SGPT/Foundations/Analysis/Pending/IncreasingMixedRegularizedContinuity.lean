import SGPT.Foundations.Analysis.Pending.IncreasingMixedContinuity
import SGPT.Foundations.Analysis.Pending.IncreasingThetaPshChartL1
import SGPT.Foundations.Analysis.PlurisubharmonicAE

set_option autoImplicit false

/-!
# Increasing mixed products at genuine regularized suprema

Xia, Corollary 2.4.1, independent-background increasing sequence case.
Chart almost-everywhere recovery and actual PSH/USC comparison identify
regularized positive subset sums, including negative-infinite poles.
-/

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace SGPT.Foundations.Analysis.Pending.IncreasingMixedRegularizedContinuity

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar DiagonalMass
open GlobalMultilinearExpansion MixedSummandCapacityDomination
open MixedProductIntegralPolarization IncreasingDiagonalContinuity
open IncreasingMixedContinuity IncreasingThetaPshChartL1

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Genuine increasing regularized limits agree with raw suprema almost everywhere
in every chart without a normalization premise. -/
theorem ae_chartFunction_iSup_eq_of_genuine
    {theta : ClosedRealOneOneForm n M} {g : ℕ → M → EReal}
    (hg : ∀ j, IsThetaPshPotential theta.val (g j)) (hmono : Monotone g)
    (hU : IsThetaPshPotential theta.val (uscRegularization (⨆ j, g j)))
    (e : ComplexChart n M) :
    ∀ᵐ z ∂(volume.restrict e.val.target),
      (⨆ j, chartFunction (g j) e z) =
        chartFunction (uscRegularization (⨆ j, g j)) e z := by
  classical
  by_cases hM : Nonempty M
  · let : Nonempty M := hM
    obtain ⟨C, hC⟩ := hU.exists_global_upper_bound
    let v : ℕ → M → EReal := fun j x => g j x + ((-C : ℝ) : EReal)
    have hv : ∀ j, IsThetaPshPotential theta.val (v j) := fun j => (hg j).add_const (-C)
    have hv0 : ∀ j, v j ≤ 0 := by
      intro j x
      have hgle : g j x ≤ (C : EReal) :=
        (le_iSup (fun k => g k) j x).trans
          ((le_uscRegularization _ x).trans (hC x))
      change g j x + ((-C : ℝ) : EReal) ≤ 0
      calc
        _ ≤ (C : EReal) + ((-C : ℝ) : EReal) := add_le_add hgle le_rfl
        _ = 0 := by rw [← EReal.coe_add]; simp
    have hvm : Monotone v := fun j k hjk x => add_le_add (hmono hjk x) le_rfl
    have hsup : (⨆ j, v j) = fun x => (⨆ j, g j) x + ((-C : ℝ) : EReal) := by
      funext x
      simp only [iSup_apply, v]
      exact iSup_add_coe (fun j => g j x) (-C)
    have heq : uscRegularization (⨆ j, v j) =
        fun x => uscRegularization (⨆ j, g j) x + ((-C : ℝ) : EReal) := by
      rw [hsup, uscRegularization_add_coe_const]
    have hae := ae_chartFunction_iSup_eq hv hv0 hvm heq e
    filter_upwards [hae] with z hz
    have hz' : (⨆ j, chartFunction (g j) e z) + ((-C : ℝ) : EReal) =
        chartFunction (uscRegularization (⨆ j, g j)) e z + ((-C : ℝ) : EReal) := by
      simpa only [chartFunction, v, iSup_add_coe] using hz
    exact eReal_add_coe_right_cancel hz'
  · have ht : e.val.target = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hM ⟨e.val.symm z⟩
    simp [ht]

/-- The raw supremum of each positive subset sum is the sum of the individual
regularized limits almost everywhere in each chart. -/
theorem ae_chartFunction_iSup_subsetSum
    {theta : Fin n → ClosedRealOneOneForm n M} {u : ℕ → Fin n → M → EReal}
    (hu : ∀ j i, IsThetaPshPotential (theta i).val (u j i))
    (hmono : ∀ i, Monotone (fun j => u j i))
    (hv : ∀ i, IsThetaPshPotential (theta i).val
      (uscRegularization (⨆ j, u j i))) (S : Finset (Fin n)) (e : ComplexChart n M) :
    ∀ᵐ z ∂(volume.restrict e.val.target),
      chartFunction (⨆ j, sumPot S (fun _ => 1) (u j)) e z =
        chartFunction (sumPot S (fun _ => 1)
          (fun i => uscRegularization (⨆ j, u j i))) e z := by
  have hae : ∀ᵐ z ∂(volume.restrict e.val.target), ∀ i,
      (⨆ j, chartFunction (u j i) e z) =
        chartFunction (uscRegularization (⨆ j, u j i)) e z := by
    rw [ae_all_iff]
    intro i
    exact ae_chartFunction_iSup_eq_of_genuine (fun j => hu j i) (hmono i) (hv i) e
  filter_upwards [hae] with z hz
  have hlim : ∀ i, Tendsto (fun j => u j i (e.val.symm z)) atTop
      (𝓝 (uscRegularization (⨆ j, u j i) (e.val.symm z))) := by
    intro i
    have h := tendsto_atTop_iSup (fun j k hjk => hmono i hjk (e.val.symm z))
    have hzi : (⨆ j, u j i (e.val.symm z)) =
        uscRegularization (⨆ j, u j i) (e.val.symm z) := by
      simpa only [chartFunction] using hz i
    rw [hzi] at h
    exact h
  have hsumlim := tendsto_finsetSum_ereal_of_ne_top atTop S hlim
    (fun i => (hv i).1.quasiPlurisubharmonic.ne_top (e.val.symm z))
  have hsumMono : Monotone (fun j => sumPot S (fun _ => 1) (u j)) :=
    fun j k hjk => sumPot_mono (fun _ => one_pos) (fun i => hmono i hjk)
  have hraw := tendsto_atTop_iSup (fun j k hjk => hsumMono hjk (e.val.symm z))
  simp only [chartFunction, iSup_apply]
  exact tendsto_nhds_unique hraw (by
    simpa only [chartFunction, sumPot, EReal.coe_one, one_mul] using hsumlim)

/-- Upper-semicontinuous regularization of an increasing subset sum equals
the genuine sum of its individual regularized suprema, including poles. -/
theorem uscRegularization_iSup_subsetSum_eq
    {theta : Fin n → ClosedRealOneOneForm n M} {u : ℕ → Fin n → M → EReal}
    (hu : ∀ j i, IsThetaPshPotential (theta i).val (u j i))
    (hmono : ∀ i, Monotone (fun j => u j i))
    (hv : ∀ i, IsThetaPshPotential (theta i).val
      (uscRegularization (⨆ j, u j i))) (S : Finset (Fin n)) :
    uscRegularization (⨆ j, sumPot S (fun _ => 1) (u j)) =
      sumPot S (fun _ => 1) (fun i => uscRegularization (⨆ j, u j i)) := by
  let A := ⨆ j, sumPot S (fun _ => 1) (u j)
  let V := sumPot S (fun _ => 1) (fun i => uscRegularization (⨆ j, u j i))
  let W := uscRegularization A
  have hV : IsThetaPshPotential (sumForm S (fun _ => 1) theta).val V :=
    isThetaPshPotential_subsetSum hv S
  have hAV : A ≤ V := by
    apply iSup_le
    intro j
    exact sumPot_mono (fun _ => one_pos) (fun i x =>
      (le_iSup (fun k => u k i) j x).trans (le_uscRegularization _ x))
  have hWV : W ≤ V := uscRegularization_le
    hV.1.quasiPlurisubharmonic.upperSemicontinuous hAV
  funext x
  apply le_antisymm (hWV x)
  let e : ComplexChart n M := complexChartAt x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  obtain ⟨O, rho, hzO, hrho⟩ := hV.1.hasSmoothLocalPotentials e
    (e.val x) (e.val.map_source hx)
  have hpsh : PlurisubharmonicOn
      (fun z => chartFunction V e z + (rho z : EReal)) O :=
    chartCorrectedFamily_plurisubharmonicOn (F := {V})
      (fun _ h => by rw [mem_singleton_iff.mp h]; exact hV) e hrho _
      ⟨V, mem_singleton _, rfl⟩
  have hwusc : UpperSemicontinuousOn
      (fun z => chartFunction W e z + (rho z : EReal)) O := by
    intro z hz
    have hw : UpperSemicontinuousAt (chartFunction W e) z :=
      (upperSemicontinuous_uscRegularization A (e.val.symm z)).comp
        (e.val.continuousAt_symm (hrho.2.1 hz))
    have hrc : ContinuousAt rho z :=
      ((hrho.2.2.1 z hz).contDiffAt (hrho.1.mem_nhds hz)).continuousAt
    have hcoe : ContinuousAt (fun y => (rho y : EReal)) z :=
      continuous_coe_real_ereal.continuousAt.comp hrc
    exact (hw.add' hcoe.upperSemicontinuousAt
      (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot (rho z)))
        (Or.inr (EReal.coe_ne_top (rho z))))).upperSemicontinuousWithinAt O
  have hae : ∀ᵐ z ∂(volume.restrict O),
      chartFunction V e z + (rho z : EReal) ≤
        chartFunction W e z + (rho z : EReal) := by
    have hs := ae_restrict_of_ae_restrict_of_subset hrho.2.1
      (ae_chartFunction_iSup_subsetSum hu hmono hv S e)
    filter_upwards [hs] with z hz
    apply add_le_add _ le_rfl
    rw [← hz]
    exact le_uscRegularization A (e.val.symm z)
  have hle := hpsh.le_of_ae_le hrho.1 hwusc volume hae (e.val x) hzO
  have hc := (EReal.addLECancellable_coe (rho (e.val x))).add_le_add_iff_right.mp hle
  simpa only [chartFunction, e.val.left_inv hx] using hc

variable [MeasurableSpace M] [BorelSpace M]

/-- Each actual subset diagonal test integral converges to the sum of the
genuine individual regularized limits. -/
theorem tendsto_integral_diagonal_subsetSum_regularized (omega : KahlerBackground n M)
    {theta : Fin n → ClosedRealOneOneForm n M} {u : ℕ → Fin n → M → EReal}
    (hu : ∀ j i, IsThetaPshPotential (theta i).val (u j i))
    (hmono : ∀ i, Monotone (fun j => u j i))
    (hv : ∀ i, IsThetaPshPotential (theta i).val
      (uscRegularization (⨆ j, u j i))) (S : Finset (Fin n)) (chi : C(M, ℝ)) :
    Tendsto (fun j => ∫ x, chi x ∂diagonalPotentialMeasure
      (sumForm S (fun _ => 1) theta) (sumPot S (fun _ => 1) (u j))
        (isThetaPshPotential_subsetSum (hu j) S)) atTop
      (𝓝 (∫ x, chi x ∂diagonalPotentialMeasure
        (sumForm S (fun _ => 1) theta)
        (sumPot S (fun _ => 1) (fun i => uscRegularization (⨆ j, u j i)))
          (isThetaPshPotential_subsetSum hv S))) := by
  have hmonoS : Monotone fun j => sumPot S (fun _ => 1) (u j) :=
    fun j k hjk => sumPot_mono (fun _ => one_pos) (fun i => hmono i hjk)
  have heq := uscRegularization_iSup_subsetSum_eq hu hmono hv S
  have hU : IsThetaPshPotential (sumForm S (fun _ => 1) theta).val
      (uscRegularization (⨆ j, sumPot S (fun _ => 1) (u j))) :=
    heq ▸ isThetaPshPotential_subsetSum hv S
  have h := tendsto_integral_diagonal_of_monotone omega
    (fun j => isThetaPshPotential_subsetSum (hu j) S) hmonoS hU chi
  simpa only [heq] using h

/-- Actual independent mixed test integrals converge at genuine regularized
suprema, without pointwise convergence or mass-convergence premises. -/
theorem tendsto_integral_mixed_of_monotone_regularized (omega : KahlerBackground n M)
    {theta : Fin n → ClosedRealOneOneForm n M} {u : ℕ → Fin n → M → EReal}
    (hu : ∀ j i, IsThetaPshPotential (theta i).val (u j i))
    (hmono : ∀ i, Monotone (fun j => u j i))
    (hv : ∀ i, IsThetaPshPotential (theta i).val
      (uscRegularization (⨆ j, u j i))) (chi : C(M, ℝ)) :
    Tendsto (fun j => ∫ x, chi x ∂globalMixedMeasure theta (u j)
      (fun i => (hu j i).1)) atTop
      (𝓝 (∫ x, chi x ∂globalMixedMeasure theta
        (fun i => uscRegularization (⨆ j, u j i)) (fun i => (hv i).1))) := by
  classical
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Finset (Fin n))) fun S _ =>
    (tendsto_const_nhds (x := (-1 : ℝ) ^ (n - S.card))).mul
      (tendsto_integral_diagonal_subsetSum_regularized omega hu hmono hv S chi)
  have hj := fun j => integral_mixed_eq_signed_diagonal_subsetSum omega (hu j) chi
  have hvtest := integral_mixed_eq_signed_diagonal_subsetSum omega hv chi
  have hfaclim : Tendsto (fun j => (n.factorial : ℝ) *
      ∫ x, chi x ∂globalMixedMeasure theta (u j) (fun i => (hu j i).1)) atTop
      (𝓝 ((n.factorial : ℝ) * ∫ x, chi x ∂globalMixedMeasure theta
        (fun i => uscRegularization (⨆ j, u j i)) (fun i => (hv i).1))) := by
    simpa only [hj, hvtest] using hsum
  have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simpa only [inv_mul_cancel_left₀ hfac] using
    (tendsto_const_nhds (x := (n.factorial : ℝ)⁻¹)).mul hfaclim

/-- Native weak convergence of actual independent mixed products at genuine
regularized suprema for increasing sequences. -/
theorem weakTendsto_mixed_of_monotone_regularized (omega : KahlerBackground n M)
    {theta : Fin n → ClosedRealOneOneForm n M} {u : ℕ → Fin n → M → EReal}
    (hu : ∀ j i, IsThetaPshPotential (theta i).val (u j i))
    (hmono : ∀ i, Monotone (fun j => u j i))
    (hv : ∀ i, IsThetaPshPotential (theta i).val
      (uscRegularization (⨆ j, u j i))) :
    Tendsto (fun j => finiteMixedMeasure omega theta (u j) (hu j)) atTop
      (𝓝 (finiteMixedMeasure omega theta
        (fun i => uscRegularization (⨆ j, u j i)) hv)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro chi
  exact tendsto_integral_mixed_of_monotone_regularized omega hu hmono hv chi

end
end SGPT.Foundations.Analysis.Pending.IncreasingMixedRegularizedContinuity
