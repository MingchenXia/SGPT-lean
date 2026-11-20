import SGPT.Foundations.Analysis.Pending.NaturalThetaPshSourceCurrent
import SGPT.Foundations.Analysis.Pending.MixedMassProductCalculus
import SGPT.Foundations.Analysis.Pending.MixedSummandCapacityDomination
import SGPT.Foundations.Analysis.Pending.LelongPoincareDivisor

set_option autoImplicit false

/-! # Actual full source-current identities for finite combinations

All-zero and empty sums are genuine internally. Chart Haar finiteness
and local integrability identify real representatives almost everywhere;
regular distributions, actual ddC and full current pairings then produce
the literal current identity, with no target-current certificate.
-/

open Set MeasureTheory
open scoped BigOperators Distributions

namespace SGPT.Foundations.Analysis.Pending.SourceCurrentFiniteCombinations

open FirstPass FirstPass.PositiveClasses GlobalCurrents GlobalCurrentPotentials
  NaturalThetaPshSourceCurrent GlobalMultilinearExpansion MixedMassProductCalculus
  _root_.SGPT.Foundations.Analysis.LocalCurrents CanonicalCurrentFrame
  CanonicalSmoothCurrentDensity ConstantFormProducts TopDegreeDensity

noncomputable section

private theorem genuine_nonnegative_sum {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {ι : Type*} [Fintype ι] {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    {α : ι → ClosedRealOneOneForm n M} {f : ι → M → EReal}
    (hf : ∀ i, IsThetaPshPotential (α i).val (f i)) :
    IsThetaPshPotential (sumForm Finset.univ c α).val (sumPot Finset.univ c f) := by
  classical
  let P := Finset.univ.filter fun i => 0 < c i
  rcases P.eq_empty_or_nonempty with hPe | hPne
  · have hz : ∀ i, c i = 0 := fun i => by
      have hi : i ∉ P := by rw [hPe]; exact Finset.notMem_empty i
      have hnot : ¬0 < c i := by simpa only [P, Finset.mem_filter,
        Finset.mem_univ, true_and] using hi
      exact le_antisymm (not_lt.mp hnot) (hc i)
    rw [sumForm_eq_zero hz, sumPot_eq_zero hz]
    exact (LocalPotentials.isThetaPshPotential_zero_iff 0).mpr fun _ _ _ _ => le_rfl
  · let w : ι → ℝ := fun i => if 0 < c i then c i else 1
    have hw : ∀ i, 0 < w i := fun i => by
      simp only [w]
      split_ifs with h
      · exact h
      · exact one_pos
    have hF : sumForm P w α = sumForm Finset.univ c α := by
      rw [← sumForm_filter_pos hc]
      exact Finset.sum_congr rfl fun i hi => by
        have hp : 0 < c i := (Finset.mem_filter.mp hi).2
        simp only [w, if_pos hp]
    have hP : sumPot P w f = sumPot Finset.univ c f := by
      rw [← sumPot_filter_pos hc]
      funext x
      exact Finset.sum_congr rfl fun i hi => by
        have hp : 0 < c i := (Finset.mem_filter.mp hi).2
        simp only [w, if_pos hp]
    have h := MixedSummandCapacityDomination.isThetaPshPotential_sumPot hPne hw hf
    rwa [hF, hP] at h

private theorem toLocalCurrent_sum_smul {n : ℕ} {U : TopologicalSpace.Opens (ComplexModel n)}
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    (k : CurrentDegree n) {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (A : ι → DistributionForm U k.val) :
    toLocalCurrent b k (∑ i, c i • A i) = ∑ i, c i • toLocalCurrent b k (A i) := by
  classical
  let L : DistributionForm U k.val →ₗ[ℝ] LocalCurrent U k :=
    { toFun := toLocalCurrent b k
      map_add' := by
        intro S T
        ext η
        simp only [toLocalCurrent, wedgePairing_apply, AlternatingMap.add_apply,
          add_apply, smul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r S
        ext η
        simp only [toLocalCurrent, wedgePairing_apply, AlternatingMap.smul_apply,
          smul_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun s _ => smul_comm _ _ _ }
  change L (∑ i, c i • A i) = ∑ i, c i • L (A i)
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => L.map_smul (c i) (A i)

private theorem globalDDC_sum {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    (hn : 0 < n) {ι : Type*} [Fintype ι] (c : ι → ℝ) (f : ι → M → EReal)
    (hf : ∀ i, IsGlobalQuasiPshPotential (n := n) (f i))
    (hF : IsGlobalQuasiPshPotential (n := n) (sumPot Finset.univ c f)) :
    globalDDC b hn (sumPot Finset.univ c f) hF = ∑ i, c i • globalDDC b hn (f i) (hf i) := by
  classical
  have hchart : ∀ e : ComplexChart n M,
      chartDDC b (sumPot Finset.univ c f) e (quasiPsh_chart_locallyIntegrable b hn _ hF e) =
        ∑ i, c i • chartDDC b (f i) e (quasiPsh_chart_locallyIntegrable b hn _ (hf i) e) := by
    intro e
    let F : ι → ComplexModel n → ℝ := fun i z => (chartFunction (f i) e z).toReal
    have hloc : ∀ i, LocallyIntegrableOn (F i) (chartTarget e) b.addHaar := fun i =>
      quasiPsh_chart_locallyIntegrable b hn _ (hf i) e
    have hwloc : ∀ i, LocallyIntegrableOn (fun z => c i * F i z)
        (chartTarget e) b.addHaar := fun i => (hloc i).smul (c i)
    have hsumloc := LelongPoincareDivisor.locallyIntegrableOn_finsetSum Finset.univ
      (fun i _ => hwloc i)
    have hreal : (fun z => (chartFunction (sumPot Finset.univ c f) e z).toReal) =ᵐ[
        b.addHaar.restrict (chartTarget e)] (fun z => ∑ i, c i * F i z) := by
      have ha : ∀ᵐ z ∂b.addHaar.restrict (chartTarget e),
          ∀ i, chartFunction (f i) e z ≠ ⊤ ∧ chartFunction (f i) e z ≠ ⊥ :=
        ae_all_iff.mpr fun i => quasiPsh_chart_ae_finite b hn _ (hf i) e
      filter_upwards [ha] with z hz
      have hcoe : ∀ S : Finset ι,
          (∑ i ∈ S, (c i : EReal) * chartFunction (f i) e z) =
            ((∑ i ∈ S, c i * F i z : ℝ) : EReal) := by
        intro S
        induction S using Finset.induction_on with
        | empty => simp
        | insert i S hi ih =>
            rw [Finset.sum_insert hi, Finset.sum_insert hi, ih,
              ← EReal.coe_toReal (hz i).1 (hz i).2, ← EReal.coe_mul, ← EReal.coe_add]
      change (∑ i, (c i : EReal) * chartFunction (f i) e z).toReal = _
      rw [hcoe Finset.univ, EReal.toReal_coe]
    unfold chartDDC
    rw [regularDistribution_congr_ae_on
      (quasiPsh_chart_locallyIntegrable b hn _ hF e) hsumloc hreal,
      LelongPoincareDivisor.regularDistribution_sum Finset.univ hwloc hsumloc]
    simp_rw [LelongPoincareDivisor.regularDistribution_const_mul _ (hloc _) (hwloc _)]
    change LelongPoincareDivisor.ddCLM (∑ i, c i • _) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => (LelongPoincareDivisor.ddCLM).map_smul (c i) _
  apply GlobalCurrent.ext
  intro e η
  change toLocalCurrent b (degreeTwo hn)
    (chartDDC b (sumPot Finset.univ c f) e (quasiPsh_chart_locallyIntegrable b hn _ hF e)) η = _
  rw [hchart e, toLocalCurrent_sum_smul]
  simp only [GlobalCurrent.inChart, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply, sum_apply, smul_apply]
  rfl

private theorem smoothGlobalCurrent_sumForm {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    (hn : 0 < n) {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (α : ι → ClosedRealOneOneForm n M) :
    smoothGlobalCurrent b (k := degreeTwo hn) (sumForm Finset.univ c α).val =
      ∑ i, c i • smoothGlobalCurrent b (k := degreeTwo hn) (α i).val := by
  classical
  have hdist : ∀ e : ComplexChart n M,
      smoothFormDistribution b (sumForm Finset.univ c α).val e =
        ∑ i, c i • smoothFormDistribution b (α i).val e := by
    intro e
    have hcoeff : ∀ z,
        (sumForm Finset.univ c α).val.coeff e z = ∑ i, c i • (α i).val.coeff e z := by
      intro z
      have hS : ∀ S : Finset ι, (∑ i ∈ S, c i • α i).val.coeff e z =
          ∑ i ∈ S, c i • (α i).val.coeff e z := by
        intro S
        induction S using Finset.induction_on with
        | empty => simp
        | insert i S hi ih =>
            rw [Finset.sum_insert hi, Finset.sum_insert hi,
              ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul, ih]
      exact hS Finset.univ
    ext v φ
    let ev : DistributionForm (chartTarget e) 2 →ₗ[ℝ] ℝ :=
      { toFun := fun A => A v φ
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    rw [smoothFormDistribution_apply]
    change (∫ x, φ x • (sumForm Finset.univ c α).val.coeff e x ∂b.addHaar) v =
      ev (∑ i, c i • smoothFormDistribution b (α i).val e)
    have he : (fun x => φ x • (sumForm Finset.univ c α).val.coeff e x) =
        fun x => ∑ i, c i • (φ x • (α i).val.coeff e x) := by
      funext x
      rw [hcoeff x, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
    have hi' : ∀ i, Integrable (fun x => c i • (φ x • (α i).val.coeff e x)) b.addHaar := by
      intro i
      have h := TestFunction.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
        (smoothForm_coeff_locallyIntegrable b (c i • α i).val e) φ
      convert h using 1 <;> first
      | rfl
      | funext x
        rw [ClosedRealOneOneForm.coeff_smul]
        exact smul_comm _ _ _
    have hsumint : (∫ x, ∑ i, c i • (φ x • (α i).val.coeff e x) ∂b.addHaar) =
        ∑ i, ∫ x, c i • (φ x • (α i).val.coeff e x) ∂b.addHaar :=
      integral_finsetSum Finset.univ (fun i _ => hi' i)
    rw [he, hsumint, map_sum]
    simp only [integral_smul, ContinuousAlternatingMap.sum_apply,
      ContinuousAlternatingMap.smul_apply, map_smul]
    exact Finset.sum_congr rfl fun i _ => by
      rw [show ev (smoothFormDistribution b (α i).val e) =
        (smoothFormDistribution b (α i).val e) v φ from rfl,
        smoothFormDistribution_apply]
  apply GlobalCurrent.ext
  intro e η
  rw [smoothGlobalCurrent_inChart]
  change toLocalCurrent b (degreeTwo hn)
    (smoothFormDistribution b (sumForm Finset.univ c α).val e) η = _
  rw [hdist e, toLocalCurrent_sum_smul]
  simp only [GlobalCurrent.inChart, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply, sum_apply, smul_apply]
  rfl

/-- A natural finite nonnegative combination is genuine internally, and its
source current is the literal weighted sum on all chart test forms. -/
theorem exists_genuine_sum_and_sourceDCurrent_eq {m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    {ι : Type*} [Fintype ι] {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    {α : ι → ClosedRealOneOneForm (m + 1) M} {f : ι → M → EReal}
    (hf : ∀ i, IsThetaPshPotential (α i).val (f i)) :
    ∃ hF : IsThetaPshPotential (sumForm Finset.univ c α).val (sumPot Finset.univ c f),
      sourceDCurrent ((2 * Real.pi) • sumForm Finset.univ c α)
        (sumPot Finset.univ c f) hF.quasiPshPotential =
      ∑ i, c i • sourceDCurrent ((2 * Real.pi) • α i) (f i) (hf i).quasiPshPotential := by
  classical
  let hF := genuine_nonnegative_sum hc hf
  refine ⟨hF, ?_⟩
  have hα : (2 * Real.pi) • sumForm Finset.univ c α =
      sumForm Finset.univ c (fun i => (2 * Real.pi) • α i) := by
    unfold sumForm
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  unfold sourceDCurrent
  rw [hα, smoothGlobalCurrent_sumForm (canonicalBasis (m + 1)) (Nat.succ_pos m),
    globalDDC_sum (canonicalBasis (m + 1)) (Nat.succ_pos m) c f
      (fun i => (hf i).quasiPshPotential) hF.quasiPshPotential,
    Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_add, smul_comm]

end
end SGPT.Foundations.Analysis.Pending.SourceCurrentFiniteCombinations
