import SGPT.Foundations.Analysis.Pending.ActualUnitMultiplierLelongBound
import SGPT.Foundations.Analysis.Pending.ActualAnalyticUnitMultiplier
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularAddition
import SGPT.Foundations.Analysis.Pending.AnalyticQuasiEquisingularRestriction
import SGPT.Foundations.Analysis.Pending.PositiveCurrentTraceMultiplier

set_option autoImplicit false

/-! # The internally produced natural generic Lelong domain for QEA addition -/

open Set Filter
open scoped Topology ENNReal Manifold

namespace SGPT.Foundations.Analysis.Pending.QuasiEquisingularAdditionGenericLelong

open FirstPass FirstPass.NonKahlerLocus FirstPass.PositiveClasses
  FirstPass.QuasiEquisingularApproximation FirstPass.HolomorphicIdealSheaves
  MixedSummandCapacityDomination GlobalMultilinearExpansion

noncomputable section

private theorem genuineAdd
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {θ σ : ClosedRealOneOneForm n M} {u v : M → EReal}
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

/-- The two original zero generic Lelong infima, via genuine analytic restrictions
and actual unit multipliers at every level, internally supply the sum domain. -/
theorem generic_lelong_inf_add_eq_zero
    {n k : ℕ} {M Y : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel k) Y] [IsComplexManifold k Y]
    [CompactSpace Y] [ConnectedSpace Y]
    {omega : KahlerBackground n M} {θ σ : ClosedRealOneOneForm n M}
    {u v : M → EReal} {ε δ : ℕ → ℝ} {U V : ℕ → M → EReal}
    (hu : IsQuasiEquisingularApproximation omega θ u ε U)
    (hv : IsQuasiEquisingularApproximation omega σ v δ V)
    {ι : Y → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) ι)
    (hgu : (⨅ y : Y, lelongNumber (n := n) u (ι y)) = 0)
    (hgv : (⨅ y : Y, lelongNumber (n := n) v (ι y)) = 0) :
    (⨅ y : Y, lelongNumber (n := n) (fun x => u x + v x) (ι y)) = 0 := by
  classical
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    have htop (y : Y) : lelongNumber (n := n) u (ι y) = ⊤ :=
      LelongNumberChartTransport.lelongNumber_eq_top_of_eventually_bot
        (by rw [LelongNumberChartTransport.nhdsWithin_ne_eq_bot_of_dim_eq_zero hn0]
            exact Filter.eventually_bot)
    simp only [htop, iInf_const] at hgu
    exact ENNReal.top_ne_zero hgu
  have hsum := QuasiEquisingularAddition.isQuasiEquisingularApproximation_add hu hv
  apply le_antisymm ?_ zero_le
  apply ENNReal.le_of_forall_pos_le_add
  intro a ha _
  have haR : 0 < (a : ℝ) := ha
  let d : ℝ := (Module.finrank ℝ (ComplexModel n) : ℝ)
  have hd : 0 ≤ d := Nat.cast_nonneg _
  let c : ℝ := (d + 1) / (a : ℝ)
  have hc : 0 < c := div_pos (by linarith) haR
  have hac : (a : ℝ) * c = d + 1 := by dsimp only [c]; field_simp
  have hdc : d / c ≤ (a : ℝ) := (div_le_iff₀ hc).mpr (by rw [hac]; linarith)
  obtain ⟨j, hj⟩ := (hsum.eventually_multiplierIdealIncluded hc (lt_add_one c)).exists
  have hU := AnalyticQuasiEquisingularRestriction.isThetaPshPotential_ordinaryRestriction_term
    hu hι hgu j
  have hV := AnalyticQuasiEquisingularRestriction.isThetaPshPotential_ordinaryRestriction_term
    hv hι hgv j
  have hY := genuineAdd hU hV
  let y₀ : Y := Classical.choice (inferInstance : Nonempty Y)
  obtain ⟨y, -, hfin⟩ := hY.2 y₀ Set.univ isOpen_univ (mem_univ y₀)
  have htype := hsum.term_hasAnalyticSingularityType j
    (complexChartAt (n := n) (ι y)) ((complexChartAt (n := n) (ι y)).val (ι y))
    ((complexChartAt (n := n) (ι y)).val.map_source (mem_complexChartAt_source (ι y)))
  have hunit := ActualAnalyticUnitMultiplier.one_mem_multiplierIdeal_of_analytic_nonpole
    (hsum.term j).1.quasiPlurisubharmonic htype hfin (hc.trans (lt_add_one c))
  have horig := PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_multiplierIdealIncluded hj
    (ι y) (fun _ => (1 : ℂ)) hunit
  have hν := ActualUnitMultiplierLelongBound.lelongNumber_le_of_unit_multiplierIdeal hn horig
  have hle : (⨅ y : Y, lelongNumber (n := n) (fun x => u x + v x) (ι y)) ≤
      ENNReal.ofReal (a : ℝ) :=
    (iInf_le_of_le y hν).trans (ENNReal.ofReal_le_ofReal hdc)
  simpa only [zero_add, ENNReal.ofReal_coe_nnreal] using hle

end

end SGPT.Foundations.Analysis.Pending.QuasiEquisingularAdditionGenericLelong
