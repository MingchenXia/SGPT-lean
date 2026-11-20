import SGPT.PSH.HermitianProductsIncreasingPotentials
import SGPT.PSH.HermitianExtremalCurrentLimits

/-!
# Actual bounded decreasing Hermitian potentials and their product limits

Original uniform real bounds give a finite literal infimum at every point.
Common local corrections manufacture its quasi-PSH regularity, and actual
current convergence preserves its original Hermitian inequality. The
corrected real readers then converge pointwise, so ordinary decreasing
Bedford--Taylor continuity applies to the fixed residual expansion.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianGlobalProducts

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere LocalProductCurrents LocalBedfordTaylorProducts
  LocalBedfordTaylorContinuity
open Hermitian HermitianProducts
open scoped Topology Distributions

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- Original real bounds internally exclude poles of the entire literal
infimum, so its genuine Hermitian class needs no noncollapse certificate. -/
theorem isHermitianPSH_iInf_of_uniform_bounds (omega : Background (m + 1) M)
    {g : ℕ → M → EReal} (hg : ∀ j, IsHermitianPSH omega (g j)) (a b : ℝ)
    (hb : ∀ j x, (a : EReal) ≤ g j x ∧ g j x ≤ (b : EReal)) (hanti : Antitone g) :
    IsHermitianPSH omega (fun x => ⨅ j, g j x) ∧
      ∀ x, (a : EReal) ≤ ⨅ j, g j x ∧ (⨅ j, g j x) ≤ (b : EReal) := by
  have hbound : ∀ x, (a : EReal) ≤ ⨅ j, g j x ∧ (⨅ j, g j x) ≤ (b : EReal) :=
    fun x => ⟨le_iInf fun j => (hb j x).1, (iInf_le (fun j => g j x) 0).trans (hb 0 x).2⟩
  have hraw := HermitianExtremalLimits.manifoldQuasiPlurisubharmonic_iInf
    (hasCommonLocalCorrections omega) hg (fun x j k hjk => hanti hjk x)
  have hquasi : IsGlobalQuasiPshPotential (n := m + 1) (fun x => ⨅ j, g j x) := by
    refine ⟨hraw, fun x V _ hx => ?_⟩
    exact ⟨x, hx, ne_of_gt ((EReal.bot_lt_coe a).trans_le (hbound x).1)⟩
  exact ⟨HermitianExtremalCurrentLimits.isFormPSH_iInf_of_quasiPshPotential hg
    (fun x j k hjk => hanti hjk x) hquasi, hbound⟩

namespace BackgroundPatch

variable {omega : Background (m + 1) M}

theorem correctedReal_antitone (P : BackgroundPatch omega)
    {g : ℕ → M → EReal} (a b : ℝ)
    (hb : ∀ j x, (a : EReal) ≤ g j x ∧ g j x ≤ (b : EReal)) (hanti : Antitone g)
    (z : ComplexModel (m + 1)) : Antitone fun j => P.correctedReal (g j) z := by
  intro j k hjk
  have hgbot : g k (P.geometry.chart.val.symm z) ≠ ⊥ :=
    ne_of_gt ((EReal.bot_lt_coe a).trans_le (hb k _).1)
  have hgtop : g j (P.geometry.chart.val.symm z) ≠ ⊤ :=
    ne_of_lt ((hb j _).2.trans_lt (EReal.coe_lt_top b))
  exact add_le_add (EReal.toReal_le_toReal (hanti hjk _) hgbot hgtop) le_rfl

/-- The real corrected readers converge to the actual literal infimum;
finiteness and continuity of `toReal` are proved from the original bounds. -/
theorem correctedReal_tendsto_iInf (P : BackgroundPatch omega)
    {g : ℕ → M → EReal} (a b : ℝ)
    (hb : ∀ j x, (a : EReal) ≤ g j x ∧ g j x ≤ (b : EReal)) (hanti : Antitone g)
    (z : ComplexModel (m + 1)) : Tendsto (fun j => P.correctedReal (g j) z) atTop
      (𝓝 (P.correctedReal (fun x => ⨅ j, g j x) z)) := by
  have hbound : (a : EReal) ≤ ⨅ j, chartFunction (g j) P.geometry.chart z :=
    le_iInf fun j => (hb j _).1
  have hupper : (⨅ j, chartFunction (g j) P.geometry.chart z) ≤ (b : EReal) :=
    (iInf_le _ 0).trans (hb 0 _).2
  have htop := ne_of_lt (hupper.trans_lt (EReal.coe_lt_top b))
  have hbot := ne_of_gt ((EReal.bot_lt_coe a).trans_le hbound)
  have hlim := (EReal.tendsto_toReal htop hbot).comp
    (tendsto_atTop_iInf (fun j k hjk => hanti hjk (P.geometry.chart.val.symm z)))
  exact hlim.add_const (P.correction z)

/-- Every actual bounded decreasing tuple gives weak convergence of
the literal fixed-residual expansion to the literal infimum tuple. -/
theorem expansion_decreasing_iInf (P : BackgroundPatch omega) (p r : ℕ) (hdegree : r + p = m + 1)
    (u : ℕ → Fin p → M → EReal) (hu : ∀ j i, IsHermitianPSH omega (u j i))
    (a b : ℝ) (hb : ∀ j i x, (a : EReal) ≤ u j i x ∧ u j i x ≤ (b : EReal))
    (hanti : ∀ i, Antitone fun j => u j i) :
    WeakTendsto (fun j => backgroundExpansion p r (fun i => P.correctedReal (u j i))
      P.residual_smooth (oneCurrentOf (U := P.geometry.domain) hdegree))
      (backgroundExpansion p r (fun i => P.correctedReal (fun x => ⨅ j, u j i x))
        P.residual_smooth (oneCurrentOf (U := P.geometry.domain) hdegree)) := by
  let u₀ : Fin p → M → EReal := fun i x => ⨅ j, u j i x
  have hlim (i : Fin p) := isHermitianPSH_iInf_of_uniform_bounds omega
    (fun j => hu j i) a b (fun j x => hb j i x) (hanti i)
  exact backgroundExpansion_decreasing p r (oneCurrentOf (U := P.geometry.domain) hdegree)
    (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _)
    (fun j i => P.correctedReal (u j i)) (fun i => P.correctedReal (u₀ i))
    (fun j i => P.correctedReal_isLocallyBoundedPshOn (hu j i) ⟨a, b, hb j i⟩)
    (fun i => P.correctedReal_isLocallyBoundedPshOn (hlim i).1 ⟨a, b, (hlim i).2⟩)
    (fun i z _ => P.correctedReal_antitone a b (fun j x => hb j i x) (hanti i) z)
    (fun i z _ => P.correctedReal_tendsto_iInf a b (fun j x => hb j i x) (hanti i) z)
    P.residual_smooth

theorem mixedCurrent_decreasing_iInf (P : BackgroundPatch omega) (p : ℕ) (hp : p ≤ m + 1)
    (u : ℕ → Fin p → M → EReal) (hu : ∀ j i, IsHermitianPSH omega (u j i))
    (a b : ℝ) (hb : ∀ j i x, (a : EReal) ≤ u j i x ∧ u j i x ≤ (b : EReal))
    (hanti : ∀ i, Antitone fun j => u j i) :
    WeakTendsto (fun j => P.mixedCurrent p hp (u j))
      (P.mixedCurrent p hp (fun i x => ⨅ j, u j i x)) :=
  P.expansion_decreasing_iInf p (m + 1 - p) (Nat.sub_add_cancel hp) u hu a b hb hanti

theorem current_decreasing_iInf (P : BackgroundPatch omega)
    (u : ℕ → Fin (m + 1) → M → EReal) (hu : ∀ j i, IsHermitianPSH omega (u j i))
    (a b : ℝ) (hb : ∀ j i x, (a : EReal) ≤ u j i x ∧ u j i x ≤ (b : EReal))
    (hanti : ∀ i, Antitone fun j => u j i) :
    WeakTendsto (fun j => P.current (u j)) (P.current (fun i x => ⨅ j, u j i x)) :=
  P.expansion_decreasing_iInf (m + 1) 0 (Nat.zero_add (m + 1)) u hu a b hb hanti

end BackgroundPatch

end SGPT.PSH.HermitianGlobalProducts
