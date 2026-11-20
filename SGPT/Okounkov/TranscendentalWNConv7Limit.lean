import SGPT.Okounkov.TranscendentalWNConv7Final
import SGPT.Okounkov.TranscendentalWNConv7Singularity
import SGPT.Okounkov.TranscendentalVolumeConcavityRestricted
import SGPT.Foundations.Analysis.Pending.IncreasingLimitMass
import SGPT.Foundations.Analysis.Pending.NegligibleSetsPluripolarProof
import SGPT.Foundations.Analysis.Pending.SingularityEnvelopeMassProof
import SGPT.Foundations.Analysis.Pending.HironakaChowLemma
import SGPT.PSH.LogResolution

/-!
# The limits of `v_k + k` on the central fibre and their masses (WN21 Propositions 7.2--7.3)

Blueprint `claude-tok-wn-conv7`, nodes `tok-wn-conv7:central-limit` and
`tok-wn-conv7:limit-mass`; source WN21 §7, Propositions 7.2 and 7.3.

Let `ι : V → 𝒳` be a holomorphic map from a compact Kähler manifold into the central fibre
`X₀ = μ⁻¹(X × {0})` (the lift `ι'` of `x ↦ (x, 0)`, image `X'`, or the inclusion of `ℰ`), on which
`g_k = -1 - k`.  For `v_k = P_Θ[ψ](g_k)`, the functions `v_k ∘ ι + k ≤ -1` increase with `k`
(`prescribedEnvelope_cutoffObstacle_sub_one_le`); their regularized limit is
`centralLimitPotential Θ μ χ ψ ι = (sup_k (v_k ∘ ι + k))^*` (WN21: `v_{X'}`, `v_ℰ`).

* `isThetaPshPotential_centralLimitPotential`: it is an `ι^*Θ`-psh potential.
* `diagonalPotentialMass_centralLimitPotential_le` (**WN21 Proposition 7.3**, first half): if
  `ψ` has a log resolution (so `v_k ⪯ ψ`, `prescribedEnvelope_le_add_of_logSingularities`), then
  `∫_V ⟨(ι^*Θ + dd^c v_V)ⁿ⟩ ≤ ∫_V ⟨(ι^*Θ + dd^c (ψ ∘ ι))ⁿ⟩`.  The proof does not use the
  convergence of Monge--Ampère measures on `{ψ > -C}` of WN21: the non-pluripolar mass of the
  regularized limit of an increasing sequence is at most the supremum of the masses
  (`IncreasingLimitMass.diagonalPotentialMass_le_iSup_of_monotone`, Xia's Corollary 2.4.1), and
  `v_k ∘ ι + k ⪯ ψ ∘ ι` (monotonicity of non-pluripolar masses).
* `diagonalPotentialMass_centralLimitPotential_le_restrictedVolume` (**WN21 Proposition 7.3**):
  if moreover `ψ ⪯ φ` for some `φ ∈ Ω(Θ)` finite somewhere on `ι(V)`, then
  `∫_V ⟨(ι^*Θ + dd^c v_V)ⁿ⟩ ≤ vol_{𝒳|ι(V)}({Θ})`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Okounkov.TranscendentalCore

/-- `g_k = -1 - k` at `0 ∈ ℙ¹`. -/
private theorem cutoffObstacleLine_zero_eq (χ : ℝ → ℝ) (k : ℕ) :
    cutoffObstacleLine χ k projectiveZero = -1 - k := by
  rw [← affineLinePoint_zero, cutoffObstacleLine_affineLinePoint]
  simp [cutoffLog_zero]

/-- **`g_k = -1 - k` on the central fibre** `X₀ = μ⁻¹(X × {0})`. -/
theorem cutoffObstacle_of_central {X : Type*} {𝒳 : Type*} {μ : 𝒳 → X × ProjectiveLine}
    (χ : ℝ → ℝ) (k : ℕ) {z : 𝒳} (hz : (μ z).2 = projectiveZero) :
    cutoffObstacle μ χ k z = -1 - k := by
  rw [cutoffObstacle, hz, cutoffObstacleLine_zero_eq]

section Limit

variable {X : Type*} {N k : ℕ} {𝒳 : Type u} [TopologicalSpace 𝒳]
  [ChartedSpace (ComplexModel N) 𝒳] [IsComplexManifold N 𝒳]
  {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]

/-- **The limit on the central fibre** (WN21 Proposition 7.2: `v_{X'}`, `v_ℰ`): the regularized
supremum `(sup_k (v_k ∘ ι + k))^*` of the increasing sequence `v_k ∘ ι + k`,
`v_k = P_Θ[ψ](g_k)`. -/
def centralLimitPotential (Θ : ClosedRealOneOneForm N 𝒳) (μ : 𝒳 → X × ProjectiveLine)
    (χ : ℝ → ℝ) (ψ : 𝒳 → EReal) (ι : V → 𝒳) : V → EReal :=
  uscRegularization (⨆ j : ℕ, fun y => prescribedEnvelope Θ (cutoffObstacle μ χ j) ψ (ι y) +
    ((j : ℝ) : EReal))

variable {Θ : ClosedRealOneOneForm N 𝒳} {μ : 𝒳 → X × ProjectiveLine} {χ : ℝ → ℝ}
  {ψ : 𝒳 → EReal} {ι : V → 𝒳}
  (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel N) ∞ ι)

omit [TopologicalSpace V] in
/-- The sequence `v_j ∘ ι + j` increases (WN21 Proposition 7.2). -/
theorem monotone_centralSequence (hχ : IsWNCutoff χ) :
    Monotone (fun j : ℕ => fun y => prescribedEnvelope Θ (cutoffObstacle μ χ j) ψ (ι y) +
      ((j : ℝ) : EReal)) := by
  refine monotone_nat_of_le_succ fun j y => ?_
  have h := add_le_add (prescribedEnvelope_cutoffObstacle_sub_one_le (μ := μ) hχ Θ ψ j (ι y))
    (le_refl (((j + 1 : ℕ) : ℝ) : EReal))
  have h2 : (-1 : ℝ) + ((j + 1 : ℕ) : ℝ) = (j : ℝ) := by push_cast; ring
  rw [add_assoc, ← EReal.coe_add, h2] at h
  exact h

omit [TopologicalSpace V] in
/-- On the central fibre, `v_j ∘ ι + j ≤ -1`. -/
theorem centralSequence_le (hg : ∀ j, Continuous (cutoffObstacle μ χ j))
    (hι0 : ∀ y, (μ (ι y)).2 = projectiveZero) (j : ℕ) (y : V) :
    prescribedEnvelope Θ (cutoffObstacle μ χ j) ψ (ι y) + ((j : ℝ) : EReal) ≤
      ((-1 : ℝ) : EReal) := by
  have h := add_le_add (prescribedEnvelope_le (Θ := Θ) (ψ := ψ) (hg j) (ι y))
    (le_refl ((j : ℝ) : EReal))
  rw [← EReal.coe_add] at h
  refine h.trans (EReal.coe_le_coe_iff.mpr ?_)
  rw [cutoffObstacle_of_central χ j (hι0 y)]
  linarith

/-- Each `v_j ∘ ι` is a genuine `ι^*Θ`-psh potential when `ψ ∘ ι` is one (`ψ ≤ v_j + C_j`). -/
theorem isThetaPshPotential_prescribedEnvelope_comp [CompactSpace 𝒳]
    (hg : ∀ j, Continuous (cutoffObstacle μ χ j)) (hψ : IsThetaPshPotential Θ.val ψ)
    (hψι : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι Θ).val (fun y => ψ (ι y)))
    (j : ℕ) : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι Θ).val
      (fun y => prescribedEnvelope Θ (cutoffObstacle μ χ j) ψ (ι y)) := by
  rcases isEmpty_or_nonempty 𝒳 with h𝒳 | h𝒳
  · exact ⟨fun e z _ => isEmptyElim (ι (e.val.symm z)),
      fun x => isEmptyElim (ι x)⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ z, cutoffObstacle μ χ j z ≤ B := by
    obtain ⟨z₀, -, hz₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty (hg j).continuousOn
    exact ⟨_, fun z => hz₀ (mem_univ z)⟩
  obtain ⟨C, hC⟩ := le_prescribedEnvelope_add (Θ := Θ) (hg j) hψ
  have hne : (prescribedCompetitors Θ (cutoffObstacle μ χ j) ψ).Nonempty := by
    obtain ⟨Mψ, hMψ⟩ := hψ.exists_global_upper_bound
    obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn univ_nonempty (hg j).continuousOn
    refine ⟨fun x => ψ x + ((cutoffObstacle μ χ j x₀ - Mψ : ℝ) : EReal),
      hψ.add_const _, fun z => ?_,
      (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨_, fun z => le_rfl⟩⟩
    calc ψ z + ((cutoffObstacle μ χ j x₀ - Mψ : ℝ) : EReal)
        ≤ (Mψ : EReal) + ((cutoffObstacle μ χ j x₀ - Mψ : ℝ) : EReal) :=
          add_le_add (hMψ z) le_rfl
      _ = (cutoffObstacle μ χ j x₀ : EReal) := by rw [← EReal.coe_add]; ring_nf
      _ ≤ (cutoffObstacle μ χ j z : EReal) := EReal.coe_le_coe_iff.mpr (hx₀ (mem_univ z))
  refine ⟨GlobalPotentialPullback.thetaPlurisubharmonic_comp hι
    (isThetaPshPotential_prescribedEnvelope hne hB).1, ?_⟩
  refine (hψι.sub_const C).2.mono fun y => ?_
  show ψ (ι y) - (C : EReal) ≤ _
  have h := add_le_add (hC (ι y)) (le_refl ((-C : ℝ) : EReal))
  rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero] at h
  rwa [sub_eq_add_neg, ← EReal.coe_neg]

/-- **`v_V` is a genuine `ι^*Θ`-psh potential** (WN21 Proposition 7.2). -/
theorem isThetaPshPotential_centralLimitPotential [CompactSpace 𝒳]
    (hg : ∀ j, Continuous (cutoffObstacle μ χ j)) (hι0 : ∀ y, (μ (ι y)).2 = projectiveZero)
    (hψ : IsThetaPshPotential Θ.val ψ)
    (hψι : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι Θ).val (fun y => ψ (ι y))) :
    IsThetaPshPotential (ClosedRealOneOneForm.pullback hι Θ).val
      (centralLimitPotential Θ μ χ ψ ι) :=
  NegligibleSetsPluripolarProof.isThetaPshPotential_uscRegularization_iSup_of_le
    (fun j => (isThetaPshPotential_prescribedEnvelope_comp hι hg hψ hψι j).add_const _)
    (centralSequence_le hg hι0)

variable [MeasurableSpace V] [BorelSpace V] [CompactSpace V]

/-- **WN21 Proposition 7.3, the mass bound**: if `ψ` has a log resolution, the limit `v_V` of
`v_k ∘ ι + k` on the central fibre has non-pluripolar mass at most that of `ψ ∘ ι`. -/
theorem diagonalPotentialMass_centralLimitPotential_le [CompactSpace 𝒳] (ωV : KahlerBackground k V)
    (hχ : IsWNCutoff χ) (hg : ∀ j, Continuous (cutoffObstacle μ χ j))
    (hψ : IsThetaPshPotential Θ.val ψ)
    (hψι : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι Θ).val (fun y => ψ (ι y)))
    {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel N) Z] [IsComplexManifold N Z]
    [CompactSpace Z] [ConnectedSpace Z] {π : Z → 𝒳} (hπ : IsAnalyticModification (n := N) π)
    (D : SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves.MeteredEffectiveQDivisor N Z)
    (L : ResidualNefReduction.HasLogSingularitiesAlong D (fun z => ψ (π z)))
    (hU : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι Θ).val
      (centralLimitPotential Θ μ χ ψ ι)) :
    diagonalPotentialMass (ClosedRealOneOneForm.pullback hι Θ) (centralLimitPotential Θ μ χ ψ ι)
        hU ≤
      diagonalPotentialMass (ClosedRealOneOneForm.pullback hι Θ) (fun y => ψ (ι y)) hψι := by
  have hw : ∀ j : ℕ, IsThetaPshPotential (ClosedRealOneOneForm.pullback hι Θ).val
      (fun y => prescribedEnvelope Θ (cutoffObstacle μ χ j) ψ (ι y) + ((j : ℝ) : EReal)) :=
    fun j => (isThetaPshPotential_prescribedEnvelope_comp hι hg hψ hψι j).add_const _
  refine (IncreasingLimitMass.diagonalPotentialMass_le_iSup_of_monotone _ hw
    (monotone_centralSequence hχ) hU).trans (iSup_le fun j => ?_)
  refine diagonalPotentialMass_mono_of_kahler ωV (hw j) hψι ?_
  obtain ⟨C, hC⟩ := prescribedEnvelope_le_add_of_logSingularities (g := cutoffObstacle μ χ j)
    (Θ := Θ) (hg j) hψ hπ D L
  refine ⟨C + j, fun y _ => ?_⟩
  calc prescribedEnvelope Θ (cutoffObstacle μ χ j) ψ (ι y) + ((j : ℝ) : EReal)
      ≤ ψ (ι y) + (C : EReal) + ((j : ℝ) : EReal) := add_le_add (hC (ι y)) le_rfl
    _ = ψ (ι y) + ((C + j : ℝ) : EReal) := by rw [add_assoc, ← EReal.coe_add]

/-- **WN21 Proposition 7.3**: if `ψ` has a log resolution and `ψ ⪯ φ` for a current
`φ ∈ Ω(Θ)` whose restriction to `ι(V)` is a genuine potential, then
`∫_V ⟨(ι^*Θ + dd^c v_V)ⁿ⟩ ≤ vol_{𝒳|ι(V)}({Θ})` (`TranscendentalVolumeConcavity.restrictedVolume`). -/
theorem diagonalPotentialMass_centralLimitPotential_le_restrictedVolume [CompactSpace 𝒳]
    (ωV : KahlerBackground k V) (hχ : IsWNCutoff χ) (hg : ∀ j, Continuous (cutoffObstacle μ χ j))
    (hψ : IsThetaPshPotential Θ.val ψ)
    (hψι : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι Θ).val (fun y => ψ (ι y)))
    {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel N) Z] [IsComplexManifold N Z]
    [CompactSpace Z] [ConnectedSpace Z] {π : Z → 𝒳} (hπ : IsAnalyticModification (n := N) π)
    (D : SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves.MeteredEffectiveQDivisor N Z)
    (L : ResidualNefReduction.HasLogSingularitiesAlong D (fun z => ψ (π z)))
    {φ : 𝒳 → EReal} (hφ : φ ∈ gentleKahlerCurrents Θ) (hψφ : SGPT.PSH.SingularityLE ψ φ)
    (hφι : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι Θ).val (fun y => φ (ι y)))
    (hU : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι Θ).val
      (centralLimitPotential Θ μ χ ψ ι)) :
    diagonalPotentialMass (ClosedRealOneOneForm.pullback hι Θ) (centralLimitPotential Θ μ χ ψ ι)
        hU ≤ TranscendentalVolumeConcavity.restrictedVolume ι hι Θ := by
  refine (diagonalPotentialMass_centralLimitPotential_le hι ωV hχ hg hψ hψι hπ D L hU).trans ?_
  obtain ⟨C, hC⟩ := hψφ
  refine (diagonalPotentialMass_mono_of_kahler ωV hψι hφι
    ⟨C, fun y _ => hC (ι y) (mem_univ _)⟩).trans ?_
  exact le_iSup_of_le φ (le_iSup_of_le hφ (le_iSup_of_le hφι le_rfl))

end Limit

/-! ### A log resolution of the weight -/

/-- **A log resolution of a gentle Kähler current** (WN21 §7, set-up; `claude-logres:kahler`):
on a compact connected Kähler manifold, a potential `ψ ∈ Ω(Θ)` has an analytic modification
`π : Z → M` from a compact connected manifold along which `ψ ∘ π` has log singularities along a
metered effective `ℚ`-divisor.  This is the input of `prescribedEnvelope_le_add_of_logSingularities`
and of `diagonalPotentialMass_centralLimitPotential_le`. -/
theorem exists_logResolution_of_mem_gentleKahlerCurrents {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    [CompactSpace M] [ConnectedSpace M] (ωM : KahlerBackground (m + 1) M)
    {Θ : ClosedRealOneOneForm (m + 1) M} {ψ : M → EReal} (hψ : ψ ∈ gentleKahlerCurrents Θ) :
    ∃ (Z : Type u) (_ : TopologicalSpace Z) (_ : ChartedSpace (ComplexModel (m + 1)) Z)
      (_ : IsComplexManifold (m + 1) Z) (π : Z → M)
      (D : SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves.MeteredEffectiveQDivisor
        (m + 1) Z),
      CompactSpace Z ∧ ConnectedSpace Z ∧ IsAnalyticModification (n := m + 1) π ∧
        Nonempty (ResidualNefReduction.HasLogSingularitiesAlong D (fun z => ψ (π z))) := by
  obtain ⟨⟨hψpsh, c, 𝔞, -, hgentle⟩, -⟩ := hψ
  obtain ⟨Z, tZ, cZ, mZ, π, hπ, -, EH, hcpt, hconn, -, -, -, -, -, -, hL, -⟩ :=
    SGPT.PSH.exists_kahler_logResolution ωM Θ hψpsh hgentle.2.1
  exact ⟨Z, tZ, cZ, mZ, π, _, hcpt, hconn,
    HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hπ, hL⟩

end SGPT.Okounkov.TranscendentalWN
