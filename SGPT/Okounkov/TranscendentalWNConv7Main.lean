import SGPT.Okounkov.TranscendentalWNConv7Envelope
import SGPT.Okounkov.TranscendentalWNVolumeFibre
import SGPT.Okounkov.TranscendentalWNDeformationBig
import SGPT.Okounkov.TranscendentalBodySingDecrease
import SGPT.Foundations.Analysis.Pending.ContinuousObstacleEnvelopeContact
import SGPT.Foundations.Analysis.Pending.MinimalSingularityLelongVanishing
import SGPT.Foundations.Analysis.Pending.SubmanifoldKahlerRestriction

/-!
# The hard inequality of the key equality from measure control

Blueprint `claude-tok-wn-conv7`, node `tok-wn-conv7:assembly` (refining `tok-wn:convergence` of
`claude-tok-wn`); source WN21 §7, proof of the hard inequality of Theorem 1.7.

`keyConvergence_of_contactMassLimit_of_cutoff`: for a cutoff `χ` whose obstacles `g_k` are
continuous, `MeasureControlStatement F` (WN21 Corollary 6.5, lane WN-CONV6) and
`ContactMassLimitStatement F` (the analytic core of WN21 §7) give `KeyConvergenceStatement F`:
`vol(ξ) ≤ vol_{𝒳|X'}(β + ε{η'}) + vol_{𝒳|ℰ}(β + ε{η'})`.

## Proof (WN21 §7)

Let `τ_k` be the sequence of measure control, `s_k` the sections of `μ` over `x ↦ (x, τ_k)`
(`exists_fibreSection`), `ψ` the weight of the analytic core, `u_k = P_{θ̃}(g_k)` and
`v_k = P_Θ[ψ](g_k)`, `Θ = θ̃ + εη'`.

* `u_k` is `θ̃`-psh with `u_k ≤ g_k` (`β` is big, `g_k` continuous); `u_k ≤ V_{θ̃} + max g_k ⪯ ψ`,
  so `u_k` is a competitor of `v_k` (`Θ - θ̃ = εη' ≥ 0`) and `u_k ≤ v_k ≤ g_k`.
* `u_k` has minimal singularities in `β`, so `u_k ∘ s_k` is a genuine `s_k^*θ̃`-psh potential
  (`tok-wn:formula-fibre`, `restrictedVolume_fibre`), hence so is `v_k ∘ s_k ≥ u_k ∘ s_k` for `s_k^*Θ`.
* `g_k` is constant on `X_{τ_k}`, so the fibrewise contact estimate (MAest,
  `positiveTopMeasure_contact_le`) gives `I_k(τ_k) ≤ ∫_{X_{τ_k} ∩ D'_k} MA(v_k|_{X_{τ_k}})`.
* `I_k(τ_k) → vol(ξ)` (measure control), so
  `vol(ξ) ≤ liminf_k ∫_{X_{τ_k} ∩ D'_k} MA(v_k|_{X_{τ_k}}) ≤ vol_{𝒳|X'}(β + ε{η'}) + vol_{𝒳|ℰ}(β + ε{η'})`
  (the analytic core); both restricted volumes are finite (`restrictedVolume_lt_top`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Okounkov.TranscendentalMain
open SGPT.Okounkov.TranscendentalVolumeConcavity

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- The point of `ℙ¹` with affine coordinate `τ ≠ 0` is not `0` (also
`affineLinePoint_ne_projectiveZero` in `TranscendentalWNConv6Obstacle`; kept private here so that this
file does not depend on the files). -/
private theorem affineLinePoint_ne_zero' {τ : ℂ} (hτ : τ ≠ 0) :
    affineLinePoint τ ≠ projectiveZero := fun h =>
  hτ (OnePoint.coe_injective (SGPT.Toric.projectiveLineHomeomorph.injective h))

/-- **`tok-wn:convergence` from measure control and the analytic core** (WN21 §7, proof of the
hard inequality of Theorem 1.7; blueprint `tok-wn-conv7:assembly`): for a cutoff `χ` with
continuous obstacles `g_k`, `MeasureControlStatement F` and `ContactMassLimitStatement F` give
`KeyConvergenceStatement F`. -/
theorem keyConvergence_of_contactMassLimit_of_cutoff {χ : ℝ → ℝ} (hχ : IsWNCutoff χ)
    (hgc : ∀ k, Continuous (cutoffObstacleLine χ k)) (hMC : MeasureControlStatement F)
    (hCore : ContactMassLimitStatement F) : KeyConvergenceStatement F := by
  intro E hE hE0 𝒳 _ _ _ μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc ι hι hμι η' ε hε
  set θ₀ := deformationForm F hμ.contMDiff θ b c Eℰ with hθ₀
  set Θ := θ₀ + ε • η'.form with hΘ
  have := compactSpace_normalCone F hμ
  have := connectedSpace_normalCone F hμ
  have hne𝒳 : Nonempty 𝒳 := ConnectedSpace.toNonempty
  let : MeasurableSpace F.carrier := borel F.carrier
  have : BorelSpace F.carrier := ⟨rfl⟩
  -- `β` is big
  obtain ⟨hbig, -, -, -⟩ := betaBig F E hE 𝒳 μ hμ Eℰ hEℰ.isDivisorMetric θ b c hc
    (by linarith) hξ hξc.1
  have hbigC : IsBigClass (RealBottChern.ofRepresentative θ₀) :=
    (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp hbig
  have hV : IsThetaPshPotential θ₀.val (thetaPshSupremum θ₀.val) :=
    MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum θ₀ hbigC
  have hΘθ₀ : (Θ - θ₀).val.IsSemipositive := by
    rw [hΘ, add_sub_cancel_left]
    exact KahlerDomination.isSemipositive_smul η'.isSemipositive hε.le
  -- measure control and the analytic core
  obtain ⟨τ, hτ0, hτlim, hMCk⟩ := hMC E hE hE0 𝒳 μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc χ hχ
  obtain ⟨ψ, -, hVψ, hcore⟩ :=
    hCore E hE hE0 𝒳 μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc ι hι hμι η' ε hε χ hχ
  obtain ⟨Cψ, hCψ⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp hVψ
  -- the sections over `τ_k`
  choose s hs hμs _hrange using fun k =>
    exists_fibreSection F hμ (affineLinePoint_ne_zero' (hτ0 k))
  -- the obstacles, the envelopes `u_k` and `v_k`
  have hμc : Continuous μ := hμ.contMDiff.continuous
  have hg : ∀ k, Continuous (cutoffObstacle μ χ k) := fun k =>
    (hgc k).comp (continuous_snd.comp hμc)
  have hgs : ∀ k x, cutoffObstacle μ χ k (s k x) = cutoffObstacleLine χ k (affineLinePoint (τ k)) :=
    fun k x => by simp only [cutoffObstacle, hμs k x]
  have hn : 0 < m + 1 + 1 := Nat.succ_pos _
  have hu : ∀ k, IsThetaPshPotential θ₀.val (cutoffEnvelope θ₀ μ χ k) := fun k =>
    ContinuousObstacleEnvelopeContact.isThetaPshPotential_rooftopEnvelope_of_continuous hn θ₀
      hbigC (hg k)
  have hug : ∀ k z, cutoffEnvelope θ₀ μ χ k z ≤ (cutoffObstacle μ χ k z : EReal) := fun k z =>
    ContinuousObstacleEnvelopeContact.rooftopEnvelope_le_of_continuous (hg k)
      (ContinuousObstacleEnvelopeContact.rooftopCompetitors_nonempty_of_isBigClass hn θ₀ hbigC
        (hg k)) (hu k).1 z
  -- bounds of the obstacles
  have hgmax : ∀ k, ∃ B : ℝ, ∀ z, cutoffObstacle μ χ k z ≤ B := fun k => by
    obtain ⟨z₀, -, hz₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty (hg k).continuousOn
    exact ⟨_, fun z => hz₀ (mem_univ z)⟩
  have hgmin : ∀ k, ∃ B : ℝ, ∀ z, B ≤ cutoffObstacle μ χ k z := fun k => by
    obtain ⟨z₀, -, hz₀⟩ := isCompact_univ.exists_isMinOn univ_nonempty (hg k).continuousOn
    exact ⟨_, fun z => hz₀ (mem_univ z)⟩
  -- `u_k` is a competitor of `v_k`
  have hmem : ∀ k, cutoffEnvelope θ₀ μ χ k ∈
      prescribedCompetitors Θ (cutoffObstacle μ χ k) ψ := fun k => by
    obtain ⟨B, hB⟩ := hgmax k
    refine ⟨TranscendentalBody.isThetaPshPotential_of_le (hu k) hΘθ₀, hug k, ?_⟩
    -- `u_k - B ≤ 0` is `θ̃`-psh, so `u_k ≤ V_{θ̃} + B ≤ ψ + Cψ + B`
    have hle0 : (fun z => cutoffEnvelope θ₀ μ χ k z + ((-B : ℝ) : EReal)) ≤ 0 := fun z => by
      have h := add_le_add ((hug k z).trans (EReal.coe_le_coe_iff.mpr (hB z)))
        (le_refl ((-B : ℝ) : EReal))
      rwa [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] at h
    have hV' := le_thetaPshSupremum ((hu k).add_const (-B)) hle0
    refine (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨Cψ + B, fun z => ?_⟩
    have h1 := add_le_add (hV' z) (le_refl ((B : ℝ) : EReal))
    rw [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero] at h1
    calc cutoffEnvelope θ₀ μ χ k z ≤ thetaPshSupremum θ₀.val z + (B : EReal) := h1
      _ ≤ ψ z + (Cψ : EReal) + (B : EReal) := add_le_add (hCψ z) le_rfl
      _ = ψ z + ((Cψ + B : ℝ) : EReal) := by rw [add_assoc, ← EReal.coe_add]
  set v : ℕ → 𝒳 → EReal := fun k => prescribedEnvelope Θ (cutoffObstacle μ χ k) ψ with hvdef
  have huv : ∀ k z, cutoffEnvelope θ₀ μ χ k z ≤ v k z := fun k => le_prescribedEnvelope (hmem k)
  have hvg : ∀ k z, v k z ≤ (cutoffObstacle μ χ k z : EReal) := fun k =>
    prescribedEnvelope_le (hg k)
  have hvΘ : ∀ k, IsThetaPshPotential Θ.val (v k) := fun k => by
    obtain ⟨B, hB⟩ := hgmax k
    exact isThetaPshPotential_prescribedEnvelope ⟨_, hmem k⟩ hB
  -- `v_k ∘ s_k` is a genuine potential on `X ≅ X_{τ_k}`
  have hFib := restrictedVolume_fibre F (betaBig F) E hE hE0 𝒳 μ hμ Eℰ hEℰ θ b c hc
    (by linarith) hξ hξc
  have hw : ∀ k, IsThetaPshPotential (ClosedRealOneOneForm.pullback (hs k) Θ).val
      (fun x => v k (s k x)) := fun k => by
    obtain ⟨B, hB⟩ := hgmin k
    -- `u_k` has minimal singularities: `V_{θ̃} + min g_k ≤ u_k`
    have hmin : MoreSingularOn (thetaPshSupremum θ₀.val) (cutoffEnvelope θ₀ μ χ k) univ := by
      have hcomp : (fun z => thetaPshSupremum θ₀.val z + (B : EReal)) ≤
          cutoffEnvelope θ₀ μ χ k := by
        refine le_rooftopEnvelope (hV.add_const B) (quasiEverywhere_of_forall fun z => ?_)
        calc thetaPshSupremum θ₀.val z + (B : EReal) ≤ 0 + (B : EReal) :=
              add_le_add (thetaPshSupremum_le_zero _ z) le_rfl
          _ = (B : EReal) := zero_add _
          _ ≤ (cutoffObstacle μ χ k z : EReal) := EReal.coe_le_coe_iff.mpr (hB z)
      refine ⟨-B, fun z _ => ?_⟩
      have h := add_le_add (hcomp z) (le_refl ((-B : ℝ) : EReal))
      rwa [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero] at h
    have hus := ((hFib (affineLinePoint (τ k)) (affineLinePoint_ne_zero' (hτ0 k))
      (s k) (hs k) (hμs k)).2 _ (hu k) hmin).1
    exact ⟨GlobalPotentialPullback.thetaPlurisubharmonic_comp (hs k) (hvΘ k).1,
      hus.2.mono fun x => huv k (s k x)⟩
  -- MAest on each fibre
  have hest : ∀ k, fibreContactMass F θ₀ μ χ k (s k) (hs k) ≤
      envelopeContactMass F Θ (cutoffObstacle μ χ k) ψ (s k) (hs k) (hw k) := fun k =>
    positiveTopMeasure_contact_le F.omega hΘθ₀ (hs k) (hgs k) (hu k).1 (hug k) (huv k) (hvg k)
      (hw k)
  -- the limit
  have hlimI := hMCk s hs hμs
  have hcore' := hcore τ hτ0 hτlim s hs hμs hw
  have hvol : ENNReal.ofReal (classVolumeReal F (RealBottChern.ofRepresentative θ)) ≤
      sectionRestrictedVolume F ι hι
          (RealBottChern.ofRepresentative θ₀ + ε • RealBottChern.ofRepresentative η'.form) +
        exceptionalRestrictedVolume F hμ
          (RealBottChern.ofRepresentative θ₀ + ε • RealBottChern.ofRepresentative η'.form) := by
    rw [← hlimI.liminf_eq]
    exact (liminf_le_liminf (Eventually.of_forall hest)).trans hcore'
  -- both restricted volumes are finite
  have hclass : RealBottChern.ofRepresentative θ₀ + ε • RealBottChern.ofRepresentative η'.form =
      RealBottChern.ofRepresentative Θ := by
    rw [hΘ, RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul]
  have hX'fin : sectionRestrictedVolume F ι hι
      (RealBottChern.ofRepresentative θ₀ + ε • RealBottChern.ofRepresentative η'.form) ≠ ⊤ := by
    rw [hclass]
    unfold sectionRestrictedVolume
    rw [← restrictedVolume_eq_classRestrictedVolume hι Θ]
    exact (restrictedVolume_lt_top hι F.omega Θ).ne
  have hEfin : exceptionalRestrictedVolume F hμ
      (RealBottChern.ofRepresentative θ₀ + ε • RealBottChern.ofRepresentative η'.form) ≠ ⊤ := by
    rw [hclass]
    let := exceptionalChartedSpace F hμ
    have := isComplexManifold_exceptional F hμ
    let : MeasurableSpace (exceptionalSet F μ) := borel (exceptionalSet F μ)
    have : BorelSpace (exceptionalSet F μ) := ⟨rfl⟩
    have := compactSpace_exceptional F hμ
    let ωE : KahlerBackground (m + 1) (exceptionalSet F μ) :=
      SubmanifoldKahlerRestriction.kahlerBackground (Nat.le_succ (m + 1))
        (fun _ hz => regularAtDim_exceptionalSet F hμ hz) η'
    unfold exceptionalRestrictedVolume
    rw [← restrictedVolume_eq_classRestrictedVolume (contMDiff_exceptionalInclusion F hμ) Θ]
    exact (restrictedVolume_lt_top (contMDiff_exceptionalInclusion F hμ) ωE Θ).ne
  rw [← ENNReal.toReal_add hX'fin hEfin]
  exact (ENNReal.ofReal_le_iff_le_toReal (ENNReal.add_ne_top.mpr ⟨hX'fin, hEfin⟩)).mp hvol

end SGPT.Okounkov.TranscendentalWN
