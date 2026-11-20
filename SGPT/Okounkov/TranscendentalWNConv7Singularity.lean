import SGPT.Okounkov.TranscendentalWNConv7Envelope
import SGPT.Okounkov.TranscendentalLiftingResolution
import SGPT.Okounkov.TranscendentalWNRegSingular
import SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback
import SGPT.Foundations.Analysis.Pending.IEnvelopeStrongOpenness
import SGPT.Foundations.Analysis.FirstPass.ThetaPshCompactBounds

/-!
# The singularity type of the envelopes `v_k` (WN21 Proposition 7.1; lane WN-CONV7)

Blueprint `claude-tok-wn-conv7`, node `tok-wn-conv7:envelope-singularity`; source WN21 §7,
Proposition 7.1 and the first line of the proof of Proposition 7.3 ("by Proposition 7.1
`|v_k - ψ| ≤ C_k`").

Let `Θ` be a closed real `(1,1)`-form on a compact complex manifold `M`, `g` a continuous obstacle
and `ψ` a `Θ`-psh potential.

* `le_prescribedEnvelope_add`: `ψ ≤ P_Θ[ψ](g) + C` (`ψ - sup ψ + min g` is a competitor).
* `prescribedEnvelope_le_add_of_logSingularities`: if `π : Z → M` is an analytic modification from
  a compact connected manifold and `ψ ∘ π = ψ_D + O(1)` has log singularities along a metered
  effective `ℚ`-divisor `D` (a log resolution of `ψ`, `claude-logres:kahler`), then
  `P_Θ[ψ](g) ≤ ψ + C`.  Hence `P_Θ[ψ](g)` has the singularity type of `ψ`
  (`singularityEquiv_prescribedEnvelope`).

## Proof of the upper bound (WN21 Proposition 7.1, without the Kähler perturbation)

For a competitor `v` (`v ≤ g`, `v ⪯ ψ`), `v' = max(v, ψ)` is `Θ`-psh with `ψ ≤ v' ≤ ψ + C_v`, so
`v' ∘ π` has log singularities along `D`; its residual `b = v' ∘ π - ψ_D` extends to a bounded
`(π^*Θ - Θ_D)`-psh function on `Z` (`TranscendentalLifting.exists_residual_current`, the removable
singularity theorem across `Supp D`).  On a fixed nonempty open set `W ⊆ Z \ Supp D` where
`ψ_D ≥ ψ_D(y₀) - 1`, `b ≤ max(max g, max ψ) - ψ_D(y₀) + 1` — a bound independent of `v`.  The
Hartogs-type bound `TranscendentalWNReg.exists_le_of_quasiEverywhere_le_on_open` (from TN's
uniform `L¹` bound) gives `b ≤ C_H` on `Z` with `C_H` independent of `v`, so
`v ∘ π ≤ ψ_D + C_H ≤ ψ ∘ π + C_H + ‖b_ψ‖_∞`, and `v ≤ ψ + C` on `M` (`π` is onto).  The envelope is
the upper regularization of the supremum of the competitors, and `ψ + C` is upper
semicontinuous.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy

variable {N : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M] {Θ : ClosedRealOneOneForm N M} {g : M → ℝ} {ψ : M → EReal}

/-- **The envelope is less singular than its weight**: `ψ ≤ P_Θ[ψ](g) + C`. -/
theorem le_prescribedEnvelope_add [CompactSpace M] (hg : Continuous g)
    (hψ : IsThetaPshPotential Θ.val ψ) :
    ∃ C : ℝ, ∀ x, ψ x ≤ prescribedEnvelope Θ g ψ x + (C : EReal) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · exact ⟨0, fun x => isEmptyElim x⟩
  obtain ⟨Mψ, hMψ⟩ := hψ.exists_global_upper_bound
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn univ_nonempty hg.continuousOn
  set a : ℝ := g x₀ - Mψ with ha
  have hmem : (fun x => ψ x + (a : EReal)) ∈ prescribedCompetitors Θ g ψ := by
    refine ⟨hψ.add_const a, fun z => ?_, ?_⟩
    · calc ψ z + (a : EReal) ≤ (Mψ : EReal) + (a : EReal) := add_le_add (hMψ z) le_rfl
        _ = (g x₀ : EReal) := by rw [← EReal.coe_add, ha]; ring_nf
        _ ≤ (g z : EReal) := EReal.coe_le_coe_iff.mpr (hx₀ (mem_univ z))
    · exact (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨a, fun z => le_rfl⟩
  refine ⟨-a, fun x => ?_⟩
  have h := add_le_add (le_prescribedEnvelope hmem x) (le_refl ((-a : ℝ) : EReal))
  rwa [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero] at h

/-- Off the support of `D`, the weight `ψ_D` is a real number (it is `≠ ⊥` there, and `≠ ⊤` where
a quasi-psh function with log singularities along `D` lives). -/
private theorem weight_eq_coe_toReal {Z : Type*} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel N) Z] [IsComplexManifold N Z] {D : MeteredEffectiveQDivisor N Z}
    {φ : Z → EReal} (L : ResidualNefReduction.HasLogSingularitiesAlong D φ) (hφ : ∀ y, φ y ≠ ⊤)
    {y : Z} (hy : y ∉ D.support) : D.weight y = ((D.weight y).toReal : EReal) := by
  have hbot : D.weight y ≠ ⊥ := hy
  have htop : D.weight y ≠ ⊤ := by
    intro htop
    apply hφ y
    rw [L.weight_add y, htop, EReal.top_add_coe]
  exact (EReal.coe_toReal htop hbot).symm

/-- **The envelope has at most the singularities of its weight** (WN21 Proposition 7.1, through a
log resolution of `ψ`): if `ψ ∘ π` has log singularities along a metered effective `ℚ`-divisor on
an analytic modification `π : Z → M` from a compact connected manifold, then
`P_Θ[ψ](g) ≤ ψ + C`. -/
theorem prescribedEnvelope_le_add_of_logSingularities [CompactSpace M] (hg : Continuous g)
    (hψ : IsThetaPshPotential Θ.val ψ) {Z : Type u} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel N) Z] [IsComplexManifold N Z] [CompactSpace Z] [ConnectedSpace Z]
    {π : Z → M} (hπ : IsAnalyticModification (n := N) π) (D : MeteredEffectiveQDivisor N Z)
    (L : ResidualNefReduction.HasLogSingularitiesAlong D (fun z => ψ (π z))) :
    ∃ C : ℝ, ∀ x, prescribedEnvelope Θ g ψ x ≤ ψ x + (C : EReal) := by
  have : Nonempty Z := ConnectedSpace.toNonempty
  have hsurj := AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hπ
  have : Nonempty M := ⟨π (Classical.arbitrary Z)⟩
  -- bounds of the data
  obtain ⟨Mψ, hMψ⟩ := hψ.exists_global_upper_bound
  obtain ⟨xg, -, hxg⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hg.continuousOn
  set G : ℝ := max (g xg) Mψ with hG
  have hψtop : ∀ x, ψ x ≠ ⊤ := hψ.1.quasiPlurisubharmonic.ne_top
  have hψπ := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    hπ Θ hψ
  -- a fixed open set off the support on which the weight is bounded below
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, y₀ ∉ D.support := by
    by_contra h
    push Not at h
    exact L.support_ne_univ hψπ.2 (eq_univ_of_forall h)
  obtain ⟨F, hFc, hFeq⟩ :=
    MeteredDivisorWeightBounds.exists_real_continuousAt_eventuallyEq_of_notMem_support D hy₀
  have hnhds : {y | D.weight y = ((F y : ℝ) : EReal) ∧ F y₀ - 1 < F y} ∈ 𝓝 y₀ :=
    hFeq.and (hFc.eventually (lt_mem_nhds (by linarith : F y₀ - 1 < F y₀)))
  obtain ⟨W, hWsub, hWo, hy₀W⟩ := mem_nhds_iff.mp hnhds
  set θ' := ClosedRealOneOneForm.pullback hπ.1 Θ - D.curvature with hθ'
  set c₀ : ℝ := G - (F y₀ - 1) with hc₀
  obtain ⟨CH, hCH⟩ := TranscendentalWNReg.exists_le_of_quasiEverywhere_le_on_open θ' hWo
    ⟨y₀, hy₀W⟩ c₀
  -- the uniform bound of the competitors
  have hcomp : ∀ v ∈ prescribedCompetitors Θ g ψ, ∀ x, v x ≤ ψ x + ((CH + L.bound : ℝ) : EReal) := by
    intro v hv
    obtain ⟨Cv, hCv⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp hv.2.2
    set v' : M → EReal := fun x => max (v x) (ψ x) with hv'def
    have hv' : IsThetaPshPotential Θ.val v' := IsThetaPshPotential.max hv.1 hψ
    have hv'π := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
      hπ Θ hv'
    have hv'le : ∀ x, v' x ≤ ψ x + ((max Cv 0 : ℝ) : EReal) := fun x =>
      max_le ((hCv x).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_max_left _ _))))
        (by
          calc ψ x = ψ x + 0 := (add_zero _).symm
            _ ≤ ψ x + ((max Cv 0 : ℝ) : EReal) :=
              add_le_add le_rfl (EReal.coe_nonneg.mpr (le_max_right _ _)))
    -- off the support, all values are real
    have hreal : ∀ y, y ∉ D.support →
        ψ (π y) = (((D.weight y).toReal + L.residual y : ℝ) : EReal) ∧
        v' (π y) = (((v' (π y)).toReal : ℝ) : EReal) ∧
        (D.weight y).toReal + L.residual y ≤ (v' (π y)).toReal ∧
        (v' (π y)).toReal ≤ (D.weight y).toReal + L.residual y + max Cv 0 := by
      intro y hy
      have hw := weight_eq_coe_toReal L (fun y => hψtop (π y)) hy
      have hψy : ψ (π y) = (((D.weight y).toReal + L.residual y : ℝ) : EReal) := by
        rw [L.weight_add y, hw, ← EReal.coe_add, EReal.toReal_coe]
      have hlo : ψ (π y) ≤ v' (π y) := le_max_right _ _
      have hhi := hv'le (π y)
      rw [hψy, ← EReal.coe_add] at hhi
      rw [hψy] at hlo
      have hne_bot : v' (π y) ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlo
      have hne_top : v' (π y) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hhi
      have hv'y := (EReal.coe_toReal hne_top hne_bot).symm
      refine ⟨hψy, hv'y, ?_, ?_⟩
      · rw [hv'y] at hlo; exact EReal.coe_le_coe_iff.mp hlo
      · rw [hv'y] at hhi; exact EReal.coe_le_coe_iff.mp hhi
    -- the log singularities of `v' ∘ π`
    classical
    let L' : ResidualNefReduction.HasLogSingularitiesAlong D (fun y => v' (π y)) :=
      { residual := fun y => if y ∈ D.support then 0 else (v' (π y)).toReal - (D.weight y).toReal
        bound := L.bound + max Cv 0
        residual_bound := by
          intro y
          by_cases hy : y ∈ D.support
          · simp only [hy, if_true, abs_zero]
            exact add_nonneg ((abs_nonneg _).trans (L.residual_bound y)) (le_max_right _ _)
          · simp only [hy, if_false]
            obtain ⟨-, -, h1, h2⟩ := hreal y hy
            have hr := L.residual_bound y
            rw [abs_le] at hr ⊢
            constructor <;> nlinarith [le_max_right Cv 0]
        weight_add := by
          intro y
          by_cases hy : y ∈ D.support
          · simp only [hy, if_true, EReal.coe_zero, add_zero]
            have hbot : D.weight y = ⊥ := hy
            have hψb : ψ (π y) = ⊥ := by rw [L.weight_add y, hbot, EReal.bot_add]
            rw [hbot]
            refine le_bot_iff.mp ((hv'le (π y)).trans ?_)
            rw [hψb, EReal.bot_add]
          · simp only [hy, if_false]
            obtain ⟨-, hv'y, -, -⟩ := hreal y hy
            rw [weight_eq_coe_toReal L (fun y => hψtop (π y)) hy, ← EReal.coe_add,
              EReal.toReal_coe, add_sub_cancel]
            exact hv'y }
    obtain ⟨b, hb, hbb, hbeq⟩ := TranscendentalLifting.exists_residual_current hv'π L'
    have hbne : ∀ y, b y ≠ ⊥ := fun y =>
      ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hbb y).1
    have hbpot : IsThetaPshPotential θ'.val b :=
      ⟨hb, fun x U _ hx => ⟨x, hx, hbne x⟩⟩
    have hbW : QuasiEverywhere (n := N) (fun y => y ∈ W → b y ≤ (c₀ : EReal)) := by
      refine quasiEverywhere_of_forall fun y hyW => ?_
      obtain ⟨hwF, hFy⟩ := hWsub hyW
      have hyD : y ∉ D.support := fun h => by
        have hbot : D.weight y = ⊥ := h
        rw [hwF] at hbot
        exact EReal.coe_ne_bot _ hbot
      have hbtop : b y ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) (hbb y).2
      have hby := (EReal.coe_toReal hbtop (hbne y)).symm
      have hv'G : v' (π y) ≤ (G : EReal) := max_le
        ((hv.2.1 (π y)).trans (EReal.coe_le_coe_iff.mpr ((hxg (mem_univ _)).trans
          (le_max_left _ _))))
        ((hMψ (π y)).trans (EReal.coe_le_coe_iff.mpr (le_max_right _ _)))
      have heq := hbeq y
      rw [hwF, hby, ← EReal.coe_add] at heq
      rw [heq] at hv'G
      have h := EReal.coe_le_coe_iff.mp hv'G
      rw [hby]
      exact EReal.coe_le_coe_iff.mpr (by rw [hc₀]; linarith)
    have hbCH := hCH b hbpot hbW
    -- transfer to `M`
    intro x
    obtain ⟨y, rfl⟩ := hsurj x
    have hvv' : v (π y) ≤ v' (π y) := le_max_left _ _
    by_cases hy : y ∈ D.support
    · have hbot : D.weight y = ⊥ := hy
      have hψb : ψ (π y) = ⊥ := by rw [L.weight_add y, hbot, EReal.bot_add]
      have hvb : v (π y) = ⊥ := le_bot_iff.mp ((hCv (π y)).trans (by rw [hψb, EReal.bot_add]))
      rw [hvb]
      exact bot_le
    · obtain ⟨hψy, -, -, -⟩ := hreal y hy
      have hw := weight_eq_coe_toReal L (fun y => hψtop (π y)) hy
      have hbtop : b y ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) (hbb y).2
      have hby := (EReal.coe_toReal hbtop (hbne y)).symm
      have heq := hbeq y
      rw [hw, hby, ← EReal.coe_add] at heq
      have hbC : (b y).toReal ≤ CH := by
        have h := hbCH y
        rw [hby] at h
        exact EReal.coe_le_coe_iff.mp h
      have hr := L.neg_bound_le y
      refine hvv'.trans ?_
      show v' (π y) ≤ ψ (π y) + ((CH + L.bound : ℝ) : EReal)
      rw [heq, hψy, ← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (by linarith)
  -- the envelope
  refine ⟨CH + L.bound, ?_⟩
  have husc : UpperSemicontinuous (fun x => ψ x + ((CH + L.bound : ℝ) : EReal)) :=
    upperSemicontinuous_add_coe_const hψ.1.quasiPlurisubharmonic.upperSemicontinuous _
  exact uscRegularization_le husc (fun y => iSup_le fun w => hcomp w.1 w.2 y)

/-- **`P_Θ[ψ](g)` has the singularity type of `ψ`** when `ψ` has a log resolution
(WN21 §7: `|v_k - ψ| ≤ C_k`, from Proposition 7.1). -/
theorem singularityEquiv_prescribedEnvelope [CompactSpace M] (hg : Continuous g)
    (hψ : IsThetaPshPotential Θ.val ψ) {Z : Type u} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel N) Z] [IsComplexManifold N Z] [CompactSpace Z] [ConnectedSpace Z]
    {π : Z → M} (hπ : IsAnalyticModification (n := N) π) (D : MeteredEffectiveQDivisor N Z)
    (L : ResidualNefReduction.HasLogSingularitiesAlong D (fun z => ψ (π z))) :
    SGPT.PSH.SingularityLE (prescribedEnvelope Θ g ψ) ψ ∧
      SGPT.PSH.SingularityLE ψ (prescribedEnvelope Θ g ψ) := by
  obtain ⟨C₁, hC₁⟩ := prescribedEnvelope_le_add_of_logSingularities hg hψ hπ D L
  obtain ⟨C₂, hC₂⟩ := le_prescribedEnvelope_add (Θ := Θ) hg hψ
  exact ⟨(SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨C₁, hC₁⟩,
    (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨C₂, hC₂⟩⟩

end SGPT.Okounkov.TranscendentalWN
