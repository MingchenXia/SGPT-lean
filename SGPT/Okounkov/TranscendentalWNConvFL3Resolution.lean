import SGPT.Okounkov.TranscendentalWNConvFLStatement
import SGPT.Okounkov.TranscendentalWNConv7Singularity
import SGPT.Okounkov.TranscendentalLiftingExtension
import SGPT.Okounkov.TranscendentalLiftingIntegral
import SGPT.Foundations.Analysis.Pending.HironakaChowLemma
import SGPT.Foundations.Analysis.Pending.DivisorialDomination
import SGPT.Foundations.Analysis.Pending.ContinuousObstacleEnvelopeContact
import SGPT.Foundations.Analysis.Pending.MeteredDivisorWeightBounds
import SGPT.Foundations.Analysis.FirstPass.UscRegularizationContinuous

/-!
# The envelope `v = P_Θ[Ψ](g)` on a log resolution of `Ψ` (WN21 Proposition 7.1; lane WN-FL3)

Blueprint `claude-tok-wn-fl3`, node `tok-wn-fl3:resolution-identity` (refining
`tok-wn-fl:resolution-identity`); source D. Witt Nyström, arXiv:2103.03660 (WN21), §7,
Proposition 7.1: `v_k ∘ π = ṽ_k + ψ ∘ π` (`references/wn21-restricted-volume`).

Let `Θ` be a closed real `(1,1)`-form on a compact manifold `𝒳`, `Ψ` a `Θ`-psh potential,
`π : 𝒵 → 𝒳` a finite sequence of blow-ups from a compact connected manifold with exceptional locus
in `Supp D'`, `Ψ ∘ π = ψ_{D'} + h` (`h` smooth) and `ω̃ = π^*Θ - Θ_{D'} + dd^c h` Kähler (in fact
only the closedness of the forms is used, not the Kähler property).  Then for every continuous `g`
(`prescribedEnvelopeResolution`, the statement `PrescribedEnvelopeResolutionStatement`):

`P_Θ[Ψ](g) ∘ π = P_{ω̃}(g ∘ π - Ψ ∘ π) + Ψ ∘ π`

on `𝒵`, where `P_{ω̃}` is the rooftop envelope (`rooftopEnvelope`, competitors below the obstacle
quasi-everywhere) and `g ∘ π - Ψ ∘ π = +∞` on `Supp D'` (both sides are `-∞` there).

## Proof

* `≤`: the envelope `v = P_Θ[Ψ](g)` is itself a competitor (it is `Θ`-psh, below `g`, and
  `v ≤ Ψ + C` by `prescribedEnvelope_le_add_of_logSingularities`, lane WN-CONV7), and
  `Ψ + c ≤ v`.  Hence `v ∘ π` has log singularities along `D'`
  (`HasLogSingularitiesAlong.ofBetween`), and the residual `b = v ∘ π - ψ_{D'}` extends across
  `Supp D'` to a bounded `(π^*Θ - Θ_{D'})`-psh function (`TranscendentalLifting.exists_residual_current`,
  the removable singularity theorem).  So `b - h` is an `ω̃`-psh competitor of `g ∘ π - Ψ ∘ π`,
  whence `v ∘ π = (b - h) + Ψ ∘ π ≤ P_{ω̃}(g ∘ π - Ψ ∘ π) + Ψ ∘ π` off `Supp D'`; on `Supp D'` the
  left side is `-∞`.
* `≥`: for an `ω̃`-psh `u ≤ g ∘ π - Ψ ∘ π` q.e., `w = ψ_{D'} + (u + h) = u + Ψ ∘ π` is `π^*Θ`-psh
  (`DivisorialDomination.isThetaPshPotential_weight_add`) and `≤ g ∘ π` q.e., hence everywhere
  (`g ∘ π` is continuous); it descends to a `Θ`-psh `φ` with `φ ∘ π = w`
  (`TranscendentalLifting.exists_descent`, the Zariski bijection), which is a competitor of `v`
  (`φ ≤ g`, `φ ≤ Ψ + sup u`).  So `u + Ψ ∘ π ≤ v ∘ π`.  Off `Supp D'`, `Ψ ∘ π` is real and
  continuous, so `u ≤ v ∘ π - Ψ ∘ π` near each such point, with an upper semicontinuous right
  side; the upper regularization of the supremum of the `u` stays below it
  (TN `uscRegularization_le_of_eventually_le`).
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
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy

/-! ### Generalities -/

section Psh

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M]

/-- `b ∈ PSH(θ)` gives `b - h ∈ PSH(θ + dd^c h)` for a chart-smooth `h`. -/
theorem thetaPlurisubharmonic_sub_of_add_ddc {θ : ClosedRealOneOneForm N M} {h : M → ℝ}
    (hh : ChartSmooth (n := N) h) {b : M → EReal} (hb : ThetaPlurisubharmonic θ.val b) :
    ThetaPlurisubharmonic (θ + ddcClosedForm h hh).val (fun z => b z - (h z : EReal)) :=
  GlobalPotentialTransforms.thetaPlurisubharmonic_sub_smooth hh (fun _ _ _ => rfl) hb

/-- `u ∈ PSH(θ + dd^c h)` gives `u + h ∈ PSH(θ)` for a chart-smooth `h`. -/
theorem thetaPlurisubharmonic_add_of_add_ddc {θ : ClosedRealOneOneForm N M} {h : M → ℝ}
    (hh : ChartSmooth (n := N) h) {u : M → EReal}
    (hu : ThetaPlurisubharmonic (θ + ddcClosedForm h hh).val u) :
    ThetaPlurisubharmonic θ.val (fun z => u z + (h z : EReal)) := by
  have hnh : ChartSmooth (n := N) (fun z => -h z) := fun e => (hh e).neg
  have key := GlobalPotentialTransforms.thetaPlurisubharmonic_sub_smooth hnh
    (θ := (θ + ddcClosedForm h hh).val) (η := θ.val) (fun e z hz => by
      rw [ClosedRealOneOneForm.coeff_add, ddcClosedForm_coeff,
        smoothDDC_neg e.val.open_target (hh e) hz]
      abel) hu
  have hfun : (fun z => u z - (((-h z : ℝ)) : EReal)) = fun z => u z + (h z : EReal) := by
    funext z
    rw [sub_eq_add_neg, EReal.coe_neg, neg_neg]
  rwa [hfun] at key

end Psh

/-! ### Log singularities of functions squeezed between two translates -/

section LogSing

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M] {D : MeteredEffectiveQDivisor N M} {φ : M → EReal}

/-- Off the support of `D`, the weight `ψ_D` is real when `φ = ψ_D + b` is finite-valued above. -/
theorem weight_eq_coe_toReal_of_logSing (L : ResidualNefReduction.HasLogSingularitiesAlong D φ)
    (hφ : ∀ y, φ y ≠ ⊤) {y : M} (hy : y ∉ D.support) :
    D.weight y = ((D.weight y).toReal : EReal) := by
  have hbot : D.weight y ≠ ⊥ := hy
  have htop : D.weight y ≠ ⊤ := by
    intro htop
    apply hφ y
    rw [L.weight_add y, htop, EReal.top_add_coe]
  exact (EReal.coe_toReal htop hbot).symm

/-- **Log singularities pass to functions between two translates**: if `φ = ψ_D + O(1)` and
`φ + a ≤ w ≤ φ + C`, then `w = ψ_D + O(1)`. -/
def HasLogSingularitiesAlong.ofBetween (L : ResidualNefReduction.HasLogSingularitiesAlong D φ)
    (hφ : ∀ y, φ y ≠ ⊤) {w : M → EReal} (a C : ℝ) (hlo : ∀ y, φ y + (a : EReal) ≤ w y)
    (hhi : ∀ y, w y ≤ φ y + (C : EReal)) :
    ResidualNefReduction.HasLogSingularitiesAlong D w := by
  classical
  -- off the support, all values are real
  have hreal : ∀ y, y ∉ D.support →
      w y = (((w y).toReal : ℝ) : EReal) ∧
      (D.weight y).toReal + L.residual y + a ≤ (w y).toReal ∧
      (w y).toReal ≤ (D.weight y).toReal + L.residual y + C := by
    intro y hy
    have hw := weight_eq_coe_toReal_of_logSing L hφ hy
    have hφy : φ y = (((D.weight y).toReal + L.residual y : ℝ) : EReal) := by
      rw [L.weight_add y, hw, ← EReal.coe_add, EReal.toReal_coe]
    have hl := hlo y
    have hh := hhi y
    rw [hφy, ← EReal.coe_add] at hl hh
    have hne_bot : w y ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hl
    have hne_top : w y ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hh
    have hwy := (EReal.coe_toReal hne_top hne_bot).symm
    refine ⟨hwy, ?_, ?_⟩
    · rw [hwy] at hl; exact EReal.coe_le_coe_iff.mp hl
    · rw [hwy] at hh; exact EReal.coe_le_coe_iff.mp hh
  exact
    { residual := fun y => if y ∈ D.support then 0 else (w y).toReal - (D.weight y).toReal
      bound := L.bound + |a| + |C|
      residual_bound := by
        intro y
        by_cases hy : y ∈ D.support
        · simp only [hy, if_true, abs_zero]
          exact add_nonneg (add_nonneg ((abs_nonneg _).trans (L.residual_bound y))
            (abs_nonneg _)) (abs_nonneg _)
        · simp only [hy, if_false]
          obtain ⟨-, h1, h2⟩ := hreal y hy
          have hr := L.residual_bound y
          rw [abs_le] at hr ⊢
          constructor <;> nlinarith [le_abs_self a, neg_abs_le a, le_abs_self C, neg_abs_le C]
      weight_add := by
        intro y
        by_cases hy : y ∈ D.support
        · simp only [hy, if_true, EReal.coe_zero, add_zero]
          have hbot : D.weight y = ⊥ := hy
          have hφb : φ y = ⊥ := by rw [L.weight_add y, hbot, EReal.bot_add]
          rw [hbot]
          refine le_bot_iff.mp ((hhi y).trans ?_)
          rw [hφb, EReal.bot_add]
        · simp only [hy, if_false]
          obtain ⟨hwy, -, -⟩ := hreal y hy
          rw [weight_eq_coe_toReal_of_logSing L hφ hy, ← EReal.coe_add, EReal.toReal_coe,
            add_sub_cancel]
          exact hwy }

end LogSing

/-! ### WN21 Proposition 7.1 -/

section Resolution

variable {N : ℕ} {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel N) 𝒳]
  [IsComplexManifold N 𝒳] {𝒵 : Type u} [TopologicalSpace 𝒵] [ChartedSpace (ComplexModel N) 𝒵]
  [IsComplexManifold N 𝒵]

/-- **The upper bound of WN21 Proposition 7.1**: `P_Θ[Ψ](g) ∘ π ≤ P_{ω̃}(g ∘ π - Ψ ∘ π) + Ψ ∘ π`
for an analytic modification `π` from a compact connected manifold along which
`Ψ ∘ π = ψ_{D'} + h`, `ω̃ = π^*Θ - Θ_{D'} + dd^c h`. -/
theorem prescribedEnvelope_comp_le [CompactSpace 𝒳] [CompactSpace 𝒵] [ConnectedSpace 𝒵]
    {Θ : ClosedRealOneOneForm N 𝒳} {Ψ : 𝒳 → EReal} (hΨ : IsThetaPshPotential Θ.val Ψ)
    {π : 𝒵 → 𝒳} (hπ : IsAnalyticModification (n := N) π) (D' : MeteredEffectiveQDivisor N 𝒵)
    {h : 𝒵 → ℝ} (hh : ChartSmooth (n := N) h) (hΨπ : ∀ z, Ψ (π z) = D'.weight z + (h z : EReal))
    {g : 𝒳 → ℝ} (hg : Continuous g) (z : 𝒵) :
    prescribedEnvelope Θ g Ψ (π z) ≤
      rooftopEnvelope ((ClosedRealOneOneForm.pullback hπ.1 Θ - D'.curvature) +
          ddcClosedForm h hh).val (fun y => (g (π y) : EReal) - Ψ (π y)) z + Ψ (π z) := by
  have : Nonempty 𝒵 := ConnectedSpace.toNonempty
  have : Nonempty 𝒳 := ⟨π (Classical.arbitrary 𝒵)⟩
  have hΨtop : ∀ x, Ψ x ≠ ⊤ := hΨ.1.quasiPlurisubharmonic.ne_top
  -- the log singularities of `Ψ ∘ π`
  obtain ⟨Bh, hBh⟩ := isCompact_univ.exists_bound_of_continuousOn
    (ProductTestForms.ChartSmooth.continuous hh).continuousOn
  let L : ResidualNefReduction.HasLogSingularitiesAlong D' (fun z => Ψ (π z)) :=
    { residual := h
      bound := Bh
      residual_bound := fun y => by simpa [Real.norm_eq_abs] using hBh y (mem_univ y)
      weight_add := hΨπ }
  -- the envelope is a competitor, squeezed between two translates of `Ψ`
  set v := prescribedEnvelope Θ g Ψ with hvdef
  obtain ⟨C, hC⟩ := prescribedEnvelope_le_add_of_logSingularities (Θ := Θ) hg hΨ hπ D' L
  obtain ⟨MΨ, hMΨ⟩ := hΨ.exists_global_upper_bound
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn univ_nonempty hg.continuousOn
  obtain ⟨xm, -, hxm⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hg.continuousOn
  set c₀ : ℝ := g x₀ - MΨ with hc₀
  have hmem : (fun x => Ψ x + (c₀ : EReal)) ∈ prescribedCompetitors Θ g Ψ := by
    refine ⟨hΨ.add_const c₀, fun x => ?_,
      (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨c₀, fun x => le_rfl⟩⟩
    calc Ψ x + (c₀ : EReal) ≤ (MΨ : EReal) + (c₀ : EReal) := add_le_add (hMΨ x) le_rfl
      _ = (g x₀ : EReal) := by rw [← EReal.coe_add, hc₀]; ring_nf
      _ ≤ (g x : EReal) := EReal.coe_le_coe_iff.mpr (hx₀ (mem_univ x))
  have hlo : ∀ x, Ψ x + (c₀ : EReal) ≤ v x := le_prescribedEnvelope hmem
  have hvpsh : IsThetaPshPotential Θ.val v :=
    isThetaPshPotential_prescribedEnvelope ⟨_, hmem⟩ (B := g xm) fun x => hxm (mem_univ x)
  have hvπ := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    hπ Θ hvpsh
  let Lv : ResidualNefReduction.HasLogSingularitiesAlong D' (fun y => v (π y)) :=
    HasLogSingularitiesAlong.ofBetween L (fun y => hΨtop (π y)) c₀ C (fun y => hlo (π y))
      (fun y => hC (π y))
  -- the residual current
  obtain ⟨b, hb, hbb, hbeq⟩ := TranscendentalLifting.exists_residual_current hvπ Lv
  have hbne : ∀ y, b y ≠ ⊥ := fun y => ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hbb y).1
  have hbtop : ∀ y, b y ≠ ⊤ := fun y => ne_top_of_le_ne_top (EReal.coe_ne_top _) (hbb y).2
  set ωt := (ClosedRealOneOneForm.pullback hπ.1 Θ - D'.curvature) + ddcClosedForm h hh with hωt
  set f : 𝒵 → EReal := fun y => (g (π y) : EReal) - Ψ (π y) with hf
  -- `b - h` is a competitor of the rooftop envelope
  have hupsh : IsThetaPshPotential ωt.val (fun y => b y - (h y : EReal)) :=
    ⟨thetaPlurisubharmonic_sub_of_add_ddc hh hb, fun x U _ hx =>
      ⟨x, hx, by
        show b x - (h x : EReal) ≠ ⊥
        rw [(EReal.coe_toReal (hbtop x) (hbne x)).symm, ← EReal.coe_sub]
        exact EReal.coe_ne_bot _⟩⟩
  have hule : ∀ y, b y - (h y : EReal) ≤ f y := by
    intro y
    by_cases hy : y ∈ D'.support
    · have hbot : D'.weight y = ⊥ := hy
      have hΨb : Ψ (π y) = ⊥ := by rw [hΨπ y, hbot, EReal.bot_add]
      simp only [hf, hΨb, EReal.coe_sub_bot, le_top]
    · have hw := weight_eq_coe_toReal_of_logSing L (fun y => hΨtop (π y)) hy
      have hby := (EReal.coe_toReal (hbtop y) (hbne y)).symm
      have hvg : v (π y) ≤ (g (π y) : EReal) := prescribedEnvelope_le hg (π y)
      rw [hbeq y, hw, hby, ← EReal.coe_add] at hvg
      have hvg' := EReal.coe_le_coe_iff.mp hvg
      simp only [hf]
      rw [hΨπ y, hw, hby, ← EReal.coe_sub, ← EReal.coe_add, ← EReal.coe_sub]
      exact EReal.coe_le_coe_iff.mpr (by linarith)
  have hle : ∀ y, b y - (h y : EReal) ≤ rooftopEnvelope ωt.val f y :=
    le_rooftopEnvelope hupsh (quasiEverywhere_of_forall hule)
  -- conclusion
  by_cases hz : z ∈ D'.support
  · have hbot : D'.weight z = ⊥ := hz
    have hΨb : Ψ (π z) = ⊥ := by rw [hΨπ z, hbot, EReal.bot_add]
    have hvb : v (π z) = ⊥ := le_bot_iff.mp ((hC (π z)).trans (by rw [hΨb, EReal.bot_add]))
    rw [hvb]
    exact bot_le
  · have hw := weight_eq_coe_toReal_of_logSing L (fun y => hΨtop (π y)) hz
    have hby := (EReal.coe_toReal (hbtop z) (hbne z)).symm
    have h1 : v (π z) = (b z - (h z : EReal)) + Ψ (π z) := by
      rw [hbeq z, hΨπ z, hw, hby, ← EReal.coe_sub, ← EReal.coe_add, ← EReal.coe_add,
        ← EReal.coe_add]
      congr 1
      ring
    rw [h1]
    exact add_le_add (hle z) le_rfl

/-- **The lower bound of WN21 Proposition 7.1**:
`P_{ω̃}(g ∘ π - Ψ ∘ π) + Ψ ∘ π ≤ P_Θ[Ψ](g) ∘ π`. -/
theorem le_prescribedEnvelope_comp [CompactSpace 𝒵] [ConnectedSpace 𝒵]
    {Θ : ClosedRealOneOneForm N 𝒳} {Ψ : 𝒳 → EReal}
    {π : 𝒵 → 𝒳} (hπ : IsAnalyticModification (n := N) π) (D' : MeteredEffectiveQDivisor N 𝒵)
    {h : 𝒵 → ℝ} (hh : ChartSmooth (n := N) h) (hΨπ : ∀ z, Ψ (π z) = D'.weight z + (h z : EReal))
    (hΨtop : ∀ x, Ψ x ≠ ⊤) {g : 𝒳 → ℝ} (hg : Continuous g) (z : 𝒵) :
    rooftopEnvelope ((ClosedRealOneOneForm.pullback hπ.1 Θ - D'.curvature) +
          ddcClosedForm h hh).val (fun y => (g (π y) : EReal) - Ψ (π y)) z + Ψ (π z) ≤
      prescribedEnvelope Θ g Ψ (π z) := by
  have : Nonempty 𝒵 := ConnectedSpace.toNonempty
  have hsurj := AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hπ
  have hπc : Continuous π := hπ.1.continuous
  set ωt := (ClosedRealOneOneForm.pullback hπ.1 Θ - D'.curvature) + ddcClosedForm h hh with hωt
  set f : 𝒵 → EReal := fun y => (g (π y) : EReal) - Ψ (π y) with hf
  set v := prescribedEnvelope Θ g Ψ with hvdef
  have hF : LocallyNondegenerate D'.weight := (TranscendentalLifting.isThetaPshPotential_weight D').2
  -- every rooftop competitor `u` satisfies `Ψ ∘ π + u ≤ v ∘ π`
  have hcomp : ∀ u ∈ rooftopCompetitors ωt.val f, ∀ y, Ψ (π y) + u y ≤ v (π y) := by
    rintro u ⟨hu, hqe⟩
    have hℓ : IsThetaPshPotential (ClosedRealOneOneForm.pullback hπ.1 Θ - D'.curvature).val
        (fun y => u y + (h y : EReal)) :=
      ⟨thetaPlurisubharmonic_add_of_add_ddc hh hu.1, fun x U hU hx => by
        obtain ⟨y, hy, hne⟩ := hu.2 x U hU hx
        exact ⟨y, hy, EReal.add_ne_bot_iff.mpr ⟨hne, EReal.coe_ne_bot _⟩⟩⟩
    have hw := DivisorialDomination.isThetaPshPotential_weight_add D' hF hℓ
    have hweq : ∀ y, D'.weight y + (u y + (h y : EReal)) = Ψ (π y) + u y := by
      intro y
      rw [hΨπ y, add_comm (u y), ← add_assoc]
    -- `w ≤ g ∘ π` quasi-everywhere, hence everywhere
    have hqe' : QuasiEverywhere (n := N)
        (fun y => D'.weight y + (u y + (h y : EReal)) ≤ ((g (π y) : ℝ) : EReal)) := by
      refine hqe.mono fun y hy => ?_
      rw [hweq y]
      by_cases hb : Ψ (π y) = ⊥
      · rw [hb, EReal.bot_add]; exact bot_le
      · have hr := (EReal.coe_toReal (hΨtop (π y)) hb).symm
        have hy' : u y ≤ (g (π y) : EReal) - Ψ (π y) := hy
        rw [hr, ← EReal.coe_sub] at hy'
        rw [hr]
        calc ((Ψ (π y)).toReal : EReal) + u y
            ≤ ((Ψ (π y)).toReal : EReal) + ((g (π y) - (Ψ (π y)).toReal : ℝ) : EReal) :=
              add_le_add le_rfl hy'
          _ = ((g (π y) : ℝ) : EReal) := by rw [← EReal.coe_add]; ring_nf
    have hwg : ∀ y, D'.weight y + (u y + (h y : EReal)) ≤ ((g (π y) : ℝ) : EReal) :=
      ContinuousObstacleEnvelopeContact.le_coe_of_ae_in_charts_le hw.1 (hg.comp hπc)
        fun e => hqe'.ae_in_chart e MeasureTheory.volume
    -- descent to `𝒳`
    obtain ⟨φ, hφ, hφw⟩ := TranscendentalLifting.exists_descent hπ Θ hw
    obtain ⟨Mu, hMu⟩ := hu.exists_global_upper_bound
    have hφmem : φ ∈ prescribedCompetitors Θ g Ψ := by
      refine ⟨hφ, fun x => ?_, (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨Mu, fun x => ?_⟩⟩
      · obtain ⟨y, rfl⟩ := hsurj x
        rw [hφw y]
        exact hwg y
      · obtain ⟨y, rfl⟩ := hsurj x
        rw [hφw y, hweq y]
        exact add_le_add le_rfl (hMu y)
    intro y
    rw [← hweq y, ← hφw y]
    exact le_prescribedEnvelope hφmem (π y)
  -- conclusion
  by_cases hz : z ∈ D'.support
  · have hbot : D'.weight z = ⊥ := hz
    have hΨb : Ψ (π z) = ⊥ := by rw [hΨπ z, hbot, EReal.bot_add]
    rw [hΨb, EReal.add_bot]
    exact bot_le
  · obtain ⟨F, hFc, hFeq⟩ :=
      MeteredDivisorWeightBounds.exists_real_continuousAt_eventuallyEq_of_notMem_support D' hz
    set r : 𝒵 → ℝ := fun y => F y + h y with hr
    have hrc : ContinuousAt r z :=
      hFc.add (ProductTestForms.ChartSmooth.continuous hh).continuousAt
    have hΨr : ∀ᶠ y in 𝓝 z, Ψ (π y) = ((r y : ℝ) : EReal) := hFeq.mono fun y hy => by
      rw [hΨπ y, hy, ← EReal.coe_add]
    set G : 𝒵 → EReal := fun y => v (π y) + ((-r y : ℝ) : EReal) with hG
    have hGusc : UpperSemicontinuousAt G z := by
      have h1 : UpperSemicontinuousAt (fun y => v (π y)) z := by
        intro a ha
        exact hπc.continuousAt.eventually
          (upperSemicontinuous_uscRegularization _ (π z) a ha)
      have h2 : ContinuousAt (fun y => ((-r y : ℝ) : EReal)) z :=
        continuous_coe_real_ereal.continuousAt.comp hrc.neg
      exact h1.add' h2.upperSemicontinuousAt
        (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _)))
    have hsup : ∀ᶠ y in 𝓝 z, rooftopSupremum ωt.val f y ≤ G y := by
      filter_upwards [hΨr] with y hy
      rw [rooftopSupremum_apply]
      refine iSup₂_le fun u hu => ?_
      have h := add_le_add (hcomp u hu y) (le_refl ((-r y : ℝ) : EReal))
      rw [hy, add_comm ((r y : ℝ) : EReal), add_assoc, ← EReal.coe_add, add_neg_cancel,
        EReal.coe_zero, add_zero] at h
      exact h
    have hRz : rooftopEnvelope ωt.val f z ≤ G z :=
      uscRegularization_le_of_eventually_le hGusc hsup
    rw [hΨr.self_of_nhds]
    calc rooftopEnvelope ωt.val f z + ((r z : ℝ) : EReal)
        ≤ G z + ((r z : ℝ) : EReal) := add_le_add hRz le_rfl
      _ = v (π z) := by
        rw [hG, add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero]

/-- **WN21 Proposition 7.1** for an analytic modification:
`P_Θ[Ψ](g) ∘ π = P_{ω̃}(g ∘ π - Ψ ∘ π) + Ψ ∘ π`. -/
theorem prescribedEnvelope_comp_eq [CompactSpace 𝒳] [CompactSpace 𝒵] [ConnectedSpace 𝒵]
    {Θ : ClosedRealOneOneForm N 𝒳} {Ψ : 𝒳 → EReal} (hΨ : IsThetaPshPotential Θ.val Ψ)
    {π : 𝒵 → 𝒳} (hπ : IsAnalyticModification (n := N) π) (D' : MeteredEffectiveQDivisor N 𝒵)
    {h : 𝒵 → ℝ} (hh : ChartSmooth (n := N) h) (hΨπ : ∀ z, Ψ (π z) = D'.weight z + (h z : EReal))
    {g : 𝒳 → ℝ} (hg : Continuous g) (z : 𝒵) :
    prescribedEnvelope Θ g Ψ (π z) =
      rooftopEnvelope ((ClosedRealOneOneForm.pullback hπ.1 Θ - D'.curvature) +
          ddcClosedForm h hh).val (fun y => (g (π y) : EReal) - Ψ (π y)) z + Ψ (π z) :=
  le_antisymm (prescribedEnvelope_comp_le hΨ hπ D' hh hΨπ hg z)
    (le_prescribedEnvelope_comp hπ D' hh hΨπ hΨ.1.quasiPlurisubharmonic.ne_top hg z)

end Resolution

/-- **`tok-wn-fl:resolution-identity`** (WN21 Proposition 7.1): the statement
`PrescribedEnvelopeResolutionStatement`. -/
theorem prescribedEnvelopeResolution : PrescribedEnvelopeResolutionStatement.{u} := by
  intro N 𝒳 _ _ _ _ Θ Ψ hΨ 𝒵 _ _ _ π hπ D' h hh h𝒵c h𝒵conn _ hΨπ _ g hg z
  have := h𝒵c
  have := h𝒵conn
  exact prescribedEnvelope_comp_eq hΨ
    (HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hπ) D' hh hΨπ hg z

end SGPT.Okounkov.TranscendentalWN
