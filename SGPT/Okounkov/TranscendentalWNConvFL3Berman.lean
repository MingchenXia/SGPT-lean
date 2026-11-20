import SGPT.Okounkov.TranscendentalWNConvFL3Resolution
import SGPT.Okounkov.TranscendentalWNRegSingular
import SGPT.Foundations.Analysis.Pending.MeteredDivisorSmoothOffSupport
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.NefBoundedMixedMass
import SGPT.Foundations.Analysis.LogPole

/-!
# WN21 Lemma 7.5 on the log resolution: Proposition 7.1 + Berman's estimate

Blueprint `claude-tok-wn-fl3`, nodes `tok-wn-fl3:weight-regularity` and
`tok-wn-fl3:resolution-laplacian`; source WN21 §7, proof of Lemma 7.5 ("From Theorem 2.5 we get
`Δ_{ω̃} ṽ_k ≤ (C(n+1) + sup Δ_{ω̃}(g_k ∘ π)) e^{B(g_k ∘ π - ψ ∘ π - inf(g_k ∘ π - ψ ∘ π))}` …
since `v_k ∘ π = ṽ_k + ψ ∘ π`"), `references/wn21-restricted-volume`.

* `continuous_meteredWeight`, `chartSmoothOn_meteredWeight_toReal`: the weight `ψ_D` of a metered effective
  `ℚ`-divisor is continuous with values in `[-∞, ∞)` and chart-smooth off `Supp D`.
* `exists_lineBound_resolvedEnvelope` (**WN21 Lemma 7.5 on `𝒵`**): for `Ψ` with a log resolution
  `Ψ ∘ π = ψ_{D'} + h`, `ω̃ = π^*Θ - Θ_{D'} + dd^c h` Kähler, there are constants `a, Λ, C`
  depending only on `(𝒵, ω̃, π^*Θ)` such that for every continuous obstacle `g` on `𝒳` with
  `g ∘ π` smooth, `dd^c(g ∘ π) ≤ S ω̃` and `m ≤ g ∘ π - Ψ ∘ π`:
  `P_Θ[Ψ](g) ∘ π = ṽ + Ψ ∘ π` with `ṽ = P_{ω̃}(g ∘ π - Ψ ∘ π)` real-valued (WN21 Proposition 7.1,
  `prescribedEnvelope_comp_eq`), and on every compact `K ⊆ 𝒵 \ Supp D'`, `ṽ` is a uniform limit of
  smooth `u_j` with `ω̃ + dd^c u_j` Kähler and `≤ ((1 + S + C) Λ e^{a(g ∘ π - Ψ ∘ π - m)} + ε) ω̃`
  (WN-REG2 `bermanSingularEnvelopeStatement` on `(𝒵, ω̃)` with `ψ = Ψ ∘ π`, which is `C ω̃`-psh).

What remains of WN21 Lemma 7.5 after this (see `tok/WN-FL3/report.json`): the bound
`dd^c(g_k ∘ π) ≤ C e^k ω̃` for the cutoff obstacles, and the transfer of the line bound to the
Laplacian in `t` along the discs `t ↦ π⁻¹(μ⁻¹(x, t))` (uniformly in `x`).
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
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy

/-! ### Regularity of the weight of a metered divisor -/

section Weight

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M]

/-- The single-generator logarithm `log |g|²` is continuous with values in `[-∞, ∞)` where `g`
is continuous. -/
theorem continuousAt_generatorLog_single {g : M → ℂ} {x : M} (hg : ContinuousAt g x) :
    ContinuousAt (fun y => generatorLog (fun _ : Fin 1 => g) y) x := by
  have heq : (fun y => generatorLog (fun _ : Fin 1 => g) y) =
      fun y => ENNReal.log (ENNReal.ofReal (‖g y‖ ^ 2)) := by
    funext y
    simp only [generatorLog, logNormSq]
    rw [generatorVector_norm_sq]
    simp [generatorNormSq]
  rw [heq]
  exact ENNReal.continuous_log.continuousAt.comp
    (ENNReal.continuous_ofReal.continuousAt.comp (hg.norm.pow 2))

omit [TopologicalSpace M] [ChartedSpace (ComplexModel N) M] [IsComplexManifold N M] in
theorem generatorLog_single_ne_top (g : M → ℂ) (y : M) :
    generatorLog (fun _ : Fin 1 => g) y ≠ ⊤ :=
  logNormSq_ne_top _

/-- A finite sum of extended-real functions continuous at `x` with values `≠ ⊤` is continuous at
`x`, with values `≠ ⊤`. -/
theorem continuousAt_finsetSum_ereal {ι X : Type*} [TopologicalSpace X] (s : Finset ι)
    {f : ι → X → EReal} {x : X} (hf : ∀ i ∈ s, ContinuousAt (f i) x)
    (htop : ∀ i ∈ s, ∀ y, f i y ≠ ⊤) :
    ContinuousAt (fun y => ∑ i ∈ s, f i y) x ∧ ∀ y, ∑ i ∈ s, f i y ≠ ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using continuousAt_const, fun y => by simp⟩
  | insert j s hj ih =>
    obtain ⟨ihc, iht⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => htop i (Finset.mem_insert_of_mem hi))
    have hjc := hf j (Finset.mem_insert_self j s)
    have hjt := htop j (Finset.mem_insert_self j s)
    simp only [Finset.sum_insert hj]
    refine ⟨?_, fun y => (EReal.add_lt_top (hjt y) (iht y)).ne⟩
    exact (EReal.continuousAt_add (Or.inl (hjt x)) (Or.inr (iht x))).comp
      (hjc.prodMk ihc)

/-- **The weight `ψ_D` of a metered effective `ℚ`-divisor is continuous** (with values in
`[-∞, ∞)`, order topology of `EReal`). -/
theorem continuous_meteredWeight (D : MeteredEffectiveQDivisor N M) : Continuous D.weight := by
  classical
  refine continuous_iff_continuousAt.mpr fun x => ?_
  obtain ⟨U, hU, hxU, k, a, g, h, ha, hg, -, hh, hw, -⟩ := D.local_presentation x
  have hgc : ∀ i, ContinuousAt (g i) x := fun i =>
    ((hg i).continuousOn).continuousAt (hU.mem_nhds hxU)
  have hhc : ContinuousAt h x :=
    MeteredDivisorWeightBounds.continuousAt_of_chartContDiffOn hU hh hxU
  have hterm : ∀ i, ContinuousAt
      (fun y => ((a i : ℝ) : EReal) * generatorLog (fun _ : Fin 1 => g i) y) x ∧
      ∀ y, ((a i : ℝ) : EReal) * generatorLog (fun _ : Fin 1 => g i) y ≠ ⊤ := by
    intro i
    rcases eq_or_lt_of_le (ha i) with hai | hai
    · simp only [← hai, Rat.cast_zero, EReal.coe_zero, zero_mul]
      exact ⟨continuousAt_const, fun _ => EReal.zero_ne_top⟩
    · have hpos : (0 : ℝ) < (a i : ℝ) := by exact_mod_cast hai
      refine ⟨?_, fun y => ?_⟩
      · have hm := EReal.continuousAt_mul (p := (((a i : ℝ) : EReal),
          generatorLog (fun _ : Fin 1 => g i) x))
          (Or.inl (EReal.coe_ne_zero.mpr hpos.ne')) (Or.inl (EReal.coe_ne_zero.mpr hpos.ne'))
          (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))
        have hpair : ContinuousAt (fun y => (((a i : ℝ) : EReal),
            generatorLog (fun _ : Fin 1 => g i) y)) x :=
          continuousAt_const.prodMk (continuousAt_generatorLog_single (hgc i))
        have h3 := ContinuousAt.comp_of_eq hm hpair rfl
        exact h3
      · have hl := generatorLog_single_ne_top (g i) y
        induction h' : generatorLog (fun _ : Fin 1 => g i) y using EReal.rec with
        | bot => rw [EReal.coe_mul_bot_of_pos hpos]; exact bot_ne_top
        | coe r => rw [← EReal.coe_mul]; exact EReal.coe_ne_top _
        | top => exact absurd h' hl
  obtain ⟨hsc, hst⟩ := continuousAt_finsetSum_ereal Finset.univ (fun i _ => (hterm i).1)
    (fun i _ => (hterm i).2)
  have hsum : ContinuousAt (fun y => (∑ i, ((a i : ℝ) : EReal) *
      generatorLog (fun _ : Fin 1 => g i) y) + (h y : EReal)) x :=
    (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))).comp
      (hsc.prodMk (continuous_coe_real_ereal.continuousAt.comp hhc))
  exact hsum.congr (Filter.eventually_of_mem (hU.mem_nhds hxU) fun y hy => (hw y hy).symm)

/-- **The weight `ψ_D` is chart-smooth off `Supp D`.** -/
theorem chartSmoothOn_meteredWeight_toReal (D : MeteredEffectiveQDivisor N M) :
    GlobalTubeFunction.ChartSmoothOn N (fun x => (D.weight x).toReal) D.supportᶜ := by
  intro e
  refine contDiffOn_of_locally_contDiffOn fun z hz => ?_
  obtain ⟨W, hzW, hW⟩ := MeteredDivisorSmoothOffSupport.exists_isSmoothLocalPotential_neg_curvature
    D hz.2 e (e.val.map_target hz.1)
  rw [e.val.right_inv hz.1] at hzW
  exact ⟨W, hW.1, hzW, hW.2.2.1.mono inter_subset_right⟩

end Weight

/-! ### WN21 Lemma 7.5 on the log resolution -/

section Resolution

variable {N : ℕ} {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel N) 𝒳]
  [IsComplexManifold N 𝒳] {𝒵 : Type u} [TopologicalSpace 𝒵] [ChartedSpace (ComplexModel N) 𝒵]
  [IsComplexManifold N 𝒵]

/-- **WN21 Lemma 7.5 on the log resolution** (Proposition 7.1 + Berman's estimate, WN21
Theorem 2.5, on `(𝒵, ω̃)`): with `ω̃ = π^*Θ - Θ_{D'} + dd^c h` Kähler there are `a ≥ 0`, `Λ > 0`
and `C ≥ 0` such that for every continuous obstacle `g` with `g ∘ π` smooth,
`dd^c(g ∘ π) ≤ S ω̃` on complex lines (`S ≥ 0`) and `m ≤ g ∘ π - Ψ ∘ π`, the function
`ṽ = P_{ω̃}(g ∘ π - Ψ ∘ π)` is real-valued, `P_Θ[Ψ](g) ∘ π = ṽ + Ψ ∘ π`, and on every compact
`K ⊆ 𝒵 \ Supp D'` the function `ṽ` is a line-bounded smooth limit with bound
`(1 + S + C) Λ e^{a(g ∘ π - Ψ ∘ π - m)}`. -/
theorem exists_lineBound_resolvedEnvelope [CompactSpace 𝒳] [CompactSpace 𝒵] [ConnectedSpace 𝒵]
    {Θ : ClosedRealOneOneForm N 𝒳} {Ψ : 𝒳 → EReal} (hΨ : IsThetaPshPotential Θ.val Ψ)
    {π : 𝒵 → 𝒳} (hπ : IsAnalyticModification (n := N) π) (D' : MeteredEffectiveQDivisor N 𝒵)
    {h : 𝒵 → ℝ} (hh : ChartSmooth (n := N) h) (hΨπ : ∀ z, Ψ (π z) = D'.weight z + (h z : EReal))
    (hK : ((ClosedRealOneOneForm.pullback hπ.1 Θ - D'.curvature) + ddcClosedForm h hh).val.IsKahler) :
    ∃ a Λ C : ℝ, 0 ≤ a ∧ 0 < Λ ∧ 0 ≤ C ∧
      ∀ (g : 𝒳 → ℝ), Continuous g → ∀ (hgπ : ChartSmooth (n := N) (fun z => g (π z))) (S : ℝ),
        0 ≤ S →
        (∀ (e : ComplexChart N 𝒵) (z : ComplexModel N), z ∈ e.val.target →
          ∀ v : ComplexModel N,
            (ddcClosedForm (fun y => g (π y)) hgπ).val.coeff e z ![v, Complex.I • v] ≤
              S * ((ClosedRealOneOneForm.pullback hπ.1 Θ - D'.curvature) +
                ddcClosedForm h hh).val.coeff e z ![v, Complex.I • v]) →
        ∀ m : ℝ, (∀ y, (m : EReal) ≤ (g (π y) : EReal) - Ψ (π y)) →
          (∀ z, rooftopEnvelope ((ClosedRealOneOneForm.pullback hπ.1 Θ - D'.curvature) +
              ddcClosedForm h hh).val (fun y => (g (π y) : EReal) - Ψ (π y)) z =
            (((rooftopEnvelope ((ClosedRealOneOneForm.pullback hπ.1 Θ - D'.curvature) +
              ddcClosedForm h hh).val (fun y => (g (π y) : EReal) - Ψ (π y)) z).toReal : ℝ) :
                EReal)) ∧
          (∀ z, prescribedEnvelope Θ g Ψ (π z) =
            rooftopEnvelope ((ClosedRealOneOneForm.pullback hπ.1 Θ - D'.curvature) +
              ddcClosedForm h hh).val (fun y => (g (π y) : EReal) - Ψ (π y)) z + Ψ (π z)) ∧
          ∀ K : Set 𝒵, IsCompact K → Disjoint K D'.support →
            TranscendentalWNReg.HasSmoothLineBoundApproximationOn
              ⟨(ClosedRealOneOneForm.pullback hπ.1 Θ - D'.curvature) + ddcClosedForm h hh, hK⟩ K
              (fun z => (rooftopEnvelope ((ClosedRealOneOneForm.pullback hπ.1 Θ - D'.curvature) +
                ddcClosedForm h hh).val (fun y => (g (π y) : EReal) - Ψ (π y)) z).toReal)
              (fun z => (1 + S + C) * Λ * Real.exp (a * (g (π z) - (Ψ (π z)).toReal - m))) := by
  set ωt := (ClosedRealOneOneForm.pullback hπ.1 Θ - D'.curvature) + ddcClosedForm h hh with hωt
  set ωK : KahlerBackground N 𝒵 := ⟨ωt, hK⟩ with hωK
  obtain ⟨a, Λ, ha, hΛ, hB⟩ := TranscendentalWNReg.bermanSingularEnvelopeStatement N 𝒵 ωK
  -- `Ψ ∘ π` is `A ω̃`-psh
  obtain ⟨A, hA, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul ωK
    (-(ClosedRealOneOneForm.pullback hπ.1 Θ))
  have hΨπp := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    hπ Θ hΨ
  have hΨA : IsThetaPshPotential (A • ωK.form).val (fun y => Ψ (π y)) := by
    refine ⟨?_, hΨπp.2⟩
    have h1 := NefBoundedMixedMass.thetaPlurisubharmonic_add_of_isSemipositive hΨπp.1 hsemi
    rwa [add_neg_cancel_left] at h1
  -- continuity and smoothness of `Ψ ∘ π`
  have hfun : (fun y => Ψ (π y)) = fun y => D'.weight y + (h y : EReal) := funext hΨπ
  have hcont : Continuous fun y => Ψ (π y) := by
    rw [hfun]
    refine continuous_iff_continuousAt.mpr fun y => ?_
    exact (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))).comp
      ((continuous_meteredWeight D').continuousAt.prodMk
        (continuous_coe_real_ereal.comp (ProductTestForms.ChartSmooth.continuous hh)).continuousAt)
  have hΨtop : ∀ x, Ψ x ≠ ⊤ := hΨ.1.quasiPlurisubharmonic.ne_top
  have hset : {y | Ψ (π y) ≠ ⊥} = D'.supportᶜ := by
    ext y
    simp only [mem_ofPred_eq, mem_compl_iff]
    constructor
    · intro hy hyS
      apply hy
      have hbot : D'.weight y = ⊥ := hyS
      rw [hΨπ y, hbot, EReal.bot_add]
    · intro hyS hy
      apply hyS
      show D'.weight y = ⊥
      rw [hΨπ y] at hy
      rcases EReal.add_eq_bot_iff.mp hy with h1 | h1
      · exact h1
      · exact absurd h1 (EReal.coe_ne_bot _)
  have hsmooth : GlobalTubeFunction.ChartSmoothOn N (fun y => (Ψ (π y)).toReal)
      {y | Ψ (π y) ≠ ⊥} := by
    rw [hset]
    intro e
    refine ((chartSmoothOn_meteredWeight_toReal D' e).add ((hh e).mono inter_subset_left)).congr
      fun z hz => ?_
    have hzS : e.val.symm z ∉ D'.support := hz.2
    have hbot : D'.weight (e.val.symm z) ≠ ⊥ := hzS
    have htop : D'.weight (e.val.symm z) ≠ ⊤ := by
      intro ht
      apply hΨtop (π (e.val.symm z))
      rw [hΨπ, ht, EReal.top_add_coe]
    show (Ψ (π (e.val.symm z))).toReal = (D'.weight (e.val.symm z)).toReal + h (e.val.symm z)
    rw [hΨπ, ← EReal.coe_toReal htop hbot, ← EReal.coe_add, EReal.toReal_coe, EReal.toReal_coe]
  refine ⟨a, Λ, A, ha, hΛ, hA.le, fun g hg hgπ S hS hgS m hm => ?_⟩
  obtain ⟨hreal, happrox⟩ := hB (fun y => g (π y)) hgπ S hS hgS (fun y => Ψ (π y)) A hA.le hΨA
    hcont hsmooth m hm
  refine ⟨hreal, fun z => prescribedEnvelope_comp_eq hΨ hπ D' hh hΨπ hg z, fun K hKc hKd => ?_⟩
  exact happrox K hKc fun y hy => by
    have : y ∈ D'.supportᶜ := Set.disjoint_left.mp hKd hy
    rw [← hset] at this
    exact this

end Resolution

end SGPT.Okounkov.TranscendentalWN
