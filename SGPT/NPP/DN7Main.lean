import SGPT.NPP.DN7Levi
import SGPT.NPP.DN7Gentle
import SGPT.Foundations.Analysis.Pending.ExceptionalMetricProof
import SGPT.Foundations.Analysis.Pending.MeteredDivisorPositivity
import SGPT.Foundations.Analysis.Pending.GlobalMultilinearExpansion
import SGPT.Foundations.Analysis.Pending.LocalPotentials
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback
import SGPT.Foundations.Analysis.Pending.AnalyticSubsetPreimage
import SGPT.Foundations.Analysis.FirstPass.ThetaPshCompactBounds
import SGPT.Foundations.Analysis.FirstPass.AnalyticSubsetTopology

/-!
# Existence of the modification data for big classes

Lane DN7, `thm:DNT23_C11bar`.  FPT `thm:big-metric-laplacian-rooftop`
(`chapters/inputs/q10-big-envelope-regularity.tex`, "Passage to a modification"): for a big class
`{θ}` on a compact complex manifold `X` of positive dimension there are

* a finite sequence of blowups with smooth centres `π : Y → X` (`Y` compact), an analytic
  modification which is an isomorphism over `X \ nK({θ})`, with a holomorphic section there;
* a Kähler form `ω_Y = (1 - s)(π^*ω₀ - Θ_E)` on `Y` (`π^*ω₀ + Σ ε_ℓ η_ℓ` in FPT; TN
  `ExceptionalMetricProof.exists_exceptionalMetric`, FPT `prop:kahler-smooth-center-blowup`);
* a potential `φ ≤ 0` with `π^*θ + ddᶜφ ≥ ω_Y`, which off `Z = π⁻¹(nK({θ}))` (an analytic subset
  with empty interior) is finite, continuous and `C^∞` in every chart, with `i∂∂̄φ ≤ C_φ ω_Y`
  there.

These are exactly the hypotheses on `(π, ω_Y, φ, Z)` of
`SGPT.NPP.DN2.hasBoundedMetricLaplacianOn_envelope_comp_of_jointSmoothing`.

The potential is `φ = v ∘ π + (1 - s) ψ_E - C₁`, where `v` is the gentle Kähler current of
`DN7Gentle` (pole set `nK({θ})`, `v ∘ π = k⁻¹ log Q + a` with `Q` a factorized weight) and `ψ_E`
the weight of the exceptional metered divisor.  Off `Z` it is a smooth local potential of the
*global* smooth form `γ = k⁻¹ Θ_Q - (1 - s) Θ_E` (`Θ_Q` the glued form of the factorization of
`Q`), which gives the Levi bound by compactness (`DN7Levi`).  This settles the gap noted by DN2:
TN's `NativeHasLogSingularitiesAlong` only provides a bounded remainder; the gentle normal form
(`DN7Weight`) provides the smooth one.

## Main results

* `SGPT.NPP.DN7.exists_modificationData_succ`;
* `SGPT.NPP.DN7.exists_modificationData` (any `n > 0`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff Manifold

universe u

namespace SGPT.NPP.DN7

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.FactorizedWeightForm
open SGPT.Foundations.Analysis.Pending.FactorizedWeightPsh
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy

section Algebra

variable {k n : ℕ} {V M : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V] [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Pull-back of closed forms commutes with `a + t • c` (coefficientwise definitional). -/
theorem pullback_add_smul' {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a c : ClosedRealOneOneForm n M) (t : ℝ) :
    ClosedRealOneOneForm.pullback hf (a + t • c) =
      ClosedRealOneOneForm.pullback hf a + t • ClosedRealOneOneForm.pullback hf c := by
  apply ClosedRealOneOneForm.ext
  intro e z
  ext v
  rfl

/-- Pull-back of closed forms is linear. -/
theorem pullback_sub_add_smul {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a b c : ClosedRealOneOneForm n M) (t : ℝ) :
    ClosedRealOneOneForm.pullback hf (a - b + t • c) =
      ClosedRealOneOneForm.pullback hf a - ClosedRealOneOneForm.pullback hf b +
        t • ClosedRealOneOneForm.pullback hf c := by
  have h1 : a - b + t • c = a + (-1 : ℝ) • b + t • c := by module
  rw [h1, pullback_add_smul', pullback_add_smul']
  module

end Algebra

section Data

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **The modification data of FPT's "passage to a modification"** for the class `{θ}`, with
`nK = nK({θ})` (TN `nonKahlerLocus`, Lelong-number definition): a compact complex manifold `Y`, a
finite sequence of blowups with smooth centres `π : Y → X` (an analytic modification) which is an
isomorphism over `X \ nK`, with a holomorphic section `σ` there, a Kähler form `ω_Y` on `Y`, and a
potential `φ ≤ 0` with `π^*θ + ddᶜφ ≥ ω_Y` (`(π^*θ - ω_Y)`-psh, and a `π^*θ`-psh potential) which
off `Z = π⁻¹(nK)` (analytic, empty interior) is finite, continuous, `C^∞` in every chart and has
Levi form `≤ C_φ · π · ω_Y` on complex lines.  These are the hypotheses on `(π, ω_Y, φ, Z)` of
`SGPT.NPP.DN2.hasBoundedMetricLaplacianOn_envelope_comp_of_jointSmoothing`. -/
def HasModificationData (θ : ClosedRealOneOneForm n X) : Prop :=
  ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
    (_ : IsComplexManifold n Y) (π : Y → X) (hπ : IsAnalyticModification (n := n) π)
    (wY : KahlerBackground n Y) (φ : Y → EReal) (Cφ : ℝ),
    CompactSpace Y ∧ IsBlowupSequence n X Y π ∧
    IsIsomorphismOver n π (nonKahlerLocus (RealBottChern.ofRepresentative θ))ᶜ ∧
    (∃ σ : X → Y, ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ σ
        (nonKahlerLocus (RealBottChern.ofRepresentative θ))ᶜ ∧
      (∀ x ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ), π (σ x) = x) ∧
      ∀ y, π y ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ) → σ (π y) = y) ∧
    ThetaPlurisubharmonic (ClosedRealOneOneForm.pullback hπ.1 θ - wY.form).val φ ∧
    IsThetaPshPotential (ClosedRealOneOneForm.pullback hπ.1 θ).val φ ∧
    (∀ y, φ y ≤ 0) ∧
    IsComplexAnalyticSubset (n := n) (π ⁻¹' nonKahlerLocus (RealBottChern.ofRepresentative θ)) ∧
    interior (π ⁻¹' nonKahlerLocus (RealBottChern.ofRepresentative θ)) = ∅ ∧
    (∀ y ∉ π ⁻¹' nonKahlerLocus (RealBottChern.ofRepresentative θ), φ y ≠ ⊥) ∧
    ContinuousOn (fun y => (φ y).toReal)
      (π ⁻¹' nonKahlerLocus (RealBottChern.ofRepresentative θ))ᶜ ∧
    0 ≤ Cφ ∧
    (∀ e : ComplexChart n Y, ContDiffOn ℝ ∞ (fun z => (φ (e.val.symm z)).toReal)
      (e.val.target ∩ e.val.symm ⁻¹'
        (π ⁻¹' nonKahlerLocus (RealBottChern.ofRepresentative θ))ᶜ)) ∧
    ∀ (e : ComplexChart n Y) (z : ComplexModel n), z ∈ e.val.target →
      e.val.symm z ∈ (π ⁻¹' nonKahlerLocus (RealBottChern.ofRepresentative θ))ᶜ →
      ∀ v : ComplexModel n,
        leviForm (fun z => (φ (e.val.symm z)).toReal) z v ≤
          Cφ * (Real.pi * wY.form.val.coeff e z ![v, Complex.I • v])

end Data

section Main

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X]

/-- **Existence of the modification data** (FPT `thm:big-metric-laplacian-rooftop`, passage to a
modification), in dimension `m + 1`. -/
theorem exists_modificationData_succ [CompactSpace X] (θ : ClosedRealOneOneForm (m + 1) X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) : HasModificationData θ := by
  classical
  set α := RealBottChern.ofRepresentative θ with hαdef
  obtain ⟨ω₀, s, v, k, a, Y, tY, chY, mY, f, Q, FQ, hs0, hs, hk, hv, hpole, hblow, hcpt, hmod,
    hiso, hsec, hvQ⟩ := exists_gentle_resolution θ hbig
  let := tY
  let := chY
  let := mY
  have hf : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ f := hmod.1
  -- the exceptional correction and the Kähler form on `Y`
  obtain ⟨Ed, hEsupp, hEK, -⟩ := ExceptionalMetricProof.exists_exceptionalMetric ω₀ f hblow
  have hs1 : 0 < 1 - s := by linarith
  let β : KahlerBackground (m + 1) Y :=
    ⟨ClosedRealOneOneForm.pullback hf ω₀.form - Ed.curvature, hEK⟩
  let wY : KahlerBackground (m + 1) Y := KahlerBackground.smul hs1 β
  -- the analytic set `Z = π⁻¹ nK`
  set Z : Set Y := f ⁻¹' nonKahlerLocus α with hZdef
  have hnKa : IsComplexAnalyticSubset (n := m + 1) (nonKahlerLocus α) :=
    NonKahlerLocusPoleSet.isComplexAnalyticSubset_nonKahlerLocus (Nat.succ_pos m) α hbig
  have hZa : IsComplexAnalyticSubset (n := m + 1) Z :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hf hnKa
  have hZc : IsClosed Z := hZa.isClosed
  have hexcZ : exceptionalLocus (m + 1) f ⊆ Z := by
    intro y hy
    by_contra hyZ
    exact disjoint_left.mp hiso.2 hyZ hy
  have hEZ : Ed.support ⊆ Z := hEsupp.trans hexcZ
  -- the weight `Q` vanishes exactly on `Z`
  have hk' : (0 : ℝ) < (k : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hk)
  have hQnn : ∀ y, 0 ≤ Q y := fun y => by
    rw [FQ.factor y y (FQ.mem_domain y)]
    exact mul_nonneg (Complex.normSq_nonneg _) (FQ.pos y y (FQ.mem_domain y)).le
  have hvbot : ∀ y, v (f y) = ⊥ ↔ Q y ≤ 0 := by
    intro y
    rw [hvQ y]
    constructor
    · intro h
      by_contra hQ
      push Not at hQ
      rw [logWeight_of_pos hQ, ← EReal.coe_mul, ← EReal.coe_add] at h
      exact EReal.coe_ne_bot _ h
    · intro hQ
      rw [logWeight, ENNReal.ofReal_eq_zero.mpr hQ, ENNReal.log_zero,
        EReal.coe_mul_bot_of_pos hk', EReal.bot_add]
  have hmemZ : ∀ y, y ∈ Z ↔ v (f y) = ⊥ := by
    intro y
    show f y ∈ nonKahlerLocus α ↔ _
    rw [← hpole]
    rfl
  have hQpos : ∀ y, y ∉ Z → 0 < Q y := fun y hy => by
    by_contra hQ
    push Not at hQ
    exact hy ((hmemZ y).mpr ((hvbot y).mpr hQ))
  have hZint : interior Z = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    obtain ⟨t, htW, hQt⟩ := FQ.nowhereZero (interior Z) isOpen_interior ⟨y, hy⟩
    have htZ : t ∈ Z := interior_subset htW
    exact hQt (le_antisymm ((hvbot t).mp ((hmemZ t).mp htZ)) (hQnn t))
  -- the potential before normalization
  have hw : ThetaPlurisubharmonic Ed.curvature.val Ed.weight :=
    MeteredDivisorPositivity.thetaPlurisubharmonic_weight Ed
  have h1 : ThetaPlurisubharmonic
      (ClosedRealOneOneForm.pullback hf (θ - ω₀.form + s • ω₀.form)).val (fun y => v (f y)) :=
    GlobalPotentialPullback.thetaPlurisubharmonic_comp hf hv.1
  have h2 : ThetaPlurisubharmonic ((1 - s) • Ed.curvature).val
      (fun y => ((1 - s : ℝ) : EReal) * Ed.weight y) :=
    GlobalMultilinearExpansion.thetaPlurisubharmonic_smul hs1 hw
  have hform : ClosedRealOneOneForm.pullback hf (θ - ω₀.form + s • ω₀.form) +
      (1 - s) • Ed.curvature = ClosedRealOneOneForm.pullback hf θ - wY.form := by
    rw [pullback_sub_add_smul, KahlerBackground.smul_form]
    show _ = _ - (1 - s) • (ClosedRealOneOneForm.pullback hf ω₀.form - Ed.curvature)
    module
  have h3 : ThetaPlurisubharmonic (ClosedRealOneOneForm.pullback hf θ - wY.form).val
      (fun y => v (f y) + ((1 - s : ℝ) : EReal) * Ed.weight y) := by
    rw [← hform]
    exact FirstPass.LocalPotentials.thetaPlurisubharmonic_add h1 h2
  -- normalization `φ ≤ 0`
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, ∀ y, v (f y) + ((1 - s : ℝ) : EReal) * Ed.weight y ≤ (C₁ : EReal) := by
    rcases isEmpty_or_nonempty Y with hY | hY
    · exact ⟨0, fun y => (hY.false y).elim⟩
    · exact h3.exists_global_upper_bound
  set φ : Y → EReal := fun y => (v (f y) + ((1 - s : ℝ) : EReal) * Ed.weight y) - (C₁ : EReal)
    with hφdef
  have hφpsh : ThetaPlurisubharmonic (ClosedRealOneOneForm.pullback hf θ - wY.form).val φ :=
    GlobalPotentialTransforms.thetaPlurisubharmonic_sub_smooth (f := fun _ => C₁)
      (fun _ => contDiffOn_const) (fun e z _ => by
        rw [GlobalPotentialTransforms.smoothDDC_const, add_zero]) h3
  have hφle : ∀ y, φ y ≤ 0 := by
    intro y
    have h := hC₁ y
    show (v (f y) + ((1 - s : ℝ) : EReal) * Ed.weight y) - (C₁ : EReal) ≤ 0
    calc (v (f y) + ((1 - s : ℝ) : EReal) * Ed.weight y) - (C₁ : EReal)
        ≤ (C₁ : EReal) - (C₁ : EReal) := EReal.sub_le_sub h le_rfl
      _ = 0 := by rw [← EReal.coe_sub, sub_self, EReal.coe_zero]
  -- off `Z` the potential is real, with an explicit formula
  have hφreal : ∀ y, y ∉ Z → φ y = (((k : ℝ)⁻¹ * Real.log (Q y) + a +
      (1 - s) * (Ed.weight y).toReal - C₁ : ℝ) : EReal) := by
    intro y hy
    have hyE : y ∉ Ed.support := fun h => hy (hEZ h)
    have hwb : Ed.weight y ≠ ⊥ := hyE
    have hwt : Ed.weight y ≠ ⊤ := hw.quasiPlurisubharmonic.ne_top y
    show (v (f y) + ((1 - s : ℝ) : EReal) * Ed.weight y) - (C₁ : EReal) = _
    rw [hvQ y, logWeight_of_pos (hQpos y hy), ← EReal.coe_toReal hwt hwb, ← EReal.coe_mul,
      ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_sub, EReal.toReal_coe]
  have hφne : ∀ y, y ∉ Z → φ y ≠ ⊥ := fun y hy => by
    rw [hφreal y hy]
    exact EReal.coe_ne_bot _
  -- smooth local potentials of the global form `γ` off `Z`
  set γ : ClosedRealOneOneForm (m + 1) Y :=
    (k : ℝ)⁻¹ • FQ.closedForm + (1 - s) • (-Ed.curvature) with hγ
  have hpot : ∀ (e : ComplexChart (m + 1) Y) (z : ComplexModel (m + 1)), z ∈ e.val.target →
      e.val.symm z ∉ Z → ∃ W : Set (ComplexModel (m + 1)), z ∈ W ∧
        IsSmoothLocalPotential γ.val e W (fun ζ => (φ (e.val.symm ζ)).toReal) := by
    intro e z hz hzZ
    obtain ⟨W₁, hzW₁, hW₁, -⟩ :=
      exists_isSmoothLocalPotential_log_weight FQ e hz (hQpos _ hzZ).ne'
    have hxs : e.val.symm z ∈ e.val.source := e.val.map_target hz
    obtain ⟨W₂, hzW₂, hW₂⟩ :=
      MeteredDivisorSmoothOffSupport.exists_isSmoothLocalPotential_neg_curvature Ed
        (fun h => hzZ (hEZ h)) e hxs
    rw [e.val.right_inv hz] at hzW₂
    have hO : IsOpen (e.val.target ∩ e.val.symm ⁻¹' Zᶜ) :=
      e.val.isOpen_inter_preimage_symm hZc.isOpen_compl
    set W : Set (ComplexModel (m + 1)) := (W₁ ∩ W₂) ∩ (e.val.target ∩ e.val.symm ⁻¹' Zᶜ)
      with hWdef
    have hA : IsSmoothLocalPotential ((k : ℝ)⁻¹ • FQ.closedForm).val e (W₁ ∩ W₂)
        (fun ζ => (k : ℝ)⁻¹ • Real.log (Q (e.val.symm ζ))) :=
      FirstPass.LocalPotentials.localPotential_smul
        (isSmoothLocalPotential_inter hW₁ hW₂.1) _
    have hB : IsSmoothLocalPotential ((1 - s) • (-Ed.curvature)).val e (W₁ ∩ W₂)
        (fun ζ => (1 - s) • (Ed.weight (e.val.symm ζ)).toReal) := by
      have h := FirstPass.LocalPotentials.localPotential_smul hW₂ (1 - s)
      have hsub : IsSmoothLocalPotential ((1 - s) • (-Ed.curvature)).val e (W₂ ∩ W₁)
          (fun ζ => (1 - s) • (Ed.weight (e.val.symm ζ)).toReal) :=
        isSmoothLocalPotential_inter h hW₁.1
      rwa [inter_comm] at hsub
    have hAB := isSmoothLocalPotential_add_const
      (FirstPass.LocalPotentials.localPotential_add hA hB) (a - C₁)
    refine ⟨W, ⟨⟨hzW₁, hzW₂⟩, hz, hzZ⟩, ?_⟩
    refine isSmoothLocalPotential_congr (isSmoothLocalPotential_inter hAB hO) fun ζ hζ => ?_
    simp only [smul_eq_mul]
    rw [hφreal _ hζ.2.2, EReal.toReal_coe]
    ring
  obtain ⟨hsmooth, hcont, Cφ, hCφ, hlevi⟩ := offClosed_data_of_localPotential wY γ hpot
  -- the potential is a `π^*θ`-psh potential
  have hθpsh : ThetaPlurisubharmonic (ClosedRealOneOneForm.pullback hf θ).val φ := by
    have h := LocalPotentials.thetaPlurisubharmonic_add_of_semipositive hφpsh wY.isSemipositive
    rwa [sub_add_cancel] at h
  have hnd : LocallyNondegenerate φ := by
    intro x U hU hxU
    by_contra hcon
    push Not at hcon
    have hsub : U ⊆ Z := fun y hy => by
      by_contra hyZ
      exact hφne y hyZ (hcon y hy)
    have hxi : x ∈ interior Z := interior_maximal hsub hU hxU
    rw [hZint] at hxi
    exact hxi
  exact ⟨Y, tY, chY, mY, f, hmod, wY, φ, Cφ, hcpt, hblow, hiso, hsec, hφpsh, ⟨hθpsh, hnd⟩, hφle,
    hZa, hZint, hφne, hcont, hCφ, hsmooth, hlevi⟩

end Main

section General

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **Existence of the modification data for big classes** (FPT
`thm:big-metric-laplacian-rooftop`, "Passage to a modification"): for a big class `{θ}` on a
compact complex manifold of positive dimension, the data `HasModificationData θ` exist. -/
theorem exists_modificationData [CompactSpace X] (hn : 0 < n) (θ : ClosedRealOneOneForm n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) : HasModificationData θ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact exists_modificationData_succ θ hbig

end General

end SGPT.NPP.DN7
