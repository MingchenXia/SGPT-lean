import SGPT.Envelopes.MADirichletSubsolution
import SGPT.Foundations.Analysis.Pending.AeRegularizedSupremum
import SGPT.Foundations.Analysis.Pending.BedfordTaylorIncreasing
import SGPT.Foundations.Analysis.FirstPass.PshSupremumRegularization
import SGPT.Foundations.Analysis.FirstPass.UscRegularizationContinuous

/-!
# Upper envelopes of Monge–Ampère subsolutions

Xia, *Foundations of pluripotential theory* (FPT), `thm:continuous-density-ball-dirichlet`,
Step 1 (and the same step in `thm:homogeneous-ball-dirichlet`): the upper envelope of a family
of subsolutions is a subsolution. Let `Ω ⊆ ℂⁿ` be open, `n ≥ 1`, `α` a measure finite on the
compact subsets of `Ω`, and `𝒮` a family of locally bounded plurisubharmonic functions on `Ω`
with `(ddᶜv)ⁿ ≥ α` on `Ω` for every `v ∈ 𝒮`, which is

* stable under maxima (`max v w ∈ 𝒮`; by `ma_ge_max` this is automatic for the class of all
  subsolutions with prescribed boundary upper limits),
* nonempty, and locally uniformly bounded above on `Ω`.

Let `H = sup 𝒮` (pointwise) and `H*` its upper semicontinuous regularization
(`regEnvelope`). Then (`ma_ge_regEnvelope`) `H*` is locally bounded plurisubharmonic on `Ω` and
`(ddᶜH*)ⁿ ≥ α`; moreover every `v ∈ 𝒮` lies below `H*`, and `H*` lies below every upper
semicontinuous local majorant of the family.

Proof (FPT): by Choquet's lemma (TN `exists_seq_uscRegularization_iSup_eq`) a sequence `vₖ ∈ 𝒮`
has the same regularized supremum; the running maxima `wⱼ = max(s, v₀, …, vⱼ) ∈ 𝒮` increase,
and their supremum agrees with its regularization `H*` almost everywhere (TN
`ae_uscRegularization_iSup_eq_on_ball`, Xia's Proposition 1.2.5), so the Bedford–Taylor measures
`(ddᶜwⱼ)ⁿ ≥ α` converge vaguely to `(ddᶜH*)ⁿ` (TN `boundedIncreasingConvergence`) and the lower
bound passes to the limit (`restrict_le_of_tendsto_integral`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ENNReal

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor

variable {n : ℕ}

/-- The family `𝒮` as extended-real functions. -/
def erealFamily (𝒮 : Set (ComplexModel n → ℝ)) : Set (ComplexModel n → EReal) :=
  (fun v z => (v z : EReal)) '' 𝒮

/-- The upper semicontinuous regularization `H*` of the upper envelope `H = sup 𝒮`, as a real
function (it is finite on `Ω` under the hypotheses below). -/
def regEnvelope (𝒮 : Set (ComplexModel n → ℝ)) (z : ComplexModel n) : ℝ :=
  (uscRegularization (sSup (erealFamily 𝒮)) z).toReal

theorem coe_le_sSup_erealFamily {𝒮 : Set (ComplexModel n → ℝ)} {v : ComplexModel n → ℝ}
    (hv : v ∈ 𝒮) (z : ComplexModel n) : (v z : EReal) ≤ sSup (erealFamily 𝒮) z := by
  rw [sSup_apply]
  exact le_iSup_of_le ⟨fun z => (v z : EReal), ⟨v, hv, rfl⟩⟩ le_rfl

theorem plurisubharmonicOn_congr_open {u w : ComplexModel n → EReal} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hu : PlurisubharmonicOn u U) (heq : EqOn u w U) :
    PlurisubharmonicOn w U := by
  intro x hx
  obtain ⟨V, hVopen, hxV, hV⟩ := hu x hx
  exact ⟨V ∩ U, hVopen.inter hU, ⟨hxV, hx⟩,
    (hV.mono inter_subset_left).congr (heq.mono inter_subset_right)⟩

/-- **Upper envelopes of Monge–Ampère subsolutions** (FPT
`thm:continuous-density-ball-dirichlet`, Step 1, for an arbitrary measure). -/
theorem ma_ge_regEnvelope {Ω : Opens (ComplexModel n)}
    {α : Measure (ComplexModel n)} (hα : ∀ K, IsCompact K → K ⊆ Ω → α K < ⊤)
    {𝒮 : Set (ComplexModel n → ℝ)} (hS : ∀ v ∈ 𝒮, IsLocallyBoundedPshOn Ω v)
    (hSα : ∀ v (hv : v ∈ 𝒮), α.restrict (Ω : Set (ComplexModel n)) ≤
      canonicalBedfordTaylorMeasure Ω v (hS v hv))
    (hmax : ∀ v ∈ 𝒮, ∀ w ∈ 𝒮, (fun z => max (v z) (w z)) ∈ 𝒮)
    {s : ComplexModel n → ℝ} (hs : s ∈ 𝒮)
    (hub : ∀ x ∈ Ω, ∃ V ∈ 𝓝 x, ∃ C : ℝ, ∀ v ∈ 𝒮, ∀ y ∈ V, v y ≤ C) :
    ∃ hH : IsLocallyBoundedPshOn Ω (regEnvelope 𝒮),
      α.restrict (Ω : Set (ComplexModel n)) ≤ canonicalBedfordTaylorMeasure Ω _ hH ∧
      ∀ v ∈ 𝒮, ∀ z ∈ Ω, v z ≤ regEnvelope 𝒮 z := by
  classical
  set F := erealFamily 𝒮 with hFdef
  set Hs : ComplexModel n → EReal := uscRegularization (sSup F) with hHsdef
  have hFne : F.Nonempty := ⟨_, ⟨s, hs, rfl⟩⟩
  have hFpsh : ∀ f ∈ F, PlurisubharmonicOn f Ω := by
    rintro f ⟨v, hv, rfl⟩
    exact (hS v hv).1
  have hFub : LocallyUniformlyBoundedAbove F Ω := by
    intro x hx
    obtain ⟨V, hV, C, hC⟩ := hub x hx
    refine ⟨V, mem_nhdsWithin_of_mem_nhds hV, C, ?_⟩
    rintro f ⟨v, hv, rfl⟩ y ⟨hyV, -⟩
    exact EReal.coe_le_coe_iff.mpr (hC v hv y hyV)
  have hHpsh : PlurisubharmonicOn Hs Ω :=
    plurisubharmonicOn_uscRegularization_sSup Ω.isOpen hFne hFpsh hFub
  -- bounds for `H*`
  have hlow : ∀ v ∈ 𝒮, ∀ z, (v z : EReal) ≤ Hs z := fun v hv z =>
    (coe_le_sSup_erealFamily hv z).trans (le_uscRegularization _ z)
  have hup : ∀ x ∈ Ω, ∃ V ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ V, Hs y ≤ (C : EReal) := by
    intro x hx
    obtain ⟨V, hV, C, hC⟩ := hub x hx
    obtain ⟨W, hWV, hWo, hxW⟩ := _root_.mem_nhds_iff.mp hV
    refine ⟨W, hWo.mem_nhds hxW, C, fun y hy => ?_⟩
    refine (uscRegularization_le_localSup _ (hWo.mem_nhds hy)).trans ?_
    refine iSup₂_le fun y' hy' => ?_
    rw [sSup_apply]
    refine iSup_le fun f => ?_
    obtain ⟨v, hv, hfv⟩ := f.2
    rw [← hfv]
    exact EReal.coe_le_coe_iff.mpr (hC v hv y' (hWV hy'))
  have hfinite : ∀ z ∈ Ω, Hs z = ((regEnvelope 𝒮 z : ℝ) : EReal) := by
    intro z hz
    obtain ⟨V, hV, C, hC⟩ := hup z hz
    have h1 : Hs z ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top C) (hC z (mem_of_mem_nhds hV))
    have h2 : Hs z ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot (s z)) (hlow s hs z)
    exact (EReal.coe_toReal h1 h2).symm
  have hHreal : IsLocallyBoundedPshOn Ω (regEnvelope 𝒮) := by
    refine ⟨plurisubharmonicOn_congr_open Ω.isOpen hHpsh hfinite, fun z hz => ?_⟩
    obtain ⟨V, hV, C, hC⟩ := hup z hz
    obtain ⟨V', hzV', hV'Ω, C', hC'⟩ := (hS s hs).2 z hz
    obtain ⟨W, hWV, hWo, hzW⟩ := _root_.mem_nhds_iff.mp hV
    refine ⟨V' ⊓ ⟨W, hWo⟩, ⟨hzV', hzW⟩, inf_le_left.trans hV'Ω, max |C| C', fun y hy => ?_⟩
    have hyΩ : y ∈ Ω := hV'Ω hy.1
    have hlo : s y ≤ regEnvelope 𝒮 y := by
      have := hlow s hs y
      rwa [hfinite y hyΩ, EReal.coe_le_coe_iff] at this
    have hhi : regEnvelope 𝒮 y ≤ C := by
      have := hC y (hWV hy.2)
      rwa [hfinite y hyΩ, EReal.coe_le_coe_iff] at this
    rw [abs_le]
    constructor
    · have := (abs_le.mp (hC' y hy.1)).1
      linarith [le_max_right |C| C']
    · linarith [le_abs_self C, le_max_left |C| C']
  have hbelow : ∀ v ∈ 𝒮, ∀ z ∈ Ω, v z ≤ regEnvelope 𝒮 z := by
    intro v hv z hz
    have := hlow v hv z
    rwa [hfinite z hz, EReal.coe_le_coe_iff] at this
  refine ⟨hHreal, ?_, hbelow⟩
  -- Choquet's lemma and the running maxima
  obtain ⟨σ, hσF, hσ⟩ := exists_seq_uscRegularization_iSup_eq hFne
  choose v hv hvσ using hσF
  let w : ℕ → ComplexModel n → ℝ := fun j => Nat.rec (fun z => max (s z) (v 0 z))
    (fun j wj => fun z => max (wj z) (v (j + 1) z)) j
  have hw0 : w 0 = fun z => max (s z) (v 0 z) := rfl
  have hwsucc : ∀ j, w (j + 1) = fun z => max (w j z) (v (j + 1) z) := fun j => rfl
  have hwS : ∀ j, w j ∈ 𝒮 := by
    intro j
    induction j with
    | zero => rw [hw0]; exact hmax s hs _ (hv 0)
    | succ j ih => rw [hwsucc]; exact hmax _ ih _ (hv (j + 1))
  have hwmono : ∀ z, Monotone fun j => w j z := by
    intro z
    refine monotone_nat_of_le_succ fun j => ?_
    rw [hwsucc]
    exact le_max_left _ _
  have hvw : ∀ k z, v k z ≤ w k z := by
    intro k z
    cases k with
    | zero => rw [hw0]; exact le_max_right _ _
    | succ k => rw [hwsucc]; exact le_max_right _ _
  -- the regularization of `sup wⱼ` is `H*`
  set W : ComplexModel n → EReal := fun z => ⨆ j : ℕ, Real.toEReal (w j z) with hWdef
  have hWreg : uscRegularization W = Hs := by
    refine le_antisymm (uscRegularization_mono fun z => iSup_le fun j =>
      coe_le_sSup_erealFamily (hwS j) z) ?_
    rw [hHsdef, ← hσ]
    refine uscRegularization_mono fun z => ?_
    rw [iSup_apply]
    refine iSup_le fun k => ?_
    rw [← hvσ k]
    exact (EReal.coe_le_coe_iff.mpr (hvw k z)).trans (le_iSup (fun j : ℕ => Real.toEReal (w j z)) k)
  -- almost every point of `Ω` is a point where `sup wⱼ` equals its regularization
  have hlocal : ∀ x ∈ Ω, ∃ r > 0, ∀ᵐ z ∂(volume : Measure (ComplexModel n)),
      z ∈ ball x r → uscRegularization W z = W z := by
    intro x hx
    obtain ⟨V, hV, C, hC⟩ := hub x hx
    obtain ⟨S, hS0, hSV⟩ := Metric.mem_nhds_iff.mp (inter_mem hV (Ω.isOpen.mem_nhds hx))
    refine ⟨S / 2, by positivity, ?_⟩
    have hpshw : ∀ j, DiscPshOn (fun z => Real.toEReal (w j z)) (Ω : Set (ComplexModel n)) :=
      fun j => FirstPass.PlurisubharmonicOn.discPshOn (hS _ (hwS j)).1
    have hae := ae_uscRegularization_iSup_eq_on_ball hpshw
      (fun y _ j k hjk => EReal.coe_le_coe_iff.mpr (hwmono y hjk)) volume x hS0
      (hSV.trans inter_subset_right)
      (fun j y hy => EReal.coe_le_coe_iff.mpr (hC _ (hwS j) y (hSV hy).1))
    filter_upwards [hae] with z hz hzb
    exact hz hzb
  have hae : ∀ᵐ z ∂(volume : Measure (ComplexModel n)), z ∈ Ω →
      Tendsto (fun j => w j z) atTop (𝓝 (regEnvelope 𝒮 z)) := by
    choose! r hr hrae using hlocal
    obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun x : (Ω : Set (ComplexModel n)) => ball (x : ComplexModel n) (r x)) fun _ => isOpen_ball
    have hcover : (Ω : Set (ComplexModel n)) ⊆ ⋃ x ∈ T, ball (x : ComplexModel n) (r x) := by
      intro z hz
      rw [hTU]
      exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (hr z hz)⟩
    have hall : ∀ᵐ z ∂(volume : Measure (ComplexModel n)), ∀ x ∈ T,
        z ∈ ball (x : ComplexModel n) (r x) → uscRegularization W z = W z :=
      (ae_ball_iff hTc).mpr fun x _ => hrae x x.2
    filter_upwards [hall] with z hz hzΩ
    obtain ⟨x, hxT, hzx⟩ := mem_iUnion₂.mp (hcover hzΩ)
    have heq : W z = ((regEnvelope 𝒮 z : ℝ) : EReal) := by
      rw [← hz x hxT hzx, hWreg, hfinite z hzΩ]
    -- a monotone real sequence with this supremum converges to it
    obtain ⟨V, hV, C, hC⟩ := hub z hzΩ
    have hbdd : BddAbove (range fun j => w j z) :=
      ⟨C, by rintro _ ⟨j, rfl⟩; exact hC _ (hwS j) z (mem_of_mem_nhds hV)⟩
    have hsup : (⨆ j, w j z) = regEnvelope 𝒮 z := by
      have h1 : W z = ((⨆ j, w j z : ℝ) : EReal) := by
        rw [hWdef]
        exact (Monotone.map_ciSup_of_continuousAt continuous_coe_real_ereal.continuousAt
          (fun a b hab => EReal.coe_le_coe_iff.mpr hab) hbdd).symm
      rw [h1, EReal.coe_eq_coe_iff] at heq
      exact heq
    rw [← hsup]
    exact tendsto_atTop_ciSup (hwmono z) hbdd
  -- increasing convergence of the Monge–Ampère measures
  have hconv := IncreasingTruncationLimit.boundedIncreasingConvergence Ω w (regEnvelope 𝒮)
    (fun j => hS _ (hwS j)) hHreal (fun z _ => hwmono z) hae
  refine restrict_le_of_tendsto_integral hα (fun j K hK hKΩ =>
    canonicalBedfordTaylorMeasure_finiteOnCompacts (hS _ (hwS j)) hK hKΩ)
    (fun K hK hKΩ => canonicalBedfordTaylorMeasure_finiteOnCompacts hHreal hK hKΩ)
    (fun j => hSα _ (hwS j)) fun φ hφ hφc hφΩ => (hconv φ hφ hφc hφΩ).1

/-- `H*` lies below every local upper semicontinuous majorant of the family. -/
theorem regEnvelope_le_of_eventually {𝒮 : Set (ComplexModel n → ℝ)} {g : ComplexModel n → ℝ}
    {z : ComplexModel n} (hg : UpperSemicontinuousAt g z)
    (hle : ∀ᶠ y in 𝓝 z, ∀ v ∈ 𝒮, v y ≤ g y) (hfin : uscRegularization (sSup (erealFamily 𝒮)) z ≠ ⊥) :
    regEnvelope 𝒮 z ≤ g z := by
  have hgE : UpperSemicontinuousAt (fun y => (g y : EReal)) z := by
    intro c hc
    induction c using EReal.rec with
    | bot => exact absurd hc (not_lt.mpr bot_le)
    | top => exact Eventually.of_forall fun _ => EReal.coe_lt_top _
    | coe c =>
      filter_upwards [hg c (EReal.coe_lt_coe_iff.mp hc)] with y hy
      exact EReal.coe_lt_coe_iff.mpr hy
  have h := uscRegularization_le_of_eventually_le (f := sSup (erealFamily 𝒮)) hgE (by
    filter_upwards [hle] with y hy
    rw [sSup_apply]
    refine iSup_le fun f => ?_
    obtain ⟨v, hv, hfv⟩ := f.2
    rw [← hfv]
    exact EReal.coe_le_coe_iff.mpr (hy v hv))
  have htop : uscRegularization (sSup (erealFamily 𝒮)) z ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) h
  unfold regEnvelope
  rw [← EReal.coe_le_coe_iff, EReal.coe_toReal htop hfin]
  exact h

end SGPT.Envelopes.MADirichlet
