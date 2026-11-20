import SGPT.Foundations.Analysis.Pending.ActualFiniteModelMixedSandwich
import SGPT.Foundations.Analysis.Pending.ActualMonotoneMixedMassNative

set_option autoImplicit false

/-! # Actual mixed-mass continuity of positive-target native model sequences

SGPT PDF0235--0237, the positive-model sequence part of Theorem 6.2.1.
Actual target positivity internally produces a common eventual stage bound.
A true common subsequence and the actual monotone mixed-mass producers
then produce convergence. No mixed-mass limit or sandwich is an input.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualPositiveModelMixedContinuity

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  DiagonalMass MixedMass GlobalMixedMassMonotone ThetaPshL1Topology
  SingularCanonicalSingularityDistance SingularCanonicalSingularityMassLipschitz
  ActualFiniteModelMixedSandwich ActualMonotoneMixedMassNative

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

private theorem tendsto_mixedMass_of_uniform_model_native
    (omega : KahlerBackground n M) {θ : Fin n → ClosedRealOneOneForm n M}
    (hbig : ∀ a, IsBigClass (RealBottChern.ofRepresentative (θ a)))
    {u : ℕ → Fin n → M → EReal} {v : Fin n → M → EReal}
    (hu : ∀ j a, IsModelPotential (θ a) (u j a))
    (hv : ∀ a, IsThetaPshPotential (θ a).val (v a))
    (hvpos : ∀ a, 0 < diagonalPotentialMass (θ a) (v a) (hv a))
    {δ : Fin n → ℝ} (hδ : ∀ a, 0 < δ a)
    (hstage : ∀ j a, ENNReal.ofReal (δ a) ≤
      diagonalPotentialMass (θ a) (u j a) (hu j a).plurisubharmonic)
    (hlim : ∀ a, Tendsto
      (fun j => (⟨u j a, (hu j a).plurisubharmonic⟩ : ThetaPshL1 (θ a).val)) atTop
      (@nhds (ThetaPshL1 (θ a).val)
        (singularityPseudoMetricSpace omega (θ a) (hbig a)).toUniformSpace.toTopologicalSpace
        ⟨v a, hv a⟩)) :
    Tendsto (fun j => globalMixedMass θ (u j)
      (fun a => (hu j a).plurisubharmonic.1)) atTop
      (𝓝 (globalMixedMass θ v (fun a => (hv a).1))) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨f, hf, hfamily⟩ := exists_simultaneous_model_sandwich omega θ hbig
    (fun a j => ⟨u (ns j) a, (hu (ns j) a).plurisubharmonic⟩)
    (fun a => ⟨v a, hv a⟩) (fun a j => hu (ns j) a) δ hδ
    (fun a j => hstage (ns j) a) (fun a => (hlim a).comp hns)
  choose η ξ hη hξ hηmono hξanti hbetween hηlim hξlim using hfamily
  let lo : ℕ → Fin n → M → EReal := fun j a => (η a j).val
  let hi : ℕ → Fin n → M → EReal := fun j a => (ξ a j).val
  have hC (a : Fin n) (j : ℕ) (x : M) : lo j a x ≤ ((0 : ℝ) : EReal) := by
    change (η a j).val x ≤ 0
    calc
      _ = singularityEnvelope (θ a).val (η a j).val x :=
        congrFun (hη a j).envelope_eq x
      _ ≤ 0 := singularityEnvelope_le_zero (θ a).val _ x
  have hl := tendsto_globalMixedMass_of_monotone_native omega hbig
    (fun j a => (η a j).property) hv hηmono hC hηlim
  have hh := tendsto_globalMixedMass_of_antitone_model_native omega hbig
    (fun j a => hξ a j) hv hξanti hvpos hξlim
  refine ⟨f, tendsto_of_tendsto_of_tendsto_of_le_of_le hl hh ?_ ?_⟩
  · intro j
    exact globalMixedMass_mono_of_isThetaPshPotential omega
      (fun a => (η a j).property) (fun a => (hu (ns (f j)) a).plurisubharmonic)
      (fun a => MoreSingularOn.of_le fun x _ => (hbetween a j).1 x)
  · intro j
    exact globalMixedMass_mono_of_isThetaPshPotential omega
      (fun a => (hu (ns (f j)) a).plurisubharmonic) (fun a => (ξ a j).property)
      (fun a => MoreSingularOn.of_le fun x _ => (hbetween a j).2 x)

/-- Genuine positive native targets internally produce eventual stage bounds
and the actual extended mixed-mass limit of arbitrary model sequences. -/
theorem tendsto_globalMixedMass_of_model_native_positive
    (omega : KahlerBackground n M) {θ : Fin n → ClosedRealOneOneForm n M}
    (hbig : ∀ a, IsBigClass (RealBottChern.ofRepresentative (θ a)))
    {u : ℕ → Fin n → M → EReal} {v : Fin n → M → EReal}
    (hu : ∀ j a, IsModelPotential (θ a) (u j a))
    (hv : ∀ a, IsThetaPshPotential (θ a).val (v a))
    (hvpos : ∀ a, 0 < diagonalPotentialMass (θ a) (v a) (hv a))
    (hlim : ∀ a, Tendsto
      (fun j => (⟨u j a, (hu j a).plurisubharmonic⟩ : ThetaPshL1 (θ a).val)) atTop
      (@nhds (ThetaPshL1 (θ a).val)
        (singularityPseudoMetricSpace omega (θ a) (hbig a)).toUniformSpace.toTopologicalSpace
        ⟨v a, hv a⟩)) :
    Tendsto (fun j => globalMixedMass θ (u j)
      (fun a => (hu j a).plurisubharmonic.1)) atTop
      (𝓝 (globalMixedMass θ v (fun a => (hv a).1))) := by
  let δ : Fin n → ℝ := fun a => (diagonalPotentialMass (θ a) (v a) (hv a)).toReal / 2
  have hp (a : Fin n) : 0 < (diagonalPotentialMass (θ a) (v a) (hv a)).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨hvpos a,
      globalMixedMass_lt_top omega (fun _ : Fin n => (hv a).1)⟩
  have hδ (a : Fin n) : 0 < δ a := div_pos (hp a) (by norm_num)
  have hevent : ∀ᶠ j in atTop, ∀ a, ENNReal.ofReal (δ a) ≤
      diagonalPotentialMass (θ a) (u j a) (hu j a).plurisubharmonic := by
    apply eventually_all.mpr
    intro a
    let := singularityPseudoMetricSpace omega (θ a) (hbig a)
    let : UniformSpace (ThetaPshL1 (θ a).val) :=
      (singularityPseudoMetricSpace omega (θ a) (hbig a)).toUniformSpace
    let : TopologicalSpace (ThetaPshL1 (θ a).val) :=
      (singularityPseudoMetricSpace omega (θ a) (hbig a)).toUniformSpace.toTopologicalSpace
    have hm := (diagonalPotentialMass_uniformContinuous omega (θ a) (hbig a)).continuous.tendsto
      (⟨v a, hv a⟩ : ThetaPshL1 (θ a).val) |>.comp (hlim a)
    have hlt : δ a < (diagonalPotentialMass (θ a) (v a) (hv a)).toReal := by
      dsimp [δ]
      linarith [hp a]
    filter_upwards [hm.eventually (Ioi_mem_nhds hlt)] with j hj
    change δ a < (diagonalPotentialMass (θ a) (u j a) (hu j a).plurisubharmonic).toReal at hj
    have hb := ENNReal.ofReal_le_ofReal hj.le
    have hfinit : diagonalPotentialMass (θ a) (u j a) (hu j a).plurisubharmonic ≠ ⊤ :=
      (globalMixedMass_lt_top omega (fun _ : Fin n => (hu j a).plurisubharmonic.1)).ne
    rwa [ENNReal.ofReal_toReal hfinit] at hb
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  apply (tendsto_add_atTop_iff_nat N).mp
  exact tendsto_mixedMass_of_uniform_model_native omega hbig
    (fun j a => hu (j + N) a) hv hvpos hδ
    (fun j a => hN (j + N) (Nat.le_add_left N j) a)
    (fun a => (hlim a).comp (tendsto_add_atTop_nat N))

end
end SGPT.Foundations.Analysis.Pending.ActualPositiveModelMixedContinuity
