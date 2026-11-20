import SGPT.Foundations.Analysis.Pending.SingularModelIncreasingRegularizedCapacity
import SGPT.Foundations.Analysis.Pending.SingularModelIncreasingMixedCapacity
import SGPT.Foundations.Analysis.Pending.IncreasingMixedRegularizedContinuity
import SGPT.Foundations.Analysis.Pending.NefBoundedMixedMass

set_option autoImplicit false

/-!
# Actual mixed canonical-gap integrals at increasing regularized suprema

An independent increasing adaptation of Lu, Theorem 2.5 and Lemma 4.1
Steps 1.2 and 2. Actual negligible-set capacity convergence, background
enlargement, and original-background regularized mixed weak convergence
produce the moving-weight limit without a pointwise-limit premise.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelIncreasingRegularizedMixedWeights

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar DiagonalMass
open SingularModelFiniteEnergyMixedGap SingularModelIncreasingMixedCapacity
open SingularModelIncreasingRegularizedCapacity CapacityWeightedConvergence ThetaCapacity
open RelativeEnergyIntegrability

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

private theorem binaryMixedMeasure_le_enlarge
    {θ γ : ClosedRealOneOneForm n M} (hγ : γ.val.IsSemipositive)
    {p q : M → EReal} (hp : IsThetaPshPotential θ.val p)
    (hq : IsThetaPshPotential θ.val q) (σ : Fin n → Bool) :
    binaryMixedMeasure hp hq σ ≤ binaryMixedMeasure
      (LocalPotentials.isThetaPshPotential_add_of_semipositive hp hγ)
      (LocalPotentials.isThetaPshPotential_add_of_semipositive hq hγ) σ := by
  have hg : ∀ i, IsThetaPshPotential θ.val (if σ i then p else q) := by
    intro i
    cases σ i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      first | exact hq | exact hp
  exact NefBoundedMixedMass.globalMixedMeasure_le_of_add_smul_on
    (Finset.univ : Finset (Fin n)) hγ one_pos
    (θ' := fun _ => θ + γ) (by simp)
    (fun i => (hg i).1) (fun i _ => hg i)
    (fun i => (LocalPotentials.isThetaPshPotential_add_of_semipositive (hg i) hγ).1)

variable [ConnectedSpace M]

/-- Genuine regularized increasing limits inside a fixed singular box
produce the actual binary mixed canonical-gap integral limit for arbitrary θ. -/
theorem tendsto_integral_canonicalGap_binaryMixedMeasure_regularized
    (omega : KahlerBackground n M) {θ : ClosedRealOneOneForm n M}
    {u : ℕ → M → EReal} {v : M → EReal}
    (hu : ∀ j, IsThetaPshPotential θ.val (u j))
    (hv : IsThetaPshPotential θ.val v) (hm : ∀ x, Monotone fun j => u j x)
    (hv0 : v ≤ 0) {B : ℝ} (hB : 0 ≤ B)
    (hvu : ∀ x, v x ≤ u 0 x + (B : EReal))
    (hreg : uscRegularization (⨆ j, u j) = v) (σ : Fin n → Bool) :
    Tendsto (fun j => ∫ x, canonicalERealDiffToReal (v x) (u j x)
      ∂binaryMixedMeasure (hu j) hv σ) atTop (𝓝 0) := by
  classical
  have huv : ∀ j, u j ≤ v := fun j x =>
    (le_iSup (fun k => u k) j x).trans (by rw [← hreg]; exact le_uscRegularization _ x)
  obtain ⟨A, hA, hγ⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omega (-θ)
  let γ := -θ + A • omega.form
  let Ω := KahlerBackground.smul hA omega
  have hform : θ + γ = Ω.form := by
    rw [KahlerBackground.smul_form]
    dsimp only [γ]
    abel
  have hform' : θ + (-θ + A • omega.form) = Ω.form := hform
  have lift {p : M → EReal} (hp : IsThetaPshPotential θ.val p) :
      IsThetaPshPotential Ω.form.val p := by
    rw [← hform]
    exact LocalPotentials.isThetaPshPotential_add_of_semipositive hp hγ
  let μ : ℕ → Measure M := fun j => binaryMixedMeasure (hu j) hv σ
  let ν := diagonalPotentialMeasure θ v hv
  have hbig := uniformCapacityControl_binaryMixedMeasure_of_box omega Ω.isSemipositive
    (lift hv) (fun j => lift (hu j)) (fun j x => hm x (Nat.zero_le j)) huv hv0 hB hvu σ
  have hcontrol : UniformCapacityControl (thetaCapacity Ω.form (fun _ => 0)) μ ν := by
    intro r hr
    obtain ⟨ε, hε, hsmall⟩ := hbig r hr
    refine ⟨ε, hε, fun E hE hcap => ⟨fun j => ?_, ?_⟩⟩
    · have hd : μ j ≤ binaryMixedMeasure (lift (hu j)) (lift hv) σ := by
        simpa only [μ, hform'] using binaryMixedMeasure_le_enlarge hγ (hu j) hv σ
      exact (Measure.le_iff'.mp hd E).trans ((hsmall E hE hcap).1 j)
    · have hd : ν ≤ diagonalPotentialMeasure Ω.form v (lift hv) := by
        simpa only [ν, hform', binaryMixedMeasure, ite_self, diagonalPotentialMeasure] using
          binaryMixedMeasure_le_enlarge hγ hv hv σ
      exact (Measure.le_iff'.mp hd E).trans (hsmall E hE hcap).2
  have ht : SameSingularityTypeOn (u 0) v univ :=
    ⟨MoreSingularOn.of_le fun x _ => huv 0 x, ⟨B, fun x _ => hvu x⟩⟩
  have hcap : ∀ δ : ℝ, 0 < δ → Tendsto
      (fun j => thetaCapacity Ω.form (fun _ => 0)
        {x | δ < |canonicalERealDiffToReal (v x) (u j x) - 0|}) atTop (𝓝 0) := by
    intro δ hδ
    simpa only [sub_zero] using tendsto_capacity_canonicalGap_of_monotone_regularized Ω
      (fun j => lift (hu j)) (lift hv) hm hv0 ht hreg hδ
  let ψ : ℕ → Fin n → M → EReal := fun j i => if σ i then u j else v
  have hψ : ∀ j i, IsThetaPshPotential θ.val (ψ j i) := by
    intro j i
    change IsThetaPshPotential θ.val (if σ i then u j else v)
    cases σ i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      first | exact hv | exact hu j
  have hψm : ∀ i, Monotone fun j => ψ j i := by
    intro i j k hjk x
    change (if σ i then u j else v) x ≤ (if σ i then u k else v) x
    cases σ i <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact le_rfl
    · exact hm x hjk
  have hψreg : ∀ i, uscRegularization (⨆ j, ψ j i) = v := by
    intro i
    change uscRegularization (⨆ j, if σ i then u j else v) = v
    cases σ i <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [iSup_const]
      exact uscRegularization_eq hv.1.quasiPlurisubharmonic.upperSemicontinuous
    · exact hreg
  have hψv : ∀ i, IsThetaPshPotential θ.val (uscRegularization (⨆ j, ψ j i)) :=
    fun i => (hψreg i).symm ▸ hv
  have hweak : ∀ w : C(M, ℝ), Tendsto (fun j => ∫ x, w x ∂μ j) atTop
      (𝓝 (∫ x, w x ∂ν)) := by
    intro w
    have h := IncreasingMixedRegularizedContinuity.tendsto_integral_mixed_of_monotone_regularized
      omega hψ hψm hψv w
    simpa only [hψreg, μ, ν, ψ, binaryMixedMeasure, diagonalPotentialMeasure] using h
  have hfm : ∀ j, Measurable (fun x => canonicalERealDiffToReal (v x) (u j x)) := fun j =>
    measurable_canonicalERealDiffToReal.comp
      (hv.1.quasiPlurisubharmonic.upperSemicontinuous.measurable.prodMk
        (hu j).1.quasiPlurisubharmonic.upperSemicontinuous.measurable)
  have hfb : ∀ j x, |canonicalERealDiffToReal (v x) (u j x)| ≤ B := by
    intro j x
    rw [canonicalERealDiffToReal_swap, abs_neg]
    exact PoleCoalescingCapacity.abs_canonicalDiff_le_of_orderGap hB (huv j) hv0
      (fun y => (hvu y).trans (add_le_add (hm y (Nat.zero_le j)) le_rfl)) x
  have hq0 : QuasiContinuousFor (thetaCapacity Ω.form (fun _ => 0)) (fun _ => (0 : ℝ)) := by
    intro ε hε
    exact ⟨∅, isOpen_empty, by simpa only [thetaCapacity_empty] using hε, continuousOn_const⟩
  have : ∀ j, IsFiniteMeasure (μ j) := fun j => globalMixedMeasure_isFiniteMeasure omega _
  have : IsFiniteMeasure ν := globalMixedMeasure_isFiniteMeasure omega _
  have h := tendsto_integral_mul_of_capacity hcontrol hweak hfm measurable_const hq0
    hB hfb (fun _ => by simpa only [abs_zero] using hB) hcap (1 : C(M, ℝ))
  simpa only [ContinuousMap.coe_one, Pi.one_apply, one_mul, mul_zero, integral_zero] using h

end

end SGPT.Foundations.Analysis.Pending.SingularModelIncreasingRegularizedMixedWeights
