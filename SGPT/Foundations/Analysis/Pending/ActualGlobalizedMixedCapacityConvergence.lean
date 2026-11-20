import SGPT.Foundations.Analysis.Pending.ActualChartCapacityLiftConvergence
import SGPT.Foundations.Analysis.Pending.ActualBoundedMixedCapacityContinuity

set_option autoImplicit false

/-! # Actual mixed weak convergence of one synchronized global lift

The common geometry/operator precedes every incoming tuple. Genuine PSH,
finite boxes, and global capacity convergence are produced from local
capacity on every smaller domain and compact. All continuous tests and
dimension zero are retained. Removing the core's fixed local potential
and unbounded mixed-mass lower semicontinuity remain separate consumers.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ActualGlobalizedMixedCapacityConvergence

open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
  GlobalNonPluripolar BedfordTaylor ThetaCapacity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The common actual lift precedes all tuples and realizes genuine mixed weak
limits against every continuous global test, with no incoming weak certificate. -/
theorem exists_synchronized_mixed_weak_lift (omega : KahlerBackground n M)
    (e : ComplexChart n M) {D : Opens (ComplexModel n)}
    (hDt : (D : Set (ComplexModel n)) ⊆ e.val.target)
    {ρ : ComplexModel n → ℝ} (hρ : IsSmoothLocalPotential omega.form.val e D ρ)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ (O : Set M) (lift : (ComplexModel n → ℝ) → M → EReal),
      IsOpen O ∧ e.val.symm '' K ⊆ O ∧
      O ⊆ e.val.source ∩ e.val ⁻¹' (D : Set (ComplexModel n)) ∧
      (∀ f, IsLocallyBoundedPshOn D f → (∀ z ∈ D, -1 ≤ f z ∧ f z ≤ 0) →
        IsThetaPshPotential omega.form.val (lift f) ∧
        (∀ x, (-1 : EReal) ≤ lift f x ∧ lift f x ≤ 0) ∧
        ∀ x ∈ O, lift f x = ((δ * f (e.val x) - δ : ℝ) : EReal)) ∧
      ∀ (u : ℕ → Fin n → ComplexModel n → ℝ) (v : Fin n → ComplexModel n → ℝ)
        (_hu : ∀ j i, IsLocallyBoundedPshOn D (u j i))
        (_hv : ∀ i, IsLocallyBoundedPshOn D (v i))
        (_huB : ∀ j i z, z ∈ D → -1 ≤ u j i z ∧ u j i z ≤ 0)
        (_hvB : ∀ i z, z ∈ D → -1 ≤ v i z ∧ v i z ≤ 0),
        (∀ i (V : Opens (ComplexModel n)), V ≤ D → ∀ T : Set (ComplexModel n),
          IsCompact T → T ⊆ V → ∀ a : ℝ, 0 < a →
          Tendsto (fun j => relCapacity V {z | z ∈ T ∧ a < |u j i z - v i z|})
            atTop (𝓝 0)) →
        ∃ (hW : ∀ j i, IsThetaPshPotential omega.form.val (lift (u j i)))
          (hV : ∀ i, IsThetaPshPotential omega.form.val (lift (v i))),
        ∀ h : C(M, ℝ), Tendsto
          (fun j => ∫ x, h x ∂globalMixedMeasure (fun _ : Fin n => omega.form)
            (fun i => lift (u j i)) (fun i => (hW j i).1)) atTop
          (𝓝 (∫ x, h x ∂globalMixedMeasure (fun _ : Fin n => omega.form)
            (fun i => lift (v i)) (fun i => (hV i).1))) := by
  obtain ⟨δ, hδ, O, lift, hO, hKO, hOS, hPSH, hcap⟩ :=
    ActualChartCapacityLiftConvergence.exists_capacity_convergent_lifts
      (I := ℕ) omega e hDt hρ hK hKD
  refine ⟨δ, hδ, O, lift, hO, hKO, hOS, hPSH, ?_⟩
  intro u v hu hv huB hvB hlocal
  let hW : ∀ j i, IsThetaPshPotential omega.form.val (lift (u j i)) :=
    fun j i => (hPSH (u j i) (hu j i) (huB j i)).1
  let hV : ∀ i, IsThetaPshPotential omega.form.val (lift (v i)) :=
    fun i => (hPSH (v i) (hv i) (hvB i)).1
  refine ⟨hW, hV, fun h => ?_⟩
  have hWB : ∀ j i x, ((-(1 : ℝ) : ℝ) : EReal) ≤ lift (u j i) x ∧
      lift (u j i) x ≤ ((1 : ℝ) : EReal) := by
    intro j i x
    have hh := (hPSH (u j i) (hu j i) (huB j i)).2.1 x
    exact ⟨hh.1, hh.2.trans (by norm_num)⟩
  have hVB : ∀ i x, ((-(1 : ℝ) : ℝ) : EReal) ≤ lift (v i) x ∧
      lift (v i) x ≤ ((1 : ℝ) : EReal) := by
    intro i x
    have hh := (hPSH (v i) (hv i) (hvB i)).2.1 x
    exact ⟨hh.1, hh.2.trans (by norm_num)⟩
  have hglobal : ∀ i a, 0 < a → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | a < |(lift (u j i) x).toReal - (lift (v i) x).toReal|}) atTop (𝓝 0) := by
    intro i a ha
    exact hcap atTop (fun j => u j i) (v i) (fun j => huB j i) (hvB i) (hlocal i) a ha
  exact ActualBoundedMixedCapacityContinuity.tendsto_integral_continuous_of_capacity
    omega hW hV (by norm_num : (0 : ℝ) ≤ 1) hWB hVB hglobal h

end
end SGPT.Foundations.Analysis.Pending.ActualGlobalizedMixedCapacityConvergence
