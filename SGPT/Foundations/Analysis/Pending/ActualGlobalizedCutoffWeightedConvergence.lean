import SGPT.Foundations.Analysis.Pending.ActualChartCapacityLiftConvergence
import SGPT.Foundations.Analysis.Pending.ActualBoundedPshCutoffWeightedConvergence

set_option autoImplicit false

/-! # One synchronized operator for actual local cutoff weighted families

The actual operator is chosen from chart geometry before all mixed tuples,
independent weight seeds and Lipschitz classifiers. Its genuine bounded
PSH lifts and capacity limits produce actual weighted mixed integrals on
the compact host, retaining all masks and dimension zero.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ActualGlobalizedCutoffWeightedConvergence

open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
  GlobalNonPluripolar BedfordTaylor ThetaCapacity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- One true geometry-first operator lifts every later normalized local tuple
and independent cutoff seed family to genuine weighted mixed integral limits. -/
theorem exists_synchronized_classifier_weighted_lift (omega : KahlerBackground n M)
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
        ∀ (m : ℕ) (w : ℕ → Fin m → ComplexModel n → ℝ)
          (z : Fin m → ComplexModel n → ℝ)
          (_hw : ∀ j i, IsLocallyBoundedPshOn D (w j i))
          (_hz : ∀ i, IsLocallyBoundedPshOn D (z i))
          (_hwB : ∀ j i y, y ∈ D → -1 ≤ w j i y ∧ w j i y ≤ 0)
          (_hzB : ∀ i y, y ∈ D → -1 ≤ z i y ∧ z i y ≤ 0),
          (∀ i (V : Opens (ComplexModel n)), V ≤ D → ∀ T : Set (ComplexModel n),
            IsCompact T → T ⊆ V → ∀ a : ℝ, 0 < a →
            Tendsto (fun j => relCapacity V {y | y ∈ T ∧ a < |w j i y - z i y|})
              atTop (𝓝 0)) →
          ∃ (hU : ∀ j i, IsThetaPshPotential omega.form.val (lift (u j i)))
            (hV : ∀ i, IsThetaPshPotential omega.form.val (lift (v i))),
            ∀ (Φ : (Fin m → ℝ) → ℝ) (L : NNReal), LipschitzWith L Φ →
            ∀ h : C(M, ℝ), Tendsto
              (fun j => ∫ x, h x * Φ (fun i => (lift (w j i) x).toReal)
                ∂globalMixedMeasure (fun _ : Fin n => omega.form)
                  (fun i => lift (u j i)) (fun i => (hU j i).1)) atTop
              (𝓝 (∫ x, h x * Φ (fun i => (lift (z i) x).toReal)
                ∂globalMixedMeasure (fun _ : Fin n => omega.form)
                  (fun i => lift (v i)) (fun i => (hV i).1))) := by
  obtain ⟨δ, hδ, O, lift, hO, hKO, hOS, hPSH, hcap⟩ :=
    ActualChartCapacityLiftConvergence.exists_capacity_convergent_lifts
      (I := ℕ) omega e hDt hρ hK hKD
  refine ⟨δ, hδ, O, lift, hO, hKO, hOS, hPSH, ?_⟩
  intro u v hu hv huB hvB hlocal m w z hw hz hwB hzB hseedlocal
  let hU : ∀ j i, IsThetaPshPotential omega.form.val (lift (u j i)) :=
    fun j i => (hPSH (u j i) (hu j i) (huB j i)).1
  let hV : ∀ i, IsThetaPshPotential omega.form.val (lift (v i)) :=
    fun i => (hPSH (v i) (hv i) (hvB i)).1
  let hW : ∀ j i, IsThetaPshPotential omega.form.val (lift (w j i)) :=
    fun j i => (hPSH (w j i) (hw j i) (hwB j i)).1
  let hZ : ∀ i, IsThetaPshPotential omega.form.val (lift (z i)) :=
    fun i => (hPSH (z i) (hz i) (hzB i)).1
  have hUB : ∀ j i x, ((-(1 : ℝ) : ℝ) : EReal) ≤ lift (u j i) x ∧
      lift (u j i) x ≤ ((1 : ℝ) : EReal) := by
    intro j i x
    have hh := (hPSH (u j i) (hu j i) (huB j i)).2.1 x
    exact ⟨hh.1, hh.2.trans (by norm_num)⟩
  have hVB : ∀ i x, ((-(1 : ℝ) : ℝ) : EReal) ≤ lift (v i) x ∧
      lift (v i) x ≤ ((1 : ℝ) : EReal) := by
    intro i x
    have hh := (hPSH (v i) (hv i) (hvB i)).2.1 x
    exact ⟨hh.1, hh.2.trans (by norm_num)⟩
  have hWB : ∀ j i x, (-1 : EReal) ≤ lift (w j i) x ∧ lift (w j i) x ≤ 0 :=
    fun j i => (hPSH (w j i) (hw j i) (hwB j i)).2.1
  have hZB : ∀ i x, (-1 : EReal) ≤ lift (z i) x ∧ lift (z i) x ≤ 0 :=
    fun i => (hPSH (z i) (hz i) (hzB i)).2.1
  have hglobal : ∀ i a, 0 < a → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | a < |(lift (u j i) x).toReal - (lift (v i) x).toReal|}) atTop (𝓝 0) := by
    intro i a ha
    exact hcap atTop (fun j => u j i) (v i) (fun j => huB j i) (hvB i) (hlocal i) a ha
  have hseedglobal : ∀ i a, 0 < a → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | a < |(lift (w j i) x).toReal - (lift (z i) x).toReal|}) atTop (𝓝 0) := by
    intro i a ha
    exact hcap atTop (fun j => w j i) (z i) (fun j => hwB j i) (hzB i) (hseedlocal i) a ha
  refine ⟨hU, hV, fun Φ L hΦ h => ?_⟩
  exact ActualBoundedPshCutoffWeightedConvergence.tendsto_integral_classifier_of_capacity
    omega hU hV (by norm_num : (0 : ℝ) ≤ 1) hUB hVB hglobal
    hW hZ hWB hZB hseedglobal hΦ h

end
end SGPT.Foundations.Analysis.Pending.ActualGlobalizedCutoffWeightedConvergence
