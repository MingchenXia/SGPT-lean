import SGPT.PSH.SourceDarvasCompleteness
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasMonotoneSandwich

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open scoped Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
  {hφ : SourceModelPotential θ φ}

/-- WHOLE original monotone sandwich lemma: one produced strict subsequence,
actual E1 lower/upper sequences, both genuine Darvas limits, the all-point
upper EReal limit and the original GLOBAL-volume lower AE limit. -/
theorem sourceDarvas_monotone_sandwich (omega : KahlerBackground n M)
    (ui : ℕ → SourceFiniteEnergyPotential θ φ hφ) (u : SourceFiniteEnergyPotential θ φ hφ)
    (hd : Tendsto (fun i ↦ sourceDarvasDistance θ φ hφ (ui i) u) atTop (𝓝 0)) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      ∃ η ψ : ℕ → SourceFiniteEnergyPotential θ φ hφ,
        (∀ x, Monotone fun i ↦ (η i).val x) ∧ (∀ x, Antitone fun i ↦ (ψ i).val x) ∧
        (∀ i, (η i).val ≤ (ui (f i)).val ∧ (ui (f i)).val ≤ (ψ i).val) ∧
        Tendsto (fun i ↦ sourceDarvasDistance θ φ hφ (η i) u) atTop (𝓝 0) ∧
        Tendsto (fun i ↦ sourceDarvasDistance θ φ hφ (ψ i) u) atTop (𝓝 0) ∧
        (∀ x, Tendsto (fun i ↦ (ψ i).val x) atTop (𝓝 (u.val x))) ∧
        (∀ᵐ x ∂sourceKahlerVolume omega,
          Tendsto (fun i ↦ (η i).val x) atTop (𝓝 (u.val x))) := by
  let := SingularModelDarvasMetricSpace.finiteEnergyMetricSpace
    (θ := atlasClosedFormToNative θ) (φ := φ) (hφ := hφ.toNative) omega
  let : UniformSpace (SingularModelDarvasMetricSpace.ModelFiniteEnergyPotential
      (atlasClosedFormToNative θ) φ hφ.toNative) :=
    (SingularModelDarvasMetricSpace.finiteEnergyMetricSpace
      (θ := atlasClosedFormToNative θ) (φ := φ) (hφ := hφ.toNative) omega).toUniformSpace
  let : TopologicalSpace (SingularModelDarvasMetricSpace.ModelFiniteEnergyPotential
      (atlasClosedFormToNative θ) φ hφ.toNative) :=
    (SingularModelDarvasMetricSpace.finiteEnergyMetricSpace
      (θ := atlasClosedFormToNative θ) (φ := φ) (hφ := hφ.toNative) omega).toUniformSpace.toTopologicalSpace
  let e := sourceFiniteEnergyPotentialEquivNative θ φ hφ
  have hn := (sourceDarvas_tendsto_iff_native omega ui u).mp hd
  obtain ⟨f, hf, η, ψ, hm, hanti, hs, hη, hψ, hp, hae⟩ :=
    SingularModelDarvasMonotoneSandwich.exists_strictMono_monotone_sandwich_of_tendsto
      omega (fun i ↦ e (ui i)) (e u) hn
  refine ⟨f, hf, (fun i ↦ e.symm (η i)), (fun i ↦ e.symm (ψ i)),
    hm, hanti, hs, ?_, ?_, hp, ?_⟩
  · apply (sourceDarvas_tendsto_iff_native omega (fun i ↦ e.symm (η i)) u).mpr
    change Tendsto (fun i ↦ e (e.symm (η i))) atTop (𝓝 (e u))
    simpa only [Equiv.apply_symm_apply] using hη
  · apply (sourceDarvas_tendsto_iff_native omega (fun i ↦ e.symm (ψ i)) u).mpr
    change Tendsto (fun i ↦ e (e.symm (ψ i))) atTop (𝓝 (e u))
    simpa only [Equiv.apply_symm_apply] using hψ
  · rw [sourceKahlerVolume_eq_native]
    exact hae

/-- Actual original E1 rooftop closure and energy order give the genuine
one-Lipschitz finite energy bound, on the ENTIRE original preceq class. -/
theorem sourceRelativeEnergy_abs_sub_le_darvas (omega : KahlerBackground n M)
    (u v : SourceFiniteEnergyPotential θ φ hφ) :
    |(sourceRelativeEnergy θ φ u.val hφ).toReal -
      (sourceRelativeEnergy θ φ v.val hφ).toReal| ≤ sourceDarvasDistance θ φ hφ u v := by
  simp only [sourceRelativeEnergy_eq_native, sourceDarvasDistance_eq_native omega]
  exact SingularModelDarvasEnergyContinuity.abs_energy_sub_le_relativeD1 omega
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp u.property)
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp v.property)

/-- The actual original finite real energy is one-Lipschitz for the
actual Darvas metric, its induced uniformity and its induced topology. -/
theorem sourceRelativeEnergy_lipschitzWith (omega : KahlerBackground n M) :
    letI := sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (SourceFiniteEnergyPotential θ φ hφ) :=
      (sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    letI : TopologicalSpace (SourceFiniteEnergyPotential θ φ hφ) :=
      (sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
    LipschitzWith 1 (fun u : SourceFiniteEnergyPotential θ φ hφ ↦
      (sourceRelativeEnergy θ φ u.val hφ).toReal) := by
  let := sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (SourceFiniteEnergyPotential θ φ hφ) :=
    (sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  let : TopologicalSpace (SourceFiniteEnergyPotential θ φ hφ) :=
    (sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simp only [Real.dist_eq, NNReal.coe_one, one_mul, sourceDarvasMetricSpace_dist omega]
  exact sourceRelativeEnergy_abs_sub_le_darvas omega u v

/-- WHOLE original thm:Efuncont on the genuine Darvas topology of the
WHOLE original E1 class, with an arbitrary unbounded original model. -/
theorem sourceRelativeEnergy_continuous (omega : KahlerBackground n M) :
    letI := sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (SourceFiniteEnergyPotential θ φ hφ) :=
      (sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    letI : TopologicalSpace (SourceFiniteEnergyPotential θ φ hφ) :=
      (sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
    Continuous (fun u : SourceFiniteEnergyPotential θ φ hφ ↦
      (sourceRelativeEnergy θ φ u.val hφ).toReal) := by
  let := sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (SourceFiniteEnergyPotential θ φ hφ) :=
    (sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  let : TopologicalSpace (SourceFiniteEnergyPotential θ φ hφ) :=
    (sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  exact (sourceRelativeEnergy_lipschitzWith (θ := θ) (φ := φ) (hφ := hφ) omega).continuous

/-- Actual Darvas convergence along ANY filter implies convergence of the
original finite real energy; no monotonicity or subsequence premise. -/
theorem sourceRelativeEnergy_toReal_tendsto_of_darvas {I : Type*} {F : Filter I}
    (omega : KahlerBackground n M) (ui : I → SourceFiniteEnergyPotential θ φ hφ)
    (u : SourceFiniteEnergyPotential θ φ hφ)
    (hd : Tendsto (fun i ↦ sourceDarvasDistance θ φ hφ (ui i) u) F (𝓝 0)) :
    Tendsto (fun i ↦ (sourceRelativeEnergy θ φ (ui i).val hφ).toReal) F
      (𝓝 (sourceRelativeEnergy θ φ u.val hφ).toReal) := by
  simp only [sourceDarvasDistance_eq_native omega] at hd
  simp only [sourceRelativeEnergy_eq_native]
  exact SingularModelDarvasEnergyContinuity.toReal_energy_tendsto_of_relativeD1_tendsto_zero omega
    (fun i ↦ (sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp (ui i).property)
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp u.property) hd

/-- Both actual energy endpoints are excluded on E1 BEFORE readback;
the identical original EReal energies therefore converge along ANY filter. -/
theorem sourceRelativeEnergy_tendsto_of_darvas {I : Type*} {F : Filter I}
    (omega : KahlerBackground n M) (ui : I → SourceFiniteEnergyPotential θ φ hφ)
    (u : SourceFiniteEnergyPotential θ φ hφ)
    (hd : Tendsto (fun i ↦ sourceDarvasDistance θ φ hφ (ui i) u) F (𝓝 0)) :
    Tendsto (fun i ↦ sourceRelativeEnergy θ φ (ui i).val hφ) F
      (𝓝 (sourceRelativeEnergy θ φ u.val hφ)) := by
  simp only [sourceDarvasDistance_eq_native omega] at hd
  simp only [sourceRelativeEnergy_eq_native]
  exact SingularModelDarvasEnergyContinuity.energy_tendsto_of_relativeD1_tendsto_zero omega
    (fun i ↦ (sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp (ui i).property)
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp u.property) hd

end SGPT.PSH.VariableComplexAtlas
