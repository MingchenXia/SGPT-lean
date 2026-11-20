import SGPT.PSH.SourceCapacity

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped ENNReal

variable {n : ℕ} {M : Type*} [TopologicalSpace M]

/-- Literal real-valued continuity on the original open subspace outside G.
The representative is unrestricted on G, where the original f may have either pole. -/
def RealContinuousOff (U : Opens M) (f : U → EReal) (G : Set M) : Prop :=
  ∃ g : U → ℝ, ContinuousOn g {x : U | x.1 ∉ G} ∧
    EqOn f (fun x ↦ (g x : EReal)) {x : U | x.1 ∉ G}

/-- The exact original real-valued clause is finite EReal continuity, not merely
continuity into the compactified line. No pole is replaced on the original domain. -/
theorem realContinuousOff_iff (U : Opens M) (f : U → EReal) (G : Set M) :
    RealContinuousOff U f G ↔
      (∀ x : U, x.1 ∉ G → f x ≠ ⊤ ∧ f x ≠ ⊥) ∧
        ContinuousOn f {x : U | x.1 ∉ G} := by
  constructor
  · rintro ⟨g, hg, hfg⟩
    constructor
    · intro x hx
      rw [hfg hx]
      exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩
    · exact (continuous_coe_real_ereal.comp_continuousOn hg).congr hfg
  · rintro ⟨hfinite, hf⟩
    refine ⟨fun x ↦ (f x).toReal, ?_, ?_⟩
    · intro x hx
      exact (EReal.tendsto_toReal (hfinite x hx).1 (hfinite x hx).2).comp (hf x hx)
    · intro x hx
      exact (EReal.coe_toReal (hfinite x hx).1 (hfinite x hx).2).symm

variable [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Original `def:qc_fun`, retaining Borel measurability and real-valued continuity
off an ambient open exceptional subset of the original open domain. -/
def SourceQuasiContinuousOn (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (U : Opens M) (f : U → EReal) : Prop :=
  Measurable f ∧ ∀ ε : ℝ, 0 < ε → ∃ G : Set M,
    IsOpen G ∧ G ⊆ U ∧ sourceThetaCapacity θ G ≤ ENNReal.ofReal ε ∧
      RealContinuousOff U f G

omit [BorelSpace M] in
/-- Whole native-capacity dictionary with every original Borel, open-domain,
finiteness, and continuity clause retained. -/
theorem sourceQuasiContinuousOn_iff_native
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (U : Opens M) (f : U → EReal) :
    SourceQuasiContinuousOn θ U f ↔ Measurable f ∧
      ∀ ε : ℝ, 0 < ε → ∃ G : Set M, IsOpen G ∧ G ⊆ U ∧
        ThetaCapacity.thetaCapacityV (atlasClosedFormToNative θ) G ≤ ENNReal.ofReal ε ∧
          (∀ x : U, x.1 ∉ G → f x ≠ ⊤ ∧ f x ≠ ⊥) ∧
            ContinuousOn f {x : U | x.1 ∉ G} := by
  simp only [SourceQuasiContinuousOn, sourceThetaCapacity_eq_native, realContinuousOff_iff]

/-- A genuine continuous real function supplies original quasi-continuity.
The actual exceptional set is empty, with actual capacity zero. -/
theorem sourceQuasiContinuousOn_of_continuous_real
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (U : Opens M)
    {g : U → ℝ} (hg : Continuous g) :
    SourceQuasiContinuousOn θ U (fun x ↦ (g x : EReal)) := by
  refine ⟨(continuous_coe_real_ereal.comp hg).measurable, ?_⟩
  intro ε _hε
  refine ⟨∅, isOpen_empty, empty_subset _, ?_, ?_⟩
  · simp only [sourceThetaCapacity_empty, zero_le]
  · exact ⟨g, hg.continuousOn, fun _ _ ↦ rfl⟩

end SGPT.PSH.VariableComplexAtlas
