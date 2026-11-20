import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityModelSandwich
import SGPT.Foundations.Analysis.Pending.SingularGlobalPEnvelopeBridge
import SGPT.Foundations.Analysis.Pending.SingularCanonicalDistanceZeroPEquivalence
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeIdempotencePositive

set_option autoImplicit false

/-! # One true common model sandwich for independent finite slots

An independent finite-coordinate adaptation of SGPT PDF0228--0230,
used in the positive-mass part of PDF0235--0237 Theorem 6.2.1.
The actual upper P-models and the one common strict subsequence are
internally produced. No mixed-mass convergence is assumed or claimed.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualFiniteModelMixedSandwich

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  DiagonalMass MixedMass ThetaPshL1Topology SingularCanonicalSingularityDistance
  SingularCanonicalSingularityModelSandwich SingularGlobalPEnvelopeBridge
  SingularCanonicalDistanceZeroPEquivalence

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

private theorem exists_model_sandwich_one
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (ui : ℕ → ThetaPshL1 θ.val) (v : ThetaPshL1 θ.val)
    (hmodels : ∀ i, IsModelPotential θ (ui i).val) {δ : ℝ} (hδ : 0 < δ)
    (hstage : ∀ i, ENNReal.ofReal δ ≤ diagonalPotentialMass θ (ui i).val (ui i).property) :
    letI := singularityPseudoMetricSpace omega θ hbig
    letI : TopologicalSpace (ThetaPshL1 θ.val) :=
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
    Tendsto ui atTop (𝓝 v) → ∃ f : ℕ → ℕ, StrictMono f ∧
      ∃ η ξ : ℕ → ThetaPshL1 θ.val,
        (∀ i, IsModelPotential θ (η i).val) ∧
        (∀ i, IsModelPotential θ (ξ i).val) ∧
        Monotone (fun i => (η i).val) ∧ Antitone (fun i => (ξ i).val) ∧
        (∀ i, (η i).val ≤ (ui (f i)).val ∧ (ui (f i)).val ≤ (ξ i).val) ∧
        Tendsto η atTop (𝓝 v) ∧ Tendsto ξ atTop (𝓝 v) := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  intro hlim
  obtain ⟨f, hf, η, ψ, _, _, hη, hηmono, hψanti, hbetween, hηlim, hψlim⟩ :=
    exists_strictMono_monotone_sandwich_of_tendsto omega θ hbig ui v
      hmodels hδ hstage hlim
  have hψpos (i : ℕ) : 0 < diagonalPotentialMass θ (ψ i).val (ψ i).property :=
    ((ENNReal.ofReal_pos.mpr hδ).trans_le (hstage (f i))).trans_le
      (diagonalPotentialMass_mono_of_kahler omega (ui (f i)).property (ψ i).property
        (MoreSingularOn.of_le fun x _ => (hbetween i).2 x))
  have hP (i : ℕ) : IsThetaPshPotential θ.val (singularityEnvelope θ.val (ψ i).val) :=
    singularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      (ψ i).property.1.hasSmoothLocalPotentials (ψ i).val (ψ i).property
  have hξmodel (i : ℕ) : IsModelPotential θ (singularityEnvelope θ.val (ψ i).val) :=
    ⟨hP i, (RooftopEnvelopeIdempotence.singularityEnvelope_idempotent_of_positive_mass
      omega θ (ψ i).val (ψ i).property (hψpos i)).symm,
      (singularityEnvelopeMassPreserving omega θ (ψ i).val (ψ i).property (hP i)).symm ▸
        hψpos i⟩
  let ξ : ℕ → ThetaPshL1 θ.val := fun i =>
    ⟨singularityEnvelope θ.val (ψ i).val, hP i⟩
  have hξanti : Antitone fun i => (ξ i).val := by
    intro i j hij
    exact singularityEnvelope_mono (θ := θ.val)
      (MoreSingularOn.of_le fun x _ => hψanti x hij)
  have hξbetween (i : ℕ) : (η i).val ≤ (ui (f i)).val ∧ (ui (f i)).val ≤ (ξ i).val := by
    refine ⟨(hbetween i).1, ?_⟩
    calc
      (ui (f i)).val = singularityEnvelope θ.val (ui (f i)).val := (hmodels (f i)).envelope_eq
      _ ≤ (ξ i).val := singularityEnvelope_mono (θ := θ.val)
        (MoreSingularOn.of_le fun x _ => (hbetween i).2 x)
  have hzero (i : ℕ) : dist (ξ i) (ψ i) = 0 := by
    have he := sourcePEquivalent_singularityEnvelope omega θ (ψ i).property
    have hz := (singularityDistance_eq_zero_iff_sourcePEquivalent omega θ hbig
      (ξ i).property (ψ i).property).mpr ⟨he.2, he.1⟩
    rw [dist_eq_singularityDistance_toReal omega θ hbig, hz, EReal.toReal_zero]
  have hξlim : Tendsto ξ atTop (𝓝 v) := tendsto_iff_dist_tendsto_zero.mpr (by
    have hd := tendsto_iff_dist_tendsto_zero.mp hψlim
    apply squeeze_zero (fun _ => dist_nonneg) (fun i => ?_) hd
    have h := dist_triangle (ξ i) (ψ i) v
    simpa only [hzero, zero_add] using h)
  exact ⟨f, hf, η, ξ, hη, hξmodel, hηmono, hξanti, hξbetween, hηlim, hξlim⟩

/-- One genuine common strict subsequence for all independent finite model slots. -/
theorem exists_simultaneous_model_sandwich
    (omega : KahlerBackground n M) (θ : Fin n → ClosedRealOneOneForm n M)
    (hbig : ∀ a, IsBigClass (RealBottChern.ofRepresentative (θ a)))
    (ui : (a : Fin n) → ℕ → ThetaPshL1 (θ a).val)
    (v : (a : Fin n) → ThetaPshL1 (θ a).val)
    (hmodels : ∀ a i, IsModelPotential (θ a) (ui a i).val)
    (δ : Fin n → ℝ) (hδ : ∀ a, 0 < δ a)
    (hstage : ∀ a i, ENNReal.ofReal (δ a) ≤
      diagonalPotentialMass (θ a) (ui a i).val (ui a i).property)
    (hlim : ∀ a,
      letI := singularityPseudoMetricSpace omega (θ a) (hbig a)
      letI : TopologicalSpace (ThetaPshL1 (θ a).val) :=
        (singularityPseudoMetricSpace omega (θ a) (hbig a)).toUniformSpace.toTopologicalSpace
      Tendsto (ui a) atTop (𝓝 (v a))) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ a,
      letI := singularityPseudoMetricSpace omega (θ a) (hbig a)
      letI : TopologicalSpace (ThetaPshL1 (θ a).val) :=
        (singularityPseudoMetricSpace omega (θ a) (hbig a)).toUniformSpace.toTopologicalSpace
      ∃ η ξ : ℕ → ThetaPshL1 (θ a).val,
        (∀ i, IsModelPotential (θ a) (η i).val) ∧
        (∀ i, IsModelPotential (θ a) (ξ i).val) ∧
        Monotone (fun i => (η i).val) ∧ Antitone (fun i => (ξ i).val) ∧
        (∀ i, (η i).val ≤ (ui a (f i)).val ∧ (ui a (f i)).val ≤ (ξ i).val) ∧
        Tendsto η atTop (𝓝 (v a)) ∧ Tendsto ξ atTop (𝓝 (v a)) := by
  have hfinite (s : Finset (Fin n)) : ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ a ∈ s,
      letI := singularityPseudoMetricSpace omega (θ a) (hbig a)
      letI : TopologicalSpace (ThetaPshL1 (θ a).val) :=
        (singularityPseudoMetricSpace omega (θ a) (hbig a)).toUniformSpace.toTopologicalSpace
      ∃ η ξ : ℕ → ThetaPshL1 (θ a).val,
        (∀ i, IsModelPotential (θ a) (η i).val) ∧
        (∀ i, IsModelPotential (θ a) (ξ i).val) ∧
        Monotone (fun i => (η i).val) ∧ Antitone (fun i => (ξ i).val) ∧
        (∀ i, (η i).val ≤ (ui a (f i)).val ∧ (ui a (f i)).val ≤ (ξ i).val) ∧
        Tendsto η atTop (𝓝 (v a)) ∧ Tendsto ξ atTop (𝓝 (v a)) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨id, strictMono_id, fun a ha => False.elim (by simp at ha)⟩
    | @insert a s ha ih =>
      obtain ⟨f, hf, hs⟩ := ih
      let := singularityPseudoMetricSpace omega (θ a) (hbig a)
      let : TopologicalSpace (ThetaPshL1 (θ a).val) :=
        (singularityPseudoMetricSpace omega (θ a) (hbig a)).toUniformSpace.toTopologicalSpace
      obtain ⟨g, hg, η, ξ, hη, hξ, hηmono, hξanti, hbetween, hηlim, hξlim⟩ :=
        exists_model_sandwich_one omega (θ a) (hbig a) (fun i => ui a (f i)) (v a)
          (fun i => hmodels a (f i)) (hδ a) (fun i => hstage a (f i))
          ((hlim a).comp hf.tendsto_atTop)
      refine ⟨f ∘ g, hf.comp hg, ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact ⟨η, ξ, hη, hξ, hηmono, hξanti, hbetween, hηlim, hξlim⟩
      · let := singularityPseudoMetricSpace omega (θ b) (hbig b)
        let : TopologicalSpace (ThetaPshL1 (θ b).val) :=
          (singularityPseudoMetricSpace omega (θ b) (hbig b)).toUniformSpace.toTopologicalSpace
        obtain ⟨ηb, ξb, hηb, hξb, hηbm, hξba, hbb, hηbl, hξbl⟩ := hs b hb
        exact ⟨ηb ∘ g, ξb ∘ g, fun i => hηb (g i), fun i => hξb (g i),
          hηbm.comp hg.monotone, hξba.comp_monotone hg.monotone,
          fun i => hbb (g i), hηbl.comp hg.tendsto_atTop, hξbl.comp hg.tendsto_atTop⟩
  obtain ⟨f, hf, hs⟩ := hfinite Finset.univ
  exact ⟨f, hf, fun a => hs a (Finset.mem_univ a)⟩

end
end SGPT.Foundations.Analysis.Pending.ActualFiniteModelMixedSandwich
