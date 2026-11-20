import SGPT.Foundations.Analysis.Pending.NativeModelStrictMultiplierSubsequence
import SGPT.Foundations.Analysis.Pending.SingularNativeBackgroundAddition
import SGPT.Foundations.Analysis.Pending.SingularPositiveCommonBackgroundExistence
import Mathlib.Topology.Sequences
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

set_option autoImplicit false

/-! # Actual native convergence produces every strict-gap multiplier inclusion -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.NativeStrictGapMultiplierInclusion
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.PositiveClasses
  FirstPass.NonKahlerLocus FirstPass.IEnvelope ThetaPshL1Topology DiagonalMass MixedMass
  SingularCanonicalSingularityDistance SingularCanonicalSingularityMassLipschitz
  SingularGlobalPEnvelopeBridge SingularCanonicalDistanceZeroPEquivalence

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

private theorem eventually_multiplierIdeal_le_sequence_of_positive_mass
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (ui : ℕ → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val)
    (hpos : HasPositivePotentialMass θ u.val u.property)
    {p q : ℝ} (hp : 0 < p) (hpq : p < q)
    (hlim : Tendsto ui atTop (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace u)) :
    ∀ᶠ j in atTop, (multiplierIdeal (n := n) q (ui j).val).Le
      (multiplierIdeal (n := n) p u.val) := by
  classical
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  by_contra hnot
  have hfreq : ∃ᶠ j in atTop, ¬ (multiplierIdeal (n := n) q (ui j).val).Le
      (multiplierIdeal (n := n) p u.val) := by
    simpa only [Filter.Frequently, not_not] using hnot
  obtain ⟨ns, hvlim, hbad⟩ := Filter.subseq_forall_of_frequently
    (p := fun z : ThetaPshL1 θ.val => ¬ (multiplierIdeal (n := n) q z.val).Le
      (multiplierIdeal (n := n) p u.val)) hlim hfreq
  let v : ℕ → ThetaPshL1 θ.val := fun j => ui (ns j)
  let L : ℝ≥0∞ := diagonalPotentialMass θ u.val u.property
  have hLtop : L ≠ ⊤ := (globalMixedMass_lt_top omega
    (fun _ : Fin n => u.property.1)).ne
  have hLpos : 0 < L.toReal := ENNReal.toReal_pos hpos.ne' hLtop
  let δ : ℝ := L.toReal / 2
  have hδ : 0 < δ := half_pos hLpos
  have hδlt : δ < L.toReal := half_lt_self hLpos
  have hmass : Tendsto (fun j => (diagonalPotentialMass θ (v j).val
      (v j).property).toReal) atTop (𝓝 L.toReal) :=
    ((diagonalPotentialMass_uniformContinuous omega θ hbig).continuous.tendsto u).comp hvlim
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.mp hmass).1 δ hδlt)
  have hstage (j : ℕ) : ENNReal.ofReal δ ≤
      diagonalPotentialMass θ (v (j + N)).val (v (j + N)).property :=
    (ENNReal.ofReal_le_iff_le_toReal
      (globalMixedMass_lt_top omega (fun _ : Fin n => (v (j + N)).property.1)).ne).mpr
        (hN (j + N) (Nat.le_add_left N j)).le
  have hmodel (j : ℕ) : IsModelPotential θ
      (singularityEnvelope θ.val (v (j + N)).val) := by
    have hjpos : HasPositivePotentialMass θ (v (j + N)).val (v (j + N)).property :=
      (ENNReal.ofReal_pos.mpr hδ).trans_le (hstage j)
    have hP := singularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      (v (j + N)).property.1.hasSmoothLocalPotentials (v (j + N)).val (v (j + N)).property
    exact ⟨hP, (RooftopEnvelopeIdempotence.singularityEnvelope_idempotent_of_positive_mass
      omega θ (v (j + N)).val (v (j + N)).property hjpos).symm,
      (singularityEnvelopeMassPreserving omega θ (v (j + N)).val
        (v (j + N)).property hP).symm ▸ hjpos⟩
  let w : ℕ → ThetaPshL1 θ.val := fun j =>
    ⟨singularityEnvelope θ.val (v (j + N)).val, (hmodel j).plurisubharmonic⟩
  have hwstage (j : ℕ) : ENNReal.ofReal δ ≤
      diagonalPotentialMass θ (w j).val (w j).property :=
    (hstage j).trans_eq (singularityEnvelopeMassPreserving omega θ
      (v (j + N)).val (v (j + N)).property (w j).property).symm
  have htail : Tendsto (fun j => v (j + N)) atTop (𝓝 u) :=
    hvlim.comp (tendsto_add_atTop_nat N)
  have hzero (j : ℕ) : dist (w j) (v (j + N)) = 0 := by
    have he := sourcePEquivalent_singularityEnvelope omega θ (v (j + N)).property
    have hz := (singularityDistance_eq_zero_iff_sourcePEquivalent omega θ hbig
      (w j).property (v (j + N)).property).mpr ⟨he.2, he.1⟩
    rw [dist_eq_singularityDistance_toReal omega θ hbig, hz, EReal.toReal_zero]
  have hwlim : Tendsto w atTop (𝓝 u) := tendsto_iff_dist_tendsto_zero.mpr (by
    have hd := tendsto_iff_dist_tendsto_zero.mp htail
    apply squeeze_zero (fun _ => dist_nonneg) (fun j => ?_) hd
    simpa only [hzero, zero_add] using dist_triangle (w j) (v (j + N)) u)
  have hsource (j : ℕ) : (multiplierIdeal (n := n) q (v (j + N)).val).Le
      (multiplierIdeal (n := n) q (w j).val) :=
    PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_iOrderOnManifold
      (GlobalPMultiplierOrder.iEquivalentOnManifold_of_sourcePEquivalent
        (sourcePEquivalent_singularityEnvelope omega θ (v (j + N)).property)).1
        (hp.trans hpq)
  obtain ⟨f, _, hinclude⟩ :=
    NativeModelStrictMultiplierSubsequence.exists_strictMono_eventually_multiplierIdeal_le
      omega θ hbig w u hmodel hδ hwstage hpos hp hpq hwlim
  obtain ⟨j, hj⟩ := hinclude.exists
  apply hbad (f j + N)
  intro x g hg
  exact hj x g (hsource (f j) x g hg)

/-- Actual native convergence supplies every strict real multiplier gap,
with zero original mass allowed and arbitrary input filter. -/
theorem eventually_multiplierIdeal_le_of_native_limit
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} (F : Filter I) (ui : I → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val)
    {p q : ℝ} (hp : 0 < p) (hpq : p < q)
    (hlim : Tendsto ui F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace u)) :
    ∀ᶠ i in F, (multiplierIdeal (n := n) q (ui i).val).Le
      (multiplierIdeal (n := n) p u.val) := by
  let γ : ClosedRealOneOneForm n M := θ + omega.form
  have hγ : IsBigClass (RealBottChern.ofRepresentative γ) := by
    simpa only [one_smul] using PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential
      omega θ u.property zero_lt_one
  let U : ThetaPshL1 γ.val := ⟨u.val,
    LocalPotentials.isThetaPshPotential_add_of_semipositive u.property omega.isSemipositive⟩
  let Ui : I → ThetaPshL1 γ.val := fun i => ⟨(ui i).val,
    LocalPotentials.isThetaPshPotential_add_of_semipositive (ui i).property omega.isSemipositive⟩
  have hUpos : HasPositivePotentialMass γ U.val U.property := by
    simpa only [one_smul] using SingularPositiveCommonBackgroundExistence.hasPositivePotentialMass_add_smul
      omega u.property zero_lt_one
  let := singularityPseudoMetricSpace omega γ hγ
  let : TopologicalSpace (ThetaPshL1 γ.val) :=
    (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace
  have hUlim : Tendsto Ui F (𝓝 U) :=
    SingularNativeBackgroundAddition.tendsto_native_add_kahler omega θ hbig F ui u hlim
  have hnhds : ∀ᶠ v : ThetaPshL1 γ.val in 𝓝 U,
      (multiplierIdeal (n := n) q v.val).Le (multiplierIdeal (n := n) p U.val) := by
    apply Filter.eventually_iff_seq_eventually.mpr
    intro vi hvi
    exact eventually_multiplierIdeal_le_sequence_of_positive_mass omega γ hγ vi U hUpos hp hpq hvi
  exact hUlim.eventually hnhds

end
end SGPT.Foundations.Analysis.Pending.NativeStrictGapMultiplierInclusion
