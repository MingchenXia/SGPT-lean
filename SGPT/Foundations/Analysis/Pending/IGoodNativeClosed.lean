import SGPT.Foundations.Analysis.Pending.IGoodPositiveBackgroundIndependence
import Mathlib.Topology.Sequences

set_option autoImplicit false

/-! # Genuine native closedness of the actual background-existential I-good locus -/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.IGoodNativeClosed

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.IEnvelope
  DiagonalMass ThetaPshL1Topology SingularCanonicalSingularityDistance
  IGoodPositiveBackgroundIndependence PositiveNativeIGoodSequenceClosure
  SingularNativeBackgroundIndependence SingularPositiveCommonBackgroundExistence

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- The actual global I-good set is closed in the original native topology;
the original masses of its members and limits are allowed to vanish. -/
theorem isClosed_iGood_native
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    @IsClosed (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
      {v | IGood (n := n) v.val} := by
  let native := singularityPseudoMetricSpace omega θ hbig
  let : PseudoMetricSpace (ThetaPshL1 θ.val) := native
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    native.toUniformSpace.toTopologicalSpace
  have hseq : @IsSeqClosed (ThetaPshL1 θ.val)
      native.toUniformSpace.toTopologicalSpace {v | IGood (n := n) v.val} := by
    intro a u hgood hlim
    let γ := θ + omega.form
    have hγ : IsBigClass (RealBottChern.ofRepresentative γ) := by
      simpa only [one_smul] using
        PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential
          omega θ u.property zero_lt_one
    let A : ℕ → ThetaPshL1 γ.val := fun j =>
      ⟨(a j).val, LocalPotentials.isThetaPshPotential_add_of_semipositive
        (a j).property omega.isSemipositive⟩
    let U : ThetaPshL1 γ.val :=
      ⟨u.val, LocalPotentials.isThetaPshPotential_add_of_semipositive
        u.property omega.isSemipositive⟩
    have hUpos : HasPositivePotentialMass γ U.val U.property := by
      simpa only [one_smul] using
        hasPositivePotentialMass_add_smul omega u.property zero_lt_one
    have hAGood (j : ℕ) : IGoodWith γ (A j).val (A j).property := by
      obtain ⟨σ, hσ, hI⟩ := hgood j
      have hApos : HasPositivePotentialMass γ (A j).val (A j).property := by
        simpa only [one_smul] using
          hasPositivePotentialMass_add_smul omega (a j).property zero_lt_one
      exact (iGoodWith_iff_positive_common_potential omega σ γ hσ (A j).property
        hI.positiveMass hApos).mp hI
    have hlimA : Tendsto A atTop (@nhds (ThetaPshL1 γ.val)
        (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace U) :=
      (tendsto_native_iff_add_kahler omega θ hbig atTop a u).mp hlim
    have hUgood : IGoodWith γ U.val U.property :=
      iGoodWith_of_native_sequence_positive_limit omega γ hγ A U hUpos
        (Eventually.of_forall hAGood) hlimA
    exact hUgood.iGood
  exact (@isSeqClosed_iff_isClosed (ThetaPshL1 θ.val)
    native.toUniformSpace.toTopologicalSpace inferInstance
    {v | IGood (n := n) v.val}).mp hseq

/-- Every nontrivial-filter native limit of eventual global I-good stages
is globally I-good; no original positive-mass or cofinal-sequence input. -/
theorem iGood_of_native_filter_limit
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} (F : Filter I) [NeBot F]
    (v : I → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val)
    (hgood : ∀ᶠ i in F, IGood (n := n) (v i).val)
    (hlim : Tendsto v F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace u)) :
    IGood (n := n) u.val := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  exact (isClosed_iGood_native omega θ hbig).mem_of_tendsto hlim hgood

end

end SGPT.Foundations.Analysis.Pending.IGoodNativeClosed
