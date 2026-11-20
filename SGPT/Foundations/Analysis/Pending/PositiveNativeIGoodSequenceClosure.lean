import SGPT.Foundations.Analysis.Pending.IModelRooftopLowerSeed
import SGPT.Foundations.Analysis.Pending.IEnvelopeIncreasingRegularizedSupremum
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityModelSandwich
import SGPT.Foundations.Analysis.Pending.IGoodGlobalPStability
import SGPT.Foundations.Analysis.Pending.AnalyticPotentialsIGood

set_option autoImplicit false

/-! # Actual original-background I-good closure at positive native sequence limits -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.PositiveNativeIGoodSequenceClosure

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.IEnvelope
  FirstPass.QuasiEquisingularApproximation
  DiagonalMass MixedMass ThetaPshL1Topology SingularCanonicalSingularityDistance
  SingularGlobalPEnvelopeBridge SingularCanonicalDistanceZeroPEquivalence
  SingularCanonicalSingularityModelSandwich SingularCanonicalSingularityMassLipschitz
  SingularCanonicalSingularityIncreasing IModelRooftopLowerSeed
  IEnvelopeIncreasingRegularizedSupremum IncreasingMixedDirectedNets
  IGoodGlobalPStability AnalyticPotentialsIGood

noncomputable section


variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

private theorem iGoodWith_of_uniform_positive_iModel_sequence
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (v : ℕ → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val)
    (hmodel : ∀ j, IsModelPotential θ (v j).val)
    (hI : ∀ j, IsIModelPotential θ.val (v j).val) {δ : ℝ} (hδ : 0 < δ)
    (hstage : ∀ j, ENNReal.ofReal δ ≤ diagonalPotentialMass θ (v j).val (v j).property)
    (hlim : Tendsto v atTop (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace u)) :
    IGoodWith θ u.val u.property := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  obtain ⟨f, _hf, η, _ψ, hηeq, _hψeq, hηmodel, hηmono, _hψanti,
      hbetween, hηlim, _hψlim⟩ :=
    exists_strictMono_monotone_sandwich_of_tendsto omega θ hbig v u hmodel hδ hstage hlim
  have hηI (i : ℕ) : IsIModelPotential θ.val (η i).val := by
    have hbelow (j : ℕ) : (η i).val ≤ (v (f (i + j))).val :=
      (hηmono (Nat.le_add_right i j)).trans (hbetween (i + j)).1
    rw [hηeq i]
    exact isIModelPotential_iInf_finiteTailRooftop_of_common_lower θ
      (fun j => hI (f j)) (η i).property i hbelow
  have hη0 (i : ℕ) (x : M) : (η i).val x ≤ 0 := by
    rw [(hηI i).envelope_eq]
    exact iSingularityEnvelope_le_zero θ.val (η i).val x
  have hS : IsThetaPshPotential θ.val (uscRegularization (⨆ i, (η i).val)) :=
    isThetaPshPotential_regularized_of_uniformlyBounded (fun i => (η i).property) hη0
  let S : ThetaPshL1 θ.val := ⟨uscRegularization (⨆ i, (η i).val), hS⟩
  have hηS : (η 0).val ≤ S.val :=
    (le_iSup (fun i => (η i).val) 0).trans (le_uscRegularization _)
  have hSpos : HasPositivePotentialMass θ S.val S.property :=
    (hηmodel 0).positive_mass.trans_le (diagonalPotentialMass_mono_of_kahler
      omega (η 0).property S.property (MoreSingularOn.of_le fun x _ => hηS x))
  have hfixed : S.val = iSingularityEnvelope θ.val S.val := by
    have he := iSingularityEnvelope_regularized_iSup_eq omega θ hbig
      (fun i => (η i).property) hηmono S.property rfl hSpos
    have hfamily : (fun i => iSingularityEnvelope θ.val (η i).val) =
        (fun i => (η i).val) := funext fun i => (hηI i).envelope_eq.symm
    rw [hfamily] at he
    exact he
  have hSgood : IGoodWith θ S.val S.property := by
    refine ⟨hSpos, ?_⟩
    have he := singularityEnvelope_iSingularityEnvelope θ.val θ.property.1 θ.property.2
      S.property.1.hasSmoothLocalPotentials S.val S.property
    rw [← hfixed] at he
    exact he.trans hfixed
  have hηSlim : Tendsto η atTop (𝓝 S) :=
    tendsto_native_of_monotone_uniformlyBounded omega θ hbig η hηmono hη0
  have hzero : dist S u = 0 := by
    have hh := hηSlim.dist hηlim
    simp only [dist_self] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  exact iGoodWith_of_native_dist_eq_zero omega θ hbig S u hSgood hzero


/-- Native mass continuity internally selects the common positive tail;
the actual I-model sandwich then produces original-background I-goodness. -/
theorem iGoodWith_of_native_sequence_positive_limit
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (v : ℕ → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val)
    (hpos : HasPositivePotentialMass θ u.val u.property)
    (hgood : ∀ᶠ j in atTop, IGoodWith θ (v j).val (v j).property)
    (hlim : Tendsto v atTop (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace u)) :
    IGoodWith θ u.val u.property := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  let L : ℝ := (diagonalPotentialMass θ u.val u.property).toReal
  have hL : 0 < L := ENNReal.toReal_pos hpos.ne'
    (globalMixedMass_lt_top omega (fun _ : Fin n => u.property.1)).ne
  let δ : ℝ := L / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδL : δ < L := by dsimp [δ]; linarith
  have hmass : Tendsto (fun j => (diagonalPotentialMass θ (v j).val (v j).property).toReal)
      atTop (𝓝 L) :=
    ((diagonalPotentialMass_uniformContinuous omega θ hbig).continuous.tendsto u).comp hlim
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hgood.and (hmass.eventually (lt_mem_nhds hδL)))
  have hG (j : ℕ) : IGoodWith θ (v (j + J)).val (v (j + J)).property :=
    (hJ (j + J) (by omega)).1
  have hP (j : ℕ) : IsThetaPshPotential θ.val
      (singularityEnvelope θ.val (v (j + J)).val) :=
    singularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      (v (j + J)).property.1.hasSmoothLocalPotentials (v (j + J)).val (v (j + J)).property
  let P : ℕ → ThetaPshL1 θ.val := fun j =>
    ⟨singularityEnvelope θ.val (v (j + J)).val, hP j⟩
  have hPmass (j : ℕ) : diagonalPotentialMass θ (P j).val (P j).property =
      diagonalPotentialMass θ (v (j + J)).val (v (j + J)).property :=
    singularityEnvelopeMassPreserving omega θ (v (j + J)).val (v (j + J)).property (hP j)
  have hPmodel (j : ℕ) : IsModelPotential θ (P j).val := by
    refine ⟨(P j).property, ?_, (hPmass j).symm ▸ (hG j).positiveMass⟩
    have he := singularityEnvelope_iSingularityEnvelope θ.val θ.property.1 θ.property.2
      (v (j + J)).property.1.hasSmoothLocalPotentials (v (j + J)).val (v (j + J)).property
    rw [← (hG j).envelope_eq] at he
    exact he.symm
  have hPI (j : ℕ) : IsIModelPotential θ.val (P j).val := by
    change IsIModelPotential θ.val (singularityEnvelope θ.val (v (j + J)).val)
    rw [(hG j).envelope_eq]
    exact iSingularityEnvelope_isIModelPotential θ.val θ.property.1 θ.property.2
      (v (j + J)).property.1.hasSmoothLocalPotentials (v (j + J)).val (v (j + J)).property
  have hstage (j : ℕ) : ENNReal.ofReal δ ≤ diagonalPotentialMass θ (P j).val (P j).property :=
    (ENNReal.ofReal_le_of_le_toReal (hJ (j + J) (by omega)).2.le).trans_eq (hPmass j).symm
  have htail : Tendsto (fun j => v (j + J)) atTop (𝓝 u) :=
    hlim.comp (tendsto_add_atTop_nat J)
  have hzero (j : ℕ) : dist (P j) (v (j + J)) = 0 := by
    have he := sourcePEquivalent_singularityEnvelope omega θ (v (j + J)).property
    have hz := (singularityDistance_eq_zero_iff_sourcePEquivalent omega θ hbig
      (P j).property (v (j + J)).property).mpr ⟨he.2, he.1⟩
    rw [dist_eq_singularityDistance_toReal omega θ hbig, hz, EReal.toReal_zero]
  have hPlim : Tendsto P atTop (𝓝 u) := tendsto_iff_dist_tendsto_zero.mpr (by
    have hd := tendsto_iff_dist_tendsto_zero.mp htail
    apply squeeze_zero (fun _ => dist_nonneg) (fun j => ?_) hd
    have hh := dist_triangle (P j) (v (j + J)) u
    simpa only [hzero j, zero_add] using hh)
  exact iGoodWith_of_uniform_positive_iModel_sequence omega θ hbig P u hPmodel hPI hδ hstage hPlim

/-- True native mass continuity makes late analytic stages positive;
the genuine sequence closure supplies I-goodness of the original positive limit. -/
theorem iGoodWith_of_analytic_native_sequence_positive_limit
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (v : ℕ → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val)
    (hpos : HasPositivePotentialMass θ u.val u.property)
    (hA : ∀ j, HasManifoldAnalyticSingularityType (n := n) (v j).val)
    (hlim : Tendsto v atTop (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace u)) :
    IGoodWith θ u.val u.property := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  have hmpos : 0 < (diagonalPotentialMass θ u.val u.property).toReal :=
    ENNReal.toReal_pos hpos.ne' (globalMixedMass_lt_top omega (fun _ : Fin n => u.property.1)).ne
  have hmass :=
    ((diagonalPotentialMass_uniformContinuous omega θ hbig).continuous.tendsto u).comp hlim
  have hgood : ∀ᶠ j in atTop, IGoodWith θ (v j).val (v j).property :=
    (hmass.eventually (lt_mem_nhds hmpos)).mono fun j hj =>
      iGoodWith_of_analytic_type_of_positive_mass omega (v j).property (hA j)
        (ENNReal.toReal_pos_iff.mp hj).1
  exact iGoodWith_of_native_sequence_positive_limit omega θ hbig v u hpos hgood hlim

end

end SGPT.Foundations.Analysis.Pending.PositiveNativeIGoodSequenceClosure
