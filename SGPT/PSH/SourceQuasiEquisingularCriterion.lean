import SGPT.PSH.SourceIGoodAnalyticCharacterization
import SGPT.PSH.SourceIModelGood
import SGPT.Foundations.Analysis.Pending.NativeStrictGapMultiplierInclusion
import SGPT.Foundations.Analysis.Pending.GenuineMultiplierIdealChartInclusion
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularBackgroundDomination
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularIEnvelopeNativeLimit

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter MeasureTheory
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.Pending
open SingularCanonicalSingularityDistance ThetaPshL1Topology DiagonalMass

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem enlarged_big (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) {t : ℝ} (ht : 0 < t) :
    IsBigClass (RealBottChern.ofRepresentative (θ+t • omega.form)) :=
  PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential omega θ hu ht

private def originalPotential (θ : ClosedRealOneOneForm n M)
    (u : ThetaPshL1 θ.val) : SourceThetaPotentialL1 (nativeClosedFormToAtlas θ) :=
  ⟨u.val,(isThetaPSH_iff_nativeThetaPotential _ _).mpr (by
    simpa only [sourceNativeAtlasForm_roundTrip] using u.property)⟩

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

private theorem originalPotential_tendsto_iff {I : Type*} (F : Filter I)
    (kappa : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (v : I → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val) :
    Tendsto (fun i => originalPotential θ (v i)) F
      (@nhds (SourceThetaPotentialL1 (nativeClosedFormToAtlas θ))
        (sourceSingularityTopology kappa (nativeClosedFormToAtlas θ) (by
          simpa only [sourceNativeAtlasForm_roundTrip] using hbig)) (originalPotential θ u)) ↔
    Tendsto v F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace kappa θ hbig).toUniformSpace.toTopologicalSpace u) := by
  have h := sourceSingularity_tendsto_iff_native F kappa (nativeClosedFormToAtlas θ)
    (by simpa only [sourceNativeAtlasForm_roundTrip] using hbig)
    (fun i => originalPotential θ (v i)) (originalPotential θ u)
  rcases θ with ⟨θ,hθ⟩
  cases θ
  exact h

/-- Native convergence in a fixed positive enlargement is asserted only for
an actual genuine PSH tail. The original background is not assumed big. -/
def NativeQEAEnlargedTendsto (omega kappa : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal)
    (hu : IsThetaPshPotential θ.val u) (U : ℕ → M → EReal) (t : ℝ) (ht : 0 < t) : Prop :=
  ∃ (N : ℕ) (hU : ∀ j, IsThetaPshPotential (θ+t • omega.form).val (U (j+N)))
    (hE : IsThetaPshPotential (θ+t • omega.form).val (iSingularityEnvelope θ.val u)),
    Tendsto (fun j => (⟨U (j+N),hU j⟩ : ThetaPshL1 (θ+t • omega.form).val)) atTop
      (@nhds (ThetaPshL1 (θ+t • omega.form).val)
        (singularityPseudoMetricSpace kappa (θ+t • omega.form)
          (enlarged_big omega θ hu ht)).toUniformSpace.toTopologicalSpace
        ⟨iSingularityEnvelope θ.val u,hE⟩)

/-- The literal source I-envelope and existing entire source PSH carrier,
with a separate auxiliary metric form and honest eventual membership. -/
def SourceQEAEnlargedTendsto (omega kappa : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal)
    (hu : IsThetaPshPotential θ.val u) (U : ℕ → M → EReal) (t : ℝ) (ht : 0 < t) : Prop :=
  ∃ (N : ℕ) (hU : ∀ j, IsThetaPshPotential (θ+t • omega.form).val (U (j+N)))
    (hE : IsThetaPshPotential (θ+t • omega.form).val
      (sourceIEnvelope (nativeClosedFormToAtlas θ) u)),
    Tendsto (fun j => originalPotential (θ+t • omega.form) ⟨U (j+N),hU j⟩) atTop
      (@nhds (SourceThetaPotentialL1 (nativeClosedFormToAtlas (θ+t • omega.form)))
        (sourceSingularityTopology kappa (nativeClosedFormToAtlas (θ+t • omega.form)) (by
          simpa only [sourceNativeAtlasForm_roundTrip] using enlarged_big omega θ hu ht))
        (originalPotential (θ+t • omega.form) ⟨sourceIEnvelope (nativeClosedFormToAtlas θ) u,hE⟩))

/-- Literal old I-envelope and entire PSH carriers agree through the genuine
source/native dictionaries; no background or function is substituted. -/
theorem sourceQEAEnlargedTendsto_iff_native (omega kappa : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal)
    (hu : IsThetaPshPotential θ.val u) (U : ℕ → M → EReal) (t : ℝ) (ht : 0 < t) :
    SourceQEAEnlargedTendsto omega kappa θ u hu U t ht ↔
      NativeQEAEnlargedTendsto omega kappa θ u hu U t ht := by
  have he : sourceIEnvelope (nativeClosedFormToAtlas θ) u = iSingularityEnvelope θ.val u := by
    have h := sourceIEnvelope_eq_native (nativeClosedFormToAtlas θ) u
      (originalPotential θ ⟨u,hu⟩).property
    simpa only [sourceNativeAtlasForm_roundTrip] using h
  unfold SourceQEAEnlargedTendsto NativeQEAEnlargedTendsto
  rw [he]
  constructor
  · rintro ⟨N,hU,hE,h⟩
    exact ⟨N,hU,hE,(originalPotential_tendsto_iff atTop kappa (θ+t • omega.form)
      (enlarged_big omega θ hu ht) (fun j => ⟨U (j+N),hU j⟩)
      ⟨iSingularityEnvelope θ.val u,hE⟩).mp h⟩
  · rintro ⟨N,hU,hE,h⟩
    exact ⟨N,hU,hE,(originalPotential_tendsto_iff atTop kappa (θ+t • omega.form)
      (enlarged_big omega θ hu ht) (fun j => ⟨U (j+N),hU j⟩)
      ⟨iSingularityEnvelope θ.val u,hE⟩).mpr h⟩

private theorem native_tendsto_auxiliary_iff {I : Type*} (F : Filter I)
    (kappa lambda : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (v : I → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val) :
    Tendsto v F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace kappa θ hbig).toUniformSpace.toTopologicalSpace u) ↔
    Tendsto v F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace lambda θ hbig).toUniformSpace.toTopologicalSpace u) := by
  exact (originalPotential_tendsto_iff F kappa θ hbig v u).symm.trans
    ((sourceSingularity_tendsto_auxiliary_iff F kappa lambda (nativeClosedFormToAtlas θ)
      (by simpa only [sourceNativeAtlasForm_roundTrip] using hbig)
      (fun i => originalPotential θ (v i)) (originalPotential θ u)).trans
      (originalPotential_tendsto_iff F lambda θ hbig v u))

/-- The auxiliary metric form changes neither the literal positive enlargement
nor the honest eventual source convergence predicate. -/
theorem sourceQEAEnlargedTendsto_auxiliary_iff (omega kappa lambda : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal)
    (hu : IsThetaPshPotential θ.val u) (U : ℕ → M → EReal) (t : ℝ) (ht : 0 < t) :
    SourceQEAEnlargedTendsto omega kappa θ u hu U t ht ↔
      SourceQEAEnlargedTendsto omega lambda θ u hu U t ht := by
  rw [sourceQEAEnlargedTendsto_iff_native,sourceQEAEnlargedTendsto_iff_native]
  constructor
  · rintro ⟨N,hU,hE,h⟩
    exact ⟨N,hU,hE,(native_tendsto_auxiliary_iff atTop kappa lambda (θ+t • omega.form)
      (enlarged_big omega θ hu ht) (fun j => ⟨U (j+N),hU j⟩)
      ⟨iSingularityEnvelope θ.val u,hE⟩).mp h⟩
  · rintro ⟨N,hU,hE,h⟩
    exact ⟨N,hU,hE,(native_tendsto_auxiliary_iff atTop kappa lambda (θ+t • omega.form)
      (enlarged_big omega θ hu ht) (fun j => ⟨U (j+N),hU j⟩)
      ⟨iSingularityEnvelope θ.val u,hE⟩).mpr h⟩

private theorem two_tails_tendsto_iff {A : Type*}
    (a b : ℕ → A) (L : Filter A) (m n : ℕ) (h : ∀ j, a (j+m) = b (j+n)) :
    Tendsto a atTop L ↔ Tendsto b atTop L := by
  exact (Filter.tendsto_add_atTop_iff_nat (f := a) m).symm.trans
    ((Iff.of_eq (congrArg (fun f : ℕ → A => Tendsto f atTop L) (funext h))).trans
      (Filter.tendsto_add_atTop_iff_nat (f := b) n))

/-- Every genuine admissible tail gives the same native convergence statement.
No membership of discarded early terms in the enlargement is required. -/
theorem nativeQEAEnlargedTendsto_iff_tail (omega kappa : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal)
    (hu : IsThetaPshPotential θ.val u) (U : ℕ → M → EReal) (t : ℝ) (ht : 0 < t)
    (N : ℕ) (hU : ∀ j, IsThetaPshPotential (θ+t • omega.form).val (U (j+N)))
    (hE : IsThetaPshPotential (θ+t • omega.form).val (iSingularityEnvelope θ.val u)) :
    NativeQEAEnlargedTendsto omega kappa θ u hu U t ht ↔
    Tendsto (fun j => (⟨U (j+N),hU j⟩ : ThetaPshL1 (θ+t • omega.form).val)) atTop
      (@nhds (ThetaPshL1 (θ+t • omega.form).val)
        (singularityPseudoMetricSpace kappa (θ+t • omega.form)
          (enlarged_big omega θ hu ht)).toUniformSpace.toTopologicalSpace
        ⟨iSingularityEnvelope θ.val u,hE⟩) := by
  constructor
  · rintro ⟨K,hK,hEK,h⟩
    apply (two_tails_tendsto_iff
      (fun j => (⟨U (j+K),hK j⟩ : ThetaPshL1 (θ+t • omega.form).val))
      (fun j => (⟨U (j+N),hU j⟩ : ThetaPshL1 (θ+t • omega.form).val))
      (@nhds (ThetaPshL1 (θ+t • omega.form).val)
        (singularityPseudoMetricSpace kappa (θ+t • omega.form)
          (enlarged_big omega θ hu ht)).toUniformSpace.toTopologicalSpace
        ⟨iSingularityEnvelope θ.val u,hE⟩) N K ?_).mp h
    intro j
    apply Subtype.ext
    change U (j+N+K) = U (j+K+N)
    congr 1
    omega
  · exact fun h => ⟨N,hU,hE,h⟩

/-- The original I-envelope is genuinely positive and I-good without an
original bigness assumption. -/
theorem originalIEnvelope_positive_iGood (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal)
    (hu : IsThetaPshPotential θ.val u) (hpos : HasPositivePotentialMass θ u hu) :
    let hE := iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      hu.1.hasSmoothLocalPotentials u hu
    IGoodWith θ (iSingularityEnvelope θ.val u) hE := by
  let hP := SGPT.Foundations.Analysis.Pending.singularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
    hu.1.hasSmoothLocalPotentials u hu
  let hE := iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
    hu.1.hasSmoothLocalPotentials u hu
  have hPpos : HasPositivePotentialMass θ (singularityEnvelope θ.val u) hP := by
    change 0 < diagonalPotentialMass θ _ _
    rw [singularityEnvelopeMassPreserving omega θ u hu hP]
    exact hpos
  refine ⟨hPpos.trans_le (diagonalPotentialMass_mono_of_kahler omega hP hE
    (MoreSingularOn.of_le fun x _ => singularityEnvelope_le_iSingularityEnvelope
      θ.val θ.property.1 θ.property.2 hu.1.hasSmoothLocalPotentials u hu x)), ?_⟩
  exact (singularityEnvelope_iSingularityEnvelope θ.val θ.property.1 θ.property.2
    hu.1.hasSmoothLocalPotentials u hu).trans
    (iSingularityEnvelope_idempotent θ.val θ.property.1 θ.property.2
      hu.1.hasSmoothLocalPotentials u hu).symm

/-- The literal old I-envelope and the enlarged I-envelope have actual zero
canonical distance, rather than an assumed equality of their functions. -/
theorem originalIEnvelope_enlarged_distance_zero (omega kappa : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal)
    (hu : IsThetaPshPotential θ.val u) (hpos : HasPositivePotentialMass θ u hu)
    (t : ℝ) (ht : 0 < t) :
    singularityDistance kappa (θ+t • omega.form) (enlarged_big omega θ hu ht)
      (iSingularityEnvelope θ.val u) (iSingularityEnvelope (θ+t • omega.form).val u) = 0 := by
  let γ := θ+t • omega.form
  let hE := iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
    hu.1.hasSmoothLocalPotentials u hu
  let huγ : IsThetaPshPotential γ.val u :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hu
      (KahlerDomination.isSemipositive_smul omega.isSemipositive ht.le)
  let hEγ : IsThetaPshPotential γ.val (iSingularityEnvelope θ.val u) :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hE
      (KahlerDomination.isSemipositive_smul omega.isSemipositive ht.le)
  let hIγ := iSingularityEnvelope_isThetaPshPotential γ.val γ.property.1 γ.property.2
    huγ.1.hasSmoothLocalPotentials u huγ
  have hgood := originalIEnvelope_positive_iGood omega θ u hu hpos
  have hgoodγ : IGoodWith γ (iSingularityEnvelope θ.val u) hEγ := by
    simpa only [KahlerBackground.smul_form] using
      (IGoodPositiveBackgroundIndependence.iGoodWith_iff_add_kahler
        (KahlerBackground.smul ht omega) θ hE hgood.1).mp hgood
  have hIE : iSingularityEnvelope γ.val (iSingularityEnvelope θ.val u) =
      iSingularityEnvelope γ.val u :=
    iSingularityEnvelope_eq_of_iEquivalent
      (iEquivalent_iSingularityEnvelope θ.val θ.property.1 θ.property.2
        hu.1.hasSmoothLocalPotentials u hu).symm
  have hPE : singularityEnvelope γ.val (iSingularityEnvelope θ.val u) =
      iSingularityEnvelope γ.val u := hgoodγ.2.trans hIE
  apply (SingularCanonicalDistanceZeroPEquivalence.singularityDistance_eq_zero_iff_sourcePEquivalent
    kappa γ (enlarged_big omega θ hu ht) hEγ hIγ).mpr
  have h := SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope omega γ hEγ
  rw [hPE] at h
  exact h

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem given_native_approximation (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal) (ε : ℕ → ℝ) (U : ℕ → M → EReal)
    (hε : NonnegativeDecreasesToZero ε)
    (hstage : ∀ j, IsThetaPshPotential (θ+ε j • omega.form).val (U j))
    (h : SGPT.PSH.SourceQuasiEquisingularApproximation θ u U) :
    IsQuasiEquisingularApproximation omega θ u ε U := by
  obtain ⟨κ,δ,hfull⟩ := SGPT.PSH.native_of_sourceQuasiEquisingularApproximation h
  exact ⟨h.1,hε,hstage,h.2.1,h.2.2.1,hfull.2.2.2.2.2⟩

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem genuine_enlarged_tail (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (ε : ℕ → ℝ) (U : ℕ → M → EReal)
    (hε : NonnegativeDecreasesToZero ε)
    (hstage : ∀ j, IsThetaPshPotential (θ+ε j • omega.form).val (U j))
    (t : ℝ) (ht : 0 < t) :
    ∃ N : ℕ, ∀ j, IsThetaPshPotential (θ+t • omega.form).val (U (j+N)) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hε.2.2.eventually (gt_mem_nhds ht))
  refine ⟨N,fun j => ?_⟩
  have hsemi := KahlerDomination.isSemipositive_smul omega.isSemipositive
    (sub_nonneg.mpr (hN (j+N) (Nat.le_add_left N j)).le)
  have hform : θ+ε (j+N) • omega.form+(t-ε (j+N)) • omega.form =
      θ+t • omega.form := by module
  simpa only [hform] using
    LocalPotentials.isThetaPshPotential_add_of_semipositive (hstage (j+N)) hsemi

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem shifted_approximation (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal) (ε : ℕ → ℝ) (U : ℕ → M → EReal)
    (h : IsQuasiEquisingularApproximation omega θ u ε U) (N : ℕ) :
    IsQuasiEquisingularApproximation omega θ u (fun j => ε (j+N)) (fun j => U (j+N)) := by
  refine ⟨h.target,⟨fun j => h.error.1 _,fun i j hij => h.error.2.1 (Nat.add_le_add_right hij N),
    h.error.2.2.comp (Filter.tendsto_add_atTop_nat N)⟩,
    fun j => h.term _,fun j => h.term_hasAnalyticSingularityType _,
    ⟨fun x i j hij => h.term_antitone x (Nat.add_le_add_right hij N),
      fun x => (h.term_tendsto x).comp (Filter.tendsto_add_atTop_nat N)⟩,?_⟩
  intro c d hc hcd
  exact (Filter.tendsto_add_atTop_nat N).eventually (h.eventually_multiplierIdealIncluded hc hcd)

private theorem pseudometric_target_transfer {A : Type*} [PseudoMetricSpace A]
    (v : ℕ → A) (a b : A) (hab : dist a b = 0)
    (h : Tendsto v atTop (𝓝 b)) : Tendsto v atTop (𝓝 a) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) (fun j => ?_)
    (tendsto_iff_dist_tendsto_zero.mp h)
  simpa only [dist_comm b a,hab,add_zero] using dist_triangle (v j) b a

/-- Any actual source QEA, using the prescribed errors and stages, converges
on a genuine tail in every positive enlargement to the original I-envelope. -/
theorem sourceQuasiEquisingular_enlarged_tendsto (omega kappa : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal) (ε : ℕ → ℝ) (U : ℕ → M → EReal)
    (hu : IsThetaPshPotential θ.val u) (hpos : HasPositivePotentialMass θ u hu)
    (hε : NonnegativeDecreasesToZero ε)
    (hstage : ∀ j, IsThetaPshPotential (θ+ε j • omega.form).val (U j))
    (h : SGPT.PSH.SourceQuasiEquisingularApproximation θ u U) (t : ℝ) (ht : 0 < t) :
    SourceQEAEnlargedTendsto omega kappa θ u hu U t ht := by
  let γ := θ+t • omega.form
  let hbig := enlarged_big omega θ hu ht
  let huγ : IsThetaPshPotential γ.val u :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hu
      (KahlerDomination.isSemipositive_smul omega.isSemipositive ht.le)
  let hE := iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
    hu.1.hasSmoothLocalPotentials u hu
  let hEγ : IsThetaPshPotential γ.val (iSingularityEnvelope θ.val u) :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hE
      (KahlerDomination.isSemipositive_smul omega.isSemipositive ht.le)
  obtain ⟨N,hU⟩ := genuine_enlarged_tail omega θ ε U hε hstage t ht
  have hfull := shifted_approximation omega θ u ε U
    (given_native_approximation omega θ u ε U hε hstage h) N
  have hsemi : (γ-θ).val.IsSemipositive := by
    have he : γ-θ=t • omega.form := by dsimp only [γ]; module
    rw [he]
    exact KahlerDomination.isSemipositive_smul omega.isSemipositive ht.le
  have hγ := QuasiEquisingularBackgroundDomination.isQuasiEquisingularApproximation_of_background_domination
    hfull hsemi
  obtain ⟨_,hI,_,hlim⟩ :=
    QuasiEquisingularIEnvelopeNativeLimit.iInf_envelopes_eq_iEnvelope_and_native_limit
      omega γ hbig hγ hU
      (SingularPositiveCommonBackgroundExistence.hasPositivePotentialMass_add_smul omega hu ht)
  have hlimκ := (native_tendsto_auxiliary_iff atTop omega kappa γ hbig
    (fun j => ⟨U (j+N),hU j⟩) ⟨iSingularityEnvelope γ.val u,hI⟩).mp hlim
  have hzero := originalIEnvelope_enlarged_distance_zero omega kappa θ u hu hpos t ht
  have hdist : @dist (ThetaPshL1 γ.val) (singularityPseudoMetricSpace kappa γ hbig).toDist
      ⟨iSingularityEnvelope θ.val u,hEγ⟩ ⟨iSingularityEnvelope γ.val u,hI⟩ = 0 := by
    exact (dist_eq_singularityDistance_toReal kappa γ hbig
      ⟨iSingularityEnvelope θ.val u,hEγ⟩ ⟨iSingularityEnvelope γ.val u,hI⟩).trans
      (by rw [hzero,EReal.toReal_zero])
  apply (sourceQEAEnlargedTendsto_iff_native omega kappa θ u hu U t ht).mpr
  exact ⟨N,hU,hEγ,@pseudometric_target_transfer (ThetaPshL1 γ.val)
    (singularityPseudoMetricSpace kappa γ hbig) (fun j => ⟨U (j+N),hU j⟩)
    ⟨iSingularityEnvelope θ.val u,hEγ⟩ ⟨iSingularityEnvelope γ.val u,hI⟩ hdist hlimκ⟩

/-- Convergence in even one positive enlargement forces the actual original
all-chart multiplier inclusions for the given approximation sequence. -/
theorem sourceQuasiEquisingular_of_enlarged_tendsto (omega kappa : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal) (ε : ℕ → ℝ) (U : ℕ → M → EReal)
    (hu : IsThetaPshPotential θ.val u)
    (hε : NonnegativeDecreasesToZero ε)
    (hstage : ∀ j, IsThetaPshPotential (θ+ε j • omega.form).val (U j))
    (ha : ∀ j, HasManifoldAnalyticSingularityType (n := n) (U j))
    (hanti : ∀ x, Antitone fun j => U j x) (hinf : ∀ x, (⨅ j, U j x) = u x)
    (t : ℝ) (ht : 0 < t) (h : SourceQEAEnlargedTendsto omega kappa θ u hu U t ht) :
    SGPT.PSH.SourceQuasiEquisingularApproximation θ u U := by
  obtain ⟨N,hU,hE,hlim⟩ := (sourceQEAEnlargedTendsto_iff_native omega kappa θ u hu U t ht).mp h
  apply SGPT.PSH.sourceQuasiEquisingularApproximation_of_native
    (ω := omega) (ε := ε)
  refine ⟨hu,hε,hstage,ha,⟨hanti,fun x => ?_⟩,?_⟩
  · simpa only [hinf x] using tendsto_atTop_iInf (hanti x)
  · intro c d hc hcd
    have hpreferred := NativeStrictGapMultiplierInclusion.eventually_multiplierIdeal_le_of_native_limit
      kappa (θ+t • omega.form) (enlarged_big omega θ hu ht) atTop
      (fun j => (⟨U (j+N),hU j⟩ : ThetaPshL1 (θ+t • omega.form).val))
      ⟨iSingularityEnvelope θ.val u,hE⟩ hc hcd hlim
    have hEu := PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_iOrderOnManifold
      (iEquivalent_iSingularityEnvelope θ.val θ.property.1 θ.property.2
        hu.1.hasSmoothLocalPotentials u hu).2 hc
    have htail : ∀ᶠ j in atTop, MultiplierIdealIncluded (n := n) (U (j+N)) d u c := by
      filter_upwards [hpreferred] with j hj
      exact GenuineMultiplierIdealChartInclusion.multiplierIdealIncluded_of_multiplierIdeal_le
        (hU j).1 hu.1 (hc.trans hcd) hc (fun x g hg => hEu x g (hj x g hg))
    obtain ⟨K,hK⟩ := eventually_atTop.mp htail
    apply eventually_atTop.mpr
    refine ⟨K+N,fun j hj => ?_⟩
    have hle : K ≤ j-N := by omega
    have he : j-N+N=j := by omega
    simpa only [he] using hK (j-N) hle

/-- The entire original criterion, including every positive fixed enlargement
and the genuine eventual-carrier interpretation of its footnote. -/
theorem sourceQuasiEquisingular_criterion (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal) (ε : ℕ → ℝ) (U : ℕ → M → EReal)
    (hu : IsThetaPshPotential θ.val u) (hpos : HasPositivePotentialMass θ u hu)
    (hε : NonnegativeDecreasesToZero ε)
    (hstage : ∀ j, IsThetaPshPotential (θ+ε j • omega.form).val (U j))
    (ha : ∀ j, HasManifoldAnalyticSingularityType (n := n) (U j))
    (hanti : ∀ x, Antitone fun j => U j x) (hinf : ∀ x, (⨅ j, U j x) = u x) :
    (SGPT.PSH.SourceQuasiEquisingularApproximation θ u U ↔
      ∀ (t : ℝ) (ht : 0 < t) (kappa : KahlerBackground n M),
        SourceQEAEnlargedTendsto omega kappa θ u hu U t ht) ∧
    (SGPT.PSH.SourceQuasiEquisingularApproximation θ u U ↔
      ∃ (t : ℝ) (ht : 0 < t) (kappa : KahlerBackground n M),
        SourceQEAEnlargedTendsto omega kappa θ u hu U t ht) ∧
    (SGPT.PSH.SourceQuasiEquisingularApproximation θ u U ↔
      ∀ (t : ℝ) (ht : 0 < t) (kappa : KahlerBackground n M),
        NativeQEAEnlargedTendsto omega kappa θ u hu U t ht) := by
  have hforward := sourceQuasiEquisingular_enlarged_tendsto omega
  have hreverse := sourceQuasiEquisingular_of_enlarged_tendsto omega
  have hall : SGPT.PSH.SourceQuasiEquisingularApproximation θ u U ↔
      ∀ (t : ℝ) (ht : 0 < t) (kappa : KahlerBackground n M),
        SourceQEAEnlargedTendsto omega kappa θ u hu U t ht := by
    constructor
    · intro h t ht kappa
      exact hforward kappa θ u ε U hu hpos hε hstage h t ht
    · intro h
      exact hreverse omega θ u ε U hu hε hstage ha hanti hinf 1 zero_lt_one
        (h 1 zero_lt_one omega)
  refine ⟨hall,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro h
    exact ⟨1,zero_lt_one,omega,hall.mp h 1 zero_lt_one omega⟩
  · rintro ⟨t,ht,kappa,h⟩
    exact hreverse kappa θ u ε U hu hε hstage ha hanti hinf t ht h
  · intro h t ht kappa
    exact (sourceQEAEnlargedTendsto_iff_native omega kappa θ u hu U t ht).mp
      (hall.mp h t ht kappa)
  · intro h
    apply hall.mpr
    intro t ht kappa
    exact (sourceQEAEnlargedTendsto_iff_native omega kappa θ u hu U t ht).mpr
      (h t ht kappa)

end SGPT.PSH.VariableComplexAtlas
