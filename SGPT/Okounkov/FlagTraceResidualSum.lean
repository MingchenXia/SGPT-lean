import SGPT.Okounkov.FlagCurrentResidualTrace
import SGPT.Okounkov.SourceTraceModification
import SGPT.Okounkov.EffectiveDivisorTrace
import SGPT.Foundations.Analysis.Pending.TraceRepresentativeAddition
import SGPT.Foundations.Analysis.Pending.TracePositiveRealHomogeneity
import SGPT.Foundations.Analysis.Pending.ActualMultiplierOrderAddition
import SGPT.Foundations.Analysis.Pending.ActualIEnvelopePositiveScaling

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending ThetaPshCodimTwoExtension
open SourceTraceRepresentativeDefinition NaturalSubmanifoldSourceTraceDefinition

/-- The existing positive scalar ideal-order producer transports both directions;
the zero branch retains all original extended-real poles. -/
theorem iEquivalentOnManifold_nonneg_smul {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    {u v : M → EReal} (hI : IEquivalentOnManifold (n := n) u v) (c : ℝ≥0) :
    IEquivalentOnManifold (n := n)
      (fun x => ((c : ℝ) : EReal) * u x) (fun x => ((c : ℝ) : EReal) * v x) := by
  by_cases hc : c = 0
  · subst c
    simpa only [NNReal.coe_zero, EReal.coe_zero, zero_mul] using
      IEquivalentOnManifold.refl (n := n) (fun _ : M => (0 : EReal))
  · have hcR : 0 < (c : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc)
    exact ⟨ActualIEnvelopePositiveScaling.iOrderOnManifold_smul hI.1 hcR,
      ActualIEnvelopePositiveScaling.iOrderOnManifold_smul hI.2 hcR⟩

/-- Genuine native trace addition and actual all-background trace comparison
identify every recorded source sum trace, including zero-dimensional targets. -/
theorem iEquivalent_sourceTrace_add {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    {u v : F.carrier → EReal} {τu τv τs : F.tail.carrier → EReal}
    (hTu : IsNaturalSourceTraceRepresentative F.omega F.firstDivisor u τu)
    (hTv : IsNaturalSourceTraceRepresentative F.omega F.firstDivisor v τv)
    (hTs : IsNaturalSourceTraceRepresentative F.omega F.firstDivisor
      (fun x => u x + v x) τs) :
    IEquivalentOnManifold (n := m) τs (fun y => τu y + τv y) := by
  let Z := F.flag (1 : Fin (m + 2))
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) F.firstDivisor.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
    (Nat.le_succ m) F.firstDivisor.2.2
  let : CompactSpace Z := F.tail.compact
  let : ConnectedSpace Z := F.tail.connected
  let : MeasurableSpace Z := borel Z
  let : BorelSpace Z := ⟨rfl⟩
  let : MeasurableSpace F.tail.carrier := borel F.tail.carrier
  let : BorelSpace F.tail.carrier := ⟨rfl⟩
  let hι := SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ m) F.firstDivisor.2.2
  change IsSourceTraceRepresentativeAlong F.omega F.tail.omega hι u τu at hTu
  change IsSourceTraceRepresentativeAlong F.omega F.tail.omega hι v τv at hTv
  change IsSourceTraceRepresentativeAlong F.omega F.tail.omega hι _ τs at hTs
  have hnativeu := (isSourceTraceRepresentativeAlong_iff_native
    (Nat.succ_ne_zero m) F.omega F.tail.omega hι _ _).mp hTu
  have hnativev := (isSourceTraceRepresentativeAlong_iff_native
    (Nat.succ_ne_zero m) F.omega F.tail.omega hι _ _).mp hTv
  obtain ⟨omegaSum, hnativeSum⟩ := TraceRepresentativeAddition.isTraceRepresentativeAlong_add
    F.tail.omega F.tail.omega F.tail.omega hι hnativeu hnativev
      ((nativeGeneric_zero_iff_source (Nat.succ_ne_zero m)
        (Subtype.val : Z → F.carrier) _).mpr hTs.1)
  have hsourceSum := (isSourceTraceRepresentativeAlong_iff_native
    (Nat.succ_ne_zero m) omegaSum F.tail.omega hι _ _).mpr hnativeSum
  exact iEquivalent_of_sourceTraceRepresentatives
    (Nat.le_succ m) F.tail.omega F.tail.omega hι hTs hsourceSum

/-- Ordinary analytic trace agreement is used only for the unscaled genuine
Cartier metric. Real trace homogeneity and all-level scalar transport then
handle every finite real coefficient, including the true constant-zero branch. -/
theorem iEquivalent_sourceTrace_scaled_divisorMetric_restriction {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    (R : EffectiveDivisor (m + 1) F.carrier)
    (RT : EffectiveDivisor m F.tail.carrier)
    (hRI : letI : ChartedSpace (ComplexModel m) (F.flag (1 : Fin (m + 2))) := F.tail.charts
      RT.ideal = GermIdeal.pullback (m := m)
        (Subtype.val : F.tail.carrier → F.carrier) R.ideal)
    (ER : MeteredEffectiveQDivisor (m + 1) F.carrier)
    (ET : MeteredEffectiveQDivisor m F.tail.carrier)
    (hERsup : ER.support = R.support) (hER : DivisorMetric.IsDivisorMetric R ER)
    (hET : DivisorMetric.IsDivisorMetric RT ET)
    (hnot : ¬ F.flag (1 : Fin (m + 2)) ⊆ R.support) (c : ℝ≥0)
    {ρ : F.tail.carrier → EReal}
    (hρ : IsNaturalSourceTraceRepresentative F.omega F.firstDivisor
      (fun x => ((c : ℝ) : EReal) * ER.weight x) ρ) :
    IEquivalentOnManifold (n := m) ρ (fun y => ((c : ℝ) : EReal) * ET.weight y) := by
  let Z := F.flag (1 : Fin (m + 2))
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) F.firstDivisor.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
    (Nat.le_succ m) F.firstDivisor.2.2
  let : CompactSpace Z := F.tail.compact
  let : ConnectedSpace Z := F.tail.connected
  let : MeasurableSpace Z := borel Z
  let : BorelSpace Z := ⟨rfl⟩
  let : MeasurableSpace F.tail.carrier := borel F.tail.carrier
  let : BorelSpace F.tail.carrier := ⟨rfl⟩
  let hι := SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ m) F.firstDivisor.2.2
  change IsSourceTraceRepresentativeAlong F.omega F.tail.omega hι _ ρ at hρ
  by_cases hc : c = 0
  · subst c
    simp only [NNReal.coe_zero, EReal.coe_zero, zero_mul] at hρ ⊢
    have hnρ := (isSourceTraceRepresentativeAlong_iff_native
      (Nat.succ_ne_zero m) F.omega F.tail.omega hι _ _).mp hρ
    have hA := QuasiEquisingularComparison.hasManifoldAnalyticSingularityType_const
      (n := m + 1) (M := F.carrier) 0
    have hP := AnalyticTraceOrdinaryAgreement.sourcePEquivalent_ordinaryRestriction_of_analytic_isTraceRepresentativeAlong
      F.tail.omega hι hnρ hA
    exact GlobalPMultiplierOrder.iEquivalentOnManifold_of_sourcePEquivalent hP
  · have hcR : 0 < (c : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc)
    have hR := isThetaPshPotential_effectiveDivisorMetric R ER hER
    have hzero := sourceGeneric_effectiveDivisorMetric_eq_zero_of_not_contains
      R ER hERsup hnot
    obtain ⟨ρ₀, hρ₀⟩ :=
      NaturalSourceTraceExistenceAllDimensions.exists_naturalSourceTrace_of_isThetaPshPotential
        F.omega F.firstDivisor hR hzero
    change IsSourceTraceRepresentativeAlong F.omega F.tail.omega hι ER.weight ρ₀ at hρ₀
    have hnρ₀ := (isSourceTraceRepresentativeAlong_iff_native
      (Nat.succ_ne_zero m) F.omega F.tail.omega hι _ _).mp hρ₀
    have hnρ := (isSourceTraceRepresentativeAlong_iff_native
      (Nat.succ_ne_zero m) F.omega F.tail.omega hι _ _).mp hρ
    have hP := TracePositiveRealHomogeneity.sourcePEquivalent_pos_smul_of_isTraceRepresentativeAlong
      F.tail.omega F.tail.omega hι hnρ₀ hcR hnρ
    have hIscaled := GlobalPMultiplierOrder.iEquivalentOnManifold_of_sourcePEquivalent hP
    have hordinary := AnalyticTraceOrdinaryAgreement.sourcePEquivalent_ordinaryRestriction_of_analytic_isTraceRepresentativeAlong
      F.tail.omega hι hnρ₀
        (DivisorMetric.hasAnalyticSingularitiesOfType_of_isDivisorMetric hER).hasManifoldAnalyticSingularityType
    have hIordinary := GlobalPMultiplierOrder.iEquivalentOnManifold_of_sourcePEquivalent hordinary
    have hImetric := iEquivalent_divisorMetric_pullback_restrictedDivisorMetric
      hι R RT hRI ER ET hER hET
    exact hIscaled.trans (iEquivalentOnManifold_nonneg_smul (hIordinary.trans hImetric) c)

private theorem theta_nonneg_smul_all_dimensions {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (c : ℝ≥0) :
    IsThetaPshPotential ((c : ℝ) • θ).val (fun x => ((c : ℝ) : EReal) * u x) := by
  by_cases hc : c = 0
  · subst c
    simp only [NNReal.coe_zero, zero_smul, EReal.coe_zero, zero_mul]
    exact (LocalPotentials.isThetaPshPotential_zero_iff 0).mpr fun _ _ _ _ => le_rfl
  · exact RestrictedApproximantComparison.isThetaPshPotential_smul hu
      (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc))

private theorem iEquivalent_add_of_four_theta_backgrounds {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [CompactSpace M] (omega : KahlerBackground n M)
    {θu θv θa θb : ClosedRealOneOneForm n M} {u v a b : M → EReal}
    (hu : IsThetaPshPotential θu.val u) (hv : IsThetaPshPotential θv.val v)
    (ha : IsThetaPshPotential θa.val a) (hb : IsThetaPshPotential θb.val b)
    (hIu : IEquivalentOnManifold (n := n) u a)
    (hIv : IEquivalentOnManifold (n := n) v b) :
    IEquivalentOnManifold (n := n) (fun x => u x + v x) (fun x => a x + b x) := by
  let B : Bool × Bool → ClosedRealOneOneForm n M := fun q =>
    if q.1 then (if q.2 then θa else θb) else (if q.2 then θu else θv)
  obtain ⟨C, hC, hdom⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul
    omega (fun q : Bool × Bool => -(B q))
  let γ : KahlerBackground n M := KahlerBackground.smul hC omega
  have hγof (q : Bool × Bool) {p : M → EReal} (hp : IsThetaPshPotential (B q).val p) :
      IsThetaPshPotential γ.form.val p := by
    have heq : B q + (-B q + C • omega.form) = γ.form := by
      dsimp only [γ, KahlerBackground.smul_form]
      module
    simpa only [heq] using LocalPotentials.isThetaPshPotential_add_of_semipositive hp (hdom q)
  exact ActualMultiplierOrderAddition.iEquivalentOnManifold_add
    (hγof (false, true) hu) (hγof (false, false) hv)
    (hγof (true, true) ha) (hγof (true, false) hb) hIu hIv

/-- Every genuine lifted residual trace has the literal sum class of the
pulled downstairs trace and the actual restricted Cartier metric. Every
membership, intermediate trace and comparison is internally manufactured. -/
theorem iEquivalent_sourceTrace_lifted_residual_sum_tail {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π)
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {v : F.carrier → EReal}
    (hv : IsThetaPshPotential θ.val v)
    (hzero : sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) v = 0)
    {τ : F.tail.carrier → EReal}
    (hτ : IsNaturalSourceTraceRepresentative F.omega F.firstDivisor v τ)
    (R : EffectiveDivisor (m + 1) W.carrier)
    (RT : EffectiveDivisor m W.tail.carrier)
    (hRI : letI : ChartedSpace (ComplexModel m) (W.flag (1 : Fin (m + 2))) := W.tail.charts
      RT.ideal = GermIdeal.pullback (m := m)
        (Subtype.val : W.tail.carrier → W.carrier) R.ideal)
    (ER : MeteredEffectiveQDivisor (m + 1) W.carrier)
    (ET : MeteredEffectiveQDivisor m W.tail.carrier)
    (hERsup : ER.support = R.support) (hER : DivisorMetric.IsDivisorMetric R ER)
    (hET : DivisorMetric.IsDivisorMetric RT ET)
    (hnot : ¬ W.flag (1 : Fin (m + 2)) ⊆ R.support) (c : ℝ≥0)
    {ρ : W.tail.carrier → EReal}
    (hρ : IsNaturalSourceTraceRepresentative W.omega W.firstDivisor
      (fun z => v (π z) + ((c : ℝ) : EReal) * ER.weight z) ρ) :
    IEquivalentOnManifold (n := m) ρ
      (fun y => τ (hπ.tailMap y) + ((c : ℝ) : EReal) * ET.weight y) := by
  have hvp := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    hπ.1 θ hv
  have hzeroV : sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : W.flag (1 : Fin (m + 2)) → W.carrier) (v ∘ π) = 0 :=
    (hπ.sourceGeneric_first_comp_eq hv.quasiPshPotential).trans hzero
  obtain ⟨ρv, hρv⟩ :=
    NaturalSourceTraceExistenceAllDimensions.exists_naturalSourceTrace_of_isThetaPshPotential
      W.omega W.firstDivisor hvp hzeroV
  have hR := isThetaPshPotential_effectiveDivisorMetric R ER hER
  have hCR := theta_nonneg_smul_all_dimensions hR c
  have hzeroR := sourceGeneric_effectiveDivisorMetric_eq_zero_of_not_contains
    R ER hERsup hnot
  have hscaled := W.smooth.flagGenericLelong_nonneg_smul_eq ER.weight
    (1 : Fin (m + 2)) c.coe_nonneg
  have hzeroCR : sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : W.flag (1 : Fin (m + 2)) → W.carrier)
      (fun z => ((c : ℝ) : EReal) * ER.weight z) = 0 := by
    simpa only [flagGenericLelong, hzeroR, mul_zero] using hscaled
  obtain ⟨ρR, hρR⟩ :=
    NaturalSourceTraceExistenceAllDimensions.exists_naturalSourceTrace_of_isThetaPshPotential
      W.omega W.firstDivisor hCR hzeroCR
  have hIsum := iEquivalent_sourceTrace_add W hρv hρR hρ
  let : MeasurableSpace F.tail.carrier := borel F.tail.carrier
  let : BorelSpace F.tail.carrier := ⟨rfl⟩
  let : MeasurableSpace W.tail.carrier := borel W.tail.carrier
  let : BorelSpace W.tail.carrier := ⟨rfl⟩
  have hIv := (GlobalPMultiplierOrder.iEquivalentOnManifold_of_sourcePEquivalent
    (hπ.sourcePEquivalent_first_sourceTrace_pullback hτ hρv)).symm
  have hIR := iEquivalent_sourceTrace_scaled_divisorMetric_restriction
    W R RT hRI ER ET hERsup hER hET hnot c hρR
  let hιF := SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ m) F.firstDivisor.2.2
  let hιW := SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ m) W.firstDivisor.2.2
  change IsSourceTraceRepresentativeAlong F.omega F.tail.omega hιF v τ at hτ
  change IsSourceTraceRepresentativeAlong W.omega W.tail.omega hιW _ ρv at hρv
  change IsSourceTraceRepresentativeAlong W.omega W.tail.omega hιW _ ρR at hρR
  obtain ⟨_hzτ, _θτ, _ετ, _Uτ, _hqτ, βτ, _hadmτ, hτβ, _htermsτ, _hlimτ⟩ := hτ
  obtain ⟨_hzv, _θv, _εv, _Uv, _hqv, βv, _hadmv, hρvβ, _htermsv, _hlimv⟩ := hρv
  obtain ⟨_hzR, _θR, _εR, _UR, _hqR, βR, _hadmR, hρRβ, _htermsR, _hlimR⟩ := hρR
  have hτp := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    hπ.tailMap_isFlagLifting.1 βτ.form hτβ
  have hET := isThetaPshPotential_effectiveDivisorMetric RT ET hET
  have hCET := theta_nonneg_smul_all_dimensions hET c
  have hIadd := iEquivalent_add_of_four_theta_backgrounds W.tail.omega
    hρvβ hρRβ hτp hCET hIv hIR
  exact hIsum.trans hIadd

end SGPT.Okounkov
