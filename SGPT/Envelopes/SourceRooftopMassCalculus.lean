import SGPT.Envelopes.SourceRelativeEnvelopeExhaustion
import SGPT.Envelopes.SourceFullMassIntegralEstimates
import SGPT.Foundations.Analysis.Pending.RooftopMassDiamondUnconditional

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending DiagonalMass

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u v g h : M → EReal}

/-- The actual pointwise maximum retains the unchanged source theta tests. -/
theorem sourceThetaMaximum_genuine
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v) :
    (ofFixedModel n M).IsThetaPSH θ (fun x => max (u x) (v x)) :=
  (isThetaPSH_iff_nativeThetaPotential θ _).mpr
    (IsThetaPshPotential.max ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
      ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv))

/-- The source rooftop's existing actual class-or-bottom producer discharges
genuineness from the original nonbottom hypothesis. -/
theorem sourceThetaRooftop_genuine_of_ne_bot
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hne : thetaRooftop θ u v ≠ ⊥) :
    (ofFixedModel n M).IsThetaPSH θ (thetaRooftop θ u v) :=
  (isThetaPSHOrBot_thetaRooftop (Or.inl hu) (Or.inl hv)).resolve_right hne

/-- Genuine local finite points exclude an identically bottom function on
the original nonempty manifold. -/
theorem sourceThetaPSH_ne_bot [Nonempty M] (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    u ≠ ⊥ := by
  obtain ⟨x, _, hx, _⟩ := ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu).quasiPshPotential.exists_finite
    (Classical.arbitrary M) isOpen_univ (mem_univ _)
  intro hbot
  exact hx (congrFun hbot x)

/-- The source additive-singularity comparison gives actual ordinary-envelope
monotonicity before any mass or model assumption. -/
theorem sourceOrdinaryEnvelope_mono (huv : SGPT.PSH.SingularityLE u v) :
    sourceSingularityEnvelope θ u ≤ sourceSingularityEnvelope θ v := by
  simp only [sourceSingularityEnvelope_eq_native]
  exact singularityEnvelope_mono huv

/-- Finite source translations use the existing genuine native producer. -/
theorem sourceThetaPSH_add_const (hu : (ofFixedModel n M).IsThetaPSH θ u) (c : ℝ) :
    (ofFixedModel n M).IsThetaPSH θ (fun x => u x + (c : EReal)) :=
  (isThetaPSH_iff_nativeThetaPotential θ _).mpr
    (((isThetaPSH_iff_nativeThetaPotential θ u).mp hu).add_const c)

omit [TopologicalSpace M] in
/-- ONE finite original additive comparison constant handles two independent
preceq inputs; no final pointwise-order premise is added. -/
theorem sourcePreceqPair_common_shift
    (hgu : SGPT.PSH.SingularityLE g u) (hhv : SGPT.PSH.SingularityLE h v) :
    ∃ c : ℝ, (fun x => g x + (c : EReal)) ≤ u ∧
      (fun x => h x + (c : EReal)) ≤ v := by
  obtain ⟨a, ha⟩ := (singularityLE_iff_exists_real _ _).mp hgu
  obtain ⟨b, hb⟩ := (singularityLE_iff_exists_real _ _).mp hhv
  refine ⟨-max a b, ?_, ?_⟩
  · intro x
    apply (RelativePreceqClasses.add_coe_le_iff _ _ _).mpr
    simpa only [neg_neg] using
      (ha x).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_max_left a b)))
  · intro x
    apply (RelativePreceqClasses.add_coe_le_iff _ _ _).mpr
    simpa only [neg_neg] using
      (hb x).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_max_right a b)))

variable [CompactSpace M] [ConnectedSpace M]

/-- Genuine ordinary-envelope closure retains zero-mass inputs. -/
theorem sourceOrdinaryEnvelope_genuine (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    (ofFixedModel n M).IsThetaPSH θ (sourceSingularityEnvelope θ u) := by
  apply (isThetaPSH_iff_nativeThetaPotential θ _).mpr
  rw [sourceSingularityEnvelope_eq_native]
  have hn := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  exact FirstPass.singularityEnvelope_isThetaPshPotential _ (atlasClosedFormToNative θ).property.1
    (atlasClosedFormToNative θ).property.2 hn.1.hasSmoothLocalPotentials u hn

/-- The genuine SOURCE raw roof is an actual common lower barrier, so native
genuineness is manufactured before using the all-minorant dictionary. -/
theorem sourceThetaRooftop_native_genuine
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hr : (ofFixedModel n M).IsThetaPSH θ (thetaRooftop θ u v)) :
    IsThetaPshPotential (atlasClosedFormToNative θ).val
      (RelativeDarvasDistance.rooftop (atlasClosedFormToNative θ) u v) :=
  (RooftopPshCriterion.rooftop_min_of_lower _
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
    ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv)
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp hr)
    (thetaRooftop_le_left θ u v) (thetaRooftop_le_right θ u v)).1

/-- WHOLE ordinary fixed-point rooftop preservation: the source's nonbottom
hypothesis is sufficient, including when the original fixed points have zero mass. -/
theorem sourceThetaRooftop_fixed_point
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hufix : u = sourceSingularityEnvelope θ u) (hvfix : v = sourceSingularityEnvelope θ v)
    (hne : thetaRooftop θ u v ≠ ⊥) :
    sourceSingularityEnvelope θ (thetaRooftop θ u v) = thetaRooftop θ u v := by
  have hr := sourceThetaRooftop_genuine_of_ne_bot hu hv hne
  have hp := sourceOrdinaryEnvelope_genuine hr
  have hpu : sourceSingularityEnvelope θ (thetaRooftop θ u v) ≤ u :=
    (sourceOrdinaryEnvelope_mono
      (MoreSingularOn.of_le fun x _ => thetaRooftop_le_left θ u v x)).trans_eq hufix.symm
  have hpv : sourceSingularityEnvelope θ (thetaRooftop θ u v) ≤ v :=
    (sourceOrdinaryEnvelope_mono
      (MoreSingularOn.of_le fun x _ => thetaRooftop_le_right θ u v x)).trans_eq hvfix.symm
  have hr0 : thetaRooftop θ u v ≤ 0 :=
    (thetaRooftop_le_left θ u v).trans (hufix ▸ sourceSingularityEnvelope_le_zero θ u)
  exact le_antisymm (le_thetaRooftop hp hpu hpv)
    (le_sourceSingularityEnvelope hr hr0 (MoreSingularOn.refl _ univ))

variable [MeasurableSpace M] [BorelSpace M]

omit [BorelSpace M] in
/-- The original raw-rooftop mass equals the actual native rooftop mass;
both genuine roofs are produced from the source's genuine-roof hypothesis. -/
theorem sourceThetaRooftop_mass_eq_native
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hr : (ofFixedModel n M).IsThetaPSH θ (thetaRooftop θ u v)) :
    sourcePotentialNonPluripolarMeasure θ (thetaRooftop θ u v) hr univ =
      diagonalPotentialMass (atlasClosedFormToNative θ)
        (RelativeDarvasDistance.rooftop (atlasClosedFormToNative θ) u v)
        (sourceThetaRooftop_native_genuine hu hv hr) :=
  RelativePreceqStatements.diagonalPotentialMass_congr
    (sourceThetaRooftop_eq_native hu hv (sourceThetaRooftop_native_genuine hu hv hr)) _ _

/-- WHOLE strict-mass criterion for the actual original raw rooftop. -/
theorem sourceThetaRooftop_genuine_of_mass_gt (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hgt : sourcePotentialNonPluripolarMeasure θ (fun x => max (u x) (v x))
        (sourceThetaMaximum_genuine hu hv) univ <
      sourcePotentialNonPluripolarMeasure θ u hu univ +
        sourcePotentialNonPluripolarMeasure θ v hv univ) :
    (ofFixedModel n M).IsThetaPSH θ (thetaRooftop θ u v) := by
  have hr := RooftopPshCriterion.isThetaPshPotential_rooftopEnvelope_min_of_mass_lt ω _
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
    ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv) hgt
  rw [sourceThetaRooftop_eq_native hu hv hr]
  exact (isThetaPSH_iff_nativeThetaPotential θ _).mpr hr

/-- The original printed variant permits ANY actual upper preceq potential,
without a common model or a full-mass hypothesis. -/
theorem sourceThetaRooftop_genuine_of_upper_mass_gt (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    {w : M → EReal} (hw : (ofFixedModel n M).IsThetaPSH θ w)
    (hmaxw : SGPT.PSH.SingularityLE (fun x => max (u x) (v x)) w)
    (hgt : sourcePotentialNonPluripolarMeasure θ w hw univ <
      sourcePotentialNonPluripolarMeasure θ u hu univ +
        sourcePotentialNonPluripolarMeasure θ v hv univ) :
    (ofFixedModel n M).IsThetaPSH θ (thetaRooftop θ u v) := by
  apply sourceThetaRooftop_genuine_of_mass_gt ω hu hv
  exact lt_of_le_of_lt (diagonalPotentialMass_mono_of_kahler ω
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp (sourceThetaMaximum_genuine hu hv))
    ((isThetaPSH_iff_nativeThetaPotential θ w).mp hw) hmaxw) hgt

private theorem nativeRooftop_mass_transfer_of_preceq (ω : KahlerBackground n M)
    (T : ClosedRealOneOneForm n M)
    (nu : IsThetaPshPotential T.val u) (nv : IsThetaPshPotential T.val v)
    (nr : IsThetaPshPotential T.val (RelativeDarvasDistance.rooftop T u v))
    (hpos : 0 < diagonalPotentialMass T _ nr)
    (ng : IsThetaPshPotential T.val g) (nh : IsThetaPshPotential T.val h)
    (hgu : SGPT.PSH.SingularityLE g u) (hhv : SGPT.PSH.SingularityLE h v)
    (hmg : diagonalPotentialMass T g ng = diagonalPotentialMass T u nu)
    (hmh : diagonalPotentialMass T h nh = diagonalPotentialMass T v nv) :
    ∃ ngh : IsThetaPshPotential T.val (RelativeDarvasDistance.rooftop T g h),
      diagonalPotentialMass T _ ngh = diagonalPotentialMass T _ nr := by
  obtain ⟨c, hgc, hhc⟩ := sourcePreceqPair_common_shift hgu hhv
  have hmgc : diagonalPotentialMass T (fun x => g x + (c : EReal)) (ng.add_const c) =
      diagonalPotentialMass T u nu :=
    (congrArg (fun μ : Measure M => μ univ)
      (DiagonalMeasureRegularity.diagonalPotentialMeasure_add_const T ng c (ng.add_const c))).trans hmg
  have hmhc : diagonalPotentialMass T (fun x => h x + (c : EReal)) (nh.add_const c) =
      diagonalPotentialMass T v nv :=
    (congrArg (fun μ : Measure M => μ univ)
      (DiagonalMeasureRegularity.diagonalPotentialMeasure_add_const T nh c (nh.add_const c))).trans hmh
  obtain ⟨nrc, hmrc⟩ := RooftopEnvelopeLatticeMass.rooftop_mass_eq_of_le_of_mass_eq₂ ω T
    nu nv nr hpos (ng.add_const c) hgc hmgc (nh.add_const c) hhc hmhc
  have hcancel : (fun x => RelativeDarvasDistance.rooftop T
      (fun y => g y + (c : EReal)) (fun y => h y + (c : EReal)) x + ((-c : ℝ) : EReal)) =
      RelativeDarvasDistance.rooftop T g h := by
    rw [RelativePreceqClasses.rooftop_add_const]
    funext x
    exact RelativePreceqClasses.add_coe_add_coe_neg _ c
  have ngh : IsThetaPshPotential T.val (RelativeDarvasDistance.rooftop T g h) :=
    hcancel ▸ nrc.add_const (-c)
  refine ⟨ngh, ?_⟩
  calc
    _ = diagonalPotentialMass T (fun x => RelativeDarvasDistance.rooftop T
        (fun y => g y + (c : EReal)) (fun y => h y + (c : EReal)) x + ((-c : ℝ) : EReal))
        (nrc.add_const (-c)) :=
      RelativePreceqStatements.diagonalPotentialMass_congr hcancel.symm _ _
    _ = diagonalPotentialMass T (RelativeDarvasDistance.rooftop T
        (fun y => g y + (c : EReal)) (fun y => h y + (c : EReal))) nrc :=
      congrArg (fun μ : Measure M => μ univ)
        (DiagonalMeasureRegularity.diagonalPotentialMeasure_add_const T nrc (-c) (nrc.add_const (-c)))
    _ = _ := hmrc

/-- WHOLE original two-endpoint mass transfer on the FULL additive preceq
domain. The stronger existing mother does not require endpoint fixed points.
Both unshifted rooftop genuineness and its mass equality are produced. -/
theorem sourceThetaRooftop_fullMass_transfer (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hr : (ofFixedModel n M).IsThetaPSH θ (thetaRooftop θ u v))
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ (thetaRooftop θ u v) hr univ)
    (hg : (ofFixedModel n M).IsThetaPSH θ g) (hh : (ofFixedModel n M).IsThetaPSH θ h)
    (hgu : SGPT.PSH.SingularityLE g u) (hhv : SGPT.PSH.SingularityLE h v)
    (hmg : sourcePotentialNonPluripolarMeasure θ g hg univ =
      sourcePotentialNonPluripolarMeasure θ u hu univ)
    (hmh : sourcePotentialNonPluripolarMeasure θ h hh univ =
      sourcePotentialNonPluripolarMeasure θ v hv univ) :
    ∃ hgh : (ofFixedModel n M).IsThetaPSH θ (thetaRooftop θ g h),
      thetaRooftop θ g h ≠ ⊥ ∧
        sourcePotentialNonPluripolarMeasure θ (thetaRooftop θ g h) hgh univ =
          sourcePotentialNonPluripolarMeasure θ (thetaRooftop θ u v) hr univ := by
  let T := atlasClosedFormToNative θ
  have nu := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have nv := (isThetaPSH_iff_nativeThetaPotential θ v).mp hv
  have ng := (isThetaPSH_iff_nativeThetaPotential θ g).mp hg
  have nh := (isThetaPSH_iff_nativeThetaPotential θ h).mp hh
  have nr := sourceThetaRooftop_native_genuine hu hv hr
  have hposn : 0 < diagonalPotentialMass T (RelativeDarvasDistance.rooftop T u v) nr := by
    rw [← sourceThetaRooftop_mass_eq_native hu hv hr]
    exact hpos
  obtain ⟨ngh, hmgh⟩ := nativeRooftop_mass_transfer_of_preceq ω T
    nu nv nr hposn ng nh hgu hhv hmg hmh
  have hgh : (ofFixedModel n M).IsThetaPSH θ (thetaRooftop θ g h) := by
    rw [sourceThetaRooftop_eq_native hg hh ngh]
    exact (isThetaPSH_iff_nativeThetaPotential θ _).mpr ngh
  refine ⟨hgh, sourceThetaPSH_ne_bot hgh, ?_⟩
  rw [sourceThetaRooftop_mass_eq_native hg hh hgh, sourceThetaRooftop_mass_eq_native hu hv hr]
  exact hmgh

/-- WHOLE original mass diamond for arbitrary genuine endpoints and genuine
raw roof, including zero masses and dimension zero. The native lattice-mass
interface and both zero-mass cases are discharged by the actual producer. -/
theorem sourceThetaRooftop_mass_diamond (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hr : (ofFixedModel n M).IsThetaPSH θ (thetaRooftop θ u v)) :
    sourcePotentialNonPluripolarMeasure θ u hu univ +
        sourcePotentialNonPluripolarMeasure θ v hv univ ≤
      sourcePotentialNonPluripolarMeasure θ (fun x => max (u x) (v x))
        (sourceThetaMaximum_genuine hu hv) univ +
      sourcePotentialNonPluripolarMeasure θ (thetaRooftop θ u v) hr univ := by
  rw [sourceThetaRooftop_mass_eq_native hu hv hr]
  exact RooftopMassDiamondUnconditional.mass_add_mass_le_mass_max_add_mass_rooftop ω _
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
    ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv)
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp (sourceThetaMaximum_genuine hu hv))
    (sourceThetaRooftop_native_genuine hu hv hr)

end SGPT.PSH.VariableComplexAtlas
