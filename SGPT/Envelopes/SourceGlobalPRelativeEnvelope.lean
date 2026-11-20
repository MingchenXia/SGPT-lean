import SGPT.Envelopes.SourceOrdinaryEnvelopeMassModel
import SGPT.Envelopes.SourcePositiveAffineEnvelopes
import SGPT.PSH.GlobalPComparison

set_option autoImplicit false

/-! The whole original `cor:P_par_envelope_rel`, for the literal source
raw roof, all positive real shifts and the ALL-QE relative envelope. -/

noncomputable section
namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending DiagonalMass

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ ψ : M → EReal}

/-- True global P-comparison manufactures a common genuine full-mass lower
reference in the actual model P[ψ], without normalizing the original inputs. -/
theorem sourcePOrder_relativeFullMassLower (ω : KahlerBackground n M)
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (hψ : (ofFixedModel n M).IsThetaPSH θ ψ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    (hψpos : 0 < sourcePotentialNonPluripolarMeasure θ ψ hψ univ)
    (hP : GlobalPComparison.sourcePOrder (n := n) ψ φ) :
    ∃ hm : SourceModelPotential θ (sourceSingularityEnvelope θ ψ),
      SourceRelativeFullMass θ (sourceSingularityEnvelope θ ψ)
          (thetaRooftop θ φ (sourceSingularityEnvelope θ ψ)) hm ∧
      SourceRelativeFullMass θ (sourceSingularityEnvelope θ ψ) ψ hm ∧
      thetaRooftop θ φ (sourceSingularityEnvelope θ ψ) ≤ φ := by
  have hφn := (isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ
  have hψn := (isThetaPSH_iff_nativeThetaPotential θ ψ).mp hψ
  have hfixed := (GlobalPComparison.sourcePOrder_iff_positive_background ω
    (atlasClosedFormToNative θ) hψn hφn hψpos hφpos).mp hP
  have horder : sourceSingularityEnvelope θ ψ ≤ sourceSingularityEnvelope θ φ := by
    simpa only [sourceSingularityEnvelope_eq_native, POrder.POrderWith] using hfixed
  have hA := sourceOrdinaryEnvelope_genuine hφ
  have hm := sourceOrdinaryEnvelope_genuine hψ
  have hmodel := sourceOrdinaryEnvelope_model ω hψ hψpos
  have hmassφ := sourceOrdinaryEnvelope_diagonalMass_eq ω hφ
  have hmassψ := sourceOrdinaryEnvelope_diagonalMass_eq ω hψ
  have hφA : SGPT.PSH.SingularityLE φ (sourceSingularityEnvelope θ φ) := by
    simpa only [sourceSingularityEnvelope_eq_native, SGPT.PSH.SingularityLE] using
      moreSingularOn_singularityEnvelope hφn
  have hψm : SGPT.PSH.SingularityLE ψ (sourceSingularityEnvelope θ ψ) := by
    simpa only [sourceSingularityEnvelope_eq_native, SGPT.PSH.SingularityLE] using
      moreSingularOn_singularityEnvelope hψn
  have heq : thetaRooftop θ (sourceSingularityEnvelope θ φ)
      (sourceSingularityEnvelope θ ψ) = sourceSingularityEnvelope θ ψ :=
    le_antisymm (thetaRooftop_le_right θ _ _) (le_thetaRooftop hm horder le_rfl)
  have hr : (ofFixedModel n M).IsThetaPSH θ
      (thetaRooftop θ (sourceSingularityEnvelope θ φ) (sourceSingularityEnvelope θ ψ)) :=
    heq.symm ▸ hm
  have hrpos : 0 < sourcePotentialNonPluripolarMeasure θ _ hr univ := by
    simpa only [heq, hmassψ] using hψpos
  obtain ⟨hχ, _, hχmass⟩ := sourceThetaRooftop_fullMass_transfer ω hA hm hr hrpos hφ hm
    hφA (MoreSingularOn.refl _ univ) hmassφ.symm rfl
  refine ⟨hmodel, ⟨hχ, MoreSingularOn.of_le fun x _ => thetaRooftop_le_right θ _ _ x, ?_⟩,
    ⟨hψ, hψm, ?_⟩, thetaRooftop_le_left θ _ _⟩
  · simpa only [heq] using hχmass
  · exact hmassψ.symm

/-- Every nonnegative finite shift gives the genuine original raw roof with
the SAME positive original mass as ψ; no output certificate is an input. -/
theorem sourcePOrder_shiftedRooftop_positive (ω : KahlerBackground n M)
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (hψ : (ofFixedModel n M).IsThetaPSH θ ψ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    (hψpos : 0 < sourcePotentialNonPluripolarMeasure θ ψ hψ univ)
    (hP : GlobalPComparison.sourcePOrder (n := n) ψ φ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ hr : (ofFixedModel n M).IsThetaPSH θ
        (thetaRooftop θ ψ (fun x => φ x + (C : EReal))),
      thetaRooftop θ ψ (fun x => φ x + (C : EReal)) ≠ ⊥ ∧
      sourcePotentialNonPluripolarMeasure θ
          (thetaRooftop θ ψ (fun x => φ x + (C : EReal))) hr univ =
        sourcePotentialNonPluripolarMeasure θ ψ hψ univ ∧
      0 < sourcePotentialNonPluripolarMeasure θ
        (thetaRooftop θ ψ (fun x => φ x + (C : EReal))) hr univ := by
  have hφn := (isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ
  have hψn := (isThetaPSH_iff_nativeThetaPotential θ ψ).mp hψ
  have hfixed := (GlobalPComparison.sourcePOrder_iff_positive_background ω
    (atlasClosedFormToNative θ) hψn hφn hψpos hφpos).mp hP
  have horder : sourceSingularityEnvelope θ ψ ≤ sourceSingularityEnvelope θ φ := by
    simpa only [sourceSingularityEnvelope_eq_native, POrder.POrderWith] using hfixed
  have hA := sourceOrdinaryEnvelope_genuine hφ
  have hm := sourceOrdinaryEnvelope_genuine hψ
  have hmassφ := sourceOrdinaryEnvelope_diagonalMass_eq ω hφ
  have hmassψ := sourceOrdinaryEnvelope_diagonalMass_eq ω hψ
  have hφA : SGPT.PSH.SingularityLE φ (sourceSingularityEnvelope θ φ) := by
    simpa only [sourceSingularityEnvelope_eq_native, SGPT.PSH.SingularityLE] using
      moreSingularOn_singularityEnvelope hφn
  have hψm : SGPT.PSH.SingularityLE ψ (sourceSingularityEnvelope θ ψ) := by
    simpa only [sourceSingularityEnvelope_eq_native, SGPT.PSH.SingularityLE] using
      moreSingularOn_singularityEnvelope hψn
  have hφAC : SGPT.PSH.SingularityLE (fun x => φ x + (C : EReal))
      (fun x => sourceSingularityEnvelope θ φ x + (C : EReal)) := by
    obtain ⟨b, hb⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp hφA
    apply (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr
    refine ⟨b, fun x => ?_⟩
    exact (add_le_add (hb x) le_rfl).trans_eq (add_right_comm _ _ _)
  have hshiftorder : sourceSingularityEnvelope θ ψ ≤
      (fun x => sourceSingularityEnvelope θ φ x + (C : EReal)) := by
    intro x
    apply (horder x).trans
    simpa only [EReal.coe_zero, add_zero] using
      add_le_add (le_refl (sourceSingularityEnvelope θ φ x)) (EReal.coe_le_coe_iff.mpr hC)
  have heq : thetaRooftop θ (fun x => sourceSingularityEnvelope θ φ x + (C : EReal))
      (sourceSingularityEnvelope θ ψ) = sourceSingularityEnvelope θ ψ :=
    le_antisymm (thetaRooftop_le_right θ _ _) (le_thetaRooftop hm hshiftorder le_rfl)
  have hr : (ofFixedModel n M).IsThetaPSH θ
      (thetaRooftop θ (fun x => sourceSingularityEnvelope θ φ x + (C : EReal))
        (sourceSingularityEnvelope θ ψ)) := heq.symm ▸ hm
  have hrpos : 0 < sourcePotentialNonPluripolarMeasure θ _ hr univ := by
    simpa only [heq, hmassψ] using hψpos
  have hmassC := (sourceAffine_mass_add_const hφ C).trans
    (hmassφ.symm.trans (sourceAffine_mass_add_const hA C).symm)
  obtain ⟨hroof, hne, hmass⟩ := sourceThetaRooftop_fullMass_transfer ω
    (sourceThetaPSH_add_const hA C) hm hr hrpos (sourceThetaPSH_add_const hφ C) hψ
    hφAC hψm hmassC hmassψ.symm
  have hswap := thetaRooftop_comm θ ψ (fun x => φ x + (C : EReal))
  have hr' : (ofFixedModel n M).IsThetaPSH θ
      (thetaRooftop θ ψ (fun x => φ x + (C : EReal))) := hswap.symm ▸ hroof
  have hmass' : sourcePotentialNonPluripolarMeasure θ
      (thetaRooftop θ ψ (fun x => φ x + (C : EReal))) hr' univ =
      sourcePotentialNonPluripolarMeasure θ ψ hψ univ := by
    simpa only [hswap, heq, hmassψ] using hmass
  exact ⟨hr', by simpa only [hswap] using hne, hmass', hmass' ▸ hψpos⟩

/-- Full additive-order exhaustion of an internally produced common lower
reference yields the printed ALL-positive-real original rooftop supremum. -/
theorem sourcePOrder_relativeRooftop_exhaustion (ω : KahlerBackground n M)
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (hψ : (ofFixedModel n M).IsThetaPSH θ ψ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    (hψpos : 0 < sourcePotentialNonPluripolarMeasure θ ψ hψ univ)
    (hP : GlobalPComparison.sourcePOrder (n := n) ψ φ) :
    uscSup (fun C : {C : ℝ // 0 < C} =>
      thetaRooftop θ ψ (fun x => φ x + (C.1 : EReal))) = ψ := by
  obtain ⟨hm, hχfull, hψfull, hχφ⟩ :=
    sourcePOrder_relativeFullMassLower ω hφ hψ hφpos hψpos hP
  let χ := thetaRooftop θ φ (sourceSingularityEnvelope θ ψ)
  have hexhaust : uscSup (fun C : {C : ℝ // 0 < C} =>
      thetaRooftop θ (fun x => χ x + (C.1 : EReal)) ψ) = ψ :=
    sourceFullMass_rooftop_exhaustion ω hχfull hψfull
  have hroof (C : {C : ℝ // 0 < C}) :
      thetaRooftop θ (fun x => χ x + (C.1 : EReal)) ψ ≤
        thetaRooftop θ ψ (fun x => φ x + (C.1 : EReal)) := by
    intro x
    apply iSup_le
    intro a
    exact le_thetaRooftop a.2.1 a.2.2.2
      (fun y => (a.2.2.1 y).trans (add_le_add (hχφ y) le_rfl)) x
  have hlow : uscSup (fun C : {C : ℝ // 0 < C} =>
      thetaRooftop θ (fun x => χ x + (C.1 : EReal)) ψ) ≤
      uscSup (fun C : {C : ℝ // 0 < C} =>
        thetaRooftop θ ψ (fun x => φ x + (C.1 : EReal))) :=
    uscRegularization_mono (fun x => iSup_mono fun C => hroof C x)
  have hupp : uscSup (fun C : {C : ℝ // 0 < C} =>
      thetaRooftop θ ψ (fun x => φ x + (C.1 : EReal))) ≤ ψ :=
    uscRegularization_le hψ.upperSemicontinuous
      (fun x => iSup_le fun C => thetaRooftop_le_left θ ψ _ x)
  exact le_antisymm hupp (hexhaust.symm.le.trans hlow)

/-- WHOLE original corollary: every positive-real raw roof is genuinely
positive, and the ALL-QE relative envelope and its printed USC supremum equal ψ. -/
theorem sourcePOrder_relativeEnvelope (ω : KahlerBackground n M)
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (hψ : (ofFixedModel n M).IsThetaPSH θ ψ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    (hψpos : 0 < sourcePotentialNonPluripolarMeasure θ ψ hψ univ)
    (hP : GlobalPComparison.sourcePOrder (n := n) ψ φ) :
    (∀ C : ℝ, 0 < C → ∃ hr : (ofFixedModel n M).IsThetaPSH θ
        (thetaRooftop θ ψ (fun x => φ x + (C : EReal))),
      0 < sourcePotentialNonPluripolarMeasure θ
        (thetaRooftop θ ψ (fun x => φ x + (C : EReal))) hr univ) ∧
    sourceRelativeEnvelope θ φ ψ = uscSup (fun C : {C : ℝ // 0 < C} =>
      thetaRooftop θ ψ (fun x => φ x + (C.1 : EReal))) ∧
    uscSup (fun C : {C : ℝ // 0 < C} =>
      thetaRooftop θ ψ (fun x => φ x + (C.1 : EReal))) = ψ := by
  refine ⟨?_, ?_, sourcePOrder_relativeRooftop_exhaustion ω hφ hψ hφpos hψpos hP⟩
  · intro C hC
    obtain ⟨hr, _, _, hrpos⟩ :=
      sourcePOrder_shiftedRooftop_positive ω hφ hψ hφpos hψpos hP C hC.le
    exact ⟨hr, hrpos⟩
  · rw [sourceRelativeEnvelope_eq_uscSup_positive_rooftop θ φ ψ hψ]
    apply congrArg uscSup
    funext C
    exact thetaRooftop_comm θ _ _

end SGPT.PSH.VariableComplexAtlas
