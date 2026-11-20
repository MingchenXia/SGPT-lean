import SGPT.Envelopes.SourceOrdinaryEnvelopeMassModel
import SGPT.PSH.SourceMixedPOrderMonotonicity
import SGPT.PSH.SourcePMassCharacterization

/-! # Original rooftops under global P-equivalence

The full original proposition retains genuine source theta-PSH endpoints,
the actual raw source roofs, and both true global orders. Positive output
mass and genuine unprimed rooftop are produced from the primed input.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

omit [ConnectedSpace M] in
/-- A genuine lower source roof and ordinary endpoint comparisons manufacture
an actual genuine upper roof, its ordinary comparison, and its mass bound. -/
theorem sourceThetaRooftop_upward_of_singularityLE (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u v a b : M → EReal}
    (ha : (ofFixedModel n M).IsThetaPSH θ a) (hb : (ofFixedModel n M).IsThetaPSH θ b)
    (hr : (ofFixedModel n M).IsThetaPSH θ (thetaRooftop θ u v))
    (hua : SGPT.PSH.SingularityLE u a) (hvb : SGPT.PSH.SingularityLE v b) :
    ∃ hR : (ofFixedModel n M).IsThetaPSH θ (thetaRooftop θ a b),
      SGPT.PSH.SingularityLE (thetaRooftop θ u v) (thetaRooftop θ a b) ∧
      sourcePotentialNonPluripolarMeasure θ (thetaRooftop θ u v) hr univ ≤
        sourcePotentialNonPluripolarMeasure θ (thetaRooftop θ a b) hR univ := by
  obtain ⟨c, huc, hvc⟩ := sourcePreceqPair_common_shift hua hvb
  let w : M → EReal := fun x => thetaRooftop θ u v x + (c : EReal)
  have hw : (ofFixedModel n M).IsThetaPSH θ w := sourceThetaPSH_add_const hr c
  have hwa : w ≤ a := fun x =>
    (add_le_add (thetaRooftop_le_left θ u v x) le_rfl).trans (huc x)
  have hwb : w ≤ b := fun x =>
    (add_le_add (thetaRooftop_le_right θ u v x) le_rfl).trans (hvc x)
  have hR := isThetaPSH_thetaRooftop_of_nonempty ha hb ⟨⟨w, hw, hwa, hwb⟩⟩
  have hwR := le_thetaRooftop hw hwa hwb
  have hrR : SGPT.PSH.SingularityLE (thetaRooftop θ u v) (thetaRooftop θ a b) :=
    ⟨-c, fun x _ => (RelativePreceqClasses.add_coe_le_iff _ _ c).mp (hwR x)⟩
  exact ⟨hR, hrR, sourcePotentialNonPluripolarMass_mono ω hr hR hrR⟩

/-- Whole original `prop:rooftopprePequiv`: manufacture the same unprimed
positive genuine roof and BOTH global P-orders; the actual roof masses agree. -/
theorem sourceThetaRooftop_of_sourcePEquivalent (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u v u' v' : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hu' : (ofFixedModel n M).IsThetaPSH θ u') (hv' : (ofFixedModel n M).IsThetaPSH θ v')
    (huu' : GlobalPComparison.sourcePEquivalent (n := n) u u')
    (hvv' : GlobalPComparison.sourcePEquivalent (n := n) v v')
    (hr' : (ofFixedModel n M).IsThetaPSH θ (thetaRooftop θ u' v'))
    (hr'pos : 0 < sourcePotentialNonPluripolarMeasure θ (thetaRooftop θ u' v') hr' univ) :
    ∃ hr : (ofFixedModel n M).IsThetaPSH θ (thetaRooftop θ u v),
      0 < sourcePotentialNonPluripolarMeasure θ (thetaRooftop θ u v) hr univ ∧
      GlobalPComparison.sourcePEquivalent (n := n)
        (thetaRooftop θ u v) (thetaRooftop θ u' v') ∧
      sourcePotentialNonPluripolarMeasure θ (thetaRooftop θ u v) hr univ =
        sourcePotentialNonPluripolarMeasure θ (thetaRooftop θ u' v') hr' univ := by
  have hmu : sourcePotentialNonPluripolarMeasure θ u hu univ =
      sourcePotentialNonPluripolarMeasure θ u' hu' univ := by
    simpa only [sourceMixedNonPluripolarMass_diagonal] using
      (sourceMixedNonPluripolarMass_eq_of_sourcePEquivalent ω
        (fun _ : Fin n => hu) (fun _ => hu') (fun _ => huu'))
  have hmv : sourcePotentialNonPluripolarMeasure θ v hv univ =
      sourcePotentialNonPluripolarMeasure θ v' hv' univ := by
    simpa only [sourceMixedNonPluripolarMass_diagonal] using
      (sourceMixedNonPluripolarMass_eq_of_sourcePEquivalent ω
        (fun _ : Fin n => hv) (fun _ => hv') (fun _ => hvv'))
  have hu'pos : 0 < sourcePotentialNonPluripolarMeasure θ u' hu' univ :=
    lt_of_lt_of_le hr'pos (sourcePotentialNonPluripolarMass_mono ω hr' hu'
      (MoreSingularOn.of_le fun x _ => thetaRooftop_le_left θ u' v' x))
  have hv'pos : 0 < sourcePotentialNonPluripolarMeasure θ v' hv' univ :=
    lt_of_lt_of_le hr'pos (sourcePotentialNonPluripolarMass_mono ω hr' hv'
      (MoreSingularOn.of_le fun x _ => thetaRooftop_le_right θ u' v' x))
  have hupos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ := hmu ▸ hu'pos
  have hvpos : 0 < sourcePotentialNonPluripolarMeasure θ v hv univ := hmv ▸ hv'pos
  let T := atlasClosedFormToNative θ
  have hnu := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have hnv := (isThetaPSH_iff_nativeThetaPotential θ v).mp hv
  have hnu' := (isThetaPSH_iff_nativeThetaPotential θ u').mp hu'
  have hnv' := (isThetaPSH_iff_nativeThetaPotential θ v').mp hv'
  have hPu : sourceSingularityEnvelope θ u = sourceSingularityEnvelope θ u' := by
    simp only [sourceSingularityEnvelope_eq_native]
    exact FirstPass.POrder.pEquivalentWith_iff_envelope_eq.mp
      ((SingularGlobalPOrder.sourcePEquivalent_iff_pEquivalentWith ω T
        hnu hnu' hupos hu'pos).mp huu')
  have hPv : sourceSingularityEnvelope θ v = sourceSingularityEnvelope θ v' := by
    simp only [sourceSingularityEnvelope_eq_native]
    exact FirstPass.POrder.pEquivalentWith_iff_envelope_eq.mp
      ((SingularGlobalPOrder.sourcePEquivalent_iff_pEquivalentWith ω T
        hnv hnv' hvpos hv'pos).mp hvv')
  let a := sourceSingularityEnvelope θ u
  let b := sourceSingularityEnvelope θ v
  have ha : (ofFixedModel n M).IsThetaPSH θ a := sourceOrdinaryEnvelope_genuine hu
  have hb : (ofFixedModel n M).IsThetaPSH θ b := sourceOrdinaryEnvelope_genuine hv
  have hua : SGPT.PSH.SingularityLE u a := by
    simpa only [a, SGPT.PSH.SingularityLE, sourceSingularityEnvelope_eq_native] using
      (moreSingularOn_singularityEnvelope hnu)
  have hvb : SGPT.PSH.SingularityLE v b := by
    simpa only [b, SGPT.PSH.SingularityLE, sourceSingularityEnvelope_eq_native] using
      (moreSingularOn_singularityEnvelope hnv)
  have hu'a : SGPT.PSH.SingularityLE u' a := by
    change SGPT.PSH.SingularityLE u' (sourceSingularityEnvelope θ u)
    rw [hPu]
    simpa only [SGPT.PSH.SingularityLE, sourceSingularityEnvelope_eq_native] using
      (moreSingularOn_singularityEnvelope hnu')
  have hv'b : SGPT.PSH.SingularityLE v' b := by
    change SGPT.PSH.SingularityLE v' (sourceSingularityEnvelope θ v)
    rw [hPv]
    simpa only [SGPT.PSH.SingularityLE, sourceSingularityEnvelope_eq_native] using
      (moreSingularOn_singularityEnvelope hnv')
  obtain ⟨hR, hr'R, hmr'R⟩ :=
    sourceThetaRooftop_upward_of_singularityLE ω ha hb hr' hu'a hv'b
  have hRpos : 0 < sourcePotentialNonPluripolarMeasure θ (thetaRooftop θ a b) hR univ :=
    lt_of_lt_of_le hr'pos hmr'R
  have hma : sourcePotentialNonPluripolarMeasure θ a ha univ =
      sourcePotentialNonPluripolarMeasure θ u hu univ :=
    sourceOrdinaryEnvelope_diagonalMass_eq ω hu
  have hmb : sourcePotentialNonPluripolarMeasure θ b hb univ =
      sourcePotentialNonPluripolarMeasure θ v hv univ :=
    sourceOrdinaryEnvelope_diagonalMass_eq ω hv
  obtain ⟨hr'₂, _, hmr'⟩ := sourceThetaRooftop_fullMass_transfer ω ha hb hR hRpos
    hu' hv' hu'a hv'b (hmu.symm.trans hma.symm) (hmv.symm.trans hmb.symm)
  have hmr'₀ : sourcePotentialNonPluripolarMeasure θ (thetaRooftop θ u' v') hr' univ =
      sourcePotentialNonPluripolarMeasure θ (thetaRooftop θ a b) hR univ := hmr'
  obtain ⟨hr, _, hmr⟩ := sourceThetaRooftop_fullMass_transfer ω ha hb hR hRpos
    hu hv hua hvb hma.symm hmb.symm
  have hrpos : 0 < sourcePotentialNonPluripolarMeasure θ (thetaRooftop θ u v) hr univ :=
    hmr ▸ hRpos
  obtain ⟨_, hrR, _⟩ := sourceThetaRooftop_upward_of_singularityLE ω ha hb hr hua hvb
  have hnr := (isThetaPSH_iff_nativeThetaPotential θ _).mp hr
  have hnr' := (isThetaPSH_iff_nativeThetaPotential θ _).mp hr'
  have hnR := (isThetaPSH_iff_nativeThetaPotential θ _).mp hR
  have hrPR := SingularGlobalPOrder.sourcePOrder_of_moreSingularOn ω T T hnr hnR hrR
  have hr'PR := SingularGlobalPOrder.sourcePOrder_of_moreSingularOn ω T T hnr' hnR hr'R
  have hrEqR := (sourcePEquivalent_iff_diagonalMass_eq_of_positive
    ω hr hR hrpos hRpos hrPR).mpr hmr
  have hr'EqR := (sourcePEquivalent_iff_diagonalMass_eq_of_positive
    ω hr' hR hr'pos hRpos hr'PR).mpr hmr'₀
  exact ⟨hr, hrpos,
    ⟨GlobalPComparison.sourcePOrder_trans ω hrEqR.1 hr'EqR.2,
      GlobalPComparison.sourcePOrder_trans ω hr'EqR.1 hrEqR.2⟩,
    hmr.trans hmr'₀.symm⟩

end SGPT.PSH.VariableComplexAtlas
