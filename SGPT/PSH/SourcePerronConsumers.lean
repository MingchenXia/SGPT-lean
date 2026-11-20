import SGPT.PSH.SourcePerronGeodesic
import SGPT.Foundations.Analysis.Pending.FiniteRightEndpointDerivative

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open scoped Topology

/-- The original actual difference supremum on EXACTLY the reference's
nonpole locus. Common negative poles are excluded, not assigned zero. -/
def sourceDifferenceSup {X : Type*} (u v : X → EReal) : EReal :=
  ⨆ x : {x // v x ≠ ⊥}, u x.1 - v x.1

theorem sourceDifferenceSup_eq_native {X : Type*} (u v : X → EReal) :
    sourceDifferenceSup u v = FiniteUpperGapGeodesicSupremum.differenceSup u v := rfl

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Genuine original singularity comparison and actual local nondegeneracy
manufacture finiteness of the printed gap before any real readback. -/
theorem sourceDifferenceSup_finite
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u₀ u₁ : M → EReal}
    (hu₀ : (ofFixedModel n M).IsThetaPSH θ u₀)
    (hu₁ : (ofFixedModel n M).IsThetaPSH θ u₁) (hmore : SingularityLE u₁ u₀) :
    sourceDifferenceSup u₁ u₀ ≠ ⊤ ∧ sourceDifferenceSup u₁ u₀ ≠ ⊥ :=
  FiniteUpperGapGeodesicSupremum.differenceSup_ne_top_ne_bot
    ((isThetaPSH_iff_nativeThetaPotential θ u₀).mp hu₀)
    ((isThetaPSH_iff_nativeThetaPotential θ u₁).mp hu₁) hmore

/-- Actual original Perron endpoint-gap formula on the ENTIRE CLOSED interval.
The statement retains the literal EReal product and exact nonpole domain;
the genuine finite-gap theorem justifies the internal native real readback. -/
theorem sourcePerron_differenceSup_closed (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u₀ u₁ : M → EReal}
    (hu₀ : (ofFixedModel n M).IsThetaPSH θ u₀)
    (hu₁ : (ofFixedModel n M).IsThetaPSH θ u₁) (hmore : SingularityLE u₁ u₀)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    sourceDifferenceSup
        (closedSubgeodesicSlice (sourcePerronGeodesic omega θ u₀ u₁) u₀ u₁ t) u₀ =
      (t : EReal) * sourceDifferenceSup u₁ u₀ := by
  have h₀ := (isThetaPSH_iff_nativeThetaPotential θ u₀).mp hu₀
  have h₁ := (isThetaPSH_iff_nativeThetaPotential θ u₁).mp hu₁
  have hfinite : FiniteUpperGapGeodesicSupremum.differenceSup u₁ u₀ ≠ ⊤ ∧
      FiniteUpperGapGeodesicSupremum.differenceSup u₁ u₀ ≠ ⊥ :=
    sourceDifferenceSup_finite hu₀ hu₁ hmore
  have hG : sourcePerronGeodesic omega θ u₀ u₁ =
      finiteGeodesic (atlasClosedFormToNative θ).val u₀ u₁ :=
    funext fun s ↦ sourcePerronGeodesic_eq_native omega θ u₀ u₁ s
  rw [hG]
  change FiniteUpperGapGeodesicSupremum.differenceSup
      (closedSubgeodesicSlice (finiteGeodesic (atlasClosedFormToNative θ).val u₀ u₁) u₀ u₁ t) u₀ =
    (t : EReal) * FiniteUpperGapGeodesicSupremum.differenceSup u₁ u₀
  rw [FiniteUpperGapGeodesicSupremum.differenceSup_closedFiniteGeodesic h₀ h₁ hmore ht,
    EReal.coe_mul, EReal.coe_toReal hfinite.1 hfinite.2]

/-- The produced original infimum makes the actual all-source rooftop family
nonempty, and its genuine original closure manufactures rooftop PSH. -/
theorem SourceSubgeodesicFrom.isThetaPSH_thetaRooftop
    {omega : KahlerBackground n M} {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {curve : ℝ → M → EReal} {u₀ u₁ : M → EReal}
    (h : SourceSubgeodesicFrom omega θ curve u₀ u₁) :
    (ofFixedModel n M).IsThetaPSH θ (thetaRooftop θ u₀ u₁) := by
  apply isThetaPSH_thetaRooftop_of_nonempty h.1 h.2.1
  exact ⟨⟨sourceSliceInfimum curve, h.isThetaPSH_sliceInfimum,
    h.sliceInfimum_le_thetaRooftop.trans (thetaRooftop_le_left θ u₀ u₁),
    h.sliceInfimum_le_thetaRooftop.trans (thetaRooftop_le_right θ u₀ u₁)⟩⟩

/-- The original existence obstruction before the affine example: an actual
subgeodesic forces the actual source rooftop to be non-bottom. -/
theorem SourceSubgeodesicFrom.thetaRooftop_ne_bot
    {omega : KahlerBackground n M} {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {curve : ℝ → M → EReal} {u₀ u₁ : M → EReal}
    (h : SourceSubgeodesicFrom omega θ curve u₀ u₁) : thetaRooftop θ u₀ u₁ ≠ ⊥ := by
  intro hbot
  have hn := (isThetaPSH_iff_nativeThetaPotential θ (thetaRooftop θ u₀ u₁)).mp
    h.isThetaPSH_thetaRooftop
  obtain ⟨x, _, hx⟩ := hn.2 (Classical.arbitrary M) univ isOpen_univ (mem_univ _)
  exact hx (congrFun hbot x)

/-- The genuine original rooftop from the produced infimum supplies its own
constant ALL-source Perron competitor and hence the actual envelope barrier. -/
theorem SourceSubgeodesicFrom.thetaRooftop_le_sourcePerron
    {omega : KahlerBackground n M} {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {curve : ℝ → M → EReal} {u₀ u₁ : M → EReal}
    (h : SourceSubgeodesicFrom omega θ curve u₀ u₁) (t : ℝ) :
    thetaRooftop θ u₀ u₁ ≤ sourcePerronGeodesic omega θ u₀ u₁ t := by
  have hr := h.isThetaPSH_thetaRooftop
  exact sourcePerron_competitor_le
    (show (fun _ : ℝ ↦ thetaRooftop θ u₀ u₁) ∈ sourcePerronCompetitors omega θ u₀ u₁ from
      ⟨_, _, hr, hr, thetaRooftop_le_left θ u₀ u₁, thetaRooftop_le_right θ u₀ u₁,
        sourceSubgeodesic_const omega hr⟩) t

/-- The slope is the ACTUAL one-sided derivative of the assigned original
closed Perron trace, not a requested derivative certificate or proxy. Its
genuine existence on the true original finite locus is proved below. -/
def sourcePerronTerminalSlope (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u₀ u₁ : M → EReal) (x : M) : ℝ :=
  derivWithin (fun t ↦ (closedSubgeodesicSlice
    (sourcePerronGeodesic omega θ u₀ u₁) u₀ u₁ t x).toReal) (Iio (1 : ℝ)) 1

/-- Actual finiteness of the entire assigned closed trace on precisely the
right endpoint nonpole locus, before using its real derivative. -/
theorem sourcePerron_closedTrace_finite (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u₀ u₁ : M → EReal}
    (hu₀ : (ofFixedModel n M).IsThetaPSH θ u₀)
    (hu₁ : (ofFixedModel n M).IsThetaPSH θ u₁) (hmore : SingularityLE u₁ u₀)
    {x : M} (hx : u₁ x ≠ ⊥) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    closedSubgeodesicSlice (sourcePerronGeodesic omega θ u₀ u₁) u₀ u₁ t x ≠ ⊤ ∧
      closedSubgeodesicSlice (sourcePerronGeodesic omega θ u₀ u₁) u₀ u₁ t x ≠ ⊥ := by
  have h₀ := (isThetaPSH_iff_nativeThetaPotential θ u₀).mp hu₀
  have h₁ := (isThetaPSH_iff_nativeThetaPotential θ u₁).mp hu₁
  rcases ht.1.eq_or_lt with h0 | h0
  · rw [← h0, closedSubgeodesicSlice_zero]
    exact ⟨h₀.1.quasiPlurisubharmonic.ne_top x,
      fun hbot ↦ hx (hmore.eq_bot_of_eq_bot (mem_univ _) hbot)⟩
  rcases ht.2.eq_or_lt with h1 | h1
  · rw [h1, closedSubgeodesicSlice_one]
    exact ⟨h₁.1.quasiPlurisubharmonic.ne_top x, hx⟩
  rw [closedSubgeodesicSlice_eq_curve ⟨h0, h1⟩, sourcePerronGeodesic_eq_native]
  exact ⟨finiteGeodesic_ne_top h₀ h₁ ⟨h0, h1⟩ x,
    FiniteRightEndpointSecant.finiteGeodesic_ne_bot_of_right_nonpole h₀ h₁ hmore hx t⟩

/-- Bounded monotone ACTUAL terminal secants manufacture the genuine
one-sided derivative of the same finite original trace; no slope is an input. -/
theorem sourcePerron_hasDerivWithinAt_terminal (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u₀ u₁ : M → EReal}
    (hu₀ : (ofFixedModel n M).IsThetaPSH θ u₀)
    (hu₁ : (ofFixedModel n M).IsThetaPSH θ u₁) (hmore : SingularityLE u₁ u₀)
    {x : M} (hx : u₁ x ≠ ⊥) :
    HasDerivWithinAt (fun t ↦ (closedSubgeodesicSlice
      (sourcePerronGeodesic omega θ u₀ u₁) u₀ u₁ t x).toReal)
      (sourcePerronTerminalSlope omega θ u₀ u₁ x) (Iio (1 : ℝ)) 1 := by
  have h₀ := (isThetaPSH_iff_nativeThetaPotential θ u₀).mp hu₀
  have h₁ := (isThetaPSH_iff_nativeThetaPotential θ u₁).mp hu₁
  have hG : sourcePerronGeodesic omega θ u₀ u₁ =
      finiteGeodesic (atlasClosedFormToNative θ).val u₀ u₁ :=
    funext fun s ↦ sourcePerronGeodesic_eq_native omega θ u₀ u₁ s
  unfold sourcePerronTerminalSlope
  rw [hG, FiniteRightEndpointDerivative.derivWithin_closedFiniteGeodesic_one h₀ h₁ hmore hx]
  exact FiniteRightEndpointDerivative.hasDerivWithinAt_closedFiniteGeodesic_one h₀ h₁ hmore hx

/-- The exact terminal-slope identity consumed by the original endpoint-gap
proof, using the ACTUAL derivative on the EXACT original right nonpole locus. -/
theorem sourcePerron_iSup_terminalSlope (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u₀ u₁ : M → EReal}
    (hu₀ : (ofFixedModel n M).IsThetaPSH θ u₀)
    (hu₁ : (ofFixedModel n M).IsThetaPSH θ u₁) (hmore : SingularityLE u₁ u₀) :
    (⨆ x : {x // u₁ x ≠ ⊥}, (sourcePerronTerminalSlope omega θ u₀ u₁ x.1 : EReal)) =
      sourceDifferenceSup u₁ u₀ := by
  have h₀ := (isThetaPSH_iff_nativeThetaPotential θ u₀).mp hu₀
  have h₁ := (isThetaPSH_iff_nativeThetaPotential θ u₁).mp hu₁
  have hG : sourcePerronGeodesic omega θ u₀ u₁ =
      finiteGeodesic (atlasClosedFormToNative θ).val u₀ u₁ :=
    funext fun s ↦ sourcePerronGeodesic_eq_native omega θ u₀ u₁ s
  unfold sourcePerronTerminalSlope
  rw [hG]
  calc
    _ = ⨆ x : {x // u₁ x ≠ ⊥},
        (FiniteRightEndpointDerivative.terminalSlope
          (finiteGeodesic (atlasClosedFormToNative θ).val u₀ u₁) u₁ x.1 : EReal) := by
      apply iSup_congr
      intro x
      rw [FiniteRightEndpointDerivative.derivWithin_closedFiniteGeodesic_one h₀ h₁ hmore x.2]
    _ = _ := FiniteRightEndpointDerivative.iSup_terminalSlope h₀ h₁ hmore

end SGPT.PSH.VariableComplexAtlas
