import SGPT.Okounkov.ValGenInfty
import SGPT.Okounkov.PartialBodyDS

/-!
# Continuity and monotonicity of partial Okounkov bodies for an arbitrary valuation

Lane VAL-GEN, blueprint `claude-val-gen.tex`. Source: chapter *The theory of Okounkov bodies*,
Section *Algebraic partial Okounkov bodies* (`sec:PoB`), `thm:Okoucont` and
`prop:IcompimplyDeltacomp`, for an **arbitrary** valuation `ν : ℂ(X)^× → ℤⁿ`.

Setting of `SGPT.Okounkov.ValGen` (`ValGenInfty`): `X` of dimension `n = m + 1` carrying a smooth
flag, `L` with atlas `a` and smooth metric `H`, `θ = c₁(L, H)`, an arbitrary valuation `v` with
section values at `c`, and `Γ(L) ∈ 𝒮'(C)` for `v` (source `prop:Okounbiglbdl`, an explicit
hypothesis). `Δ_ν(θ, φ)` is `SGPT.Okounkov.ValGen.partialBody` (source `def:Okounkov:L687`).

* **`tendsto_dist_multiplierConeSubset_of_tendsto`**: if `φ_i → φ` in `d_S` (`{θ}` big,
  `∫_X θ_φⁿ > 0`), then `d_sg(Γ(θ, φ_i), Γ(θ, φ)) → 0`. As in the source (`d_sg` of nested
  section sets is a difference of volumes, `thm:DXmain1`), with the maxima `max(φ_i, φ)`
  (`d_sg ≤ 2 vol θ_{max(φ_i,φ)}/n! - vol θ_{φ_i}/n! - vol θ_φ/n!`) and `thm:contvolu`.
* **`exists_continuous_partialBody`** (source `thm:Okoucont`): the map
  `(PSH(X, θ)_{>0}, d_S) → (𝒦ₙ, d_Haus)`, `φ ↦ Δ_ν(θ, φ)` is continuous.
* **`partialBody_subset_of_iOrder`** (source `prop:IcompimplyDeltacomp`): for
  `φ, ψ ∈ PSH(X, θ)_{>0}` with `φ ⪯_𝓘 ψ`, `Δ_ν(θ, φ) ⊆ Δ_ν(θ, ψ)`, and
  `partialBody_subset_okounkovBody'`: `Δ_ν(θ, φ) ⊆ Δ_ν(L)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Okounkov.ValGen

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Okounkov.AlgebraicValuation SGPT.LineBundle SGPT.PSH SGPT.AlmostSemigroup
open SGPT.AlmostSemigroup.Class SGPT.AlmostSemigroup.Okounkov SGPT.AlmostSemigroup.OkounkovExtension
open SGPT.Foundations.Analysis.Pending.DiagonalMass SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology
  SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDistance
open scoped Topology ENNReal

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f] [IsSeparated f] [QuasiCompact f]

local instance valGenContTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance valGenContCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance valGenContManifold :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
  (c : X) (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))

include Y hY in
/-- `vol Δ_{Y•}(θ_φ) = vol θ_φ / n!` is continuous along `d_S`-convergent families with
positive-mass limit (`thm:contvolu`). -/
theorem tendsto_volume_generalPartialBody [Nonempty (SchemeComplexPoint f)]
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
    {ι : Type*} (l : Filter ι) (u : ι → ThetaPshL1 (H.curvature a).val)
    (w : ThetaPshL1 (H.curvature a).val)
    (hw : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      HasPositivePotentialMass (H.curvature a) w.val w.property)
    (hlim : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      haveI : ConnectedSpace (SchemeComplexPoint f) :=
        schemeSmoothFlag_connectedSpace f (m + 1) Y hY;
      Tendsto u l (@nhds (ThetaPshL1 (H.curvature a).val)
        (singularityPseudoMetricSpace (schemeProjectiveTNKahlerBackground f (m + 1) E)
          (H.curvature a) hbig).toUniformSpace.toTopologicalSpace w)) :
    Tendsto (fun i => volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) (u i).val)) l
      (𝓝 (volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) w.val))) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
  have hiv := PartialBody.tendsto_iVolume_of_tendsto (schemeProjectiveTNKahlerBackground f (m + 1) E)
    (H.curvature a) hbig l u w hw hlim
  have hreal := (ENNReal.tendsto_toReal (PartialBody.iVolume_ne_top
    (schemeProjectiveTNKahlerBackground f (m + 1) E) w.property)).comp hiv
  have h := hreal.div_const ((m + 1).factorial : ℝ)
  simp only [Function.comp_def] at h
  rw [AlgPOB.volume_real_generalPartialBody f E Y hY a H w.property]
  refine h.congr fun i => ?_
  rw [AlgPOB.volume_real_generalPartialBody f E Y hY a H (u i).property]

include Y hY in
/-- **`d_S`-continuity of `Γ(θ, ·)` for the valuation `v`** (the core of source `thm:Okoucont`):
if `φ_i → φ` in `d_S` and `∫_X θ_φⁿ > 0`, then `d_sg(Γ(θ, φ_i), Γ(θ, φ)) → 0`. -/
theorem tendsto_dist_multiplierConeSubset_of_tendsto [Nonempty (SchemeComplexPoint f)]
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
    {C : AdmissibleCone (m + 1)}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤)
    {ι : Type*} (l : Filter ι) (u : ι → ThetaPshL1 (H.curvature a).val)
    (w : ThetaPshL1 (H.curvature a).val)
    (hw : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      HasPositivePotentialMass (H.curvature a) w.val w.property)
    (hlim : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      haveI : ConnectedSpace (SchemeComplexPoint f) :=
        schemeSmoothFlag_connectedSpace f (m + 1) Y hY;
      Tendsto u l (@nhds (ThetaPshL1 (H.curvature a).val)
        (singularityPseudoMetricSpace (schemeProjectiveTNKahlerBackground f (m + 1) E)
          (H.curvature a) hbig).toUniformSpace.toTopologicalSpace w)) :
    Tendsto (fun i => dist (multiplierConeSubset f E a c v hS (u i).val)
      (multiplierConeSubset f E a c v hS w.val)) l (𝓝 0) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
  let Vf : (SchemeComplexPoint f → EReal) → ℝ :=
    fun φ => volume.real (PartialBody.generalPartialBody
      (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ)
  let Z : ι → ThetaPshL1 (H.curvature a).val := fun i =>
    ⟨fun x => max ((u i).val x) (w.val x), IsThetaPshPotential.max (u i).property w.property⟩
  have hZ : Tendsto Z l (@nhds (ThetaPshL1 (H.curvature a).val)
      (singularityPseudoMetricSpace (schemeProjectiveTNKahlerBackground f (m + 1) E)
        (H.curvature a) hbig).toUniformSpace.toTopologicalSpace w) :=
    ((SingularCanonicalSingularityMaximumCriterion.tendsto_native_iff_max_and_endpointMixedMass
      (schemeProjectiveTNKahlerBackground f (m + 1) E) (H.curvature a) hbig l u w).mp hlim).1
  have hVu := tendsto_volume_generalPartialBody f E Y hY a H hbig l u w hw hlim
  have hVZ := tendsto_volume_generalPartialBody f E Y hY a H hbig l Z w hw hZ
  have hbound : ∀ i, dist (multiplierConeSubset f E a c v hS (u i).val)
      (multiplierConeSubset f E a c v hS w.val) ≤
        (Vf (Z i).val - Vf (u i).val) + (Vf (Z i).val - Vf w.val) := by
    intro i
    have hZθ : IsThetaPshPotential (H.curvature a).val (Z i).val := (Z i).property
    have hTZ := tendsto_normalizedCardinality_multiplierSectionSet f E Y hY a H c v hS hG hZθ
    have h1 := dist_multiplierConeSubset_eq_of_subset f E a c v hS
      (multiplierSectionSet_mono_of_le f E a c v hZθ.1.quasiPlurisubharmonic
        (fun x => le_max_left ((u i).val x) (w.val x)))
      (tendsto_normalizedCardinality_multiplierSectionSet f E Y hY a H c v hS hG (u i).property)
      hTZ
    have h2 := dist_multiplierConeSubset_eq_of_subset f E a c v hS
      (multiplierSectionSet_mono_of_le f E a c v hZθ.1.quasiPlurisubharmonic
        (fun x => le_max_right ((u i).val x) (w.val x)))
      (tendsto_normalizedCardinality_multiplierSectionSet f E Y hY a H c v hS hG w.property)
      hTZ
    calc dist (multiplierConeSubset f E a c v hS (u i).val)
          (multiplierConeSubset f E a c v hS w.val)
        ≤ dist (multiplierConeSubset f E a c v hS (u i).val)
            (multiplierConeSubset f E a c v hS (Z i).val) +
          dist (multiplierConeSubset f E a c v hS (Z i).val)
            (multiplierConeSubset f E a c v hS w.val) := dist_triangle _ _ _
      _ = _ := by rw [h1, dist_comm, h2]
  have hlim0 : Tendsto (fun i => (Vf (Z i).val - Vf (u i).val) + (Vf (Z i).val - Vf w.val)) l
      (𝓝 ((Vf w.val - Vf w.val) + (Vf w.val - Vf w.val))) :=
    ((hVZ.sub hVu).add (hVZ.sub tendsto_const_nhds))
  simp only [sub_self, add_zero] at hlim0
  exact squeeze_zero (fun i => dist_nonneg) hbound hlim0

include Y hY in
/-- Positive mass gives `vol Δ_{Y•}(θ_φ) > 0`, hence (`thm:Gammaasg` for `v`) `Γ(θ, φ)` is an
almost semigroup. -/
theorem multiplierConeSubset_mem_almostSemigroupLocus_of_mass [Nonempty (SchemeComplexPoint f)]
    {C : AdmissibleCone (m + 1)}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hmass : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      HasPositivePotentialMass (H.curvature a) φ hφ) :
    multiplierConeSubset f E a c v hS φ ∈ almostSemigroupLocus C := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : MeasurableSpace (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY).carrier :=
    borel (SchemeComplexPoint f)
  have : BorelSpace (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY).carrier := ⟨rfl⟩
  have hpos := PartialBody.volume_generalPartialBody_pos
    (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hφ hmass
  have hfin := (PartialBody.convex_isCompact_generalPartialBody
    (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hφ).2.measure_lt_top
    (μ := (volume : Measure (Fin (m + 1) → ℝ))) |>.ne
  have hpos' : 0 < volume.real (PartialBody.generalPartialBody
      (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) :=
    ENNReal.toReal_pos hpos.ne' hfin
  exact (multiplierConeSubset_mem_almostSemigroupLocus f E Y hY a H c v hS hG hφ hpos').1

include Y hY in
/-- **Source `thm:Okoucont` for an arbitrary valuation `ν = v`**: for a big class `{θ}` and under
`Γ(L) ∈ 𝒮'(C)` for `v` (source `prop:Okounbiglbdl`), the partial Okounkov body map
`(PSH(X, θ)_{>0}, d_S) → (𝒦ₙ, d_Haus)`, `φ ↦ Δ_ν(θ, φ)`, is continuous: there is a continuous map
`G` to the convex bodies (Hausdorff metric) with `G φ = Δ_ν(θ, φ)`. -/
theorem exists_continuous_partialBody [Nonempty (SchemeComplexPoint f)]
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
    {C : AdmissibleCone (m + 1)}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
    letI : TopologicalSpace (ThetaPshL1 (H.curvature a).val) :=
      (singularityPseudoMetricSpace (schemeProjectiveTNKahlerBackground f (m + 1) E)
        (H.curvature a) hbig).toUniformSpace.toTopologicalSpace
    ∃ G : {w : ThetaPshL1 (H.curvature a).val //
        HasPositivePotentialMass (H.curvature a) w.val w.property} →
        ConvexBody (EuclideanSpace ℝ (Fin (m + 1))),
      Continuous G ∧ ∀ w, (G w : Set (EuclideanSpace ℝ (Fin (m + 1)))) =
        partialBody f (m + 1) E v c a C w.val.val := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
  let : TopologicalSpace (ThetaPshL1 (H.curvature a).val) :=
    (singularityPseudoMetricSpace (schemeProjectiveTNKahlerBackground f (m + 1) E)
      (H.curvature a) hbig).toUniformSpace.toTopologicalSpace
  let g : {w : ThetaPshL1 (H.curvature a).val //
      HasPositivePotentialMass (H.curvature a) w.val w.property} → AlmostSpace C := fun w =>
    ⟨multiplierConeSubset f E a c v hS w.val.val,
      multiplierConeSubset_mem_almostSemigroupLocus_of_mass f E Y hY a H c v hS hG
        w.val.property w.property⟩
  refine ⟨fun w => bodyExtension (g w), (continuous_bodyExtension C).comp ?_, fun w => ?_⟩
  · rw [continuous_iff_continuousAt]
    intro w
    rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
    have h := tendsto_dist_multiplierConeSubset_of_tendsto f E Y hY a H c v hbig hS hG (𝓝 w)
      (fun x => x.val) w.val w.property (continuous_subtype_val.tendsto w)
    exact h
  · exact (partialBody_eq a _ _ (g w).property).symm

include Y hY in
/-- **Source `prop:IcompimplyDeltacomp` for an arbitrary valuation `ν = v`**: under
`Γ(L) ∈ 𝒮'(C)` for `v`, for `φ, ψ ∈ PSH(X, θ)` with `vol θ_φ, vol θ_ψ > 0` and `φ ⪯_𝓘 ψ`,
`Δ_ν(θ, φ) ⊆ Δ_ν(θ, ψ)`; in particular `Δ_ν(θ, φ) ⊆ Δ_ν(L)`. -/
theorem partialBody_subset_of_iOrder [Nonempty (SchemeComplexPoint f)]
    {C : AdmissibleCone (m + 1)}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤)
    {φ ψ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hψ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val ψ)
    (hφpos : 0 < volume.real (PartialBody.generalPartialBody
      (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ))
    (hψpos : 0 < volume.real (PartialBody.generalPartialBody
      (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) ψ))
    (hI : letI := E.isSeparated; letI := E.quasiCompact; IOrderOnManifold (n := m + 1) φ ψ) :
    partialBody f (m + 1) E v c a C φ ⊆ partialBody f (m + 1) E v c a C ψ ∧
      partialBody f (m + 1) E v c a C φ ⊆
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm '' okounkovBody v c a := by
  let := E.isSeparated
  let := E.quasiCompact
  have hmφ := (multiplierConeSubset_mem_almostSemigroupLocus f E Y hY a H c v hS hG hφ hφpos).1
  have hmψ := (multiplierConeSubset_mem_almostSemigroupLocus f E Y hY a H c v hS hG hψ hψpos).1
  refine ⟨partialBody_mono a (fun k hk => SGPT.Okounkov.multiplierIdeal_le_of_iOrderOnManifold hI
    (by exact_mod_cast hk)) ⟨_, hmφ⟩ ⟨_, hmψ⟩, partialBody_subset_okounkovBody a hS hG ⟨_, hmφ⟩⟩

end SGPT.Okounkov.ValGen
