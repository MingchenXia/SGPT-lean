import SGPT.Okounkov.AlgPOBComparison
import SGPT.Okounkov.ValuativeTestCurve
import SGPT.Okounkov.PartialBodyDSRepresentative

/-!
# Properties of the algebraic partial Okounkov bodies, from the transcendental theory

Source: chapter *The theory of Okounkov bodies*, Section *Algebraic partial Okounkov bodies*:
`cor:POBvolume`, `prop:Okocurrent`, `prop:IcompimplyDeltacomp`, `thm:Okoucont`, `thm:concOko`.

By `SGPT.Okounkov.AlgPOB.partialOkounkovBody_eq_generalPartialBody_of_lowerBound`, under the lower
bound of `thm:DXmain1` (`SGPT.IGood.DXMain.DXMainLowerBound`, not proved in the workspace) the
algebraic partial Okounkov body `Δ_{Y•}(θ, φ) = Δ(Γ(θ, φ))` (`def:Okounkov:L687`, relative to a
large cube cone) is the Euclidean copy of the transcendental partial Okounkov body
`Δ_{Y•}(θ_φ)` of `def:generalPOB`. The properties below are transported from the corresponding
items of `thm:pobmain` (proved unconditionally): each statement carries the lower bound of
`thm:DXmain1` for the potentials involved as its only unproved hypothesis.

## Main results

* `volume_partialOkounkovBody_of_lowerBound` (`cor:POBvolume`).
* `partialOkounkovBody_subset_of_iOrder_of_lowerBound`,
  `partialOkounkovBody_subset_lineBundleOkounkovBody_of_lowerBound`
  (`prop:IcompimplyDeltacomp`).
* `exists_continuous_partialOkounkovBody_of_lowerBound` (`thm:Okoucont`).
* `partialOkounkovBody_eq_of_sameCurrent_of_lowerBound` (`prop:Okocurrent`).
* `convexComb_mem_partialOkounkovBody_of_lowerBound` (`thm:concOko` for rational `t`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.AlgPOB

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.LineBundle SGPT.PSH SGPT.AlmostSemigroup SGPT.AlmostSemigroup.Class
  SGPT.AlmostSemigroup.OkounkovExtension SGPT.IGood.DXMain
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus SGPT.Foundations.Analysis.Pending.DiagonalMass
  SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology
  SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDistance
open scoped Topology ENNReal NNReal Pointwise

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]

local instance algPOBPropTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance algPOBPropCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance algPOBPropManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)

/-- **The comparison in uniform form**: there is `C₀` such that for every `C ≥ C₀` and every
`φ ∈ PSH(X, θ)` with `vol Δ_{Y•}(θ_φ) > 0` satisfying the lower bound of `thm:DXmain1`, the
algebraic partial Okounkov body relative to `C([0, C]ⁿ)` is the Euclidean copy of `Δ_{Y•}(θ_φ)`. -/
theorem exists_partialOkounkovBody_eq_of_lowerBound [Nonempty (SchemeComplexPoint f)] :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ φ : SchemeComplexPoint f → EReal,
      ∀ hφ : (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val φ),
      0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) →
      DXMainLowerBound f E a H hφ →
      partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a φ =
        TranscendentalMain.euclideanImage (PartialBody.generalPartialBody
          (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_cubeCone_contains f E Y hY a H
  refine ⟨C₀, hC₀, fun C hC₀C φ hφ hpos hlow => ?_⟩
  obtain ⟨hsub, hKC⟩ := hC C hC₀C φ hφ
  exact partialOkounkovBody_eq_generalPartialBody_of_lowerBound f E Y hY a H hφ hpos hlow hsub hKC

/-- **Source `cor:POBvolume`, conditional on the lower bound of `thm:DXmain1`**:
`vol Δ_{Y•}(θ, φ) = vol θ_φ / n!` for `vol θ_φ > 0`. -/
theorem volume_partialOkounkovBody_of_lowerBound [Nonempty (SchemeComplexPoint f)] :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ φ : SchemeComplexPoint f → EReal,
      ∀ hφ : (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val φ),
      (letI := E.isSeparated; letI := E.quasiCompact;
        letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
        haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
        haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
        0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ) →
      DXMainLowerBound f E a H hφ →
      (letI := E.isSeparated; letI := E.quasiCompact;
        letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
        haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
        haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
        volume (partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a φ) =
          iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ /
            ((m + 1).factorial : ℝ≥0∞)) := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_partialOkounkovBody_eq_of_lowerBound f E Y hY a H
  refine ⟨C₀, hC₀, fun C hC₀C φ hφ hpos hlow => ?_⟩
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hpos' := volume_real_generalPartialBody_pos f E Y hY a H hφ hpos
  rw [hC C hC₀C φ hφ hpos' hlow, PartialBody.volume_euclideanImage]
  exact PartialBody.volume_generalPartialBody_uncond
    (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hφ

/-- **Source `prop:IcompimplyDeltacomp`, conditional on the lower bound of `thm:DXmain1`**: for
`φ, ψ ∈ PSH(X, θ)_{>0}` with `φ ⪯_𝓘 ψ`, `Δ_{Y•}(θ, φ) ⊆ Δ_{Y•}(θ, ψ)` (for all large cube cones). -/
theorem partialOkounkovBody_subset_of_iOrder_of_lowerBound [Nonempty (SchemeComplexPoint f)] :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ φ ψ : SchemeComplexPoint f → EReal,
      ∀ hφ : (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val φ),
      ∀ hψ : (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val ψ),
      0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) →
      0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) ψ) →
      DXMainLowerBound f E a H hφ → DXMainLowerBound f E a H hψ →
      (letI := E.isSeparated; letI := E.quasiCompact;
        SGPT.Foundations.Analysis.FirstPass.IEnvelope.IOrderOnManifold (n := m + 1) φ ψ) →
      partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a φ ⊆
        partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a ψ := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_partialOkounkovBody_eq_of_lowerBound f E Y hY a H
  refine ⟨C₀, hC₀, fun C hC₀C φ ψ hφ hψ hposφ hposψ hlowφ hlowψ hI => ?_⟩
  let := E.isSeparated
  let := E.quasiCompact
  rw [hC C hC₀C φ hφ hposφ hlowφ, hC C hC₀C ψ hψ hposψ hlowψ]
  refine image_mono (iInter_mono fun j => ?_)
  exact (PartialBody.kahlerPartialBody_subset_of_iOrder
    (PartialBody.isKahlerCurrentPotential_add_smul hφ _ (t := ((j : ℝ) + 1)⁻¹) (by positivity))
    (PartialBody.isKahlerCurrentPotential_add_smul hψ _ (t := ((j : ℝ) + 1)⁻¹) (by positivity))
    hI).1

/-- **Source `prop:IcompimplyDeltacomp`, "in particular" clause, conditional on the lower bound of
`thm:DXmain1`** (for `φ` and for `V_θ`): for a big line bundle, `Δ_{Y•}(θ, φ) ⊆ Δ_{Y•}(L)`. -/
theorem partialOkounkovBody_subset_lineBundleOkounkovBody_of_lowerBound
    [Nonempty (SchemeComplexPoint f)] (hbig : IsBig f L (m + 1))
    (hV : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val (thetaPshSupremum (H.curvature a).val))
    (hlowV : DXMainLowerBound f E a H hV) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ φ : SchemeComplexPoint f → EReal,
      ∀ hφ : (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val φ),
      0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) →
      DXMainLowerBound f E a H hφ →
      partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a φ ⊆
        TranscendentalMain.euclideanImage (lineBundleOkounkovBody f (m + 1) E Y hY a) := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_partialOkounkovBody_eq_of_lowerBound f E Y hY a H
  refine ⟨C₀, hC₀, fun C hC₀C φ hφ hpos hlow => ?_⟩
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  rw [hC C hC₀C φ hφ hpos hlow,
    lineBundleOkounkovBody_eq_generalPartialBody_of_lowerBound f E Y hY a H hbig hV hlowV]
  set θ := H.curvature a with hθ
  obtain ⟨c, hc⟩ := FirstPass.thetaPshSupremum_minimalSingularities θ.val θ.2.1 θ.2.2
    (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) ⟨_, hφ⟩ φ hφ
  have hI : SGPT.Foundations.Analysis.FirstPass.IEnvelope.IOrderOnManifold (n := m + 1) φ
      (thetaPshSupremum θ.val) :=
    iOrderOnManifold_of_le_add hV.1.quasiPlurisubharmonic (C := c) fun x => hc x (mem_univ x)
  refine image_mono (iInter_mono fun j => ?_)
  exact (PartialBody.kahlerPartialBody_subset_of_iOrder
    (PartialBody.isKahlerCurrentPotential_add_smul hφ _ (t := ((j : ℝ) + 1)⁻¹) (by positivity))
    (PartialBody.isKahlerCurrentPotential_add_smul hV _ (t := ((j : ℝ) + 1)⁻¹) (by positivity))
    hI).1

/-- **Source `thm:Okoucont`, conditional on the lower bound of `thm:DXmain1`**: for a big class
`{θ}`, if the lower bound of `thm:DXmain1` holds for every `φ ∈ PSH(X, θ)_{>0}`, then for every
large cube cone the partial Okounkov body map
`(PSH(X, θ)_{>0}, d_S) → (𝒦ₙ, d_Haus)`, `φ ↦ Δ_{Y•}(θ, φ)`, is continuous: it is the underlying
set map of a continuous map into the convex bodies with the Hausdorff metric. (`d_S` with the
Fubini–Study reference form of the projective embedding.) -/
theorem exists_continuous_partialOkounkovBody_of_lowerBound [Nonempty (SchemeComplexPoint f)]
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
    (hlow : ∀ (φ : SchemeComplexPoint f → EReal)
      (hφ : letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val φ),
      (letI := E.isSeparated; letI := E.quasiCompact;
        letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
        haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
        haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
        HasPositivePotentialMass (H.curvature a) φ hφ) →
      DXMainLowerBound f E a H hφ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C →
      letI := E.isSeparated
      letI := E.quasiCompact
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
      haveI : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
      letI : TopologicalSpace (ThetaPshL1 (H.curvature a).val) :=
        (singularityPseudoMetricSpace (schemeProjectiveTNKahlerBackground f (m + 1) E)
          (H.curvature a) hbig).toUniformSpace.toTopologicalSpace
      ∃ G : {v : ThetaPshL1 (H.curvature a).val //
          HasPositivePotentialMass (H.curvature a) v.val v.property} →
          ConvexBody (EuclideanSpace ℝ (Fin (m + 1))),
        Continuous G ∧ ∀ v, (G v : Set (EuclideanSpace ℝ (Fin (m + 1)))) =
          partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a v.val.val := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_partialOkounkovBody_eq_of_lowerBound f E Y hY a H
  refine ⟨C₀, hC₀, fun C hC₀C => ?_⟩
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
  let : MeasurableSpace (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY).carrier :=
    borel (SchemeComplexPoint f)
  have : BorelSpace (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY).carrier := ⟨rfl⟩
  refine ⟨fun v => PartialBody.partialConvexBody (schemeFubiniStudyOriginalFlagGeometry
      f (m + 1) E Y hY) (H.curvature a) v.val,
    PartialBody.continuous_partialConvexBody_positiveMass
      (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
      (schemeProjectiveTNKahlerBackground f (m + 1) E) hbig, fun v => ?_⟩
  rw [PartialBody.coe_partialConvexBody]
  have hposK : 0 < volume.real (PartialBody.generalPartialBody
      (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) v.val.val) := by
    have h := PartialBody.volume_generalPartialBody_pos
      (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) v.val.property v.property
    have hfin := ((PartialBody.convex_isCompact_generalPartialBody
      (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
      v.val.property).2.measure_lt_top (μ := (volume : Measure (Fin (m + 1) → ℝ)))).ne
    exact ENNReal.toReal_pos h.ne' hfin
  exact (hC C hC₀C v.val.val v.val.property hposK (hlow _ _ v.property)).symm

/-- **Source `prop:Okocurrent`, conditional on the lower bound of `thm:DXmain1`**: the partial
Okounkov body depends only on the current `dd^c h`. Two Hermitian line bundles `(L, h)`,
`(L', h')` with smooth reference metrics `H`, `H'` (`θ = c₁(L, H)`, `θ' = c₁(L', H')`) and weights
`φ`, `φ'` have the same curvature current `θ + dd^c φ = θ' + dd^c φ'` when
`θ' = θ + dd^c g` and `φ' = φ - g` for a smooth function `g`; then
`Δ_{Y•}(L, h) = Δ_{Y•}(L', h')`. -/
theorem partialOkounkovBody_eq_of_sameCurrent_of_lowerBound [Nonempty (SchemeComplexPoint f)]
    {L' : X.Modules} (a' : LineBundleAtlas L') (H' : SchemeLineBundleMetric f (m + 1) E L')
    {g : SchemeComplexPoint f → ℝ}
    (hg : letI := E.isSeparated; letI := E.quasiCompact; ChartSmooth (n := m + 1) g)
    (hθθ' : letI := E.isSeparated; letI := E.quasiCompact;
      ∀ (e : ComplexChart (m + 1) (SchemeComplexPoint f)) (z : ComplexModel (m + 1)),
        z ∈ e.val.target → (H'.curvature a').val.coeff e z =
          (H.curvature a).val.coeff e z + smoothDDC (fun y => g (e.val.symm y)) z)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hφ' : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H'.curvature a').val (fun x => φ x - (g x : EReal)))
    (hpos : 0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ))
    (hlow : DXMainLowerBound f E a H hφ) (hlow' : DXMainLowerBound f E a' H' hφ') :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C →
      partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a φ =
        partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a' (fun x => φ x - (g x : EReal)) := by
  let := E.isSeparated
  let := E.quasiCompact
  have hK : PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
      (H'.curvature a') (fun x => φ x - (g x : EReal)) =
      PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
        (H.curvature a) φ :=
    PartialBody.generalPartialBody_sub_smooth
      (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hg hθθ' hφ
  obtain ⟨C₁, hC₁, hC⟩ := exists_partialOkounkovBody_eq_of_lowerBound f E Y hY a H
  obtain ⟨C₂, hC₂, hC'⟩ := exists_partialOkounkovBody_eq_of_lowerBound f E Y hY a' H'
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁, fun C hC₀C => ?_⟩
  rw [hC C ((le_max_left _ _).trans hC₀C) φ hφ hpos hlow,
    hC' C ((le_max_right _ _).trans hC₀C) _ hφ' (lt_of_lt_of_eq hpos (congrArg (fun K => volume.real K) hK).symm) hlow']
  exact (congrArg TranscendentalMain.euclideanImage hK).symm

/-- **Source `thm:concOko` for rational `t`, conditional on the lower bound of `thm:DXmain1`**:
for `φ, ψ ∈ PSH(X, θ)_{>0}` and `t ∈ ℚ ∩ (0, 1)`,
`t Δ_{Y•}(θ, φ) + (1 - t) Δ_{Y•}(θ, ψ) ⊆ Δ_{Y•}(θ, tφ + (1 - t)ψ)`. -/
theorem convexComb_mem_partialOkounkovBody_of_lowerBound [Nonempty (SchemeComplexPoint f)] :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ φ ψ : SchemeComplexPoint f → EReal,
      ∀ hφ : (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val φ),
      ∀ hψ : (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val ψ),
      ∀ t : ℚ, 0 < t → t < 1 →
      ∀ hχ : (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val
          (SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination.convexComb (t : ℝ) φ ψ)),
      0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) →
      0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) ψ) →
      0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a)
          (SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination.convexComb (t : ℝ) φ ψ)) →
      DXMainLowerBound f E a H hφ → DXMainLowerBound f E a H hψ → DXMainLowerBound f E a H hχ →
      (t : ℝ) • partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a φ +
          (1 - (t : ℝ)) • partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a ψ ⊆
        partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a
          (SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination.convexComb (t : ℝ) φ ψ) := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_partialOkounkovBody_eq_of_lowerBound f E Y hY a H
  refine ⟨C₀, hC₀, fun C hC₀C φ ψ hφ hψ t ht0 ht1 hχ hpφ hpψ hpχ hlφ hlψ hlχ => ?_⟩
  let := E.isSeparated
  let := E.quasiCompact
  rw [hC C hC₀C φ hφ hpφ hlφ, hC C hC₀C ψ hψ hpψ hlψ, hC C hC₀C _ hχ hpχ hlχ]
  rintro _ ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, _, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
  refine ⟨(t : ℝ) • x + (1 - (t : ℝ)) • y,
    Valuative.convexComb_mem_generalPartialBody (F := schemeFubiniStudyOriginalFlagGeometry
      f (m + 1) E Y hY) hφ hψ ht0 ht1 hx hy, ?_⟩
  simp only [map_add, map_smul]

end SGPT.Okounkov.AlgPOB
