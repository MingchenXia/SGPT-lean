import SGPT.GAGA.H0LDXMain
import SGPT.Okounkov.AlgPOBProperties
import SGPT.IGood.Misc2VolBigL

/-!
# Algebraic (partial) Okounkov bodies and the volume of a line bundle, unconditionally


The algebraic Okounkov theory of the workspace (`SGPT.Okounkov.AlgPOB`, `SGPT.IGood.Misc2VolBigL`)
was proved conditionally on the lower bound of `thm:DXmain1`
(`SGPT.IGood.DXMain.DXMainLowerBound`).  That bound is now `SGPT.GAGA.H0L.dxMainLowerBound`
(on `X` with connected analytic space; a smooth flag makes `X(ℂ)` connected), so the statements
below hold unconditionally, in the setting of the conditional ones: `X` an integral smooth
projective complex scheme of dimension `m + 1` carrying a smooth flag `Y•` (`ν = ν_{Y•}`), `L` a
line bundle with atlas `a` and smooth metric `H`, `θ = c₁(L, H)`.

* `cor:volbigL`: `lim_k n! h⁰(X, Lᵏ)/kⁿ = ∫_X θ_{V_θ}ⁿ` (`tendsto_normalized_h0`).
* `thm:Gammaasg`, `def:Okounkov:L687`, `cor:transalgPOB`, `cor:POBvolume`, `thm:HCP`/`lma:twistedHcp`
  (`T = 𝒪_X`): `multiplierConeSubset_mem_almostSemigroupLocus`,
  `partialOkounkovBody_eq_generalPartialBody`, `exists_partialOkounkovBody_eq`,
  `volume_partialOkounkovBody`, `tendsto_hausdorffDist_multiplierDegreePolytope`.
* `prop:Okounbiglbdl`, `def:Okobd`, `cor:Okounvol`, `prop:Deltaconvtwisted` (`T = 𝒪_X`), for big `L`:
  `exists_sectionSemigroup_mem_fullSemigroupLocus`, `lineBundleOkounkovBody_eq_generalPartialBody`,
  `volume_eq_factorial_mul_okounkovBody`, `tendsto_hausdorffDist_lineBundleDegreeBody`.
* `prop:IcompimplyDeltacomp`, `thm:Okoucont`, `prop:Okocurrent`, `thm:concOko` (rational `t`):
  `partialOkounkovBody_subset_of_iOrder`, `partialOkounkovBody_subset_lineBundleOkounkovBody`,
  `exists_continuous_partialOkounkovBody`, `partialOkounkovBody_eq_of_sameCurrent`,
  `convexComb_mem_partialOkounkovBody`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.GAGA.H0L

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.Okounkov.AlgPOB SGPT.LineBundle SGPT.PSH SGPT.AlmostSemigroup
  SGPT.AlmostSemigroup.Class SGPT.AlmostSemigroup.OkounkovExtension SGPT.IGood.DXMain
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus SGPT.Foundations.Analysis.Pending.DiagonalMass
  SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology
  SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDistance
open scoped Topology ENNReal NNReal Pointwise

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]

local instance h0lOkoTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance h0lOkoCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance h0lOkoManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)

omit [IsIntegral X] in
include Y hY in
/-- **The lower bound of `thm:DXmain1` on `X` with a smooth flag** (the flag makes `X(ℂ)`
connected). -/
theorem dxMainLowerBound_of_smoothFlag [Nonempty (SchemeComplexPoint f)]
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) :
    DXMainLowerBound f E a H hφ := by
  have : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
  exact dxMainLowerBound a H hφ

/-! ### `cor:volbigL` -/

include Y hY in
/-- **Source `cor:volbigL`** (`X` projective with a smooth flag): for a pseudo-effective line
bundle `L` (`V_θ ∈ PSH(X, θ)`) with a smooth metric, `θ = c₁(L, H)`,
`lim_k n! h⁰(X, Lᵏ)/kⁿ = ∫_X θ_{V_θ}ⁿ`. -/
theorem tendsto_normalized_h0 [Nonempty (SchemeComplexPoint f)]
    (hV : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val (thetaPshSupremum (H.curvature a).val)) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    Tendsto (fun k : ℕ => (((m + 1).factorial : ℝ≥0∞) * (h0 f L k : ℝ≥0∞)) / (k : ℝ≥0∞) ^ (m + 1))
      atTop (𝓝 (diagonalPotentialMass (H.curvature a)
        (thetaPshSupremum (H.curvature a).val) hV)) :=
  SGPT.IGood.Misc2VolBigL.tendsto_normalized_h0_of_lowerBound f E a H Y hY hV
    (dxMainLowerBound_of_smoothFlag f E Y hY a H hV)

/-! ### Partial Okounkov bodies -/

/-- **Source `thm:Gammaasg`** (flag valuations): if `vol θ_φ > 0`, then for every cube cone
`C([0, C]ⁿ)` containing `Γ(θ, φ)` and `Δ_{Y•}(θ_φ)`, `Γ(θ, φ) ∈ 𝒮'(C)‾_{>0}` with
`vol Γ(θ, φ) = vol Δ_{Y•}(θ_φ) = vol θ_φ / n!`. -/
theorem multiplierConeSubset_mem_almostSemigroupLocus [Nonempty (SchemeComplexPoint f)]
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hpos : 0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ)) {C : ℝ}
    (hsub : multiplierSectionSet f (m + 1) E Y hY a φ ⊆
      (latticePoints (cubeCone (n := m + 1) C).cone : Set _))
    (hKC : PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
      (H.curvature a) φ ⊆ heightOne (cubeCone (n := m + 1) C).cone) :
    multiplierConeSubset f E Y hY a φ hsub ∈ almostSemigroupLocus (cubeCone (n := m + 1) C) ∧
      (multiplierConeSubset f E Y hY a φ hsub).volume =
        volume.real (PartialBody.generalPartialBody
          (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) :=
  multiplierConeSubset_mem_almostSemigroupLocus_of_lowerBound f E Y hY a H hφ hpos
    (dxMainLowerBound_of_smoothFlag f E Y hY a H hφ) hsub hKC

/-- **Source `cor:transalgPOB`, `def:Okounkov:L687`**: the algebraic partial Okounkov body
`Δ_{Y•}(θ, φ) = Δ(Γ(θ, φ))` is the transcendental partial Okounkov body `Δ_{Y•}(θ_φ)`. -/
theorem partialOkounkovBody_eq_generalPartialBody [Nonempty (SchemeComplexPoint f)]
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hpos : 0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ)) {C : ℝ}
    (hsub : multiplierSectionSet f (m + 1) E Y hY a φ ⊆
      (latticePoints (cubeCone (n := m + 1) C).cone : Set _))
    (hKC : PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
      (H.curvature a) φ ⊆ heightOne (cubeCone (n := m + 1) C).cone) :
    partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a φ =
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm '' PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ :=
  partialOkounkovBody_eq_generalPartialBody_of_lowerBound f E Y hY a H hφ hpos
    (dxMainLowerBound_of_smoothFlag f E Y hY a H hφ) hsub hKC

/-- **Source `thm:HCP` and `lma:twistedHcp` for `T = 𝒪_X`**: `Δ_k(θ, φ) → Δ_{Y•}(θ, φ)` in the
Hausdorff metric. -/
theorem tendsto_hausdorffDist_multiplierDegreePolytope [Nonempty (SchemeComplexPoint f)]
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hpos : 0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ)) {C : ℝ}
    (hsub : multiplierSectionSet f (m + 1) E Y hY a φ ⊆
      (latticePoints (cubeCone (n := m + 1) C).cone : Set _))
    (hKC : PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
      (H.curvature a) φ ⊆ heightOne (cubeCone (n := m + 1) C).cone) :
    Tendsto (fun k => hausdorffDist
        ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm '' multiplierDegreePolytope f (m + 1) E Y hY a φ k)
        (partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a φ)) atTop (𝓝 0) :=
  tendsto_hausdorffDist_multiplierDegreePolytope_of_lowerBound f E Y hY a H hφ hpos
    (dxMainLowerBound_of_smoothFlag f E Y hY a H hφ) hsub hKC

/-- **Source `def:Okounkov:L687` / `cor:transalgPOB`, uniform form**: there is `C₀` such that for
every `C ≥ C₀` and every `φ ∈ PSH(X, θ)` with `vol Δ_{Y•}(θ_φ) > 0`, the algebraic partial
Okounkov body relative to `C([0, C]ⁿ)` is the Euclidean copy of `Δ_{Y•}(θ_φ)`. -/
theorem exists_partialOkounkovBody_eq [Nonempty (SchemeComplexPoint f)] :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ φ : SchemeComplexPoint f → EReal,
      (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val φ) →
      0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) →
      partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a φ =
        TranscendentalMain.euclideanImage (PartialBody.generalPartialBody
          (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_partialOkounkovBody_eq_of_lowerBound f E Y hY a H
  exact ⟨C₀, hC₀, fun C hC' φ hφ hpos =>
    hC C hC' φ hφ hpos (dxMainLowerBound_of_smoothFlag f E Y hY a H hφ)⟩

/-- **Source `cor:POBvolume`**: `vol Δ_{Y•}(θ, φ) = vol θ_φ / n!` for `vol θ_φ > 0` (for all large
cube cones). -/
theorem volume_partialOkounkovBody [Nonempty (SchemeComplexPoint f)] :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ φ : SchemeComplexPoint f → EReal,
      ∀ hφ : (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val φ),
      (letI := E.isSeparated; letI := E.quasiCompact;
        letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
        haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
        haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
        0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ) →
      (letI := E.isSeparated; letI := E.quasiCompact;
        letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
        haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
        haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
        volume (partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a φ) =
          iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ /
            ((m + 1).factorial : ℝ≥0∞)) := by
  obtain ⟨C₀, hC₀, hC⟩ := volume_partialOkounkovBody_of_lowerBound f E Y hY a H
  exact ⟨C₀, hC₀, fun C hC' φ hφ hpos =>
    hC C hC' φ hφ hpos (dxMainLowerBound_of_smoothFlag f E Y hY a H hφ)⟩

/-- **Source `prop:IcompimplyDeltacomp`**: for `φ, ψ ∈ PSH(X, θ)_{>0}` with `φ ⪯_𝓘 ψ`,
`Δ_{Y•}(θ, φ) ⊆ Δ_{Y•}(θ, ψ)` (for all large cube cones). -/
theorem partialOkounkovBody_subset_of_iOrder [Nonempty (SchemeComplexPoint f)] :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ φ ψ : SchemeComplexPoint f → EReal,
      (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val φ) →
      (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val ψ) →
      0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) →
      0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) ψ) →
      (letI := E.isSeparated; letI := E.quasiCompact;
        SGPT.Foundations.Analysis.FirstPass.IEnvelope.IOrderOnManifold (n := m + 1) φ ψ) →
      partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a φ ⊆
        partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a ψ := by
  obtain ⟨C₀, hC₀, hC⟩ := partialOkounkovBody_subset_of_iOrder_of_lowerBound f E Y hY a H
  exact ⟨C₀, hC₀, fun C hC' φ ψ hφ hψ hpφ hpψ hI =>
    hC C hC' φ ψ hφ hψ hpφ hpψ (dxMainLowerBound_of_smoothFlag f E Y hY a H hφ)
      (dxMainLowerBound_of_smoothFlag f E Y hY a H hψ) hI⟩

/-- **Source `prop:IcompimplyDeltacomp`, "in particular"**: for a big line bundle,
`Δ_{Y•}(θ, φ) ⊆ Δ_{Y•}(L)`. -/
theorem partialOkounkovBody_subset_lineBundleOkounkovBody [Nonempty (SchemeComplexPoint f)]
    (hbig : IsBig f L (m + 1)) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ φ : SchemeComplexPoint f → EReal,
      (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val φ) →
      0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) →
      partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a φ ⊆
        TranscendentalMain.euclideanImage (lineBundleOkounkovBody f (m + 1) E Y hY a) := by
  have hV := isThetaPshPotential_thetaPshSupremum_of_isBig f E a H hbig
  obtain ⟨C₀, hC₀, hC⟩ := partialOkounkovBody_subset_lineBundleOkounkovBody_of_lowerBound f E Y hY
    a H hbig hV (dxMainLowerBound_of_smoothFlag f E Y hY a H hV)
  exact ⟨C₀, hC₀, fun C hC' φ hφ hpos =>
    hC C hC' φ hφ hpos (dxMainLowerBound_of_smoothFlag f E Y hY a H hφ)⟩

/-- **Source `thm:Okoucont`**: for a big class `{θ}`, for every large cube cone the partial
Okounkov body map `(PSH(X, θ)_{>0}, d_S) → (𝒦ₙ, d_Haus)`, `φ ↦ Δ_{Y•}(θ, φ)`, is continuous. -/
theorem exists_continuous_partialOkounkovBody [Nonempty (SchemeComplexPoint f)]
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
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
          partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a v.val.val :=
  exists_continuous_partialOkounkovBody_of_lowerBound f E Y hY a H hbig
    fun _ hφ _ => dxMainLowerBound_of_smoothFlag f E Y hY a H hφ

/-- **Source `prop:Okocurrent`**: the partial Okounkov body depends only on the current
`θ + dd^c φ = θ' + dd^c φ'` (`θ' = θ + dd^c g`, `φ' = φ - g` for a smooth `g`). -/
theorem partialOkounkovBody_eq_of_sameCurrent [Nonempty (SchemeComplexPoint f)]
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
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ)) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C →
      partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a φ =
        partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a' (fun x => φ x - (g x : EReal)) :=
  partialOkounkovBody_eq_of_sameCurrent_of_lowerBound f E Y hY a H a' H' hg hθθ' hφ hφ' hpos
    (dxMainLowerBound_of_smoothFlag f E Y hY a H hφ)
    (dxMainLowerBound_of_smoothFlag f E Y hY a' H' hφ')

/-- **Source `thm:concOko` for rational `t`**: for `φ, ψ ∈ PSH(X, θ)_{>0}` and `t ∈ ℚ ∩ (0, 1)`,
`t Δ_{Y•}(θ, φ) + (1 - t) Δ_{Y•}(θ, ψ) ⊆ Δ_{Y•}(θ, tφ + (1 - t)ψ)`. -/
theorem convexComb_mem_partialOkounkovBody [Nonempty (SchemeComplexPoint f)] :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ φ ψ : SchemeComplexPoint f → EReal,
      (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val φ) →
      (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val ψ) →
      ∀ t : ℚ, 0 < t → t < 1 →
      (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val
          (SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination.convexComb (t : ℝ) φ ψ)) →
      0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) →
      0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) ψ) →
      0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a)
          (SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination.convexComb (t : ℝ) φ ψ)) →
      (t : ℝ) • partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a φ +
          (1 - (t : ℝ)) • partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a ψ ⊆
        partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a
          (SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination.convexComb (t : ℝ) φ ψ) := by
  obtain ⟨C₀, hC₀, hC⟩ := convexComb_mem_partialOkounkovBody_of_lowerBound f E Y hY a H
  exact ⟨C₀, hC₀, fun C hC' φ ψ hφ hψ t ht0 ht1 hχ hpφ hpψ hpχ =>
    hC C hC' φ ψ hφ hψ t ht0 ht1 hχ hpφ hpψ hpχ
      (dxMainLowerBound_of_smoothFlag f E Y hY a H hφ)
      (dxMainLowerBound_of_smoothFlag f E Y hY a H hψ)
      (dxMainLowerBound_of_smoothFlag f E Y hY a H hχ)⟩

/-! ### The Okounkov body of a big line bundle -/

include H in
/-- **Source `prop:Okounbiglbdl`** (flag valuations): for a big line bundle `L` there is a convex
body `Δ = [0, C]ⁿ` with `Γ(L) ∈ 𝒮'(Δ)`. -/
theorem exists_sectionSemigroup_mem_fullSemigroupLocus [Nonempty (SchemeComplexPoint f)]
    (hbig : IsBig f L (m + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ hS : schemeProjectiveSectionSemigroup f (m + 1) E Y hY a ≤
      latticePoints (cubeCone (n := m + 1) C).cone,
      SGPT.AlmostSemigroup.Okounkov.sourceSubset (cubeCone (n := m + 1) C) _ hS ∈
        fullSemigroupLocus (cubeCone (n := m + 1) C) := by
  have hV := isThetaPshPotential_thetaPshSupremum_of_isBig f E a H hbig
  exact exists_sectionSemigroup_mem_fullSemigroupLocus_of_lowerBound f E Y hY a H hbig hV
    (dxMainLowerBound_of_smoothFlag f E Y hY a H hV)

include H in
/-- `Γ(L)` generates `ℤⁿ⁺¹` for a big line bundle (`prop:Okounbiglbdl`, Step 2). -/
theorem generatedGroup_sectionSemigroup_eq_top [Nonempty (SchemeComplexPoint f)]
    (hbig : IsBig f L (m + 1)) :
    LatticeSlices.generatedGroup (schemeProjectiveSectionSemigroup f (m + 1) E Y hY a) = ⊤ := by
  have hV := isThetaPshPotential_thetaPshSupremum_of_isBig f E a H hbig
  exact generatedGroup_sectionSemigroup_eq_top_of_lowerBound f E Y hY a H hbig hV
    (dxMainLowerBound_of_smoothFlag f E Y hY a H hV)

/-- **Source `def:Okobd` / `cor:transalgPOB` for minimal singularities**: for a big line bundle,
`Δ_{Y•}(L) = Δ_{Y•}(θ, V_θ)`, the transcendental partial body of `θ_{V_θ}`. -/
theorem lineBundleOkounkovBody_eq_generalPartialBody [Nonempty (SchemeComplexPoint f)]
    (hbig : IsBig f L (m + 1)) :
    lineBundleOkounkovBody f (m + 1) E Y hY a =
      PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
        (H.curvature a) (thetaPshSupremum (H.curvature a).val) := by
  have hV := isThetaPshPotential_thetaPshSupremum_of_isBig f E a H hbig
  exact lineBundleOkounkovBody_eq_generalPartialBody_of_lowerBound f E Y hY a H hbig hV
    (dxMainLowerBound_of_smoothFlag f E Y hY a H hV)

include H in
/-- **Source `cor:Okounvol`** (flag valuations): for a big line bundle,
`vol L = n! vol Δ_{Y•}(L)`. -/
theorem volume_eq_factorial_mul_okounkovBody [Nonempty (SchemeComplexPoint f)]
    (hbig : IsBig f L (m + 1)) :
    SGPT.LineBundle.volume f L (m + 1) = ENNReal.ofReal (((m + 1).factorial : ℝ) *
      volume.real (lineBundleOkounkovBody f (m + 1) E Y hY a)) := by
  have hV := isThetaPshPotential_thetaPshSupremum_of_isBig f E a H hbig
  exact volume_eq_factorial_mul_okounkovBody_of_lowerBound f E Y hY a H hbig hV
    (dxMainLowerBound_of_smoothFlag f E Y hY a H hV)

include H in
/-- **Source `prop:Deltaconvtwisted` for `T = 𝒪_X`**: `Δ_k(L) → Δ_{Y•}(L)` in the Hausdorff
metric, for a big line bundle. -/
theorem tendsto_hausdorffDist_lineBundleDegreeBody [Nonempty (SchemeComplexPoint f)]
    (hbig : IsBig f L (m + 1)) :
    Tendsto (fun k => hausdorffDist (schemeProjectiveSectionDegreeBody f (m + 1) E Y hY a k)
      ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm '' lineBundleOkounkovBody f (m + 1) E Y hY a))
      atTop (𝓝 0) := by
  have hV := isThetaPshPotential_thetaPshSupremum_of_isBig f E a H hbig
  exact tendsto_hausdorffDist_lineBundleDegreeBody_of_lowerBound f E Y hY a H hbig hV
    (dxMainLowerBound_of_smoothFlag f E Y hY a H hV)

end SGPT.GAGA.H0L
