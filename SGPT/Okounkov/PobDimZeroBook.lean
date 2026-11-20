import SGPT.Okounkov.PobDimZeroCore
import SGPT.Okounkov.OkoNSInfty
import SGPT.Okounkov.OkoNSAlgebraic
import SGPT.Okounkov.QwOkoScaling
import SGPT.Okounkov.ChowBlDeltaCont

/-!
# The statements of `sec:PoB` in dimension zero

Lane POB-DIM0, blueprint `claude-pob-dim0.tex`. Section *Algebraic partial Okounkov bodies*
(`sec:PoB`) of the chapter *The theory of Okounkov bodies* works on a connected smooth complex
projective variety `X` of dimension `n` with a rank-`n` valuation `ν`, a big line bundle `L` with
smooth reference metric `h₀`, `θ = c₁(L, h₀)` and `φ ∈ PSH(X, θ)`; the case `n = 0` is not
excluded. The workspace states the section's results for `X` of relative dimension `m + 1`
(lanes OKO-A, DXMAIN, H0-GAGA3, OKO-CLOSE, OKO-NS, QW-OKO, CHOW-BLOWUP, VAL-GEN). This file states
and proves them for `X` of relative dimension `0`, in the same setting (`X` an integral smooth
projective complex scheme, structure morphism `f`, closed projective embedding `E`, smooth flag
`Y` — here `Y₀ = X`, which makes `X(ℂ)` connected —, `L` with atlas `a` and smooth metric `H`,
`θ = c₁(L, H)`) and with the same section-level objects, all of which are defined in every
relative dimension.

In dimension `0`, `X` is a point, `vol θ_φ = ∫_X θ_φ⁰ = 1` for every `φ ∈ PSH(X, θ)` (so
`PSH(X, θ)_{>0} = PSH(X, θ)` and every `L` is big), `Γ(θ, φ) = Γ^∞(θ, φ) = Γ(L) = {(0, k)}` and
every body is `ℝ⁰ = {0}` (`SGPT.Okounkov.PobDimZero`, file `PobDimZeroCore`). The statements
below are the book's statements for `n = 0`; where the positive-dimensional Lean statement
carries the positivity hypothesis `vol θ_φ > 0` it is dropped (it always holds), which makes the
statements stronger.

Every statement also holds for an arbitrary (rank-`0`) valuation `ν`: in dimension `0` the
section sets and bodies of every valuation coincide with those of the flag valuation
(`valuation_multiplierSectionSet_eq_flag`, `valuation_partialBody_eq_partialOkounkovBody`,
`valuation_okounkovBody_eq_flag`), and the hypothesis `Γ_ν(L) ∈ 𝒮'(C)` (source
`prop:Okounbiglbdl`) holds (`valuation_sectionSemigroup_mem_fullSemigroupLocus`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.PobDimZero

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus SGPT.Foundations.Analysis.Pending.DiagonalMass
  SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology
  SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDistance
open SGPT.AlmostSemigroup SGPT.AlmostSemigroup.Class SGPT.AlmostSemigroup.Okounkov
open scoped Topology ENNReal Pointwise

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] [SmoothOfRelativeDimension 0 f]

local instance pobDimZeroBookTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance pobDimZeroBookCharts : ChartedSpace (ComplexModel 0) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f 0
local instance pobDimZeroBookManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold 0 (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f 0

variable (Y : Fin (0 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f 0 E L)

omit [IsIntegral X] in
/-- A `θ`-psh weight is quasi-psh. -/
theorem quasiPsh_of_curvature {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    IsGlobalQuasiPshPotential (n := 0) φ := by
  let := E.isSeparated
  let := E.quasiCompact
  exact hφ.quasiPshPotential

omit [IsIntegral X] in
/-- A `θ`-psh weight is finite on the point `X(ℂ)`. -/
theorem finite_of_curvature {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) (x : SchemeComplexPoint f) :
    φ x ≠ ⊤ ∧ φ x ≠ ⊥ := by
  let := E.isSeparated
  let := E.quasiCompact
  exact finite_of_isThetaPshPotential hφ x

omit [IsIntegral X] in
include Y hY in
/-- **`vol θ_φ = 1`** for every `φ ∈ PSH(X, θ)` in dimension `0`. -/
theorem iVolume_curvature_eq_one {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : Nonempty (SchemeComplexPoint f) := nonempty_complexPoint f E Y hY
    iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ = 1 := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : Nonempty (SchemeComplexPoint f) := nonempty_complexPoint f E Y hY
  have : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f 0 Y hY
  exact iVolume_eq_one _ _ hφ

omit [IsIntegral X] in
include Y hY in
/-- **`∫_X θ_φ⁰ = 1`** for every `φ ∈ PSH(X, θ)` in dimension `0`. -/
theorem diagonalPotentialMass_curvature_eq_one {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    diagonalPotentialMass (H.curvature a) φ hφ = 1 := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f 0 Y hY
  exact diagonalPotentialMass_eq_one _ hφ

/-! ### `thm:Gammaasg`, `def:Okounkov:L687`, `cor:POBvolume` -/

/-- **Source `thm:Gammaasg` and the well-definedness in `def:Okounkov:L687`, dimension `0`**: for
every `φ ∈ PSH(X, θ)` (`= PSH(X, θ)_{>0}`) and every cube cone `C([0, c]⁰)`,
`Γ(θ, φ) ∈ 𝒮'(C)‾_{>0}` (indeed `Γ(θ, φ) ∈ 𝒮'(C)`), `vol Γ(θ, φ) = vol θ_φ / 0! = 1`, and the
partial Okounkov body `Δ_{Y•}(θ, φ) = Δ(Γ(θ, φ))` is `ℝ⁰`. -/
theorem multiplierSectionSet_mem_almostSemigroupLocus_dim_zero {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) (c : ℝ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : Nonempty (SchemeComplexPoint f) := nonempty_complexPoint f E Y hY
    ∃ hsub : multiplierSectionSet f 0 E Y hY a φ ⊆
        (latticePoints (cubeCone (n := 0) c).cone : Set _),
      (⟨_, hsub⟩ : ConeSubset (cubeCone (n := 0) c)) ∈ fullSemigroupLocus (cubeCone c) ∧
      (⟨_, hsub⟩ : ConeSubset (cubeCone (n := 0) c)) ∈ almostSemigroupLocus (cubeCone c) ∧
      ConeSubset.volume (⟨_, hsub⟩ : ConeSubset (cubeCone (n := 0) c)) =
        (iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ
          hφ).toReal / ((0 : ℕ).factorial : ℝ) ∧
      partialOkounkovBody f 0 E Y hY (cubeCone c) a φ = univ := by
  have hq := quasiPsh_of_curvature f E a H hφ
  obtain ⟨h1, h2, h3⟩ := multiplierConeSubset_mem_almostSemigroupLocus f E Y hY a hq
    (cubeCone c) (mem_cubeCone_zero_one c)
  refine ⟨multiplierSectionSet_subset f E Y hY a hq _ (mem_cubeCone_zero_one c), h1, h2, ?_,
    partialOkounkovBody_cubeCone_eq_univ f E Y hY a hq c⟩
  rw [h3, iVolume_curvature_eq_one f E Y hY a H hφ]
  simp

/-- **Source `thm:Gammaasg`, dimension `0`, with the source's cone `C(Δ_ν(L))`**:
`Δ_ν(L) = ℝ⁰` is a convex body and for every `φ ∈ PSH(X, θ)`,
`Γ(θ, φ) ∈ 𝒮'(Δ_ν(L))‾_{>0}` (indeed `∈ 𝒮'(Δ_ν(L))`) with volume `vol θ_φ / 0! = 1`. -/
theorem multiplierSectionSet_mem_almostSemigroupLocus_coneOver_dim_zero
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : Nonempty (SchemeComplexPoint f) := nonempty_complexPoint f E Y hY
    ∃ (hKc : IsCompact (lineBundleOkounkovBody f 0 E Y hY a))
      (hKv : Convex ℝ (lineBundleOkounkovBody f 0 E Y hY a))
      (hsub : multiplierSectionSet f 0 E Y hY a φ ⊆
        (latticePoints (SGPT.GAGA.OkoClose.coneOver _ hKc hKv).cone : Set _)),
      (⟨_, hsub⟩ : ConeSubset (SGPT.GAGA.OkoClose.coneOver _ hKc hKv)) ∈
          fullSemigroupLocus (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) ∧
        (⟨_, hsub⟩ : ConeSubset (SGPT.GAGA.OkoClose.coneOver _ hKc hKv)) ∈
          almostSemigroupLocus (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) ∧
        ConeSubset.volume (⟨_, hsub⟩ : ConeSubset (SGPT.GAGA.OkoClose.coneOver _ hKc hKv)) =
          (iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ
            hφ).toReal / ((0 : ℕ).factorial : ℝ) := by
  have hq := quasiPsh_of_curvature f E a H hφ
  have hK := lineBundleOkounkovBody_eq_univ f E Y hY a
  have hKc : IsCompact (lineBundleOkounkovBody f 0 E Y hY a) := by
    rw [hK]
    exact isCompact_univ
  have hKv : Convex ℝ (lineBundleOkounkovBody f 0 E Y hY a) := by
    rw [hK]
    exact convex_univ
  have h1 := mem_coneOver_zero_one hKc hKv (by rw [hK]; exact univ_nonempty)
  obtain ⟨hA, hB, hC⟩ := multiplierConeSubset_mem_almostSemigroupLocus f E Y hY a hq _ h1
  refine ⟨hKc, hKv, multiplierSectionSet_subset f E Y hY a hq _ h1, hA, hB, ?_⟩
  rw [hC, iVolume_curvature_eq_one f E Y hY a H hφ]
  simp

/-- **Source `cor:POBvolume`, dimension `0`**, in the form of the positive-dimensional statement
`SGPT.GAGA.H0L.volume_partialOkounkovBody`: for all cube cones and every `φ ∈ PSH(X, θ)` with
`vol θ_φ > 0`, `vol Δ_{Y•}(θ, φ) = vol θ_φ / 0!` (both sides are `1`). -/
theorem volume_partialOkounkovBody_dim_zero :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ φ : SchemeComplexPoint f → EReal,
      ∀ hφ : (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val φ),
      (letI := E.isSeparated; letI := E.quasiCompact;
        letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
        haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
        haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
        haveI : Nonempty (SchemeComplexPoint f) := nonempty_complexPoint f E Y hY;
        0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ) →
      (letI := E.isSeparated; letI := E.quasiCompact;
        letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
        haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
        haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
        haveI : Nonempty (SchemeComplexPoint f) := nonempty_complexPoint f E Y hY;
        volume (partialOkounkovBody f 0 E Y hY (cubeCone C) a φ) =
          iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ /
            ((0 : ℕ).factorial : ℝ≥0∞)) := by
  refine ⟨0, le_rfl, fun C _ φ hφ _ => ?_⟩
  have hq := quasiPsh_of_curvature f E a H hφ
  rw [partialOkounkovBody_cubeCone_eq_univ f E Y hY a hq C, volume_univ_euclidean,
    iVolume_curvature_eq_one f E Y hY a H hφ]
  simp

/-- `vol Δ_{Y•}(θ, φ) = 1` in dimension `0`. -/
theorem volume_partialOkounkovBody_eq_one_dim_zero {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) (c : ℝ) :
    volume (partialOkounkovBody f 0 E Y hY (cubeCone c) a φ) = 1 := by
  rw [partialOkounkovBody_cubeCone_eq_univ f E Y hY a (quasiPsh_of_curvature f E a H hφ) c,
    volume_univ_euclidean]

/-! ### `prop:GammaepsSp` and `rmk:DeltaanaW0` -/

/-- **Source `prop:GammaepsSp`, dimension `0`**: for every `φ ∈ PSH(X, θ)` (in particular for `φ`
with analytic singularities and `θ_φ` a Kähler current), `Γ^∞(θ, φ)` is the semigroup
`{(0, k) : k ∈ ℕ}`, it lies in `𝒮'(Δ_ν(L))` (the cone over the convex body `Δ_ν(L) = ℝ⁰`), and
`k⁻⁰ #Γ^∞_k(θ, φ) → (1/0!) ∫_X θ_φ⁰`, so `vol Γ^∞(θ, φ) = (1/0!) ∫_X θ_φ⁰` (`= 1`). -/
theorem inftySectionSet_mem_fullSemigroupLocus_dim_zero {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ∃ (hKc : IsCompact (lineBundleOkounkovBody f 0 E Y hY a))
      (hKv : Convex ℝ (lineBundleOkounkovBody f 0 E Y hY a))
      (hS : nonnegHeight ≤ latticePoints (SGPT.GAGA.OkoClose.coneOver _ hKc hKv).cone),
      (nonnegHeight : Set ((Fin 0 → ℤ) × ℤ)) = inftySectionSet f 0 E Y hY a φ ∧
      sourceSubset (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) _ hS ∈
          fullSemigroupLocus (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) ∧
        Tendsto (sourceSubset (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) _ hS).normalizedCardinality
          atTop (𝓝 ((diagonalPotentialMass (H.curvature a) φ hφ).toReal /
            ((0 : ℕ).factorial : ℝ))) ∧
        (sourceSubset (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) _ hS).volume =
          (diagonalPotentialMass (H.curvature a) φ hφ).toReal / ((0 : ℕ).factorial : ℝ) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hq := quasiPsh_of_curvature f E a H hφ
  have hK := lineBundleOkounkovBody_eq_univ f E Y hY a
  have hKc : IsCompact (lineBundleOkounkovBody f 0 E Y hY a) := by
    rw [hK]
    exact isCompact_univ
  have hKv : Convex ℝ (lineBundleOkounkovBody f 0 E Y hY a) := by
    rw [hK]
    exact convex_univ
  have hS := nonnegHeight_le_latticePoints _
    (mem_coneOver_zero_one hKc hKv (by rw [hK]; exact univ_nonempty))
  have hmass :
      (diagonalPotentialMass (H.curvature a) φ hφ).toReal / ((0 : ℕ).factorial : ℝ) = 1 := by
    rw [diagonalPotentialMass_curvature_eq_one f E Y hY a H hφ]
    simp
  refine ⟨hKc, hKv, hS, (inftySectionSet_eq f E Y hY a hq).symm,
    sourceSubset_nonnegHeight_mem_fullSemigroupLocus _ hS, ?_, ?_⟩
  · rw [hmass]
    exact tendsto_normalizedCardinality_nonnegHeight _ hS
  · rw [hmass]
    exact volume_sourceSubset_nonnegHeight _ hS

/-- **Source `rmk:DeltaanaW0` (first sentence, `eq:Gamma0Gammaanalytic`), dimension `0`**:
`Γ^∞(θ, φ) = Γ(θ, φ)`, hence `d_sg(Γ^∞(θ, φ), Γ(θ, φ)) = 0`, in every cube cone. -/
theorem dist_inftySection_multiplierSection_eq_zero_dim_zero {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) (c : ℝ) :
    inftySectionSet f 0 E Y hY a φ = multiplierSectionSet f 0 E Y hY a φ ∧
    ∃ (hU : inftySectionSet f 0 E Y hY a φ ⊆ (latticePoints (cubeCone (n := 0) c).cone : Set _))
      (hsub : multiplierSectionSet f 0 E Y hY a φ ⊆
        (latticePoints (cubeCone (n := 0) c).cone : Set _)),
      dist (α := ConeSubset (cubeCone (n := 0) c)) ⟨_, hU⟩ ⟨_, hsub⟩ = 0 := by
  have hq := quasiPsh_of_curvature f E a H hφ
  have heq : inftySectionSet f 0 E Y hY a φ = multiplierSectionSet f 0 E Y hY a φ := by
    rw [inftySectionSet_eq f E Y hY a hq, multiplierSectionSet_eq f E Y hY a hq]
  have hsub := multiplierSectionSet_subset f E Y hY a hq _ (mem_cubeCone_zero_one c)
  refine ⟨heq, heq ▸ hsub, hsub, ?_⟩
  have : (⟨_, heq ▸ hsub⟩ : ConeSubset (cubeCone (n := 0) c)) = ⟨_, hsub⟩ := Subtype.ext heq
  rw [this, dist_self]

/-! ### `prop:Deltaconvtwisted`, `thm:HCP`, `lma:twistedHcp` -/

/-- **Source `prop:Deltaconvtwisted`, dimension `0`**: for every holomorphic line bundle `T`
(with atlases `b k` of `T ⊗ Lᵏ`), `Δ_{k,T}(L) = Δ_ν(L) = ℝ⁰` for every `k`, so
`Δ_{k,T}(L) → Δ_ν(L)` in the Hausdorff metric. -/
theorem tendsto_hausdorffDist_twistedDegreePolytope_dim_zero {T : X.Modules}
    (b : ∀ k : ℕ, LineBundleAtlas (bundleTensor T (bundleTensorPower L k))) :
    (∀ k, twistedDegreePolytope f 0 E Y hY k (b k) = lineBundleOkounkovBody f 0 E Y hY a) ∧
    Tendsto (fun k => hausdorffDist
        ((EuclideanSpace.equiv (Fin 0) ℝ).symm '' twistedDegreePolytope f 0 E Y hY k (b k))
        ((EuclideanSpace.equiv (Fin 0) ℝ).symm '' lineBundleOkounkovBody f 0 E Y hY a))
      atTop (𝓝 0) := by
  refine ⟨fun k => ?_, ?_⟩
  · rw [twistedDegreePolytope_eq_univ, lineBundleOkounkovBody_eq_univ]
  · simp_rw [hausdorffDist_euclidean]
    exact tendsto_const_nhds

/-- **Source `thm:HCP` and `lma:twistedHcp`, dimension `0`**: for every `φ ∈ PSH(X, θ)`, every
holomorphic line bundle `T` and every cube cone, `Δ_{k,T}(θ, φ) = Δ_ν(θ, φ) = ℝ⁰` for every `k`,
so `Δ_{k,T}(θ, φ) → Δ_ν(θ, φ)` in the Hausdorff metric (for `T = 𝒪_X` as well, with
`Δ_k(θ, φ)`). -/
theorem tendsto_hausdorffDist_twistedMultiplierDegreePolytope_dim_zero
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) (c : ℝ) {T : X.Modules}
    (b : ∀ k : ℕ, LineBundleAtlas (bundleTensor T (bundleTensorPower L k))) :
    (∀ k, (EuclideanSpace.equiv (Fin 0) ℝ).symm ''
        twistedMultiplierDegreePolytope f 0 E Y hY k (b k) φ =
      partialOkounkovBody f 0 E Y hY (cubeCone c) a φ) ∧
    Tendsto (fun k => hausdorffDist
        ((EuclideanSpace.equiv (Fin 0) ℝ).symm ''
          twistedMultiplierDegreePolytope f 0 E Y hY k (b k) φ)
        (partialOkounkovBody f 0 E Y hY (cubeCone c) a φ)) atTop (𝓝 0) ∧
    (∀ k, (EuclideanSpace.equiv (Fin 0) ℝ).symm '' multiplierDegreePolytope f 0 E Y hY a φ k =
      partialOkounkovBody f 0 E Y hY (cubeCone c) a φ) ∧
    Tendsto (fun k => hausdorffDist
        ((EuclideanSpace.equiv (Fin 0) ℝ).symm '' multiplierDegreePolytope f 0 E Y hY a φ k)
        (partialOkounkovBody f 0 E Y hY (cubeCone c) a φ)) atTop (𝓝 0) := by
  have hq := quasiPsh_of_curvature f E a H hφ
  refine ⟨fun k => ?_, ?_, fun k => ?_, ?_⟩
  · rw [twistedMultiplierDegreePolytope_eq_univ f E Y hY k (b k) hq,
      partialOkounkovBody_cubeCone_eq_univ f E Y hY a hq c, image_univ_of_surjective
        (EuclideanSpace.equiv (Fin 0) ℝ).symm.surjective]
  · simp_rw [hausdorffDist_euclidean]
    exact tendsto_const_nhds
  · rw [multiplierDegreePolytope_eq_univ f E Y hY a hq,
      partialOkounkovBody_cubeCone_eq_univ f E Y hY a hq c, image_univ_of_surjective
        (EuclideanSpace.equiv (Fin 0) ℝ).symm.surjective]
  · simp_rw [hausdorffDist_euclidean]
    exact tendsto_const_nhds

/-! ### `prop:Okocurrent`, `prop:IcompimplyDeltacomp`, `thm:Okoucont` -/

/-- **Source `prop:Okocurrent`, dimension `0`**: the partial Okounkov body does not depend on the
choices of `L`, `h₀`, `h`: for any two Hermitian line bundles `(L, h₀ e^{-φ})`,
`(L', h₀' e^{-φ'})` (any atlases, smooth reference metrics and psh weights) and any cube cones,
`Δ_ν(θ, φ) = Δ_ν(θ', φ')` (both are `ℝ⁰`). This contains both steps of the source proof (the
change of `h₀`, and two line bundles with the same curvature current). -/
theorem partialOkounkovBody_eq_of_sameCurrent_dim_zero {L' : X.Modules} (a' : LineBundleAtlas L')
    (H' : SchemeLineBundleMetric f 0 E L') {φ φ' : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hφ' : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H'.curvature a').val φ') (c c' : ℝ) :
    partialOkounkovBody f 0 E Y hY (cubeCone c) a φ =
      partialOkounkovBody f 0 E Y hY (cubeCone c') a' φ' := by
  rw [partialOkounkovBody_cubeCone_eq_univ f E Y hY a (quasiPsh_of_curvature f E a H hφ) c,
    partialOkounkovBody_cubeCone_eq_univ f E Y hY a' (quasiPsh_of_curvature f E a' H' hφ') c']

/-- **Source `prop:IcompimplyDeltacomp`, dimension `0`**: for `ψ ∈ PSH(X, θ)` and every
`φ : X → [-∞, ∞]` (so in particular for `φ ∈ PSH(X, θ)`; `φ ⪯_𝓘 ψ` always holds on a point,
`SGPT.Okounkov.PobDimZero.iOrderOnManifold_of_dim_zero`), `Δ_ν(θ, φ) ⊆ Δ_ν(θ, ψ)`, and
`Δ_ν(θ, φ) ⊆ Δ_ν(L)`. -/
theorem partialOkounkovBody_subset_dim_zero {φ ψ : SchemeComplexPoint f → EReal}
    (hψ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val ψ) (c : ℝ) :
    (letI := E.isSeparated; letI := E.quasiCompact;
      IEnvelope.IOrderOnManifold (n := 0) φ ψ) ∧
    partialOkounkovBody f 0 E Y hY (cubeCone c) a φ ⊆
      partialOkounkovBody f 0 E Y hY (cubeCone c) a ψ ∧
    partialOkounkovBody f 0 E Y hY (cubeCone c) a φ ⊆
      TranscendentalMain.euclideanImage (lineBundleOkounkovBody f 0 E Y hY a) := by
  have hqψ := quasiPsh_of_curvature f E a H hψ
  refine ⟨?_, ?_, ?_⟩
  · let := E.isSeparated
    let := E.quasiCompact
    exact iOrderOnManifold_of_dim_zero φ hqψ
  · rw [partialOkounkovBody_cubeCone_eq_univ f E Y hY a hqψ c]
    exact subset_univ _
  · rw [lineBundleOkounkovBody_eq_univ, TranscendentalMain.euclideanImage,
      image_univ_of_surjective (EuclideanSpace.equiv (Fin 0) ℝ).symm.surjective]
    exact subset_univ _

/-- **Source `thm:Okoucont`, dimension `0`**: the partial Okounkov body map
`PSH(X, θ)_{>0} → 𝒦₀`, `φ ↦ Δ_ν(θ, φ)`, is constant (`= ℝ⁰`), hence continuous for every topology
on `PSH(X, θ)_{>0}`, in particular for `d_S` (for every cube cone). -/
theorem exists_continuous_partialOkounkovBody_dim_zero (c : ℝ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ∀ τ : TopologicalSpace {v : ThetaPshL1 (H.curvature a).val //
        HasPositivePotentialMass (H.curvature a) v.val v.property},
      ∃ G : {v : ThetaPshL1 (H.curvature a).val //
          HasPositivePotentialMass (H.curvature a) v.val v.property} →
          ConvexBody (EuclideanSpace ℝ (Fin 0)),
        Continuous[τ, _] G ∧ ∀ v, (G v : Set (EuclideanSpace ℝ (Fin 0))) =
          partialOkounkovBody f 0 E Y hY (cubeCone c) a v.val.val := by
  let := E.isSeparated
  let := E.quasiCompact
  intro τ
  refine ⟨fun _ => ⟨univ, convex_univ, isCompact_univ, univ_nonempty⟩,
    @continuous_const _ _ τ _ _, fun v => ?_⟩
  exact (partialOkounkovBody_cubeCone_eq_univ f E Y hY a
    (quasiPsh_of_curvature f E a H v.val.property) c).symm

/-- **Source `thm:Okoucont`, dimension `0`, with the `d_S` topology**: for a big class `{θ}`, the
partial Okounkov body map is continuous for the singularity pseudometric `d_S`, in the form of
the positive-dimensional `SGPT.GAGA.H0L.exists_continuous_partialOkounkovBody`. -/
theorem exists_continuous_partialOkounkovBody_dS_dim_zero
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C →
      letI := E.isSeparated
      letI := E.quasiCompact
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
      haveI : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f 0 Y hY
      letI : TopologicalSpace (ThetaPshL1 (H.curvature a).val) :=
        (singularityPseudoMetricSpace (schemeProjectiveTNKahlerBackground f 0 E)
          (H.curvature a) hbig).toUniformSpace.toTopologicalSpace
      ∃ G : {v : ThetaPshL1 (H.curvature a).val //
          HasPositivePotentialMass (H.curvature a) v.val v.property} →
          ConvexBody (EuclideanSpace ℝ (Fin 0)),
        Continuous G ∧ ∀ v, (G v : Set (EuclideanSpace ℝ (Fin 0))) =
          partialOkounkovBody f 0 E Y hY (cubeCone C) a v.val.val :=
  ⟨0, le_rfl, fun C _ => exists_continuous_partialOkounkovBody_dim_zero f E Y hY a H C _⟩

/-! ### `prop:suba`, `thm:concOko`, `prop:res` -/

/-- **Source `prop:suba`, dimension `0`**: for Hermitian line bundles `(L, h)`, `(L', h')`,
`φ + φ'` is `c₁(L ⊗ L', h₀ ⊗ h₀')`-psh and
`Δ_ν(L, h) + Δ_ν(L', h') ⊆ Δ_ν(L ⊗ L', h ⊗ h')` (for every cube cone). -/
theorem partialOkounkovBody_add_subset_tensor_dim_zero {L' : X.Modules}
    (a' : LineBundleAtlas L') (H' : SchemeLineBundleMetric f 0 E L') (c : ℝ)
    {φ φ' : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hφ' : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H'.curvature a').val φ') :
    (letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential ((H.tensorProduct H' a a').curvature (pairwiseTensorAtlas a a')).val
        (fun x => φ x + φ' x)) ∧
    partialOkounkovBody f 0 E Y hY (cubeCone c) a φ +
        partialOkounkovBody f 0 E Y hY (cubeCone c) a' φ' ⊆
      partialOkounkovBody f 0 E Y hY (cubeCone c) (pairwiseTensorAtlas a a')
        (fun x => φ x + φ' x) := by
  have hfin := finite_add (finite_of_curvature f E a H hφ) (finite_of_curvature f E a' H' hφ')
  have hsum : (letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential ((H.tensorProduct H' a a').curvature (pairwiseTensorAtlas a a')).val
        (fun x => φ x + φ' x)) := by
    let := E.isSeparated
    let := E.quasiCompact
    exact isThetaPshPotential_of_finite _ hfin
  refine ⟨hsum, ?_⟩
  rw [partialOkounkovBody_cubeCone_eq_univ f E Y hY _ (quasiPsh_of_curvature f E _ _ hsum) c]
  exact subset_univ _

/-- **Source `thm:concOko`, dimension `0`**: for `φ, ψ ∈ PSH(X, θ)` and every real `t ∈ (0, 1)`,
`tφ + (1 - t)ψ ∈ PSH(X, θ)` and
`Δ_ν(θ, tφ + (1 - t)ψ) ⊇ tΔ_ν(θ, φ) + (1 - t)Δ_ν(θ, ψ)` (for every cube cone). -/
theorem convexComb_partialOkounkovBody_subset_dim_zero (c : ℝ) {φ ψ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hψ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val ψ) (t : ℝ) :
    (letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val
        (SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination.convexComb t φ ψ)) ∧
    t • partialOkounkovBody f 0 E Y hY (cubeCone c) a φ +
        (1 - t) • partialOkounkovBody f 0 E Y hY (cubeCone c) a ψ ⊆
      partialOkounkovBody f 0 E Y hY (cubeCone c) a
        (SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination.convexComb t φ ψ) := by
  have hfin := finite_add (finite_coe_mul (finite_of_curvature f E a H hφ) t)
    (finite_coe_mul (finite_of_curvature f E a H hψ) (1 - t))
  have hcomb : (letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val
        (SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination.convexComb t φ ψ)) := by
    let := E.isSeparated
    let := E.quasiCompact
    exact isThetaPshPotential_of_finite _ hfin
  refine ⟨hcomb, ?_⟩
  rw [partialOkounkovBody_cubeCone_eq_univ f E Y hY a (quasiPsh_of_curvature f E a H hcomb) c]
  exact subset_univ _

/-- **Source `prop:res`, dimension `0`**: for every integer `p > 0`, `pφ` is
`c₁(Lᵖ, h₀ᵖ)`-psh and `Δ_ν(pθ, pφ) = pΔ_ν(θ, φ)` (for every cube cone). -/
theorem partialOkounkovBody_tensorPower_eq_smul_dim_zero (c : ℝ) {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) (p : ℕ) (hp : 0 < p) :
    (letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential ((H.tensorPower a p).curvature (a.tensorPower p)).val
        (fun x => ((p : ℝ) : EReal) * φ x)) ∧
    partialOkounkovBody f 0 E Y hY (cubeCone c) (a.tensorPower p)
        (fun x => ((p : ℝ) : EReal) * φ x) =
      (p : ℝ) • partialOkounkovBody f 0 E Y hY (cubeCone c) a φ := by
  have hpsh : (letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential ((H.tensorPower a p).curvature (a.tensorPower p)).val
        (fun x => ((p : ℝ) : EReal) * φ x)) := by
    let := E.isSeparated
    let := E.quasiCompact
    exact isThetaPshPotential_of_finite _ (finite_coe_mul (finite_of_curvature f E a H hφ) p)
  refine ⟨hpsh, ?_⟩
  rw [partialOkounkovBody_cubeCone_eq_univ f E Y hY _ (quasiPsh_of_curvature f E _ _ hpsh) c,
    partialOkounkovBody_cubeCone_eq_univ f E Y hY a (quasiPsh_of_curvature f E a H hφ) c,
    Set.smul_set_univ₀ (by exact_mod_cast hp.ne')]

/-! ### `prop:Deltapert` and `lma:Hausconvbetato0` -/

/-- The algebraic body `Δ_ν(θ + δω + dd^c φ) = q⁻¹ Δ_ν(Lᵠ ⊗ Aᵖ, qφ)` of source
`eq:DeltanuTalgebraic1` for `δ = p/q ≥ 0` (written with the reduced fraction of `δ`). -/
def perturbBody {A : X.Modules} (aA : LineBundleAtlas A) (c : ℝ)
    (φ : SchemeComplexPoint f → EReal) (δ : ℚ) : Set (EuclideanSpace ℝ (Fin 0)) :=
  ((δ.den : ℝ))⁻¹ • partialOkounkovBody f 0 E Y hY (cubeCone c)
    (SGPT.Okounkov.OkoNS.perturbAtlas a aA δ.den δ.num.toNat)
    (fun x => ((δ.den : ℝ) : EReal) * φ x)

/-- **Source `prop:Deltapert`, dimension `0`**: let `(A, h_A)` be a Hermitian line bundle,
`ω = c₁(A, h_A)`. For every rational `δ = p/q ≥ 0`, `qφ` is `c₁(Lᵠ ⊗ Aᵖ, h₀ᵠ ⊗ h_Aᵖ)`-psh and
`Δ_ν(θ + δω + dd^c φ) = q⁻¹ Δ_ν(Lᵠ ⊗ Aᵖ, qφ) = Δ_ν(θ_φ)`; hence the bodies
`Δ_ν(θ + δω + dd^c φ)` are decreasing as `δ ↘ 0` and converge to `Δ_ν(θ_φ)` in the Hausdorff
metric (for every cube cone). -/
theorem partialOkounkovBody_perturb_dim_zero {A : X.Modules} (aA : LineBundleAtlas A)
    (HA : SchemeLineBundleMetric f 0 E A) {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) (c : ℝ) :
    (∀ (δ : ℚ) (q p : ℕ), 0 < q → δ = (p : ℚ) / q →
      (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (((H.tensorPower a q).tensorProduct (HA.tensorPower aA p)
          (a.tensorPower q) (aA.tensorPower p)).curvature
            (SGPT.Okounkov.OkoNS.perturbAtlas a aA q p)).val
          (fun x => ((q : ℝ) : EReal) * φ x)) ∧
      ((q : ℝ))⁻¹ • partialOkounkovBody f 0 E Y hY (cubeCone c)
          (SGPT.Okounkov.OkoNS.perturbAtlas a aA q p) (fun x => ((q : ℝ) : EReal) * φ x) =
        partialOkounkovBody f 0 E Y hY (cubeCone c) a φ) ∧
    (∀ δ δ' : ℚ, 0 ≤ δ → δ ≤ δ' →
      perturbBody f E Y hY a aA c φ δ ⊆ perturbBody f E Y hY a aA c φ δ') ∧
    Tendsto (fun δ : ℚ => hausdorffDist (perturbBody f E Y hY a aA c φ δ)
        (partialOkounkovBody f 0 E Y hY (cubeCone c) a φ)) (𝓝[>] 0) (𝓝 0) := by
  have hfin := finite_of_curvature f E a H hφ
  have hbody : ∀ q p : ℕ, 0 < q → ((q : ℝ))⁻¹ • partialOkounkovBody f 0 E Y hY (cubeCone c)
      (SGPT.Okounkov.OkoNS.perturbAtlas a aA q p) (fun x => ((q : ℝ) : EReal) * φ x) = univ := by
    intro q p hq
    have hq' : (letI := E.isSeparated; letI := E.quasiCompact;
        IsGlobalQuasiPshPotential (n := 0) (fun x => ((q : ℝ) : EReal) * φ x)) := by
      let := E.isSeparated
      let := E.quasiCompact
      exact isGlobalQuasiPshPotential_of_finite (finite_coe_mul hfin q)
    rw [partialOkounkovBody_cubeCone_eq_univ f E Y hY _ hq' c,
      Set.smul_set_univ₀ (inv_ne_zero (by exact_mod_cast hq.ne'))]
  have hΔ := partialOkounkovBody_cubeCone_eq_univ f E Y hY a (quasiPsh_of_curvature f E a H hφ) c
  refine ⟨fun δ q p hq _ => ⟨?_, by rw [hbody q p hq, hΔ]⟩, fun δ δ' _ _ => ?_, ?_⟩
  · let := E.isSeparated
    let := E.quasiCompact
    exact isThetaPshPotential_of_finite _ (finite_coe_mul hfin q)
  · rw [perturbBody, perturbBody, hbody _ _ δ'.den_pos]
    exact subset_univ _
  · simp_rw [hausdorffDist_euclidean]
    exact tendsto_const_nhds

/-- The algebraic body `Δ_ν((1 - β)θ, φ) = q⁻¹ Δ_ν(L^{q - p}, qφ)` of source
`eq:DeltanuTalgebraic1` for `β = p/q` (written with the reduced fraction of `β`). -/
def oneSubBody (c : ℝ) (φ : SchemeComplexPoint f → EReal) (β : ℚ) :
    Set (EuclideanSpace ℝ (Fin 0)) :=
  ((β.den : ℝ))⁻¹ • partialOkounkovBody f 0 E Y hY (cubeCone c)
    (a.tensorPower (β.den - β.num.toNat)) (fun x => ((β.den : ℝ) : EReal) * φ x)

/-- **Source `lma:Hausconvbetato0`, dimension `0`**: for every `φ ∈ PSH(X, θ)` (in particular when
`θ_φ` is a Kähler current) and every rational `β = p/q ∈ (0, 1)`, `φ` is `(1 - β)θ`-psh and
`Δ_ν((1 - β)θ, φ) = q⁻¹ Δ_ν(L^{q - p}, qφ) = Δ_ν(θ, φ)`; hence
`Δ_ν((1 - β)θ, φ) → Δ_ν(θ, φ)` in the Hausdorff metric as `ℚ ∋ β → 0+` (for every cube cone). -/
theorem tendsto_hausdorffDist_one_sub_dim_zero {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) (c : ℝ) :
    (∀ (β : ℚ) (q p : ℕ), 0 < q → β = (p : ℚ) / q → 0 < β → β < 1 →
      (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential ((1 - (β : ℝ)) • H.curvature a).val φ) ∧
      ((q : ℝ))⁻¹ • partialOkounkovBody f 0 E Y hY (cubeCone c) (a.tensorPower (q - p))
          (fun x => ((q : ℝ) : EReal) * φ x) =
        partialOkounkovBody f 0 E Y hY (cubeCone c) a φ) ∧
    Tendsto (fun β : ℚ => hausdorffDist (oneSubBody f E Y hY a c φ β)
        (partialOkounkovBody f 0 E Y hY (cubeCone c) a φ)) (𝓝[>] 0) (𝓝 0) := by
  have hfin := finite_of_curvature f E a H hφ
  refine ⟨fun β q p hq _ _ _ => ⟨?_, ?_⟩, ?_⟩
  · let := E.isSeparated
    let := E.quasiCompact
    exact isThetaPshPotential_of_finite _ hfin
  · have hq' : (letI := E.isSeparated; letI := E.quasiCompact;
        IsGlobalQuasiPshPotential (n := 0) (fun x => ((q : ℝ) : EReal) * φ x)) := by
      let := E.isSeparated
      let := E.quasiCompact
      exact isGlobalQuasiPshPotential_of_finite (finite_coe_mul hfin q)
    rw [partialOkounkovBody_cubeCone_eq_univ f E Y hY _ hq' c,
      Set.smul_set_univ₀ (inv_ne_zero (by exact_mod_cast hq.ne')),
      partialOkounkovBody_cubeCone_eq_univ f E Y hY a (quasiPsh_of_curvature f E a H hφ) c]
  · simp_rw [hausdorffDist_euclidean]
    exact tendsto_const_nhds

/-! ### `cor:Okounvol`, `prop:Okounonlydepnum` -/

/-- **Source `cor:Okounvol`, dimension `0`**, unconditionally: `vol Δ_ν(L) = vol L / 0!`
(both sides are `1`; every line bundle is big in dimension `0`). -/
theorem volume_eq_factorial_mul_okounkovBody_dim_zero :
    SGPT.LineBundle.volume f L 0 = ENNReal.ofReal (((0 : ℕ).factorial : ℝ) *
      volume.real (lineBundleOkounkovBody f 0 E Y hY a)) := by
  rw [lineBundle_volume_eq_one f E Y hY a, lineBundleOkounkovBody_eq_univ, measureReal_def,
    volume_univ_fun]
  simp

/-- **Source `prop:Okounonlydepnum`, dimension `0`**: `Δ_ν(L)` does not depend on `L` at all (it
is `ℝ⁰` for every line bundle), in particular it only depends on the numerical class of `L`. -/
theorem lineBundleOkounkovBody_eq_dim_zero {L' : X.Modules} (a' : LineBundleAtlas L') :
    lineBundleOkounkovBody f 0 E Y hY a = lineBundleOkounkovBody f 0 E Y hY a' := by
  rw [lineBundleOkounkovBody_eq_univ, lineBundleOkounkovBody_eq_univ]

/-! ### `cor:Deltacontimplyvarphi` -/

section IOrder

open SGPT.PSH.VariableComplexAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel 0) M]
  [IsComplexManifold 0 M]

/-- A `θ`-psh potential (for a native closed form `θ`) on a manifold of dimension `0` is
quasi-psh in the atlas sense. -/
theorem isQPSH_of_isThetaPshPotential_dim_zero {θ : ClosedRealOneOneForm 0 M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) : (ofFixedModel 0 M).IsQPSH u := by
  refine ⟨nativeClosedFormToAtlas θ, (isThetaPSH_iff_nativeThetaPotential _ u).mpr ?_⟩
  have : atlasClosedFormToNative (nativeClosedFormToAtlas θ) = θ := by
    rcases θ with ⟨θ, hθ⟩
    cases θ
    rfl
  rw [this]
  exact hu

/-- **Source `cor:Deltacontimplyvarphi`, dimension `0`**: on a manifold of dimension `0`, for all
`φ, ψ ∈ PSH(X, θ)` one has `φ ⪯_𝓘 ψ` (in the source's sense `sourceIOrder`); so the implication
of the corollary holds, whatever the partial Okounkov bodies are. -/
theorem sourceIOrder_dim_zero (θ : ClosedRealOneOneForm 0 M) {φ ψ : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hψ : IsThetaPshPotential θ.val ψ) :
    sourceIOrder (ofFixedModel 0 M) φ ψ :=
  (sourceIOrder_iff_native (isQPSH_of_isThetaPshPotential_dim_zero hφ)
    (isQPSH_of_isThetaPshPotential_dim_zero hψ)).mpr
    (ZeroDimensionalQuasiPshMultiplierIdeals.iOrderOnManifold_of_genuine_right φ
      hψ.quasiPshPotential)

end IOrder

/-! ### Arbitrary valuations in dimension zero -/

section Valuation

variable (c : X) (v : AddValuation X.functionField (WithTop (Lex (Fin 0 → ℤ))))

/-- In dimension `0`, the section set `Γ_ν(θ, φ)` of an arbitrary valuation is that of the flag
valuation. -/
theorem valuation_multiplierSectionSet_eq_flag {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) :
    AlgebraicValuation.multiplierSectionSet f 0 E v c a φ =
      multiplierSectionSet f 0 E Y hY a φ := by
  have hq := quasiPsh_of_curvature f E a H hφ
  rw [valuation_multiplierSectionSet_eq f E Y hY a c v hq, multiplierSectionSet_eq f E Y hY a hq]

/-- In dimension `0`, `Γ^∞_ν(θ, φ)` of an arbitrary valuation is that of the flag valuation. -/
theorem valuation_inftySectionSet_eq_flag {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) :
    AlgebraicValuation.inftySectionSet f 0 E v c a φ = inftySectionSet f 0 E Y hY a φ := by
  have hq := quasiPsh_of_curvature f E a H hφ
  rw [valuation_inftySectionSet_eq f E Y hY a c v hq, inftySectionSet_eq f E Y hY a hq]

/-- In dimension `0`, the partial Okounkov body `Δ_ν(θ, φ)` of an arbitrary valuation (relative to
any admissible cone `C`) is that of the flag valuation. -/
theorem valuation_partialBody_eq_partialOkounkovBody {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) (C : AdmissibleCone 0) :
    SGPT.Okounkov.ValGen.partialBody f 0 E v c a C φ = partialOkounkovBody f 0 E Y hY C a φ := by
  change SGPT.Okounkov.ValGen.setBody C _ = SGPT.Okounkov.ValGen.setBody C _
  rw [valuation_multiplierSectionSet_eq_flag f E Y hY a H c v hφ]

/-- In dimension `0`, `Δ_ν(L)` of an arbitrary valuation is that of the flag valuation. -/
theorem valuation_okounkovBody_eq_flag :
    AlgebraicValuation.okounkovBody v c a = lineBundleOkounkovBody f 0 E Y hY a := by
  rw [valuation_okounkovBody_eq_univ f E Y hY a c v, lineBundleOkounkovBody_eq_univ]

include E Y hY in
/-- **Source `prop:Okounbiglbdl` for an arbitrary valuation, dimension `0`**: `Γ_ν(L)` is the
semigroup `{(0, k) : k ∈ ℕ}`; it lies in every admissible cone `C ∋ (0, 1)` (e.g. the cone over
the convex body `Δ_ν(L) = ℝ⁰`) and generates `ℤ⁰⁺¹`, i.e. `Γ_ν(L) ∈ 𝒮'(C)`. This is the
hypothesis under which the arbitrary-valuation statements of `SGPT.Okounkov.ValGen` are proved. -/
theorem valuation_sectionSemigroup_mem_fullSemigroupLocus (C : AdmissibleCone 0)
    (h1 : ((0 : Fin 0 → ℝ), (1 : ℝ)) ∈ C.cone) :
    ∃ hS : AlgebraicValuation.sectionSemigroup v c a ≤ latticePoints C.cone,
      LatticeSlices.generatedGroup (AlgebraicValuation.sectionSemigroup v c a) = ⊤ ∧
      sourceSubset C _ hS ∈ fullSemigroupLocus C := by
  have heq := valuation_sectionSemigroup_eq f E Y hY a c v
  have hS : AlgebraicValuation.sectionSemigroup v c a ≤ latticePoints C.cone :=
    heq ▸ nonnegHeight_le_latticePoints C h1
  refine ⟨hS, heq ▸ generatedGroup_nonnegHeight, ?_⟩
  exact sourceSubset_mem_fullSemigroupLocus C _ hS (heq ▸ generatedGroup_nonnegHeight)

end Valuation

end SGPT.Okounkov.PobDimZero
