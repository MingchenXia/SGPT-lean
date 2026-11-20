import SGPT.Okounkov.PobDimZeroBook

/-!
# Statements of `sec:PoB` in every dimension


The book's `X` in Section *Algebraic partial Okounkov bodies* (`sec:PoB`) has any dimension `n`.
The statements below are written for `X` of relative dimension `n` (any `n`, including `0`) in the
setting of the positive-dimensional Lean statements (`X` an integral smooth projective complex
scheme with a smooth flag `Y`, `L` with atlas `a` and smooth metric `H`, `θ = c₁(L, H)`). For
`n = m + 1` each of them is the corresponding positive-dimensional statement of lanes H0-GAGA3,
OKO-CLOSE, OKO-NS (literally, with `m + 1` replaced by `n`; the positivity hypothesis
`vol θ_φ > 0` is written as `0 < vol θ_φ = iVolume θ φ`, which for `n = m + 1` implies the
hypothesis `0 < vol Δ_{Y•}(θ_φ)` of those statements by
`SGPT.Okounkov.AlgPOB.volume_real_generalPartialBody_pos`); for `n = 0` it is proved in
`PobDimZeroBook`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.PobDimZero

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus SGPT.Foundations.Analysis.Pending.DiagonalMass
  SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology
  SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDistance
open SGPT.AlmostSemigroup SGPT.AlmostSemigroup.Class
open scoped Topology ENNReal Pointwise

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] (n : ℕ) [SmoothOfRelativeDimension n f]

local instance pobDimTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance pobDimCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance pobDimManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)

/-- **Source `cor:POBvolume` in every dimension `n`**: for all large cube cones and every
`φ ∈ PSH(X, θ)_{>0}`, `vol Δ_{Y•}(θ, φ) = vol θ_φ / n!`. For `n = m + 1` this is
`SGPT.GAGA.H0L.volume_partialOkounkovBody`. -/
theorem volume_partialOkounkovBody_dim [Nonempty (SchemeComplexPoint f)] :
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
        volume (partialOkounkovBody f n E Y hY (cubeCone C) a φ) =
          iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ /
            (n.factorial : ℝ≥0∞)) := by
  cases n with
  | zero => exact volume_partialOkounkovBody_dim_zero f E Y hY a H
  | succ m => exact SGPT.GAGA.H0L.volume_partialOkounkovBody f E Y hY a H

/-- **Source `prop:Deltaconvtwisted` in every dimension `n`**: for a big line bundle `L` and every
holomorphic line bundle `T`, `Δ_{k,T}(L) → Δ_{Y•}(L)` in the Hausdorff metric. For `n = m + 1`
this is `SGPT.GAGA.OkoClose.tendsto_hausdorffDist_twistedDegreePolytope`. -/
theorem tendsto_hausdorffDist_twistedDegreePolytope_dim {T : X.Modules} (aT : LineBundleAtlas T)
    [Nonempty (SchemeComplexPoint f)] (hbig : SGPT.LineBundle.IsBig f L n)
    (b : ∀ k : ℕ, LineBundleAtlas (bundleTensor T (bundleTensorPower L k))) :
    Tendsto (fun k => hausdorffDist
        ((EuclideanSpace.equiv (Fin n) ℝ).symm '' twistedDegreePolytope f n E Y hY k (b k))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm '' lineBundleOkounkovBody f n E Y hY a))
      atTop (𝓝 0) := by
  cases n with
  | zero => exact (tendsto_hausdorffDist_twistedDegreePolytope_dim_zero f E Y hY a b).2
  | succ m =>
    exact SGPT.GAGA.OkoClose.tendsto_hausdorffDist_twistedDegreePolytope f E Y hY a aT hbig b

include H in
/-- **Source `cor:Okounvol` in every dimension `n`**: for a big line bundle `L`,
`vol L = n! vol Δ_{Y•}(L)`. For `n = m + 1` this is
`SGPT.GAGA.H0L.volume_eq_factorial_mul_okounkovBody`. -/
theorem volume_eq_factorial_mul_okounkovBody_dim [Nonempty (SchemeComplexPoint f)]
    (hbig : SGPT.LineBundle.IsBig f L n) :
    SGPT.LineBundle.volume f L n = ENNReal.ofReal ((n.factorial : ℝ) *
      volume.real (lineBundleOkounkovBody f n E Y hY a)) := by
  cases n with
  | zero => exact volume_eq_factorial_mul_okounkovBody_dim_zero f E Y hY a
  | succ m => exact SGPT.GAGA.H0L.volume_eq_factorial_mul_okounkovBody f E Y hY a H hbig

/-- **Source `prop:Okounonlydepnum` in every dimension `n`**, in the form proved for flags in
positive dimension: big line bundles with the same real first Chern class have the same
Okounkov body. For `n = m + 1` this is
`SGPT.Okounkov.OkoNS.lineBundleOkounkovBody_eq_of_chernClass_eq`. -/
theorem lineBundleOkounkovBody_eq_of_chernClass_eq_dim [Nonempty (SchemeComplexPoint f)]
    {L' : X.Modules} (a' : LineBundleAtlas L') (H' : SchemeLineBundleMetric f n E L')
    (hbig : SGPT.LineBundle.IsBig f L n) (hbig' : SGPT.LineBundle.IsBig f L' n)
    (hclass : letI := E.isSeparated; letI := E.quasiCompact;
      RealBottChern.ofRepresentative (H.curvature a) =
        RealBottChern.ofRepresentative (H'.curvature a')) :
    lineBundleOkounkovBody f n E Y hY a = lineBundleOkounkovBody f n E Y hY a' := by
  cases n with
  | zero => exact lineBundleOkounkovBody_eq_dim_zero f E Y hY a a'
  | succ m =>
    exact SGPT.Okounkov.OkoNS.lineBundleOkounkovBody_eq_of_chernClass_eq f E Y hY a H a' H' hbig
      hbig' hclass

/-- **Source `thm:Okoucont` in every dimension `n`**: for a big class `{θ}` and all large cube
cones, `φ ↦ Δ_{Y•}(θ, φ)` is continuous from `(PSH(X, θ)_{>0}, d_S)` to `(𝒦ₙ, d_Haus)`. For
`n = m + 1` this is `SGPT.GAGA.H0L.exists_continuous_partialOkounkovBody`. -/
theorem exists_continuous_partialOkounkovBody_dim [Nonempty (SchemeComplexPoint f)]
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C →
      letI := E.isSeparated
      letI := E.quasiCompact
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
      haveI : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f n Y hY
      letI : TopologicalSpace (ThetaPshL1 (H.curvature a).val) :=
        (singularityPseudoMetricSpace (schemeProjectiveTNKahlerBackground f n E)
          (H.curvature a) hbig).toUniformSpace.toTopologicalSpace
      ∃ G : {v : ThetaPshL1 (H.curvature a).val //
          HasPositivePotentialMass (H.curvature a) v.val v.property} →
          ConvexBody (EuclideanSpace ℝ (Fin n)),
        Continuous G ∧ ∀ v, (G v : Set (EuclideanSpace ℝ (Fin n))) =
          partialOkounkovBody f n E Y hY (cubeCone C) a v.val.val := by
  cases n with
  | zero => exact exists_continuous_partialOkounkovBody_dS_dim_zero f E Y hY a H hbig
  | succ m => exact SGPT.GAGA.H0L.exists_continuous_partialOkounkovBody f E Y hY a H hbig

/-- **Source `prop:IcompimplyDeltacomp` in every dimension `n`**: for all large cube cones and
`φ, ψ ∈ PSH(X, θ)_{>0}` with `φ ⪯_𝓘 ψ`, `Δ_{Y•}(θ, φ) ⊆ Δ_{Y•}(θ, ψ)`. For `n = m + 1` this is
`SGPT.GAGA.H0L.partialOkounkovBody_subset_of_iOrder`. -/
theorem partialOkounkovBody_subset_of_iOrder_dim [Nonempty (SchemeComplexPoint f)] :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ φ ψ : SchemeComplexPoint f → EReal,
      ∀ hφ : (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val φ),
      ∀ hψ : (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val ψ),
      (letI := E.isSeparated; letI := E.quasiCompact;
        letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
        haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
        haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
        0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ) →
      (letI := E.isSeparated; letI := E.quasiCompact;
        letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
        haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
        haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
        0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) ψ hψ) →
      (letI := E.isSeparated; letI := E.quasiCompact;
        IEnvelope.IOrderOnManifold (n := n) φ ψ) →
      partialOkounkovBody f n E Y hY (cubeCone C) a φ ⊆
        partialOkounkovBody f n E Y hY (cubeCone C) a ψ := by
  cases n with
  | zero =>
    exact ⟨0, le_rfl, fun C _ φ ψ _ hψ _ _ _ =>
      (partialOkounkovBody_subset_dim_zero f E Y hY a H hψ C).2.1⟩
  | succ m =>
    obtain ⟨C₀, hC₀, hC⟩ := SGPT.GAGA.H0L.partialOkounkovBody_subset_of_iOrder f E Y hY a H
    exact ⟨C₀, hC₀, fun C hC' φ ψ hφ hψ hpφ hpψ hI => hC C hC' φ ψ hφ hψ
      (SGPT.Okounkov.AlgPOB.volume_real_generalPartialBody_pos f E Y hY a H hφ hpφ)
      (SGPT.Okounkov.AlgPOB.volume_real_generalPartialBody_pos f E Y hY a H hψ hpψ) hI⟩

/-- **Source `prop:IcompimplyDeltacomp`, second assertion, in every dimension `n`**: for a big
line bundle `L`, all large cube cones and `φ ∈ PSH(X, θ)_{>0}`, `Δ_{Y•}(θ, φ) ⊆ Δ_{Y•}(L)`. For
`n = m + 1` this is `SGPT.GAGA.H0L.partialOkounkovBody_subset_lineBundleOkounkovBody`. -/
theorem partialOkounkovBody_subset_lineBundleOkounkovBody_dim [Nonempty (SchemeComplexPoint f)]
    (hbig : SGPT.LineBundle.IsBig f L n) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ φ : SchemeComplexPoint f → EReal,
      ∀ hφ : (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val φ),
      (letI := E.isSeparated; letI := E.quasiCompact;
        letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
        haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
        haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
        0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ) →
      partialOkounkovBody f n E Y hY (cubeCone C) a φ ⊆
        TranscendentalMain.euclideanImage (lineBundleOkounkovBody f n E Y hY a) := by
  cases n with
  | zero =>
    exact ⟨0, le_rfl, fun C _ φ hφ _ => (partialOkounkovBody_subset_dim_zero f E Y hY a H hφ C).2.2⟩
  | succ m =>
    obtain ⟨C₀, hC₀, hC⟩ :=
      SGPT.GAGA.H0L.partialOkounkovBody_subset_lineBundleOkounkovBody f E Y hY a H hbig
    exact ⟨C₀, hC₀, fun C hC' φ hφ hpφ => hC C hC' φ hφ
      (SGPT.Okounkov.AlgPOB.volume_real_generalPartialBody_pos f E Y hY a H hφ hpφ)⟩

/-- **Source `prop:suba` in every dimension `n`**: for Hermitian line bundles `(L, h)`, `(L', h')`
with `φ ∈ PSH(X, θ)_{>0}`, `φ' ∈ PSH(X, θ')_{>0}`, `φ + φ'` is `c₁(L ⊗ L', h₀ ⊗ h₀')`-psh and
`Δ_{Y•}(L, h) + Δ_{Y•}(L', h') ⊆ Δ_{Y•}(L ⊗ L', h ⊗ h')` for all large cube cones. For `n = m + 1`
this is `SGPT.Okounkov.OkoNS.partialOkounkovBody_add_subset_tensor`. -/
theorem partialOkounkovBody_add_subset_tensor_dim [Nonempty (SchemeComplexPoint f)]
    {L' : X.Modules} (a' : LineBundleAtlas L') (H' : SchemeLineBundleMetric f n E L') :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ φ φ' : SchemeComplexPoint f → EReal,
      ∀ hφ : (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val φ),
      ∀ hφ' : (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H'.curvature a').val φ'),
      (letI := E.isSeparated; letI := E.quasiCompact;
        letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
        haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
        haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
        0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ) →
      (letI := E.isSeparated; letI := E.quasiCompact;
        letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
        haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
        haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
        0 < iVolume (H'.curvature a') (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ'
          hφ') →
      (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential ((H.tensorProduct H' a a').curvature (pairwiseTensorAtlas a a')).val
          (fun x => φ x + φ' x)) ∧
      partialOkounkovBody f n E Y hY (cubeCone C) a φ +
          partialOkounkovBody f n E Y hY (cubeCone C) a' φ' ⊆
        partialOkounkovBody f n E Y hY (cubeCone C) (pairwiseTensorAtlas a a')
          (fun x => φ x + φ' x) := by
  cases n with
  | zero =>
    exact ⟨0, le_rfl, fun C _ φ φ' hφ hφ' _ _ =>
      partialOkounkovBody_add_subset_tensor_dim_zero f E Y hY a H a' H' C hφ hφ'⟩
  | succ m =>
    obtain ⟨C₀, hC₀, hC⟩ :=
      SGPT.Okounkov.OkoNS.partialOkounkovBody_add_subset_tensor f E Y hY a H a' H'
    exact ⟨C₀, hC₀, fun C hC' φ φ' hφ hφ' hpφ hpφ' => hC C hC' φ φ' hφ hφ'
      (SGPT.Okounkov.AlgPOB.volume_real_generalPartialBody_pos f E Y hY a H hφ hpφ)
      (SGPT.Okounkov.AlgPOB.volume_real_generalPartialBody_pos f E Y hY a' H' hφ' hpφ')⟩

/-- **Source `thm:concOko` (rational `t`) in every dimension `n`**: for all large cube cones,
`φ, ψ ∈ PSH(X, θ)_{>0}` and `t ∈ ℚ ∩ (0, 1)` with `tφ + (1 - t)ψ ∈ PSH(X, θ)_{>0}`,
`tΔ_{Y•}(θ, φ) + (1 - t)Δ_{Y•}(θ, ψ) ⊆ Δ_{Y•}(θ, tφ + (1 - t)ψ)`. For `n = m + 1` this is
`SGPT.GAGA.H0L.convexComb_mem_partialOkounkovBody`; in dimension `0` all real `t` are allowed
(`convexComb_partialOkounkovBody_subset_dim_zero`). -/
theorem convexComb_mem_partialOkounkovBody_dim [Nonempty (SchemeComplexPoint f)] :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ φ ψ : SchemeComplexPoint f → EReal,
      ∀ hφ : (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val φ),
      ∀ hψ : (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val ψ),
      ∀ t : ℚ, 0 < t → t < 1 →
      ∀ hχ : (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val
          (SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination.convexComb (t : ℝ) φ ψ)),
      (letI := E.isSeparated; letI := E.quasiCompact;
        letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
        haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
        haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
        0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ) →
      (letI := E.isSeparated; letI := E.quasiCompact;
        letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
        haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
        haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
        0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) ψ hψ) →
      (letI := E.isSeparated; letI := E.quasiCompact;
        letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
        haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
        haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
        0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _)
          (SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination.convexComb (t : ℝ) φ ψ) hχ) →
      (t : ℝ) • partialOkounkovBody f n E Y hY (cubeCone C) a φ +
          (1 - (t : ℝ)) • partialOkounkovBody f n E Y hY (cubeCone C) a ψ ⊆
        partialOkounkovBody f n E Y hY (cubeCone C) a
          (SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination.convexComb (t : ℝ) φ ψ) := by
  cases n with
  | zero =>
    exact ⟨0, le_rfl, fun C _ φ ψ hφ hψ t _ _ _ _ _ _ =>
      (convexComb_partialOkounkovBody_subset_dim_zero f E Y hY a H C hφ hψ t).2⟩
  | succ m =>
    obtain ⟨C₀, hC₀, hC⟩ := SGPT.GAGA.H0L.convexComb_mem_partialOkounkovBody f E Y hY a H
    exact ⟨C₀, hC₀, fun C hC' φ ψ hφ hψ t ht0 ht1 hχ hpφ hpψ hpχ => hC C hC' φ ψ hφ hψ t ht0 ht1
      hχ (SGPT.Okounkov.AlgPOB.volume_real_generalPartialBody_pos f E Y hY a H hφ hpφ)
      (SGPT.Okounkov.AlgPOB.volume_real_generalPartialBody_pos f E Y hY a H hψ hpψ)
      (SGPT.Okounkov.AlgPOB.volume_real_generalPartialBody_pos f E Y hY a H hχ hpχ)⟩

/-- **Source `thm:Gammaasg`, the well-definedness in `def:Okounkov:L687` and `cor:POBvolume`
(volume of `Γ(θ, φ)`), in every dimension `n`**: for all large cube cones `C([0, C]ⁿ)` and every
`φ ∈ PSH(X, θ)_{>0}`, `Γ(θ, φ) ⊆ C([0, C]ⁿ)`, `Γ(θ, φ) ∈ 𝒮'(C([0, C]ⁿ))‾_{>0}` and
`vol Γ(θ, φ) = vol θ_φ / n!`. For `n = m + 1` it combines
`SGPT.Okounkov.AlgPOB.exists_cubeCone_contains`,
`SGPT.GAGA.H0L.multiplierConeSubset_mem_almostSemigroupLocus`
and `SGPT.Okounkov.AlgPOB.volume_real_generalPartialBody`. -/
theorem multiplierSectionSet_mem_almostSemigroupLocus_dim [Nonempty (SchemeComplexPoint f)] :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ φ : SchemeComplexPoint f → EReal,
      ∀ hφ : (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val φ),
      (letI := E.isSeparated; letI := E.quasiCompact;
        letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
        haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
        haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
        0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ) →
      ∃ hsub : multiplierSectionSet f n E Y hY a φ ⊆
          (latticePoints (cubeCone (n := n) C).cone : Set _),
        (⟨_, hsub⟩ : ConeSubset (cubeCone (n := n) C)) ∈ almostSemigroupLocus (cubeCone C) ∧
        ConeSubset.volume (⟨_, hsub⟩ : ConeSubset (cubeCone (n := n) C)) =
          (letI := E.isSeparated; letI := E.quasiCompact;
            letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
            haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
            haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
            (iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ
              hφ).toReal / (n.factorial : ℝ)) := by
  cases n with
  | zero =>
    refine ⟨0, le_rfl, fun C _ φ hφ _ => ?_⟩
    obtain ⟨hsub, -, h2, h3, -⟩ :=
      multiplierSectionSet_mem_almostSemigroupLocus_dim_zero f E Y hY a H hφ C
    exact ⟨hsub, h2, h3⟩
  | succ m =>
    obtain ⟨C₀, hC₀, hC⟩ := SGPT.Okounkov.AlgPOB.exists_cubeCone_contains f E Y hY a H
    refine ⟨C₀, hC₀, fun C hC' φ hφ hpos => ?_⟩
    obtain ⟨hsub, hKC⟩ := hC C hC' φ hφ
    obtain ⟨h1, h2⟩ := SGPT.GAGA.H0L.multiplierConeSubset_mem_almostSemigroupLocus f E Y hY a H hφ
      (SGPT.Okounkov.AlgPOB.volume_real_generalPartialBody_pos f E Y hY a H hφ hpos) hsub hKC
    refine ⟨hsub, h1, ?_⟩
    rw [← SGPT.Okounkov.AlgPOB.volume_real_generalPartialBody f E Y hY a H hφ]
    exact h2

/-- **Source `prop:Okocurrent`, Step 1, in every dimension `n`**: changing the smooth reference
metric (`θ' = θ + dd^c g`, `φ' = φ - g` for a chart-smooth `g`) does not change the partial
Okounkov body, for `φ ∈ PSH(X, θ)_{>0}` and all large cube cones. For `n = m + 1` this is
`SGPT.GAGA.H0L.partialOkounkovBody_eq_of_sameCurrent`; in dimension `0` the body does not depend
on `(L, h₀, h)` at all (`partialOkounkovBody_eq_of_sameCurrent_dim_zero`). -/
theorem partialOkounkovBody_eq_of_sameCurrent_dim [Nonempty (SchemeComplexPoint f)]
    {L' : X.Modules} (a' : LineBundleAtlas L') (H' : SchemeLineBundleMetric f n E L')
    {g : SchemeComplexPoint f → ℝ}
    (hg : letI := E.isSeparated; letI := E.quasiCompact; ChartSmooth (n := n) g)
    (hθθ' : letI := E.isSeparated; letI := E.quasiCompact;
      ∀ (e : ComplexChart n (SchemeComplexPoint f)) (z : ComplexModel n),
        z ∈ e.val.target → (H'.curvature a').val.coeff e z =
          (H.curvature a).val.coeff e z + smoothDDC (fun y => g (e.val.symm y)) z)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hφ' : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H'.curvature a').val (fun x => φ x - (g x : EReal)))
    (hpos : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C →
      partialOkounkovBody f n E Y hY (cubeCone C) a φ =
        partialOkounkovBody f n E Y hY (cubeCone C) a' (fun x => φ x - (g x : EReal)) := by
  cases n with
  | zero =>
    exact ⟨0, le_rfl, fun C _ =>
      partialOkounkovBody_eq_of_sameCurrent_dim_zero f E Y hY a H a' H' hφ hφ' C C⟩
  | succ m =>
    exact SGPT.GAGA.H0L.partialOkounkovBody_eq_of_sameCurrent f E Y hY a H a' H' hg hθθ' hφ hφ'
      (SGPT.Okounkov.AlgPOB.volume_real_generalPartialBody_pos f E Y hY a H hφ hpos)

end SGPT.Okounkov.PobDimZero
