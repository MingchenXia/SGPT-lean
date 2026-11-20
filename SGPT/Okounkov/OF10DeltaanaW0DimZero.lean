import SGPT.Okounkov.OF10DeltaanaW0AnyDimension
import SGPT.Okounkov.PobDimZeroBook
import SGPT.PSH.NativeCartierLogReconstruction
import SGPT.Projective.OkounkovOriginalBookVolume

/-!
# `rmk:DeltaanaW0` in dimension zero

Source: chapter *The theory of Okounkov bodies*, Section *Algebraic partial Okounkov bodies*
(`sec:PoB`), remark `rmk:DeltaanaW0`, second sentence, `eq:DeltaanaW0`:
`Δ_ν(θ, φ) = Δ_ν(π^*L - D) + ν(D)`.

`sec:PoB` works on a smooth projective variety `X` of any dimension `n`; lane OF8 proved the
formula for `n = m + 1`. This file treats `n = 0`, with the same objects and hypotheses:
`X` an integral smooth projective complex scheme of relative dimension `0` (closed projective
embedding `E`), `L` with atlas `a` and smooth metric `H`, `θ = c₁(L, H)`, `φ ∈ PSH(X, θ)`, `ν` a
surjective rank-`0` valuation of `ℂ(X)` (values at its centre), `π : Y → X(ℂ)` a finite sequence
of blow-ups with smooth centres, `D` an effective `ℚ`-divisor on `Y` with `π^*φ` log singular
along `D`, and a presentation `D = (1/d) F`.

In dimension `0` everything is degenerate but nothing is vacuous:

* the volume hypothesis of `sec:PoB` always holds, `vol θ_φ = 1`
  (`iVolume_pos_dim_zero`), so it is dropped from the statements below;
* `Y` has no prime divisors, so `D = 0`, `F = 0` and every presentation `D = (1/d) F` holds
  (`isCartierPresentationAny_of_dim_zero`); `W_k = H⁰(Y, π^*L^{dk})` and
  `Γ_ν(W) = {(0, k) : k ∈ ℕ}` (`pullbackDivisorValuesAny_dim_zero`);
* both sides of `eq:DeltaanaW0` are `ℝ⁰ = {0}` (`partialBody_eq_univ_and_logResolutionBody_eq_univ_dim_zero`);
* the hypotheses are satisfiable: for every `φ ∈ PSH(X, θ)`, `π = id` is a modification
  (the empty sequence of blow-ups), `π^*φ = φ` has log singularities along every (the zero)
  divisor `D`, `D = (1/1) 0`, and a surjective rank-`0` valuation of `ℂ(X)` exists (the trivial
  valuation) (`logResolution_hypotheses_dim_zero`, `exists_surjective_valuation_dim_zero`).

## Main results

* **`partialBody_eq_logResolution_dim_zero`**, **`partialBody_eq_logResolutionBody_dim_zero`**:
  `eq:DeltaanaW0` for `n = 0` (the `n = 0` case of
  `SGPT.Okounkov.OF10.partialBody_eq_logResolutionAny`, `partialBody_eq_logResolutionBodyAny`,
  without the volume hypothesis);
* `partialBody_eq_univ_and_logResolutionBody_eq_univ_dim_zero`, `pullbackDivisorValuesAny_dim_zero`;
* `iVolume_pos_dim_zero`, `logResolution_hypotheses_dim_zero`,
  `exists_surjective_valuation_dim_zero`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov.OF10

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.PSH SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup
open SGPT.AlmostSemigroup.Class
open scoped Topology Manifold ContDiff Pointwise ENNReal

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
  [SmoothOfRelativeDimension 0 f] (E : ClosedProjectiveEmbedding f)

local instance of10zTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of10zCharts : ChartedSpace (ComplexModel 0) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f 0
local instance of10zManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold 0 (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f 0

variable {f E}

/-! ### The hypotheses are satisfiable in dimension zero -/

/-- **`vol θ_φ > 0` in dimension `0`**: `vol θ_φ = ∫_X θ_φ⁰ = 1` for every `φ ∈ PSH(X, θ)`, so the
standing volume hypothesis of `sec:PoB` always holds. -/
theorem iVolume_pos_dim_zero {L : X.Modules} (a : LineBundleAtlas L)
    (H : SchemeLineBundleMetric f 0 E L) {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : Nonempty (SchemeComplexPoint f) := OF8.nonempty_schemeComplexPoint f E
    0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : Nonempty (SchemeComplexPoint f) := OF8.nonempty_schemeComplexPoint f E
  have : ConnectedSpace (SchemeComplexPoint f) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E 0
  rw [PobDimZero.iVolume_eq_one (H.curvature a) _ hφ]
  exact zero_lt_one

omit [IsIntegral X] in
/-- **The hypotheses of `eq:DeltaanaW0` are satisfiable in dimension `0`**: for every
`φ ∈ PSH(X, θ)`, the identity `π = id` is a modification (the empty sequence of blow-ups with
smooth centres), `π^*φ = φ` has log singularities (book Definition 1.6.2) along every effective
`ℚ`-divisor `D` of `X(ℂ)` (there is only `D = 0`), and `D = (1/1) · 0`. -/
theorem logResolution_hypotheses_dim_zero {L : X.Modules} (a : LineBundleAtlas L)
    (H : SchemeLineBundleMetric f 0 E L) {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    IsBlowupSequence 0 (SchemeComplexPoint f) (SchemeComplexPoint f) id ∧
      ∀ D : EffectiveGeometricQDivisor 0 (SchemeComplexPoint f),
        NativeHasLogSingularitiesAlongAnyDimension D (fun z => φ (id z)) ∧
          IsCartierPresentationAny D 0 1 := by
  let := E.isSeparated
  let := E.quasiCompact
  refine ⟨IsBlowupSequence.refl, fun D => ⟨?_, isCartierPresentationAny_of_dim_zero D 0 1⟩⟩
  exact native_log_of_qpsh_dim_zero D (PobDimZero.isQPSH_of_isThetaPshPotential_dim_zero hφ)

omit [SmoothOfRelativeDimension 0 f] in
/-- **A surjective rank-`0` valuation of `ℂ(X)` exists**: the trivial valuation
(`ν(0) = ∞`, `ν(g) = 0` for `g ≠ 0`) has values in `ℤ⁰ ∪ {∞}` and is onto. -/
theorem exists_surjective_valuation_dim_zero :
    ∃ v : AddValuation X.functionField (WithTop (Lex (Fin 0 → ℤ))), Function.Surjective v := by
  classical
  refine ⟨AddValuation.ofValuation
    (1 : Valuation X.functionField (Multiplicative (WithTop (Lex (Fin 0 → ℤ)))ᵒᵈ)), ?_⟩
  intro y
  induction y using WithTop.recTopCoe with
  | top => exact ⟨0, AddValuation.map_zero _⟩
  | coe g =>
    refine ⟨1, ?_⟩
    rw [AddValuation.map_one, Subsingleton.elim g 0, WithTop.coe_zero]

/-! ### `eq:DeltaanaW0` in dimension zero -/

variable {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel 0) Z]
  [IsComplexManifold 0 Z]

/-- **Source `rmk:DeltaanaW0`, `eq:DeltaanaW0`, dimension `0`.** `X` an integral smooth projective
complex scheme of dimension `0`, `L` with atlas and smooth metric `H`, `θ = c₁(L, H)`,
`φ ∈ PSH(X, θ)` (the volume hypothesis of `sec:PoB` holds automatically, `iVolume_pos_dim_zero`),
`ν` a surjective rank-`0` valuation (values at its centre), `π : Y → X` a modification (a finite
sequence of blow-ups with smooth centres) with `π^*φ` log singular along the effective
`ℚ`-divisor `D`, and `D = (1/d) F` with `F` an effective divisor. Then
`Δ_ν(θ, φ) = d⁻¹ Δ(Γ_ν(W)) = Δ_ν(π^*L - D) + ν(D)`, `W_k = H⁰(Y, π^*L^{dk} ⊗ 𝒪_Y(-kF))`, in the
book's cones `C(Δ_ν(L))` and `C(Δ_ν(L^d))`. -/
theorem partialBody_eq_logResolution_dim_zero
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f 0 E L)
    (v : AddValuation X.functionField (WithTop (Lex (Fin 0 → ℤ))))
    (hv : Function.Surjective v) {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    {π : Z → SchemeComplexPoint f}
    (hseq : letI := E.isSeparated; letI := E.quasiCompact;
      IsBlowupSequence 0 (SchemeComplexPoint f) Z π)
    {D : EffectiveGeometricQDivisor 0 Z}
    (hlog : NativeHasLogSingularitiesAlongAnyDimension D (fun z => φ (π z)))
    (F : EffectiveDivisor 0 Z) {d : ℕ} (hd : 0 < d) (hDF : IsCartierPresentationAny D F d) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI := E.isProper
    ∃ (hKc : IsCompact (okounkovBody v (valuationCenter f v) a))
      (hKv : Convex ℝ (okounkovBody v (valuationCenter f v) a)),
      ValGen.partialBody f 0 E v (valuationCenter f v) a
          (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ =
        ((d : ℝ)⁻¹) • ValGen.setBody
          (ValGen2.veroneseCone (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) hd)
          (pullbackDivisorValuesAny f 0 E v (valuationCenter f v) a π d F) :=
  partialBody_eq_logResolutionAny a H v hv hφ (iVolume_pos_dim_zero a H hφ) hseq hlog F hd hDF

/-- **Source `rmk:DeltaanaW0`, `eq:DeltaanaW0`, dimension `0`, presentation-free form**:
`Δ_ν(θ, φ) = Δ_ν(π^*L - D) + ν(D)` (`logResolutionBodyAny`, in the cone `C(Δ_ν(L))`). -/
theorem partialBody_eq_logResolutionBody_dim_zero
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f 0 E L)
    (v : AddValuation X.functionField (WithTop (Lex (Fin 0 → ℤ))))
    (hv : Function.Surjective v) {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    {π : Z → SchemeComplexPoint f}
    (hseq : letI := E.isSeparated; letI := E.quasiCompact;
      IsBlowupSequence 0 (SchemeComplexPoint f) Z π)
    {D : EffectiveGeometricQDivisor 0 Z}
    (hlog : NativeHasLogSingularitiesAlongAnyDimension D (fun z => φ (π z))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI := E.isProper
    ∃ (hKc : IsCompact (okounkovBody v (valuationCenter f v) a))
      (hKv : Convex ℝ (okounkovBody v (valuationCenter f v) a)),
      ValGen.partialBody f 0 E v (valuationCenter f v) a
          (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ =
        logResolutionBodyAny f 0 E (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) v
          (valuationCenter f v) a π D :=
  partialBody_eq_logResolutionBodyAny a H v hv hφ (iVolume_pos_dim_zero a H hφ) hseq hlog

/-- **Both sides of `eq:DeltaanaW0` are `ℝ⁰ = {0}` in dimension `0`**: under the hypotheses of
the remark, `Δ_ν(θ, φ) = ℝ⁰` and `Δ_ν(π^*L - D) + ν(D) = ℝ⁰` (in the cone `C(Δ_ν(L))`). -/
theorem partialBody_eq_univ_and_logResolutionBody_eq_univ_dim_zero
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f 0 E L)
    (v : AddValuation X.functionField (WithTop (Lex (Fin 0 → ℤ))))
    (hv : Function.Surjective v) {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    {π : Z → SchemeComplexPoint f}
    (hseq : letI := E.isSeparated; letI := E.quasiCompact;
      IsBlowupSequence 0 (SchemeComplexPoint f) Z π)
    {D : EffectiveGeometricQDivisor 0 Z}
    (hlog : NativeHasLogSingularitiesAlongAnyDimension D (fun z => φ (π z))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI := E.isProper
    ∃ (hKc : IsCompact (okounkovBody v (valuationCenter f v) a))
      (hKv : Convex ℝ (okounkovBody v (valuationCenter f v) a)),
      ValGen.partialBody f 0 E v (valuationCenter f v) a
          (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ = univ ∧
        logResolutionBodyAny f 0 E (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) v
          (valuationCenter f v) a π D = univ := by
  let := E.isSeparated
  let := E.quasiCompact
  let := E.isProper
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : Nonempty (SchemeComplexPoint f) := OF8.nonempty_schemeComplexPoint f E
  have hpos := iVolume_pos_dim_zero a H hφ
  obtain ⟨hKc, hKv, hbody⟩ := partialBody_eq_logResolutionBody_dim_zero a H v hv hφ hseq hlog
  have hbig := OriginalBook.original_isBig_of_positive_iVolume_allDimensions f 0 E a H hφ hpos
  obtain ⟨hKc', hKv', hsub', hΓ', -, -, hvol⟩ :=
    OriginalBook.centreMultiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions
      f 0 E a H hbig v hv hφ hpos
  have hvol' : volume (ValGen.partialBody f 0 E v (valuationCenter f v) a
      (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ) ≠ 0 := by
    have hv2 := hvol
    change volume (ValGen.partialBody f 0 E v (valuationCenter f v) a
      (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ) = _ at hv2
    rw [hv2]
    exact (ENNReal.div_pos_iff.mpr ⟨hpos.ne', ENNReal.natCast_ne_top _⟩).ne'
  have huniv := PobDimZero.eq_univ_of_nonempty_euclidean (nonempty_of_measure_ne_zero hvol')
  exact ⟨hKc, hKv, huniv, hbody ▸ huniv⟩

omit [IsIntegral X] in
private theorem holomorphicAt_of_dim_zero'' {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel 0) Y] [IsComplexManifold 0 Y] (g : Y → ℂ) (z : Y) :
    HolomorphicAt 0 g z := by
  refine Eventually.of_forall fun y => ?_
  have hc : MDifferentiableAt 𝓘(ℂ, ComplexModel 0) 𝓘(ℂ, ℂ) (fun _ : Y => g y) y :=
    mdifferentiableAt_const
  apply hc.congr_of_eventuallyEq
  filter_upwards [(RooftopDimZero.isOpen_singleton_of_dim_zero rfl y).mem_nhds rfl] with w hw
  exact congrArg g (mem_singleton_iff.mp hw)

/-- **`Γ_ν(W) = {(0, k) : k ∈ ℕ}` in dimension `0`**: for every map `π : Y → X(ℂ)` from a
`0`-dimensional manifold, every effective divisor `F` (necessarily `0`) and every `d > 0`,
`W_k = H⁰(Y, π^*L^{dk} ⊗ 𝒪_Y(-kF)) = H⁰(X, L^{dk}) ≠ 0`, and every value lies in `ℤ⁰ = {0}`. So
`π^*L - D = π^*L`, `ν(D) = 0`, and the right-hand side of `eq:DeltaanaW0` is `Δ_ν(L) = ℝ⁰`. -/
theorem pullbackDivisorValuesAny_dim_zero {L : X.Modules} (a : LineBundleAtlas L)
    (v : AddValuation X.functionField (WithTop (Lex (Fin 0 → ℤ)))) (c : X)
    (π : Z → SchemeComplexPoint f) {d : ℕ} (F : EffectiveDivisor 0 Z) :
    pullbackDivisorValuesAny f 0 E v c a π d F =
      (PobDimZero.nonnegHeight : Set ((Fin 0 → ℤ) × ℤ)) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : Nonempty (SchemeComplexPoint f) := OF8.nonempty_schemeComplexPoint f E
  obtain ⟨Y, hY⟩ := OriginalBook.exists_original_smoothFlag_allDimensions f 0 E
  ext ⟨x, j⟩
  constructor
  · rintro ⟨k, s, hs, -, hz⟩
    simp only [Prod.mk.injEq] at hz
    rw [SetLike.mem_coe, PobDimZero.mem_nonnegHeight, hz.2]
    exact Nat.cast_nonneg _
  · intro hj
    rw [SetLike.mem_coe, PobDimZero.mem_nonnegHeight] at hj
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    obtain ⟨s, hs⟩ := PobDimZero.exists_section_ne_zero f E Y hY a (d * k)
    refine ⟨k, s, hs, ?_, ?_⟩
    · intro U α z _
      rw [effectiveDivisor_ideal_eq_unit_of_dimension_zero (k • F)]
      exact holomorphicAt_of_dim_zero'' _ z
    · exact Prod.ext (Subsingleton.elim _ _) rfl

end SGPT.Okounkov.OF10
