import SGPT.Okounkov.OF8DeltaanaW0
import SGPT.Okounkov.OF8MultiplierIdealCartier
import SGPT.Okounkov.ValGen2Res
import SGPT.Projective.OriginalBookModificationInvariance
import SGPT.Projective.OkounkovOriginalBookPartial

/-!
# `rmk:DeltaanaW0`: the log-resolution formula `eq:DeltaanaW0` in general

Source: chapter *The theory of Okounkov bodies*, Section *Algebraic partial Okounkov bodies*
(`sec:PoB`), remark `rmk:DeltaanaW0`, second sentence:

> *If we take a modification `π : Y → X` such that `π^*φ` has log singularities along an
> effective `ℚ`-divisor `D` on `Y`, then* `Δ_ν(θ, φ) = Δ_ν(π^*L - D) + ν(D)`.  (`eq:DeltaanaW0`)

The book uses the formula for every `φ ∈ PSH(X, θ)_{>0}` admitting such a modification
(`prop:birinvO`, `prop:suba`, `thm:concOko`, `prop:res`, `thm:HCP`), not only for Kähler
currents; this file proves it in that generality: `φ` is any `θ`-psh function with positive
(`𝓘`-)volume (the standing assumption of `sec:PoB`), `ν` any surjective rank-`n` valuation
(values at its centre), `π` a modification (a finite sequence of blow-ups with smooth centres,
the book's convention, as in `prop:birinvO`), `D` an effective `ℚ`-divisor on `Y` with
`π^*φ` log singular along `D` (book Definition 1.6.2). No Kähler-current or
analytic-singularity hypothesis on `X` is needed.

## The right-hand side

Write `D = (1/d) F` (`F` an effective divisor, `d > 0`; `exists_cartier_presentation`). Then
`d(π^*L - D) = π^*L^d - F`, `Δ_ν(π^*L - D) = d⁻¹ Δ_ν(π^*L^d - F)` (`prop:Okourescaling`), and
multiplication by `σ_F^k` identifies `H⁰(Y, k(π^*L^d - F))` with
`W_k = H⁰(Y, π^*L^{dk} ⊗ 𝒪_Y(-kF)) ⊆ H⁰(Y, π^*L^{dk}) = H⁰(X, L^{dk})` (read on `X`, as in
`prop:birinvO`), shifting values by `k ν(F)`. Hence
`Δ_ν(π^*L - D) + ν(D) = d⁻¹ Δ(Γ_ν(W))`,
`Γ_ν(W) = {(ν(s), k) : s ∈ H⁰(X, L^{dk}) \ {0}, π^*s ∈ H⁰(Y, π^*L^{dk} ⊗ 𝒪_Y(-kF))}`
(`pullbackDivisorValues`), with `Δ` the Okounkov body of `thm:Okocont` (`ValGen.setBody`, which
for semigroups in `𝒮'` is `def:Okokk`). `logResolutionBody` is the presentation-free version.

## Proof

`Δ_ν(θ, φ) = Δ_ν(π^*θ, π^*φ)` (`prop:birinvO`, sections `s` of `L^k` with
`π^*s ∈ 𝓘(k π^*φ)`); at the levels `k = dj`, `𝓘(dj π^*φ) = 𝒪_Y(-jF)`
(`SGPT.Okounkov.OF8.multiplierIdeal_mem_iff_nsmul_ideal`, `L²` Riemann extension), so the
Veronese subset of order `d` of `Γ_ν(π^*θ, π^*φ)` is `Γ_ν(W)`; and the Okounkov body of an
almost semigroup commutes with Veronese subsets (`SGPT.Okounkov.ValGen2.setBody_veroneseSet`).

## Main results

* `pullbackDivisorValues`, `veroneseSet_pullbackValues_eq`;
* **`partialBody_eq_logResolution`** (`eq:DeltaanaW0`, for every presentation `D = (1/d) F`);
* `logResolutionBody`, **`partialBody_eq_logResolutionBody`** (presentation-free).

For Kähler currents with analytic singularities, `SGPT.Okounkov.OF8.partialBody_eq_logResolution_of_kahler`
shows in addition that the body is the `def:Okokk` body of the semigroup
`SGPT.Okounkov.OF8.pullbackDivisorSectionSemigroup`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov.OF8

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.PSH SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup
open SGPT.AlmostSemigroup.Class
open scoped Topology Manifold ContDiff Pointwise ENNReal

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) {m : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] (E : ClosedProjectiveEmbedding f)

local instance of8gTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of8gCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance of8gManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable [IsIntegral X] {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z]
  [IsComplexManifold (m + 1) Z]

/-- **The values of the graded linear series `W_k = H⁰(Z, π^*L^{dk} ⊗ 𝒪_Z(-kF))`**, read on `X`:
`Γ_ν(W) = {(ν(s), k) : s ∈ H⁰(X, L^{dk}) \ {0}, π^*s ∈ H⁰(Z, π^*L^{dk} ⊗ 𝒪_Z(-kF))}`.
Since `W_k = σ_F^k H⁰(Z, k(π^*L^d - F))` and `ν(σ_F^k) = k ν(F)`,
`Δ(Γ_ν(W)) = Δ_ν(π^*L^d - F) + ν(F)`. -/
def pullbackDivisorValues (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (c : X) {L : X.Modules} (a : LineBundleAtlas L) (π : Z → SchemeComplexPoint f) (d : ℕ)
    (F : EffectiveDivisor (m + 1) Z) : Set ((Fin (m + 1) → ℤ) × ℤ) :=
  {z | ∃ (k : ℕ) (s : bundlePowerGlobalSections L (d * k)) (hs : s ≠ 0),
    IsPullbackIdealSection f E π (k • F).ideal (d * k) s ∧ z = (sectionVector v c a (d * k) s hs, (k : ℤ))}

variable {f E}

omit [IsIntegral X] in
/-- At the levels `dk`, `π^*s ∈ 𝓘(dk π^*φ)` iff `π^*s ∈ 𝒪_Z(-kF)` (for `k = 0` both hold). -/
theorem isPullbackMultiplierSection_iff_isPullbackIdealSection {π : Z → SchemeComplexPoint f}
    (hπ : letI := E.isSeparated; letI := E.quasiCompact;
      IsAnalyticModification (n := m + 1) π)
    {φ : SchemeComplexPoint f → EReal} {D : EffectiveGeometricQDivisor (m + 1) Z}
    (hlog : NativeHasLogSingularitiesAlong D (fun z => φ (π z)))
    (F : EffectiveDivisor (m + 1) Z) {d : ℕ} (hd : 0 < d)
    (hDF : D = cartierGeometricQDivisor F (1 / (d : ℚ)) (by positivity))
    {L : X.Modules} (k : ℕ) (s : bundlePowerGlobalSections L (d * k)) :
    OriginalModification.AllDimensions.IsPullbackMultiplierSection f (m + 1) E π φ (d * k) s ↔
      IsPullbackIdealSection f E π (k • F).ideal (d * k) s := by
  let := E.isSeparated
  let := E.quasiCompact
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- degree zero: both conditions hold
    refine iff_of_true (Or.inl (by simp)) ?_
    intro U α z hz
    obtain ⟨V, hV, hzV, h, hhol, -, hgen⟩ := F.isInvertible z
    have hhz : HolomorphicAt (m + 1) h z :=
      InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hV hhol hzV
    have hcoef : HolomorphicAt (m + 1)
        (fun w => sectionFrameCoefficient f (m + 1) E α (d * 0) s (π w)) z :=
      HadamardBridge.holomorphicAt_comp_map
        (Eventually.of_forall fun w => hπ.1.mdifferentiable (by simp) w)
        (schemeOpenRegularFunction_holomorphicAt f (m + 1) E U _ (π z) hz)
    refine (nsmul_ideal_mem_iff_of_generator F hhz (hgen z hzV) 0 _).mpr
      ⟨hcoef, _, hcoef, Eventually.of_forall fun w => by simp⟩
  · have hdk : d * k ≠ 0 := (Nat.mul_pos hd hk).ne'
    constructor
    · rintro (h0 | hs)
      · exact absurd h0 hdk
      intro U α z hz
      exact (multiplierIdeal_mem_iff_nsmul_ideal hlog F hd hDF hk z _).mp (hs U α z hz)
    · intro hs
      right
      intro U α z hz
      exact (multiplierIdeal_mem_iff_nsmul_ideal hlog F hd hDF hk z _).mpr (hs U α z hz)

/-- **The Veronese subset of order `d` of `Γ_ν(π^*θ, π^*φ)` is `Γ_ν(W)`.** -/
theorem veroneseSet_pullbackValues_eq
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ)))) (c : X)
    {L : X.Modules} (a : LineBundleAtlas L) {π : Z → SchemeComplexPoint f}
    (hπ : letI := E.isSeparated; letI := E.quasiCompact;
      IsAnalyticModification (n := m + 1) π)
    {φ : SchemeComplexPoint f → EReal} {D : EffectiveGeometricQDivisor (m + 1) Z}
    (hlog : NativeHasLogSingularitiesAlong D (fun z => φ (π z)))
    (F : EffectiveDivisor (m + 1) Z) {d : ℕ} (hd : 0 < d)
    (hDF : D = cartierGeometricQDivisor F (1 / (d : ℚ)) (by positivity)) :
    ValGen2.veroneseSet d (OriginalModification.AllDimensions.pullbackValues f (m + 1) E a v c π φ) =
      pullbackDivisorValues f E v c a π d F := by
  ext ⟨x, j⟩
  rw [ValGen2.mem_veroneseSet]
  constructor
  · rintro ⟨k', s, hs, hP, hz⟩
    simp only [Prod.mk.injEq] at hz
    obtain ⟨hx, hj⟩ := hz
    have hj0 : 0 ≤ j := by
      have hdpos : (0 : ℤ) < d := by exact_mod_cast hd
      have : (0 : ℤ) ≤ (d : ℤ) * j := by rw [hj]; exact Nat.cast_nonneg _
      exact nonneg_of_mul_nonneg_right (by linarith) hdpos
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hj0
    have hk' : k' = d * k := by exact_mod_cast hj.symm
    subst hk'
    exact ⟨k, s, hs, (isPullbackMultiplierSection_iff_isPullbackIdealSection hπ hlog F hd hDF k s).mp hP,
      by rw [hx]⟩
  · rintro ⟨k, s, hs, hP, hz⟩
    simp only [Prod.mk.injEq] at hz
    obtain ⟨hx, hj⟩ := hz
    subst hx hj
    exact ⟨d * k, s, hs,
      (isPullbackMultiplierSection_iff_isPullbackIdealSection hπ hlog F hd hDF k s).mpr hP,
      by simp⟩

/-- **Source `rmk:DeltaanaW0`, `eq:DeltaanaW0`.** Let `φ ∈ PSH(X, θ)` have positive volume
(`sec:PoB`), `ν` a surjective rank-`n` valuation (values at its centre), `π : Y → X` a
modification (a finite sequence of blow-ups with smooth centres) such that `π^*φ` has log
singularities along the effective `ℚ`-divisor `D`, and `D = (1/d) F` with `F` an effective
divisor. Then `Δ_ν(θ, φ) = d⁻¹ Δ(Γ_ν(W))`, `W_k = H⁰(Y, π^*L^{dk} ⊗ 𝒪_Y(-kF))`, i.e.
`Δ_ν(θ, φ) = Δ_ν(π^*L - D) + ν(D)`. The bodies are taken in the book's cones: `C(Δ_ν(L))` on the
left, its Veronese cone `C(Δ_ν(L^d))` on the right. -/
theorem partialBody_eq_logResolution
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hv : Function.Surjective v) {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hpos : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      haveI : Nonempty (SchemeComplexPoint f) := nonempty_schemeComplexPoint f E;
      0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ)
    {π : Z → SchemeComplexPoint f}
    (hseq : letI := E.isSeparated; letI := E.quasiCompact;
      IsBlowupSequence (m + 1) (SchemeComplexPoint f) Z π)
    {D : EffectiveGeometricQDivisor (m + 1) Z}
    (hlog : NativeHasLogSingularitiesAlong D (fun z => φ (π z)))
    (F : EffectiveDivisor (m + 1) Z) {d : ℕ} (hd : 0 < d)
    (hDF : D = cartierGeometricQDivisor F (1 / (d : ℚ)) (by positivity)) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI := E.isProper
    ∃ (hKc : IsCompact (okounkovBody v (valuationCenter f v) a))
      (hKv : Convex ℝ (okounkovBody v (valuationCenter f v) a)),
      ValGen.partialBody f (m + 1) E v (valuationCenter f v) a
          (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ =
        ((d : ℝ)⁻¹) • ValGen.setBody
          (ValGen2.veroneseCone (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) hd)
          (pullbackDivisorValues f E v (valuationCenter f v) a π d F) := by
  let := E.isSeparated
  let := E.quasiCompact
  let := E.isProper
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : Nonempty (SchemeComplexPoint f) := nonempty_schemeComplexPoint f E
  have hπ := HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hseq
  set c := valuationCenter f v with hcdef
  obtain ⟨hKc, hKv, hB⟩ :=
    OriginalBook.modification_partialBody_invariant_allDimensions f (m + 1) E a H v hv hseq hφ hpos
  refine ⟨hKc, hKv, ?_⟩
  set C := SGPT.GAGA.OkoClose.coneOver _ hKc hKv with hCdef
  set P := OriginalModification.AllDimensions.pullbackValues f (m + 1) E a v c π φ with hPdef
  -- the partial body has positive volume, hence `P` is an almost semigroup in `C`
  have hbig := OriginalBook.original_isBig_of_positive_iVolume_allDimensions f (m + 1) E a H hφ hpos
  obtain ⟨hKc', hKv', hsub', hΓ', -, -, hvol⟩ :=
    OriginalBook.centreMultiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions
      f (m + 1) E a H hbig v hv hφ hpos
  have hvol' : volume (ValGen.partialBody f (m + 1) E v c a C φ) ≠ 0 := by
    have hv2 := hvol
    change volume (ValGen.partialBody f (m + 1) E v c a C φ) = _ at hv2
    rw [hv2]
    exact (ENNReal.div_pos_iff.mpr ⟨hpos.ne', ENNReal.natCast_ne_top _⟩).ne'
  have hne : (ValGen.setBody C P).Nonempty := by
    rw [← hB] at hvol'
    exact nonempty_of_measure_ne_zero hvol'
  have hcond : ∃ hsub : P ⊆ (latticePoints C.cone : Set _),
      (⟨P, hsub⟩ : ConeSubset C) ∈ almostSemigroupLocus C := by
    by_contra hno
    unfold ValGen.setBody at hne
    rw [dif_neg hno] at hne
    exact Set.not_nonempty_empty hne
  obtain ⟨hsub, hP⟩ := hcond
  have hver := ValGen2.setBody_veroneseSet hd hsub hP
  rw [veroneseSet_pullbackValues_eq v c a hπ hlog F hd hDF] at hver
  rw [hver, inv_smul_smul₀ (by exact_mod_cast hd.ne' : (d : ℝ) ≠ 0)]
  exact hB.symm

variable (f E) in
open Classical in
/-- **The right-hand side of `eq:DeltaanaW0`, `Δ_ν(π^*L - D) + ν(D)`**, in an ambient admissible
cone `C` (the book takes `C = C(Δ_ν(L))`; as for `ValGen.partialBody`, the cone is a parameter):
for a chosen presentation `D = (1/d) F` (`F` an effective divisor, `d > 0`),
`d⁻¹ Δ(Γ_ν(W))` with `W_k = H⁰(Z, π^*L^{dk} ⊗ 𝒪_Z(-kF))` read on `X`
(`pullbackDivisorValues`) and `Δ` taken in the Veronese cone `C^{(d)}`. Empty if `D` has no
such presentation (never on a compact `Z`, `exists_cartier_presentation`). By
`partialBody_eq_logResolution` the value does not depend on the presentation whenever the
hypotheses of the remark hold. -/
def logResolutionBody (C : AdmissibleCone (m + 1))
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (c : X) {L : X.Modules} (a : LineBundleAtlas L) (π : Z → SchemeComplexPoint f)
    (D : EffectiveGeometricQDivisor (m + 1) Z) : Set (EuclideanSpace ℝ (Fin (m + 1))) :=
  if h : ∃ (d : ℕ) (F : EffectiveDivisor (m + 1) Z),
      0 < d ∧ D = cartierGeometricQDivisor F (1 / (d : ℚ)) (by positivity) then
    ((h.choose : ℝ)⁻¹) • ValGen.setBody (ValGen2.veroneseCone C h.choose_spec.choose_spec.1)
      (pullbackDivisorValues f E v c a π h.choose h.choose_spec.choose)
  else ∅

/-- **Source `rmk:DeltaanaW0`, `eq:DeltaanaW0`, presentation-free form**: for `φ ∈ PSH(X, θ)`
with positive volume, a modification `π : Y → X` with `π^*φ` log singular along the effective
`ℚ`-divisor `D`, and every surjective rank-`n` valuation `ν` (values at its centre),
`Δ_ν(θ, φ) = Δ_ν(π^*L - D) + ν(D)` (`logResolutionBody`, in the cone `C(Δ_ν(L))`). -/
theorem partialBody_eq_logResolutionBody
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hv : Function.Surjective v) {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hpos : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      haveI : Nonempty (SchemeComplexPoint f) := nonempty_schemeComplexPoint f E;
      0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ)
    {π : Z → SchemeComplexPoint f}
    (hseq : letI := E.isSeparated; letI := E.quasiCompact;
      IsBlowupSequence (m + 1) (SchemeComplexPoint f) Z π)
    {D : EffectiveGeometricQDivisor (m + 1) Z}
    (hlog : NativeHasLogSingularitiesAlong D (fun z => φ (π z))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI := E.isProper
    ∃ (hKc : IsCompact (okounkovBody v (valuationCenter f v) a))
      (hKv : Convex ℝ (okounkovBody v (valuationCenter f v) a)),
      ValGen.partialBody f (m + 1) E v (valuationCenter f v) a
          (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ =
        logResolutionBody f E (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) v (valuationCenter f v) a π D := by
  let := E.isSeparated
  let := E.quasiCompact
  let := E.isProper
  have hπ := HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hseq
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : CompactSpace Z := by
    refine ⟨?_⟩
    have h := hπ.2.1.isCompact_preimage (isCompact_univ (X := SchemeComplexPoint f))
    rwa [Set.preimage_univ] at h
  have hex : ∃ (d : ℕ) (F : EffectiveDivisor (m + 1) Z),
      0 < d ∧ D = cartierGeometricQDivisor F (1 / (d : ℚ)) (by positivity) :=
    exists_cartier_presentation D
  obtain ⟨hKc, hKv, hbody⟩ := partialBody_eq_logResolution a H v hv hφ hpos hseq hlog
    hex.choose_spec.choose hex.choose_spec.choose_spec.1 hex.choose_spec.choose_spec.2
  refine ⟨hKc, hKv, ?_⟩
  rw [hbody, logResolutionBody, dif_pos hex]

end SGPT.Okounkov.OF8
