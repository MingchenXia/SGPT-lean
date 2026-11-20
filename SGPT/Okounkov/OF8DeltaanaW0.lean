import SGPT.Okounkov.OF8InftyIdealModification
import SGPT.Okounkov.OkoNSInfty
import SGPT.Projective.OkoNov16OriginalInftySemigroupBody
import SGPT.Projective.OkoNov16AttributedCompactCartierReuse
import SGPT.Projective.OkounkovOriginalInftyBodyLimit
import SGPT.Foundations.Analysis.Pending.HironakaChowLemma

/-!
# `rmk:DeltaanaW0`, `eq:DeltaanaW0`: the Kähler-current case via `Γ^∞`

Source: chapter *The theory of Okounkov bodies*, Section *Algebraic partial Okounkov bodies*
(`sec:PoB`), remark `rmk:DeltaanaW0`:

> *It follows from the proof that if `φ` has analytic singularities and `θ_φ` is a Kähler
> current, then `eq:Gamma0Gammaanalytic` holds. If we take a modification `π : Y → X` such that
> `π^*φ` has log singularities along an effective `ℚ`-divisor `D` on `Y`, then*
> `Δ_ν(θ, φ) = Δ_ν(π^*L - D) + ν(D)`.  (`eq:DeltaanaW0`)

This file follows the book's own argument (proof of `prop:GammaepsSp` plus the first sentence)
in the situation of the first sentence (`φ` with analytic singularities, `θ_φ` a Kähler
current); there the right-hand side is the `def:Okokk` body of an honest semigroup. The general
statement (every `φ` with positive volume, no Kähler or analytic hypothesis on `X`) is
`SGPT.Okounkov.OF8.partialBody_eq_logResolution` in `SGPT.Okounkov.OF8DeltaanaW0General`.

## Setting (as in `sec:PoB`)

`X` an integral smooth projective complex scheme of dimension `n = m + 1` (closed projective
embedding `E`), `L` a big line bundle with atlas `a` and smooth metric `H`, `θ = c₁(L, H)`,
`ν = v : ℂ(X)^× → ℤⁿ` an arbitrary surjective valuation, section values read at the centre
`c = valuationCenter f v` of `v`. A *modification* `π : Y → X(ℂ)` is, as everywhere in the book
(`conventions`, and `prop:birinvO` in the formalization), a finite sequence of blow-ups with
smooth centres (`IsBlowupSequence`); here every proper bimeromorphic holomorphic map
(`IsAnalyticModification`) is allowed as well. `D` is an effective geometric `ℚ`-divisor on `Y`
(`EffectiveGeometricQDivisor`) and *log singularities along `D`* is the book's Definition 1.6.2
(`NativeHasLogSingularitiesAlong D (φ ∘ π)`).

## The right-hand side

Write `D = (1/d) F` with `F` an effective (Cartier) divisor on `Y` and `d > 0` (such a
presentation exists, `exists_cartier_presentation`). The `ℚ`-line bundle `π^*L - D` has
`d(π^*L - D) = π^*L^d - F`, and by `prop:Okourescaling`
`Δ_ν(π^*L - D) = d⁻¹ Δ_ν(π^*L^d - F)`. The sections of `k(π^*L^d - F)` are identified, by
multiplication with `σ_F^k` (`σ_F` the canonical section of `𝒪_Y(F)`), with the sections of
`π^*L^{dk}` vanishing along `kF`, i.e. with
`W_k = H⁰(Y, π^*L^{dk} ⊗ 𝒪_Y(-kF)) ⊆ H⁰(Y, π^*L^{dk}) = H⁰(X, L^{dk})` (sections read on `X`
as in `prop:birinvO`), and the valuation of a section is shifted by `ν(σ_F^k) = k ν(F) = kd ν(D)`
(`ν(F)` is the value of a local equation of `F` at the centre). Hence
`Δ_ν(π^*L - D) + ν(D) = d⁻¹ Δ(Γ_ν(W))` with
`Γ_ν(W) = {(ν(s), k) : s ∈ H⁰(X, (L^d)^k) \ {0}, π^*s ∈ H⁰(Y, π^*L^{dk} ⊗ 𝒪_Y(-kF))}`
(`pullbackDivisorSectionSemigroup`, a semigroup; `Δ` the Okounkov body `def:Okokk` of a
semigroup).

## Main results

* `IsPullbackIdealSection`, `pullbackDivisorSectionSemigroup`;
* `isInftySection_iff_isPullbackIdealSection`: for `D = (1/d) F` and `π^*φ` log singular along
  `D`, a section `s` of `M^k` lies in `H⁰(X, M^k ⊗ 𝓘_∞(k d φ))` iff
  `π^*s ∈ H⁰(Y, π^*M^k ⊗ 𝒪_Y(-kF))` (the identification in the proof of `prop:GammaepsSp`);
* `partialBody_eq_logResolution_of_kahler_of_isAnalyticModification`,
  `partialBody_eq_logResolution_of_kahler`: `eq:DeltaanaW0` for Kähler currents with analytic
  singularities, `Δ_ν(θ, φ) = d⁻¹ Δ(Γ_ν(W))` for every presentation `D = (1/d) F`;
* `exists_cartier_presentation`: every effective `ℚ`-divisor on a compact manifold is `(1/d) F`.

The proof is the book's: `Δ_ν(θ, φ) = Δ(Γ^∞(θ, φ))` (the first sentence of the remark,
`SGPT.Okounkov.OriginalInftyBodyLimit.infty_body_eq_partialBody_and_degree_limit`), the Veronese
rescaling `Δ(Γ^∞(dθ, dφ)) = d Δ(Γ^∞(θ, φ))`, and `Γ^∞(dθ, dφ) = Γ_ν(W)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov.OF8

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.PSH SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup
open scoped Topology Manifold ContDiff Pointwise

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) {m : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] (E : ClosedProjectiveEmbedding f)

local instance of8Topology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of8Charts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance of8Manifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

/-! ### Sections whose pullback lies in an ideal sheaf of the modification -/

section Pullback

variable {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z]
  [IsComplexManifold (m + 1) Z]

/-- `π^*s ∈ H⁰(Z, π^*M^k ⊗ 𝔞)`: in every local frame `α` of `M`, the pullback along `π` of the
coefficient of `s ∈ H⁰(X, M^k)` lies in the ideal sheaf `𝔞` of `Z` at every point of the
preimage of the frame domain. For `𝔞 = 𝒪_Z(-kF)` this is `π^*s ∈ H⁰(Z, π^*M^k ⊗ 𝒪_Z(-kF))`. -/
def IsPullbackIdealSection (π : Z → SchemeComplexPoint f) (𝔞 : GermIdeal (m + 1) Z)
    {M : X.Modules} (k : ℕ) (s : bundlePowerGlobalSections M k) : Prop :=
  ∀ (U : X.Opens) (α : LocalBundleFrame M U) (z : Z),
    schemeComplexPointImage f (π z) ∈ U →
      𝔞.mem z (fun w => sectionFrameCoefficient f (m + 1) E α k s (π w))

variable {f E}

/-- Products: `π^*s ∈ 𝒪(-kF)` and `π^*t ∈ 𝒪(-lF)` give `π^*(st) ∈ 𝒪(-(k+l)F)`. -/
theorem isPullbackIdealSection_atlasPowerGlobalMul [IsIntegral X] {π : Z → SchemeComplexPoint f}
    (hπc : Continuous π) (F : EffectiveDivisor (m + 1) Z) {M : X.Modules}
    (a : LineBundleAtlas M) {k l : ℕ} {s : bundlePowerGlobalSections M k}
    {t : bundlePowerGlobalSections M l}
    (hs : IsPullbackIdealSection f E π (k • F).ideal k s)
    (ht : IsPullbackIdealSection f E π (l • F).ideal l t) :
    IsPullbackIdealSection f E π ((k + l) • F).ideal (k + l) (atlasPowerGlobalMul a k l s t) := by
  intro U α z hz
  obtain ⟨V, hV, hzV, h, hhol, -, hgen⟩ := F.isInvertible z
  have hhz : HolomorphicAt (m + 1) h z :=
    InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hV hhol hzV
  have hgz := hgen z hzV
  obtain ⟨hfs, a₁, ha₁, hs'⟩ :=
    (nsmul_ideal_mem_iff_of_generator F hhz hgz k _).mp (hs U α z hz)
  obtain ⟨hft, a₂, ha₂, ht'⟩ :=
    (nsmul_ideal_mem_iff_of_generator F hhz hgz l _).mp (ht U α z hz)
  have hU : π ⁻¹' (schemeComplexPointImage f ⁻¹' (U : Set X)) ∈ 𝓝 z :=
    ((U.isOpen.preimage (schemeComplexPointImage_continuous f)).preimage hπc).mem_nhds hz
  have hprod : (fun w => sectionFrameCoefficient f (m + 1) E α (k + l)
      (atlasPowerGlobalMul a k l s t) (π w)) =ᶠ[𝓝 z]
      fun w => sectionFrameCoefficient f (m + 1) E α k s (π w) *
        sectionFrameCoefficient f (m + 1) E α l t (π w) := by
    filter_upwards [hU] with w hw
    exact OkoNS.sectionFrameCoefficient_atlasPowerGlobalMul f E a α k l s t hw
  refine (nsmul_ideal_mem_iff_of_generator F hhz hgz (k + l) _).mpr
    ⟨(hfs.mul hft).congr hprod.symm, fun w => a₁ w * a₂ w, ha₁.mul ha₂, ?_⟩
  filter_upwards [hprod, hs', ht'] with w h1 h2 h3
  rw [h1, h2, h3, pow_add]
  ring

variable (f E)

/-- **The value semigroup of the graded linear series `W_k = H⁰(Z, π^*M^k ⊗ 𝒪_Z(-kF))`**,
read on `X`: `Γ_ν(W) = {(ν(s), k) : s ∈ H⁰(X, M^k) \ {0}, π^*s ∈ H⁰(Z, π^*M^k ⊗ 𝒪_Z(-kF))}`.
Multiplication by `σ_F^k` identifies `H⁰(Z, k(π^*M - F))` with `W_k`, shifting values by
`k ν(F)`; hence `Δ(Γ_ν(W)) = Δ_ν(π^*M - F) + ν(F)`. -/
def pullbackDivisorSectionSemigroup [IsIntegral X]
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ)))) (c : X)
    {M : X.Modules} (a : LineBundleAtlas M) (π : Z → SchemeComplexPoint f) (hπc : Continuous π)
    (F : EffectiveDivisor (m + 1) Z) : AddSubsemigroup ((Fin (m + 1) → ℤ) × ℤ) where
  carrier := AlgebraicValuation.sectionValueSet v c a fun k s => IsPullbackIdealSection f E π (k • F).ideal k s
  add_mem' := by
    rintro z w ⟨k, s, hs, hks, rfl⟩ ⟨l, t, ht, hlt, rfl⟩
    have hu := atlasPowerGlobalMul_ne_zero (v := v) c a k l hs ht
    refine ⟨k + l, atlasPowerGlobalMul a k l s t, hu,
      isPullbackIdealSection_atlasPowerGlobalMul hπc F a hks hlt, ?_⟩
    have hv := sectionValue_mul (v := v) c a k l s t
    rw [sectionValue_eq_vector c a (k + l) _ hu, sectionValue_eq_vector c a k s hs,
      sectionValue_eq_vector c a l t ht, ← WithTop.coe_add, ← toLex_add] at hv
    have hv' := toLex.injective (WithTop.coe_injective hv)
    rw [hv']
    ext <;> simp

theorem mem_pullbackDivisorSectionSemigroup [IsIntegral X]
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ)))) (c : X)
    {M : X.Modules} (a : LineBundleAtlas M) (π : Z → SchemeComplexPoint f) (hπc : Continuous π)
    (F : EffectiveDivisor (m + 1) Z) (z : (Fin (m + 1) → ℤ) × ℤ) :
    z ∈ pullbackDivisorSectionSemigroup f E v c a π hπc F ↔
      z ∈ AlgebraicValuation.sectionValueSet v c a fun k s => IsPullbackIdealSection f E π (k • F).ideal k s :=
  Iff.rfl

variable {f E}

/-- **`𝓘_∞` sections are the sections vanishing along `kF` on the modification** (the
identification in the proof of `prop:GammaepsSp`): if `π` is a proper modification, `π^*φ` has
log singularities along `D` and `D = (1/d) F`, then for every line bundle `M`, `k ∈ ℕ` and
`s ∈ H⁰(X, M^k)`: `s ∈ H⁰(X, M^k ⊗ 𝓘_∞(k d φ))` iff `π^*s ∈ H⁰(Z, π^*M^k ⊗ 𝒪_Z(-kF))`. -/
theorem isInftySection_iff_isPullbackIdealSection {π : Z → SchemeComplexPoint f}
    (hπ : letI := E.isSeparated; letI := E.quasiCompact;
      IsAnalyticModification (n := m + 1) π)
    {φ : SchemeComplexPoint f → EReal} {D : EffectiveGeometricQDivisor (m + 1) Z}
    (hlog : NativeHasLogSingularitiesAlong D (fun z => φ (π z)))
    (F : EffectiveDivisor (m + 1) Z) {d : ℕ} (hd : 0 < d)
    (hDF : D = cartierGeometricQDivisor F (1 / (d : ℚ)) (by positivity))
    {M : X.Modules} (k : ℕ) (s : bundlePowerGlobalSections M k) :
    IsInftySection f (m + 1) E (fun y => (d : EReal) * φ y) k s ↔
      IsPullbackIdealSection f E π (k • F).ideal k s := by
  let := E.isSeparated
  let := E.quasiCompact
  have hmd : ∀ z, MDifferentiableAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) π z :=
    fun z => hπ.1.mdifferentiable (by simp) z
  constructor
  · intro hs U α z hz
    have h1 := hs U α (π z) hz
    exact (nsmul_ideal_mem_iff_inftyIdeal hlog F hd hDF k z _).mpr (inftyIdeal_mem_comp hmd h1)
  · intro hs U α p hp
    refine inftyIdeal_mem_of_forall_comp_mem (n := m + 1) (m := m + 1) hπ.2.1
      (AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hπ)
      (schemeOpenRegularFunction_holomorphicAt f (m + 1) E U _ p hp) ?_
    intro z hz
    exact (nsmul_ideal_mem_iff_inftyIdeal hlog F hd hDF k z _).mp
      (hs U α z (by rw [hz]; exact hp))

/-- Value sets of equivalent section conditions coincide. -/
theorem sectionValueSet_congr [IsIntegral X] {n : ℕ}
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (c : X)
    {M : X.Modules} (a : LineBundleAtlas M) {P Q : ∀ k : ℕ, bundlePowerGlobalSections M k → Prop}
    (h : ∀ k s, P k s ↔ Q k s) : AlgebraicValuation.sectionValueSet v c a P = AlgebraicValuation.sectionValueSet v c a Q := by
  ext z
  constructor
  · rintro ⟨k, s, hs, hP, rfl⟩
    exact ⟨k, s, hs, (h k s).mp hP, rfl⟩
  · rintro ⟨k, s, hs, hQ, rfl⟩
    exact ⟨k, s, hs, (h k s).mpr hQ, rfl⟩

end Pullback

/-! ### The log-resolution formula -/

section Formula

omit [SmoothOfRelativeDimension (m + 1) f] in
theorem nonempty_schemeComplexPoint [IsIntegral X] (E : ClosedProjectiveEmbedding f) :
    Nonempty (SchemeComplexPoint f) := by
  have := E.locallyOfFiniteType
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : Nonempty (U : X.Opens) := ⟨⟨x, hxU⟩⟩
  obtain ⟨P, hP⟩ := Ideal.exists_maximal Γ(X, U)
  obtain ⟨p, -⟩ := SGPT.NAPotential.Berkovich.exists_schemeComplexPoint_fromSpec f hU P hP
  exact ⟨p⟩

variable [IsIntegral X] {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z]
  [IsComplexManifold (m + 1) Z]

/-- **Source `rmk:DeltaanaW0`, `eq:DeltaanaW0`, for a proper modification.** Let `φ` have
analytic singularities with `θ_φ` a Kähler current, `π : Z → X` a proper modification such that
`π^*φ` has log singularities along the effective `ℚ`-divisor `D`, and `D = (1/d) F` with `F` an
effective divisor. Then, for the arbitrary surjective valuation `ν` (values at its centre),
`Δ_ν(θ, φ) = d⁻¹ Δ(Γ_ν(W))`, `W_k = H⁰(Z, π^*L^{dk} ⊗ 𝒪_Z(-kF))`, i.e.
`Δ_ν(θ, φ) = Δ_ν(π^*L - D) + ν(D)`. -/
theorem partialBody_eq_logResolution_of_kahler_of_isAnalyticModification
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
    (hbig : SGPT.LineBundle.IsBig f L (m + 1))
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hv : Function.Surjective v) {φ : SchemeComplexPoint f → EReal}
    (hK : letI := E.isSeparated; letI := E.quasiCompact;
      IsKahlerCurrentPotential (H.curvature a) φ)
    (hA : letI := E.isSeparated; letI := E.quasiCompact;
      HasManifoldAnalyticSingularityType (n := m + 1) φ)
    {π : Z → SchemeComplexPoint f}
    (hπ : letI := E.isSeparated; letI := E.quasiCompact;
      IsAnalyticModification (n := m + 1) π)
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
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm ''
          (((d : ℝ)⁻¹) • Okounkov.body (pullbackDivisorSectionSemigroup f E v
            (valuationCenter f v) (a.tensorPower d) π hπ.1.continuous F)) := by
  let := E.isSeparated
  let := E.quasiCompact
  let := E.isProper
  have : Nonempty (SchemeComplexPoint f) := nonempty_schemeComplexPoint f E
  set c := valuationCenter f v with hcdef
  have hc : IsNonnegAt v c := isNonnegAt_valuationCenter f v
  obtain ⟨hKc, hKv, hbody, -⟩ :=
    OriginalInftyBodyLimit.infty_body_eq_partialBody_and_degree_limit f E a H hbig v hv c hK hA
  refine ⟨hKc, hKv, ?_⟩
  rw [← hbody]
  congr 1
  -- `Γ^∞(θ, φ)` as the semigroup of the Veronese computation
  have hS : ValGen.inftySemigroup f E a c v φ =
      OkoNov16.originalInftySectionSemigroup f (m + 1) E v c a φ :=
    AddSubsemigroup.ext fun _ => Iff.rfl
  -- `Γ^∞(dθ, dφ) = Γ_ν(W)`
  have hW : OkoNov16.originalInftySectionSemigroup f (m + 1) E v c (a.tensorPower d)
      (fun y => (d : EReal) * φ y) =
      pullbackDivisorSectionSemigroup f E v c (a.tensorPower d) π hπ.1.continuous F := by
    apply SetLike.coe_injective
    change AlgebraicValuation.inftySectionSet f (m + 1) E v c (a.tensorPower d)
        (fun y => (d : EReal) * φ y) =
      AlgebraicValuation.sectionValueSet v c (a.tensorPower d) fun k s => IsPullbackIdealSection f E π (k • F).ideal k s
    exact sectionValueSet_congr v c (a.tensorPower d) fun k s =>
      isInftySection_iff_isPullbackIdealSection hπ hlog F hd hDF k s
  have hver := OkoNov16.original_inftySectionBody_veronese f (m + 1) E v c hc a φ hd
  rw [hW] at hver
  rw [hver, hS, inv_smul_smul₀ (by exact_mod_cast hd.ne' : (d : ℝ) ≠ 0)]

/-- **Source `rmk:DeltaanaW0`, `eq:DeltaanaW0`.** For a modification `π : Y → X` (a finite
sequence of blow-ups with smooth centres, the book's convention) such that `π^*φ` has log
singularities along the effective `ℚ`-divisor `D = (1/d) F`:
`Δ_ν(θ, φ) = d⁻¹ Δ(Γ_ν(W)) = Δ_ν(π^*L - D) + ν(D)`. -/
theorem partialBody_eq_logResolution_of_kahler
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
    (hbig : SGPT.LineBundle.IsBig f L (m + 1))
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hv : Function.Surjective v) {φ : SchemeComplexPoint f → EReal}
    (hK : letI := E.isSeparated; letI := E.quasiCompact;
      IsKahlerCurrentPotential (H.curvature a) φ)
    (hA : letI := E.isSeparated; letI := E.quasiCompact;
      HasManifoldAnalyticSingularityType (n := m + 1) φ)
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
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm ''
          (((d : ℝ)⁻¹) • Okounkov.body (pullbackDivisorSectionSemigroup f E v
            (valuationCenter f v) (a.tensorPower d) π
              (HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hseq).1.continuous
              F)) :=
  let := E.isSeparated
  let := E.quasiCompact
  partialBody_eq_logResolution_of_kahler_of_isAnalyticModification f E a H hbig v hv hK hA
    (HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hseq) hlog F hd hDF

/-! ### The presentation-free right-hand side -/

omit [SmoothOfRelativeDimension (m + 1) f] [IsIntegral X] in
/-- **Every effective `ℚ`-divisor on a compact manifold is `(1/d) F`** for an effective
(Cartier) divisor `F` and `d > 0` (its finitely many coefficients have a common denominator). -/
theorem exists_cartier_presentation [CompactSpace Z] (D : EffectiveGeometricQDivisor (m + 1) Z) :
    ∃ (d : ℕ) (F : EffectiveDivisor (m + 1) Z),
      0 < d ∧ D = cartierGeometricQDivisor F (1 / (d : ℚ)) (by positivity) := by
  obtain ⟨d, F, hd, hcoeff⟩ := OkoNov16.AttributedGeometricLogReuse.compact_exists_global_integral_cartier D
  refine ⟨d, F, hd, ?_⟩
  have hc : ∀ Q, D.coefficient Q =
      (cartierGeometricQDivisor F (1 / (d : ℚ)) (by positivity)).coefficient Q := by
    intro Q
    rw [hcoeff Q, cartierGeometricQDivisor_coefficient]
    ring
  have hext : ∀ {A B : EffectiveGeometricQDivisor (m + 1) Z},
      (∀ Q, A.coefficient Q = B.coefficient Q) → A = B := by
    intro A B h
    cases A
    cases B
    have h' := funext h
    cases h'
    rfl
  exact hext hc

end Formula

end SGPT.Okounkov.OF8
