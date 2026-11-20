import SGPT.Okounkov.OF9ModelFlagUniqueness
import SGPT.Okounkov.OF9FlagLiftingRecognition
import SGPT.Okounkov.FlagLiftingExistence
import SGPT.Okounkov.FiniteBlowupCommonModification
import SGPT.Okounkov.OF2AbhyankarCurve
import SGPT.Okounkov.OF4ValCurrLiftedFlags
import SGPT.Foundations.Analysis.Pending.ProperMappingTheorem

/-!
# `rmk:valcurr`: `ν(T)` does not depend on the resolution

Source: chapter *The theory of Okounkov bodies*, `rmk:valcurr`: for a rank `n` surjective valuation
`ν` of `ℂ(X)` and a presentation `ν = ν_{Y•} g` on a resolution `π : Y → X`,
`ν(T) := ν_{Y•}(π^*T) g`; *"this definition does not depend on the choice of `π`, by passing to a
common resolution and applying `prop:cormatrix` and `prop:cormult`."*

The book's modifications and resolutions are finite sequences of blow-ups with smooth centres
(`def:modif`, `thm:res`).  We prove the independence for any two presentations on such
modifications of an integral smooth projective complex scheme `X`, including flags with
exceptional members:

* `genFun_comp_mem_iff_global_zero`, `prefixValuation_pos_iff_global_zero_comp`: the polynomial
  criterion of `OF9ModelFlagUniqueness` read on a flag of a model `M'` dominating a rational model
  `M` through `q : M' → M`;
* `image_flag_eq_of_lexEquivalent`: if the flag `W•` of `M'` and the flag `Y•` of the rational model
  `M` induce equivalent valuations of `ℂ(X)`, then `q(Wₖ) = Yₖ` for every `k` (inclusion by the
  polynomial criterion and Chow; equality by Remmert's proper mapping theorem and Chow);
* **`isFlagLifting_of_lexEquivalent`**: hence `W•` is the lifting of `Y•` along `q`
  (`OF9.isFlagLifting_of_image_eq`);
* **`modificationPresentationValue_eq_of_isBlowupSequence`** (`rmk:valcurr`): two presentations
  `ν = (ν_{F₁} ∘ π₁^*) G₁ = (ν_{F₂} ∘ π₂^*) G₂` of a surjective `ν` by smooth flags on two finite
  blow-up towers `πᵢ : Xᵢ → X(ℂ)` give the same `ν(T)` for every closed positive `(1,1)`-current
  `T = θ + dd^c u` on `X(ℂ)`.  Proof: a common modification `U` of `X₁` and `X₂`
  (`exists_kahler_commonModification_of_isBlowupSequence`), a further blow-up tower on which
  `F₁•` lifts (`thm:liftableflag`, `exists_flagLifting_dominating_nativeModel`); the lifted flag
  induces a valuation equivalent to `ν`, hence (above) it is also the lifting of `F₂•`; then the
  common-lifting argument (`OF4.modificationPresentationValue_eq_of_common_lifting`:
  `prop:cormatrix`, `prop:cormult`) applies.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov.OF9

open CategoryTheory AlgebraicGeometry Set Filter SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.Okounkov.ValCurr
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.GAGA.H0S SGPT.GAGA.ChowBl
open GlobalCurrents CanonicalCurrentFrame GlobalPositiveCurrentACRestriction
open NaturalThetaPshGeometricCurrent NaturalThetaPshClosedCurrent
open scoped Topology Manifold ContDiff Matrix

/-- **Homogeneous equations pulled back to a dominating flag** are determined by their germ at the
flag point (identity theorem on the connected flag member). -/
theorem genFun_comp_mem_iff_global_zero {n N d : ℕ} (W : OriginalFlagGeometry.{0} n)
    (x : OriginalFlagGermPoint W) {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
    {Ψ : M → ComplexProjectiveSpace N} (hΨ : IsHolomorphicEmbedding (n := n) Ψ)
    {q : W.carrier → M} (hq : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ q)
    (k : ℕ) (hk : k ≤ n) (i : Fin (N + 1)) (hi : Ψ (q x.1) ∈ (affineChart i).source)
    {P : MvPolynomial (Fin (N + 1)) ℂ} (hP : P.IsHomogeneous d) :
    (vanishingIdeal (n := n) (W.flag ⟨k, Nat.lt_succ_of_le hk⟩)).mem x.1 (genFun Ψ i P ∘ q) ↔
      ∀ y ∈ W.flag ⟨k, Nat.lt_succ_of_le hk⟩, MvPolynomial.eval (Ψ (q y)).rep P = 0 := by
  let j : Fin (n + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
  have hx : x.1 ∈ W.flag j := W.smooth.2.1 (Fin.le_last j) x.property
  have hnear : ∀ᶠ y in 𝓝 x.1, Ψ (q y) ∈ (affineChart i).source :=
    (hΨ.continuous.comp hq.continuous).continuousAt.eventually
      ((affineChart i).open_source.mem_nhds hi)
  constructor
  · intro hv
    let : ChartedSpace (ComplexModel (n - (j : ℕ))) (W.flag j) := W.componentCharts j
    have : IsComplexManifold (n - (j : ℕ)) (W.flag j) := W.componentComplex j
    have : ConnectedSpace (W.flag j) :=
      isConnected_iff_connectedSpace.mp (W.smooth.2.2 j).2.1
    let xp : W.flag j := ⟨x.1, hx⟩
    let A : Set (W.flag j) := {y | MvPolynomial.eval (Ψ (q y.1)).rep P = 0}
    have hinc : ContMDiff 𝓘(ℂ, ComplexModel (n - (j : ℕ))) 𝓘(ℂ, ComplexModel n) ∞
        (Subtype.val : W.flag j → W.carrier) :=
      SubmanifoldChartedSpace.contMDiff_val (Nat.sub_le n j) (W.smooth.2.2 j).2.2
    have hA : IsComplexAnalyticSubset (n := n - (j : ℕ)) A :=
      AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
        (((SGPT.GAGA.SmoothFlags.contMDiff_of_isHolomorphicEmbedding hΨ).comp hq).comp hinc)
        (isComplexAnalyticSubset_homogeneousPolynomialZeroSet hP)
    have hxA : xp ∈ interior A := by
      apply mem_interior_iff_mem_nhds.mpr
      filter_upwards [continuous_subtype_val.continuousAt.eventually hv.2,
        continuous_subtype_val.continuousAt.eventually hnear] with y hy hyi
      exact (eval_rep_eq_zero_iff_genFun Ψ i hyi hP).mpr (hy y.property)
    have hAeq := hA.eq_univ_of_interior_nonempty ⟨xp, hxA⟩
    intro y hy
    have hmem : (⟨y, hy⟩ : W.flag j) ∈ A := by rw [hAeq]; exact mem_univ _
    exact hmem
  · intro hglobal
    refine ⟨HolomorphicAt.comp_contMDiff (holomorphicAt_genFun hΨ hi P)
      (Eventually.of_forall fun y => hq y), ?_⟩
    filter_upwards [hnear] with y hy
    intro hyF
    exact (eval_rep_eq_zero_iff_genFun Ψ i hy hP).mp (hglobal y hyF)

section Scheme

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) {n : ℕ}
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance of9InTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of9InCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance of9InManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- **The polynomial criterion on a dominating model.** Let `q : W.carrier → F.carrier` be an
analytic modification over the model `ρ`, and `r ∈ ℂ(X)` with `ρ^* r · Q(Ψ) = P(Ψ)` on
`F.carrier`.  If `Q(Ψ(q w)) ≠ 0` at the flag point `w` of `W•`, the `k`-th prefix of
`ν_{W•} ∘ (ρ q)^*` is positive at `r` iff `P` vanishes on `Ψ(q(W_k))`. -/
theorem prefixValuation_pos_iff_global_zero_comp (F W : OriginalFlagGeometry.{0} n)
    {ρ : F.carrier → SchemeComplexPoint f} (hρ : IsAnalyticModification (n := n) ρ)
    {q : W.carrier → F.carrier} (hq : IsAnalyticModification (n := n) q)
    (hρq : IsAnalyticModification (n := n) (ρ ∘ q)) {N : ℕ}
    {Ψ : F.carrier → ComplexProjectiveSpace N} (hΨ : IsHolomorphicEmbedding (n := n) Ψ) {d : ℕ}
    {P Q : MvPolynomial (Fin (N + 1)) ℂ} (hP : P.IsHomogeneous d) (hQ : Q.IsHomogeneous d)
    (r : X.functionField)
    (hr : ∀ (y : F.carrier) (i : Fin (N + 1)) (hi : Ψ y ∈ (affineChart i).source),
      ratGerm f hρ y r * algebraMap _ (FractionRing (NativeHolGerm n F.carrier y))
          (polyGerm hΨ hi Q) =
        algebraMap _ (FractionRing (NativeHolGerm n F.carrier y)) (polyGerm hΨ hi P))
    (x : OriginalFlagGermPoint W) (hQx : MvPolynomial.eval (Ψ (q x.1)).rep Q ≠ 0)
    (k : ℕ) (hk : k ≤ n) :
    0 < prefixValuation hk (OF2.modificationFlagValuation f W hρq) r ↔
      ∀ y ∈ W.flag ⟨k, Nat.lt_succ_of_le hk⟩, MvPolynomial.eval (Ψ (q y)).rep P = 0 := by
  set i := chartIndex (Ψ (q x.1))
  have hi : Ψ (q x.1) ∈ (affineChart i).source := mem_affineChart_chartIndex _
  have hhol : HolomorphicAt n (genFun Ψ i P ∘ q) x.1 :=
    HolomorphicAt.comp_contMDiff (holomorphicAt_genFun hΨ hi P)
      (Eventually.of_forall fun y => hq.1 y)
  have hcomP : NativeHolGerm.comap q hq.1 x.1 (polyGerm hΨ hi P) =
      NativeHolGerm.mk (genFun Ψ i P ∘ q) hhol := Subtype.ext rfl
  have hunit : IsUnit (NativeHolGerm.comap q hq.1 x.1 (polyGerm hΨ hi Q)) := by
    rw [NativeHolGerm.isUnit_iff_eval_ne_zero, NativeHolGerm.eval_comap, eval_polyGerm]
    exact fun h0 => hQx ((eval_rep_eq_zero_iff_genFun Ψ i hi hQ).mpr h0)
  have hval : OF2.modificationFlagValuation f W hρq r =
      originalFlagGermValuation W x (NativeHolGerm.mk (genFun Ψ i P ∘ q) hhol) := by
    rw [OF2.modificationFlagValuation_eq_at f W hρq x]
    change originalFlagGermFractionValuation W x (ratGerm f hρq x.1 r) = _
    have hrel := congrArg (fracComap hq x.1) (hr (q x.1) i hi)
    rw [map_mul, fracComap_algebraMap, fracComap_algebraMap,
      ← ratGerm_comp f hρ hq hρq] at hrel
    have h := congrArg (originalFlagGermFractionValuation W x) hrel
    rw [AddValuation.map_mul, originalFlagGermFractionValuation_algebraMap,
      originalFlagGermFractionValuation_algebraMap,
      originalFlagGermValuation_eq_zero_of_isUnit W x hunit, add_zero, hcomP] at h
    exact h
  change 0 < prefixWithTopHom hk (OF2.modificationFlagValuation f W hρq r) ↔ _
  rw [hval]
  change 0 < prefixValuation hk (originalFlagGermValuation W x)
    (NativeHolGerm.mk (genFun Ψ i P ∘ q) hhol) ↔ _
  rw [originalFlagPrefixValuation_pos_iff_vanishingIdeal W x k hk _ hhol]
  exact genFun_comp_mem_iff_global_zero W x hΨ hq.1 k hk i hi hP

/-- **Equivalent valuations have the same flag images.** Let `ρ : F.carrier → X(ℂ)` be a model with
a rational embedding, `q : W.carrier → F.carrier` an analytic modification, and suppose that the
flags `F•` and `W•` induce equivalent valuations of `ℂ(X)`.  Then `q(Wₖ) = Fₖ` for every `k`. -/
theorem image_flag_eq_of_lexEquivalent (F W : OriginalFlagGeometry.{0} n)
    {ρ : F.carrier → SchemeComplexPoint f} (hρ : IsAnalyticModification (n := n) ρ) {N : ℕ}
    {Ψ : F.carrier → ComplexProjectiveSpace N} (hΨ : IsHolomorphicEmbedding (n := n) Ψ)
    (hR : IsRationalEmbedding f hρ hΨ)
    {q : W.carrier → F.carrier} (hq : IsAnalyticModification (n := n) q)
    (hρq : IsAnalyticModification (n := n) (ρ ∘ q))
    (h : ValuationsLexEquivalent (OF2.modificationFlagValuation f F hρ)
      (OF2.modificationFlagValuation f W hρq)) (j : Fin (n + 1)) :
    q '' W.flag j = F.flag j := by
  let x : OriginalFlagGermPoint F := OF2.modificationFlagPoint n F
  let x' : OriginalFlagGermPoint W := OF2.modificationFlagPoint n W
  obtain ⟨ℓ, hℓ, hℓx, hℓx'⟩ :=
    exists_linear_ne_zero (Ψ x.1).rep_ne_zero (Ψ (q x'.1)).rep_ne_zero
  have hk : (j : ℕ) ≤ n := Nat.le_of_lt_succ j.isLt
  -- the two flag members are contained in the same homogeneous hypersurfaces
  have hpoly : ∀ (d : ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ), P.IsHomogeneous d →
      ((∀ y ∈ F.flag j, MvPolynomial.eval (Ψ y).rep P = 0) ↔
        ∀ y ∈ q '' W.flag j, MvPolynomial.eval (Ψ y).rep P = 0) := by
    intro d P hP
    have hQ : (ℓ ^ d).IsHomogeneous d := by
      have := hℓ.pow d
      rwa [one_mul] at this
    have hQx : MvPolynomial.eval (Ψ x.1).rep (ℓ ^ d) ≠ 0 := by
      rw [map_pow]
      exact pow_ne_zero _ hℓx
    have hQx' : MvPolynomial.eval (Ψ (q x'.1)).rep (ℓ ^ d) ≠ 0 := by
      rw [map_pow]
      exact pow_ne_zero _ hℓx'
    obtain ⟨r, hr⟩ := hR d P (ℓ ^ d) hP hQ ⟨x.1, hQx⟩
    have e1 := prefixValuation_pos_iff_global_zero f F hρ hΨ hP hQ r hr x hQx j hk
    have e2 := prefixValuation_pos_iff_global_zero_comp f F W hρ hq hρq hΨ hP hQ r hr x' hQx'
      j hk
    have hsign : 0 < prefixValuation hk (OF2.modificationFlagValuation f F hρ) r ↔
        0 < prefixValuation hk (OF2.modificationFlagValuation f W hρq) r := by
      obtain ⟨G, hG, hmap⟩ := h
      rw [hmap]
      exact (ValCurr.prefixValuation_pos_lexMap_iff hk hG _ r).symm
    have e3 := e1.symm.trans (hsign.trans e2)
    refine e3.trans ⟨fun hW y hy => ?_, fun hW y hy => hW (q y) ⟨y, hy, rfl⟩⟩
    obtain ⟨z, hz, rfl⟩ := hy
    exact hW z hz
  have hFa : IsComplexAnalyticSubset (n := n) (F.flag j) :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      ⟨(F.smooth.2.2 j).1, fun z hz => ⟨n - (j : ℕ), (F.smooth.2.2 j).2.2 z hz⟩⟩
  have hWa : IsComplexAnalyticSubset (n := n) (W.flag j) :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      ⟨(W.smooth.2.2 j).1, fun z hz => ⟨n - (j : ℕ), (W.smooth.2.2 j).2.2 z hz⟩⟩
  have hqa : IsComplexAnalyticSubset (n := n) (q '' W.flag j) :=
    ProperMappingTheorem.isComplexAnalyticSubset_image hq.1 hWa fun K hK =>
      ((W.smooth.2.2 j).1.inter (hK.isClosed.preimage hq.1.continuous)).isCompact
  exact (analytic_subset_eq_of_global_homogeneous_polynomials hΨ hFa hqa hpoly).symm

/-- **Recognition of liftings by valuations.** If the flag `W•` on a model dominating, through
`q`, a rational model `ρ` with flag `F•` induces a valuation of `ℂ(X)` equivalent to that of
`F•`, then `W•` is the lifting of `F•` along `q` (`def:lifting`). -/
theorem isFlagLifting_of_lexEquivalent (F W : OriginalFlagGeometry.{0} n)
    {ρ : F.carrier → SchemeComplexPoint f} (hρ : IsAnalyticModification (n := n) ρ) {N : ℕ}
    {Ψ : F.carrier → ComplexProjectiveSpace N} (hΨ : IsHolomorphicEmbedding (n := n) Ψ)
    (hR : IsRationalEmbedding f hρ hΨ)
    {q : W.carrier → F.carrier} (hq : IsAnalyticModification (n := n) q)
    (hρq : IsAnalyticModification (n := n) (ρ ∘ q))
    (h : ValuationsLexEquivalent (OF2.modificationFlagValuation f F hρ)
      (OF2.modificationFlagValuation f W hρq)) :
    IsFlagLifting F W q :=
  isFlagLifting_of_image_eq n F W q hq
    (image_flag_eq_of_lexEquivalent f F W hρ hΨ hR hq hρq h)

end Scheme

/-! ### `rmk:valcurr`: independence of the resolution -/

section Presentation

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) {m : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] [IsSeparated f] [QuasiCompact f]

local instance of9VcTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of9VcCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance of9VcManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

/-- **`rmk:valcurr`: `ν(T)` does not depend on the resolution.** Let `X` be an integral smooth
projective complex scheme of dimension `m + 1` and `ν` a surjective valuation
`ℂ(X)^× → ℤ^{m+1}_lex`.  Two presentations `ν = (ν_{F₁•} ∘ π₁^*) G₁ = (ν_{F₂•} ∘ π₂^*) G₂` by smooth
flags on two modifications `πᵢ : Xᵢ → X(ℂ)` (finite sequences of blow-ups with smooth centres,
`def:modif`; the flags may have exceptional members), with `Gᵢ` unipotent upper triangular, give
the same value `ν(T) = ν_{F₁•}(π₁^*T) G₁ = ν_{F₂•}(π₂^*T) G₂` for every closed positive
`(1,1)`-current `T = θ + dd^c u` on `X(ℂ)`. -/
theorem modificationPresentationValue_eq_of_isBlowupSequence (E : ClosedProjectiveEmbedding f)
    {F₁ F₂ : OriginalFlagGeometry.{0} (m + 1)}
    {π₁ : F₁.carrier → SchemeComplexPoint f} (hπ₁ : IsAnalyticModification (n := m + 1) π₁)
    (hs₁ : IsBlowupSequence (m + 1) (SchemeComplexPoint f) F₁.carrier π₁)
    {π₂ : F₂.carrier → SchemeComplexPoint f} (hπ₂ : IsAnalyticModification (n := m + 1) π₂)
    (hs₂ : IsBlowupSequence (m + 1) (SchemeComplexPoint f) F₂.carrier π₂)
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hv : Function.Surjective v)
    {G₁ G₂ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hG₁ : IsUnitUpperTriangular G₁)
    (hG₂ : IsUnitUpperTriangular G₂)
    (h₁ : v = lexMapValuation G₁ hG₁ (OF2.modificationFlagValuation f F₁ hπ₁))
    (h₂ : v = lexMapValuation G₂ hG₂ (OF2.modificationFlagValuation f F₂ hπ₂))
    (θ : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f)) (u : SchemeComplexPoint f → EReal)
    (hu : IsThetaPshPotential θ.val u) :
    OF2.modificationPresentationValue f F₁ hπ₁ G₁ θ u hu =
      OF2.modificationPresentationValue f F₂ hπ₂ G₂ θ u hu := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  -- a common modification, Kähler, finite over `X₂`
  obtain ⟨U, tU, aU, mU, σ, ℓ, hUc, ⟨omegaU⟩, -, hσ, hℓ, hsquare⟩ :=
    exists_kahler_commonModification_of_isBlowupSequence hs₁ hπ₂ ⟨F₂.omega⟩
  let := tU
  let := aU
  let := mU
  let := hUc
  -- lift `F₁•` to a further blow-up tower over `U`
  obtain ⟨W, a, ha, hL₁⟩ := exists_flagLifting_dominating_nativeModel (m + 1) F₁ U omegaU ℓ hℓ
  have ham : IsAnalyticModification (n := m + 1) a :=
    isAnalyticModification_of_isBlowupSequence ha
  have hq : IsAnalyticModification (n := m + 1) (σ ∘ a) :=
    AnalyticModificationComposition.isAnalyticModification_comp hσ ham
  have hcomm : π₁ ∘ (ℓ ∘ a) = π₂ ∘ (σ ∘ a) := by
    funext w
    exact congrFun hsquare (a w)
  have hρ₁ := AnalyticModificationComposition.isAnalyticModification_comp hπ₁ hL₁.1
  have hρ₂ := AnalyticModificationComposition.isAnalyticModification_comp hπ₂ hq
  -- the lifted flag presents `ν`
  obtain ⟨hv₁, -⟩ := OF2.modificationPresentationValue_lifting f hπ₁ hL₁ v hG₁ h₁ θ u hu
  rw [OF4.modificationFlagValuation_congr_map f W hcomm hρ₁ hρ₂] at hv₁
  have hequiv : ValuationsLexEquivalent (OF2.modificationFlagValuation f F₂ hπ₂)
      (OF2.modificationFlagValuation f W hρ₂) :=
    valuationsLexEquivalent_equivalence.trans ⟨G₂, hG₂, h₂⟩
      (valuationsLexEquivalent_equivalence.symm ⟨_, _, hv₁⟩)
  -- hence it is also the lifting of `F₂•`
  obtain ⟨-, N, Ψ, hΨ, hR⟩ := exists_isRationalEmbedding_of_isBlowupSequence f E hs₂
  have hL₂ : IsFlagLifting F₂ W (σ ∘ a) :=
    isFlagLifting_of_lexEquivalent f F₂ W hπ₂ hΨ hR hq hρ₂ hequiv
  exact OF4.modificationPresentationValue_eq_of_common_lifting f hπ₁ hπ₂ hL₁ hL₂ hcomm v hv
    hG₁ hG₂ h₁ h₂ θ u hu

/-- A **presentation** of a valuation `ν` of `ℂ(X)` on a resolution, in the sense of `rmk:valcurr`:
a modification `π : Y → X(ℂ)` which is a finite sequence of blow-ups with smooth centres
(`def:modif`), a smooth flag `Y•` on `Y` (bundled with `Y` as an `OriginalFlagGeometry`) and
`G ∈ Aut(ℤⁿ_lex)` (unipotent upper triangular) with `ν = ν_{Y•} G`. -/
structure BlowupPresentation (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    where
  /-- The resolution together with its smooth flag. -/
  F : OriginalFlagGeometry.{0} (m + 1)
  /-- The resolution map. -/
  π : F.carrier → SchemeComplexPoint f
  isModification : IsAnalyticModification (n := m + 1) π
  isBlowupSequence : IsBlowupSequence (m + 1) (SchemeComplexPoint f) F.carrier π
  /-- The matrix of the automorphism `g` of `ℤⁿ_lex`. -/
  G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ
  unitriangular : IsUnitUpperTriangular G
  presents : v = lexMapValuation G unitriangular (OF2.modificationFlagValuation f F isModification)

/-- **`rmk:valcurr`, the definition of `ν(T)`**: the value `ν_{Y•}(π^*T) G` of any presentation of
`ν` on a resolution (`0` if `ν` has none), for `T = θ + dd^c u`. -/
def valuationCurrentValue (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (θ : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f)) (u : SchemeComplexPoint f → EReal)
    (hu : IsThetaPshPotential θ.val u) : Fin (m + 1) → ℝ := by
  classical
  exact if h : Nonempty (BlowupPresentation f v) then
    OF2.modificationPresentationValue f h.some.F h.some.isModification h.some.G θ u hu
  else 0

/-- **`rmk:valcurr`: `ν(T)` is well defined.** For a surjective `ν`, the value of EVERY
presentation of `ν` on a resolution is `ν(T)`. -/
theorem valuationCurrentValue_eq (E : ClosedProjectiveEmbedding f)
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hv : Function.Surjective v) (P : BlowupPresentation f v)
    (θ : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f)) (u : SchemeComplexPoint f → EReal)
    (hu : IsThetaPshPotential θ.val u) :
    valuationCurrentValue f v θ u hu =
      OF2.modificationPresentationValue f P.F P.isModification P.G θ u hu := by
  classical
  have h : Nonempty (BlowupPresentation f v) := ⟨P⟩
  unfold valuationCurrentValue
  rw [dif_pos h]
  exact modificationPresentationValue_eq_of_isBlowupSequence f E h.some.isModification
    h.some.isBlowupSequence P.isModification P.isBlowupSequence v hv h.some.unitriangular
    P.unitriangular h.some.presents P.presents θ u hu

/-- In dimension one every surjective valuation has a presentation on `X` itself (`π = id`,
`G = I`), by the curve theorem; hence `ν(T)` is defined for every surjective `ν`. -/
theorem nonempty_blowupPresentation_of_curve (E : ClosedProjectiveEmbedding f) (hm : m = 0)
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hv : Function.Surjective v) : Nonempty (BlowupPresentation f v) := by
  subst hm
  obtain ⟨Y, hY, hvY⟩ := OF2.exists_isSmoothFlag_eq_flagValuation_of_curve f E v hv
  refine ⟨{ F := schemeFubiniStudyOriginalFlagGeometry f (0 + 1) E Y hY
            π := id
            isModification := OF4.isAnalyticModification_flagGeometry_id f E Y hY
            isBlowupSequence := IsBlowupSequence.refl
            G := 1
            unitriangular := IsUnitUpperTriangular.one
            presents := ?_ }⟩
  rw [OF4.modificationFlagValuation_id_eq f E Y hY]
  apply AddValuation.ext
  intro r
  rw [lexMapValuation_apply, lexWithTopHom_one, ← hvY]

end Presentation

end SGPT.Okounkov.OF9
