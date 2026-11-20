import SGPT.Okounkov.OF9BlowupRationalEmbedding
import SGPT.Okounkov.OF4ValCurrCommonLifting
import SGPT.Okounkov.FlagValuationChoiceIndependence
import SGPT.Okounkov.FlagValuationPrefixIdeals

/-!
# `rmk:valcurr`: a smooth flag on a modification is determined by its valuation

Source: chapter *The theory of Okounkov bodies*, `rmk:valcurr`: `ν(T) := ν_{Y•}(π^*T) g` for a
presentation `ν = ν_{Y•} g` on a resolution `π`; *"this definition does not depend on the choice
of `π`, by passing to a common resolution and applying `prop:cormatrix` and `prop:cormult`."*

The step of the book's argument left open by lanes OF2/OF4: on the common resolution, the two
lifted flags induce equivalent valuations of `ℂ(X)`, and they must **coincide**.  We prove this for
every model which is a modification in the sense of the book (`def:modif`: a finite sequence of
blow-ups with smooth centres of `X(ℂ)`), and more generally on every model with a rational
projective embedding (`OF9.IsRationalEmbedding`):

* `prefixValuation_pos_iff_global_zero`: for `P, Q` homogeneous of degree `d` with
  `ρ^* q · Q(Ψ) = P(Ψ)` and `Q(Ψ(w)) ≠ 0` at the flag point `w`, the `k`-th prefix of the induced
  valuation is positive on `q` iff `P` vanishes on the whole flag member `Ψ(W_k)`;
* **`modificationFlags_eq_of_lexEquivalent`**: two smooth flags on a rational model whose induced
  valuations of `ℂ(X)` are equivalent (`ν' = ν G`, `G` unipotent upper triangular) are equal
  (Chow: an analytic subset of `ℙᴺ` is cut out by the homogeneous polynomials vanishing on it);
* **`modificationFlags_eq_of_isBlowupSequence`**: the same on every finite sequence of blow-ups
  with smooth centres of `X(ℂ)` (`exists_isRationalEmbedding_of_isBlowupSequence`);
* **`modificationPresentationValue_eq_of_common_model`**: the book's common-resolution argument
  without the extra hypothesis of OF4: two presentations
  `ν = (ν_{F₁} ∘ π₁^*) G₁ = (ν_{F₂} ∘ π₂^*) G₂`
  of a surjective valuation give the same `ν(T)` as soon as the two flags have liftings `Y¹•`,
  `Y²•` to one common model `M` over `X(ℂ)` (`π₁ p₁ = π₂ p₂`) which is a blow-up tower of `X(ℂ)`:
  the liftings coincide (`Y¹• = Y²•`) and OF4's argument applies.
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

/-- Two nonzero vectors are both off some hyperplane. -/
theorem exists_linear_ne_zero {N : ℕ} {a b : Fin (N + 1) → ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ ℓ : MvPolynomial (Fin (N + 1)) ℂ, ℓ.IsHomogeneous 1 ∧ MvPolynomial.eval a ℓ ≠ 0 ∧
      MvPolynomial.eval b ℓ ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hb
  have hi' : a i ≠ 0 := hi
  have hj' : b j ≠ 0 := hj
  by_cases hbi : b i = 0
  · by_cases haj : a j = 0
    · refine ⟨MvPolynomial.X i + MvPolynomial.X j,
        (MvPolynomial.isHomogeneous_X ℂ i).add (MvPolynomial.isHomogeneous_X ℂ j), ?_, ?_⟩
      · rw [map_add, MvPolynomial.eval_X, MvPolynomial.eval_X, haj, add_zero]
        exact hi'
      · rw [map_add, MvPolynomial.eval_X, MvPolynomial.eval_X, hbi, zero_add]
        exact hj'
    · exact ⟨MvPolynomial.X j, MvPolynomial.isHomogeneous_X ℂ j,
        by rw [MvPolynomial.eval_X]; exact haj, by rw [MvPolynomial.eval_X]; exact hj'⟩
  · exact ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X ℂ i,
      by rw [MvPolynomial.eval_X]; exact hi', by rw [MvPolynomial.eval_X]; exact hbi⟩

/-- The flag valuation of a unit germ vanishes. -/
theorem originalFlagGermValuation_eq_zero_of_isUnit {n : ℕ} (F : OriginalFlagGeometry.{0} n)
    (x : OriginalFlagGermPoint F) {u : NativeHolGerm n F.carrier x.1} (hu : IsUnit u) :
    originalFlagGermValuation F x u = 0 := by
  obtain ⟨w, rfl⟩ := hu
  have h1 := (originalFlagGermValuation F x).map_mul w.val w.inv
  rw [w.val_inv, (originalFlagGermValuation F x).map_one] at h1
  have h2 := originalFlagGermValuation_nonneg F x w.val
  have h3 := originalFlagGermValuation_nonneg F x w.inv
  exact le_antisymm (h1 ▸ le_add_of_nonneg_right h3) h2

section Scheme

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) {n : ℕ}
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance of9FlTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of9FlCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance of9FlManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- **Prefix positivity reads global polynomial vanishing.** On a model `π` with a holomorphic
embedding `Ψ`, let `q ∈ ℂ(X)` satisfy `π^* q · Q(Ψ) = P(Ψ)` everywhere (`P, Q` homogeneous of
degree `d`), with `Q(Ψ(w)) ≠ 0` at the flag point `w` of a smooth flag `W•`.  Then the `k`-th
prefix of `ν_{W•} ∘ π^*` is positive at `q` iff `P` vanishes on `Ψ(W_k)`. -/
theorem prefixValuation_pos_iff_global_zero (F : OriginalFlagGeometry.{0} n)
    {π : F.carrier → SchemeComplexPoint f} (hπ : IsAnalyticModification (n := n) π) {N : ℕ}
    {Ψ : F.carrier → ComplexProjectiveSpace N} (hΨ : IsHolomorphicEmbedding (n := n) Ψ) {d : ℕ}
    {P Q : MvPolynomial (Fin (N + 1)) ℂ} (hP : P.IsHomogeneous d) (hQ : Q.IsHomogeneous d)
    (q : X.functionField)
    (hq : ∀ (y : F.carrier) (i : Fin (N + 1)) (hi : Ψ y ∈ (affineChart i).source),
      ratGerm f hπ y q * algebraMap _ (FractionRing (NativeHolGerm n F.carrier y))
          (polyGerm hΨ hi Q) =
        algebraMap _ (FractionRing (NativeHolGerm n F.carrier y)) (polyGerm hΨ hi P))
    (x : OriginalFlagGermPoint F) (hQx : MvPolynomial.eval (Ψ x.1).rep Q ≠ 0)
    (k : ℕ) (hk : k ≤ n) :
    0 < prefixValuation hk (OF2.modificationFlagValuation f F hπ) q ↔
      ∀ y ∈ F.flag ⟨k, Nat.lt_succ_of_le hk⟩, MvPolynomial.eval (Ψ y).rep P = 0 := by
  set i := chartIndex (Ψ x.1)
  have hi : Ψ x.1 ∈ (affineChart i).source := mem_affineChart_chartIndex _
  have hval : OF2.modificationFlagValuation f F hπ q =
      originalFlagGermValuation F x (polyGerm hΨ hi P) := by
    rw [OF2.modificationFlagValuation_eq_at f F hπ x]
    change originalFlagGermFractionValuation F x (ratGerm f hπ x.1 q) = _
    have hu : originalFlagGermFractionValuation F x
        (algebraMap _ (FractionRing (NativeHolGerm n F.carrier x.1)) (polyGerm hΨ hi Q)) = 0 := by
      rw [originalFlagGermFractionValuation_algebraMap]
      exact originalFlagGermValuation_eq_zero_of_isUnit F x (isUnit_polyGerm hΨ hi hQ hQx)
    have h := congrArg (originalFlagGermFractionValuation F x) (hq x.1 i hi)
    rw [AddValuation.map_mul, hu, add_zero, originalFlagGermFractionValuation_algebraMap] at h
    exact h
  change 0 < prefixWithTopHom hk (OF2.modificationFlagValuation f F hπ q) ↔ _
  rw [hval]
  change 0 < prefixValuation hk (originalFlagGermValuation F x)
    (NativeHolGerm.mk (genFun Ψ i P) (holomorphicAt_genFun hΨ hi P)) ↔ _
  rw [originalFlagPrefixValuation_pos_iff_vanishingIdeal F x k hk (genFun Ψ i P)
    (holomorphicAt_genFun hΨ hi P)]
  exact originalFlag_genFun_mem_iff_global_polynomial_zero F x Ψ hΨ k hk i hi hP

/-- **A smooth flag on a rational model is determined by its valuation.** Let `π : M → X(ℂ)` be
a model with a rational projective embedding.  Two smooth flags `Y•`, `Y'•` on `M` whose induced
valuations `ν_{Y•} ∘ π^*`, `ν_{Y'•} ∘ π^*` of `ℂ(X)` are equivalent (`ν' = ν G`, `G` unipotent
upper triangular) are equal. -/
theorem modificationFlags_eq_of_lexEquivalent {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] [ConnectedSpace M]
    {π : M → SchemeComplexPoint f} (hπ : IsAnalyticModification (n := n) π) {N : ℕ}
    {Ψ : M → ComplexProjectiveSpace N} (hΨ : IsHolomorphicEmbedding (n := n) Ψ)
    (hR : IsRationalEmbedding f hπ hΨ) (om om' : KahlerBackground n M)
    (Y Y' : Fin (n + 1) → Set M) (hY : IsSmoothFlag Y) (hY' : IsSmoothFlag Y')
    (h : ValuationsLexEquivalent
      (OF2.modificationFlagValuation f (OriginalFlagGeometry.ofOriginal om Y hY) hπ)
      (OF2.modificationFlagValuation f (OriginalFlagGeometry.ofOriginal om' Y' hY') hπ)) :
    Y = Y' := by
  let F := OriginalFlagGeometry.ofOriginal om Y hY
  let F' := OriginalFlagGeometry.ofOriginal om' Y' hY'
  let x : OriginalFlagGermPoint F := OF2.modificationFlagPoint n F
  let x' : OriginalFlagGermPoint F' := OF2.modificationFlagPoint n F'
  obtain ⟨ℓ, hℓ, hℓx, hℓx'⟩ :=
    exists_linear_ne_zero (Ψ x.1).rep_ne_zero (Ψ x'.1).rep_ne_zero
  funext j
  apply analytic_subset_eq_of_global_homogeneous_polynomials hΨ
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      (show IsClosedSubmanifold n (Y j) from
        ⟨(hY.2.2 j).1, fun z hz => ⟨n - (j : ℕ), (hY.2.2 j).2.2 z hz⟩⟩))
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      (show IsClosedSubmanifold n (Y' j) from
        ⟨(hY'.2.2 j).1, fun z hz => ⟨n - (j : ℕ), (hY'.2.2 j).2.2 z hz⟩⟩))
  intro d P hP
  have hQ : (ℓ ^ d).IsHomogeneous d := by
    have := hℓ.pow d
    rwa [one_mul] at this
  have hQx : MvPolynomial.eval (Ψ x.1).rep (ℓ ^ d) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ hℓx
  have hQx' : MvPolynomial.eval (Ψ x'.1).rep (ℓ ^ d) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ hℓx'
  obtain ⟨q, hq⟩ := hR d P (ℓ ^ d) hP hQ ⟨x.1, hQx⟩
  have hk : (j : ℕ) ≤ n := Nat.le_of_lt_succ j.isLt
  have e1 := prefixValuation_pos_iff_global_zero f F hπ hΨ hP hQ q hq x hQx j hk
  have e2 := prefixValuation_pos_iff_global_zero f F' hπ hΨ hP hQ q hq x' hQx' j hk
  have hsign : 0 < prefixValuation hk (OF2.modificationFlagValuation f F hπ) q ↔
      0 < prefixValuation hk (OF2.modificationFlagValuation f F' hπ) q := by
    obtain ⟨G, hG, hmap⟩ := h
    change _ ↔ 0 < prefixValuation hk
      (OF2.modificationFlagValuation f (OriginalFlagGeometry.ofOriginal om' Y' hY') hπ) q
    rw [hmap]
    exact (ValCurr.prefixValuation_pos_lexMap_iff hk hG _ q).symm
  exact e1.symm.trans (hsign.trans e2)

/-- **`rmk:valcurr`: a smooth flag on a modification of `X` is determined by its valuation.**
On a finite sequence of blow-ups with smooth centres `π : M → X(ℂ)` (`def:modif`) of an integral
smooth projective complex scheme `X`, two smooth flags whose induced valuations of `ℂ(X)` are
equivalent are equal. -/
theorem modificationFlags_eq_of_isBlowupSequence (E : ClosedProjectiveEmbedding f) {M : Type}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [CompactSpace M] [ConnectedSpace M] {π : M → SchemeComplexPoint f}
    (hseq : IsBlowupSequence n (SchemeComplexPoint f) M π)
    (hπ : IsAnalyticModification (n := n) π) (om om' : KahlerBackground n M)
    (Y Y' : Fin (n + 1) → Set M) (hY : IsSmoothFlag Y) (hY' : IsSmoothFlag Y')
    (h : ValuationsLexEquivalent
      (OF2.modificationFlagValuation f (OriginalFlagGeometry.ofOriginal om Y hY) hπ)
      (OF2.modificationFlagValuation f (OriginalFlagGeometry.ofOriginal om' Y' hY') hπ)) :
    Y = Y' := by
  obtain ⟨-, N, Ψ, hΨ, hR⟩ := exists_isRationalEmbedding_of_isBlowupSequence f E hseq
  exact modificationFlags_eq_of_lexEquivalent f hπ hΨ hR om om' Y Y' hY hY' h

end Scheme

/-! ### Independence of `ν(T)` through a common blow-up model -/

section Presentation

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) {m : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] [IsSeparated f] [QuasiCompact f]

local instance of9PrTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of9PrCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance of9PrManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

/-- **`rmk:valcurr`, independence through a common resolution.** Let `ν` be a surjective
valuation of `ℂ(X)` with presentations `ν = (ν_{F₁} ∘ π₁^*) G₁ = (ν_{F₂} ∘ π₂^*) G₂` by smooth
flags on two modifications `πᵢ : Xᵢ → X(ℂ)`.  Suppose that both flags lift (`def:lifting`) to
smooth flags `Y¹•`, `Y²•` on one common model `M` (`π₁ p₁ = π₂ p₂`) which is a finite sequence of
blow-ups with smooth centres of `X(ℂ)`.  Then the two lifted flags coincide, and the two
presentations give the same value `ν(T)` for every closed positive `(1,1)`-current
`T = θ + dd^c u` on `X(ℂ)`. -/
theorem modificationPresentationValue_eq_of_common_model (E : ClosedProjectiveEmbedding f)
    {F₁ F₂ : OriginalFlagGeometry.{0} (m + 1)}
    {π₁ : F₁.carrier → SchemeComplexPoint f} (hπ₁ : IsAnalyticModification (n := m + 1) π₁)
    {π₂ : F₂.carrier → SchemeComplexPoint f} (hπ₂ : IsAnalyticModification (n := m + 1) π₂)
    {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
    [IsComplexManifold (m + 1) M] [CompactSpace M] [ConnectedSpace M]
    (om : KahlerBackground (m + 1) M) (Y₁ Y₂ : Fin (m + 1 + 1) → Set M)
    (hY₁ : IsSmoothFlag Y₁) (hY₂ : IsSmoothFlag Y₂)
    {p₁ : M → F₁.carrier} (hp₁ : IsFlagLifting F₁ (OriginalFlagGeometry.ofOriginal om Y₁ hY₁) p₁)
    {p₂ : M → F₂.carrier} (hp₂ : IsFlagLifting F₂ (OriginalFlagGeometry.ofOriginal om Y₂ hY₂) p₂)
    (hcomm : π₁ ∘ p₁ = π₂ ∘ p₂)
    (hseq : IsBlowupSequence (m + 1) (SchemeComplexPoint f) M (π₁ ∘ p₁))
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hv : Function.Surjective v)
    {G₁ G₂ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hG₁ : IsUnitUpperTriangular G₁)
    (hG₂ : IsUnitUpperTriangular G₂)
    (h₁ : v = lexMapValuation G₁ hG₁ (OF2.modificationFlagValuation f F₁ hπ₁))
    (h₂ : v = lexMapValuation G₂ hG₂ (OF2.modificationFlagValuation f F₂ hπ₂))
    (θ : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f)) (u : SchemeComplexPoint f → EReal)
    (hu : IsThetaPshPotential θ.val u) :
    Y₁ = Y₂ ∧
      OF2.modificationPresentationValue f F₁ hπ₁ G₁ θ u hu =
        OF2.modificationPresentationValue f F₂ hπ₂ G₂ θ u hu := by
  obtain ⟨hv₁, -⟩ := OF2.modificationPresentationValue_lifting f hπ₁ hp₁ v hG₁ h₁ θ u hu
  obtain ⟨hv₂, -⟩ := OF2.modificationPresentationValue_lifting f hπ₂ hp₂ v hG₂ h₂ θ u hu
  have hρ₁ := AnalyticModificationComposition.isAnalyticModification_comp hπ₁ hp₁.1
  have hρ₂ := AnalyticModificationComposition.isAnalyticModification_comp hπ₂ hp₂.1
  rw [OF4.modificationFlagValuation_congr_map f _ hcomm.symm hρ₂ hρ₁] at hv₂
  have hequiv : ValuationsLexEquivalent
      (OF2.modificationFlagValuation f (OriginalFlagGeometry.ofOriginal om Y₁ hY₁) hρ₁)
      (OF2.modificationFlagValuation f (OriginalFlagGeometry.ofOriginal om Y₂ hY₂) hρ₁) :=
    valuationsLexEquivalent_equivalence.trans ⟨_, _, hv₁⟩
      (valuationsLexEquivalent_equivalence.symm ⟨_, _, hv₂⟩)
  have hY : Y₁ = Y₂ :=
    modificationFlags_eq_of_isBlowupSequence f E hseq hρ₁ om om Y₁ Y₂ hY₁ hY₂ hequiv
  subst hY
  exact ⟨rfl, OF4.modificationPresentationValue_eq_of_common_lifting f hπ₁ hπ₂ hp₁ hp₂ hcomm
    v hv hG₁ hG₂ h₁ h₂ θ u hu⟩

end Presentation

end SGPT.Okounkov.OF9
