import SGPT.TestCurve.FGRelTCSaturation

/-!
# The chart condition for the filtration of a test configuration

See [BHJ17, Prop. 2.15]. For a test configuration `(𝓧, 𝓛)` with weight sections
`ξ_i ∈ H⁰(𝓧, 𝓛^r)` (`ξ_i` extends `t^{-w_i} q^* y_i`), the *weight chart condition*
(`WeightChartCondition`) says that for every weight vector `σ ∈ H⁰(𝓧, 𝓛^{rk})` (a section
extending `t^{-λ} q^* s`) and every `i`, some `ξ_i^D σ` is a linear combination of monomials
`t^a ξ^β` of the same weight (`Σ_l β_l w_l - a = D w_i + λ`) and degree (`|β| = D + k`). For the
equivariant closed embedding `(ξ, π) : 𝓧 ↪ ℙᴺ × 𝔸¹` of an ample test configuration this is the
statement that the weight components of `Γ({ξ_i ≠ 0}, 𝒪_𝓧)` are spanned by the weight-homogeneous
monomials in `t` and the `ξ_l / ξ_i` (the affine chart `{ξ_i ≠ 0}` is a closed subscheme of
`{X_i ≠ 0} × 𝔸¹ = 𝔸ᴺ × 𝔸¹`, `𝔾_m`-stably).

The condition gives the chart condition `H1` of `FGRel.mono_mem_polAlg_of_large`
(`chart_of_weightChartCondition`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.FGRel

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle Opposite
open SGPT.TestCurve.TestConfig SGPT.TestCurve.TestConfig.LaurentSecRing SGPT.TestCurve.TCEnc

namespace TestConfiguration'

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}
  (T : TestConfiguration f a)

theorem extends_zero (lam : ℤ) (m : ℕ) : T.Extends lam m 0 0 := by
  intro j
  simp only [TestConfiguration.epsCoeff]
  rw [atlasPowerGlobalCoefficients_zero, atlasPowerGlobalCoefficients_zero, map_zero, mul_zero]

theorem extends_add {lam : ℤ} {m : ℕ} {s s' : SectionSpace f L m}
    {σ σ' : SectionSpace T.structureMap T.line m} (h : T.Extends lam m s σ)
    (h' : T.Extends lam m s' σ') : T.Extends lam m (s + s') (σ + σ') := by
  intro j
  have e1 := h j
  have e2 := h' j
  simp only [TestConfiguration.epsCoeff] at e1 e2 ⊢
  erw [atlasPowerGlobalCoefficients_add, atlasPowerGlobalCoefficients_add]
  rw [e1, e2, map_add, mul_add]

theorem extends_smul {lam : ℤ} {m : ℕ} {s : SectionSpace f L m}
    {σ : SectionSpace T.structureMap T.line m} (h : T.Extends lam m s σ) (c : ℂ) :
    T.Extends lam m (c • s) (c • σ) := by
  intro j
  have e1 := h j
  simp only [TestConfiguration.epsCoeff] at e1 ⊢
  rw [SectionSpace.atlasPowerGlobalCoefficients_smul_const,
    SectionSpace.atlasPowerGlobalCoefficients_smul_const, e1, map_mul]
  have hc := pullFun_appTop T.coord T.coord_over' (a.opens j)
    ((Scheme.ΓSpecIso (.of ℂ)).inv c)
  erw [hc]
  simp only [schemeGlobalConstants]
  rw [mul_left_comm]
  rfl

/-- A section extends at most one `t^{-λ} q^* s`: `q^♯` is injective. -/
theorem extends_unique {lam : ℤ} {m : ℕ} {s s' : SectionSpace f L m}
    {σ : SectionSpace T.structureMap T.line m} (h : T.Extends lam m s σ)
    (h' : T.Extends lam m s' σ) : s = s' := by
  apply atlasPowerGlobalCoefficients_ext a m
  intro j
  have e := (h j).symm.trans (h' j)
  have hu : IsUnit ((T.tUnit j ^ (-lam)).val) := Units.isUnit _
  exact T.pullFun_injective _ (hu.mul_left_cancel e)

/-- The coordinate `t ∈ H⁰(𝓧, 𝒪)` extends `t · 1`. -/
theorem extends_tFun :
    T.Extends (-1) 0 (secOne f L) (show SectionSpace T.structureMap T.line 0 from tFun T.toLine) := by
  intro j
  simp only [TestConfiguration.epsCoeff, neg_neg, zpow_one]
  rw [atlasPowerGlobalCoefficients_degree_zero]
  simp only [secOne]
  erw [atlasPowerGlobalCoefficients_one, map_one, mul_one]
  rfl

end TestConfiguration'

/-! ### Monomials -/

theorem tElt_pow {X : Scheme} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}
    (n : ℕ) : (tElt f a) ^ n = mono (n : ℤ) 0 (secOne f L) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', ih, tElt_mul_mono]
    congr 1
    push_cast
    ring

section Monomials

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}
  (T : TestConfiguration f a)

/-- The section `t ∈ H⁰(𝓧, 𝒪)` in the section ring of `𝓛`. -/
def tSecRing : SecRing T.structureMap T.extAtlas :=
  SecRing.of 0 (show SectionSpace T.structureMap T.line 0 from tFun T.toLine)

variable {N r : ℕ} (w : Fin (N + 1) → ℤ) (y : Fin (N + 1) → SectionSpace f L r)
  (ξ : Fin (N + 1) → SectionSpace T.structureMap T.line r)

/-- The monomial `t^a ξ^β` in the section ring of `𝓛`. -/
def secMonomialξ (a' : ℕ) (β : Fin (N + 1) →₀ ℕ) : SecRing T.structureMap T.extAtlas :=
  tSecRing T ^ a' * β.prod fun l e => (SecRing.of r (ξ l) : SecRing T.structureMap T.extAtlas) ^ e

/-- The weight `Σ_l β_l w_l - a` of the monomial `t^a ξ^β`. -/
def monoWeight (a' : ℕ) (β : Fin (N + 1) →₀ ℕ) : ℤ := (β.sum fun l e => (e : ℤ) * w l) - a'

open TestConfiguration' in
/-- Monomials `t^a ξ^β` are weight vectors: they extend `t^{a - Σ β_l w_l} y^β`, and the
corresponding element of the Rees algebra is `t^a x^β`. -/
theorem exists_monomial_extends (hext : ∀ i, T.Extends (w i) r (y i) (ξ i)) (a' : ℕ)
    (β : Fin (N + 1) →₀ ℕ) :
    ∃ (M : ℕ) (s0 : SectionSpace f L M) (σ0 : SectionSpace T.structureMap T.line M),
      M = r * expSum β ∧ secMonomialξ T ξ a' β = SecRing.of M σ0 ∧
      T.Extends (monoWeight w a' β) M s0 σ0 ∧
      tElt f a ^ a' * coordEval a w y (MvPolynomial.monomial β 1) =
        mono (-monoWeight w a' β) M s0 := by
  classical
  -- the `ξ`-part
  have hβ : ∃ (M : ℕ) (s0 : SectionSpace f L M) (σ0 : SectionSpace T.structureMap T.line M),
      M = r * expSum β ∧
      (β.prod fun l e => (SecRing.of r (ξ l) : SecRing T.structureMap T.extAtlas) ^ e) =
        SecRing.of M σ0 ∧
      T.Extends (β.sum fun l e => (e : ℤ) * w l) M s0 σ0 ∧
      coordEval a w y (MvPolynomial.monomial β 1) =
        mono (-(β.sum fun l e => (e : ℤ) * w l)) M s0 := by
    induction β using Finsupp.induction with
    | zero =>
      refine ⟨0, secOne f L, secOne T.structureMap T.line, by simp [expSum], rfl, ?_, ?_⟩
      · simpa using extends_one T
      · rw [coordEval, MvPolynomial.aeval_monomial, Finsupp.prod_zero_index, map_one, mul_one,
          Finsupp.sum_zero_index, neg_zero]
        rfl
    | single_add i e β hi he ih =>
      obtain ⟨M, s0, σ0, hM, hprod, hext0, hev⟩ := ih
      refine ⟨r * e + M, SectionSpace.mul f a (r * e) M (secPow a (y i) e) s0,
        SectionSpace.mul T.structureMap T.extAtlas (r * e) M (secPow T.extAtlas (ξ i) e) σ0,
        ?_, ?_, ?_, ?_⟩
      · rw [hM, expSum, expSum, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
          Finsupp.sum_single_index rfl, mul_add]
      · rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
          Finsupp.prod_single_index (by rw [pow_zero]), hprod]
        have hpow : ∀ e : ℕ, (SecRing.of r (ξ i) : SecRing T.structureMap T.extAtlas) ^ e =
            SecRing.of (r * e) (secPow T.extAtlas (ξ i) e) := by
          intro e
          induction e with
          | zero => rfl
          | succ e ihe => rw [pow_succ, ihe, SecRing.of_mul_of]; rfl
        rw [hpow, SecRing.of_mul_of]
      · have h1 := extends_mul T (extends_secPow T (hext i) e) hext0
        rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; ring),
          Finsupp.sum_single_index (by simp)]
        exact h1
      · rw [← mul_one (1 : ℂ), ← MvPolynomial.monomial_mul, map_mul, hev, coordEval,
          MvPolynomial.aeval_monomial, map_one, one_mul,
          Finsupp.prod_single_index (by rw [pow_zero])]
        change coordElt a w y i ^ e * _ = _
        rw [coordElt_pow, mono_mul_mono, Finsupp.sum_add_index' (fun _ => by simp)
          (fun _ _ _ => by push_cast; ring), Finsupp.sum_single_index (by simp)]
        congr 1
        ring
  obtain ⟨M, s0, σ0, hM, hprod, hext0, hev⟩ := hβ
  -- the `t`-part
  have htpow : ∀ n : ℕ, ∃ τ : SectionSpace T.structureMap T.line 0,
      tSecRing T ^ n = SecRing.of 0 τ ∧ T.Extends (-(n : ℤ)) 0 (secOne f L) τ := by
    intro n
    induction n with
    | zero => exact ⟨secOne T.structureMap T.line, rfl, by simpa using extends_one T⟩
    | succ n ih =>
      obtain ⟨τ, hτ, hτe⟩ := ih
      refine ⟨SectionSpace.mul T.structureMap T.extAtlas 0 0 τ
        (show SectionSpace T.structureMap T.line 0 from tFun T.toLine), ?_, ?_⟩
      · rw [pow_succ, hτ, tSecRing, SecRing.of_mul_of]
      · have := extends_mul T hτe (extends_tFun T)
        have e1 : SectionSpace.mul f a 0 0 (secOne f L) (secOne f L) = secOne f L := by
          apply atlasPowerGlobalCoefficients_ext a 0
          intro j
          have h := SectionSpace.coefficients_mul (f := f) a 0 0 j (secOne f L) (secOne f L)
          simp only [secOne] at h ⊢
          erw [h, atlasPowerGlobalCoefficients_one, one_mul]
        rw [e1, show -(n : ℤ) + -1 = -((n + 1 : ℕ) : ℤ) by push_cast; ring] at this
        exact this
  obtain ⟨τ, hτ, hτe⟩ := htpow a'
  refine ⟨0 + M, SectionSpace.mul f a 0 M (secOne f L) s0,
    SectionSpace.mul T.structureMap T.extAtlas 0 M τ σ0, by rw [zero_add, hM], ?_, ?_, ?_⟩
  · rw [secMonomialξ, hτ, hprod, SecRing.of_mul_of]
  · have := extends_mul T hτe hext0
    rw [show -(a' : ℤ) + (β.sum fun l e => (e : ℤ) * w l) = monoWeight w a' β by
      rw [monoWeight]; ring] at this
    exact this
  · rw [hev, tElt]
    rw [← tElt, tElt_pow, mono_mul_mono]
    congr 1
    rw [monoWeight]
    ring

end Monomials

/-! ### The weight chart condition -/

section Chart

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}
  (T : TestConfiguration f a) {N r : ℕ} (w : Fin (N + 1) → ℤ)
  (ξ : Fin (N + 1) → SectionSpace T.structureMap T.line r)

/-- The monomials `t^a ξ^β` of degree `|β| = n` and weight `μ`. -/
def weightMonomials (n : ℕ) (μ : ℤ) : Set (SecRing T.structureMap T.extAtlas) :=
  {z | ∃ (a' : ℕ) (β : Fin (N + 1) →₀ ℕ), expSum β = n ∧ monoWeight w a' β = μ ∧
    z = secMonomialξ T ξ a' β}

/-- **The weight chart condition**: for every weight vector `σ ∈ H⁰(𝓧, 𝓛^{rk})` (extending
`t^{-λ} q^* s`) and every `i`, some `ξ_i^D σ` is a linear combination of the monomials `t^a ξ^β`
of degree `D + k` and weight `D w_i + λ` (the weight components of the coordinate ring of the
chart `{ξ_i ≠ 0}` are spanned by monomials in `t` and the `ξ_l / ξ_i`). -/
def WeightChartCondition : Prop :=
  ∀ (i : Fin (N + 1)) (k : ℕ) (lam : ℤ) (s : SectionSpace f L (r * k))
    (σ : SectionSpace T.structureMap T.line (r * k)), T.Extends lam (r * k) s σ →
    ∃ D : ℕ, (SecRing.of (r * D + r * k)
      (SectionSpace.mul T.structureMap T.extAtlas (r * D) (r * k) (secPow T.extAtlas (ξ i) D) σ) :
        SecRing T.structureMap T.extAtlas) ∈
      Submodule.span ℂ (weightMonomials T w ξ (D + k) ((D : ℤ) * w i + lam))

open TestConfiguration' in
/-- **The chart condition `H1`** for the filtration of a test configuration with weight sections
satisfying the weight chart condition. -/
theorem chart_of_weightChartCondition (y : Fin (N + 1) → SectionSpace f L r) (hext : ∀ i, T.Extends (w i) r (y i) (ξ i))
    (hW : WeightChartCondition T w ξ) (k : ℕ) (j : ℤ) (s : SectionSpace f L (r * k))
    (hs : s ∈ T.piece (-j) (r * k)) :
    ∃ D : ℕ, ∀ i, coordElt a w y i ^ D * mono j (r * k) s ∈ polAlg a w y := by
  classical
  obtain ⟨σ, hσ⟩ := hs
  have hD : ∀ i, ∃ D : ℕ, coordElt a w y i ^ D * mono j (r * k) s ∈ polAlg a w y := by
    intro i
    obtain ⟨D, hD⟩ := hW i k (-j) s σ hσ
    refine ⟨D, ?_⟩
    set M := r * D + r * k
    set μ : ℤ := (D : ℤ) * w i + -j
    -- every element of the span is the degree-`M` part of an extension of some `t^{-μ} s'`
    have key : ∀ z ∈ Submodule.span ℂ (weightMonomials T w ξ (D + k) μ),
        ∃ s' : SectionSpace f L M, T.Extends μ M s' (SecRing.comp M z) ∧
          mono (-μ) M s' ∈ polAlg a w y := by
      intro z hz
      refine Submodule.span_induction (p := fun z _ => ∃ s' : SectionSpace f L M,
        T.Extends μ M s' (SecRing.comp M z) ∧ mono (-μ) M s' ∈ polAlg a w y) ?_ ?_ ?_ ?_ hz
      · rintro _ ⟨a', β, hβ, hwt, rfl⟩
        obtain ⟨M', s0, σ0, hM', hz, hext0, hev⟩ := exists_monomial_extends T w y ξ hext a' β
        have hMM : M' = M := by rw [hM', hβ]; ring
        subst hMM
        refine ⟨s0, ?_, ?_⟩
        · rw [hz, SecRing.comp_of_same, ← hwt]
          exact hext0
        · rw [← hwt, ← hev]
          exact mul_mem (pow_mem (tElt_mem_polAlg a w y) _) (coordEval_mem_polAlg a w y _)
      · exact ⟨0, by rw [SecRing.comp_zero]; exact extends_zero T μ M, by
          rw [mono_zero]; exact zero_mem _⟩
      · rintro z z' - - ⟨s', h1, h2⟩ ⟨s'', h1', h2'⟩
        exact ⟨s' + s'', by rw [SecRing.comp_add]; exact extends_add T h1 h1', by
          rw [mono_add]; exact add_mem h2 h2'⟩
      · rintro c z - ⟨s', h1, h2⟩
        exact ⟨c • s', by rw [SecRing.comp_smul]; exact extends_smul T h1 c, by
          rw [mono_smul]; exact Subalgebra.smul_mem _ h2 c⟩
    obtain ⟨s', hs', hmem⟩ := key _ hD
    rw [SecRing.comp_of_same] at hs'
    have hξσ := extends_mul T (extends_secPow T (hext i) D) hσ
    have heq := extends_unique T hξσ hs'
    rw [coordElt_pow, mono_mul_mono, heq]
    convert hmem using 2
    ring
  choose D hD using hD
  refine ⟨∑ i, D i, fun i => ?_⟩
  have hle : D i ≤ ∑ i, D i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [show ∑ i, D i = (∑ i, D i - D i) + D i by omega, pow_add, mul_assoc]
  exact mul_mem (pow_mem (coordElt_mem_polAlg a w y i) _) (hD i)

end Chart

end SGPT.TestCurve.FGRel
