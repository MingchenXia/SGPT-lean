import SGPT.NAPotential.BerkovichIdealValue
import SGPT.Okounkov.SchemeOpenRegularFunctions

/-! # The analytification `φ^An` of a quasi-plurisubharmonic function

Source `def:NApotential:L975` (`chapter_NApotential.tex`, Section *The transcendental setting*):
for `φ ∈ PSH(X, θ)` on the connected projective manifold `X`,

`φ^An(v) := -v(φ) = -lim_{k → ∞} k⁻¹ v(𝓘(kφ)) ∈ [-∞, 0]`,   `v ∈ X^An`,

where `𝓘(kφ)` is the multiplier ideal sheaf; *by `thm:multipsubadd` and Fekete's lemma the limit
exists*, and `φ^An(v) = inf_k -2^{-k} v(𝓘(2^k φ))` (`eq:varphiAnalt`).

## Formal setting

`X` is a scheme smooth of relative dimension `n` over `ℂ` with a closed projective embedding `E`;
its complex points `SchemeComplexPoint f` form the complex manifold `X(ℂ)` of the workspace
(`SGPT.Okounkov.schemeAnalyticTNChartedSpace`), on which the multiplier ideals `𝓘(kφ)`
(`SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves.multiplierIdeal`) live.  The value
`v(𝓘(kφ))` of `eq:va` needs the *algebraic* coherent ideal sheaf corresponding to the analytic
coherent ideal `𝓘(kφ)` (Serre's GAGA).  We use its canonical algebraic model
`algebraization I`: the largest quasi-coherent ideal sheaf of `X` all of whose sections have
analytic germs in `I` (Mathlib's `IdealSheafData.ofIdeals`).  When `I` is the analytification of
an algebraic coherent ideal sheaf `𝔞` (always the case for coherent `I` on projective `X`, by
GAGA), this is `𝔞` (faithful flatness of `𝒪_{X,x} → 𝒪^an_{X,x}`); neither fact is formalized here.

## Main results

* `superadditive_tendsto_iSup` (Fekete's lemma in `[0, ∞]`) and
  `superadditive_iSup_eq_iSup_dyadic`.
* `algebraization`, `analytificationIdeal` and the (unproved) statement `SerreGAGAIdeals` of
  the GAGA correspondence they should satisfy.
* `BerkovichPoint.multiplierIdealVal v φ k = v(𝓘(kφ))`,
  `BerkovichPoint.potentialVal v φ = v(φ)`, `potentialAn φ v = φ^An(v) ∈ [-∞, 0]`.
* `potentialAn_congr`: `φ^An` only depends on the multiplier ideals `𝓘(kφ)`, `k ∈ ℕ`.
* `tendsto_potentialVal`, `potentialVal_eq_iSup`, `potentialVal_eq_iSup_dyadic`: the limit exists,
  equals `sup_k k⁻¹ v(𝓘(kφ))` and `sup_k 2^{-k} v(𝓘(2^k φ))` (i.e. `eq:varphiAnalt`), *provided*
  the algebraized multiplier ideals are submultiplicative
  (`AlgebraizedSubmultiplicative`): `alg 𝓘((k+l)φ) ⊆ alg 𝓘(kφ) · alg 𝓘(lφ)`.  For psh `φ` this is
  the subadditivity theorem `thm:multipsubadd` (verified analytically:
  `SGPT.PSH.ManifoldPSH.multiplierIdeal_sum_le_mul`) transported through GAGA; the transport
  (`alg(I J) = alg(I) alg(J)` for coherent analytic ideals) is the missing ingredient.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.Berkovich

open Filter Topology
open scoped ENNReal

/-! ### Fekete's lemma in `[0, ∞]` -/

/-- `q a(m) ≤ a(q m)` for a superadditive `a`. -/
theorem superadditive_natCast_mul_le {a : ℕ → ℝ≥0∞} (h : ∀ k l, a k + a l ≤ a (k + l))
    (m q : ℕ) : (q : ℝ≥0∞) * a m ≤ a (q * m) := by
  induction q with
  | zero => simp
  | succ q ih =>
    calc ((q + 1 : ℕ) : ℝ≥0∞) * a m = (q : ℝ≥0∞) * a m + a m := by push_cast; ring
      _ ≤ a (q * m) + a m := add_le_add ih le_rfl
      _ ≤ a (q * m + m) := h _ _
      _ = a ((q + 1) * m) := by ring_nf

/-- Fekete's lemma in `[0, ∞]`: for a superadditive sequence, `a k / k → sup_{k ≥ 1} a k / k`. -/
theorem superadditive_tendsto_iSup {a : ℕ → ℝ≥0∞} (h : ∀ k l, a k + a l ≤ a (k + l)) :
    Tendsto (fun k : ℕ => a k / k) atTop (𝓝 (⨆ k : ℕ, ⨆ (_ : 0 < k), a k / k)) := by
  set S := ⨆ k : ℕ, ⨆ (_ : 0 < k), a k / k
  rw [tendsto_order]
  constructor
  · intro b hb
    obtain ⟨m, hbm⟩ := lt_iSup_iff.mp hb
    obtain ⟨hm, hbm⟩ := lt_iSup_iff.mp hbm
    by_cases hinf : a m = ⊤
    · filter_upwards [eventually_ge_atTop m] with k hk
      have : a k = ⊤ := by
        obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hk
        exact top_le_iff.mp (le_trans (by rw [hinf]; exact le_add_right le_rfl) (h m l))
      rw [this, ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top k)]
      exact lt_of_lt_of_le hbm le_top
    · have hb_top : b ≠ ⊤ := ne_top_of_lt hbm
      set A := (a m).toReal
      have hA : a m = ENNReal.ofReal A := (ENNReal.ofReal_toReal hinf).symm
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm
      have hbR : b.toReal < A / m := by
        have h1 : b < ENNReal.ofReal (A / m) := by
          rw [ENNReal.ofReal_div_of_pos hmR, ← hA, ENNReal.ofReal_natCast]
          exact hbm
        exact (ENNReal.toReal_lt_toReal hb_top ENNReal.ofReal_ne_top).mpr h1 |>.trans_le
          (by rw [ENNReal.toReal_ofReal (div_nonneg ENNReal.toReal_nonneg hmR.le)])
      have hlim : Tendsto (fun k : ℕ => A / m * (1 - m / k)) atTop (𝓝 (A / m)) := by
        have : Tendsto (fun k : ℕ => (m : ℝ) / k) atTop (𝓝 0) :=
          tendsto_const_div_atTop_nhds_zero_nat (m : ℝ)
        simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub this).const_mul (A / m)
      filter_upwards [hlim.eventually (lt_mem_nhds hbR), eventually_ge_atTop m] with k hk hkm
      have hk0 : 0 < k := lt_of_lt_of_le hm hkm
      set q := k / m
      have hq : (q : ℝ≥0∞) * a m ≤ a k := by
        have h1 := superadditive_natCast_mul_le h m q
        have h2 : a (q * m) + a (k % m) ≤ a k := by
          have := h (q * m) (k % m)
          have e : q * m + k % m = k := by rw [mul_comm]; exact Nat.div_add_mod k m
          rwa [e] at this
        exact le_trans h1 (le_trans le_self_add h2)
      have hqR : ((k : ℝ) - m) / m ≤ q := by
        rw [div_le_iff₀ hmR]
        have : k < (q + 1) * m := by
          calc k < k / m * m + m := Nat.lt_div_mul_add hm
            _ = (q + 1) * m := by ring
        have : (k : ℝ) < (q + 1) * m := by exact_mod_cast this
        linarith
      have hlow : ENNReal.ofReal (A / m * (1 - m / k)) ≤ a k / k := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hk0.ne'))
          (Or.inl (ENNReal.natCast_ne_top k))]
        calc ENNReal.ofReal (A / m * (1 - m / k)) * k
            = ENNReal.ofReal (((k : ℝ) - m) / m * A) := by
              rw [← ENNReal.ofReal_natCast k, ← ENNReal.ofReal_mul']
              · congr 1
                field_simp
              · exact Nat.cast_nonneg k
          _ ≤ ENNReal.ofReal (q * A) := by
              apply ENNReal.ofReal_le_ofReal
              exact mul_le_mul_of_nonneg_right hqR ENNReal.toReal_nonneg
          _ = (q : ℝ≥0∞) * a m := by
              rw [ENNReal.ofReal_mul (Nat.cast_nonneg q), ENNReal.ofReal_natCast, ← hA]
          _ ≤ a k := hq
      calc b = ENNReal.ofReal b.toReal := (ENNReal.ofReal_toReal hb_top).symm
        _ < ENNReal.ofReal (A / m * (1 - m / k)) := by
            rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg]
            exact hk
        _ ≤ a k / k := hlow
  · intro b hb
    filter_upwards [eventually_gt_atTop 0] with k hk
    exact lt_of_le_of_lt (le_iSup₂_of_le k hk le_rfl) hb

/-- For a superadditive sequence the dyadic quotients `a(2^j)/2^j` increase. -/
theorem superadditive_dyadic_monotone {a : ℕ → ℝ≥0∞} (h : ∀ k l, a k + a l ≤ a (k + l)) :
    Monotone (fun j : ℕ => a (2 ^ j) / (2 ^ j : ℕ)) := by
  apply monotone_nat_of_le_succ
  intro j
  have h2 : (2 : ℝ≥0∞) * a (2 ^ j) ≤ a (2 ^ (j + 1)) := by
    have := superadditive_natCast_mul_le h (2 ^ j) 2
    rwa [pow_succ, mul_comm (2 ^ j) 2]
  have hpos : ((2 ^ j : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
  calc a (2 ^ j) / (2 ^ j : ℕ) = (2 * a (2 ^ j)) / (2 ^ (j + 1) : ℕ) := by
        rw [pow_succ, Nat.cast_mul, mul_comm ((2 ^ j : ℕ) : ℝ≥0∞), Nat.cast_ofNat,
          ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]
    _ ≤ a (2 ^ (j + 1)) / (2 ^ (j + 1) : ℕ) := ENNReal.div_le_div_right h2 _

/-- For a superadditive sequence, `sup_{k ≥ 1} a k / k = sup_j a(2^j)/2^j`. -/
theorem superadditive_iSup_eq_iSup_dyadic {a : ℕ → ℝ≥0∞} (h : ∀ k l, a k + a l ≤ a (k + l)) :
    (⨆ k : ℕ, ⨆ (_ : 0 < k), a k / k) = ⨆ j : ℕ, a (2 ^ j) / (2 ^ j : ℕ) := by
  have h1 := (superadditive_tendsto_iSup h).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2))
  have h2 := tendsto_atTop_iSup (superadditive_dyadic_monotone h)
  exact tendsto_nhds_unique h1 h2

/-! ### Algebraization of analytic ideal sheaves and `φ^An` -/

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f)

local instance berkovichAnPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance berkovichAnPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

/-- The regular functions on an affine open `U` all of whose analytic germs at the complex points
of `U` lie in the analytic ideal `I`. -/
def algebraicSections (I : GermIdeal n (SchemeComplexPoint f)) (U : X.affineOpens) :
    Set Γ(X, U) :=
  {r | ∀ p : SchemeComplexPoint f, schemeComplexPointImage f p ∈ (U : X.Opens) →
    I.mem p (schemeOpenRegularFunction f n E U r)}

/-- The algebraic model of an analytic ideal sheaf `I` on `X(ℂ)`: the largest quasi-coherent ideal
sheaf of `X` whose sections have all their analytic germs in `I`. -/
def algebraization (I : GermIdeal n (SchemeComplexPoint f)) : X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals fun U => Ideal.span (algebraicSections f n E I U)

theorem algebraization_ideal_le (I : GermIdeal n (SchemeComplexPoint f)) (U : X.affineOpens) :
    (algebraization f n E I).ideal U ≤ Ideal.span (algebraicSections f n E I U) :=
  Scheme.IdealSheafData.ideal_ofIdeals_le _ U

theorem algebraization_mono {I J : GermIdeal n (SchemeComplexPoint f)} (h : I.Le J) :
    algebraization f n E I ≤ algebraization f n E J := by
  apply Scheme.IdealSheafData.ofIdeals_mono
  intro U
  apply Ideal.span_mono
  intro r hr p hp
  exact h p _ (hr p hp)

/-- The analytification `𝔞^an` of an algebraic ideal sheaf: the germs that are holomorphic
combinations of the analytic germs of sections of `𝔞` over affine neighbourhoods. -/
def analytificationIdeal (𝔞 : X.IdealSheafData) : GermIdeal n (SchemeComplexPoint f) where
  mem p := IsInSpanAt (n := n) (fun s => ∃ (U : X.affineOpens)
    (_ : schemeComplexPointImage f p ∈ (U : X.Opens)) (r : Γ(X, U)), r ∈ 𝔞.ideal U ∧
      s = schemeOpenRegularFunction f n E U r) p

/-- Serre's GAGA for ideal sheaves on the projective `X`, in the two forms used by the source:
every coherent analytic ideal sheaf `I` on `X(ℂ)` is the analytification of its algebraic model,
and an algebraic ideal sheaf is recovered from its analytification.  This is the missing
ingredient behind `def:NApotential:L975` (it is not proved here). -/
def SerreGAGAIdeals : Prop :=
  (∀ I : GermIdeal n (SchemeComplexPoint f), I.IsCoherent →
      analytificationIdeal f n E (algebraization f n E I) = I) ∧
    ∀ 𝔞 : X.IdealSheafData, algebraization f n E (analytificationIdeal f n E 𝔞) = 𝔞

variable {f} [IsProper f]

namespace BerkovichPoint

/-- `v(𝓘(kφ))` (`eq:va` for the algebraic model of the multiplier ideal `𝓘(kφ)`). -/
def multiplierIdealVal (v : BerkovichPoint f) (φ : SchemeComplexPoint f → EReal) (k : ℕ) :
    ℝ≥0∞ :=
  v.idealVal (algebraization f n E (multiplierIdeal (n := n) (k : ℝ) φ))

/-- `v(φ) := lim_k k⁻¹ v(𝓘(kφ)) ∈ [0, ∞]`. -/
def potentialVal (v : BerkovichPoint f) (φ : SchemeComplexPoint f → EReal) : ℝ≥0∞ :=
  limUnder atTop fun k : ℕ => v.multiplierIdealVal n E φ k / k

end BerkovichPoint

/-- Source `def:NApotential:L975`: the analytification `φ^An : X^An → [-∞, 0]`,
`φ^An(v) = -v(φ) = -lim_k k⁻¹ v(𝓘(kφ))`. -/
def potentialAn (φ : SchemeComplexPoint f → EReal) (v : BerkovichPoint f) : EReal :=
  -((v.potentialVal n E φ : ℝ≥0∞) : EReal)

theorem potentialAn_nonpos (φ : SchemeComplexPoint f → EReal) (v : BerkovichPoint f) :
    potentialAn n E φ v ≤ 0 := by
  unfold potentialAn
  rw [EReal.neg_le, neg_zero]
  exact EReal.coe_ennreal_nonneg _

/-- `φ^An` only depends on the multiplier ideals `𝓘(kφ)`, `k ∈ ℕ` (so `𝓘`-equivalent potentials
have the same analytification). -/
theorem potentialAn_congr {φ ψ : SchemeComplexPoint f → EReal}
    (h : ∀ k : ℕ, multiplierIdeal (n := n) (k : ℝ) φ = multiplierIdeal (n := n) (k : ℝ) ψ) :
    potentialAn n E φ = potentialAn n E ψ := by
  funext v
  unfold potentialAn BerkovichPoint.potentialVal BerkovichPoint.multiplierIdealVal
  simp_rw [h]

/-- The algebraized multiplier ideals of `φ` are submultiplicative:
`alg 𝓘((k+l)φ) ⊆ alg 𝓘(kφ) · alg 𝓘(lφ)` (the algebraic form of `thm:multipsubadd`). -/
def AlgebraizedSubmultiplicative (φ : SchemeComplexPoint f → EReal) : Prop :=
  ∀ k l : ℕ, algebraization f n E (multiplierIdeal (n := n) ((k + l : ℕ) : ℝ) φ) ≤
    algebraization f n E (multiplierIdeal (n := n) (k : ℝ) φ) *
      algebraization f n E (multiplierIdeal (n := n) (l : ℝ) φ)

variable [IsLocallyNoetherian X]

namespace BerkovichPoint

theorem multiplierIdealVal_superadditive {φ : SchemeComplexPoint f → EReal}
    (hφ : AlgebraizedSubmultiplicative n E φ) (v : BerkovichPoint f) (k l : ℕ) :
    v.multiplierIdealVal n E φ k + v.multiplierIdealVal n E φ l ≤
      v.multiplierIdealVal n E φ (k + l) := by
  unfold multiplierIdealVal
  rw [← v.idealVal_mul]
  exact v.idealVal_antitone (hφ k l)

/-- `def:NApotential:L975`, existence of the limit (Fekete), under
`AlgebraizedSubmultiplicative`: `k⁻¹ v(𝓘(kφ)) → sup_{k ≥ 1} k⁻¹ v(𝓘(kφ))`. -/
theorem tendsto_potentialVal {φ : SchemeComplexPoint f → EReal}
    (hφ : AlgebraizedSubmultiplicative n E φ) (v : BerkovichPoint f) :
    Tendsto (fun k : ℕ => v.multiplierIdealVal n E φ k / k) atTop (𝓝 (v.potentialVal n E φ)) := by
  have h := superadditive_tendsto_iSup (v.multiplierIdealVal_superadditive n E hφ)
  rwa [potentialVal, h.limUnder_eq]

theorem potentialVal_eq_iSup {φ : SchemeComplexPoint f → EReal}
    (hφ : AlgebraizedSubmultiplicative n E φ) (v : BerkovichPoint f) :
    v.potentialVal n E φ = ⨆ k : ℕ, ⨆ (_ : 0 < k), v.multiplierIdealVal n E φ k / k :=
  (superadditive_tendsto_iSup (v.multiplierIdealVal_superadditive n E hφ)).limUnder_eq

/-- `eq:varphiAnalt` (under `AlgebraizedSubmultiplicative`):
`v(φ) = sup_j 2^{-j} v(𝓘(2^j φ))`, i.e. `φ^An(v) = inf_j -2^{-j} v(𝓘(2^j φ))`. -/
theorem potentialVal_eq_iSup_dyadic {φ : SchemeComplexPoint f → EReal}
    (hφ : AlgebraizedSubmultiplicative n E φ) (v : BerkovichPoint f) :
    v.potentialVal n E φ = ⨆ j : ℕ, v.multiplierIdealVal n E φ (2 ^ j) / (2 ^ j : ℕ) := by
  rw [potentialVal_eq_iSup n E hφ,
    superadditive_iSup_eq_iSup_dyadic (v.multiplierIdealVal_superadditive n E hφ)]

end BerkovichPoint

end SGPT.NAPotential.Berkovich

end
