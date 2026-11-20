import SGPT.TestCurve.SkodaIncOpenness

/-!
# The Skoda inclusion for finitely generated filtrations from Skoda's global division theorem

Source `rmk:PhongSturm` (chapter *Test curves*), through `SkodaInclusionIdeal`: the Skoda-division
part of [RWN14, Theorem 7.10] used in [RWN14, Proposition 7.11]. For a normalized finitely
generated `ℤ`-filtration `𝓕` of `R(X, L)` (the encoding of an ample test configuration,
[BHJ17, Prop. 2.15]) and `τ' < τ < τ(𝓕)`,

`H⁰(X, L^k ⊗ 𝓘(kψ_τ)) ⊆ 𝓕^{kτ'}_k`  for `k ≫ 0`,

`ψ_τ` the obstacle of `ex:RWN`. This file reduces this inclusion to Skoda's `L²` division theorem
on `X` (`GlobalSkodaDivision`, a statement: Skoda [Sko72b]; Demailly, *Analytic methods in
algebraic geometry*, Theorems 12.8 and 12.12) and the global generation of `L^e`, `e ≫ 0`.

## The route ([RWN14, §7])

Let `τ'' = (τ' + τ)/2`. For `d` large, `W = 𝓕^{dτ''}_d`, spanned by `w₁, …, w_r`:

1. `ψ_τ` is dominated by the analytic singularities of `W`: `𝓘(cψ_τ) ⊆ 𝓘(c d⁻¹ log |w|²)` for
   every `c > 0` (`SkodaIncComparison`: finite generation and a rounding of exponents, with
   constants depending on the level; `SkodaIncOpenness`: strong openness for increasing
   sequences removes the dependence on the level).
2. Hence `H⁰(X, L^k ⊗ 𝓘(kψ_τ)) ⊆ H⁰(X, L^k ⊗ 𝓘(M log |w|²))` for `M = ⌊(k - c₀)/d⌋`.
3. Skoda's division, iterated `M - n - 1` times (`mem_piece_of_globalSkodaDivision`):
   `H⁰(X, L^k ⊗ 𝓘(M log |w|²)) ⊆ W^{M-n-1} · H⁰(X, L^{k - (M-n-1)d}) ⊆ 𝓕^{(M-n-1)⌈dτ''⌉ - C(k - (M-n-1)d)}_k`.
4. The weight is `≥ kτ'' - O(1) ≥ kτ'` for `k ≫ 0`.

## Main results

* `GlobalSkodaDivision`: Skoda's division theorem for sections of `L^k` on `X` (statement).
* **`skodaInclusionIdeal_of_globalSkodaDivision`**: `SkodaInclusionIdeal 𝓕` for every normalized
  finitely generated `ℤ`-filtration, from `GlobalSkodaDivision` and the global generation of
  `L^e`, `e ≫ 0`.
* `exists_globalGeneration_of_pointExtension`: the global generation from the `L²` point
  extension; `skodaInclusionIdeal_of_sectionsAlgebraic_of_globalSkodaDivision`: from GAGA for
  `H⁰(X, L^k)` and `GlobalSkodaDivision`, for a positively curved metric.
* `rwnSkodaClause_of_sectionsAlgebraic_of_globalSkodaDivision`: [RWN14, Proposition 7.11],
  `P_θ[ψ_τ] = ψ_τ`, for the filtrations of ample test configurations.
* **`phongSturmRemark_of_sectionsAlgebraic_of_globalSkodaDivision`**: `rmk:PhongSturm` for
  `μ = (dd^c φ)ⁿ` from GAGA for `H⁰(X, L^k)` (`k ≫ 0`) and `GlobalSkodaDivision`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.SkodaInc

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set SGPT.Okounkov SGPT.LineBundle
open SGPT.TestCurve.TestConfig SGPT.TestCurve.SkodaRWN MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.NAPotential.GAGAMult
open scoped Topology

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  {E : ClosedProjectiveEmbedding f}

local instance skodaIncMainTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance skodaIncMainCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance skodaIncMainManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
local instance skodaIncMainMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance skodaIncMainBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

variable {L : X.Modules} {a : LineBundleAtlas L}

/-- **Skoda's division theorem on `X`** (statement; one division step). Let `h` be positively
curved (`c₁(L, h)` Kähler). For sections `w₁, …, w_r ∈ H⁰(X, L^d)`, `d > 0`, there is `c₀` such
that for every integer `M ≥ n + 1` (`n = dim X`) and every `k ≥ c₀ + M d`, every section
`σ ∈ H⁰(X, L^{d+k})` lying in the multiplier ideal `𝓘((M + 1) log |w|²)` (i.e.
`|σ|² |w|^{-2(M+1)}` is locally integrable) is `σ = ∑ⱼ wⱼ tⱼ` with `tⱼ ∈ H⁰(X, L^k)` in
`𝓘(M log |w|²)`.

This is Skoda's `L²` division theorem (Skoda [Sko72b]; Demailly, *Analytic methods in algebraic
geometry*, Theorem 12.8 with Theorem 12.12 for the generically surjective morphism
`w : 𝒪_X^r → L^d` on the compact Kähler manifold `X^{an}`): write
`L^{d+k} = K_X ⊗ L^d ⊗ (L^k ⊗ K_X^{-1})` and give `L^k ⊗ K_X^{-1}` the weight
`h^k ⊗ det ω · |w|^{-2(M - m - ε)}_{h^d}`, `m = min(n, r - 1) < M`; since
`dd^c log |w|²_{h^d} ≥ -d c₁(L, h)`, the curvature hypothesis
`iΘ - (m + ε) iΘ(L^d) ≥ (k - Md) c₁(L, h) + Ric(ω) ≥ 0` holds as soon as `k - Md ≥ c₀`, and the
`L²` conditions are the multiplier-ideal conditions on the compact `X^{an}`. The `tⱼ` are the
sections of the algebraic `L^k`, so the statement also contains GAGA for `H⁰(X, L^k)`
(`SchemeSectionsAlgebraic`). Not proved in this workspace. -/
def GlobalSkodaDivision (H : SchemeLineBundleMetric f n E L) (a : LineBundleAtlas L) : Prop :=
  (letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler) →
  ∀ (d r : ℕ), 0 < d → ∀ w : Fin r → SectionSpace f L d, ∃ c₀ : ℕ, ∀ M k : ℕ, n + 1 ≤ M →
    c₀ + M * d ≤ k → ∀ σ : SectionSpace f L (d + k),
      IsIdealSection f n E (multiplierIdeal (n := n) ((M + 1 : ℕ) : ℝ) (familyLog H a d w))
        (d + k) σ →
      ∃ t : Fin r → SectionSpace f L k,
        (∀ j, IsIdealSection f n E (multiplierIdeal (n := n) (M : ℝ) (familyLog H a d w)) k (t j)) ∧
          σ = ∑ j, SectionSpace.mul f a d k (w j) (t j)

/-- **Iterated division.** Under one-step Skoda division for `w` (with constant `c₀`), if the `wⱼ`
lie in `𝓕^{μ_W}_d` and `𝓕^{-Cm}_m = H⁰(X, L^m)`, then every `σ ∈ H⁰(X, L^k)` in
`𝓘((j + n + 1) log |w|²)`, `k ≥ c₀ + (j + n + 1) d`, lies in `𝓕^{j μ_W - C(k - jd)}_k`. -/
theorem mem_piece_of_globalSkodaDivision (H : SchemeLineBundleMetric f n E L)
    (G : SectionZFiltration f a) {CF : ℕ} (hCF : ∀ m : ℕ, 0 < m → G.piece (-((CF : ℤ) * m)) m = ⊤)
    {d r : ℕ} (hd : 0 < d) (w : Fin r → SectionSpace f L d) {μW : ℤ}
    (hwmem : ∀ j, w j ∈ G.piece μW d) {c₀ : ℕ}
    (hdiv : ∀ M k : ℕ, n + 1 ≤ M → c₀ + M * d ≤ k → ∀ σ : SectionSpace f L (d + k),
      IsIdealSection f n E (multiplierIdeal (n := n) ((M + 1 : ℕ) : ℝ) (familyLog H a d w))
        (d + k) σ →
      ∃ t : Fin r → SectionSpace f L k,
        (∀ j, IsIdealSection f n E (multiplierIdeal (n := n) (M : ℝ) (familyLog H a d w)) k (t j)) ∧
          σ = ∑ j, SectionSpace.mul f a d k (w j) (t j)) :
    ∀ j k : ℕ, c₀ + (j + n + 1) * d ≤ k → ∀ σ : SectionSpace f L k,
      IsIdealSection f n E
        (multiplierIdeal (n := n) ((j + n + 1 : ℕ) : ℝ) (familyLog H a d w)) k σ →
      σ ∈ G.piece ((j : ℤ) * μW - CF * ((k : ℤ) - j * d)) k := by
  intro j
  induction j with
  | zero =>
    intro k hk σ _
    have hk0 : 0 < k := lt_of_lt_of_le (by positivity) hk
    have hw : ((0 : ℕ) : ℤ) * μW - CF * ((k : ℤ) - ((0 : ℕ) : ℤ) * d) = -((CF : ℤ) * k) := by
      push_cast; ring
    rw [hw, hCF k hk0]
    exact Submodule.mem_top
  | succ j ih =>
    intro k hk σ hσ
    have hsplit : (j + 1 + n + 1) * d = (j + n + 1) * d + d := by ring
    obtain ⟨k', rfl⟩ : ∃ k', k = d + k' := ⟨k - d, by omega⟩
    have hk' : c₀ + (j + n + 1) * d ≤ k' := by omega
    have hidx : j + 1 + n + 1 = (j + n + 1) + 1 := by ring
    rw [hidx] at hσ
    obtain ⟨t, ht, rfl⟩ := hdiv (j + n + 1) k' (by omega) hk' σ hσ
    have hmem : ∀ i, SectionSpace.mul f a d k' (w i) (t i) ∈
        G.piece (μW + ((j : ℤ) * μW - CF * ((k' : ℤ) - j * d))) (d + k') :=
      fun i => G.mul_mem _ _ _ _ _ _ (hwmem i) (ih k' hk' (t i) (ht i))
    have hw : (μW + ((j : ℤ) * μW - CF * ((k' : ℤ) - j * d))) =
        ((j + 1 : ℕ) : ℤ) * μW - CF * (((d + k' : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ) * d) := by
      push_cast; ring
    rw [← hw]
    exact Submodule.sum_mem _ fun i _ => hmem i

/-- Multiplication by a positive real is continuous on `EReal`. -/
theorem continuous_coe_mul_ereal {c : ℝ} (hc : c ≠ 0) :
    Continuous fun t : EReal => (c : EReal) * t :=
  continuous_iff_continuousAt.mpr fun t =>
    (EReal.continuousAt_mul (p := ((c : EReal), t)) (Or.inl (by simpa using hc))
      (Or.inl (by simpa using hc)) (Or.inl (EReal.coe_ne_bot c))
      (Or.inl (EReal.coe_ne_top c))).comp
      (continuousAt_const.prodMk continuousAt_id)

/-- The weight bound at the end of the iteration: if `jd ≤ k ≤ jd + c₀ + (n+2)d`,
`μ_W ≥ dτ''` and `k (τ'' - τ') ≥ (|τ''| + C)(c₀ + (n+2)d) + 1`, then
`⌈kτ'⌉ ≤ j μ_W - C(k - jd)`. -/
theorem ceil_le_iterated_weight {τ' τ'' : ℝ} {CF c₀ n d k j : ℕ} {μW : ℤ}
    (hμW : (d : ℝ) * τ'' ≤ μW) (hjd1 : (j : ℝ) * d ≤ k)
    (hjd2 : (k : ℝ) - (c₀ + (n + 2) * d) ≤ (j : ℝ) * d)
    (hk : (|τ''| + CF) * ((c₀ : ℝ) + (n + 2) * d) + 1 ≤ (k : ℝ) * (τ'' - τ')) :
    ⌈(k : ℝ) * τ'⌉ ≤ (j : ℤ) * μW - CF * ((k : ℤ) - j * d) := by
  rw [Int.ceil_le]
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hCF0 : (0 : ℝ) ≤ CF := Nat.cast_nonneg _
  have h1 : (j : ℝ) * (d * τ'') ≤ (j : ℝ) * (μW : ℝ) := mul_le_mul_of_nonneg_left hμW hj0
  have h2 : (k : ℝ) * τ'' - |τ''| * ((c₀ : ℝ) + (n + 2) * d) ≤ (j : ℝ) * (d * τ'') := by
    have habs : |((j : ℝ) * d - k) * τ''| ≤ ((c₀ : ℝ) + (n + 2) * d) * |τ''| := by
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      rw [abs_le]
      constructor <;> linarith
    have := neg_abs_le (((j : ℝ) * d - k) * τ'')
    nlinarith
  have hkjd : (k : ℝ) - (j : ℝ) * d ≤ (c₀ : ℝ) + (n + 2) * d := by linarith
  have h3 := mul_le_mul_of_nonneg_left hkjd hCF0
  push_cast
  nlinarith

variable [IsIntegral X]

/-- **The Skoda inclusion from one level and Skoda's division** (core of
`skodaInclusionIdeal_of_globalSkodaDivision`). Let `τ' < τ'' ` and `w₁, …, w_r ∈ 𝓕^{μ_W}_d`
(`μ_W ≥ dτ''`) with `𝓘(cψ_τ) ⊆ 𝓘(c d⁻¹ log |w|²)` for all `c > 0`, and assume one-step Skoda
division for `w`. Then `H⁰(X, L^k ⊗ 𝓘(kψ_τ)) ⊆ 𝓕^{kτ'}_k` for `k ≫ 0`. -/
theorem exists_mem_piece_of_iOrder (G : SectionZFiltration f a) (hG : G.IsFinitelyGenerated)
    (h0 : G.piece 0 0 = ⊤) (H : SchemeLineBundleMetric f n E L)
    {CF : ℕ} (hCF : ∀ m : ℕ, 0 < m → G.piece (-((CF : ℤ) * m)) m = ⊤)
    {τ' τ'' τ : ℝ} (hτ'' : τ' < τ'') {d r : ℕ} (hd : 0 < d) (w : Fin r → SectionSpace f L d)
    {μW : ℤ} (hμW : (d : ℝ) * τ'' ≤ μW) (hwmem : ∀ j, w j ∈ G.piece μW d)
    (hIO : letI := E.isSeparated; letI := E.quasiCompact;
      IOrderOnManifold (n := n) ((G.fgFiltration hG h0).obstacle H τ)
        fun x => (((d : ℝ)⁻¹ : ℝ) : EReal) * familyLog H a d w x)
    {c₀ : ℕ}
    (hdiv : ∀ M k : ℕ, n + 1 ≤ M → c₀ + M * d ≤ k → ∀ σ : SectionSpace f L (d + k),
      IsIdealSection f n E (multiplierIdeal (n := n) ((M + 1 : ℕ) : ℝ) (familyLog H a d w))
        (d + k) σ →
      ∃ t : Fin r → SectionSpace f L k,
        (∀ j, IsIdealSection f n E (multiplierIdeal (n := n) (M : ℝ) (familyLog H a d w)) k (t j)) ∧
          σ = ∑ j, SectionSpace.mul f a d k (w j) (t j)) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ σ : SectionSpace f L k,
      IsMultiplierSection f n E ((G.fgFiltration hG h0).obstacle H τ) k σ →
        σ ∈ (G.fgFiltration hG h0).piece ((k : ℝ) * τ') k := by
  have hiter := mem_piece_of_globalSkodaDivision H G hCF hd w hwmem hdiv
  have hgap : 0 < τ'' - τ' := by linarith
  refine ⟨max (c₀ + (n + 2) * d)
    ⌈((|τ''| + CF) * ((c₀ : ℝ) + (n + 2) * d) + 1) / (τ'' - τ')⌉₊, fun k hk σ hσ => ?_⟩
  have hk1 : c₀ + (n + 2) * d ≤ k := (le_max_left _ _).trans hk
  have hk2 : ((|τ''| + CF) * ((c₀ : ℝ) + (n + 2) * d) + 1) / (τ'' - τ') ≤ (k : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hk)
  rw [div_le_iff₀ hgap] at hk2
  -- `M = ⌊(k - c₀)/d⌋`
  obtain ⟨M, hM⟩ : ∃ M, M = (k - c₀) / d := ⟨_, rfl⟩
  have hMd : M * d ≤ k - c₀ := hM ▸ Nat.div_mul_le_self _ _
  have hMd' : k - c₀ < M * d + d := hM ▸ Nat.lt_div_mul_add hd
  have hMn : n + 2 ≤ M := by
    rw [hM, Nat.le_div_iff_mul_le hd]
    omega
  have hMk : M * d ≤ k := hMd.trans (Nat.sub_le _ _)
  have hσM := isIdealSection_familyLog_of_isMultiplierSection H hd w hIO
    (lt_of_lt_of_le (by omega) hMn) hMk σ hσ
  obtain ⟨j, hjM⟩ : ∃ j, j + n + 1 = M := ⟨M - (n + 1), by omega⟩
  have hσj : IsIdealSection f n E
      (multiplierIdeal (n := n) ((j + n + 1 : ℕ) : ℝ) (familyLog H a d w)) k σ := by
    rw [hjM]; exact hσM
  have hmem := hiter j k (by rw [hjM]; omega) σ hσj
  have hjd1 : (j : ℝ) * d ≤ k := by
    have h1 : j * d + (n + 1) * d = M * d := by rw [← hjM]; ring
    have : j * d ≤ k := by omega
    exact_mod_cast this
  have hjd2 : (k : ℝ) - (c₀ + (n + 2) * d) ≤ (j : ℝ) * d := by
    have : k ≤ j * d + (c₀ + (n + 2) * d) := by
      have h1 : j * d + (n + 1) * d = M * d := by rw [← hjM]; ring
      have h2 : (n + 2) * d = (n + 1) * d + d := by ring
      omega
    have : (k : ℝ) ≤ (j : ℝ) * d + (c₀ + (n + 2) * d) := by exact_mod_cast this
    linarith
  exact G.piece_anti (ceil_le_iterated_weight hμW hjd1 hjd2 hk2) k hmem

/-- **The Skoda inclusion from Skoda's division theorem** (`SkodaInclusionIdeal`, the
Skoda-division part of [RWN14, Theorem 7.10]). Let `𝓕` be a normalized finitely generated
`ℤ`-filtration of `R(X, L)` and `h` positively curved. If `L^e` is globally generated for
`e ≫ 0` and Skoda's division theorem `GlobalSkodaDivision` holds on `X`, then for
`τ' < τ < τ(𝓕)` and `k ≫ 0`, `H⁰(X, L^k ⊗ 𝓘(kψ_τ)) ⊆ 𝓕^{kτ'}_k`. -/
theorem skodaInclusionIdeal_of_globalSkodaDivision [Nonempty (SchemeComplexPoint f)]
    (G : SectionZFiltration f a) (hG : G.IsFinitelyGenerated) (h0 : G.piece 0 0 = ⊤)
    (H : SchemeLineBundleMetric f n E L)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hbpf : ∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e → ∀ p : SchemeComplexPoint f,
      ∃ σ : SectionSpace f L e, H.sectionNormSq a e σ p ≠ 0)
    (hSk : GlobalSkodaDivision H a) :
    SkodaInclusionIdeal (G.fgFiltration hG h0) H := by
  classical
  let := E.isSeparated
  let := E.quasiCompact
  intro τ' τ hτ' hτ
  obtain ⟨R⟩ := SectionZFiltration.exists_reesGenerators G hG h0
  obtain ⟨CF, -, hCFb⟩ := SectionZFiltration.IsFinitelyGenerated.linearlyBounded G hG h0
  have hCF : ∀ m : ℕ, 0 < m → G.piece (-((CF : ℤ) * m)) m = ⊤ := fun m hm => (hCFb m hm).2
  obtain ⟨e₁, he₁⟩ := hbpf
  obtain ⟨e₀, he₀def⟩ : ∃ e₀, e₀ = max e₁ 1 := ⟨_, rfl⟩
  have he₀ : 0 < e₀ := he₀def ▸ lt_of_lt_of_le one_pos (le_max_right _ _)
  have hbpf' : ∀ e : ℕ, e₀ ≤ e → ∀ p : SchemeComplexPoint f,
      ∃ σ : SectionSpace f L e, H.sectionNormSq a e σ p ≠ 0 :=
    fun e he => he₁ e ((he₀def ▸ le_max_left _ _).trans he)
  -- the auxiliary slope `τ''` and the degree `d`
  obtain ⟨τ'', hτ''def⟩ : ∃ τ'', τ'' = (τ' + τ) / 2 := ⟨_, rfl⟩
  have hgap : 0 < τ - τ'' := by rw [hτ''def]; linarith
  have hτ'τ'' : τ' < τ'' := by rw [hτ''def]; linarith
  obtain ⟨d, hde, hdQ⟩ : ∃ d : ℕ, e₀ ≤ d ∧ (e₀ : ℝ) * |τ| + ∑ i, |(R.wt i : ℝ)| +
      (CF : ℝ) * ((e₀ : ℝ) + ∑ i, (R.deg i : ℝ)) ≤ (d : ℝ) * (τ - τ'') := by
    refine ⟨max e₀ ⌈((e₀ : ℝ) * |τ| + ∑ i, |(R.wt i : ℝ)| +
      (CF : ℝ) * ((e₀ : ℝ) + ∑ i, (R.deg i : ℝ))) / (τ - τ'')⌉₊, le_max_left _ _, ?_⟩
    rw [← div_le_iff₀ hgap]
    exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  have hd0 : 0 < d := lt_of_lt_of_le he₀ hde
  -- the level `W = 𝓕^{dτ''}_d` and a basis `w`
  have := SectionSpace.finiteDimensional f E a d
  let W := G.piece ⌈(d : ℝ) * τ''⌉ d
  let bW := Module.finBasis ℂ W
  let w : Fin (Module.finrank ℂ W) → SectionSpace f L d := fun j => (bW j : SectionSpace f L d)
  have hwmem : ∀ j, w j ∈ W := fun j => (bW j).2
  have hwspan : ∀ t ∈ W, ∃ c : Fin (Module.finrank ℂ W) → ℂ, t = ∑ j, c j • w j := by
    intro t ht
    refine ⟨fun j => bW.repr ⟨t, ht⟩ j, ?_⟩
    have h := bW.sum_repr ⟨t, ht⟩
    have h' := congrArg (Subtype.val : W → SectionSpace f L d) h
    rw [Submodule.coe_sum] at h'
    simp only [Submodule.coe_smul] at h'
    exact h'.symm
  -- the multiplier ideals of the obstacle
  have hφc : Continuous fun x => (((d : ℝ)⁻¹ : ℝ) : EReal) * familyLog H a d w x :=
    (continuous_coe_mul_ereal (inv_ne_zero (Nat.cast_pos.mpr hd0).ne')).comp
      (continuous_familyLog H a d w)
  have hIO := iOrderOnManifold_obstacle (G.fgFiltration hG h0) H hτ hφc fun K hK =>
    normalizedPotential_le_familyLog H a G hG h0 R hCF he₀ hbpf' hde hdQ w hwspan hK
  -- Skoda's division
  obtain ⟨c₀, hdiv⟩ := hSk hK d _ hd0 w
  exact exists_mem_piece_of_iOrder G hG h0 H hCF hτ'τ'' hd0 w (Int.le_ceil _) hwmem hIO hdiv

omit [IsIntegral X] in
/-- **Global generation from the point extension**: for a positively curved metric, the `L²`
point extension (`SchemePointExtension`) gives a section of `L^e` not vanishing at any prescribed
point, for all `e ≫ 0`. -/
theorem exists_globalGeneration_of_pointExtension (H : SchemeLineBundleMetric f n E L)
    (μ : Measure (SchemeComplexPoint f))
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hPE : SchemePointExtension H a μ (curvatureKahlerBackground H a hK)) :
    ∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e → ∀ p : SchemeComplexPoint f,
      ∃ σ : SectionSpace f L e, H.sectionNormSq a e σ p ≠ 0 := by
  let := E.isSeparated
  let := E.quasiCompact
  have h0psh : IsThetaPshPotential (H.curvature a).val (fun _ => (0 : EReal)) :=
    (LocalPotentials.isThetaPshPotential_zero_iff (H.curvature a)).mpr
      (curvatureKahlerBackground H a hK).isSemipositive
  have hφpsh : IsThetaPshPotential
      (H.curvature a - (1 / 2 : ℝ) • (curvatureKahlerBackground H a hK).form).val
      (fun _ => (0 : EReal)) := by
    have h := PotentialMassComparison.isThetaPshPotential_smul h0psh
      (by norm_num : (0 : ℝ) < 1 - 1 / 2)
    have hform : H.curvature a - (1 / 2 : ℝ) • (curvatureKahlerBackground H a hK).form =
        (1 - 1 / 2 : ℝ) • H.curvature a := by
      change H.curvature a - (1 / 2 : ℝ) • H.curvature a = _
      rw [sub_smul, one_smul]
    rw [hform]
    simpa only [mul_zero] using h
  obtain ⟨k₀, C, -, hext⟩ := hPE (1 / 2) (by norm_num)
  refine ⟨k₀, fun e he p => ?_⟩
  obtain ⟨σ, hσ, -⟩ := hext e he (fun _ => 0) hφpsh p (by simp)
  exact ⟨σ, hσ⟩

/-- **The Skoda inclusion from GAGA and Skoda's division theorem**: for a positively curved
metric (`c₁(L, h)` Kähler), GAGA for `H⁰(X, L^k)` (`k ≫ 0`) and `GlobalSkodaDivision` give
`SkodaInclusionIdeal 𝓕` for every normalized finitely generated `ℤ`-filtration. -/
theorem skodaInclusionIdeal_of_sectionsAlgebraic_of_globalSkodaDivision
    [Nonempty (SchemeComplexPoint f)]
    (G : SectionZFiltration f a) (hG : G.IsFinitelyGenerated) (h0 : G.piece 0 0 = ⊤)
    (H : SchemeLineBundleMetric f n E L)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hgaga : letI := E.isSeparated; letI := E.quasiCompact;
      ∀ᶠ j in atTop, SchemeSectionsAlgebraic f n E a H j)
    (hSk : GlobalSkodaDivision H a) :
    SkodaInclusionIdeal (G.fgFiltration hG h0) H :=
  skodaInclusionIdeal_of_globalSkodaDivision G hG h0 H hK
    (exists_globalGeneration_of_pointExtension H (curvatureVolume H a hK) hK
      (schemePointExtension_of_sectionsAlgebraic H a (curvatureVolume H a hK)
        (isSmoothPositiveVolume_curvatureVolume H a hK) (curvatureKahlerBackground H a hK) hgaga))
    hSk

/-- **[RWN14, Proposition 7.11] for ample test configurations** (the claim of the footnote to
`ex:RWN`: `P_θ` is not needed when `L` is ample): for a positively curved metric, GAGA for
`H⁰(X, L^k)` (`k ≫ 0`) and `GlobalSkodaDivision` give `P_θ[ψ_τ] = ψ_τ` for `τ < τ(𝓕)`, for every
normalized finitely generated `ℤ`-filtration `𝓕`. -/
theorem rwnSkodaClause_of_sectionsAlgebraic_of_globalSkodaDivision
    [Nonempty (SchemeComplexPoint f)]
    (G : SectionZFiltration f a) (hG : G.IsFinitelyGenerated) (h0 : G.piece 0 0 = ⊤)
    (H : SchemeLineBundleMetric f n E L)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hgaga : letI := E.isSeparated; letI := E.quasiCompact;
      ∀ᶠ j in atTop, SchemeSectionsAlgebraic f n E a H j)
    (hSk : GlobalSkodaDivision H a) :
    RWNSkodaClause H (G.fgFiltration hG h0) :=
  rwnSkodaClause_of_sectionsAlgebraic_of_skodaInclusionIdeal _ H hK hgaga
    (skodaInclusionIdeal_of_sectionsAlgebraic_of_globalSkodaDivision G hG h0 H hK hgaga hSk)

/-- **`rmk:PhongSturm` from GAGA for `H⁰(X, L^k)` and Skoda's division theorem.** Let `L` be ample
on the smooth projective variety `X`, `h = e^{-φ}` a positively curved smooth metric on `L` and
`μ = (dd^c φ)ⁿ`. Assume GAGA for the sections of `L^k`, `k ≫ 0` (`SchemeSectionsAlgebraic`), and
Skoda's `L²` division theorem on `X` (`GlobalSkodaDivision`). Then for every ample test
configuration of `(X, L)` (normalized finitely generated `ℤ`-filtration `𝓕`), `Γ^{𝓕*}_t = Φ(t)`
for all `t > 0` and every choice of adapted orthonormal bases (`PhongSturmRemark`): the
geodesic ray of `ex:RWN` is the Phong–Sturm ray. -/
theorem phongSturmRemark_of_sectionsAlgebraic_of_globalSkodaDivision
    [Nonempty (SchemeComplexPoint f)] [CompactSpace (SchemeComplexPoint f)]
    (H : SchemeLineBundleMetric f n E L) (P : AmplePolarization f L)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hgaga : letI := E.isSeparated; letI := E.quasiCompact;
      ∀ᶠ j in atTop, SchemeSectionsAlgebraic f n E a H j)
    (hSk : GlobalSkodaDivision H a) :
    PhongSturmRemark H a (curvatureVolume H a hK) :=
  phongSturmRemark_of_sectionsAlgebraic_of_skodaInclusionIdeal H P hK hgaga fun G hG h0 =>
    skodaInclusionIdeal_of_sectionsAlgebraic_of_globalSkodaDivision G hG h0 H hK hgaga hSk

end SGPT.TestCurve.SkodaInc
