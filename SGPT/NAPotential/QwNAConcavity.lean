import SGPT.NAPotential.BerkovichPiecewiseLinear
import SGPT.GAGA.H0SSchemeGAGA
import SGPT.Foundations.Analysis.Pending.MultiplierSubadditivity
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularBasics
import SGPT.Foundations.Analysis.Pending.ZeroDimensionalQuasiPshMultiplierIdeals
import SGPT.Foundations.Analysis.Pending.PshConvexCone
import SGPT.Foundations.Analysis.Pending.DemaillyApproximationAnalyticType

/-!
# Concavity of `φ ↦ φ^An` and the analytification of a piecewise linear curve

Lane QW-NA, blueprint `claude-qw-na.tex`.  Source `def:piecewiselincurv`
(`chapter_NApotential.tex`, Section *The transcendental setting*): the analytification of a
piecewise linear curve `A` with nodes `τ_0 > ⋯ > τ_N` and potentials `A_i = A_{τ_i}` is

`A^An(v) := sup_{τ ≤ τ_0} (A_τ^An(v) + τ) = max_{i = 0, …, N} (A_{τ_i}^An(v) + τ_i)`.

The first expression is `PiecewiseLinearData.curveAn`; the inequality `≥` is `le_curveAn`.  The
second equality (the supremum is the maximum over the nodes) is proved here
(`PiecewiseLinearData.curveAn_eq_iSup`, `PiecewiseLinearData.exists_curveAn_eq`).  Its key input
is the **concavity of the analytification**: for `φ ∈ PSH(X, θ)`, `ψ ∈ PSH(X, θ')`, `c₁, c₂ > 0`
with `c₁ φ + c₂ ψ` quasi-psh,

`(c₁ φ + c₂ ψ)^An ≤ c₁ φ^An + c₂ ψ^An`   on `X^An`   (`potentialAn_smul_add_le`).

## Proof

* `multiplierIdeal_le_of_exponent_le`: `𝓘(dφ) ⊆ 𝓘(cφ)` for `0 < c ≤ d` and quasi-psh `φ`.
* `multiplierIdeal_smul_add_le_mul`: **subadditivity for independent weights**
  (Demailly–Ein–Lazarsfeld): `𝓘(c (c₁ φ + c₂ ψ)) ⊆ 𝓘(c c₁ φ) · 𝓘(c c₂ ψ)` for a `θ`-psh `φ` and a
  `θ'`-psh `ψ`.  In the chart at `x`, `Φ = φ + ρ₁` and `Ψ = ψ + ρ₂` are psh, the weight of the
  left side is comparable with that of `c c₁ Φ + c c₂ Ψ`, and the local theorem
  `MultiplierSubadditivityLocal.inGermSpan_mul_of_multiplierIntegrableAt` applies.
* `algebraization_multiplierIdeal_smul_add_le_mul`: the same for the algebraic models
  (`alg`), transported through GAGA (`SGPT.GAGA.H0S.multiplierIdealAlgebraic`,
  `analytificationIdeal_le_iff`).
* `potentialVal_smul_add_ge`: `c₁ v(φ) + c₂ v(ψ) ≤ v(c₁ φ + c₂ ψ)`.  With `j = ⌊c₁ k⌋`,
  `v(𝓘(k(c₁φ + c₂ψ))) ≥ v(𝓘(⌊c₁ k⌋ φ)) + v(𝓘(⌊c₂ k⌋ ψ))`; divide by `k` and let `k → ∞`
  (`SGPT.GAGA.H0S.tendsto_potentialVal`, `⌊c k⌋ / k → c`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.NAPotential.Berkovich

open Set Filter
open scoped Topology Manifold ENNReal
open MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending

/-! ### Multiplier ideals of positive combinations of two quasi-psh weights -/

section Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Multiplier ideals of a quasi-psh function decrease in the exponent:
`𝓘(dφ) ⊆ 𝓘(cφ)` for `0 < c ≤ d`. -/
theorem multiplierIdeal_le_of_exponent_le {φ : M → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    (multiplierIdeal (n := n) d φ).Le (multiplierIdeal (n := n) c φ) := by
  rintro x g ⟨hg, hint⟩
  refine ⟨hg, ?_⟩
  have hx : x ∈ (complexChartAt (n := n) x).val.source := mem_complexChartAt_source x
  exact multiplierIntegrableAt_of_exponent_le
    (hφ (complexChartAt (n := n) x) _ ((complexChartAt (n := n) x).val.map_source hx)) hc hcd hint

/-- `c (c₁ a + c₂ b) + (c c₁ r + c c₂ s) = c c₁ (a + r) + c c₂ (b + s)` in `[-∞, ∞]`, `c, c₁, c₂ ≥ 0`. -/
theorem ereal_smul_add_add_coe {c c₁ c₂ : ℝ} (hc : 0 ≤ c) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (a b : EReal) (r s : ℝ) :
    (c : EReal) * ((c₁ : EReal) * a + (c₂ : EReal) * b) + ((c * c₁ * r + c * c₂ * s : ℝ) : EReal) =
      ((c * c₁ : ℝ) : EReal) * (a + r) + ((c * c₂ : ℝ) : EReal) * (b + s) := by
  have h0 : ∀ x : ℝ, 0 ≤ x → (0 : EReal) ≤ (x : EReal) := fun x hx => EReal.coe_nonneg.mpr hx
  rw [EReal.left_distrib_of_nonneg_of_ne_top (h0 c hc) (EReal.coe_ne_top c),
    EReal.left_distrib_of_nonneg_of_ne_top (h0 _ (mul_nonneg hc hc₁)) (EReal.coe_ne_top _),
    EReal.left_distrib_of_nonneg_of_ne_top (h0 _ (mul_nonneg hc hc₂)) (EReal.coe_ne_top _),
    ← mul_assoc, ← mul_assoc, ← EReal.coe_mul, ← EReal.coe_mul, EReal.coe_add,
    ← EReal.coe_mul (c * c₁), ← EReal.coe_mul (c * c₂)]
  exact add_add_add_comm _ _ _ _

/-- **Subadditivity of multiplier ideals for independent weights** (Demailly–Ein–Lazarsfeld,
`thm:multipsubadd`): for a `θ`-psh `φ`, a `θ'`-psh `ψ` and `c, c₁, c₂ > 0`,
`𝓘(c (c₁ φ + c₂ ψ)) ⊆ 𝓘(c c₁ φ) · 𝓘(c c₂ ψ)`. -/
theorem multiplierIdeal_smul_add_le_mul {θ θ' : SmoothRealForm n M 2} {φ ψ : M → EReal}
    (hφ : IsThetaPshPotential θ φ) (hψ : IsThetaPshPotential θ' ψ)
    {c c₁ c₂ : ℝ} (hc : 0 < c) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    (multiplierIdeal (n := n) c (fun x => (c₁ : EReal) * φ x + (c₂ : EReal) * ψ x)).Le
      ((multiplierIdeal (n := n) (c * c₁) φ).mul (multiplierIdeal (n := n) (c * c₂) ψ)) := by
  have hcc₁ : 0 < c * c₁ := mul_pos hc hc₁
  have hcc₂ : 0 < c * c₂ := mul_pos hc hc₂
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- dimension zero: every holomorphic germ lies in every multiplier ideal
    subst hn
    have hqφ : IsGlobalQuasiPshPotential (n := 0) φ := ⟨hφ.1.quasiPlurisubharmonic, hφ.2⟩
    have hqψ : IsGlobalQuasiPshPotential (n := 0) ψ := ⟨hψ.1.quasiPlurisubharmonic, hψ.2⟩
    intro x g hg
    refine ⟨hg.1, 1, fun _ => g, fun _ _ => 1, fun _ => ?_,
      fun _ => holomorphicAt_const 1, Eventually.of_forall fun _ => by simp⟩
    refine ⟨g, fun _ => 1,
      (ZeroDimensionalQuasiPshMultiplierIdeals.mem_multiplierIdeal_iff_holomorphicAt
        hqφ hcc₁ x g).mpr hg.1,
      (ZeroDimensionalQuasiPshMultiplierIdeals.mem_multiplierIdeal_iff_holomorphicAt
        hqψ hcc₂ x _).mpr (holomorphicAt_const 1), ?_⟩
    funext y
    simp
  obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  intro x g hg
  set e : ComplexChart (d' + 1) M := complexChartAt (n := d' + 1) x with he
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  set z₀ : ComplexModel (d' + 1) := e.val x with hz₀
  have hz₀t : z₀ ∈ e.val.target := e.val.map_source hxs
  obtain ⟨W₁, ρ₁, hz₁, hρ₁, hp₁⟩ := hφ.1 e z₀ hz₀t
  obtain ⟨W₂, ρ₂, hz₂, hρ₂, hp₂⟩ := hψ.1 e z₀ hz₀t
  obtain ⟨hW₁o, -, hρ₁s, -⟩ := hρ₁
  obtain ⟨hW₂o, -, hρ₂s, -⟩ := hρ₂
  have hWo : IsOpen (W₁ ∩ W₂) := hW₁o.inter hW₂o
  set Φ : ComplexModel (d' + 1) → EReal := fun w => chartFunction φ e w + (ρ₁ w : EReal) with hΦ
  set Ψ : ComplexModel (d' + 1) → EReal := fun w => chartFunction ψ e w + (ρ₂ w : EReal) with hΨ
  set P₁ : ComplexModel (d' + 1) → EReal := fun w => ((c * c₁ : ℝ) : EReal) * Φ w with hP₁
  set P₂ : ComplexModel (d' + 1) → EReal := fun w => ((c * c₂ : ℝ) : EReal) * Ψ w with hP₂
  have hpsh₁ : PlurisubharmonicOn P₁ (W₁ ∩ W₂) := (hp₁.mono inter_subset_left).const_mul hcc₁
  have hpsh₂ : PlurisubharmonicOn P₂ (W₁ ∩ W₂) := (hp₂.mono inter_subset_right).const_mul hcc₂
  -- the germ is `L²` against the chart weight of `c (c₁ φ + c₂ ψ)` with exponent `1`
  have h1 : MultiplierIntegrableAt
      (fun w => (c : EReal) * chartFunction (fun p => (c₁ : EReal) * φ p + (c₂ : EReal) * ψ p) e w)
      1 (fun w => g (e.val.symm w)) z₀ volume :=
    MultiplierSubadditivity.multiplierIntegrableAt_of_weight_eq one_pos
      (fun y => (MultiplierSubadditivity.multiplierWeight_one_mul c _).symm) hg.2
  -- add the continuous correction `c c₁ ρ₁ + c c₂ ρ₂`
  have hρ : ContinuousOn (fun w => c * c₁ * ρ₁ w + c * c₂ * ρ₂ w) (W₁ ∩ W₂) :=
    ((continuousOn_const.mul (hρ₁s.continuousOn.mono inter_subset_left)).add
      (continuousOn_const.mul (hρ₂s.continuousOn.mono inter_subset_right)))
  have hfun : (fun w => (c : EReal) *
        chartFunction (fun p => (c₁ : EReal) * φ p + (c₂ : EReal) * ψ p) e w +
        ((c * c₁ * ρ₁ w + c * c₂ * ρ₂ w : ℝ) : EReal)) = fun w => P₁ w + P₂ w := by
    funext w
    exact ereal_smul_add_add_coe hc.le hc₁.le hc₂.le _ _ _ _
  have h2 : MultiplierIntegrableAt (fun w => P₁ w + P₂ w) 1 (fun w => g (e.val.symm w)) z₀
      volume := by
    have := QuantitativeRegularizationChartGermTransfer.multiplierIntegrableAt_add_continuous
      hWo hρ (by rw [hfun]; exact hpsh₁.add hpsh₂) ⟨hz₁, hz₂⟩ h1
    rwa [hfun] at this
  obtain ⟨N, sv, A, hsv, hA, hev⟩ :=
    MultiplierSubadditivityLocal.inGermSpan_mul_of_multiplierIntegrableAt hWo hpsh₁ hpsh₂
      ⟨hz₁, hz₂⟩ h2
  choose aa bb haa hbb hsveq using hsv
  have haa' : ∀ i, (multiplierIdeal (n := d' + 1) (c * c₁) φ).mem x (fun p => aa i (e.val p)) :=
    fun i => DemaillyApproximationAnalyticType.mem_multiplierIdeal_of_chart hφ.1 hcc₁ e hW₁o
      hρ₁s.continuousOn hxs hz₁
      (MultiplierSubadditivity.multiplierIntegrableAt_of_weight_eq hcc₁
        (fun y => MultiplierSubadditivity.multiplierWeight_one_mul (c * c₁) (Φ y)) (haa i))
  have hbb' : ∀ i, (multiplierIdeal (n := d' + 1) (c * c₂) ψ).mem x (fun p => bb i (e.val p)) :=
    fun i => DemaillyApproximationAnalyticType.mem_multiplierIdeal_of_chart hψ.1 hcc₂ e hW₂o
      hρ₂s.continuousOn hxs hz₂
      (MultiplierSubadditivity.multiplierIntegrableAt_of_weight_eq hcc₂
        (fun y => MultiplierSubadditivity.multiplierWeight_one_mul (c * c₂) (Ψ y)) (hbb i))
  refine ⟨hg.1, N, fun i p => aa i (e.val p) * bb i (e.val p), fun i p => A i (e.val p),
    fun i => ⟨_, _, haa' i, hbb' i, rfl⟩,
    fun i => DemaillyApproximationAnalyticType.holomorphicAt_comp_atlas hxs (hA i), ?_⟩
  filter_upwards [e.val.open_source.mem_nhds hxs, (e.val.continuousAt hxs).eventually hev]
    with p hp hpev
  have h3 : g p = g (e.val.symm (e.val p)) := by rw [e.val.left_inv hp]
  rw [h3, hpev]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsveq i]

end Manifold

/-! ### Concavity of `φ ↦ φ^An` -/

section Scheme

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov

/-- `a / j * (j / k) = a / k` in `[0, ∞]` for a positive integer `j`. -/
theorem ennreal_div_natCast_mul_div_cancel (a : ℝ≥0∞) {j : ℕ} (hj : 1 ≤ j) (k : ℝ≥0∞) :
    a / (j : ℝ≥0∞) * ((j : ℝ≥0∞) / k) = a / k := by
  have hj0 : (j : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hj)
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_assoc, ← mul_assoc ((j : ℝ≥0∞)⁻¹),
    ENNReal.inv_mul_cancel hj0 (ENNReal.natCast_ne_top j), one_mul]

/-- `⌊c k⌋ / k → c` in `[0, ∞]`, `c ≥ 0`. -/
theorem tendsto_natFloor_mul_div_ennreal {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun k : ℕ => (⌊c * k⌋₊ : ℝ≥0∞) / k) atTop (𝓝 (ENNReal.ofReal c)) := by
  have h := (tendsto_nat_floor_mul_div_atTop hc).comp tendsto_natCast_atTop_atTop
  refine ((ENNReal.continuous_ofReal.tendsto c).comp h).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  simp only [Function.comp_apply]
  rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr hk), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast]

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f) [IsProper f]

local instance qwNAPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance qwNAPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance qwNAPointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable {θ θ' θ'' : SmoothRealForm n (SchemeComplexPoint f) 2} {φ ψ : SchemeComplexPoint f → EReal}
  {c₁ c₂ : ℝ}

/-- **Subadditivity of the algebraic models of multiplier ideals for independent weights**:
`alg 𝓘(c (c₁ φ + c₂ ψ)) ≤ alg 𝓘(c c₁ φ) · alg 𝓘(c c₂ ψ)` (GAGA transport of
`multiplierIdeal_smul_add_le_mul`). -/
theorem algebraization_multiplierIdeal_smul_add_le_mul (hφ : IsThetaPshPotential θ φ)
    (hψ : IsThetaPshPotential θ' ψ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hχ : IsThetaPshPotential θ'' (fun x => (c₁ : EReal) * φ x + (c₂ : EReal) * ψ x))
    {c : ℝ} (hc : 0 < c) :
    algebraization f n E
        (multiplierIdeal (n := n) c (fun x => (c₁ : EReal) * φ x + (c₂ : EReal) * ψ x)) ≤
      algebraization f n E (multiplierIdeal (n := n) (c * c₁) φ) *
        algebraization f n E (multiplierIdeal (n := n) (c * c₂) ψ) := by
  have hA := SGPT.GAGA.H0S.multiplierIdealAlgebraic f E n
  rw [← analytificationIdeal_le_iff f n E,
    analytificationIdeal_algebraization_eq f n E hA ⟨hχ.1.quasiPlurisubharmonic, hχ.2⟩ hc]
  intro x g hg
  have h1 := multiplierIdeal_smul_add_le_mul hφ hψ hc hc₁ hc₂ x g hg
  rw [← analytificationIdeal_algebraization_eq f n E hA ⟨hφ.1.quasiPlurisubharmonic, hφ.2⟩
      (mul_pos hc hc₁),
    ← analytificationIdeal_algebraization_eq f n E hA ⟨hψ.1.quasiPlurisubharmonic, hψ.2⟩
      (mul_pos hc hc₂)] at h1
  exact mul_analytificationIdeal_le f n E _ _ x g h1

/-- `v(𝓘(j₁ φ)) + v(𝓘(j₂ ψ)) ≤ v(𝓘(k (c₁ φ + c₂ ψ)))` for positive integers `j₁ ≤ k c₁`,
`j₂ ≤ k c₂`. -/
theorem multiplierIdealVal_add_le_smul_add (hφ : IsThetaPshPotential θ φ)
    (hψ : IsThetaPshPotential θ' ψ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hχ : IsThetaPshPotential θ'' (fun x => (c₁ : EReal) * φ x + (c₂ : EReal) * ψ x))
    (v : BerkovichPoint f) {k j₁ j₂ : ℕ} (hk : 0 < k) (hj₁ : 0 < j₁) (hj₂ : 0 < j₂)
    (hjk₁ : (j₁ : ℝ) ≤ k * c₁) (hjk₂ : (j₂ : ℝ) ≤ k * c₂) :
    v.multiplierIdealVal n E φ j₁ + v.multiplierIdealVal n E ψ j₂ ≤
      v.multiplierIdealVal n E (fun x => (c₁ : EReal) * φ x + (c₂ : EReal) * ψ x) k := by
  have := E.locallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  unfold BerkovichPoint.multiplierIdealVal
  rw [← v.idealVal_mul]
  apply v.idealVal_antitone
  refine (algebraization_multiplierIdeal_smul_add_le_mul n E hφ hψ hc₁ hc₂ hχ
    (Nat.cast_pos.mpr hk)).trans ?_
  exact mul_le_mul'
    (algebraization_mono f n E (multiplierIdeal_le_of_exponent_le hφ.1.quasiPlurisubharmonic
      (Nat.cast_pos.mpr hj₁) hjk₁))
    (algebraization_mono f n E (multiplierIdeal_le_of_exponent_le hψ.1.quasiPlurisubharmonic
      (Nat.cast_pos.mpr hj₂) hjk₂))

/-- **Concavity of `v(·)`**: `c₁ v(φ) + c₂ v(ψ) ≤ v(c₁ φ + c₂ ψ)` for `v ∈ X^An`,
`φ ∈ PSH(X, θ)`, `ψ ∈ PSH(X, θ')` and `c₁, c₂ > 0` with `c₁ φ + c₂ ψ` quasi-psh. -/
theorem potentialVal_smul_add_ge (hφ : IsThetaPshPotential θ φ)
    (hψ : IsThetaPshPotential θ' ψ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hχ : IsThetaPshPotential θ'' (fun x => (c₁ : EReal) * φ x + (c₂ : EReal) * ψ x))
    (v : BerkovichPoint f) :
    ENNReal.ofReal c₁ * v.potentialVal n E φ + ENNReal.ofReal c₂ * v.potentialVal n E ψ ≤
      v.potentialVal n E (fun x => (c₁ : EReal) * φ x + (c₂ : EReal) * ψ x) := by
  have hfloor : ∀ {c : ℝ}, 0 < c → Tendsto (fun k : ℕ => ⌊c * k⌋₊) atTop atTop := fun hc =>
    tendsto_nat_floor_atTop.comp (Tendsto.const_mul_atTop hc tendsto_natCast_atTop_atTop)
  have hterm : ∀ {θ₀ : SmoothRealForm n (SchemeComplexPoint f) 2} {u : SchemeComplexPoint f → EReal}
      {c : ℝ}, IsThetaPshPotential θ₀ u → 0 < c →
      Tendsto (fun k : ℕ => v.multiplierIdealVal n E u ⌊c * k⌋₊ / (⌊c * k⌋₊ : ℝ≥0∞) *
        ((⌊c * k⌋₊ : ℝ≥0∞) / k)) atTop (𝓝 (v.potentialVal n E u * ENNReal.ofReal c)) :=
    fun hu hc => ENNReal.Tendsto.mul
      ((SGPT.GAGA.H0S.tendsto_potentialVal E n hu v).comp (hfloor hc))
      (Or.inr ENNReal.ofReal_ne_top) (tendsto_natFloor_mul_div_ennreal hc.le)
      (Or.inl (ENNReal.ofReal_pos.mpr hc).ne')
  rw [mul_comm (ENNReal.ofReal c₁), mul_comm (ENNReal.ofReal c₂)]
  refine le_of_tendsto_of_tendsto ((hterm hφ hc₁).add (hterm hψ hc₂))
    (SGPT.GAGA.H0S.tendsto_potentialVal E n hχ v) ?_
  filter_upwards [(hfloor hc₁).eventually_ge_atTop 1, (hfloor hc₂).eventually_ge_atTop 1,
    eventually_gt_atTop 0] with k h1 h2 hk
  rw [ennreal_div_natCast_mul_div_cancel _ h1, ennreal_div_natCast_mul_div_cancel _ h2,
    ← ENNReal.add_div]
  refine ENNReal.div_le_div_right (multiplierIdealVal_add_le_smul_add n E hφ hψ hc₁ hc₂ hχ v hk
    h1 h2 ?_ ?_) _
  · exact (Nat.floor_le (by positivity)).trans_eq (mul_comm _ _)
  · exact (Nat.floor_le (by positivity)).trans_eq (mul_comm _ _)

/-- `((ENNReal.ofReal c) p : [-∞, ∞]) = c p` for `c ≥ 0`. -/
theorem coe_ennreal_ofReal_mul {c : ℝ} (hc : 0 ≤ c) (p : ℝ≥0∞) :
    ((ENNReal.ofReal c * p : ℝ≥0∞) : EReal) = (c : EReal) * (p : EReal) := by
  rw [EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal, max_eq_left hc]

/-- **Concavity of the analytification** (the input of the second equality of
`eq:psianvlinear`): `(c₁ φ + c₂ ψ)^An ≤ c₁ φ^An + c₂ ψ^An` on `X^An`. -/
theorem potentialAn_smul_add_le (hφ : IsThetaPshPotential θ φ)
    (hψ : IsThetaPshPotential θ' ψ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hχ : IsThetaPshPotential θ'' (fun x => (c₁ : EReal) * φ x + (c₂ : EReal) * ψ x))
    (v : BerkovichPoint f) :
    potentialAn n E (fun x => (c₁ : EReal) * φ x + (c₂ : EReal) * ψ x) v ≤
      (c₁ : EReal) * potentialAn n E φ v + (c₂ : EReal) * potentialAn n E ψ v := by
  have h := potentialVal_smul_add_ge n E hφ hψ hc₁ hc₂ hχ v
  unfold potentialAn
  have hne : ∀ p : ℝ≥0∞, (p : EReal) ≠ ⊥ := fun p => ne_bot_of_le_ne_bot EReal.zero_ne_bot
    (EReal.coe_ennreal_nonneg p)
  rw [mul_neg, mul_neg, ← coe_ennreal_ofReal_mul hc₁.le, ← coe_ennreal_ofReal_mul hc₂.le,
    ← sub_eq_add_neg, ← EReal.neg_add (Or.inl (hne _)) (Or.inr (hne _)), ← EReal.coe_ennreal_add,
    EReal.neg_le_neg_iff, EReal.coe_ennreal_le_coe_ennreal_iff]
  exact h

/-- The affine-combination step of `eq:psianvlinear`: if `(1-t) a + t b ≤ x` in `[0, ∞]`,
`0 < t < 1`, then `-x + ((1-t) σ + t τ) ≤ max(-a + σ, -b + τ)` in `[-∞, ∞]`. -/
theorem ereal_neg_add_affine_le_max {a b x : ℝ≥0∞} {t σ τ : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (h : ENNReal.ofReal (1 - t) * a + ENNReal.ofReal t * b ≤ x) :
    -(x : EReal) + (((1 - t) * σ + t * τ : ℝ) : EReal) ≤
      max (-(a : EReal) + (σ : EReal)) (-(b : EReal) + (τ : EReal)) := by
  by_cases hx : x = ⊤
  · rw [hx, EReal.coe_ennreal_top, EReal.neg_top, EReal.bot_add]
    exact bot_le
  have hxlt : ENNReal.ofReal (1 - t) * a + ENNReal.ofReal t * b < ⊤ :=
    lt_of_le_of_lt h (lt_top_iff_ne_top.mpr hx)
  have ha : a ≠ ⊤ := by
    intro ha
    rw [ha, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (sub_pos.mpr ht1)).ne', top_add] at hxlt
    exact lt_irrefl _ hxlt
  have hb : b ≠ ⊤ := by
    intro hb
    rw [hb, ENNReal.mul_top (ENNReal.ofReal_pos.mpr ht0).ne', add_top] at hxlt
    exact lt_irrefl _ hxlt
  obtain ⟨a', ha', rfl⟩ : ∃ a' : ℝ, 0 ≤ a' ∧ a = ENNReal.ofReal a' :=
    ⟨a.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal ha).symm⟩
  obtain ⟨b', hb', rfl⟩ : ∃ b' : ℝ, 0 ≤ b' ∧ b = ENNReal.ofReal b' :=
    ⟨b.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hb).symm⟩
  obtain ⟨x', hx', rfl⟩ : ∃ x' : ℝ, 0 ≤ x' ∧ x = ENNReal.ofReal x' :=
    ⟨x.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hx).symm⟩
  rw [← ENNReal.ofReal_mul (sub_pos.mpr ht1).le, ← ENNReal.ofReal_mul ht0.le,
    ← ENNReal.ofReal_add (mul_nonneg (sub_pos.mpr ht1).le ha') (mul_nonneg ht0.le hb'),
    ENNReal.ofReal_le_ofReal_iff hx'] at h
  simp only [EReal.coe_ennreal_ofReal, max_eq_left ha', max_eq_left hb', max_eq_left hx']
  rw [← EReal.coe_neg, ← EReal.coe_neg, ← EReal.coe_neg, ← EReal.coe_add, ← EReal.coe_add,
    ← EReal.coe_add, le_max_iff, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
  rcases le_total (-a' + σ) (-b' + τ) with hab | hab
  · right; nlinarith
  · left; nlinarith

/-! ### The analytification of a piecewise linear curve -/

namespace PiecewiseLinearData

open SGPT.PSH.VariableComplexAtlas

variable {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
  (D : PiecewiseLinearData θ)

/-- `A_τ^An(v) + τ ≤ max_i (A_{τ_i}^An(v) + τ_i)` for every `τ ≤ τ_0`. -/
theorem potentialAn_curve_add_le_iSup (v : BerkovichPoint f) {s : ℝ} (hs : s ≤ D.τ 0) :
    potentialAn n E (D.curve s) v + (s : EReal) ≤
      ⨆ i, potentialAn n E (D.A i) v + (D.τ i : EReal) := by
  set i := D.segIndex s hs
  have hle : s ≤ D.τ i := D.le_tau_segIndex s hs
  rcases hle.lt_or_eq with hlt | heq
  · by_cases hi : i.val < D.N
    · set j := D.nextIdx i hi
      have hjs : D.τ j < s := D.tau_lt_of_segIndex_lt s hs (D.lt_nextIdx i hi)
      set t := (D.τ i - s) / (D.τ i - D.τ j) with htdef
      have hden : 0 < D.τ i - D.τ j := by linarith
      have ht0 : 0 < t := div_pos (by linarith) hden
      have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
      have hst : s = (1 - t) * D.τ i + t * D.τ j := by
        rw [htdef]
        field_simp
        ring
      have hcurve : D.curve s = affineComb t (D.A i) (D.A j) := by
        rw [hst]
        exact D.curve_affine i hi ht0 ht1
      have hφ := (isThetaPSH_iff_nativeThetaPotential θ _).mp (D.isThetaPSH i)
      have hψ := (isThetaPSH_iff_nativeThetaPotential θ _).mp (D.isThetaPSH j)
      have hχ := (isThetaPSH_iff_nativeThetaPotential θ _).mp (D.isThetaPSH_curve hs)
      rw [hcurve] at hχ
      have hval := potentialVal_smul_add_ge n E hφ hψ (sub_pos.mpr ht1) ht0 hχ v
      calc potentialAn n E (D.curve s) v + (s : EReal)
          ≤ max (potentialAn n E (D.A i) v + (D.τ i : EReal))
              (potentialAn n E (D.A j) v + (D.τ j : EReal)) := by
            rw [hcurve]
            conv_lhs => rw [hst]
            exact ereal_neg_add_affine_le_max ht0 ht1 hval
        _ ≤ _ := max_le
            (le_iSup (fun i => potentialAn n E (D.A i) v + (D.τ i : EReal)) i)
            (le_iSup (fun i => potentialAn n E (D.A i) v + (D.τ i : EReal)) j)
    · have hlast : i = Fin.last D.N := by
        ext
        simp only [Fin.val_last]
        omega
      have hsl : s ≤ D.τ (Fin.last D.N) := hlast ▸ hle
      rw [D.curve_of_le_last hsl]
      exact le_iSup_of_le (Fin.last D.N) (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hsl))
  · rw [heq, D.curve_tau]
    exact le_iSup (fun i => potentialAn n E (D.A i) v + (D.τ i : EReal)) i

/-- **Source `def:piecewiselincurv`, second equality of `eq:psianvlinear`**: the analytification
`A^An(v) = sup_{τ ≤ τ_0} (A_τ^An(v) + τ)` of a piecewise linear curve equals
`max_{i = 0, …, N} (A_{τ_i}^An(v) + τ_i)` for every `v ∈ X^An`. -/
theorem curveAn_eq_iSup (v : BerkovichPoint f) :
    D.curveAn n E v = ⨆ i, potentialAn n E (D.A i) v + (D.τ i : EReal) :=
  le_antisymm (iSup₂_le fun _ hs => D.potentialAn_curve_add_le_iSup n E v hs)
    (iSup_le fun i => D.le_curveAn n E v i)

/-- The supremum in `eq:psianvlinear` is a maximum over the nodes: it is attained at some `τ_i`. -/
theorem exists_curveAn_eq (v : BerkovichPoint f) :
    ∃ i, D.curveAn n E v = potentialAn n E (D.A i) v + (D.τ i : EReal) := by
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite
    (f := fun i : Fin (D.N + 1) => potentialAn n E (D.A i) v + (D.τ i : EReal))
  exact ⟨i, (D.curveAn_eq_iSup n E v).trans hi.symm⟩

/-- `A^An` takes values in `[-∞, τ_0] ⊆ [-∞, ∞)` (the codomain in `eq:psianvlinear`). -/
theorem curveAn_le_tau_zero (v : BerkovichPoint f) : D.curveAn n E v ≤ (D.τ 0 : EReal) := by
  rw [D.curveAn_eq_iSup n E v]
  refine iSup_le fun i => ?_
  calc potentialAn n E (D.A i) v + (D.τ i : EReal) ≤ 0 + (D.τ 0 : EReal) :=
        add_le_add (potentialAn_nonpos n E _ v) (EReal.coe_le_coe_iff.mpr (D.tau_le_tau_zero i))
    _ = (D.τ 0 : EReal) := zero_add _

theorem curveAn_ne_top (v : BerkovichPoint f) : D.curveAn n E v ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.coe_ne_top _) (D.curveAn_le_tau_zero n E v)

end PiecewiseLinearData

end Scheme

end SGPT.NAPotential.Berkovich

end
