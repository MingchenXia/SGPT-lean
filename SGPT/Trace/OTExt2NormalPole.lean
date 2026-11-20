import SGPT.Okounkov.TranscendentalPoleExtension
import SGPT.Trace.TwistedL2Statement
import SGPT.Foundations.Analysis.Pending.HolomorphicGermAlgebra

/-!
# FPT `lem:global-normal-pole`: the function `R_Y`

Blueprint `claude-ot-ext2.tex`, node `claude-ot-ext2:normal-pole`.  Xia, *Foundations of
pluripotential theory*, q07, `lem:global-normal-pole`: for a closed complex submanifold `Y` of
codimension `≥ 1` of a compact Kähler manifold `(X, ω)` there is a smooth function `R_Y ≥ 0`
vanishing exactly on `Y` such that

* (2) `ddᶜ log R_Y ≥ -b ω` and `ddᶜ log (R_Y + ε) ≥ -b ω` for every `ε > 0`, with one `b ≥ 0`;
* (3) `c |w|² ≤ R_Y ≤ C |w|²` near every point of `Y`, in holomorphic coordinates `(z', w)` with
  `Y = {w = 0}`;
* (4) `log R_Y` has gentle analytic singularities of type `(1, 𝓘_Y)`;
* `max_X R_Y < e^{-4}` (after multiplication by a small constant).

## Formalization

`IsGlobalNormalPole ω Y R` records these properties.  Clauses (2)--(4) and much more are packaged
through the Okounkov chapter's `IsSubmanifoldPole ω Y (log R)` (`ddᶜ log R ≥ -Cω` as currents, pole
set exactly `Y`, the local form `log R = log ∑_{i ≥ k} |ζ_i|² + O(1)` in **every** flattening chart
`ζ` of `Y`, analytic singularities of type `(1, 𝓘_Y)`, the factorization on every blowup along
`Y` and gentle analytic singularities of type `(c, 𝓘_Y)` of `c log R` for every `c ∈ ℚ_{>0}`),
together with the uniform pointwise Levi bounds of (2) in every chart
(`ddᶜ u` evaluated on `(v, iv)` is `Levi(u)(v)/π`).

FPT's clauses (1) (the real Hessian of `R_Y` at points of `Y` is positive on non-tangent vectors)
and the Taylor expansion `|R_Y - Q_{z'}(w)| ≤ C |w|³` in (3) are used only in the proof of
`lem:gentle-weighted-normal-residue` (identification of the limit on the blowup), which is not
formalized here; they are not recorded.

## Construction

`R = U` is Demailly--Păun's weight `U = ∑_a θ_a² ∑_i |c g_{a,i}|²` of a concentration partition
of `Y` (`SubmanifoldConcentrationPotential.ConcentrationPartition`, FPT's `∑ χ_i² |w^{(i)}|²` with
arbitrary local generators of `𝓘_Y`), the generators being multiplied by a small constant `c`
(`ConcentrationPartition.scaleGen`) so that `max U < e^{-4}`.  The pole properties are those of
the Okounkov chapter (`exists_submanifold_pole`); the uniform bound (2) is TN's
`exists_pos_isSemipositive_ddc_log_weight` (dp04 Lemma 2.1 (ii)).

## Main results

* `IsGlobalNormalPole`, `logPole`;
* `ConcentrationPartition.scaleGen`, `weight_scaleGen`;
* `exists_isGlobalNormalPole`: FPT `lem:global-normal-pole` (clauses (2), (3) comparison, (4)).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.OTExt2

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SubmanifoldConcentrationPotential
open SGPT.Okounkov.TranscendentalPole
open SGPT.Trace.TwistedL2 (kahlerQuad)

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- `log R` as an extended real function, with `log 0 = -∞`. -/
def logPole (R : X → ℝ) (x : X) : EReal := ENNReal.log (ENNReal.ofReal (R x))

/-- **FPT `lem:global-normal-pole`**: `R` is a normal pole function of the closed submanifold `W`
of the Kähler manifold `(X, ω)`: `R` is smooth, `0 ≤ R < e^{-4}`, `log R` is a pole along `W`
(`IsSubmanifoldPole`: `ddᶜ log R ≥ -C ω`, `log R = -∞` exactly on `W`, the local form
`log R = log |w|² + O(1)` in every flattening chart, gentle analytic singularities of type
`(c, 𝓘_W)` of `c log R`, ...), and there is one `b ≥ 0` with `ddᶜ log (R + ε) ≥ -b ω` for every
`ε > 0` and `ddᶜ log R ≥ -b ω` off `W`, in every chart. -/
structure IsGlobalNormalPole (omega : KahlerBackground n X) (W : Set X) (R : X → ℝ) : Prop where
  smooth : ChartSmooth (n := n) R
  nonneg : ∀ x, 0 ≤ R x
  lt_exp : ∀ x, R x < Real.exp (-4)
  pole : IsSubmanifoldPole omega W (logPole R)
  levi : ∃ b : ℝ, 0 ≤ b ∧
    (∀ ε : ℝ, 0 < ε → ∀ (c : ComplexChart n X), ∀ z ∈ c.val.target, ∀ v : ComplexModel n,
      0 ≤ leviForm (fun w => Real.log (R (c.val.symm w) + ε)) z v / Real.pi +
        b * kahlerQuad omega c z v) ∧
    (∀ (c : ComplexChart n X), ∀ z ∈ c.val.target, 0 < R (c.val.symm z) →
      ∀ v : ComplexModel n,
        0 ≤ leviForm (fun w => Real.log (R (c.val.symm w))) z v / Real.pi +
          b * kahlerQuad omega c z v)

namespace IsGlobalNormalPole

variable {omega : KahlerBackground n X} {W : Set X} {R : X → ℝ}

theorem eq_zero_iff (hR : IsGlobalNormalPole omega W R) (x : X) : R x = 0 ↔ x ∈ W := by
  rw [← hR.pole.eq_bot_iff x, logPole, ENNReal.log_eq_bot_iff, ENNReal.ofReal_eq_zero]
  exact ⟨fun h => h.le, fun h => le_antisymm h (hR.nonneg x)⟩

theorem pos_of_notMem (hR : IsGlobalNormalPole omega W R) {x : X} (hx : x ∉ W) : 0 < R x :=
  lt_of_le_of_ne (hR.nonneg x) fun h => hx ((hR.eq_zero_iff x).mp h.symm)

theorem continuous (hR : IsGlobalNormalPole omega W R) : Continuous R :=
  continuous_iff_continuousAt.mpr fun x =>
    MeteredDivisorWeightBounds.continuousAt_of_chartContDiffOn (n := n) (h := R) isOpen_univ
      (fun e => by simpa using hR.smooth e) (mem_univ x)

theorem le_exp (hR : IsGlobalNormalPole omega W R) (x : X) : R x ≤ Real.exp (-4) :=
  (hR.lt_exp x).le

end IsGlobalNormalPole

/-! ### Scaling the generators of a concentration partition -/

omit [IsComplexManifold n X] in
theorem isInSpanAt_range_const_mul_iff {N : ℕ} (g : Fin N → X → ℂ) {c : ℂ} (hc : c ≠ 0)
    (y : X) (f : X → ℂ) :
    IsInSpanAt (n := n) (· ∈ range fun i y => c * g i y) y f ↔
      IsInSpanAt (n := n) (· ∈ range g) y f := by
  constructor
  · rintro ⟨hf, N', s, a, hs, ha, heq⟩
    choose j hj using hs
    refine ⟨hf, N', fun i => g (j i), fun i y => c * a i y, fun i => ⟨j i, rfl⟩,
      fun i => (holomorphicAt_const c).mul (ha i), ?_⟩
    filter_upwards [heq] with y hy
    rw [hy]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hj i]
    ring
  · rintro ⟨hf, N', s, a, hs, ha, heq⟩
    choose j hj using hs
    refine ⟨hf, N', fun i y => c * g (j i) y, fun i y => c⁻¹ * a i y, fun i => ⟨j i, rfl⟩,
      fun i => (holomorphicAt_const c⁻¹).mul (ha i), ?_⟩
    filter_upwards [heq] with y hy
    rw [hy]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hj i]
    field_simp

namespace ConcentrationPartitionScale

variable {Y : Set X} {ι : Type} [Fintype ι]

/-- The concentration partition with generators `c g_{a,i}` (`c ≠ 0`); its weight is
`|c|² U`. -/
def scaleGen (P : ConcentrationPartition n Y ι) (c : ℂ) (hc : c ≠ 0) :
    ConcentrationPartition n Y ι where
  dom := P.dom
  isOpen_dom := P.isOpen_dom
  arity := P.arity
  gen := fun a i y => c * P.gen a i y
  gen_mdifferentiableOn := fun a i => (P.gen_mdifferentiableOn a i).const_smul c
  gen_spec := fun a y hy f =>
    (P.gen_spec a y hy f).trans (isInSpanAt_range_const_mul_iff (n := n) (P.gen a) hc y f).symm
  part := P.part
  part_smooth := P.part_smooth
  part_nonneg := P.part_nonneg
  part_tsupport := P.part_tsupport
  part_sum := P.part_sum

theorem weight_scaleGen (P : ConcentrationPartition n Y ι) {c : ℂ} (hc : c ≠ 0) (y : X) :
    (scaleGen P c hc).weight y = ‖c‖ ^ 2 * P.weight y := by
  simp only [ConcentrationPartition.weight, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [ConcentrationPartition.genNormSq, scaleGen]
  by_cases hy : y ∈ P.dom a
  · rw [indicator_of_mem hy, indicator_of_mem hy]
    simp only [generatorNormSq, norm_mul, mul_pow, ← Finset.mul_sum]
    ring
  · rw [indicator_of_notMem hy, indicator_of_notMem hy]
    ring

end ConcentrationPartitionScale

open ConcentrationPartitionScale

/-! ### Existence -/

/-- **FPT `lem:global-normal-pole`** (clauses (2), the comparison of (3), (4), and
`max R < e^{-4}`): every closed complex submanifold with empty interior of a compact Kähler
manifold carries a normal pole function. -/
theorem exists_isGlobalNormalPole [CompactSpace X] (omega : KahlerBackground n X) {W : Set X}
    (hW : IsClosedSubmanifold n W) (hWint : interior W = ∅) :
    ∃ R : X → ℝ, IsGlobalNormalPole omega W R := by
  obtain ⟨ι, _, ⟨P₀⟩⟩ :=
    exists_of_isCoherent (VanishingIdealCoherent.isCoherent_vanishingIdeal hW)
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ x, P₀.weight x ≤ B := by
    obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn
      P₀.continuous_weight.continuousOn
    exact ⟨B, fun x => (le_abs_self _).trans ((hB x (mem_univ x)).trans_eq' rfl)⟩
  set t : ℝ := Real.exp (-4) / (2 * (|B| + 1)) with ht
  have ht0 : 0 < t := by positivity
  set c : ℂ := ((Real.sqrt t : ℝ) : ℂ) with hcdef
  have hc : c ≠ 0 := by
    rw [hcdef, Ne, Complex.ofReal_eq_zero]
    exact (Real.sqrt_pos.mpr ht0).ne'
  have hcn : ‖c‖ ^ 2 = t := by
    rw [hcdef, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt ht0.le]
  set P := scaleGen P₀ c hc with hP
  have hw : ∀ x, P.weight x < Real.exp (-4) := by
    intro x
    rw [hP, weight_scaleGen P₀ hc, hcn]
    have h1 : P₀.weight x ≤ |B| + 1 := (hB x).trans ((le_abs_self B).trans (by linarith))
    have h2 : t * P₀.weight x ≤ t * (|B| + 1) :=
      mul_le_mul_of_nonneg_left h1 ht0.le
    have h3 : t * (|B| + 1) = Real.exp (-4) / 2 := by
      rw [ht]; field_simp
    have h4 : 0 < Real.exp (-4) := Real.exp_pos _
    linarith
  obtain ⟨A₀, hA₀, hpsh⟩ := exists_isThetaPshPotential_concentrationPole P hW.1 hWint omega
  refine ⟨P.weight, ⟨P.chartSmooth_weight, P.weight_nonneg, hw, ?_, ?_⟩⟩
  · refine
      { exists_thetaPsh := ⟨A₀, hA₀.le, hpsh⟩
        eq_bot_iff := concentrationPole_eq_bot_iff P hW.1
        ne_top := concentrationPole_ne_top P
        continuous := continuous_concentrationPole P
        smoothOn_compl := smoothOn_compl_concentrationPole P hW.1
        chartSmooth_exp := chartSmooth_exp_concentrationPole P
        localForm := fun x _ k Φ hΦ => localForm_concentrationPole P hW.1 hΦ
        analyticType := hasAnalyticSingularitiesOfType_concentrationPole P hW
        blowup := ?_
        gentle := fun c hc => sourceGentle_concentrationPole P omega hW hWint hc }
    intro Zb _ _ _ π hπ z
    obtain ⟨S, h, R, hS, hzS, hhol, -, hgen, hR, hid⟩ := exists_blowup_factor P hπ z
    exact ⟨S, h, R, hS, hzS, hhol, hgen, hR, hid⟩
  · obtain ⟨A₁, hA₁, h1⟩ := P.exists_pos_isSemipositive_ddc_log_weight omega
    obtain ⟨A₂, hA₂, h2⟩ := P.exists_pos_levi_log_weight omega
    refine ⟨max A₁ A₂, le_max_of_le_left hA₁.le, fun ε hε e z hz v => ?_,
      fun e z hz hpos v => ?_⟩
    · have hq : 0 ≤ kahlerQuad omega e z v := omega.isSemipositive e z hz v
      have h := h1 ε hε e z hz v
      simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
        ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
        smul_eq_mul] at h
      rw [P.ddc_log_weight_lineValue hε e hz v] at h
      have : A₁ * kahlerQuad omega e z v ≤ max A₁ A₂ * kahlerQuad omega e z v :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hq
      unfold kahlerQuad at this hq ⊢
      linarith
    · have hq : 0 ≤ kahlerQuad omega e z v := omega.isSemipositive e z hz v
      have h := h2 e z hz hpos v
      have : A₂ * kahlerQuad omega e z v ≤ max A₁ A₂ * kahlerQuad omega e z v :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hq
      unfold kahlerQuad at this hq ⊢
      linarith

/-- **FPT `lem:global-normal-pole`** for a closed connected submanifold of dimension `m < n`. -/
theorem exists_isGlobalNormalPole_of_lt [CompactSpace X] (omega : KahlerBackground n X)
    {W : Set X} {m : ℕ} (hW : IsClosedConnectedSubmanifold n W m) (hmn : m < n) :
    ∃ R : X → ℝ, IsGlobalNormalPole omega W R :=
  exists_isGlobalNormalPole omega (isClosedSubmanifold_of_isClosedConnectedSubmanifold hW)
    (interior_eq_empty_of_lt hW hmn)

end SGPT.Trace.OTExt2
