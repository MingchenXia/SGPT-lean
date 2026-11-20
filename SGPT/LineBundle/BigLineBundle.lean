import SGPT.LineBundle.SectionRing
import SGPT.Okounkov.SchemeLineBundleMetricGeometry
import SGPT.Okounkov.SchemeLineBundleStructuralMetric
import SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Big line bundles and the volume of a line bundle

Source: the standing hypothesis "`L` is a big line bundle" of `def:testcurve:L1134`,
`ex:RWN` (chapter *Test curves*) and of Section *Algebraic partial Okounkov bodies* (chapter
*The theory of Okounkov bodies*); the volume `vol L = lim_k n! h⁰(X, L^k) / k^n`
(`cor:volbigL`, chapter *I-good singularities*).

## Main definitions

* `SGPT.LineBundle.h0 f L k`: the dimension `h⁰(X, L^k)`.
* `SGPT.LineBundle.IsBig f L n`: `L` is big on the `n`-dimensional `X`, in the
  section-growth sense: there is `c > 0` with `h⁰(X, L^k) ≥ c k^n` for all large `k`.
* `SGPT.LineBundle.volume f L n`: `vol L = limsup_k n! h⁰(X, L^k) / k^n ∈ [0, ∞]`. The
  source writes a limit; that the limit exists is source `cor:volbigL` (via `thm:DXmain1`),
  not formalized, so the `limsup` is used, which is the limit whenever it exists.
* `SGPT.LineBundle.HasBigChernClass f n E a`: the source's literal definition
  (`def:psefclass`): the first Chern class `c₁(L)` of the analytic line bundle is big, i.e.
  contains a Kähler current.

The equivalence of the two notions of bigness (holomorphic Morse inequalities / Ji–Shiffman /
Bonavero) is not formalized; both are recorded so that consumers can state which one they use.

## Main results

* `IsBig.eventually_nontrivial`, `IsBig.eventually_exists_ne_zero`: a big line bundle has
  nonzero sections in all large degrees.
* `IsBig.volume_pos`: a big line bundle has positive volume.
* `volume_eq_of_tendsto`: if `k^{-n} h⁰(X, L^k) → v`, then `vol L = n! v`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.LineBundle

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter
open scoped ENNReal Nat Topology

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (L : X.Modules)

/-- The dimension `h⁰(X, L^k) = dim_ℂ H⁰(X, L^k)`. -/
def h0 (k : ℕ) : ℕ := Module.finrank ℂ (SectionSpace f L k)

/-- `L` is big on the `n`-dimensional scheme `X` (section-growth definition): there is a
constant `c > 0` such that `h⁰(X, L^k) ≥ c k^n` for all sufficiently large `k`. -/
def IsBig (n : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop, c * (k : ℝ) ^ n ≤ (h0 f L k : ℝ)

/-- The volume `vol L = limsup_{k → ∞} n! h⁰(X, L^k) / k^n ∈ [0, ∞]` of a line bundle on an
`n`-dimensional scheme. -/
def volume (n : ℕ) : ℝ≥0∞ :=
  limsup (fun k : ℕ => ((n ! : ℝ≥0∞) * (h0 f L k : ℝ≥0∞)) / (k : ℝ≥0∞) ^ n) atTop

variable {f L}

/-- A big line bundle has `h⁰(X, L^k) > 0` for all large `k`. -/
theorem IsBig.eventually_h0_pos {n : ℕ} (hL : IsBig f L n) : ∀ᶠ k : ℕ in atTop, 0 < h0 f L k := by
  obtain ⟨c, hc, hev⟩ := hL
  filter_upwards [hev, eventually_ge_atTop 1] with k hk hk1
  have hkpos : (0 : ℝ) < (k : ℝ) ^ n := pow_pos (by exact_mod_cast hk1) n
  have : (0 : ℝ) < h0 f L k := lt_of_lt_of_le (mul_pos hc hkpos) hk
  exact_mod_cast this

/-- A big line bundle has nonzero sections in all large degrees. -/
theorem IsBig.eventually_nontrivial {n : ℕ} (hL : IsBig f L n) :
    ∀ᶠ k : ℕ in atTop, Nontrivial (SectionSpace f L k) := by
  filter_upwards [hL.eventually_h0_pos] with k hk
  exact Module.nontrivial_of_finrank_pos hk

/-- A big line bundle has a nonzero section of `L^k` for all large `k`. -/
theorem IsBig.eventually_exists_ne_zero {n : ℕ} (hL : IsBig f L n) :
    ∀ᶠ k : ℕ in atTop, ∃ s : SectionSpace f L k, s ≠ 0 := by
  filter_upwards [hL.eventually_nontrivial] with k hk
  exact exists_ne 0

/-- A big line bundle has positive volume: `vol L ≥ n! c > 0`. -/
theorem IsBig.volume_pos {n : ℕ} (hL : IsBig f L n) : 0 < volume f L n := by
  obtain ⟨c, hc, hev⟩ := hL
  have hb : (0 : ℝ≥0∞) < ENNReal.ofReal ((n ! : ℝ) * c) :=
    ENNReal.ofReal_pos.mpr (mul_pos (by exact_mod_cast Nat.factorial_pos n) hc)
  refine lt_of_lt_of_le hb (le_limsup_of_frequently_le ?_ (by isBoundedDefault))
  refine (hev.and (eventually_ge_atTop 1)).frequently.mono ?_
  rintro k ⟨hk, hk1⟩
  have hkR : (0 : ℝ) < (k : ℝ) ^ n := pow_pos (by exact_mod_cast hk1) n
  have hk0 : ((k : ℝ≥0∞) ^ n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (show k ≠ 0 by omega))
  have hktop : ((k : ℝ≥0∞) ^ n) ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top k)
  rw [ENNReal.le_div_iff_mul_le (Or.inl hk0) (Or.inl hktop)]
  have hreal : (n ! : ℝ) * c * (k : ℝ) ^ n ≤ (n ! : ℝ) * (h0 f L k : ℝ) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hk (by positivity)
  have hcast : ((k : ℝ≥0∞) ^ n) = ENNReal.ofReal ((k : ℝ) ^ n) := by
    rw [ENNReal.ofReal_pow (Nat.cast_nonneg k), ENNReal.ofReal_natCast]
  rw [hcast, ← ENNReal.ofReal_mul (by positivity)]
  calc ENNReal.ofReal ((n ! : ℝ) * c * (k : ℝ) ^ n)
      ≤ ENNReal.ofReal ((n ! : ℝ) * (h0 f L k : ℝ)) := ENNReal.ofReal_le_ofReal hreal
    _ = (n ! : ℝ≥0∞) * (h0 f L k : ℝ≥0∞) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

/-- If the normalized dimensions converge, `k^{-n} h⁰(X, L^k) → v`, then `vol L = n! v` (the
`limsup` defining the volume is then a limit). -/
theorem volume_eq_of_tendsto {n : ℕ} {v : ℝ}
    (h : Tendsto (fun k : ℕ => (k : ℝ)⁻¹ ^ n * (h0 f L k : ℝ)) atTop (𝓝 v)) :
    volume f L n = ENNReal.ofReal ((n ! : ℝ) * v) := by
  have hT : Tendsto (fun k : ℕ => ENNReal.ofReal ((n ! : ℝ) * ((k : ℝ)⁻¹ ^ n * (h0 f L k : ℝ))))
      atTop (𝓝 (ENNReal.ofReal ((n ! : ℝ) * v))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (h.const_mul _)
  unfold volume
  rw [← hT.limsup_eq]
  apply limsup_congr
  filter_upwards [eventually_ge_atTop 1] with k hk1
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hk0 : ((k : ℝ≥0∞) ^ n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (show k ≠ 0 by omega))
  have hktop : ((k : ℝ≥0∞) ^ n) ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top k)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, inv_pow,
    ENNReal.ofReal_inv_of_pos (pow_pos hkR n), ENNReal.ofReal_pow hkR.le,
    ENNReal.ofReal_natCast, div_eq_mul_inv]
  ring

end SGPT.LineBundle

namespace SGPT.LineBundle

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]

local instance bigPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance bigPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance bigPointManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- Source `def:psefclass` for line bundles: `L` is big when its first Chern class
`c₁(L) = {c₁(L, h)}` (the class of the curvature form of a smooth Hermitian metric `h`) is a
big class, i.e. contains a Kähler current. The class does not depend on the metric or the
atlas (`SchemeLineBundleMetric.chernClass_independent`); the canonical structural metric is
used. -/
def HasBigChernClass (E : ClosedProjectiveEmbedding f) {L : X.Modules} (a : LineBundleAtlas L) :
    Prop :=
  letI := E.isSeparated
  letI := E.quasiCompact
  IsBigClass ((schemeLineBundleMetric f n E a).chernClass a)

/-- `HasBigChernClass` can be read with any smooth metric and any atlas. -/
theorem hasBigChernClass_iff (E : ClosedProjectiveEmbedding f) {L : X.Modules}
    (a b : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L) :
    letI := E.isSeparated
    letI := E.quasiCompact
    HasBigChernClass f n E a ↔ IsBigClass (H.chernClass b) := by
  let := E.isSeparated
  let := E.quasiCompact
  unfold HasBigChernClass
  rw [(schemeLineBundleMetric f n E a).chernClass_independent H a b]

end SGPT.LineBundle
