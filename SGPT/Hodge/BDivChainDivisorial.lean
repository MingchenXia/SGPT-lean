import SGPT.Hodge.ConeWeak
import SGPT.BDivisor.BlowupModel2Order
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Dominated convergence of Siu divisorial parts

Infrastructure for `prop:dscontbdiv` (chapter *The theory of b-divisors*).  On a compact complex
manifold `M`, the divisorial part `Div T = ∑_D ν(T, D)[D]` of Siu's decomposition is the weak sum
of a series over **all** prime divisors (`SGPT.Siu.hasSum_siuDivisorialPart`).  Here:

* `tendsto_siuDivisorialPart_inChart_of_dominated`: **Tannery's theorem for divisorial parts.**
  If `ν(S_i, D) → ν(S, D)` for every prime divisor `D` and, eventually, `ν(S_i, D) ≤ ν(G, D)` for
  all `D` and a fixed closed positive current `G`, then `Div S_i → Div S` on every chart test form
  (along an arbitrary filter).  The dominating series `∑_D ν(G, D)|[D](η)|` converges because the
  real series `∑_D ν(G, D)[D](η)` converges unconditionally.
* `weakTendsto_siuDivisorialPart_of_dominated`, `tendsto_bottChernClass_siuDivisorialPart`: the
  sequential version, and the resulting convergence of the classes `{Div S_k} → {Div S}` in the
  Euclidean topology of `H^{1,1}(M, ℝ)` (weak continuity of the class map,
  `SGPT.Hodge.tendsto_bottChernClass_of_tendsto`), `M` compact connected Kähler.

This replaces the book's "finite-tail argument" (`eq:Regpivarphij_conv_temp1`): the tails of the
Siu series are controlled termwise by a single summable majorant, so no enumeration of the
countably many primes with positive Lelong number is needed.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Hodge.BDivChain

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass

section Divisorial

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M] [CompactSpace M]

local notation "Cur" => GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))

/-- The terms of the Siu series on a chart test form: `(ν(T, D)[D])(η) = ν(T, D) · [D](η)`. -/
theorem siuTerm_inChart (T : Cur) (hT : SGPT.Siu.IsClosedPositiveCurrent T)
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) (e : ComplexChart (m + 1) M)
    (η : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget e)
      (Module.finrank ℝ (ComplexModel (m + 1)) - 2)) :
    ((SGPT.Siu.currentGenericLelong T hT D).toReal • SGPT.Siu.primeDivisorCurrent D).inChart e η =
      (SGPT.Siu.currentGenericLelong T hT D).toReal *
        (SGPT.Siu.primeDivisorCurrent D).inChart e η := by
  rw [GlobalCurrent.inChart_smul, smul_apply, smul_eq_mul]

/-- **Tannery's theorem for Siu divisorial parts.** Let `S_i` (`i` along a filter `l`) and `S` be
closed positive `(1,1)`-currents on `M` such that `ν(S_i, D) → ν(S, D)` for every prime divisor
`D`, and such that eventually `ν(S_i, D) ≤ ν(G, D)` for every `D`, for a fixed closed positive
current `G`.  Then `Div S_i → Div S` on every chart test form. -/
theorem tendsto_siuDivisorialPart_inChart_of_dominated {ι : Type*} {l : Filter ι}
    {S : ι → Cur} (hS : ∀ i, SGPT.Siu.IsClosedPositiveCurrent (S i)) {S₀ : Cur}
    (hS₀ : SGPT.Siu.IsClosedPositiveCurrent S₀) {G : Cur} (hG : SGPT.Siu.IsClosedPositiveCurrent G)
    (hlim : ∀ D, Tendsto (fun i => SGPT.Siu.currentGenericLelong (S i) (hS i) D) l
      (𝓝 (SGPT.Siu.currentGenericLelong S₀ hS₀ D)))
    (hdom : ∀ᶠ i in l, ∀ D, SGPT.Siu.currentGenericLelong (S i) (hS i) D ≤
      SGPT.Siu.currentGenericLelong G hG D)
    (e : ComplexChart (m + 1) M)
    (η : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget e)
      (Module.finrank ℝ (ComplexModel (m + 1)) - 2)) :
    Tendsto (fun i => (SGPT.Siu.siuDivisorialPart (S i) (hS i)).inChart e η) l
      (𝓝 ((SGPT.Siu.siuDivisorialPart S₀ hS₀).inChart e η)) := by
  have hsum : ∀ (T : Cur) (hT : SGPT.Siu.IsClosedPositiveCurrent T),
      (SGPT.Siu.siuDivisorialPart T hT).inChart e η =
        ∑' D, (SGPT.Siu.currentGenericLelong T hT D).toReal *
          (SGPT.Siu.primeDivisorCurrent D).inChart e η := by
    intro T hT
    rw [← (SGPT.Siu.hasSum_siuDivisorialPart hT e η).tsum_eq]
    exact tsum_congr fun D => siuTerm_inChart T hT D e η
  have hG' := SGPT.Siu.hasSum_siuDivisorialPart hG e η
  have hbound : Summable fun D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M =>
      ‖(SGPT.Siu.currentGenericLelong G hG D).toReal *
        (SGPT.Siu.primeDivisorCurrent D).inChart e η‖ :=
    (hG'.summable.congr fun D => siuTerm_inChart G hG D e η).norm
  simp only [hsum]
  refine tendsto_tsum_of_dominated_convergence hbound (fun D => ?_) ?_
  · exact ((ENNReal.tendsto_toReal (SGPT.Siu.currentGenericLelong_ne_top hS₀ D)).comp
      (hlim D)).mul_const _
  · filter_upwards [hdom] with i hi D
    rw [norm_mul, norm_mul, Real.norm_of_nonneg ENNReal.toReal_nonneg,
      Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul_of_nonneg_right
      (ENNReal.toReal_mono (SGPT.Siu.currentGenericLelong_ne_top hG D) (hi D)) (norm_nonneg _)

/-- The divisorial part as a closed `(1,1)`-current. -/
def siuDivisorialClosed (T : Cur) (hT : SGPT.Siu.IsClosedPositiveCurrent T) :
    ClosedOneOneCurrent (M := M) (canonicalBasis (m + 1)) (Nat.succ_pos m) :=
  ⟨SGPT.Siu.siuDivisorialPart T hT, (SGPT.Siu.isClosedPositiveCurrent_siuDivisorialPart hT).1,
    (SGPT.Siu.isClosedPositiveCurrent_siuDivisorialPart hT).2.1⟩

/-- The sequential version: weak convergence of the divisorial parts. -/
theorem weakTendsto_siuDivisorialPart_of_dominated {S : ℕ → Cur}
    (hS : ∀ k, SGPT.Siu.IsClosedPositiveCurrent (S k)) {S₀ : Cur}
    (hS₀ : SGPT.Siu.IsClosedPositiveCurrent S₀) {G : Cur} (hG : SGPT.Siu.IsClosedPositiveCurrent G)
    (hlim : ∀ D, Tendsto (fun k => SGPT.Siu.currentGenericLelong (S k) (hS k) D) atTop
      (𝓝 (SGPT.Siu.currentGenericLelong S₀ hS₀ D)))
    (hdom : ∀ᶠ k in atTop, ∀ D, SGPT.Siu.currentGenericLelong (S k) (hS k) D ≤
      SGPT.Siu.currentGenericLelong G hG D) :
    WeakTendsto (fun k => siuDivisorialClosed (S k) (hS k)) (siuDivisorialClosed S₀ hS₀) :=
  fun e η => tendsto_siuDivisorialPart_inChart_of_dominated hS hS₀ hG hlim hdom e η

variable [ConnectedSpace M]

/-- **Convergence of the classes of the divisorial parts** in the Euclidean topology of
`H^{1,1}(M, ℝ)`, `M` compact connected Kähler, under the hypotheses of
`tendsto_siuDivisorialPart_inChart_of_dominated` (for sequences). -/
theorem tendsto_bottChernClass_siuDivisorialPart (w : KahlerBackground (m + 1) M)
    {S : ℕ → Cur} (hS : ∀ k, SGPT.Siu.IsClosedPositiveCurrent (S k)) {S₀ : Cur}
    (hS₀ : SGPT.Siu.IsClosedPositiveCurrent S₀) {G : Cur} (hG : SGPT.Siu.IsClosedPositiveCurrent G)
    (hlim : ∀ D, Tendsto (fun k => SGPT.Siu.currentGenericLelong (S k) (hS k) D) atTop
      (𝓝 (SGPT.Siu.currentGenericLelong S₀ hS₀ D)))
    (hdom : ∀ᶠ k in atTop, ∀ D, SGPT.Siu.currentGenericLelong (S k) (hS k) D ≤
      SGPT.Siu.currentGenericLelong G hG D) :
    Tendsto (fun k => bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
        (siuDivisorialClosed (S k) (hS k))) atTop
      (@nhds _ (SGPT.BDivisor.euclideanTopology (RealBottChern (m + 1) M))
        (bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) (siuDivisorialClosed S₀ hS₀))) :=
  tendsto_bottChernClass_of_tendsto w
    (fun k => (SGPT.Siu.isClosedPositiveCurrent_siuDivisorialPart (hS k)).2.2)
    (weakTendsto_siuDivisorialPart_of_dominated hS hS₀ hG hlim hdom)

end Divisorial

end SGPT.Hodge.BDivChain
