import SGPT.NAPotential.BerkovichAnalytification
import SGPT.PSH.NativeThetaCompactMaximum
import SGPT.Foundations.Analysis.Pending.EndpointMixedMassConvexCombination

/-! # Piecewise linear curves and their analytification

Source `def:piecewiselincurv` (`chapter_NApotential.tex`, Section *The transcendental setting*):
for `A_0, …, A_N ∈ PSH(X, θ)` and `τ_0 > τ_1 > ⋯ > τ_N`, the *piecewise linear curve*
`A = (A_τ)_{τ ∈ ℝ}` in `PSH(X, θ) ∪ {-∞}` is the affine interpolation of these data:

1. `A_{τ_i} = A_i`;
2. `A_τ = A_{τ_N}` for `τ ≤ τ_N`;
3. `A_{(1-t) τ_i + t τ_{i+1}} = (1-t) A_{τ_i} + t A_{τ_{i+1}}` for `t ∈ (0, 1)`, `i < N`;
4. `A_τ ≡ -∞` for `τ > τ_0`.

Its analytification is `A^An(v) := sup_{τ ≤ τ_0} (A_τ^An(v) + τ) = max_i (A_{τ_i}^An(v) + τ_i)`.

## Main results

* `PiecewiseLinearData θ`: the data `(A_i, τ_i)`; `PiecewiseLinearData.curve`: the curve.
* `curve_tau`, `curve_of_le_last`, `curve_affine`, `curve_of_lt`: clauses 1–4.
* `curve_unique`: clauses 1–4 determine the curve (so the definition is well posed).
* `isThetaPSH_curve`: `A_τ ∈ PSH(X, θ)` for `τ ≤ τ_0` (so `A` is a curve in `PSH(X, θ) ∪ {-∞}`).
* `PiecewiseLinearData.curveAn`: `A^An(v) = sup_{τ ≤ τ_0} (A_τ^An(v) + τ)` on `X^An` (for
  `X(ℂ)` the complex points of a smooth projective scheme, `φ^An` as in
  `SGPT.NAPotential.Berkovich.potentialAn`), and `le_curveAn`:
  `max_i (A_{τ_i}^An(v) + τ_i) ≤ A^An(v)`.  The reverse inequality (the second equality of
  `eq:psianvlinear`) needs the concavity `((1-t)φ + tψ)^An ≤ (1-t)φ^An + tψ^An`, i.e. the
  subadditivity of algebraized multiplier ideals and the homogeneity `v(cφ) = c v(φ)`; it is not
  formalized.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.Berkovich

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The data `A_0, …, A_N ∈ PSH(X, θ)` and `τ_0 > ⋯ > τ_N` of a piecewise linear curve. -/
structure PiecewiseLinearData (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) where
  /-- The number `N` of segments. -/
  N : ℕ
  /-- The potentials `A_i`. -/
  A : Fin (N + 1) → M → EReal
  isThetaPSH : ∀ i, (ofFixedModel n M).IsThetaPSH θ (A i)
  /-- The nodes `τ_i`. -/
  τ : Fin (N + 1) → ℝ
  strictAnti : StrictAnti τ

namespace PiecewiseLinearData

variable {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} (D : PiecewiseLinearData θ)

theorem tau_le_tau_zero (i : Fin (D.N + 1)) : D.τ i ≤ D.τ 0 :=
  D.strictAnti.antitone (Fin.zero_le i)

theorem tau_last_le (i : Fin (D.N + 1)) : D.τ (Fin.last D.N) ≤ D.τ i :=
  D.strictAnti.antitone (Fin.le_last i)

/-- For `s ≤ τ_0`, the largest index `i` with `s ≤ τ_i`. -/
def segIndex (s : ℝ) (hs : s ≤ D.τ 0) : Fin (D.N + 1) :=
  (Finset.univ.filter fun i => s ≤ D.τ i).max' ⟨0, by simp [hs]⟩

theorem le_tau_segIndex (s : ℝ) (hs : s ≤ D.τ 0) : s ≤ D.τ (D.segIndex s hs) := by
  have := Finset.max'_mem (Finset.univ.filter fun i => s ≤ D.τ i) ⟨0, by simp [hs]⟩
  exact (Finset.mem_filter.mp this).2

theorem tau_lt_of_segIndex_lt (s : ℝ) (hs : s ≤ D.τ 0) {j : Fin (D.N + 1)}
    (hj : D.segIndex s hs < j) : D.τ j < s := by
  by_contra h
  have h : s ≤ D.τ j := not_lt.mp h
  have := Finset.le_max' (Finset.univ.filter fun i => s ≤ D.τ i) j (by simp [h])
  exact absurd hj (not_lt.mpr this)

theorem segIndex_eq (s : ℝ) (hs : s ≤ D.τ 0) {i : Fin (D.N + 1)} (hi : s ≤ D.τ i)
    (hj : ∀ j, i < j → D.τ j < s) : D.segIndex s hs = i := by
  apply le_antisymm
  · by_contra h
    have h : i < D.segIndex s hs := not_le.mp h
    exact absurd (D.le_tau_segIndex s hs) (not_le.mpr (hj _ h))
  · exact Finset.le_max' _ i (by simp [hi])

/-- The next node after `i < N`. -/
def nextIdx (i : Fin (D.N + 1)) (hi : i.val < D.N) : Fin (D.N + 1) := ⟨i.val + 1, by omega⟩

theorem lt_nextIdx (i : Fin (D.N + 1)) (hi : i.val < D.N) : i < D.nextIdx i hi := by
  simp [nextIdx, Fin.lt_def]

/-- The interpolation parameter `t = (τ_i - s)/(τ_i - τ_{i+1})` on the segment `[τ_{i+1}, τ_i]`. -/
def param (i : Fin (D.N + 1)) (hi : i.val < D.N) (s : ℝ) : ℝ :=
  (D.τ i - s) / (D.τ i - D.τ (D.nextIdx i hi))

theorem param_congr {i i' : Fin (D.N + 1)} (h : i = i') (hi : i.val < D.N) (hi' : i'.val < D.N)
    (s : ℝ) : D.param i hi s = D.param i' hi' s := by
  subst h
  rfl

theorem nextIdx_congr {i i' : Fin (D.N + 1)} (h : i = i') (hi : i.val < D.N) (hi' : i'.val < D.N) :
    D.nextIdx i hi = D.nextIdx i' hi' := by
  subst h
  rfl

/-- The pointwise affine combination `(1-t) u + t w` in `[-∞, ∞]`. -/
def affineComb (t : ℝ) (u w : M → EReal) : M → EReal :=
  fun x => ((1 - t : ℝ) : EReal) * u x + (t : EReal) * w x

/-- Source `def:piecewiselincurv`: the piecewise linear curve `A_τ` (`τ ∈ ℝ`). -/
def curve (s : ℝ) : M → EReal :=
  if h : D.τ 0 < s then fun _ => ⊥
  else if hi : (D.segIndex s (not_lt.mp h)).val < D.N then
    affineComb (D.param _ hi s) (D.A (D.segIndex s (not_lt.mp h)))
      (D.A (D.nextIdx _ hi))
  else D.A (D.segIndex s (not_lt.mp h))

/-- Clause 4: `A_τ ≡ -∞` for `τ > τ_0`. -/
theorem curve_of_lt {s : ℝ} (hs : D.τ 0 < s) : D.curve s = fun _ => ⊥ := by
  simp [curve, hs]

theorem segIndex_tau (i : Fin (D.N + 1)) : D.segIndex (D.τ i) (D.tau_le_tau_zero i) = i :=
  D.segIndex_eq _ _ le_rfl fun _ hj => D.strictAnti hj

/-- Clause 1: `A_{τ_i} = A_i`. -/
theorem curve_tau (i : Fin (D.N + 1)) : D.curve (D.τ i) = D.A i := by
  have h : ¬ D.τ 0 < D.τ i := not_lt.mpr (D.tau_le_tau_zero i)
  unfold curve
  rw [dif_neg h]
  have hseg := D.segIndex_tau i
  split_ifs with hi
  · funext x
    have hp : D.param (D.segIndex (D.τ i) (not_lt.mp h)) hi (D.τ i) = 0 := by
      simp [param, hseg]
    simp only [affineComb, hp, sub_zero, EReal.coe_one, one_mul, EReal.coe_zero, zero_mul,
      add_zero]
    rw [hseg]
  · rw [hseg]

/-- Clause 2: `A_τ = A_{τ_N}` for `τ ≤ τ_N`. -/
theorem curve_of_le_last {s : ℝ} (hs : s ≤ D.τ (Fin.last D.N)) :
    D.curve s = D.A (Fin.last D.N) := by
  have h : ¬ D.τ 0 < s := not_lt.mpr (hs.trans (D.tau_le_tau_zero _))
  have hseg : D.segIndex s (not_lt.mp h) = Fin.last D.N :=
    D.segIndex_eq _ _ hs fun j hj => absurd hj (not_lt.mpr (Fin.le_last j))
  unfold curve
  rw [dif_neg h]
  split_ifs with hi
  · rw [hseg] at hi
    simp at hi
  · rw [hseg]

/-- Clause 3: `A_{(1-t) τ_i + t τ_{i+1}} = (1-t) A_{τ_i} + t A_{τ_{i+1}}` for `t ∈ (0, 1)`. -/
theorem curve_affine (i : Fin (D.N + 1)) (hi : i.val < D.N) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    D.curve ((1 - t) * D.τ i + t * D.τ (D.nextIdx i hi)) =
      affineComb t (D.A i) (D.A (D.nextIdx i hi)) := by
  set j := D.nextIdx i hi
  have hij : D.τ j < D.τ i := D.strictAnti (D.lt_nextIdx i hi)
  set s := (1 - t) * D.τ i + t * D.τ j
  have hs1 : s < D.τ i := by nlinarith
  have hs2 : D.τ j < s := by nlinarith
  have h : ¬ D.τ 0 < s := not_lt.mpr (hs1.le.trans (D.tau_le_tau_zero i))
  have hseg : D.segIndex s (not_lt.mp h) = i := by
    apply D.segIndex_eq _ _ hs1.le
    intro k hk
    have hjk : j ≤ k := by
      simp only [j, nextIdx, Fin.le_def, Fin.lt_def] at hk ⊢
      omega
    exact lt_of_le_of_lt (D.strictAnti.antitone hjk) hs2
  unfold curve
  rw [dif_neg h]
  have hi' : (D.segIndex s (not_lt.mp h)).val < D.N := by rw [hseg]; exact hi
  rw [dif_pos hi']
  have hp : D.param (D.segIndex s (not_lt.mp h)) hi' s = t := by
    rw [D.param_congr hseg hi' hi]
    have hne : D.τ i - D.τ j ≠ 0 := by linarith
    change (D.τ i - s) / (D.τ i - D.τ j) = t
    rw [div_eq_iff hne]
    simp only [s]
    ring
  have hn : D.nextIdx (D.segIndex s (not_lt.mp h)) hi' = j := D.nextIdx_congr hseg hi' hi
  rw [hp, hn, hseg]

/-- The four clauses determine the curve: any family satisfying them is `D.curve`. -/
theorem curve_unique (B : ℝ → M → EReal) (h1 : ∀ i, B (D.τ i) = D.A i)
    (h2 : ∀ s, s ≤ D.τ (Fin.last D.N) → B s = D.A (Fin.last D.N))
    (h3 : ∀ (i : Fin (D.N + 1)) (hi : i.val < D.N) (t : ℝ), 0 < t → t < 1 →
      B ((1 - t) * D.τ i + t * D.τ (D.nextIdx i hi)) =
        affineComb t (D.A i) (D.A (D.nextIdx i hi)))
    (h4 : ∀ s, D.τ 0 < s → B s = fun _ => ⊥) : B = D.curve := by
  funext s
  by_cases hs0 : D.τ 0 < s
  · rw [h4 s hs0, D.curve_of_lt hs0]
  have hs : s ≤ D.τ 0 := not_lt.mp hs0
  set i := D.segIndex s hs
  have hle : s ≤ D.τ i := D.le_tau_segIndex s hs
  rcases hle.lt_or_eq with hlt | heq
  · by_cases hi : i.val < D.N
    · set j := D.nextIdx i hi
      have hjs : D.τ j < s := D.tau_lt_of_segIndex_lt s hs (D.lt_nextIdx i hi)
      have hij : D.τ j < D.τ i := hjs.trans hlt
      set t := (D.τ i - s) / (D.τ i - D.τ j)
      have hden : 0 < D.τ i - D.τ j := by linarith
      have ht0 : 0 < t := div_pos (by linarith) hden
      have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
      have hst : s = (1 - t) * D.τ i + t * D.τ j := by
        simp only [t]
        field_simp
        ring
      rw [hst, h3 i hi t ht0 ht1, D.curve_affine i hi ht0 ht1]
    · have hlast : i = Fin.last D.N := by
        ext
        simp only [Fin.val_last]
        omega
      have : s ≤ D.τ (Fin.last D.N) := hlast ▸ hle
      rw [h2 s this, D.curve_of_le_last this]
  · rw [heq, h1, D.curve_tau]

/-- `A_τ ∈ PSH(X, θ)` for `τ ≤ τ_0`. -/
theorem isThetaPSH_curve {s : ℝ} (hs : s ≤ D.τ 0) :
    (ofFixedModel n M).IsThetaPSH θ (D.curve s) := by
  have h : ¬ D.τ 0 < s := not_lt.mpr hs
  unfold curve
  rw [dif_neg h]
  split_ifs with hi
  · set i := D.segIndex s (not_lt.mp h)
    set j := D.nextIdx i hi
    have hjs : D.τ j < s := D.tau_lt_of_segIndex_lt s _ (D.lt_nextIdx i hi)
    have his : s ≤ D.τ i := D.le_tau_segIndex s _
    have hden : 0 < D.τ i - D.τ j := by linarith
    have ht0 : 0 ≤ D.param i hi s := div_nonneg (by linarith) hden.le
    have ht1 : D.param i hi s ≤ 1 := (div_le_one hden).mpr (by linarith)
    have hc : affineComb (D.param i hi s) (D.A i) (D.A j) =
        ThetaPshConvexCombination.convexComb (D.param i hi s) (D.A j) (D.A i) := by
      funext x
      rw [ThetaPshConvexCombination.convexComb_apply]
      exact add_comm _ _
    rw [hc, isThetaPSH_iff_nativeThetaPotential]
    exact EndpointMixedMassConvexCombination.isThetaPshPotential_convexComb_closed
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp (D.isThetaPSH j))
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp (D.isThetaPSH i)) ht0 ht1
  · exact D.isThetaPSH _

end PiecewiseLinearData

/-! ### The analytification `A^An` -/

section Analytification

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (k : ℕ) [SmoothOfRelativeDimension k f]
  (E : ClosedProjectiveEmbedding f) [IsProper f]

local instance berkovichPLPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance berkovichPLPointCharts : ChartedSpace (ComplexModel k) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f k
local instance berkovichPLPointManifold : IsComplexManifold k (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f k

namespace PiecewiseLinearData

variable {θ : AtlasClosedRealOneOneForm (ofFixedModel k (SchemeComplexPoint f))}
  (D : PiecewiseLinearData θ)

/-- Source `eq:psianvlinear`: `A^An(v) := sup_{τ ≤ τ_0} (A_τ^An(v) + τ)`. -/
def curveAn (v : BerkovichPoint f) : EReal :=
  ⨆ s : ℝ, ⨆ (_ : s ≤ D.τ 0), potentialAn k E (D.curve s) v + (s : EReal)

/-- `max_i (A_{τ_i}^An(v) + τ_i) ≤ A^An(v)` (one half of the second equality of
`eq:psianvlinear`). -/
theorem le_curveAn (v : BerkovichPoint f) (i : Fin (D.N + 1)) :
    potentialAn k E (D.A i) v + (D.τ i : EReal) ≤ D.curveAn k E v := by
  rw [← D.curve_tau i]
  exact le_iSup₂_of_le (D.τ i) (D.tau_le_tau_zero i) le_rfl

end PiecewiseLinearData

end Analytification

end SGPT.NAPotential.Berkovich

end
