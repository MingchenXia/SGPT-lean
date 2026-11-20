import SGPT.Okounkov.TranscendentalPoleCore
import SGPT.Okounkov.TranscendentalPoleExtension
import SGPT.Foundations.Analysis.Pending.LelongNumberComparison
import SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization

/-!
# Lelong numbers for the interior of the Okounkov body: chart lemmas

Source: DRWNXZ (Darvas--Reboulet--Witt Nyström--Xia--Zhang, *Transcendental Okounkov bodies*),
proof of Proposition 3.4; blueprint node `tok:body-interior` (sub-lemmas
`tok-body2:lelong-restriction`, `tok-body2:lelong-zero`, `tok-body2:cut-extension`,
`tok-body2:pole-lelong` of `claude-tok-body2.tex`).

The valuation of the Kähler currents `ω + ε ddᶜ ψ_k` built from the poles `ψ_k` of the members
`Y_k` of the flag is computed by successive restrictions. This file provides the local facts used
in that computation, for the Lelong number `lelongNumber` of TN (computed in the preferred chart,
`ν(u, x) = sup {γ ≥ 0 : u ≤ γ log ‖z - x‖ + O(1)}`):

* `lelongNumber_le_comp`: Lelong numbers do not decrease under pullback by a map that is
  holomorphic at the point, between manifolds of possibly **different** dimensions (the
  restriction to a submanifold); this generalizes TN's `LelongNumberComparison.lelongNumber_le_comp`
  (same dimension).
* `lelongNumber_eq_zero_of_ne_bot`: a quasi-psh function that is finite at `x` has Lelong number `0`
  at `x` (positive dimension).
* `uscRegularization_cut_eq`: the upper regularization of a function continuous at `x`, cut to
  `-∞` on a set with empty interior, is the function at `x`. Hence the residual extension
  `extensionAcross W (smoothDivisorOffResidual E 0 φ)` of a continuous `φ` along a divisor with
  empty interior is `φ` (`extensionAcross_smoothDivisorOffResidual_zero`).
* `lelongNumber_smul_ge_of_isSubmanifoldPole`: a positive multiple `ε F` of a pole along `V` has
  Lelong number at least `2 ε` at every point of `V` (from the local form
  `F = log ∑_{i ≥ k} |ζ_i|² + O(1)` in a flattening chart, and the Lipschitz bound of the
  flattening at the centre).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalBody2

open Set Filter Asymptotics
open scoped Topology Manifold ENNReal NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization
open SGPT.Foundations.Analysis.Pending.ThetaPshCodimTwoExtension
open SGPT.Foundations.Analysis.Pending.BlowupFlatCoordinates

section Comparison

variable {m n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel m) V]

/-- **Lelong numbers do not decrease under holomorphic pullback** (Demailly, *Complex analytic
and differential geometry*, III.7), for a map `f : V → M` holomorphic at `z` between manifolds
of possibly different dimensions: `ν(u, f z) ≤ ν(u ∘ f, z)`. In charts `‖f z' - f z‖ ≤ c ‖z' - z‖`,
so a bound `u ≤ γ log ‖· - f z‖ + C` pulls back; at the points with `f z' = f z` the value
`u (f z) = -∞` is used (a positive Lelong number forces a pole, hypothesis `hbot`). -/
theorem lelongNumber_le_comp {f : V → M} {z : V}
    (hf : MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) f z) {u : M → EReal}
    (hbot : 0 < lelongNumber (n := n) u (f z) → u (f z) = ⊥) :
    lelongNumber (n := n) u (f z) ≤ lelongNumber (n := m) (fun z' => u (f z')) z := by
  set y := f z
  set d := complexChartAt (n := n) y
  set e := complexChartAt (n := m) z
  have hze : z ∈ e.val.source := mem_complexChartAt_source z
  have hyd : y ∈ d.val.source := mem_complexChartAt_source y
  set F : ComplexModel m → ComplexModel n := fun w => d.val (f (e.val.symm w))
  have hFd : DifferentiableAt ℂ F (e.val z) := by
    have h := hf.differentiableWithinAt_writtenInExtChartAt
    simp only [modelWithCornersSelf_coe, range_id, differentiableWithinAt_univ] at h
    exact h
  obtain ⟨c, hc, hcw⟩ := hFd.hasFDerivAt.isBigO_sub.exists_pos
  have hlip : ∀ᶠ z' in 𝓝 z, ‖d.val (f z') - d.val y‖ ≤ c * ‖e.val z' - e.val z‖ := by
    have h1 := (e.val.continuousAt hze).eventually hcw.bound
    filter_upwards [h1, e.val.open_source.mem_nhds hze] with z' hz' hz'e
    simpa [F, e.val.left_inv hz'e, e.val.left_inv hze] using hz'
  have hfc : ContinuousAt f z := hf.continuousAt
  unfold lelongNumber
  refine iSup₂_le fun γ hγC => ?_
  obtain ⟨C, hC⟩ := hγC
  rcases eq_or_ne γ 0 with rfl | hγ0
  · simp
  have hγpos : (0 : ℝ) < γ := by
    have := (pos_iff_ne_zero (a := γ)).mpr hγ0; exact_mod_cast this
  have hybot : u y = ⊥ := hbot (LelongNumberComparison.lelongNumber_pos_of_le_log hγpos hC)
  refine le_iSup₂_of_le (f := fun (γ : ℝ≥0) (_ : ∃ C : ℝ, ∀ᶠ z' in 𝓝[≠] z,
      u (f z') ≤ (((γ : ℝ) * Real.log
        ‖(complexChartAt (n := m) z).val z' - (complexChartAt (n := m) z).val z‖ + C : ℝ) :
          EReal)) => (γ : ℝ≥0∞)) γ ⟨C + γ * Real.log c, ?_⟩ le_rfl
  have hC' : ∀ᶠ z' in 𝓝 z, f z' ≠ y → u (f z') ≤ ((γ * Real.log
      ‖d.val (f z') - d.val y‖ + C : ℝ) : EReal) :=
    hfc.eventually (eventually_nhdsWithin_iff.mp hC)
  have hsrc : ∀ᶠ z' in 𝓝 z, f z' ∈ d.val.source :=
    hfc.eventually (d.val.open_source.mem_nhds hyd)
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hC', hsrc, hlip, e.val.open_source.mem_nhds hze] with z' h1 h2 h3 h4 hz'z
  by_cases hfz : f z' = y
  · rw [hfz, hybot]; exact bot_le
  have hnz : 0 < ‖e.val z' - e.val z‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact fun h => hz'z (e.val.injOn h4 hze h)
  have hny : 0 < ‖d.val (f z') - d.val y‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact fun h => hfz (d.val.injOn h2 hyd h)
  refine (h1 hfz).trans (EReal.coe_le_coe_iff.mpr ?_)
  have hlog : Real.log ‖d.val (f z') - d.val y‖ ≤
      Real.log c + Real.log ‖e.val z' - e.val z‖ := by
    rw [← Real.log_mul hc.ne' hnz.ne']
    exact Real.log_le_log hny h3
  nlinarith [hlog, hγpos]

end Comparison

section Zero

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A `θ`-psh function finite at `x` has Lelong number `0` at `x` (positive dimension): a positive
Lelong number forces `u x = -∞` (TN `eq_bot_of_lelongNumber_pos`). -/
theorem lelongNumber_eq_zero_of_ne_bot (hn : 0 < n) {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hu : ThetaPlurisubharmonic θ u) {x : M} (hx : u x ≠ ⊥) :
    lelongNumber (n := n) u x = 0 :=
  le_antisymm (le_of_not_gt fun h => hx (eq_bot_of_lelongNumber_pos hn hu h)) bot_le

/-- The squared-logarithmic Lelong number (the normalization of `sourceGenericLelongNumber`) of a
`θ`-psh function finite at `x` vanishes. -/
theorem squaredLogLelongNumber_eq_zero_of_ne_bot (hn : 0 < n) {θ : SmoothRealForm n M 2}
    {u : M → EReal} (hu : ThetaPlurisubharmonic θ u) {x : M} (hx : u x ≠ ⊥) :
    squaredLogLelongNumber (n := n) u x = 0 := by
  have h := lelongNumber_eq_two_mul_squaredLog (n := n) hn.ne' u x
  rw [lelongNumber_eq_zero_of_ne_bot hn hu hx] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (by norm_num)

omit [IsComplexManifold n M] in
/-- A lower bound `δ ≤ ν(u, x)` gives `δ / 2 ≤` the squared-logarithmic Lelong number. -/
theorem half_le_squaredLogLelongNumber (hn : n ≠ 0) {u : M → EReal} {x : M} {δ : ℝ≥0∞}
    (h : δ ≤ lelongNumber (n := n) u x) : δ / 2 ≤ squaredLogLelongNumber (n := n) u x := by
  rw [lelongNumber_eq_two_mul_squaredLog hn, mul_comm] at h
  exact ENNReal.div_le_of_le_mul h

end Zero

section Cut

variable {X : Type*} [TopologicalSpace X]

open scoped Classical in
/-- The upper regularization of a function continuous at `x`, cut to `-∞` on a set `K` with
empty interior, is the function itself at `x`. -/
theorem uscRegularization_cut_eq {K : Set X} (hK : interior K = ∅) {φ : X → EReal} {x : X}
    (hφ : ContinuousAt φ x) :
    uscRegularization (fun y => if y ∈ K then ⊥ else φ y) x = φ x := by
  apply le_antisymm
  · refine uscRegularization_le_of_eventually_le hφ.upperSemicontinuousAt
      (Eventually.of_forall fun y => ?_)
    split_ifs
    · exact bot_le
    · exact le_rfl
  · refine le_iInf₂ fun U hU => ?_
    refine le_of_forall_lt fun a ha => ?_
    have hS : {y | a < φ y} ∈ 𝓝 x := hφ.eventually (lt_mem_nhds ha)
    have hUS : U ∩ {y | a < φ y} ∈ 𝓝 x := Filter.inter_mem hU hS
    have hnot : ¬ U ∩ {y | a < φ y} ⊆ K := by
      intro hsub
      have hx : x ∈ interior K := interior_mono hsub (mem_interior_iff_mem_nhds.mpr hUS)
      rw [hK] at hx
      exact hx
    obtain ⟨y, ⟨hyU, hya⟩, hyK⟩ := not_subset.mp hnot
    refine lt_of_lt_of_le hya ?_
    refine le_iSup₂_of_le (f := fun y (_ : y ∈ U) => if y ∈ K then (⊥ : EReal) else φ y) y hyU ?_
    simp [hyK]

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **The residual extension with coefficient `0` of a continuous potential is the potential**:
for a metered divisor `E` with support `W` of empty interior and `φ` continuous at `x`,
`extensionAcross W (smoothDivisorOffResidual E 0 φ) x = φ x`. -/
theorem extensionAcross_smoothDivisorOffResidual_zero
    (E : SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves.MeteredEffectiveQDivisor n M)
    {W : Set M} (hEW : E.support = W) (hW : interior W = ∅) {φ : M → EReal} {x : M}
    (hφ : ContinuousAt φ x) :
    extensionAcross W (SGPT.Okounkov.smoothDivisorOffResidual E 0 φ) x = φ x := by
  classical
  rw [extensionAcross]
  have hfun : (fun y => if y ∈ W then (⊥ : EReal) else
      SGPT.Okounkov.smoothDivisorOffResidual E 0 φ y) =
      fun y => if y ∈ W then (⊥ : EReal) else φ y := by
    funext y
    by_cases hy : y ∈ W
    · simp [hy]
    · have hyE : y ∉ E.support := hEW ▸ hy
      simp [hy, SGPT.Okounkov.smoothDivisorOffResidual, hyE]
  rw [hfun]
  exact uscRegularization_cut_eq hW hφ

end Cut

section Pole

open SGPT.Okounkov.TranscendentalPole

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {omega : KahlerBackground n X} {V : Set X} {F : X → EReal}

/-- `↑ε * a ≤ ↑(ε * b)` for `a ≤ ↑b` and `ε > 0`. -/
theorem coe_mul_le_coe_mul {a : EReal} {b ε : ℝ} (hε : 0 < ε) (h : a ≤ (b : EReal)) :
    (ε : EReal) * a ≤ ((ε * b : ℝ) : EReal) := by
  induction a using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos hε]; exact bot_le
  | top => exact absurd h (not_le.mpr (EReal.coe_lt_top b))
  | coe a =>
      rw [← EReal.coe_mul]
      exact EReal.coe_le_coe_iff.mpr
        (mul_le_mul_of_nonneg_left (EReal.coe_le_coe_iff.mp h) hε.le)

/-- **The local form of a pole gives a logarithmic upper bound in the preferred chart**: if `x` is
a regular point of `V` of dimension `k`, then `F ≤ 2 log ‖z - x‖ + C` near `x` (coordinates of
`complexChartAt x`). The flattening `Φ` of `RegularAtDim` sends `x` to `0`, so
`∑_{i ≥ k} |ζ_i|² ≤ ‖Φ(z)‖² ≤ c² ‖z - x‖²` by the Lipschitz bound of `Φ` at the centre, and
`F = log ∑_{i ≥ k} |ζ_i|² + O(1)` off `V` (`IsSubmanifoldPole.localForm`). -/
theorem exists_log_bound_of_isSubmanifoldPole (hF : IsSubmanifoldPole omega V F) {x : X}
    (hx : x ∈ V) {k : ℕ} (hreg : RegularAtDim (n := n) V x k) :
    ∃ C : ℝ, ∀ᶠ y in 𝓝[≠] x, F y ≤ ((2 * Real.log
      ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖ + C : ℝ) :
        EReal) := by
  obtain ⟨-, -, Φ, hsub, hzero, hflat⟩ := hreg
  have hΦ : IsFlatteningOf V (x₀ := x) Φ k := ⟨hsub, fun hy hyΦ => hflat hy hyΦ⟩
  obtain ⟨U, hU, C, hUC⟩ := hF.localForm x hx k Φ hΦ
  have hxe : x ∈ (complexChartAt (n := n) x).val.source := mem_complexChartAt_source x
  have hp : (complexChartAt (n := n) x).val x ∈ Φ.source := Φ.center_mem_source
  have hdiff : DifferentiableAt ℂ Φ.toFun ((complexChartAt (n := n) x).val x) :=
    Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hp)
  obtain ⟨c, hc, hcw⟩ := hdiff.hasFDerivAt.isBigO_sub.exists_pos
  have hlip : ∀ᶠ y in 𝓝 x, ‖Φ.toFun ((complexChartAt (n := n) x).val y) -
      Φ.toFun ((complexChartAt (n := n) x).val x)‖ ≤
      c * ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖ :=
    ((complexChartAt (n := n) x).val.continuousAt hxe).eventually hcw.bound
  have hΦsrc : ∀ᶠ y in 𝓝 x, (complexChartAt (n := n) x).val y ∈ Φ.source :=
    ((complexChartAt (n := n) x).val.continuousAt hxe).eventually
      (Φ.isOpen_source.mem_nhds hp)
  refine ⟨C + 2 * Real.log c, ?_⟩
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hU, hlip, hΦsrc, (complexChartAt (n := n) x).val.open_source.mem_nhds hxe]
    with y hyU hyl hyΦ hys hyx
  by_cases hyV : y ∈ V
  · rw [(hF.eq_bot_iff y).mpr hyV]; exact bot_le
  have hFne : F y ≠ ⊥ := fun h => hyV ((hF.eq_bot_iff y).mp h)
  have hFy : F y = (((F y).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal (hF.ne_top y) hFne).symm
  have hb := hUC y hyU hyV
  -- the flattened point is off the coordinate plane
  have hnotplane : Φ.toFun ((complexChartAt (n := n) x).val y) ∉ complexCoordinatePlane n k :=
    fun h => hyV ((hflat hys hyΦ).mpr h)
  have hw_eq : flatNormalWeight Φ k y = ∑ i : Fin n,
      if k ≤ i.1 then Complex.normSq (Φ.toFun ((complexChartAt (n := n) x).val y) i) else 0 :=
    rfl
  have hw_pos : 0 < flatNormalWeight Φ k y := by
    rw [hw_eq]
    simp only [complexCoordinatePlane, mem_ofPred_eq, not_forall] at hnotplane
    obtain ⟨i, hik, hi⟩ := hnotplane
    refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
    · split_ifs
      · exact Complex.normSq_nonneg _
      · exact le_rfl
    · rw [if_pos hik]
      exact Complex.normSq_pos.mpr hi
  have hw_le : flatNormalWeight Φ k y ≤ ‖Φ.toFun ((complexChartAt (n := n) x).val y)‖ ^ 2 := by
    rw [hw_eq, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_le_sum fun i _ => ?_
    split_ifs
    · rw [Complex.normSq_eq_norm_sq]
    · exact sq_nonneg _
  have hz0 : Φ.toFun ((complexChartAt (n := n) x).val x) = 0 := hzero
  have hzl : ‖Φ.toFun ((complexChartAt (n := n) x).val y)‖ ≤
      c * ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖ := by
    simpa only [hz0, sub_zero] using hyl
  have hd_pos : 0 < ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact fun h => hyx ((complexChartAt (n := n) x).val.injOn hys hxe h)
  have hlog : Real.log (flatNormalWeight Φ k y) ≤ 2 * Real.log c +
      2 * Real.log ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖ := by
    have h1 : flatNormalWeight Φ k y ≤
        (c * ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖) ^ 2 :=
      hw_le.trans (pow_le_pow_left₀ (norm_nonneg _) hzl 2)
    have h2 := Real.log_le_log hw_pos h1
    rw [Real.log_pow, Real.log_mul hc.ne' hd_pos.ne'] at h2
    push_cast at h2
    linarith
  rw [hFy]
  refine EReal.coe_le_coe_iff.mpr ?_
  have := (abs_le.mp hb).2
  linarith

/-- **Lelong numbers of a multiple of a pole**: for `ε > 0`, the Lelong number of `ε F` at every
point of `V` is at least `2 ε`, provided every point of `V` is regular (of some dimension). -/
theorem lelongNumber_smul_ge_of_isSubmanifoldPole (hF : IsSubmanifoldPole omega V F)
    (hreg : ∀ x ∈ V, ∃ k, RegularAtDim (n := n) V x k) {ε : ℝ} (hε : 0 < ε) :
    ∀ x ∈ V, ((Real.toNNReal (2 * ε) : ℝ≥0) : ℝ≥0∞) ≤
      lelongNumber (n := n) (fun y => (ε : EReal) * F y) x := by
  intro x hx
  obtain ⟨k, hk⟩ := hreg x hx
  obtain ⟨C, hC⟩ := exists_log_bound_of_isSubmanifoldPole hF hx hk
  unfold lelongNumber
  refine le_iSup₂_of_le (f := fun (γ : ℝ≥0) (_ : ∃ C : ℝ, ∀ᶠ y in 𝓝[≠] x,
      (ε : EReal) * F y ≤ (((γ : ℝ) * Real.log
        ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖ + C : ℝ) :
          EReal)) => (γ : ℝ≥0∞)) (Real.toNNReal (2 * ε)) ⟨ε * C, ?_⟩ le_rfl
  filter_upwards [hC] with y hy
  have h := coe_mul_le_coe_mul hε hy
  rw [Real.coe_toNNReal _ (by positivity)]
  refine h.trans (le_of_eq ?_)
  congr 1
  ring

end Pole

end SGPT.Okounkov.TranscendentalBody2
