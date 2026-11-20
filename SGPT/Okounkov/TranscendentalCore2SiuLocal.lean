import SGPT.Okounkov.TranscendentalCoreSiuLocal
import SGPT.Foundations.Analysis.Pending.ThetaPshCodimTwoExtension

/-!
# Local tools for subtracting a prime divisor from an analytic potential

Auxiliary for blueprint node `tok:siu-analytic` (DRWNXZ Lemma 2.3) in the general case of a
possibly singular prime divisor (sub-lemmas `tok-core2:factor`, `tok-core2:cut-bounds`,
`tok-core2:power-family` of `claude-tok-core2.tex`).

* `exists_eq_pow_mul_of_log_le` (**division by a power of a local equation**): let `G` be
  holomorphic near `z`, with zero set of empty interior near `z`, generating the holomorphic germs
  at `z` that vanish on `{G = 0}`. If `F` is holomorphic near `z` and
  `log |F|² ≤ e log |G|² + C` off `{G = 0}` near `z`, with `e > k - 1`, then `F = G^k H` near `z`
  with `H` holomorphic. No Riemann extension theorem is needed: the bound forces `F` to vanish on
  `{G = 0}`, so `F = A G`, and `A` satisfies the bound with `e - 1`.
* `uscRegularization_cut_le`, `le_uscRegularization_cut`: two-sided bounds for the upper
  regularization of a function cut to `-∞` on a set `K` (the lower bound where every
  neighbourhood of the point meets the complement of `K`).
* `continuousAt_generatorLog`, `exists_eventually_le_of_hasAnalyticSingularityTypeAt`:
  `log ∑ |H_i|²` is continuous (as an extended-real function) where the `H_i` are, and a function with analytic
  singularity type is locally bounded above.
* `generatorLog_powerFamily`: the products `∏_{j < L} f_{β(j)}` of `L` members of a finite family
  satisfy `log ∑_β |∏_j f_{β j}|² = L log ∑_i |f_i|²`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalCore2

open Set Filter
open scoped Topology ENNReal NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

section Factor

variable {n : ℕ}

/-- **Division by a power of a local equation** (blueprint `tok-core2:factor`). -/
theorem exists_eq_pow_mul_of_log_le {G : ComplexModel n → ℂ} {z : ComplexModel n}
    (hG : ∀ᶠ w in 𝓝 z, ContinuousAt G w)
    (hnd : ∀ᶠ w in 𝓝 z, ∀ U ∈ 𝓝 w, ∃ w' ∈ U, G w' ≠ 0)
    (hideal : ∀ F : ComplexModel n → ℂ, (∀ᶠ w in 𝓝 z, DifferentiableAt ℂ F w) →
      (∀ᶠ w in 𝓝 z, G w = 0 → F w = 0) →
        ∃ A : ComplexModel n → ℂ, (∀ᶠ w in 𝓝 z, DifferentiableAt ℂ A w) ∧
          F =ᶠ[𝓝 z] fun w => A w * G w) :
    ∀ (k : ℕ) (F : ComplexModel n → ℂ) (e C : ℝ), (k : ℝ) - 1 < e →
      (∀ᶠ w in 𝓝 z, DifferentiableAt ℂ F w) →
      (∀ᶠ w in 𝓝 z, G w ≠ 0 → F w ≠ 0 →
        Real.log (‖F w‖ ^ 2) ≤ e * Real.log (‖G w‖ ^ 2) + C) →
      ∃ H : ComplexModel n → ℂ, (∀ᶠ w in 𝓝 z, DifferentiableAt ℂ H w) ∧
        F =ᶠ[𝓝 z] fun w => G w ^ k * H w := by
  intro k
  induction k with
  | zero =>
      intro F e C _ hF _
      exact ⟨F, hF, Eventually.of_forall fun w => by simp⟩
  | succ k ih =>
      intro F e C hek hF hbound
      have he : 0 < e := by
        push_cast at hek
        linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      -- `F` vanishes on the zero set of `G`
      have hvan : ∀ᶠ w in 𝓝 z, G w = 0 → F w = 0 := by
        obtain ⟨O, hOsub, hO, hzO⟩ := _root_.mem_nhds_iff.mp (hF.and (hG.and (hnd.and hbound)))
        filter_upwards [hO.mem_nhds hzO] with w hwO hGw
        by_contra hFw
        obtain ⟨hFd, hGc, hndw, -⟩ := hOsub hwO
        have hFpos : 0 < ‖F w‖ ^ 2 := by positivity
        set L₀ : ℝ := Real.log (‖F w‖ ^ 2 / 4) with hL₀
        have hFnear : ∀ᶠ w' in 𝓝 w, ‖F w‖ ^ 2 / 4 < ‖F w'‖ ^ 2 := by
          have hc : ContinuousAt (fun w' => ‖F w'‖ ^ 2) w :=
            (hFd.continuousAt.norm).pow 2
          exact hc.eventually (lt_mem_nhds (by linarith))
        have hGnear : ∀ᶠ w' in 𝓝 w, ‖G w'‖ ^ 2 < Real.exp ((L₀ - C) / e) := by
          have hc : ContinuousAt (fun w' => ‖G w'‖ ^ 2) w := (hGc.norm).pow 2
          have h0 : ‖G w‖ ^ 2 < Real.exp ((L₀ - C) / e) := by
            rw [hGw, norm_zero]; simpa using Real.exp_pos _
          exact hc.eventually (gt_mem_nhds h0)
        obtain ⟨w', ⟨h1, h2, h3⟩, hGw'⟩ :=
          hndw _ (hFnear.and (hGnear.and (hO.mem_nhds hwO)))
        have hFw' : F w' ≠ 0 := by
          intro h0
          rw [h0, norm_zero] at h1
          linarith
        have hb := (hOsub h3).2.2.2 hGw' hFw'
        have hlogF : L₀ < Real.log (‖F w'‖ ^ 2) := Real.log_lt_log (by positivity) h1
        have hlogG : Real.log (‖G w'‖ ^ 2) < (L₀ - C) / e := by
          rw [← Real.log_exp ((L₀ - C) / e)]
          exact Real.log_lt_log (by positivity) h2
        have : e * Real.log (‖G w'‖ ^ 2) < L₀ - C := by
          have := mul_lt_mul_of_pos_left hlogG he
          rwa [mul_div_cancel₀ _ he.ne'] at this
        linarith
      obtain ⟨A, hA, hFA⟩ := hideal F hF hvan
      have hbA : ∀ᶠ w in 𝓝 z, G w ≠ 0 → A w ≠ 0 →
          Real.log (‖A w‖ ^ 2) ≤ (e - 1) * Real.log (‖G w‖ ^ 2) + C := by
        filter_upwards [hbound, hFA] with w hb hFAw hGw hAw
        have hFw : F w ≠ 0 := by rw [hFAw]; exact mul_ne_zero hAw hGw
        have h := hb hGw hFw
        rw [hFAw, norm_mul, mul_pow, Real.log_mul (by positivity) (by positivity)] at h
        linarith
      obtain ⟨H, hH, hAH⟩ := ih A (e - 1) C (by push_cast at hek ⊢; linarith) hA hbA
      refine ⟨H, hH, ?_⟩
      filter_upwards [hFA, hAH] with w h1 h2
      rw [h1, h2]
      ring

end Factor

section Cut

variable {X : Type*} [TopologicalSpace X]

open scoped Classical in
/-- Upper bound for a cut regularization: if `φ ≤ ψ` off `K` near `x` and `ψ` is upper
semicontinuous at `x`, then the regularization of `φ` cut to `-∞` on `K` is `≤ ψ x`. -/
theorem uscRegularization_cut_le {K : Set X} {φ ψ : X → EReal} {x : X}
    (hψ : UpperSemicontinuousAt ψ x) (hle : ∀ᶠ y in 𝓝 x, y ∉ K → φ y ≤ ψ y) :
    uscRegularization (fun y => if y ∈ K then ⊥ else φ y) x ≤ ψ x := by
  refine uscRegularization_le_of_eventually_le hψ ?_
  filter_upwards [hle] with y hy
  split_ifs with hyK
  · exact bot_le
  · exact hy hyK

open scoped Classical in
/-- Lower bound for a cut regularization: if `ψ ≤ φ` off `K` near `x`, `ψ` is continuous at `x` and
every neighbourhood of `x` meets the complement of `K`, then `ψ x` is at most the regularization of
`φ` cut to `-∞` on `K`. -/
theorem le_uscRegularization_cut {K : Set X} {φ ψ : X → EReal} {x : X}
    (hK : ∀ U ∈ 𝓝 x, ∃ y ∈ U, y ∉ K) (hψ : ContinuousAt ψ x)
    (hle : ∀ᶠ y in 𝓝 x, y ∉ K → ψ y ≤ φ y) :
    ψ x ≤ uscRegularization (fun y => if y ∈ K then ⊥ else φ y) x := by
  refine le_iInf₂ fun U hU => ?_
  refine le_of_forall_lt fun a ha => ?_
  have hS : {y | a < ψ y} ∈ 𝓝 x := hψ.eventually (lt_mem_nhds ha)
  have hUS : U ∩ ({y | a < ψ y} ∩ {y | y ∉ K → ψ y ≤ φ y}) ∈ 𝓝 x :=
    Filter.inter_mem hU (Filter.inter_mem hS hle)
  obtain ⟨y, ⟨hyU, hya, hyle⟩, hyK⟩ := hK _ hUS
  refine lt_of_lt_of_le (lt_of_lt_of_le hya (hyle hyK)) ?_
  refine le_iSup₂_of_le (f := fun y (_ : y ∈ U) => if y ∈ K then (⊥ : EReal) else φ y) y hyU ?_
  simp [hyK]

end Cut

section PowerFamily

variable {E : Type*}

/-- The family of the products `∏_{j < L} f_{β j}`, `β : Fin L → Fin K`, indexed by `Fin` through
`Fintype.equivFin`. -/
def powerFamily {K : ℕ} (L : ℕ) (f : Fin K → E → ℂ) :
    Fin (Fintype.card (Fin L → Fin K)) → E → ℂ :=
  fun i w => ∏ j : Fin L, f ((Fintype.equivFin (Fin L → Fin K)).symm i j) w

/-- `∑_β |∏_j f_{β j}|² = (∑_i |f_i|²)^L`. -/
theorem sum_norm_sq_powerFamily {K : ℕ} (L : ℕ) (f : Fin K → E → ℂ) (w : E) :
    ∑ i, ‖powerFamily L f i w‖ ^ 2 = (∑ i, ‖f i w‖ ^ 2) ^ L := by
  rw [Fintype.sum_pow]
  rw [← (Fintype.equivFin (Fin L → Fin K)).symm.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [powerFamily, norm_prod, Finset.prod_pow]

/-- **The power family** (blueprint `tok-core2:power-family`):
`log ∑_β |∏_j f_{β j}|² = L log ∑_i |f_i|²`. -/
theorem generatorLog_powerFamily {K : ℕ} (L : ℕ) (f : Fin K → E → ℂ) (w : E) :
    generatorLog (powerFamily L f) w = ((L : ℝ) : EReal) * generatorLog f w := by
  rw [generatorLog_eq_log_sum, generatorLog_eq_log_sum, sum_norm_sq_powerFamily,
    ENNReal.ofReal_pow (Finset.sum_nonneg fun i _ => by positivity), ENNReal.log_pow]
  simp

/-- A member of the power family is at most the sum, squared. -/
theorem norm_sq_powerFamily_le {K : ℕ} (L : ℕ) (f : Fin K → E → ℂ) (w : E)
    (i : Fin (Fintype.card (Fin L → Fin K))) :
    ‖powerFamily L f i w‖ ^ 2 ≤ (∑ i, ‖f i w‖ ^ 2) ^ L := by
  rw [← sum_norm_sq_powerFamily]
  exact Finset.single_le_sum (f := fun i => ‖powerFamily L f i w‖ ^ 2)
    (fun j _ => by positivity) (Finset.mem_univ i)

end PowerFamily

section Continuity

variable {E : Type*} [TopologicalSpace E]

/-- `log ∑ |H_i|²` is continuous (with values in `[-∞, ∞)`) where the `H_i` are continuous. -/
theorem continuousAt_generatorLog {N : ℕ} {H : Fin N → E → ℂ} {w : E}
    (hH : ∀ i, ContinuousAt (H i) w) : ContinuousAt (generatorLog H) w := by
  have hfun : generatorLog H = fun w => ENNReal.log (ENNReal.ofReal (∑ j, ‖H j w‖ ^ 2)) :=
    funext (generatorLog_eq_log_sum H)
  rw [hfun]
  have hsum : ContinuousAt (fun w => ∑ j, ‖H j w‖ ^ 2) w :=
    tendsto_finsetSum _ fun j _ => ((hH j).norm).pow 2
  exact ENNReal.continuous_log.continuousAt.comp
    (ENNReal.continuous_ofReal.continuousAt.comp hsum)

/-- `↑r * log ∑ |H_i|²` is continuous where the `H_i` are, for a real `r ≠ 0`. -/
theorem continuousAt_coe_mul_generatorLog {N : ℕ} {H : Fin N → E → ℂ} {w : E} {r : ℝ}
    (hr : r ≠ 0) (hH : ∀ i, ContinuousAt (H i) w) :
    ContinuousAt (fun w => (r : EReal) * generatorLog H w) w := by
  have hr' : (r : EReal) ≠ 0 := EReal.coe_ne_zero.mpr hr
  have hmul := EReal.continuousAt_mul (p := ((r : EReal), generatorLog H w)) (Or.inl hr')
    (Or.inl hr') (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))
  have hg : ContinuousAt (fun w => ((r : EReal), generatorLog H w)) w :=
    continuousAt_const.prodMk (continuousAt_generatorLog hH)
  exact ContinuousAt.comp (f := fun w => ((r : EReal), generatorLog H w)) (x := w) hmul hg

/-- Adding a real constant is continuous on `EReal`. -/
theorem continuousAt_add_coe {f : E → EReal} {w : E} (hf : ContinuousAt f w) (B : ℝ) :
    ContinuousAt (fun w => f w + (B : EReal)) w := by
  have hadd := EReal.continuousAt_add (p := (f w, (B : EReal))) (Or.inr (EReal.coe_ne_bot _))
    (Or.inr (EReal.coe_ne_top _))
  have hg : ContinuousAt (fun w => (f w, (B : EReal))) w := hf.prodMk continuousAt_const
  exact ContinuousAt.comp (f := fun w => (f w, (B : EReal))) (x := w) hadd hg

end Continuity

section EReal

/-- `↑r * X ≤ ↑t` with `r > 0` and `X ≠ ⊤` gives `X ≤ ↑(t / r)`. -/
theorem le_coe_div_of_coe_mul_le {X : EReal} {r t : ℝ} (hr : 0 < r)
    (h : (r : EReal) * X ≤ (t : EReal)) : X ≤ ((t / r : ℝ) : EReal) := by
  induction X using EReal.rec with
  | bot => exact bot_le
  | top =>
      rw [EReal.coe_mul_top_of_pos hr] at h
      exact absurd h (not_le.mpr (EReal.coe_lt_top t))
  | coe x =>
      rw [← EReal.coe_mul, EReal.coe_le_coe_iff] at h
      exact EReal.coe_le_coe_iff.mpr ((le_div_iff₀ hr).mpr (by linarith))

/-- `↑r * X ≤ ↑(r * q)` for `X ≤ ↑q` and `r ≥ 0`. -/
theorem coe_mul_le_coe_mul_of_le {X : EReal} {r q : ℝ} (hr : 0 ≤ r) (h : X ≤ (q : EReal)) :
    (r : EReal) * X ≤ ((r * q : ℝ) : EReal) := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  induction X using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos hr]; exact bot_le
  | top => exact absurd h (not_le.mpr (EReal.coe_lt_top q))
  | coe x =>
      rw [← EReal.coe_mul]
      exact EReal.coe_le_coe_iff.mpr
        (mul_le_mul_of_nonneg_left (EReal.coe_le_coe_iff.mp h) hr.le)

end EReal

section Bounded

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A function with analytic singularity type at `z` is bounded above near `z`. -/
theorem exists_eventually_le_of_hasAnalyticSingularityTypeAt {φ : E → EReal} {z : E}
    (hφ : HasAnalyticSingularityTypeAt φ z) : ∃ C : ℝ, ∀ᶠ w in 𝓝 z, φ w ≤ (C : EReal) := by
  obtain ⟨c, N, f, hc, ⟨U, hU, hzU, hf⟩, b, ⟨B, -, hB⟩, heq⟩ := hφ
  have hfc : ∀ i, ContinuousAt (f i) z :=
    fun i => (hf i).continuousOn.continuousAt (hU.mem_nhds hzU)
  have hlt : generatorLog f z < ⊤ :=
    lt_top_iff_ne_top.mpr (TranscendentalCore.generatorLog_ne_top f z)
  obtain ⟨q, hq, -⟩ := EReal.exists_rat_btwn_of_lt hlt
  have hev : ∀ᶠ w in 𝓝 z, generatorLog f w < (((q : ℝ)) : EReal) :=
    (continuousAt_generatorLog hfc).eventually (gt_mem_nhds hq)
  refine ⟨(c : ℝ) * q + B, ?_⟩
  filter_upwards [hev, hB, heq] with w hw hBw hw'
  rw [hw', EReal.coe_add]
  refine add_le_add (coe_mul_le_coe_mul_of_le hc.le ?_) (EReal.coe_le_coe_iff.mpr (abs_le.mp hBw).2)
  exact hw.le

end Bounded

end SGPT.Okounkov.TranscendentalCore2
