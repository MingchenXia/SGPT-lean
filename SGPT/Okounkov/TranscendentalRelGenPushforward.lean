import SGPT.Okounkov.TranscendentalRelGenLocal
import SGPT.Okounkov.TranscendentalRelGenDescent
import SGPT.Foundations.Analysis.Pending.MeteredDivisorPositivity

/-!
# Pushforwards with analytic singularities from relative global generation

Blueprint node `tok:boucksom-pushforward` (DRWNXZ Lemma 2.8; chapter `claude-tok-relgen`):
`RelativeGlobalGenerationStatement → PushforwardAnalyticStatement`
(`pushforwardAnalyticStatement_of_relativeGlobalGeneration`).

Let `π : Z → X` be an analytic modification from a compact complex manifold, `D` an effective
divisor on `Z` with a smooth metric `E` (weight `ψ_E`), and assume that for some `N` the sections
of `𝒪(-(N+1)D)` over `π⁻¹ U` generate `𝒪(-(N+1)D)_z` for a neighbourhood `U` of `π z`, for every
`z`.

* `exists_fibre_generators`: every `x ∈ X` has a neighbourhood `O` with finitely many holomorphic
  `f_i` on `O` such that `δ e^{(N+1)ψ_E} ≤ ∑ |f_i ∘ π|² ≤ K e^{(N+1)ψ_E}` on `π⁻¹ O`. The fibre
  `π⁻¹(x)` is compact, finitely many sections generate near each of its points
  (`exists_generator_bound`), the generation neighbourhoods cover a neighbourhood
  `π⁻¹ O` of the fibre (`π` is closed), the sections are bounded by the weight on the compact
  set `π⁻¹ K` (`exists_section_bound`), and they descend to `X`
  (`exists_holomorphic_descent`).
* `pushforwardAnalyticStatement_of_relativeGlobalGeneration`: if `φ ∘ π = c ψ_E + O(1)` then
  near every `x`, `φ = (c / (N + 1)) log ∑ |f_i|² + O(1)`, so `φ` has analytic singularities.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalRelGen

open Set Filter Metric
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Okounkov.TranscendentalCore

/-! ### The logarithmic remainder -/

/-- The real remainder `log S - (N + 1) ψ` (and `0` along the poles `ψ = ⊥`). -/
def logRemainder (N : ℕ) (ψ : EReal) (S : ℝ) : ℝ :=
  if ψ = ⊥ then 0 else Real.log S - ((N : ℝ) + 1) * ψ.toReal

theorem wexp_pow_eq (N : ℕ) (u : ℝ) :
    wexp (u : EReal) ^ (N + 1) = Real.exp (((N : ℝ) + 1) * u) := by
  rw [wexp_coe, ← Real.exp_nat_mul]
  push_cast
  ring_nf

/-- Two-sided bounds `δ e^{(N+1)ψ} ≤ S ≤ K e^{(N+1)ψ}` bound the logarithmic remainder. -/
theorem abs_logRemainder_le {N : ℕ} {ψ : EReal} (hψ : ψ ≠ ⊤) {S δ K : ℝ} (hδ : 0 < δ)
    (hlow : δ * wexp ψ ^ (N + 1) ≤ S) (hup : S ≤ K * wexp ψ ^ (N + 1)) :
    |logRemainder N ψ S| ≤ |Real.log δ| + |Real.log K| := by
  unfold logRemainder
  split_ifs with hbot
  · simp only [abs_zero]
    positivity
  · lift ψ to ℝ using ⟨hψ, hbot⟩
    rw [EReal.toReal_coe]
    rw [wexp_pow_eq] at hlow hup
    set P := Real.exp (((N : ℝ) + 1) * ψ) with hP
    have hPpos : 0 < P := Real.exp_pos _
    have hSpos : 0 < S := lt_of_lt_of_le (mul_pos hδ hPpos) hlow
    have hKpos : 0 < K := by
      by_contra hK
      push Not at hK
      have : K * P ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hK hPpos.le
      linarith
    have h1 : Real.log δ + ((N : ℝ) + 1) * ψ ≤ Real.log S := by
      have := Real.log_le_log (mul_pos hδ hPpos) hlow
      rwa [Real.log_mul hδ.ne' hPpos.ne', hP, Real.log_exp] at this
    have h2 : Real.log S ≤ Real.log K + ((N : ℝ) + 1) * ψ := by
      have := Real.log_le_log hSpos hup
      rwa [Real.log_mul hKpos.ne' hPpos.ne', hP, Real.log_exp] at this
    rw [abs_le]
    constructor
    · have := neg_abs_le (Real.log δ)
      have := abs_nonneg (Real.log K)
      linarith
    · have := le_abs_self (Real.log K)
      have := abs_nonneg (Real.log δ)
      linarith

/-- Under two-sided bounds, `log S = (N + 1) ψ + (remainder)` in `[-∞, ∞)`. -/
theorem log_eq_add_logRemainder {N : ℕ} {ψ : EReal} (hψ : ψ ≠ ⊤) {S δ K : ℝ} (hδ : 0 < δ)
    (hS : 0 ≤ S) (hlow : δ * wexp ψ ^ (N + 1) ≤ S) (hup : S ≤ K * wexp ψ ^ (N + 1)) :
    ENNReal.log (ENNReal.ofReal S) =
      (((N : ℝ) + 1 : ℝ) : EReal) * ψ + (logRemainder N ψ S : EReal) := by
  unfold logRemainder
  split_ifs with hbot
  · subst hbot
    have hS0 : S = 0 := by
      have : S ≤ 0 := by simpa [wexp_bot] using hup
      linarith
    rw [hS0, EReal.coe_mul_bot_of_pos (by positivity), EReal.bot_add]
    simp
  · lift ψ to ℝ using ⟨hψ, hbot⟩
    rw [EReal.toReal_coe]
    rw [wexp_pow_eq] at hlow
    have hSpos : 0 < S := lt_of_lt_of_le (mul_pos hδ (Real.exp_pos _)) hlow
    rw [ENNReal.log_ofReal_of_pos hSpos, ← EReal.coe_mul, ← EReal.coe_add]
    congr 1
    ring

/-- The arithmetic of the last step, in `[-∞, ∞)`: with `c = c' (N + 1)`,
`c ψ + b = c' ((N + 1) ψ + L) + (b - c' L)`. -/
theorem ereal_affine_identity {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') {N : ℕ}
    (hcc' : c = c' * ((N : ℝ) + 1)) {ψ : EReal} (hψ : ψ ≠ ⊤) (b L : ℝ) :
    (c : EReal) * ψ + (b : EReal) =
      (c' : EReal) * ((((N : ℝ) + 1 : ℝ) : EReal) * ψ + (L : EReal)) +
        ((b - c' * L : ℝ) : EReal) := by
  induction ψ using EReal.rec with
  | bot =>
      rw [EReal.coe_mul_bot_of_pos hc, EReal.bot_add,
        EReal.coe_mul_bot_of_pos (by positivity), EReal.bot_add,
        EReal.coe_mul_bot_of_pos hc', EReal.bot_add]
  | coe u =>
      rw [← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_add,
        ← EReal.coe_mul, ← EReal.coe_add]
      congr 1
      rw [hcc']
      ring
  | top => exact absurd rfl hψ

/-! ### Generators near a fibre -/

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- **Local generators near a fibre.** If the sections of `𝒪(-(N+1)D)` over `π⁻¹ U_z`
generate the stalk at every `z`, every `x ∈ X` has a neighbourhood `O` with finitely many
holomorphic `f_i` on `O` such that `δ e^{(N+1)ψ_E} ≤ ∑ |f_i ∘ π|² ≤ K e^{(N+1)ψ_E}` on
`π⁻¹ O`. -/
theorem exists_fibre_generators {π : Z → X} (hπ : IsAnalyticModification (n := n) π)
    {D : EffectiveDivisor n Z} {E : MeteredEffectiveQDivisor n Z}
    (hE : DivisorMetric.IsDivisorMetric D E) {N : ℕ}
    (hgen : ∀ z : Z, ∃ U : Set X, IsOpen U ∧ π z ∈ U ∧
      SectionsGenerateAt (divisorSuccNsmul D N).ideal (π ⁻¹' U) z) (x : X) :
    ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ ∃ (r : ℕ) (f : Fin r → X → ℂ),
      (∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (f i) O) ∧
      ∃ δ K : ℝ, 0 < δ ∧ ∀ z ∈ π ⁻¹' O,
        δ * wexp (E.weight z) ^ (N + 1) ≤ ∑ i, ‖f i (π z)‖ ^ 2 ∧
        ∑ i, ‖f i (π z)‖ ^ 2 ≤ K * wexp (E.weight z) ^ (N + 1) := by
  classical
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  have hπc : Continuous π := hπ.1.continuous
  choose U hU hxU hgenU using hgen
  choose r σ hσ W hW C hC using fun z => exists_generator_bound hE (hgenU z)
  -- the fibre and a finite subcover
  have hFc : IsCompact (π ⁻¹' {x}) := hπ.2.1.isCompact_preimage isCompact_singleton
  obtain ⟨t, htF, hcover⟩ := hFc.elim_nhds_subcover (fun z => interior (W z))
    (fun z _ => isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr (hW z)))
  let Wo : Set Z := ⋃ z ∈ t, interior (W z)
  have hWo : IsOpen Wo := isOpen_biUnion fun z _ => isOpen_interior
  let O₀ : Set X := (π '' Woᶜ)ᶜ
  have hO₀ : IsOpen O₀ := (hπ.2.1.isClosedMap _ hWo.isClosed_compl).isOpen_compl
  have hxO₀ : x ∈ O₀ := by
    rintro ⟨y, hy, hyx⟩
    exact hy (hcover (show y ∈ π ⁻¹' {x} from hyx))
  have hpreO₀ : π ⁻¹' O₀ ⊆ Wo := by
    intro y hy
    by_contra hyW
    exact hy ⟨y, hyW, rfl⟩
  let U' : Set X := ⋂ z ∈ t, U z
  have hU' : IsOpen U' := isOpen_biInter_finset fun z _ => hU z
  have hxU' : x ∈ U' := by
    refine mem_iInter₂.mpr fun z hz => ?_
    have hzx : π z = x := htF z hz
    rw [← hzx]
    exact hxU z
  have hU'U : ∀ z ∈ t, U' ⊆ U z := fun z hz => biInter_subset_of_mem hz
  -- a compact neighbourhood
  obtain ⟨K₀, hK₀n, hK₀sub, hK₀c⟩ := local_compact_nhds ((hU'.inter hO₀).mem_nhds ⟨hxU', hxO₀⟩)
  let O : Set X := interior K₀
  have hO : IsOpen O := isOpen_interior
  have hxO : x ∈ O := mem_interior_iff_mem_nhds.mpr hK₀n
  have hOK : O ⊆ K₀ := interior_subset
  have hKpre : IsCompact (π ⁻¹' K₀) := hπ.2.1.isCompact_preimage hK₀c
  -- the family of all sections
  let ι := Σ z : t, Fin (r z)
  let σa : ι → Z → ℂ := fun i => σ i.1 i.2
  have hσa : ∀ i : ι, IsIdealSectionOn (divisorSuccNsmul D N).ideal (π ⁻¹' U i.1) (σa i) :=
    fun i => hσ i.1 i.2
  have hσaU' : ∀ i : ι, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (σa i) (π ⁻¹' U') :=
    fun i => (hσa i).1.mono fun y hy => hU'U i.1 i.1.2 hy
  choose f₀ hf₀ hf₀π using fun i => exists_holomorphic_descent hπ hU' (hσaU' i)
  let eι := Fintype.equivFin ι
  let f : Fin (Fintype.card ι) → X → ℂ := fun j => f₀ (eι.symm j)
  have hsum : ∀ y ∈ π ⁻¹' U', ∑ j, ‖f j (π y)‖ ^ 2 = ∑ i : ι, ‖σa i y‖ ^ 2 := by
    intro y hy
    rw [← Equiv.sum_comp eι.symm]
    refine Finset.sum_congr rfl fun j _ => ?_
    change ‖f₀ (eι.symm j) (π y)‖ ^ 2 = _
    rw [hf₀π _ y hy]
  -- upper bounds for each section on the compact set `π⁻¹ K₀`
  have hup : ∀ i : ι, ∃ c : ℝ, 0 ≤ c ∧ ∀ y ∈ π ⁻¹' K₀,
      ‖σa i y‖ ^ 2 ≤ c * wexp (E.weight y) ^ (N + 1) := by
    intro i
    refine exists_uniform_bound_of_local hKpre (fun _ => pow_nonneg (wexp_nonneg _) _) ?_
    intro y hy
    exact exists_section_bound hE (hσa i) (hU'U i.1 i.1.2 (hK₀sub (show π y ∈ K₀ from hy)).1)
  choose cu hcu0 hcu using hup
  let Cl : ℝ := ∑ z ∈ t, max (C z) 0
  have hCl : 0 ≤ Cl := Finset.sum_nonneg fun _ _ => le_max_right _ _
  refine ⟨O, hO, hxO, Fintype.card ι, f, fun j => (hf₀ (eι.symm j)).mono fun y hy =>
    (hK₀sub (hOK hy)).1, (Cl + 1)⁻¹, ∑ i : ι, cu i, inv_pos.mpr (by linarith), ?_⟩
  intro y hy
  have hyK : y ∈ π ⁻¹' K₀ := hOK hy
  have hyU' : y ∈ π ⁻¹' U' := (hK₀sub hyK).1
  rw [hsum y hyU']
  constructor
  · -- lower bound: `y` lies in a generation neighbourhood
    have hyW : y ∈ Wo := hpreO₀ (hK₀sub hyK).2
    obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.mp hyW
    have hlow := hC z y (interior_subset hyz)
    have hpart : ∑ j, ‖σ z j y‖ ^ 2 ≤ ∑ i : ι, ‖σa i y‖ ^ 2 := by
      rw [Fintype.sum_sigma]
      exact Finset.single_le_sum (f := fun z' : t => ∑ j, ‖σ z' j y‖ ^ 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ ⟨z, hz⟩)
    have hCz : C z ≤ Cl + 1 := by
      have : max (C z) 0 ≤ Cl :=
        Finset.single_le_sum (f := fun z => max (C z) 0) (fun _ _ => le_max_right _ _) hz
      linarith [le_max_left (C z) 0]
    have hS0 : 0 ≤ ∑ j, ‖σ z j y‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hmain : wexp (E.weight y) ^ (N + 1) ≤ (Cl + 1) * ∑ i : ι, ‖σa i y‖ ^ 2 :=
      hlow.trans ((mul_le_mul_of_nonneg_right hCz hS0).trans
        (mul_le_mul_of_nonneg_left hpart (by linarith)))
    rw [inv_mul_le_iff₀ (by linarith)]
    exact hmain
  · rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => hcu i y hyK

/-! ### The pushforward -/

/-- **Pushforwards with analytic singularities** (blueprint `tok:boucksom-pushforward`, DRWNXZ
Lemma 2.8), from relative global generation (`tok:relgen`). -/
theorem pushforwardAnalyticStatement_of_relativeGlobalGeneration
    (h : RelativeGlobalGenerationStatement.{u}) : PushforwardAnalyticStatement.{u} := by
  intro n X Z _ _ _ _ _ _ _ π hπ θ β D E c hc hβ hE hclass φ hφ hφπ
  obtain ⟨b, Cb, hbC, hφb⟩ := hφπ
  obtain ⟨N, hgen⟩ := h n X Z π hπ θ β D E (c : ℝ) (by exact_mod_cast hc) hβ hE hclass
  refine ⟨hφ, ?_⟩
  intro e w hw
  have hsurj := AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hπ
  let x := e.val.symm w
  obtain ⟨O, hO, hxO, r, f, hf, δ, K, hδ, hbounds⟩ := exists_fibre_generators hπ hE hgen x
  let c' : ℚ := c / ((N : ℚ) + 1)
  have hc' : (0 : ℝ) < c' := by
    have : (0 : ℚ) < c' := div_pos hc (by positivity)
    exact_mod_cast this
  have hcc' : (c : ℝ) = (c' : ℝ) * ((N : ℝ) + 1) := by
    have hN : ((N : ℚ) + 1) ≠ 0 := by positivity
    have : c = c' * ((N : ℚ) + 1) := by
      change c = c / ((N : ℚ) + 1) * ((N : ℚ) + 1)
      rw [div_mul_cancel₀ c hN]
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) this
  let zs : ComplexModel n → Z := fun v => Function.surjInv hsurj (e.val.symm v)
  have hzs : ∀ v, π (zs v) = e.val.symm v := fun v => Function.surjInv_eq hsurj _
  let S : Z → ℝ := fun z => ∑ i, ‖f i (π z)‖ ^ 2
  let R : ComplexModel n → ℝ := fun v =>
    b (zs v) - (c' : ℝ) * logRemainder N (E.weight (zs v)) (S (zs v))
  let Ω : Set (ComplexModel n) := e.val.target ∩ e.val.symm ⁻¹' O
  have hΩ : IsOpen Ω := e.val.isOpen_inter_preimage_symm hO
  have hwΩ : w ∈ Ω := ⟨hw, hxO⟩
  refine ⟨c', r, fun i v => f i (e.val.symm v), hc', ⟨Ω, hΩ, hwΩ, ?_⟩, R, ?_, ?_⟩
  · exact fun i => MeteredDivisorPositivity.differentiableOn_comp_chartSymm e (hf i)
  · refine ⟨|Cb| + (c' : ℝ) * (|Real.log δ| + |Real.log K|), by positivity, ?_⟩
    filter_upwards [hΩ.mem_nhds hwΩ] with v hv
    have hzO : zs v ∈ π ⁻¹' O := by
      change π (zs v) ∈ O
      rw [hzs v]
      exact hv.2
    have hrem := abs_logRemainder_le (weight_ne_top_of_isDivisorMetric hE (zs v)) hδ
      (hbounds _ hzO).1 (hbounds _ hzO).2
    calc |R v| ≤ |b (zs v)| + |(c' : ℝ) * logRemainder N (E.weight (zs v)) (S (zs v))| :=
          abs_sub _ _
      _ ≤ |Cb| + (c' : ℝ) * (|Real.log δ| + |Real.log K|) := by
          rw [abs_mul, abs_of_pos hc']
          exact add_le_add ((hbC _).trans (le_abs_self Cb))
            (mul_le_mul_of_nonneg_left hrem hc'.le)
  · filter_upwards [hΩ.mem_nhds hwΩ] with v hv
    have hzO : zs v ∈ π ⁻¹' O := by
      change π (zs v) ∈ O
      rw [hzs v]
      exact hv.2
    have hlog := log_eq_add_logRemainder (weight_ne_top_of_isDivisorMetric hE (zs v)) hδ
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (hbounds _ hzO).1 (hbounds _ hzO).2
    have hgl : generatorLog (fun i v => f i (e.val.symm v)) v =
        ENNReal.log (ENNReal.ofReal (S (zs v))) := by
      rw [generatorLog_eq_log_sum]
      change ENNReal.log (ENNReal.ofReal (∑ i, ‖f i (e.val.symm v)‖ ^ 2)) =
        ENNReal.log (ENNReal.ofReal (∑ i, ‖f i (π (zs v))‖ ^ 2))
      rw [hzs v]
    change φ (e.val.symm v) = ((c' : ℝ) : EReal) * generatorLog (fun i v => f i (e.val.symm v)) v +
      (R v : EReal)
    rw [← hzs v, hφb (zs v), hgl, hlog]
    exact ereal_affine_identity (by exact_mod_cast hc) hc' hcc'
      (weight_ne_top_of_isDivisorMetric hE (zs v)) _ _

end SGPT.Okounkov.TranscendentalRelGen
