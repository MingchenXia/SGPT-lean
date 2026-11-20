import SGPT.Okounkov.TranscendentalRelGenStatement

/-!
# Local comparison of sections of `𝒪(-(N+1)D)` with the divisor weight

Auxiliary for blueprint node `tok:boucksom-pushforward` (chapter `claude-tok-relgen`,
`relgen:local-bounds`). Let `D` be an effective divisor with a smooth metric `E`
(`DivisorMetric.IsDivisorMetric D E`), `ψ_E = E.weight` its weight and `e^{ψ_E} = |s_D|²_h`
(`wexp ψ_E`, the real exponential of the extended real weight, `0` along `D`).

* `exists_local_weight_bounds`: near every point `e^{-M} |g|² ≤ e^{ψ_E} ≤ e^{M} |g|²` for a
  local equation `g` of `D`.
* `exists_section_bound`: a section `σ` of `𝒪(-(N+1)D)` satisfies `|σ|² ≤ C e^{(N+1)ψ_E}` near
  every point of its domain.
* `exists_generator_bound`: if the sections of `𝒪(-(N+1)D)` over `V` generate the stalk at
  `z`, finitely many of them satisfy `e^{(N+1)ψ_E} ≤ C ∑ |σ_j|²` near `z`.
* `exists_uniform_bound_of_local`: local bounds `F ≤ C G` give one bound on a compact set.
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
open SGPT.Okounkov.TranscendentalCore

/-! ### The real exponential of an extended real weight -/

/-- The exponential `e^x ∈ [0, ∞)` of an extended real number `x < ⊤`, with `e^{⊥} = 0`
(the junk value `e^{x.toReal}` at `⊤` is never used). -/
def wexp (x : EReal) : ℝ := if x = ⊥ then 0 else Real.exp x.toReal

@[simp] theorem wexp_bot : wexp ⊥ = 0 := if_pos rfl

theorem wexp_coe (t : ℝ) : wexp (t : EReal) = Real.exp t := by
  rw [wexp, if_neg (EReal.coe_ne_bot t), EReal.toReal_coe]

theorem wexp_nonneg (x : EReal) : 0 ≤ wexp x := by
  unfold wexp
  split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

/-- `e^{log a + h} = a e^h`. -/
theorem wexp_log_add {a : ℝ} (ha : 0 ≤ a) (h : ℝ) :
    wexp (ENNReal.log (ENNReal.ofReal a) + (h : EReal)) = a * Real.exp h := by
  rcases ha.eq_or_lt with rfl | hpos
  · simp
  · rw [ENNReal.log_ofReal_of_pos hpos, ← EReal.coe_add, wexp_coe, Real.exp_add,
      Real.exp_log hpos]

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### Local equations from a divisor metric -/

omit [IsComplexManifold n M] in
/-- A chart-smooth function on an open set is continuous there. -/
theorem continuousOn_of_chartSmooth {V : Set M} (hV : IsOpen V) {h : M → ℝ}
    (hh : ∀ e : ComplexChart n M,
      ContDiffOn ℝ ∞ (fun z => h (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' V)) :
    ContinuousOn h V := by
  intro t ht
  let e := complexChartAt (n := n) t
  have hte : t ∈ e.val.source := mem_complexChartAt_source t
  have hmem : e.val t ∈ e.val.target ∩ e.val.symm ⁻¹' V :=
    ⟨e.val.map_source hte, by change e.val.symm (e.val t) ∈ V; rw [e.val.left_inv hte]; exact ht⟩
  have hopen : IsOpen (e.val.target ∩ e.val.symm ⁻¹' V) :=
    e.val.isOpen_inter_preimage_symm hV
  have hc : ContinuousAt (fun z => h (e.val.symm z)) (e.val t) :=
    ((hh e).continuousOn).continuousAt (hopen.mem_nhds hmem)
  have hc' : ContinuousAt (fun y => h (e.val.symm (e.val y))) t :=
    hc.comp (e.val.continuousAt hte)
  refine (hc'.congr ?_).continuousWithinAt
  filter_upwards [e.val.open_source.mem_nhds hte] with y hy
  rw [e.val.left_inv hy]

/-- The local generators of `𝒪(-D)` given by a divisor metric are local equations: they vanish
identically on no nonempty open set (because `𝒪(-D)` is invertible). -/
theorem exists_localEquation_of_isDivisorMetric {D : EffectiveDivisor n M}
    {E : MeteredEffectiveQDivisor n M} (hE : DivisorMetric.IsDivisorMetric D E) (y : M) :
    ∃ V : Set M, IsOpen V ∧ y ∈ V ∧ ∃ g : M → ℂ, IsLocalEquationOn D.ideal V g ∧
      ∃ h : M → ℝ, ContinuousOn h V ∧
        ∀ t ∈ V, E.weight t = generatorLog (fun _ : Fin 1 => g) t + (h t : EReal) := by
  obtain ⟨V, hV, hyV, g, hg, hgen, h, hh, hw⟩ := hE y
  refine ⟨V, hV, hyV, g, ⟨hg, ?_, hgen⟩, h, continuousOn_of_chartSmooth hV hh, hw⟩
  intro W hW hWV hWne
  by_contra hall
  push Not at hall
  obtain ⟨t₀, ht₀⟩ := hWne
  obtain ⟨U, hU, ht₀U, k, hk, hknon, hkgen⟩ := D.isInvertible t₀
  have hkhol : HolomorphicAt n k t₀ :=
    InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU hk ht₀U
  have hkmem : D.ideal.mem t₀ k := (hkgen t₀ ht₀U k).mpr (InvertibleIdealQuotient.isInSpanAt_self rfl hkhol)
  obtain ⟨-, a, -, heq⟩ := isInSpanAt_eq_iff.mp ((hgen t₀ (hWV ht₀) k).mp hkmem)
  have hzero : ∀ᶠ t in 𝓝 t₀, k t = 0 := by
    filter_upwards [heq, hW.mem_nhds ht₀] with t ht htW
    rw [ht, hall t htW, mul_zero]
  obtain ⟨O, hOsub, hOo, ht₀O⟩ := _root_.mem_nhds_iff.mp hzero
  obtain ⟨t, ht, hkt⟩ := hknon (O ∩ U) (hOo.inter hU) inter_subset_right ⟨t₀, ht₀O, ht₀U⟩
  exact hkt (hOsub ht.1)

/-- The weight of a divisor metric never takes the value `⊤`. -/
theorem weight_ne_top_of_isDivisorMetric {D : EffectiveDivisor n M}
    {E : MeteredEffectiveQDivisor n M} (hE : DivisorMetric.IsDivisorMetric D E) (t : M) :
    E.weight t ≠ ⊤ := by
  obtain ⟨V, -, htV, g, -, -, h, -, hw⟩ := hE t
  rw [hw t htV, generatorLog_eq_log_sum, ENNReal.log_ofReal]
  split_ifs
  · simp
  · rw [← EReal.coe_add]
    exact EReal.coe_ne_top _

/-- **Local comparison of the weight with a local equation**: near every point there are a
local equation `g` of `D` and `M` with `e^{-M} |g|² ≤ e^{ψ_E} ≤ e^{M} |g|²`. -/
theorem exists_local_weight_bounds {D : EffectiveDivisor n M}
    {E : MeteredEffectiveQDivisor n M} (hE : DivisorMetric.IsDivisorMetric D E) (y : M) :
    ∃ V : Set M, IsOpen V ∧ y ∈ V ∧ ∃ g : M → ℂ, IsLocalEquationOn D.ideal V g ∧
      ∃ K : ℝ, ∀ t ∈ V, Real.exp (-K) * ‖g t‖ ^ 2 ≤ wexp (E.weight t) ∧
        wexp (E.weight t) ≤ Real.exp K * ‖g t‖ ^ 2 := by
  obtain ⟨V, hV, hyV, g, hg, h, hhc, hw⟩ := exists_localEquation_of_isDivisorMetric hE y
  have hcy : ContinuousAt h y := hhc.continuousAt (hV.mem_nhds hyV)
  have hev : ∀ᶠ t in 𝓝 y, |h t| < |h y| + 1 :=
    hcy.abs.eventually_lt continuousAt_const (lt_add_one _)
  obtain ⟨O, hOsub, hOo, hyO⟩ := _root_.mem_nhds_iff.mp hev
  refine ⟨V ∩ O, hV.inter hOo, ⟨hyV, hyO⟩, g, hg.mono inter_subset_left, |h y| + 1, ?_⟩
  intro t ht
  have hwt : wexp (E.weight t) = ‖g t‖ ^ 2 * Real.exp (h t) := by
    rw [hw t ht.1, generatorLog_eq_log_sum]
    simp only [Finset.univ_unique, Finset.sum_singleton]
    exact wexp_log_add (sq_nonneg _) _
  have hb : -(|h y| + 1) < h t ∧ h t < |h y| + 1 := abs_lt.mp (hOsub ht.2)
  have hg2 : 0 ≤ ‖g t‖ ^ 2 := sq_nonneg _
  rw [hwt]
  constructor
  · rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hg2
  · rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hg2

/-! ### Sections and generators -/

/-- **Sections of `𝒪(-(N+1)D)` are bounded by the weight**: `|σ|² ≤ C e^{(N+1)ψ_E}` near
every point of the domain of the section. -/
theorem exists_section_bound {D : EffectiveDivisor n M} {E : MeteredEffectiveQDivisor n M}
    (hE : DivisorMetric.IsDivisorMetric D E) {N : ℕ} {V' : Set M} {σ : M → ℂ}
    (hσ : IsIdealSectionOn (divisorSuccNsmul D N).ideal V' σ) {y : M} (hy : y ∈ V') :
    ∃ W ∈ 𝓝 y, ∃ C : ℝ, ∀ t ∈ W, ‖σ t‖ ^ 2 ≤ C * wexp (E.weight t) ^ (N + 1) := by
  obtain ⟨V, hV, hyV, g, hg, K, hK⟩ := exists_local_weight_bounds hE y
  have hgN := IsLocalEquationOn.succNsmul hV hg N
  obtain ⟨-, a, ha, heq⟩ := isInSpanAt_eq_iff.mp ((hgN.2.2 y hyV σ).mp (hσ.2 y hy))
  have hac : ContinuousAt a y := ha.continuousAt
  have hev : ∀ᶠ t in 𝓝 y, ‖a t‖ < ‖a y‖ + 1 :=
    hac.norm.eventually_lt continuousAt_const (lt_add_one _)
  refine ⟨_, Filter.inter_mem (Filter.inter_mem heq hev) (hV.mem_nhds hyV),
    (‖a y‖ + 1) ^ 2 * Real.exp K ^ (N + 1), ?_⟩
  rintro t ⟨⟨hteq, hta⟩, htV⟩
  change σ t = a t * g t ^ (N + 1) at hteq
  have hgle : ‖g t‖ ^ 2 ≤ Real.exp K * wexp (E.weight t) := by
    have h1 := (hK t htV).1
    have h2 : ‖g t‖ ^ 2 = Real.exp K * (Real.exp (-K) * ‖g t‖ ^ 2) := by
      rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos K).le
  have ha2 : ‖a t‖ ^ 2 ≤ (‖a y‖ + 1) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hta.le 2
  calc ‖σ t‖ ^ 2 = ‖a t‖ ^ 2 * (‖g t‖ ^ 2) ^ (N + 1) := by
        rw [hteq, norm_mul, norm_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 (N + 1)]
    _ ≤ (‖a y‖ + 1) ^ 2 * (Real.exp K * wexp (E.weight t)) ^ (N + 1) := by
        apply mul_le_mul ha2 (pow_le_pow_left₀ (sq_nonneg _) hgle _)
          (pow_nonneg (sq_nonneg _) _) (sq_nonneg _)
    _ = (‖a y‖ + 1) ^ 2 * Real.exp K ^ (N + 1) * wexp (E.weight t) ^ (N + 1) := by
        rw [mul_pow, mul_assoc]

/-- **Generators bound the weight from below**: if the sections of `𝒪(-(N+1)D)` over `V'`
generate the stalk at `z`, finitely many of them satisfy `e^{(N+1)ψ_E} ≤ C ∑ |σ_j|²` near
`z`. -/
theorem exists_generator_bound {D : EffectiveDivisor n M} {E : MeteredEffectiveQDivisor n M}
    (hE : DivisorMetric.IsDivisorMetric D E) {N : ℕ} {V' : Set M} {z : M}
    (hgen : SectionsGenerateAt (divisorSuccNsmul D N).ideal V' z) :
    ∃ (r : ℕ) (σ : Fin r → M → ℂ),
      (∀ j, IsIdealSectionOn (divisorSuccNsmul D N).ideal V' (σ j)) ∧
      ∃ W ∈ 𝓝 z, ∃ C : ℝ, ∀ t ∈ W, wexp (E.weight t) ^ (N + 1) ≤ C * ∑ j, ‖σ j t‖ ^ 2 := by
  obtain ⟨V, hV, hzV, g, hg, K, hK⟩ := exists_local_weight_bounds hE z
  have hgN := IsLocalEquationOn.succNsmul hV hg N
  have hghol : HolomorphicAt n (fun y => g y ^ (N + 1)) z :=
    InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hV hgN.1 hzV
  have hmem : (divisorSuccNsmul D N).ideal.mem z (fun y => g y ^ (N + 1)) :=
    (hgN.2.2 z hzV _).mpr (InvertibleIdealQuotient.isInSpanAt_self rfl hghol)
  obtain ⟨-, r, σ, a, hσ, ha, hsum⟩ := hgen _ hmem
  refine ⟨r, σ, hσ, ?_⟩
  have hac : ∀ j, ContinuousAt (a j) z := fun j => (ha j).continuousAt
  have hev : ∀ᶠ t in 𝓝 z, ∀ j, ‖a j t‖ < ‖a j z‖ + 1 :=
    eventually_all.mpr fun j => (hac j).norm.eventually_lt continuousAt_const (lt_add_one _)
  let A : ℝ := ∑ j, (‖a j z‖ + 1) ^ 2
  refine ⟨_, Filter.inter_mem (Filter.inter_mem hsum hev) (hV.mem_nhds hzV),
    Real.exp K ^ (N + 1) * A, ?_⟩
  rintro t ⟨⟨hteq, hta⟩, htV⟩
  change g t ^ (N + 1) = ∑ j, a j t * σ j t at hteq
  have hwle : wexp (E.weight t) ≤ Real.exp K * ‖g t‖ ^ 2 := (hK t htV).2
  have hCS : ‖∑ j, a j t * σ j t‖ ^ 2 ≤ (∑ j, ‖a j t‖ ^ 2) * ∑ j, ‖σ j t‖ ^ 2 := by
    have h1 : ‖∑ j, a j t * σ j t‖ ≤ ∑ j, ‖a j t‖ * ‖σ j t‖ :=
      (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖a j t‖) fun j => ‖σ j t‖
    calc ‖∑ j, a j t * σ j t‖ ^ 2 ≤ (∑ j, ‖a j t‖ * ‖σ j t‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
  have hA : ∑ j, ‖a j t‖ ^ 2 ≤ A :=
    Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hta j).le 2
  have hS : 0 ≤ ∑ j, ‖σ j t‖ ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  calc wexp (E.weight t) ^ (N + 1) ≤ (Real.exp K * ‖g t‖ ^ 2) ^ (N + 1) :=
        pow_le_pow_left₀ (wexp_nonneg _) hwle _
    _ = Real.exp K ^ (N + 1) * ‖g t ^ (N + 1)‖ ^ 2 := by
        rw [mul_pow, norm_pow, ← pow_mul, ← pow_mul, mul_comm 2 (N + 1)]
    _ ≤ Real.exp K ^ (N + 1) * ((∑ j, ‖a j t‖ ^ 2) * ∑ j, ‖σ j t‖ ^ 2) := by
        rw [hteq]
        exact mul_le_mul_of_nonneg_left hCS (pow_nonneg (Real.exp_pos K).le _)
    _ ≤ Real.exp K ^ (N + 1) * (A * ∑ j, ‖σ j t‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA hS)
          (pow_nonneg (Real.exp_pos K).le _)
    _ = Real.exp K ^ (N + 1) * A * ∑ j, ‖σ j t‖ ^ 2 := by ring

/-! ### Compactness -/

omit [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- Local bounds `F ≤ C G` near every point of a compact set give one bound on it. -/
theorem exists_uniform_bound_of_local {K : Set M} (hK : IsCompact K) {F G : M → ℝ}
    (hG : ∀ t, 0 ≤ G t) (h : ∀ y ∈ K, ∃ W ∈ 𝓝 y, ∃ C : ℝ, ∀ t ∈ W, F t ≤ C * G t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ K, F t ≤ C * G t := by
  classical
  choose W hW C hC using h
  obtain ⟨s, hs⟩ := hK.elim_nhds_subcover' W hW
  refine ⟨∑ y ∈ s, max (C y.1 y.2) 0, Finset.sum_nonneg fun _ _ => le_max_right _ _, ?_⟩
  intro t ht
  obtain ⟨y, hy, htW⟩ := mem_iUnion₂.mp (hs ht)
  calc F t ≤ C y.1 y.2 * G t := hC y.1 y.2 t htW
    _ ≤ max (C y.1 y.2) 0 * G t := mul_le_mul_of_nonneg_right (le_max_left _ _) (hG t)
    _ ≤ (∑ y ∈ s, max (C y.1 y.2) 0) * G t := by
        apply mul_le_mul_of_nonneg_right _ (hG t)
        exact Finset.single_le_sum (f := fun y : K => max (C y.1 y.2) 0)
          (fun _ _ => le_max_right _ _) hy

end SGPT.Okounkov.TranscendentalRelGen
