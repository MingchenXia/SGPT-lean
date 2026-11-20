import SGPT.Okounkov.TranscendentalRelGenPole
import SGPT.Okounkov.TranscendentalRelGenWeight
import SGPT.Foundations.Analysis.Pending.LelongPoincareDivisor
import SGPT.Foundations.Analysis.Pending.MultiplierIdealBergmanNadelManifold

/-!
# Relative global generation from `L²` generation

Blueprint node `tok:relgen` (chapter `claude-okounkov-transcendental`; sub-lemmas in
`claude-tok-relgen`): `WeaklyPseudoconvexL2GenerationStatement → L2DivisibilityStatement →
RelativeGlobalGenerationStatement` (`relativeGlobalGeneration_of_l2Generation`).

`L2DivisibilityStatement` (`relgen:l2-divisibility`) is the classical identity
`𝓘(m log |g|²) = (g^m)`: a holomorphic `F` with `∫ |F|² |g|^{-2m} < ∞` near `p` is divisible by
`g^m` near `p`.

Proof of relative global generation: for `z ∈ Z`, take a coordinate ball `U` around `π z` on
which `θ` has a smooth potential `ρ`, and the weight
`φ_N = (N + 1) ψ_E + ((N + 1) / c) (ρ ∘ d ∘ π + h)` on `V = π⁻¹ U`
(`TranscendentalRelGenWeight`): `V` is weakly pseudoconvex and `dd^c φ_N ≥ ((N+1)/c) β`. Near
every point of `V`, `φ_N = (N + 1) log |g|² + b` with `g` a local equation of `D` and `b`
continuous (`exists_chart_weight_presentation`). The `L²` generation theorem with the pole
order `q = n` gives a holomorphic `F` on `V`; `L²` divisibility makes `F` a section of
`𝒪(-(N+1)D)` over `V`, and near `z`, `F = A g^{N+1}`; the pole forces `A(z) = 1`
(`eq_zero_of_lintegral_div_norm_pow_ne_top`), so `F` generates the stalk at `z`. In dimension
`0` the constant `1` is a section generating every stalk.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalRelGen

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Okounkov.TranscendentalCore

variable {n : ℕ}

/-- **`L²` divisibility** (blueprint `relgen:l2-divisibility`): the identity
`𝓘(m log |g|²) = (g^m)` for a holomorphic `g`, not identically zero near `p`: a holomorphic `F`
with `∫_{B(p, r)} |F|² |g|^{-2m} < ∞` is `a g^m` near `p` with `a` holomorphic. -/
def L2DivisibilityStatement : Prop :=
  ∀ (d : ℕ) (p : ComplexModel d) (r : ℝ), 0 < r → ∀ F g : ComplexModel d → ℂ,
    DifferentiableOn ℂ F (ball p r) → DifferentiableOn ℂ g (ball p r) →
    (¬ ∀ᶠ w in 𝓝 p, g w = 0) → ∀ m : ℕ,
    (∫⁻ w in ball p r, ENNReal.ofReal (‖F w‖ ^ 2) / ENNReal.ofReal (‖g w‖ ^ (2 * m))) ≠ ⊤ →
    ∃ a : ComplexModel d → ℂ, (∀ᶠ w in 𝓝 p, DifferentiableAt ℂ a w) ∧
      ∀ᶠ w in 𝓝 p, F w = a w * g w ^ m

/-! ### The multiplier weight of a logarithmic presentation -/

/-- `e^{-(m log |k|² + b)} = e^{-b} |k|^{-2m}` away from the zeros of `k`. -/
theorem multiplierWeight_log_add {m : ℕ} {k : ℂ} (hk : k ≠ 0) (b : ℝ) :
    multiplierWeight 1 ((((m : ℝ) : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (‖k‖ ^ 2)) +
      (b : EReal)) = ENNReal.ofReal (Real.exp (-b) / ‖k‖ ^ (2 * m)) := by
  have hk2 : 0 < ‖k‖ ^ 2 := by positivity
  rw [ENNReal.log_ofReal_of_pos hk2, ← EReal.coe_mul, ← EReal.coe_add, multiplierWeight_coe]
  congr 1
  calc Real.exp (-(1 * ((m : ℝ) * Real.log (‖k‖ ^ 2) + b))) =
        Real.exp (-b) / Real.exp ((m : ℝ) * Real.log (‖k‖ ^ 2)) := by
        rw [one_mul, neg_add, Real.exp_add, Real.exp_neg ((m : ℝ) * _), div_eq_mul_inv, mul_comm]
    _ = Real.exp (-b) / ‖k‖ ^ (2 * m) := by
        rw [Real.exp_nat_mul, Real.exp_log hk2, pow_mul]

/-- The weighted density of `G` for a logarithmic presentation `u = m log |k|² + b`, at a
point where `k ≠ 0`. -/
theorem multiplierDensity_of_presentation {u : ComplexModel n → EReal} {m : ℕ}
    {k : ComplexModel n → ℂ} {b : ComplexModel n → ℝ} {w : ComplexModel n}
    (hu : u w = (((m : ℝ) : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (‖k w‖ ^ 2)) +
      (b w : EReal)) (hk : k w ≠ 0) (G : ComplexModel n → ℂ) :
    multiplierDensity u 1 G w =
      ENNReal.ofReal (‖G w‖ ^ 2 * Real.exp (-b w) / ‖k w‖ ^ (2 * m)) := by
  rw [multiplierDensity, hu, multiplierWeight_log_add hk, ← ENNReal.ofReal_mul (sq_nonneg _),
    mul_div_assoc]

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

omit [IsComplexManifold n X] in
/-- **The weight in the preferred chart at a point of `V`**: near `e y`, `φ_N ∘ e⁻¹ =
(N + 1) log |g ∘ e⁻¹|² + b` with `g` a local equation of `D` near `y` and `b` continuous. -/
theorem exists_chart_weight_presentation {π : Z → X} (hπc : Continuous π)
    {D : EffectiveDivisor n Z} {E : MeteredEffectiveQDivisor n Z}
    (hE : DivisorMetric.IsDivisorMetric D E) (d : ComplexChart n X) {W : Set (ComplexModel n)}
    (hW : IsOpen W) {ρ : ComplexModel n → ℝ} (hρ : ContinuousOn ρ W) {h : Z → ℝ}
    (hh : ChartSmooth (n := n) h) (N : ℕ) (a : ℝ) {y : Z}
    (hy : y ∈ π ⁻¹' (d.val.source ∩ d.val ⁻¹' W)) :
    ∃ (Vy : Set Z) (g : Z → ℂ), IsOpen Vy ∧ y ∈ Vy ∧ IsLocalEquationOn D.ideal Vy g ∧
      ∃ (O : Set (ComplexModel n)) (b : ComplexModel n → ℝ),
        IsOpen O ∧ (complexChartAt (n := n) y).val y ∈ O ∧
        O ⊆ (complexChartAt (n := n) y).val.target ∩
          (complexChartAt (n := n) y).val.symm ⁻¹' (Vy ∩ π ⁻¹' (d.val.source ∩ d.val ⁻¹' W)) ∧
        ContinuousOn b O ∧
        ∀ w ∈ O, chartFunction (relgenWeight π E d ρ h N a) (complexChartAt (n := n) y) w =
          ((((N : ℝ) + 1 : ℝ) : ℝ) : EReal) *
            ENNReal.log (ENNReal.ofReal (‖g ((complexChartAt (n := n) y).val.symm w)‖ ^ 2)) +
            (b w : EReal) := by
  set e := complexChartAt (n := n) y with he
  obtain ⟨Vy, hVy, hyVy, g, hg, hE', hE'c, hw⟩ := exists_localEquation_of_isDivisorMetric hE y
  have hpre : IsOpen (π ⁻¹' (d.val.source ∩ d.val ⁻¹' W)) :=
    (d.val.isOpen_inter_preimage hW).preimage hπc
  set O := e.val.target ∩ e.val.symm ⁻¹' (Vy ∩ π ⁻¹' (d.val.source ∩ d.val ⁻¹' W)) with hO
  have hOo : IsOpen O := e.val.isOpen_inter_preimage_symm (hVy.inter hpre)
  have hye : y ∈ e.val.source := mem_complexChartAt_source y
  have hyO : e.val y ∈ O :=
    ⟨e.val.map_source hye, by rw [mem_preimage, e.val.left_inv hye]; exact ⟨hyVy, hy⟩⟩
  refine ⟨Vy, g, hVy, hyVy, hg, O, fun w =>
    ((N : ℝ) + 1) * hE' (e.val.symm w) + a * (ρ (d.val (π (e.val.symm w))) + h (e.val.symm w)),
    hOo, hyO, subset_rfl, ?_, ?_⟩
  · have hsymm : ContinuousOn e.val.symm O := e.val.continuousOn_symm.mono fun w hw => hw.1
    have h1 : ContinuousOn (fun w => hE' (e.val.symm w)) O :=
      hE'c.comp hsymm fun w hw => hw.2.1
    have h2 : ContinuousOn (fun w => ρ (d.val (π (e.val.symm w)))) O := by
      refine hρ.comp ?_ fun w hw => hw.2.2.2
      exact d.val.continuousOn.comp (hπc.continuousOn.comp hsymm fun w _ => mem_univ _)
        fun w hw => hw.2.2.1
    have h3 : ContinuousOn (fun w => h (e.val.symm w)) O :=
      ((hh e).continuousOn).mono fun w hw => hw.1
    exact (continuousOn_const.mul h1).add (continuousOn_const.mul (h2.add h3))
  · intro w hwO
    simp only [chartFunction, relgenWeight]
    rw [hw _ hwO.2.1, generatorLog_eq_log_sum]
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rw [ereal_mul_add_coe (by positivity), add_assoc, ← EReal.coe_add]

omit [IsComplexManifold n Z] in
/-- A local equation, read in a chart, vanishes identically near no point. -/
theorem frequently_ne_zero_comp_symm {Vy : Set Z} {g : Z → ℂ}
    (hg : ∀ W : Set Z, IsOpen W → W ⊆ Vy → W.Nonempty → ∃ t ∈ W, g t ≠ 0)
    (e : ComplexChart n Z) {O : Set (ComplexModel n)} (hO : IsOpen O)
    (hOsub : O ⊆ e.val.target ∩ e.val.symm ⁻¹' Vy) :
    ∀ w ∈ O, ∃ᶠ v in 𝓝 w, g (e.val.symm v) ≠ 0 := by
  intro w hw
  rw [Filter.frequently_iff]
  intro N hN
  obtain ⟨N', hN'sub, hN'o, hwN'⟩ := _root_.mem_nhds_iff.mp hN
  have hopen : IsOpen (e.val.source ∩ e.val ⁻¹' (N' ∩ O)) :=
    e.val.isOpen_inter_preimage (hN'o.inter hO)
  have hsub : e.val.source ∩ e.val ⁻¹' (N' ∩ O) ⊆ Vy := by
    intro t ht
    have h1 := (hOsub ht.2.2).2
    rwa [mem_preimage, e.val.left_inv ht.1] at h1
  have hne : (e.val.source ∩ e.val ⁻¹' (N' ∩ O)).Nonempty := by
    refine ⟨e.val.symm w, e.val.map_target (hOsub hw).1, ?_⟩
    rw [mem_preimage, e.val.right_inv (hOsub hw).1]
    exact ⟨hwN', hw⟩
  obtain ⟨t, ht, hgt⟩ := hg _ hopen hsub hne
  refine ⟨e.val t, hN'sub ht.2.1, ?_⟩
  rwa [e.val.left_inv ht.1]

omit [IsComplexManifold n X] in
/-- **Germs of `𝓘(φ_N)` are multiples of `g^{N+1}`** (from `L²` divisibility), in the chart at
the point. -/
theorem exists_chart_factor_of_mem_multiplierIdeal (hdiv : L2DivisibilityStatement)
    {π : Z → X} {D : EffectiveDivisor n Z} {E : MeteredEffectiveQDivisor n Z}
    {d : ComplexChart n X} {ρ : ComplexModel n → ℝ} {h : Z → ℝ} {N : ℕ} {a : ℝ} {y : Z}
    {Vy : Set Z} {g : Z → ℂ} (hg : IsLocalEquationOn D.ideal Vy g) {O : Set (ComplexModel n)}
    {b : ComplexModel n → ℝ} (hO : IsOpen O) (hyO : (complexChartAt (n := n) y).val y ∈ O)
    (hOsub : O ⊆ (complexChartAt (n := n) y).val.target ∩
      (complexChartAt (n := n) y).val.symm ⁻¹' Vy)
    (hb : ContinuousOn b O)
    (hpres : ∀ w ∈ O, chartFunction (relgenWeight π E d ρ h N a) (complexChartAt (n := n) y) w =
      ((((N : ℝ) + 1 : ℝ) : ℝ) : EReal) *
        ENNReal.log (ENNReal.ofReal (‖g ((complexChartAt (n := n) y).val.symm w)‖ ^ 2)) +
        (b w : EReal))
    {F : Z → ℂ} (hF : (multiplierIdeal (n := n) 1 (relgenWeight π E d ρ h N a)).mem y F) :
    ∃ A : ComplexModel n → ℂ,
      (∀ᶠ w in 𝓝 ((complexChartAt (n := n) y).val y), DifferentiableAt ℂ A w) ∧
      ∀ᶠ w in 𝓝 ((complexChartAt (n := n) y).val y),
        F ((complexChartAt (n := n) y).val.symm w) =
          A w * g ((complexChartAt (n := n) y).val.symm w) ^ (N + 1) := by
  obtain ⟨-, -, U₀, hU₀, hpU₀, hFd, -, hFint⟩ := hF
  set e := complexChartAt (n := n) y with he
  set p := e.val y
  have hpres' : ∀ w ∈ O, chartFunction (relgenWeight π E d ρ h N a) e w =
      ((((N + 1 : ℕ) : ℝ) : ℝ) : EReal) *
        ENNReal.log (ENNReal.ofReal (‖g (e.val.symm w)‖ ^ 2)) + (b w : EReal) := by
    intro w hw
    rw [hpres w hw]
    push_cast
    rfl
  set k : ComplexModel n → ℂ := fun w => g (e.val.symm w)
  have hkd : DifferentiableOn ℂ k O :=
    (MeteredDivisorPositivity.differentiableOn_comp_chartSymm e hg.1).mono hOsub
  have hkfreq := frequently_ne_zero_comp_symm hg.2.1 e hO hOsub
  -- a small ball on which `b` is bounded
  have hbc : ContinuousAt b p := hb.continuousAt (hO.mem_nhds hyO)
  obtain ⟨r₀, hr₀, hr₀s⟩ := Metric.isOpen_iff.mp (hU₀.inter hO) p ⟨hpU₀, hyO⟩
  obtain ⟨r₁, hr₁, hr₁s⟩ := Metric.eventually_nhds_iff_ball.mp
    (hbc.eventually (Metric.ball_mem_nhds (b p) one_pos))
  set r := min r₀ r₁ with hr
  have hr0 : 0 < r := lt_min hr₀ hr₁
  have hballO : ball p r ⊆ U₀ ∩ O := (ball_subset_ball (min_le_left _ _)).trans hr₀s
  have hbM : ∀ w ∈ ball p r, |b w| ≤ |b p| + 1 := by
    intro w hw
    have h1 : dist (b w) (b p) < 1 := hr₁s w (ball_subset_ball (min_le_right _ _) hw)
    rw [Real.dist_eq] at h1
    have := abs_sub_abs_le_abs_sub (b w) (b p)
    linarith
  have hae : ∀ᵐ w ∂(volume.restrict (ball p r)), k w ≠ 0 :=
    ae_restrict_of_ae_restrict_of_subset (fun w hw => (hballO hw).2)
      (LelongPoincareDivisor.ae_ne_zero hO hkd hkfreq)
  -- the quotient is square integrable
  have hfin : (∫⁻ w in ball p r, ENNReal.ofReal (‖F (e.val.symm w)‖ ^ 2) /
      ENNReal.ofReal (‖k w‖ ^ (2 * (N + 1)))) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top
      (ENNReal.ofReal_ne_top (r := Real.exp (|b p| + 1)))
      (ne_top_of_le_ne_top hFint.ne (lintegral_mono_set (fun w hw => (hballO hw).1)))) ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [hae, ae_restrict_mem measurableSet_ball] with w hkw hw
    have hden : multiplierDensity (chartFunction (relgenWeight π E d ρ h N a) e) 1
        (fun z => F (e.val.symm z)) w = ENNReal.ofReal (‖F (e.val.symm w)‖ ^ 2 *
          Real.exp (-b w) / ‖k w‖ ^ (2 * (N + 1))) :=
      multiplierDensity_of_presentation (k := k) (hpres' w (hballO hw).2) hkw _
    rw [hden]
    have hk2 : 0 < ‖k w‖ ^ (2 * (N + 1)) := pow_pos (norm_pos_iff.mpr hkw) _
    rw [← ENNReal.ofReal_div_of_pos hk2, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hbw := abs_le.mp (hbM w hw)
    have hexp : 1 ≤ Real.exp (|b p| + 1) * Real.exp (-b w) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    have hq : 0 ≤ ‖F (e.val.symm w)‖ ^ 2 / ‖k w‖ ^ (2 * (N + 1)) := by positivity
    calc ‖F (e.val.symm w)‖ ^ 2 / ‖k w‖ ^ (2 * (N + 1))
        ≤ Real.exp (|b p| + 1) * Real.exp (-b w) *
          (‖F (e.val.symm w)‖ ^ 2 / ‖k w‖ ^ (2 * (N + 1))) := le_mul_of_one_le_left hq hexp
      _ = Real.exp (|b p| + 1) *
          (‖F (e.val.symm w)‖ ^ 2 * Real.exp (-b w) / ‖k w‖ ^ (2 * (N + 1))) := by ring
  have hne : ¬ ∀ᶠ w in 𝓝 p, k w = 0 := by
    intro hev
    exact (hkfreq p hyO).and_eventually hev |>.exists.elim fun w hw => hw.1 hw.2
  obtain ⟨A, hA, hAeq⟩ := hdiv n p r hr0 (fun w => F (e.val.symm w)) k
    (hFd.mono fun w hw => (hballO hw).1) (hkd.mono fun w hw => (hballO hw).2) hne (N + 1) hfin
  exact ⟨A, hA, hAeq⟩

omit [IsComplexManifold n X] in
/-- **A local generator of `𝒪(-(N+1)D)` lies in `𝓘(φ_N)`**: `|g^{N+1}|² e^{-φ_N} = e^{-b}` is
bounded near the point. -/
theorem mem_multiplierIdeal_localEquation_pow
    {π : Z → X} {D : EffectiveDivisor n Z} {E : MeteredEffectiveQDivisor n Z}
    {d : ComplexChart n X} {ρ : ComplexModel n → ℝ} {h : Z → ℝ} {N : ℕ} {a : ℝ} {y : Z}
    {Vy : Set Z} {g : Z → ℂ} (hVy : IsOpen Vy) (hyVy : y ∈ Vy)
    (hg : IsLocalEquationOn D.ideal Vy g) {O : Set (ComplexModel n)}
    {b : ComplexModel n → ℝ} (hO : IsOpen O) (hyO : (complexChartAt (n := n) y).val y ∈ O)
    (hOsub : O ⊆ (complexChartAt (n := n) y).val.target ∩
      (complexChartAt (n := n) y).val.symm ⁻¹' Vy)
    (hb : ContinuousOn b O)
    (hpres : ∀ w ∈ O, chartFunction (relgenWeight π E d ρ h N a) (complexChartAt (n := n) y) w =
      ((((N : ℝ) + 1 : ℝ) : ℝ) : EReal) *
        ENNReal.log (ENNReal.ofReal (‖g ((complexChartAt (n := n) y).val.symm w)‖ ^ 2)) +
        (b w : EReal)) :
    (multiplierIdeal (n := n) 1 (relgenWeight π E d ρ h N a)).mem y (fun t => g t ^ (N + 1)) := by
  have hgN := IsLocalEquationOn.succNsmul hVy hg N
  refine ⟨InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hVy hgN.1 hyVy, ?_⟩
  set e := complexChartAt (n := n) y with he
  set p := e.val y
  have hpres' : ∀ w ∈ O, chartFunction (relgenWeight π E d ρ h N a) e w =
      ((((N + 1 : ℕ) : ℝ) : ℝ) : EReal) *
        ENNReal.log (ENNReal.ofReal (‖g (e.val.symm w)‖ ^ 2)) + (b w : EReal) := by
    intro w hw
    rw [hpres w hw]
    push_cast
    rfl
  set k : ComplexModel n → ℂ := fun w => g (e.val.symm w)
  have hkd : DifferentiableOn ℂ k O :=
    (MeteredDivisorPositivity.differentiableOn_comp_chartSymm e hg.1).mono hOsub
  have hkfreq := frequently_ne_zero_comp_symm hg.2.1 e hO hOsub
  have hbc : ContinuousAt b p := hb.continuousAt (hO.mem_nhds hyO)
  obtain ⟨r₀, hr₀, hr₀s⟩ := Metric.isOpen_iff.mp hO p hyO
  obtain ⟨r₁, hr₁, hr₁s⟩ := Metric.eventually_nhds_iff_ball.mp
    (hbc.eventually (Metric.ball_mem_nhds (b p) one_pos))
  set r := min r₀ r₁ with hr
  have hr0 : 0 < r := lt_min hr₀ hr₁
  have hballO : ball p r ⊆ O := (ball_subset_ball (min_le_left _ _)).trans hr₀s
  have hbM : ∀ w ∈ ball p r, |b w| ≤ |b p| + 1 := by
    intro w hw
    have h1 : dist (b w) (b p) < 1 := hr₁s w (ball_subset_ball (min_le_right _ _) hw)
    rw [Real.dist_eq] at h1
    have := abs_sub_abs_le_abs_sub (b w) (b p)
    linarith
  have hae : ∀ᵐ w ∂(volume.restrict (ball p r)), k w ≠ 0 :=
    ae_restrict_of_ae_restrict_of_subset hballO
      (LelongPoincareDivisor.ae_ne_zero hO hkd hkfreq)
  have hden : (fun w => multiplierDensity (chartFunction (relgenWeight π E d ρ h N a) e) 1
      (fun z => g (e.val.symm z) ^ (N + 1)) w) =ᵐ[volume.restrict (ball p r)]
      fun w => ENNReal.ofReal (Real.exp (-b w)) := by
    filter_upwards [hae, ae_restrict_mem measurableSet_ball] with w hkw hw
    rw [multiplierDensity_of_presentation (k := k) (hpres' w (hballO hw)) hkw]
    congr 1
    have hk2 : 0 < ‖k w‖ ^ (2 * (N + 1)) := pow_pos (norm_pos_iff.mpr hkw) _
    change ‖k w ^ (N + 1)‖ ^ 2 * Real.exp (-b w) / ‖k w‖ ^ (2 * (N + 1)) = Real.exp (-b w)
    rw [norm_pow, ← pow_mul, mul_comm (N + 1) 2]
    field_simp
  have hbcont : ContinuousOn (fun w => ENNReal.ofReal (Real.exp (-b w))) (ball p r) :=
    ENNReal.continuous_ofReal.comp_continuousOn
      (Real.continuous_exp.comp_continuousOn ((hb.mono hballO).neg))
  refine ⟨one_pos, ball p r, isOpen_ball, mem_ball_self hr0,
    (MeteredDivisorPositivity.differentiableOn_comp_chartSymm e hgN.1).mono
      (hballO.trans hOsub), ?_, ?_⟩
  · exact (hbcont.aemeasurable measurableSet_ball).congr hden.symm
  · rw [lintegral_congr_ae hden]
    calc ∫⁻ w in ball p r, ENNReal.ofReal (Real.exp (-b w))
        ≤ ∫⁻ _ in ball p r, ENNReal.ofReal (Real.exp (|b p| + 1)) := by
          refine setLIntegral_mono' measurableSet_ball fun w hw => ?_
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
          have := abs_le.mp (hbM w hw)
          linarith
      _ < ⊤ := by
          rw [setLIntegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

omit [IsComplexManifold n X] in
/-- **The pole at `z` forces `A(z) = 1`** where `F = A g^{N+1}` near `z`. -/
theorem eq_one_of_pole_integral (hn : 0 < n)
    {π : Z → X} {D : EffectiveDivisor n Z} {E : MeteredEffectiveQDivisor n Z}
    {d : ComplexChart n X} {ρ : ComplexModel n → ℝ} {h : Z → ℝ} {N : ℕ} {a : ℝ} {y : Z}
    {Vy : Set Z} {g : Z → ℂ} (hg : IsLocalEquationOn D.ideal Vy g) {O : Set (ComplexModel n)}
    {b : ComplexModel n → ℝ} (hO : IsOpen O) (hyO : (complexChartAt (n := n) y).val y ∈ O)
    (hOsub : O ⊆ (complexChartAt (n := n) y).val.target ∩
      (complexChartAt (n := n) y).val.symm ⁻¹' Vy)
    (hb : ContinuousOn b O)
    (hpres : ∀ w ∈ O, chartFunction (relgenWeight π E d ρ h N a) (complexChartAt (n := n) y) w =
      ((((N : ℝ) + 1 : ℝ) : ℝ) : EReal) *
        ENNReal.log (ENNReal.ofReal (‖g ((complexChartAt (n := n) y).val.symm w)‖ ^ 2)) +
        (b w : EReal))
    {F : Z → ℂ} {A : ComplexModel n → ℂ}
    (hA : ∀ᶠ w in 𝓝 ((complexChartAt (n := n) y).val y), DifferentiableAt ℂ A w)
    (hAeq : ∀ᶠ w in 𝓝 ((complexChartAt (n := n) y).val y),
      F ((complexChartAt (n := n) y).val.symm w) =
        A w * g ((complexChartAt (n := n) y).val.symm w) ^ (N + 1))
    {r' : ℝ} (hr'0 : 0 < r') (hint : (∫⁻ w in ball ((complexChartAt (n := n) y).val y) r',
      multiplierDensity (chartFunction (relgenWeight π E d ρ h N a) (complexChartAt (n := n) y)) 1
        (fun w => F ((complexChartAt (n := n) y).val.symm w) -
          g ((complexChartAt (n := n) y).val.symm w) ^ (N + 1)) w /
        ENNReal.ofReal (‖w - (complexChartAt (n := n) y).val y‖ ^ (2 * n))) < ⊤) :
    A ((complexChartAt (n := n) y).val y) = 1 := by
  set e := complexChartAt (n := n) y with he
  set p := e.val y
  have hpres' : ∀ w ∈ O, chartFunction (relgenWeight π E d ρ h N a) e w =
      ((((N + 1 : ℕ) : ℝ) : ℝ) : EReal) *
        ENNReal.log (ENNReal.ofReal (‖g (e.val.symm w)‖ ^ 2)) + (b w : EReal) := by
    intro w hw
    rw [hpres w hw]
    push_cast
    rfl
  set k : ComplexModel n → ℂ := fun w => g (e.val.symm w)
  have hkd : DifferentiableOn ℂ k O :=
    (MeteredDivisorPositivity.differentiableOn_comp_chartSymm e hg.1).mono hOsub
  have hkfreq := frequently_ne_zero_comp_symm hg.2.1 e hO hOsub
  have hbc : ContinuousAt b p := hb.continuousAt (hO.mem_nhds hyO)
  obtain ⟨r₀, hr₀, hr₀s⟩ := Metric.isOpen_iff.mp hO p hyO
  obtain ⟨r₁, hr₁, hr₁s⟩ := Metric.eventually_nhds_iff_ball.mp
    ((hbc.eventually (Metric.ball_mem_nhds (b p) one_pos)).and hAeq)
  set r := min (min r₀ r₁) r' with hr
  have hr0 : 0 < r := lt_min (lt_min hr₀ hr₁) hr'0
  have hballO : ball p r ⊆ O :=
    (ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _))).trans hr₀s
  have hball1 : ball p r ⊆ ball p r₁ :=
    ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _))
  have hbM : ∀ w ∈ ball p r, |b w| ≤ |b p| + 1 := by
    intro w hw
    have h1 : dist (b w) (b p) < 1 := (hr₁s w (hball1 hw)).1
    rw [Real.dist_eq] at h1
    have := abs_sub_abs_le_abs_sub (b w) (b p)
    linarith
  have hae : ∀ᵐ w ∂(volume.restrict (ball p r)), k w ≠ 0 :=
    ae_restrict_of_ae_restrict_of_subset hballO
      (LelongPoincareDivisor.ae_ne_zero hO hkd hkfreq)
  set H : ComplexModel n → ℂ := fun w => A w - 1
  have hHc : ContinuousAt H p := (hA.self_of_nhds.continuousAt).sub continuousAt_const
  have hfin : (∫⁻ w in ball p r, ENNReal.ofReal (‖H w‖ ^ 2) *
      ENNReal.ofReal (Real.exp (-(|b p| + 1))) / ENNReal.ofReal (‖w - p‖ ^ (2 * n))) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hint.ne ?_
    refine (lintegral_mono_ae ?_).trans (lintegral_mono_set (ball_subset_ball (min_le_right _ _)))
    filter_upwards [hae, ae_restrict_mem measurableSet_ball] with w hkw hw
    refine ENNReal.div_le_div_right ?_ _
    have hFw : F (e.val.symm w) - g (e.val.symm w) ^ (N + 1) = H w * k w ^ (N + 1) := by
      rw [(hr₁s w (hball1 hw)).2]
      simp only [H, k]
      ring
    have hden := multiplierDensity_of_presentation (k := k) (hpres' w (hballO hw)) hkw
      (fun w => F (e.val.symm w) - g (e.val.symm w) ^ (N + 1))
    rw [hden, hFw, ← ENNReal.ofReal_mul (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hk2 : 0 < ‖k w‖ ^ (2 * (N + 1)) := pow_pos (norm_pos_iff.mpr hkw) _
    have heq : ‖H w * k w ^ (N + 1)‖ ^ 2 * Real.exp (-b w) / ‖k w‖ ^ (2 * (N + 1)) =
        ‖H w‖ ^ 2 * Real.exp (-b w) := by
      rw [norm_mul, norm_pow, mul_pow, ← pow_mul, mul_comm (N + 1) 2]
      field_simp
    rw [heq]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (sq_nonneg _)
    have := abs_le.mp (hbM w hw)
    linarith
  have hH0 := eq_zero_of_lintegral_div_norm_pow_ne_top hn hHc hr0 (Real.exp_pos _)
    (fun _ _ => le_rfl) hfin
  simpa [H, sub_eq_zero] using hH0

/-! ### Assembly -/

omit [IsComplexManifold n X] in
/-- The inverse of a holomorphic function that does not vanish at a point is holomorphic
there. -/
theorem holomorphicAt_inv_of_ne_zero {Vy : Set Z} (hVy : IsOpen Vy)
    {g : Z → ℂ} (hg : MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g Vy) {y : Z}
    (hy : y ∈ Vy) (hgy : g y ≠ 0) : HolomorphicAt n (fun t => (g t)⁻¹) y := by
  set e := complexChartAt (n := n) y
  have hye : y ∈ e.val.source := mem_complexChartAt_source y
  have hmem : e.val y ∈ e.val.target ∩ e.val.symm ⁻¹' Vy :=
    ⟨e.val.map_source hye, by rw [mem_preimage, e.val.left_inv hye]; exact hy⟩
  have hopen : IsOpen (e.val.target ∩ e.val.symm ⁻¹' Vy) := e.val.isOpen_inter_preimage_symm hVy
  have hgd := MeteredDivisorPositivity.differentiableOn_comp_chartSymm e hg
  have hW : ∀ᶠ w in 𝓝 (e.val y), DifferentiableAt ℂ (fun w => (g (e.val.symm w))⁻¹) w := by
    have hc : ContinuousAt (fun w => g (e.val.symm w)) (e.val y) :=
      (hgd.differentiableAt (hopen.mem_nhds hmem)).continuousAt
    have hne : g (e.val.symm (e.val y)) ≠ 0 := by rwa [e.val.left_inv hye]
    filter_upwards [hopen.mem_nhds hmem, hc.eventually_ne hne] with w hw hw0
    exact (hgd.differentiableAt (hopen.mem_nhds hw)).inv hw0
  have h := MultiplierIdealBergmanNadelManifold.holomorphicAt_comp_chart (x := y) hye hW
  refine h.congr ?_
  filter_upwards [e.val.open_source.mem_nhds hye] with t ht
  change (g (e.val.symm (e.val t)))⁻¹ = (g t)⁻¹
  rw [e.val.left_inv ht]

omit [IsComplexManifold n X] [IsComplexManifold n Z] in
/-- Transfer of a chart factorization `F ∘ e⁻¹ = A (g ∘ e⁻¹)^{N+1}` to the manifold. -/
theorem eventually_eq_mul_of_chart {y : Z} {F g : Z → ℂ}
    {A : ComplexModel n → ℂ} {N : ℕ}
    (hAeq : ∀ᶠ w in 𝓝 ((complexChartAt (n := n) y).val y),
      F ((complexChartAt (n := n) y).val.symm w) =
        A w * g ((complexChartAt (n := n) y).val.symm w) ^ (N + 1)) :
    ∀ᶠ t in 𝓝 y, F t = A ((complexChartAt (n := n) y).val t) * g t ^ (N + 1) := by
  set e := complexChartAt (n := n) y
  have hye : y ∈ e.val.source := mem_complexChartAt_source y
  filter_upwards [(e.val.continuousAt hye).eventually hAeq, e.val.open_source.mem_nhds hye]
    with t ht hts
  rwa [e.val.left_inv hts] at ht

omit [IsComplexManifold n X] in
/-- Germs of `𝒪(-(N+1)D)` are holomorphic. -/
theorem holomorphicAt_of_mem_divisorSuccNsmul
    {D : EffectiveDivisor n Z} {E : MeteredEffectiveQDivisor n Z}
    (hE : DivisorMetric.IsDivisorMetric D E) {N : ℕ} {z : Z} {b' : Z → ℂ}
    (hb' : (divisorSuccNsmul D N).ideal.mem z b') : HolomorphicAt n b' z := by
  obtain ⟨Vz, hVz, hzVz, g, hg, -, -, -⟩ := exists_localEquation_of_isDivisorMetric hE z
  exact ((IsLocalEquationOn.succNsmul hVz hg N).2.2 z hzVz b').mp hb' |>.1

/-- **Relative global generation** (blueprint `tok:relgen`) from the `L²` generation theorem
(`relgen:l2-generation`) and `L²` divisibility (`relgen:l2-divisibility`). -/
theorem relativeGlobalGeneration_of_l2Generation
    (hL2 : WeaklyPseudoconvexL2GenerationStatement.{u}) (hdiv : L2DivisibilityStatement) :
    RelativeGlobalGenerationStatement.{u} := by
  intro n X Z _ _ _ _ _ _ _ π hπ θ β D E c hc hβ hE hclass
  have hrel : ClosedRealOneOneForm.BottChernRel (ClosedRealOneOneForm.pullback hπ.1 θ)
      (β + c • E.curvature) := by
    rw [← RealBottChern.ofRepresentative_eq_iff, RealBottChern.ofRepresentative_add,
      RealBottChern.ofRepresentative_smul]
    exact hclass
  obtain ⟨h, hh, hheq⟩ := hrel
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · -- dimension zero: the constant `1` is a section generating every stalk
    refine ⟨0, fun z => ⟨univ, isOpen_univ, mem_univ _, ?_⟩⟩
    have hone : IsIdealSectionOn (divisorSuccNsmul D 0).ideal (π ⁻¹' univ) (fun _ => (1 : ℂ)) := by
      refine ⟨mdifferentiableOn_const, fun y _ => ?_⟩
      obtain ⟨Vy, hVy, hyVy, g, hg, -, -, -⟩ := exists_localEquation_of_isDivisorMetric hE y
      have hg0 := IsLocalEquationOn.succNsmul hVy hg 0
      -- in dimension zero every point is isolated
      have hiso : IsOpen ({y} : Set Z) := by
        have hsrc := (chartAt (ComplexModel n) y).open_source
        convert hsrc using 1
        ext t
        constructor
        · intro ht
          rw [mem_singleton_iff.mp ht]
          exact mem_chart_source _ y
        · intro ht
          have hinj := (chartAt (ComplexModel n) y).injOn ht (mem_chart_source _ y)
          subst hn0
          exact hinj (Subsingleton.elim _ _)
      obtain ⟨t, ht, hgt⟩ := hg.2.1 {y} hiso (singleton_subset_iff.mpr hyVy) ⟨y, rfl⟩
      rw [mem_singleton_iff.mp ht] at hgt
      have hgyN : g y ^ (0 + 1) ≠ 0 := pow_ne_zero _ hgt
      refine (hg0.2.2 y hyVy _).mpr (isInSpanAt_eq_iff.mpr ⟨holomorphicAt_const 1,
        fun t => (g t ^ (0 + 1))⁻¹, ?_, ?_⟩)
      · exact holomorphicAt_inv_of_ne_zero hVy hg0.1 hyVy hgyN
      · filter_upwards [hiso.mem_nhds rfl] with t ht
        rw [mem_singleton_iff.mp ht, inv_mul_cancel₀ hgyN]
    intro b' hb'
    have hb'hol := holomorphicAt_of_mem_divisorSuccNsmul hE hb'
    exact isInSpanAt_of_eq_mul hone hb'hol hb'hol (Eventually.of_forall fun _ => (mul_one _).symm)
  -- positive dimension
  obtain ⟨C, hC, hgen⟩ := hL2 n Z ⟨β, hβ⟩
  set K : ℝ := C * ((n : ℝ) + 1) with hK
  obtain ⟨N, hN⟩ : ∃ N : ℕ, K ≤ ((N : ℝ) + 1) / c := by
    refine ⟨⌈K * c⌉₊, ?_⟩
    rw [le_div_iff₀ hc]
    linarith [Nat.le_ceil (K * c)]
  refine ⟨N, fun z => ?_⟩
  set x := π z
  set d := complexChartAt (n := n) x
  have hxd : x ∈ d.val.source := mem_complexChartAt_source x
  obtain ⟨W, ρ, hpW, hρ⟩ := LocalPotentials.hasSmoothLocalPotentials_of_closed_typeOneOne
    θ.val θ.property.1 θ.property.2 d (d.val x) (d.val.map_source hxd)
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hρ.1 _ hpW
  set p := d.val x
  set r := ε / 2 with hr
  have hr0 : 0 < r := half_pos hε
  have hcl : closedBall p r ⊆ W := (closedBall_subset_ball (half_lt_self hε)).trans hεW
  have hcl' : closedBall p r ⊆ d.val.target := hcl.trans hρ.2.1
  have hρb : IsSmoothLocalPotential θ.val d (ball p r) ρ :=
    ⟨isOpen_ball, ball_subset_closedBall.trans hcl',
      hρ.2.2.1.mono (ball_subset_closedBall.trans hcl),
      fun w hw => hρ.2.2.2 (hcl (ball_subset_closedBall hw))⟩
  refine ⟨d.val.source ∩ d.val ⁻¹' ball p r, d.val.isOpen_inter_preimage isOpen_ball,
    ⟨hxd, mem_ball_self hr0⟩, ?_⟩
  set V := π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball p r) with hVdef
  set a := ((N : ℝ) + 1) / c with ha
  have hV := isWeaklyPseudoconvexOpen_preimage_ball hπ.1 hπ.2.1 d hcl'
  have hφ := isThetaPshPotentialOn_weight hπ.1 θ β hβ hE hc hh hheq d hρb N hN
  have hzV : z ∈ V := ⟨hxd, mem_ball_self hr0⟩
  have hρc : ContinuousOn ρ (ball p r) := hρb.2.2.1.continuousOn
  obtain ⟨Vz, g, hVz, hzVz, hg, O, b, hO, hzO, hOsub, hb, hpres⟩ :=
    exists_chart_weight_presentation hπ.1.continuous hE d isOpen_ball hρc hh N a hzV
  have hOsub' : O ⊆ (complexChartAt (n := n) z).val.target ∩
      (complexChartAt (n := n) z).val.symm ⁻¹' Vz := fun w hw => ⟨(hOsub hw).1, (hOsub hw).2.1⟩
  have hf := mem_multiplierIdeal_localEquation_pow hVz hzVz hg hO hzO hOsub' hb hpres
  obtain ⟨F, hFd, hFmem, r', hr', -, hint⟩ :=
    hgen n V hV (relgenWeight π E d ρ h N a) hφ z hzV (fun t => g t ^ (N + 1)) hf
  -- `F` is a section of `𝒪(-(N+1)D)` over `V`
  have hFsec : IsIdealSectionOn (divisorSuccNsmul D N).ideal V F := by
    refine ⟨hFd, fun y hy => ?_⟩
    obtain ⟨Vy, gy, hVy, hyVy, hgy, Oy, by', hOy, hyOy, hOysub, hby, hpresy⟩ :=
      exists_chart_weight_presentation hπ.1.continuous hE d isOpen_ball hρc hh N a hy
    obtain ⟨A, hA, hAeq⟩ := exists_chart_factor_of_mem_multiplierIdeal hdiv hgy hOy hyOy
      (fun w hw => ⟨(hOysub hw).1, (hOysub hw).2.1⟩) hby hpresy (hFmem y hy)
    have hgyN := IsLocalEquationOn.succNsmul hVy hgy N
    refine (hgyN.2.2 y hyVy F).mpr (isInSpanAt_eq_iff.mpr ⟨?_, fun t => A
      ((complexChartAt (n := n) y).val t), ?_, eventually_eq_mul_of_chart hAeq⟩)
    · exact InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hV.1 hFd hy
    · exact MultiplierIdealBergmanNadelManifold.holomorphicAt_comp_chart (x := y)
        (mem_complexChartAt_source y) hA
  -- `F = A g^{N+1}` near `z` with `A(z) = 1`
  obtain ⟨A, hA, hAeq⟩ := exists_chart_factor_of_mem_multiplierIdeal hdiv hg hO hzO hOsub' hb
    hpres (hFmem z hzV)
  have hA1 := eq_one_of_pole_integral hn hg hO hzO hOsub' hb hpres hA hAeq hr' hint
  set ez := complexChartAt (n := n) z
  have hze : z ∈ ez.val.source := mem_complexChartAt_source z
  have hAinv : ∀ᶠ w in 𝓝 (ez.val z), DifferentiableAt ℂ (fun w => (A w)⁻¹) w := by
    filter_upwards [hA, hA.self_of_nhds.continuousAt.eventually_ne (by rw [hA1]; exact one_ne_zero)]
      with w hw hw0
    exact hw.inv hw0
  have hAz : ∀ᶠ t in 𝓝 z, A (ez.val t) ≠ 0 := by
    have hc : ContinuousAt (fun t => A (ez.val t)) z :=
      hA.self_of_nhds.continuousAt.comp (ez.val.continuousAt hze)
    exact hc.eventually_ne (by rw [hA1]; exact one_ne_zero)
  have hFz : ∀ᶠ t in 𝓝 z, F t = A (ez.val t) * g t ^ (N + 1) := eventually_eq_mul_of_chart hAeq
  have hgz := IsLocalEquationOn.succNsmul hVz hg N
  intro b' hb'
  obtain ⟨hb'hol, c', hc', hc'eq⟩ := isInSpanAt_eq_iff.mp ((hgz.2.2 z hzVz b').mp hb')
  have hAinvz : HolomorphicAt n (fun t => (A (ez.val t))⁻¹) z :=
    MultiplierIdealBergmanNadelManifold.holomorphicAt_comp_chart (x := z) hze hAinv
  refine isInSpanAt_of_eq_mul (s := F) (a := fun t => c' t * (A (ez.val t))⁻¹) hFsec hb'hol
    (hc'.mul hAinvz) ?_
  filter_upwards [hc'eq, hFz, hAz] with t ht hFt hAt
  rw [ht, hFt]
  field_simp

end SGPT.Okounkov.TranscendentalRelGen
