import SGPT.Okounkov.TranscendentalRelGenLocal
import SGPT.Foundations.Analysis.Pending.MeteredDivisorPositivity
import SGPT.Foundations.Analysis.Pending.LocalPotentials
import SGPT.Foundations.Analysis.Pending.SmoothPotentialDomination
import SGPT.Foundations.Analysis.Pending.HolomorphicPullback
import SGPT.Foundations.Analysis.Pending.ConvexExhaustion
import SGPT.Foundations.Analysis.Pending.PshConvexCone
import SGPT.Foundations.Analysis.FirstPass.HolomorphicDDC

/-!
# The weight on the preimage of a coordinate ball

Blueprint node `relgen:weight` (chapter `claude-tok-relgen`). Let `π : Z → X` be holomorphic,
`θ` a closed real `(1,1)`-form on `X`, `β` a Kähler form on `Z`, `E` a metered divisor (weight
`ψ_E`, curvature `Θ_E`) and `h` a chart-smooth function with
`β + c Θ_E = π^*θ + dd^c h` (the class condition `{β} = π^*{θ} - c {D}`, `c > 0`). Let `ρ` be a
smooth local potential of `θ` on an open set `W` of a chart `d` of `X`. Then on
`π⁻¹(d⁻¹ W)` the weight

  `φ_N = (N + 1) ψ_E + ((N + 1) / c) (ρ ∘ d ∘ π + h)`

satisfies `dd^c φ_N = (N + 1) [E] + ((N + 1) / c) β`, hence `φ_N ∈ PSH(π⁻¹(d⁻¹ W), -K β)` for
every `K ≤ (N + 1) / c` (`thetaPlurisubharmonicOn_weight`). The preimage of a coordinate ball
is weakly pseudoconvex, with the exhaustion `(r² - |d ∘ π - p|²)⁻¹`
(`isWeaklyPseudoconvexOpen_preimage_ball`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalRelGen

open Set Filter Metric
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending

/-- `t (x + s) = t x + t s` in `[-∞, ∞]` for `t > 0` real and `s` real. -/
theorem ereal_mul_add_coe {t : ℝ} (ht : 0 < t) (x : EReal) (s : ℝ) :
    (t : EReal) * (x + (s : EReal)) = (t : EReal) * x + ((t * s : ℝ) : EReal) := by
  induction x using EReal.rec with
  | bot => rw [EReal.bot_add, EReal.coe_mul_bot_of_pos ht, EReal.bot_add]
  | coe u =>
      rw [← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, mul_add]
  | top => rw [EReal.top_add_coe, EReal.coe_mul_top_of_pos ht, EReal.top_add_coe]

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- The weight `φ_N = (N + 1) ψ_E + a (ρ ∘ d ∘ π + h)`. -/
def relgenWeight (π : Z → X) (E : MeteredEffectiveQDivisor n Z) (d : ComplexChart n X)
    (ρ : ComplexModel n → ℝ) (h : Z → ℝ) (N : ℕ) (a : ℝ) (y : Z) : EReal :=
  (((N : ℝ) + 1 : ℝ) : EReal) * E.weight y + ((a * (ρ (d.val (π y)) + h y) : ℝ) : EReal)

/-- **The weight is `(-K β)`-plurisubharmonic on `π⁻¹(d⁻¹ W)`** for `K ≤ a = (N + 1) / c`. -/
theorem thetaPlurisubharmonicOn_weight {π : Z → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (θ : ClosedRealOneOneForm n X) (β : ClosedRealOneOneForm n Z) (hβ : β.val.IsKahler)
    (E : MeteredEffectiveQDivisor n Z) {c : ℝ} (hc : 0 < c) {h : Z → ℝ}
    (hh : ChartSmooth (n := n) h)
    (hheq : ∀ (e : ComplexChart n Z) (z : ComplexModel n), z ∈ e.val.target →
      (β + c • E.curvature).val.coeff e z =
        (ClosedRealOneOneForm.pullback hπ θ).val.coeff e z +
          smoothDDC (fun y => h (e.val.symm y)) z)
    (d : ComplexChart n X) {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ.val d W ρ) (N : ℕ) {K : ℝ}
    (hK : K ≤ ((N : ℝ) + 1) / c) :
    ThetaPlurisubharmonicOn (-(K • β)).val (relgenWeight π E d ρ h N (((N : ℝ) + 1) / c))
      (π ⁻¹' (d.val.source ∩ d.val ⁻¹' W)) := by
  set a : ℝ := ((N : ℝ) + 1) / c with ha
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  intro e w hw hyV
  obtain ⟨W₁, ρ₁, hwW₁, hρ₁, hpsh₁⟩ := MeteredDivisorPositivity.thetaPlurisubharmonic_weight E e w hw
  obtain ⟨W₂, ρ₂, hwW₂, hρ₂⟩ := LocalPotentials.hasSmoothLocalPotentials_of_closed_typeOneOne
    β.val β.property.1 β.property.2 e w hw
  -- the coordinate representative of `π`
  set F : ComplexModel n → ComplexModel n := coordinateMap π e d with hF
  have hFcd : ContDiffOn ℂ ∞ F (coordinateDomain π e d) := coordinateMap_contDiffOn hπ e d
  have hdomo : IsOpen (coordinateDomain π e d) := coordinateDomain_isOpen hπ e d
  set W₃ : Set (ComplexModel n) := coordinateDomain π e d ∩ F ⁻¹' W with hW₃
  have hW₃o : IsOpen W₃ := hFcd.continuousOn.isOpen_inter_preimage hdomo hρ.1
  have hwW₃ : w ∈ W₃ := ⟨⟨hw, hyV.1⟩, hyV.2⟩
  set W' : Set (ComplexModel n) := (W₁ ∩ W₂) ∩ W₃ with hW'
  have hW'o : IsOpen W' := (hρ₁.1.inter hρ₂.1).inter hW₃o
  have hW'e : W' ⊆ e.val.target := fun z hz => hρ₂.2.1 hz.1.2
  refine ⟨W', fun z => -K * ρ₂ z, ⟨⟨hwW₁, hwW₂⟩, hwW₃⟩, ⟨hW'o, hW'e, ?_, ?_⟩, ?_⟩
  · exact (hρ₂.2.2.1.mono fun z hz => hz.1.2).const_smul (-K)
  · intro z hz
    have hρ₂z := hρ₂.2.2.2 hz.1.2
    have h1 : smoothDDC (fun y => -K * ρ₂ y) z = (-K) • smoothDDC ρ₂ z :=
      smoothDDC_smul hρ₂.1 hρ₂.2.2.1 (-K) hz.1.2
    rw [h1, hρ₂z, ClosedRealOneOneForm.coeff_neg, ClosedRealOneOneForm.coeff_smul]
    exact neg_smul K (β.val.coeff e z)
  -- the decomposition into a divisorial part and a smooth part
  set H : ComplexModel n → ℝ := fun z =>
    a * (ρ (F z) + h (e.val.symm z)) - ((N : ℝ) + 1) * ρ₁ z - K * ρ₂ z with hHdef
  have hsplit : (fun z => chartFunction (relgenWeight π E d ρ h N a) e z +
      ((-K * ρ₂ z : ℝ) : EReal)) = fun z =>
      (((N : ℝ) + 1 : ℝ) : EReal) * (chartFunction E.weight e z + (ρ₁ z : EReal)) +
        (H z : EReal) := by
    funext z
    simp only [chartFunction, relgenWeight, hHdef, hF, coordinateMap, Function.comp_apply]
    rw [ereal_mul_add_coe hN, add_assoc, add_assoc, ← EReal.coe_add, ← EReal.coe_add]
    congr 2
    ring
  rw [hsplit]
  refine (hpsh₁.mono fun z hz => hz.1.1).const_mul hN |>.add ?_
  -- the smooth part is plurisubharmonic
  have hρF : ContDiffOn ℝ ∞ (fun z => ρ (F z)) W₃ :=
    hρ.2.2.1.comp ((hFcd.restrict_scalars ℝ).mono inter_subset_left) fun z hz => hz.2
  have hhe : ContDiffOn ℝ ∞ (fun z => h (e.val.symm z)) e.val.target := hh e
  have hHs : ContDiffOn ℝ ∞ H W' := by
    have h1 : ContDiffOn ℝ ∞ (fun z => ρ (F z) + h (e.val.symm z)) W' :=
      (hρF.mono fun z hz => hz.2).add (hhe.mono hW'e)
    exact ((h1.const_smul a).sub ((hρ₁.2.2.1.mono fun z hz => hz.1.1).const_smul
      ((N : ℝ) + 1))).sub ((hρ₂.2.2.1.mono fun z hz => hz.1.2).const_smul K)
  refine SmoothPotentialDomination.plurisubharmonicOn_coe_of_smoothDDC_nonneg hW'o hHs ?_
  intro z hz v
  -- `dd^c H = (a - K) β`
  have hzd : z ∈ coordinateDomain π e d := hz.2.1
  have hcomp : smoothDDC (fun y => ρ (F y)) z = (ClosedRealOneOneForm.pullback hπ θ).val.coeff e z := by
    rw [HolomorphicDDC.smoothDDC_comp hW₃o hρ.1 (hFcd.mono inter_subset_left) hρ.2.2.1
      (fun y (hy : y ∈ W₃) => hy.2) hz.2, hρ.2.2.2 hz.2.2, ClosedRealOneOneForm.pullback_val,
      SmoothRealForm.pullback_coeff hπ θ.val e d hzd]
  have hsum : smoothDDC (fun y => ρ (F y) + h (e.val.symm y)) z =
      (β + c • E.curvature).val.coeff e z := by
    rw [smoothDDC_add hW'o (hρF.mono fun y hy => hy.2) (hhe.mono hW'e) hz, hcomp,
      hheq e z (hW'e hz)]
  have hH1 : smoothDDC H z =
      a • (β + c • E.curvature).val.coeff e z - ((N : ℝ) + 1) • E.curvature.val.coeff e z -
        K • β.val.coeff e z := by
    have hs1 : ContDiffOn ℝ ∞ (fun y => ρ (F y) + h (e.val.symm y)) W' :=
      (hρF.mono fun y hy => hy.2).add (hhe.mono hW'e)
    have hs2 : ContDiffOn ℝ ∞ (fun y => a * (ρ (F y) + h (e.val.symm y))) W' := hs1.const_smul a
    have hs3 : ContDiffOn ℝ ∞ (fun y => ((N : ℝ) + 1) * ρ₁ y) W' :=
      (hρ₁.2.2.1.mono fun y (hy : y ∈ W') => hy.1.1).const_smul ((N : ℝ) + 1)
    have hs4 : ContDiffOn ℝ ∞ (fun y => K * ρ₂ y) W' :=
      (hρ₂.2.2.1.mono fun y (hy : y ∈ W') => hy.1.2).const_smul K
    have e1 : smoothDDC H z = smoothDDC (fun y => a * (ρ (F y) + h (e.val.symm y)) -
        ((N : ℝ) + 1) * ρ₁ y) z - smoothDDC (fun y => K * ρ₂ y) z :=
      PositiveClasses.smoothDDC_sub hW'o (hs2.sub hs3) hs4 hz
    have e2 : smoothDDC (fun y => a * (ρ (F y) + h (e.val.symm y)) - ((N : ℝ) + 1) * ρ₁ y) z =
        smoothDDC (fun y => a * (ρ (F y) + h (e.val.symm y))) z -
          smoothDDC (fun y => ((N : ℝ) + 1) * ρ₁ y) z :=
      PositiveClasses.smoothDDC_sub hW'o hs2 hs3 hz
    have e3 : smoothDDC (fun y => a * (ρ (F y) + h (e.val.symm y))) z =
        a • smoothDDC (fun y => ρ (F y) + h (e.val.symm y)) z :=
      smoothDDC_smul hW'o hs1 a hz
    have e4 : smoothDDC (fun y => ((N : ℝ) + 1) * ρ₁ y) z =
        ((N : ℝ) + 1) • smoothDDC ρ₁ z :=
      smoothDDC_smul hρ₁.1 hρ₁.2.2.1 _ hz.1.1
    have e5 : smoothDDC (fun y => K * ρ₂ y) z = K • smoothDDC ρ₂ z :=
      smoothDDC_smul hρ₂.1 hρ₂.2.2.1 _ hz.1.2
    rw [e1, e2, e3, e4, e5, hsum, hρ₁.2.2.2 hz.1.1, hρ₂.2.2.2 hz.1.2]
  rw [hH1]
  simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
    ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
    ContinuousAlternatingMap.add_apply, smul_eq_mul]
  have hβv : 0 ≤ β.val.coeff e z ![v, Complex.I • v] := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact ((hβ.1 e z (hW'e hz)).2 v hv).le
  have hac : a * c = (N : ℝ) + 1 := by rw [ha]; field_simp
  have hKa : 0 ≤ a - K := by linarith
  have key : a * (β.val.coeff e z ![v, Complex.I • v] + c * E.curvature.val.coeff e z
      ![v, Complex.I • v]) - ((N : ℝ) + 1) * E.curvature.val.coeff e z ![v, Complex.I • v] -
      K * β.val.coeff e z ![v, Complex.I • v] = (a - K) * β.val.coeff e z ![v, Complex.I • v] := by
    rw [← hac]
    ring
  rw [key]
  exact mul_nonneg hKa hβv

/-- The weight of a divisor metric is not `-∞` everywhere on an open set. -/
theorem exists_weight_ne_bot {D : EffectiveDivisor n Z} {E : MeteredEffectiveQDivisor n Z}
    (hE : DivisorMetric.IsDivisorMetric D E) {U : Set Z} (hU : IsOpen U) {x : Z} (hx : x ∈ U) :
    ∃ y ∈ U, E.weight y ≠ ⊥ := by
  obtain ⟨V, hV, hxV, g, hg, h, -, hw⟩ := exists_localEquation_of_isDivisorMetric hE x
  obtain ⟨y, hy, hgy⟩ := hg.2.1 (U ∩ V) (hU.inter hV) inter_subset_right ⟨x, hx, hxV⟩
  refine ⟨y, hy.1, ?_⟩
  rw [hw y hy.2, generatorLog_eq_log_sum]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rw [ENNReal.log_ofReal_of_pos (by positivity), ← EReal.coe_add]
  exact EReal.coe_ne_bot _

theorem ereal_mul_add_coe_ne_bot_iff {t : ℝ} (ht : 0 < t) (x : EReal) (s : ℝ) :
    (t : EReal) * x + (s : EReal) ≠ ⊥ ↔ x ≠ ⊥ := by
  induction x using EReal.rec with
  | bot => simp [EReal.coe_mul_bot_of_pos ht]
  | coe u =>
      rw [← EReal.coe_mul, ← EReal.coe_add]
      simp only [ne_eq, EReal.coe_ne_bot, not_false_eq_true]
  | top =>
      rw [EReal.coe_mul_top_of_pos ht, EReal.top_add_coe]

omit [IsComplexManifold n X] in
theorem relgenWeight_ne_bot_iff {π : Z → X} {E : MeteredEffectiveQDivisor n Z}
    {d : ComplexChart n X} {ρ : ComplexModel n → ℝ} {h : Z → ℝ} {N : ℕ} {a : ℝ} {y : Z} :
    relgenWeight π E d ρ h N a y ≠ ⊥ ↔ E.weight y ≠ ⊥ :=
  ereal_mul_add_coe_ne_bot_iff (by positivity) _ _

/-- **The weight is a `(-K β)`-psh potential on `π⁻¹(d⁻¹ W)`** (`relgen:weight`). -/
theorem isThetaPshPotentialOn_weight {π : Z → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (θ : ClosedRealOneOneForm n X) (β : ClosedRealOneOneForm n Z) (hβ : β.val.IsKahler)
    {D : EffectiveDivisor n Z} {E : MeteredEffectiveQDivisor n Z}
    (hE : DivisorMetric.IsDivisorMetric D E) {c : ℝ} (hc : 0 < c) {h : Z → ℝ}
    (hh : ChartSmooth (n := n) h)
    (hheq : ∀ (e : ComplexChart n Z) (z : ComplexModel n), z ∈ e.val.target →
      (β + c • E.curvature).val.coeff e z =
        (ClosedRealOneOneForm.pullback hπ θ).val.coeff e z +
          smoothDDC (fun y => h (e.val.symm y)) z)
    (d : ComplexChart n X) {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ.val d W ρ) (N : ℕ) {K : ℝ}
    (hK : K ≤ ((N : ℝ) + 1) / c) :
    IsThetaPshPotentialOn (-(K • β)).val (relgenWeight π E d ρ h N (((N : ℝ) + 1) / c))
      (π ⁻¹' (d.val.source ∩ d.val ⁻¹' W)) := by
  refine ⟨thetaPlurisubharmonicOn_weight hπ θ β hβ E hc hh hheq d hρ N hK, ?_⟩
  intro x _ U hU hxU
  obtain ⟨y, hyU, hy⟩ := exists_weight_ne_bot hE hU hxU
  exact ⟨y, hyU, relgenWeight_ne_bot_iff.mpr hy⟩

/-! ### Weak pseudoconvexity of the preimage of a ball -/

/-- The exhaustion `(r² - |v - p|²)⁻¹` of the ball `B(p, r)`. -/
def ballExhaustion (p : ComplexModel n) (r : ℝ) (v : ComplexModel n) : ℝ :=
  (r ^ 2 - ‖v - p‖ ^ 2)⁻¹

theorem ballExhaustion_pos {p : ComplexModel n} {r : ℝ} {v : ComplexModel n}
    (hv : v ∈ ball p r) : 0 < ballExhaustion p r v := by
  have h1 : ‖v - p‖ < r := by rw [← dist_eq_norm]; exact hv
  have h2 : ‖v - p‖ ^ 2 < r ^ 2 := pow_lt_pow_left₀ h1 (norm_nonneg _) two_ne_zero
  exact inv_pos.mpr (by linarith)

theorem contDiffOn_ballExhaustion (p : ComplexModel n) (r : ℝ) :
    ContDiffOn ℝ ∞ (ballExhaustion p r) (ball p r) := by
  have hq : ContDiff ℝ ∞ fun v : ComplexModel n => r ^ 2 - ‖v - p‖ ^ 2 :=
    contDiff_const.sub ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))
  refine hq.contDiffOn.inv fun v hv => ?_
  exact (inv_pos.mp (ballExhaustion_pos hv)).ne'

theorem convexOn_ballExhaustion (p : ComplexModel n) (r : ℝ) :
    ConvexOn ℝ (ball p r) (ballExhaustion p r) := by
  refine ⟨convex_ball p r, fun x hx y hy a b ha hb hab => ?_⟩
  have hpos : ∀ v ∈ ball p r, 0 < r ^ 2 - ‖v - p‖ ^ 2 := fun v hv =>
    inv_pos.mp (ballExhaustion_pos hv)
  set u := r ^ 2 - ‖x - p‖ ^ 2
  set w := r ^ 2 - ‖y - p‖ ^ 2
  have hu := hpos x hx
  have hw := hpos y hy
  -- concavity of `r² - |· - p|²`
  have hconc : a * u + b * w ≤ r ^ 2 - ‖a • x + b • y - p‖ ^ 2 := by
    have hxy : a • x + b • y - p = a • (x - p) + b • (y - p) := by
      rw [smul_sub, smul_sub, ← add_sub_add_comm, ← add_smul, hab, one_smul]
    have hn : ‖a • (x - p) + b • (y - p)‖ ≤ a * ‖x - p‖ + b * ‖y - p‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    have hsq : (a * ‖x - p‖ + b * ‖y - p‖) ^ 2 ≤ a * ‖x - p‖ ^ 2 + b * ‖y - p‖ ^ 2 := by
      have hb' : b = 1 - a := by linarith
      subst hb'
      nlinarith [sq_nonneg (‖x - p‖ - ‖y - p‖), mul_nonneg ha hb]
    have h2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    rw [hxy]
    have : a * u + b * w = r ^ 2 - (a * ‖x - p‖ ^ 2 + b * ‖y - p‖ ^ 2) := by
      simp only [u, w]
      have hb' : b = 1 - a := by linarith
      subst hb'
      ring
    rw [this]
    linarith
  have hpos' : 0 < a * u + b * w := by
    rcases ha.eq_or_lt with rfl | ha'
    · simp only [zero_add, zero_mul] at hab ⊢
      rw [hab, one_mul]
      exact hw
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hu) (mul_nonneg hb hw.le)
  -- convexity of `t ↦ t⁻¹` on `(0, ∞)`
  have hinv : (a * u + b * w)⁻¹ ≤ a * u⁻¹ + b * w⁻¹ := by
    have := (convexOn_zpow (𝕜 := ℝ) (-1)).2 (mem_Ioi.mpr hu) (mem_Ioi.mpr hw) ha hb hab
    simpa [zpow_neg_one, smul_eq_mul] using this
  calc ballExhaustion p r (a • x + b • y) = (r ^ 2 - ‖a • x + b • y - p‖ ^ 2)⁻¹ := rfl
    _ ≤ (a * u + b * w)⁻¹ := inv_anti₀ hpos' hconc
    _ ≤ a * u⁻¹ + b * w⁻¹ := hinv
    _ = a • ballExhaustion p r x + b • ballExhaustion p r y := rfl

/-- **The preimage of a coordinate ball is weakly pseudoconvex**: `(r² - |d ∘ π - p|²)⁻¹` is a
smooth plurisubharmonic exhaustion of `π⁻¹(d⁻¹ B(p, r))` when `closedBall p r ⊆ d.target`. -/
theorem isWeaklyPseudoconvexOpen_preimage_ball {π : Z → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π) (hπp : IsProperMap π)
    (d : ComplexChart n X) {p : ComplexModel n} {r : ℝ} (hball : closedBall p r ⊆ d.val.target) :
    IsWeaklyPseudoconvexOpen (n := n) (π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball p r)) := by
  set V := π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball p r) with hVdef
  have hVo : IsOpen V := (d.val.isOpen_inter_preimage isOpen_ball).preimage hπ.continuous
  let ψ : Z → ℝ := fun y => ballExhaustion p r (d.val (π y))
  have hdom : ∀ e : ComplexChart n Z, e.val.target ∩ e.val.symm ⁻¹' V ⊆
      coordinateDomain π e d ∩ coordinateMap π e d ⁻¹' ball p r := by
    intro e w hw
    exact ⟨⟨hw.1, hw.2.1⟩, hw.2.2⟩
  refine ⟨hVo, ψ, ?_, ?_, ?_⟩
  · intro e
    refine ((contDiffOn_ballExhaustion p r).comp
      ((coordinateMap_contDiffOn_real hπ e d).mono fun w hw => (hdom e hw).1)
      fun w hw => (hdom e hw).2).congr fun w _ => rfl
  · intro e
    have hU : IsOpen (e.val.target ∩ e.val.symm ⁻¹' V) := e.val.isOpen_inter_preimage_symm hVo
    have hF : DifferentiableOn ℂ (coordinateMap π e d) (e.val.target ∩ e.val.symm ⁻¹' V) :=
      ((coordinateMap_contDiffOn hπ e d).differentiableOn (by simp)).mono fun w hw =>
        (hdom e hw).1
    have hpsh := plurisubharmonicOn_of_convexOn isOpen_ball (convexOn_ballExhaustion p r)
      (contDiffOn_ballExhaustion p r).continuousOn
    exact HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hU hF
      (fun w hw => (hdom e hw).2) hpsh
  · intro t
    by_cases hr : 0 < r
    swap
    · convert isCompact_empty
      ext y
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro hy
      have h1 : dist (d.val (π y)) p < r := hy.2
      exact absurd (lt_of_le_of_lt dist_nonneg h1) hr
    by_cases ht : 0 < t
    · set s := Real.sqrt (max (r ^ 2 - t⁻¹) 0) with hs
      have hsr : s < r := by
        rw [hs, Real.sqrt_lt' hr]
        exact max_lt (by linarith [inv_pos.mpr ht]) (by positivity)
      have hsub : closedBall p s ⊆ d.val.target :=
        (closedBall_subset_closedBall hsr.le).trans hball
      have hsubb : closedBall p s ⊆ ball p r := closedBall_subset_ball hsr
      set K := π ⁻¹' (d.val.symm '' closedBall p s) with hK
      have hKc : IsCompact K := hπp.isCompact_preimage
        ((isCompact_closedBall p s).image_of_continuousOn (d.val.continuousOn_symm.mono hsub))
      have hKV : K ⊆ V := by
        rintro y ⟨v, hv, hvy⟩
        have hvt : v ∈ d.val.target := hsub hv
        refine ⟨?_, ?_⟩
        · rw [← hvy]; exact d.val.map_target hvt
        · change d.val (π y) ∈ ball p r
          rw [← hvy, d.val.right_inv hvt]
          exact hsubb hv
      have hψc : ContinuousOn ψ V := by
        refine (contDiffOn_ballExhaustion p r).continuousOn.comp ?_ fun y hy => hy.2
        exact (d.val.continuousOn.comp hπ.continuous.continuousOn fun y hy => hy.1)
      have hset : {y | y ∈ V ∧ ψ y ≤ t} = K ∩ ψ ⁻¹' Iic t := by
        ext y
        constructor
        · rintro ⟨hyV, hyt⟩
          refine ⟨⟨d.val (π y), ?_, d.val.left_inv hyV.1⟩, hyt⟩
          have hpos := ballExhaustion_pos hyV.2
          have h1 : t⁻¹ ≤ r ^ 2 - ‖d.val (π y) - p‖ ^ 2 := by
            have := (inv_le_inv₀ ht hpos).mpr hyt
            simpa [ballExhaustion, inv_inv] using this
          rw [mem_closedBall, dist_eq_norm, hs]
          refine Real.le_sqrt_of_sq_le ?_
          exact le_max_of_le_left (by linarith)
        · rintro ⟨hyK, hyt⟩
          exact ⟨hKV hyK, hyt⟩
      rw [hset]
      exact hKc.of_isClosed_subset
        ((hψc.mono hKV).preimage_isClosed_of_isClosed hKc.isClosed isClosed_Iic)
        inter_subset_left
    · -- no point of `V` has `ψ ≤ t ≤ 0`
      convert isCompact_empty
      ext y
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
      intro hy
      exact lt_of_le_of_lt (not_lt.mp ht) (ballExhaustion_pos hy.2)

end SGPT.Okounkov.TranscendentalRelGen
