import SGPT.Okounkov.TranscendentalL2Transport

/-!
# Solving `∂̄` on the complement of the hypersurface

Plan `tok/RELGEN3` steps P8–P9 (blueprint `l2:transported-weight`, `l2:modification-generation`,
chapter `claude-tok-l2`).

In the setting of `ModificationL2GenerationStatement`, with the hypersurface `{k = 0}` of
`exists_hypersurface`, the pole `P = q χ_P(e₀ · - e₀ z) log |e₀ · - e₀ z|²` of
`exists_pole_family`, the relative Jacobian weight `Γ = ψ_R` and the data `χ f`, put
`σ = s ∘ d⁻¹` on `Ω* = B(x₀, r₁) \ {k = 0}` and

  `Φ = (φ_N + P + Γ) ∘ σ`, `h₀ = (χ f) ∘ σ`.

`exists_solution_on_complement`: `Φ` is smooth and psh on `Ω*`, `|∂̄_ξ h₀|² ≤ g · Levi Φ (ξ)`
with `∫_{Ω*} g e^{-Φ} < ∞`, so Hörmander's estimate on `Ω*` (`exists_holomorphic_ball_inter_ne_zero`)
gives `G` holomorphic on `Ω*` with `∫_{Ω*} |h₀ - G|² e^{-Φ} < ∞`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalL2

open Set Filter MeasureTheory Metric Complex
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DivisorialChangeOfVariables
open SGPT.Foundations.Analysis.Pending.GlobalRelativeJacobianIdeal
open SGPT.Okounkov.TranscendentalRelGen

variable {n : ℕ} {X Z : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- The cut-off pole `q χ_P(e₀ · - w₀) log |e₀ · - w₀|²` on `Z`. -/
def poleWeight (e₀ : ComplexChart n Z) (χP : ComplexModel n → ℝ) (w₀ : ComplexModel n)
    (q : ℕ) : Z → ℝ :=
  chartLift e₀ fun w => (q : ℝ) * cutoffPole χP w₀ w

/-- The data `χ f`, `χ` a cut-off in the chart `e₀`. -/
def cutFunction (e₀ : ComplexChart n Z) (χD : ComplexModel n → ℝ) (f : Z → ℂ) : Z → ℂ :=
  chartLift e₀ fun w => (χD w : ℂ) * f (e₀.val.symm w)

/-- The total weight `φ_N + P + Γ` on `Z`. -/
def totalWeight (π : Z → X) (E : MeteredEffectiveQDivisor n Z) (d : ComplexChart n X)
    (ρ : ComplexModel n → ℝ) (h : Z → ℝ) (N : ℕ) (a : ℝ) (ER : MeteredEffectiveQDivisor n Z)
    (e₀ : ComplexChart n Z) (χP : ComplexModel n → ℝ) (w₀ : ComplexModel n) (q : ℕ) (t : Z) :
    ℝ :=
  realWeight π E d ρ h N a t + poleWeight e₀ χP w₀ q t + (ER.weight t).toReal

/-! ### Points of the complement -/

omit [IsComplexManifold n X] in
/-- Points of `Ω*` come from points of `Z` off the exceptional set and the divisor. -/
theorem sigma_facts {π : Z → X} (hsurj : Function.Surjective π) {B : Set X} {s : X → Z}
    (hright : ∀ x ∉ B, π (s x) = x) {E : MeteredEffectiveQDivisor n Z} {d : ComplexChart n X}
    {x₀ : ComplexModel n} {r₁ : ℝ} {k : ComplexModel n → ℂ}
    (hkzero : ∀ y : Z, π y ∈ d.val.source → d.val (π y) ∈ ball x₀ r₁ →
      (π y ∈ B ∨ E.weight y = ⊥) → k (d.val (π y)) = 0)
    {x : ComplexModel n} (hxt : x ∈ d.val.target) (hx : x ∈ ball x₀ r₁) (hkx : k x ≠ 0) :
    d.val.symm x ∉ B ∧ π (s (d.val.symm x)) = d.val.symm x ∧
      E.weight (s (d.val.symm x)) ≠ ⊥ := by
  have hxB : d.val.symm x ∉ B := by
    intro hB
    obtain ⟨y, hy⟩ := hsurj (d.val.symm x)
    apply hkx
    have h1 : π y ∈ d.val.source := by rw [hy]; exact d.val.map_target hxt
    have h2 : d.val (π y) = x := by rw [hy, d.val.right_inv hxt]
    have := hkzero y h1 (by rw [h2]; exact hx) (Or.inl (by rw [hy]; exact hB))
    rwa [h2] at this
  have hπs := hright _ hxB
  refine ⟨hxB, hπs, fun hE => hkx ?_⟩
  have h1 : π (s (d.val.symm x)) ∈ d.val.source := by rw [hπs]; exact d.val.map_target hxt
  have h2 : d.val (π (s (d.val.symm x))) = x := by rw [hπs, d.val.right_inv hxt]
  have := hkzero _ h1 (by rw [h2]; exact hx) (Or.inr hE)
  rwa [h2] at this

omit [IsComplexManifold n X] in
/-- Points of `Z` over `Ω*` are off the exceptional set, and `σ` inverts `d ∘ π` there. -/
theorem upstairs_facts {π : Z → X} {A : Set Z} {B : Set X} {s : X → Z} (hpre : π ⁻¹' B = A)
    (hleft : ∀ y ∉ A, s (π y) = y) {E : MeteredEffectiveQDivisor n Z} {d : ComplexChart n X}
    {x₀ : ComplexModel n} {r₁ : ℝ} {k : ComplexModel n → ℂ}
    (hkzero : ∀ y : Z, π y ∈ d.val.source → d.val (π y) ∈ ball x₀ r₁ →
      (π y ∈ B ∨ E.weight y = ⊥) → k (d.val (π y)) = 0)
    {y : Z} (hyd : π y ∈ d.val.source) (hyb : d.val (π y) ∈ ball x₀ r₁)
    (hky : k (d.val (π y)) ≠ 0) :
    y ∉ A ∧ s (d.val.symm (d.val (π y))) = y ∧ E.weight y ≠ ⊥ := by
  have hyB : π y ∉ B := fun hB => hky (hkzero y hyd hyb (Or.inl hB))
  have hyA : y ∉ A := fun hA => hyB (by rw [← hpre] at hA; exact hA)
  refine ⟨hyA, ?_, fun hE => hky (hkzero y hyd hyb (Or.inr hE))⟩
  rw [d.val.left_inv hyd, hleft y hyA]

/-! ### The total weight is strictly psh on the complement -/

/-- **The total weight has Levi form `≥ π β`** (blueprint `l2:transported-weight`) at points of
`V` off the exceptional set, the divisor and the pole, in the pole chart `e₀` if the point lies in
it and in the preferred chart otherwise. -/
theorem exists_hasLeviLB_totalWeight [CompactSpace Z] {π : Z → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π)
    {A : Set Z} {B : Set X} {s : X → Z} (hAc : IsClosed A) (hBc : IsClosed B)
    (hpre : π ⁻¹' B = A) (hs : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s Bᶜ)
    (hleft : ∀ y ∉ A, s (π y) = y)
    (θ : ClosedRealOneOneForm n X) (β : ClosedRealOneOneForm n Z) (hβ : β.val.IsKahler)
    {D : EffectiveDivisor n Z} {E : MeteredEffectiveQDivisor n Z}
    (hE : DivisorMetric.IsDivisorMetric D E) {c : ℝ} (hc : 0 < c) {h : Z → ℝ}
    (hh : ChartSmooth (n := n) h)
    (hheq : ∀ (e : ComplexChart n Z) (z : ComplexModel n), z ∈ e.val.target →
      (β + c • E.curvature).val.coeff e z =
        (ClosedRealOneOneForm.pullback hπ.1 θ).val.coeff e z +
          smoothDDC (fun y => h (e.val.symm y)) z)
    {ER : MeteredEffectiveQDivisor n Z}
    (hER : DivisorMetric.IsDivisorMetric (actualRelativeJacobianDivisor (n := n) hπ) ER)
    {C₂ : ℝ} (hdom : ∀ (e : ComplexChart n Z) (z : ComplexModel n), z ∈ e.val.target →
      ∀ v : ComplexModel n, 0 ≤ (-ER.curvature).val.coeff e z ![v, Complex.I • v] +
        C₂ * β.val.coeff e z ![v, Complex.I • v])
    (d : ComplexChart n X) {p : ComplexModel n} {r : ℝ} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ.val d (ball p r) ρ)
    (q N : ℕ) {CP : ℝ} (hCP : 0 ≤ CP) (hqa : (q : ℝ) * CP + C₂ + 1 ≤ ((N : ℝ) + 1) / c)
    (e₀ : ComplexChart n Z) {ε : ℝ} {χP : ComplexModel n → ℝ} {w₀ : ComplexModel n}
    (hχP : ContDiff ℝ ∞ χP) (hεt : closedBall w₀ ε ⊆ e₀.val.target)
    (hχP0 : ∀ w, ε ≤ ‖w‖ → χP w = 0)
    (hlevi : ∀ w ∈ e₀.val.target, w ≠ w₀ → ∀ v : ComplexModel n,
      -CP * (Real.pi * β.val.coeff e₀ w ![v, Complex.I • v]) ≤ leviForm (cutoffPole χP w₀) w v)
    {t : Z} (htV : t ∈ π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball p r)) (htA : t ∉ A)
    (htE : E.weight t ≠ ⊥) (ht₀ : t ∈ e₀.val.source → e₀.val t ≠ w₀) :
    ∃ e' : ComplexChart n Z, t ∈ e'.val.source ∧ (t ∈ e₀.val.source → e' = e₀) ∧
      HasLeviLB β (totalWeight π E d ρ h N (((N : ℝ) + 1) / c) ER e₀ χP w₀ q) 1 e'
        (e'.val t) := by
  set a : ℝ := ((N : ℝ) + 1) / c with ha
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  by_cases hte : t ∈ e₀.val.source
  · refine ⟨e₀, hte, fun _ => rfl, ?_⟩
    have hφ := hasLeviLB_realWeight hπ.1 θ β hβ hE hc hh hheq d hρ N htV htE e₀ hte
    have hΓ := hasLeviLB_relJacobianWeight hπ hER hAc hBc hpre hs hleft β hdom htA e₀ hte
    have hP := hasLeviLB_poleZ β e₀ hχP hlevi q hte (ht₀ hte)
    have hsum := (hφ.add hP).add hΓ
    refine hsum.mono hβ ?_
    have : (q : ℝ) * CP ≥ 0 := mul_nonneg hq0 hCP
    linarith
  · set e' := complexChartAt (n := n) t
    have hte' : t ∈ e'.val.source := mem_complexChartAt_source t
    refine ⟨e', hte', fun h => absurd h hte, ?_⟩
    have hφ := hasLeviLB_realWeight hπ.1 θ β hβ hE hc hh hheq d hρ N htV htE e' hte'
    have hΓ := hasLeviLB_relJacobianWeight hπ hER hAc hBc hpre hs hleft β hdom htA e' hte'
    have hN : IsOpen (e₀.val.symm '' closedBall w₀ ε)ᶜ :=
      (isClosed_chart_symm_image e₀ (isCompact_closedBall _ _) hεt).isOpen_compl
    have hP := hasLeviLB_of_eventually_zero β (u := poleWeight e₀ χP w₀ q) hN
      (notMem_chart_symm_image hεt hte) fun t' ht' =>
        chartLift_eq_zero e₀ (K := closedBall w₀ ε) (fun w hw => by
          rw [mem_closedBall, dist_eq_norm, not_le] at hw
          rw [cutoffPole_eq_zero hχP0 hw.le, mul_zero]) ht'
    have hsum := (hφ.add hP).add hΓ
    refine hsum.mono hβ ?_
    have : (q : ℝ) * CP ≥ 0 := mul_nonneg hq0 hCP
    linarith

/-! ### Functions read through the pole chart, along `σ` -/

omit [IsComplexManifold n X] [IsComplexManifold n Z] in
theorem chartLift_comp_sigma_eventuallyEq {B : Set X} {s : X → Z} (hBc : IsClosed B)
    (hs : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s Bᶜ)
    {d : ComplexChart n X} {e₀ : ComplexChart n Z} {α : Type*} [Zero α]
    (f₀ : ComplexModel n → α) {x : ComplexModel n} (hx : x ∈ sigmaDomain B s d e₀) :
    (fun x' => chartLift e₀ f₀ (s (d.val.symm x'))) =ᶠ[𝓝 x]
      fun x' => f₀ (coordinateMap s d e₀ x') := by
  filter_upwards [(isOpen_sigmaDomain hBc hs d e₀).mem_nhds hx] with x' hx'
  rw [chartLift_of_mem e₀ f₀ hx'.1.2]
  rfl

omit [IsComplexManifold n X] in
theorem chartLift_comp_sigma_eventually_zero {B : Set X} {s : X → Z} (hBc : IsClosed B)
    (hs : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s Bᶜ)
    {d : ComplexChart n X} {e₀ : ComplexChart n Z} {α : Type*} [Zero α]
    {f₀ : ComplexModel n → α} {K : Set (ComplexModel n)} (hK : IsCompact K)
    (hKe : K ⊆ e₀.val.target) (hf₀ : ∀ w ∉ K, f₀ w = 0) {x : ComplexModel n}
    (hx : x ∈ d.val.target) (hxB : d.val.symm x ∉ B) (hxe : s (d.val.symm x) ∉ e₀.val.source) :
    ∀ᶠ x' in 𝓝 x, chartLift e₀ f₀ (s (d.val.symm x')) = 0 := by
  have hN : IsOpen (e₀.val.symm '' K)ᶜ := (isClosed_chart_symm_image e₀ hK hKe).isOpen_compl
  have hc := continuousAt_sigma hBc hs d hx hxB
  filter_upwards [hc.eventually (hN.mem_nhds (notMem_chart_symm_image hKe hxe))] with x' hx'
  exact chartLift_eq_zero e₀ hf₀ hx'

/-- The density `|f|² |∇χ|²` of the data bound is continuous on `ℂⁿ`. -/
theorem continuous_cutDensity {χ : ComplexModel n → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {w₀ : ComplexModel n} {δ : ℝ} (hδ : 0 < δ) (hχ0 : ∀ w, δ ≤ ‖w - w₀‖ → χ w = 0)
    {f' : ComplexModel n → ℂ} (hf' : DifferentiableOn ℂ f' (ball w₀ (2 * δ))) (K : ℝ) :
    Continuous fun w => ‖f' w‖ ^ 2 * ‖fderiv ℝ χ w‖ ^ 2 / K := by
  rw [continuous_iff_continuousAt]
  intro w
  have hDχ : Continuous (fderiv ℝ χ) := hχ.continuous_fderiv (by simp)
  by_cases hw : w ∈ ball w₀ (2 * δ)
  · have hfc : ContinuousAt f' w :=
      (hf'.differentiableAt (isOpen_ball.mem_nhds hw)).continuousAt
    exact (((hfc.norm.pow 2).mul (hDχ.continuousAt.norm.pow 2)).div_const K)
  · have hfar : δ < ‖w - w₀‖ := by
      rw [mem_ball, dist_eq_norm, not_lt] at hw; linarith
    have hopen : IsOpen {u : ComplexModel n | δ < ‖u - w₀‖} :=
      isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
    refine continuousAt_const (y := (0 : ℝ)) |>.congr ?_
    filter_upwards [hopen.mem_nhds hfar] with u hu
    rw [fderiv_eq_zero_of_far hχ0 hu]
    simp

/-! ### Hörmander's estimate on the complement -/

/-- **The `∂̄` problem on the complement of the hypersurface** (blueprint
`l2:modification-generation`, first half): `G` holomorphic on `Ω* = B(x₀, r₁) \ {k = 0}` with
`∫_{Ω*} |h₀ - G|² e^{-Φ} < ∞`, `h₀ = (χ f) ∘ σ`, `Φ = (φ_N + P + Γ) ∘ σ`. -/
theorem exists_solution_on_complement [CompactSpace Z] {π : Z → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π)
    {A : Set Z} {B : Set X} {s : X → Z} (hAc : IsClosed A) (hBc : IsClosed B)
    (hpre : π ⁻¹' B = A) (hs : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s Bᶜ)
    (hright : ∀ x ∉ B, π (s x) = x) (hleft : ∀ y ∉ A, s (π y) = y)
    (θ : ClosedRealOneOneForm n X) (β : ClosedRealOneOneForm n Z) (hβ : β.val.IsKahler)
    {D : EffectiveDivisor n Z} {E : MeteredEffectiveQDivisor n Z}
    (hE : DivisorMetric.IsDivisorMetric D E) {c : ℝ} (hc : 0 < c) {h : Z → ℝ}
    (hh : ChartSmooth (n := n) h)
    (hheq : ∀ (e : ComplexChart n Z) (z : ComplexModel n), z ∈ e.val.target →
      (β + c • E.curvature).val.coeff e z =
        (ClosedRealOneOneForm.pullback hπ.1 θ).val.coeff e z +
          smoothDDC (fun y => h (e.val.symm y)) z)
    {ER : MeteredEffectiveQDivisor n Z}
    (hER : DivisorMetric.IsDivisorMetric (actualRelativeJacobianDivisor (n := n) hπ) ER)
    {C₂ : ℝ} (hdom : ∀ (e : ComplexChart n Z) (z : ComplexModel n), z ∈ e.val.target →
      ∀ v : ComplexModel n, 0 ≤ (-ER.curvature).val.coeff e z ![v, Complex.I • v] +
        C₂ * β.val.coeff e z ![v, Complex.I • v])
    (d : ComplexChart n X) {p : ComplexModel n} {r : ℝ} {ρ : ComplexModel n → ℝ}
    (hcl : closedBall p r ⊆ d.val.target) (hρ : IsSmoothLocalPotential θ.val d (ball p r) ρ)
    (q N : ℕ) {CP : ℝ} (hCP : 0 ≤ CP) (hqa : (q : ℝ) * CP + C₂ + 1 ≤ ((N : ℝ) + 1) / c)
    {z : Z} (hzA : z ∈ A) (e₀ : ComplexChart n Z) (hz₀ : z ∈ e₀.val.source) {ε : ℝ}
    {χP : ComplexModel n → ℝ} (hχP : ContDiff ℝ ∞ χP)
    (hεt : closedBall (e₀.val z) ε ⊆ e₀.val.target)
    (hχP1 : ∀ w, ‖w‖ < ε / 2 → χP w = 1) (hχP0 : ∀ w, ε ≤ ‖w‖ → χP w = 0)
    (hlevi : ∀ w ∈ e₀.val.target, w ≠ e₀.val z → ∀ v : ComplexModel n,
      -CP * (Real.pi * β.val.coeff e₀ w ![v, Complex.I • v]) ≤
        leviForm (cutoffPole χP (e₀.val z)) w v)
    {x₀ : ComplexModel n} {r₁ : ℝ} (hr₁ : closedBall x₀ r₁ ⊆ ball p r)
    {k : ComplexModel n → ℂ} (hk : DifferentiableOn ℂ k (ball x₀ r₁))
    (hkzero : ∀ y : Z, π y ∈ d.val.source → d.val (π y) ∈ ball x₀ r₁ →
      (π y ∈ B ∨ E.weight y = ⊥) → k (d.val (π y)) = 0)
    {δ : ℝ} (hδ : 0 < δ) (hδε : δ < ε / 2) {χD : ComplexModel n → ℝ} (hχD : ContDiff ℝ ∞ χD)
    (hχD1 : ∀ w, ‖w - e₀.val z‖ < δ / 2 → χD w = 1)
    (hχD0 : ∀ w, δ ≤ ‖w - e₀.val z‖ → χD w = 0)
    {f : Z → ℂ} (hfd : DifferentiableOn ℂ (fun w => f (e₀.val.symm w)) (ball (e₀.val z) (2 * δ)))
    (hfint : ∫⁻ w in ball (e₀.val z) (2 * δ), multiplierDensity
      (chartFunction (relgenWeight π E d ρ h N (((N : ℝ) + 1) / c)) e₀) 1
        (fun w => f (e₀.val.symm w)) w < ⊤)
    (hδdom : ball (e₀.val z) (2 * δ) ⊆ coordinateDomain π e₀ d ∩
      coordinateMap π e₀ d ⁻¹' ball x₀ r₁)
    {CJ : ℝ} (hCJ : ∀ w ∈ ball (e₀.val z) (2 * δ),
      complexJacobian (coordinateMap π e₀ d) w ≠ 0 →
        Complex.normSq (complexJacobian (coordinateMap π e₀ d) w) *
          Real.exp (-(ER.weight (e₀.val.symm w)).toReal) ≤ CJ)
    {m₀ : ℝ} (hm₀ : 0 < m₀) (hm₀le : ∀ w ∈ closedBall (e₀.val z) δ, ∀ v : ComplexModel n,
      m₀ * ‖v‖ ^ 2 ≤ β.val.coeff e₀ w ![v, Complex.I • v]) :
    ∃ G : ComplexModel n → ℂ, DifferentiableOn ℂ G (ball x₀ r₁ ∩ {x | k x ≠ 0}) ∧
      ∫⁻ x in ball x₀ r₁ ∩ {x | k x ≠ 0}, ENNReal.ofReal
        (‖cutFunction e₀ χD f (s (d.val.symm x)) - G x‖ ^ 2 *
          Real.exp (-totalWeight π E d ρ h N (((N : ℝ) + 1) / c) ER e₀ χP (e₀.val z) q
            (s (d.val.symm x)))) < ⊤ := by
  classical
  set a : ℝ := ((N : ℝ) + 1) / c with ha
  set w₀ := e₀.val z with hw₀
  set Ω := ball x₀ r₁ ∩ {x | k x ≠ 0} with hΩ
  set Tw := totalWeight π E d ρ h N a ER e₀ χP w₀ q with hTw
  set Φ : ComplexModel n → ℝ := fun x => Tw (s (d.val.symm x)) with hΦdef
  set ĥ : ComplexModel n → ℂ := fun w => (χD w : ℂ) * f (e₀.val.symm w) with hĥ
  set h₀ : ComplexModel n → ℂ := fun x => cutFunction e₀ χD f (s (d.val.symm x)) with hh₀
  set ĝ : ComplexModel n → ℝ := fun w =>
    ‖f (e₀.val.symm w)‖ ^ 2 * ‖fderiv ℝ χD w‖ ^ 2 / (Real.pi * m₀) with hĝ
  set g : ComplexModel n → ℝ := fun x => chartLift e₀ ĝ (s (d.val.symm x)) with hg
  have hsurj := AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hπ
  have hΩo : IsOpen Ω := hk.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
  have hballt : ball x₀ r₁ ⊆ d.val.target :=
    ball_subset_closedBall.trans (hr₁.trans (ball_subset_closedBall.trans hcl))
  have hĥs : ContDiff ℝ ∞ ĥ := contDiff_cutData hχD hδ hχD0 hfd
  have hĥ0 : ∀ w ∉ closedBall w₀ δ, ĥ w = 0 := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm, not_le] at hw
    simp [hĥ, hχD0 w hw.le]
  have hĝ0 : ∀ w ∉ closedBall w₀ δ, ĝ w = 0 := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm, not_le] at hw
    simp [hĝ, fderiv_eq_zero_of_far hχD0 hw]
  have hĝc : Continuous ĝ := continuous_cutDensity hχD hδ hχD0 hfd (Real.pi * m₀)
  have hĝnn : ∀ w, 0 ≤ ĝ w := fun w => by positivity
  have hKδ : IsCompact (closedBall w₀ δ) := isCompact_closedBall _ _
  have hKδt : closedBall w₀ δ ⊆ e₀.val.target :=
    (closedBall_subset_closedBall (by linarith)).trans hεt
  -- pointwise facts on `Ω*`
  have hpt : ∀ x ∈ Ω, x ∈ d.val.target ∧ d.val.symm x ∉ B ∧
      s (d.val.symm x) ∉ A ∧ E.weight (s (d.val.symm x)) ≠ ⊥ ∧
      s (d.val.symm x) ∈ π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball p r) ∧
      s (d.val.symm x) ≠ z := by
    intro x hx
    have hxt := hballt hx.1
    obtain ⟨hxB, hπs, hEs⟩ := sigma_facts hsurj hright hkzero hxt hx.1 hx.2
    have hsA : s (d.val.symm x) ∉ A := fun hA => hxB (by rw [← hπs]; rw [← hpre] at hA; exact hA)
    refine ⟨hxt, hxB, hsA, hEs, ⟨?_, ?_⟩, fun hz => hsA (hz ▸ hzA)⟩
    · show π (s (d.val.symm x)) ∈ d.val.source
      rw [hπs]; exact d.val.map_target hxt
    · show d.val (π (s (d.val.symm x))) ∈ ball p r
      rw [hπs, d.val.right_inv hxt]
      exact hr₁ (ball_subset_closedBall hx.1)
  -- the Levi form of `Φ`
  have hΦpt : ∀ x ∈ Ω, ∃ e' : ComplexChart n Z, s (d.val.symm x) ∈ e'.val.source ∧
      (s (d.val.symm x) ∈ e₀.val.source → e' = e₀) ∧ ContDiffAt ℝ ∞ Φ x ∧
      ∀ ξ : ComplexModel n, Real.pi * β.val.coeff e' (coordinateMap s d e' x)
        ![fderiv ℝ (coordinateMap s d e') x ξ, Complex.I • fderiv ℝ (coordinateMap s d e') x ξ] ≤
          leviForm Φ x ξ := by
    intro x hx
    obtain ⟨hxt, hxB, hsA, hEs, hsV, hsz⟩ := hpt x hx
    have ht₀ : s (d.val.symm x) ∈ e₀.val.source → e₀.val (s (d.val.symm x)) ≠ w₀ :=
      fun hte heq => hsz (e₀.val.injOn hte hz₀ heq)
    obtain ⟨e', hte', he', hlb⟩ := exists_hasLeviLB_totalWeight hπ hAc hBc hpre hs hleft θ β hβ
      hE hc hh hheq hER hdom d hρ q N hCP hqa e₀ hχP hεt hχP0 hlevi hsV hsA hEs ht₀
    obtain ⟨O, hO, hwO, hOt, hsm, hbd⟩ := hlb
    have hxσ : x ∈ sigmaDomain B s d e' := mem_sigmaDomain hxt hxB hte'
    have hSx : coordinateMap s d e' x = e'.val (s (d.val.symm x)) := rfl
    obtain ⟨hcd, hlf⟩ := leviForm_comp_sigma hBc hs d e' (u := Tw) hO hsm hxσ hwO
    refine ⟨e', hte', he', hcd, fun ξ => ?_⟩
    rw [hlf ξ]
    have := hbd _ hwO (fderiv ℝ (coordinateMap s d e') x ξ)
    rw [one_mul] at this
    exact this
  have hβnn : ∀ (e' : ComplexChart n Z) w, w ∈ e'.val.target → ∀ v : ComplexModel n,
      0 ≤ β.val.coeff e' w ![v, Complex.I • v] := by
    intro e' w hw v
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact ((hβ.1 e' w hw).2 v hv).le
  have hΦs : ContDiffOn ℝ ∞ Φ Ω := fun x hx => (hΦpt x hx).choose_spec.2.2.1.contDiffWithinAt
  have hpsh : ∀ x ∈ Ω, ∀ ξ, 0 ≤ leviForm Φ x ξ := by
    intro x hx ξ
    obtain ⟨e', hte', -, -, hbd⟩ := hΦpt x hx
    obtain ⟨hxt, hxB, -⟩ := hpt x hx
    have hSt : coordinateMap s d e' x ∈ e'.val.target := e'.val.map_source hte'
    exact (mul_nonneg Real.pi_pos.le (hβnn e' _ hSt _)).trans (hbd ξ)
  -- smoothness of the data and the `∂̄` bound
  have hh₀s : ContDiffOn ℝ ∞ h₀ Ω := by
    intro x hx
    obtain ⟨hxt, hxB, -⟩ := hpt x hx
    by_cases hxe : s (d.val.symm x) ∈ e₀.val.source
    · have hxσ : x ∈ sigmaDomain B s d e₀ := mem_sigmaDomain hxt hxB hxe
      have hev := chartLift_comp_sigma_eventuallyEq hBc hs ĥ hxσ
      have h2 : ContDiffAt ℝ ∞ (coordinateMap s d e₀) x :=
        (contDiffAt_coordinateMap_sigma hBc hs d e₀ hxσ).restrict_scalars ℝ
      exact ((hĥs.contDiffAt.comp x h2).congr_of_eventuallyEq hev).contDiffWithinAt
    · have hev := chartLift_comp_sigma_eventually_zero hBc hs hKδ hKδt hĥ0 hxt hxB hxe
      exact (contDiffAt_const (c := (0 : ℂ)) |>.congr_of_eventuallyEq hev).contDiffWithinAt
  have hgc : ContinuousOn g Ω := by
    intro x hx
    obtain ⟨hxt, hxB, -⟩ := hpt x hx
    by_cases hxe : s (d.val.symm x) ∈ e₀.val.source
    · have hxσ : x ∈ sigmaDomain B s d e₀ := mem_sigmaDomain hxt hxB hxe
      have hev := chartLift_comp_sigma_eventuallyEq hBc hs ĝ hxσ
      exact ((hĝc.continuousAt.comp
        (contDiffAt_coordinateMap_sigma hBc hs d e₀ hxσ).continuousAt).congr
          hev.symm).continuousWithinAt
    · have hev := chartLift_comp_sigma_eventually_zero hBc hs hKδ hKδt hĝ0 hxt hxB hxe
      exact (continuousAt_const.congr (hev.mono fun x' hx' => hx'.symm)).continuousWithinAt
  have hg0 : ∀ x ∈ Ω, 0 ≤ g x := by
    intro x _
    simp only [hg, chartLift]
    split_ifs
    · exact hĝnn _
    · exact le_rfl
  have hfg : ∀ x ∈ Ω, ∀ ξ : ComplexModel n,
      ‖CauchyGreen.dbarDir ξ h₀ x‖ ^ 2 ≤ g x * leviForm Φ x ξ := by
    intro x hx ξ
    obtain ⟨hxt, hxB, -⟩ := hpt x hx
    obtain ⟨e', hte', he', -, hbd⟩ := hΦpt x hx
    have hLnn := hpsh x hx ξ
    by_cases hxe : s (d.val.symm x) ∈ e₀.val.source
    · have he'0 : e' = e₀ := he' hxe
      subst he'0
      have hxσ : x ∈ sigmaDomain B s d e' := mem_sigmaDomain hxt hxB hxe
      set S := coordinateMap s d e' with hS
      set η := fderiv ℝ S x ξ with hη
      have hev := chartLift_comp_sigma_eventuallyEq hBc hs ĥ hxσ
      have hSd : DifferentiableAt ℂ S x :=
        (contDiffAt_coordinateMap_sigma hBc hs d e' hxσ).differentiableAt (by simp)
      have hev' : h₀ =ᶠ[𝓝 x] fun x' => ĥ (S x') := hev
      have hdbar : CauchyGreen.dbarDir ξ h₀ x = CauchyGreen.dbarDir η ĥ (S x) := by
        rw [show CauchyGreen.dbarDir ξ h₀ x = CauchyGreen.dbarDir ξ (fun x' => ĥ (S x')) x by
          simp only [CauchyGreen.dbarDir, hev'.fderiv_eq]]
        exact dbarDir_comp_of_differentiableAt hSd (hĥs.differentiable (by simp) _) ξ
      have hnorm := norm_dbarDir_cutData_le hχD hδ hχD0 hfd (S x) η
      have hgx : g x = ĝ (S x) := chartLift_of_mem e' ĝ hxe
      rw [hdbar, hgx]
      by_cases hfar : δ < ‖S x - w₀‖
      · have h0 : fderiv ℝ χD (S x) = 0 := fderiv_eq_zero_of_far hχD0 hfar
        rw [h0, norm_zero, mul_zero, zero_mul] at hnorm
        have : CauchyGreen.dbarDir η ĥ (S x) = 0 := norm_le_zero_iff.mp hnorm
        rw [this, norm_zero]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        exact mul_nonneg (hĝnn _) hLnn
      · push Not at hfar
        have hSK : S x ∈ closedBall w₀ δ := by rw [mem_closedBall, dist_eq_norm]; exact hfar
        have hm := hm₀le _ hSK η
        have hb := hbd ξ
        have h1 : ‖CauchyGreen.dbarDir η ĥ (S x)‖ ^ 2 ≤
            (‖f (e'.val.symm (S x))‖ * ‖fderiv ℝ χD (S x)‖ * ‖η‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm 2
        have h2 : (‖f (e'.val.symm (S x))‖ * ‖fderiv ℝ χD (S x)‖ * ‖η‖) ^ 2 =
            ĝ (S x) * (Real.pi * (m₀ * ‖η‖ ^ 2)) := by
          simp only [hĝ]
          field_simp
        have h3 : ĝ (S x) * (Real.pi * (m₀ * ‖η‖ ^ 2)) ≤ ĝ (S x) * leviForm Φ x ξ := by
          refine mul_le_mul_of_nonneg_left ?_ (hĝnn _)
          refine le_trans ?_ hb
          exact mul_le_mul_of_nonneg_left hm Real.pi_pos.le
        linarith
    · have hev := chartLift_comp_sigma_eventually_zero hBc hs hKδ hKδt hĥ0 hxt hxB hxe
      have hev' : h₀ =ᶠ[𝓝 x] fun _ => (0 : ℂ) := hev
      have h0 : CauchyGreen.dbarDir ξ h₀ x = 0 := by
        simp [CauchyGreen.dbarDir, hev'.fderiv_eq]
      rw [h0, norm_zero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact mul_nonneg (hg0 x hx) hLnn
  -- the integral of `g e^{-Φ}`, by the change of variables along `d ∘ π`
  set F₀ := coordinateMap π e₀ d with hF₀
  have hF₀c : ContinuousOn F₀ (coordinateDomain π e₀ d) :=
    (coordinateMap_contDiffOn hπ.1 e₀ d).continuousOn
  set U₁ := ball w₀ (2 * δ) ∩ F₀ ⁻¹' Ω with hU₁
  have hU₁d : U₁ ⊆ coordinateDomain π e₀ d := fun w hw => (hδdom hw.1).1
  have hU₁o : IsOpen U₁ := by
    have : U₁ = ball w₀ (2 * δ) ∩ (coordinateDomain π e₀ d ∩ F₀ ⁻¹' Ω) := by
      ext w; constructor
      · rintro ⟨hw1, hw2⟩; exact ⟨hw1, (hδdom hw1).1, hw2⟩
      · rintro ⟨hw1, -, hw2⟩; exact ⟨hw1, hw2⟩
    rw [this]
    exact isOpen_ball.inter (hF₀c.isOpen_inter_preimage (coordinateDomain_isOpen hπ.1 e₀ d) hΩo)
  have hU₁pt : ∀ w ∈ U₁, e₀.val.symm w ∈ e₀.val.source ∧ π (e₀.val.symm w) ∈ d.val.source ∧
      e₀.val.symm w ∉ A ∧ s (d.val.symm (F₀ w)) = e₀.val.symm w ∧
      E.weight (e₀.val.symm w) ≠ ⊥ := by
    intro w hw
    have hwd := hU₁d hw
    have hFw : F₀ w = d.val (π (e₀.val.symm w)) := rfl
    obtain ⟨hA', hs', hE'⟩ := upstairs_facts hpre hleft hkzero hwd.2 (by rw [← hFw]; exact hw.2.1)
      (by rw [← hFw]; exact hw.2.2)
    exact ⟨e₀.val.map_target hwd.1, hwd.2, hA', hs', hE'⟩
  have hσc : ContinuousOn (fun x => s (d.val.symm x)) Ω := fun x hx =>
    (continuousAt_sigma hBc hs d (hpt x hx).1 (hpt x hx).2.1).continuousWithinAt
  set T := Ω ∩ (fun x => s (d.val.symm x)) ⁻¹' (e₀.val.source ∩ e₀.val ⁻¹' ball w₀ (2 * δ))
    with hT
  have hTo : IsOpen T := hσc.isOpen_inter_preimage hΩo
    (e₀.val.isOpen_inter_preimage isOpen_ball)
  have hTim : T = F₀ '' U₁ := by
    ext x; constructor
    · rintro ⟨hxΩ, hxe, hxb⟩
      obtain ⟨hxt, hxB, -⟩ := hpt x hxΩ
      have hπs : π (s (d.val.symm x)) = d.val.symm x := hright _ hxB
      have hFx : F₀ (e₀.val (s (d.val.symm x))) = x := by
        show d.val (π (e₀.val.symm (e₀.val (s (d.val.symm x))))) = x
        rw [e₀.val.left_inv hxe, hπs, d.val.right_inv hxt]
      exact ⟨e₀.val (s (d.val.symm x)), ⟨hxb, by rw [mem_preimage, hFx]; exact hxΩ⟩, hFx⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨hte, -, -, hsw, -⟩ := hU₁pt w hw
      refine ⟨hw.2, ?_, ?_⟩
      · show s (d.val.symm (F₀ w)) ∈ e₀.val.source
        rw [hsw]; exact hte
      · show e₀.val (s (d.val.symm (F₀ w))) ∈ ball w₀ (2 * δ)
        rw [hsw, e₀.val.right_inv (hU₁d hw).1]; exact hw.1
  set u : ComplexModel n → ℝ≥0∞ := fun x => ENNReal.ofReal (g x * Real.exp (-Φ x)) with hu
  have hu0 : ∀ x ∈ Ω \ T, u x = 0 := by
    intro x hx
    have hgx : g x = 0 := by
      by_cases hxe : s (d.val.symm x) ∈ e₀.val.source
      · have hxb : e₀.val (s (d.val.symm x)) ∉ ball w₀ (2 * δ) := fun hb => hx.2 ⟨hx.1, hxe, hb⟩
        simp only [hg]
        rw [chartLift_of_mem e₀ ĝ hxe]
        refine hĝ0 _ fun hK => hxb ?_
        rw [mem_closedBall] at hK
        rw [mem_ball]; linarith
      · simp only [hg, chartLift, if_neg hxe]
    simp [hu, hgx]
  -- a bound for `|∇χ|`
  obtain ⟨Mχ, hMχ⟩ := hKδ.exists_bound_of_continuousOn
    (hχD.continuous_fderiv (by simp)).continuousOn
  set M := max Mχ 0 with hM
  set K : ℝ := max CJ 0 * Real.exp (-((q : ℝ) * Real.log (δ ^ 2 / 4))) * M ^ 2 /
    (Real.pi * m₀) with hK
  have hpt₁ : ∀ w ∈ U₁, ENNReal.ofReal (Complex.normSq (complexJacobian F₀ w)) * u (F₀ w) ≤
      ENNReal.ofReal K * multiplierDensity
        (chartFunction (relgenWeight π E d ρ h N a) e₀) 1 (fun w => f (e₀.val.symm w)) w := by
    intro w hw
    obtain ⟨hte, hπt, htA, hsw, htE⟩ := hU₁pt w hw
    set t := e₀.val.symm w with ht
    have hwt : w ∈ e₀.val.target := (hU₁d hw).1
    have hgw : g (F₀ w) = ĝ w := by
      simp only [hg]; rw [hsw, chartLift_symm e₀ ĝ hwt]
    have hΦw : Φ (F₀ w) = Tw t := by simp only [hΦdef]; rw [hsw]
    have hφN : relgenWeight π E d ρ h N a t = (realWeight π E d ρ h N a t : EReal) :=
      relgenWeight_eq_realWeight htE (weight_ne_top_of_isDivisorMetric hE t)
    have hdens : multiplierDensity (chartFunction (relgenWeight π E d ρ h N a) e₀) 1
        (fun w => f (e₀.val.symm w)) w = ENNReal.ofReal (‖f t‖ ^ 2 *
          Real.exp (-realWeight π E d ρ h N a t)) := by
      simp only [multiplierDensity, chartFunction]
      rw [← ht, hφN, multiplierWeight_coe, one_mul, ← ENNReal.ofReal_mul (sq_nonneg _)]
    rw [hdens, hu]
    simp only
    rw [hgw, hΦw, ← ENNReal.ofReal_mul (Complex.normSq_nonneg _),
      ← ENNReal.ofReal_mul (by rw [hK]; positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases hĝw : ĝ w = 0
    · rw [hĝw, zero_mul, mul_zero]
      positivity
    -- `∇χ ≠ 0` forces `δ/2 ≤ |w - w₀| ≤ δ`
    have hDχ : fderiv ℝ χD w ≠ 0 := by
      intro h0; apply hĝw; simp [hĝ, h0]
    have hwδ : ‖w - w₀‖ ≤ δ := by
      by_contra hc
      exact hDχ (fderiv_eq_zero_of_far hχD0 (lt_of_not_ge hc))
    have hwδ' : δ / 2 ≤ ‖w - w₀‖ := by
      by_contra hc
      push Not at hc
      apply hDχ
      have hopen : IsOpen {u : ComplexModel n | ‖u - w₀‖ < δ / 2} :=
        isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
      have hev : χD =ᶠ[𝓝 w] fun _ => (1 : ℝ) := by
        filter_upwards [hopen.mem_nhds hc] with u hu
        exact hχD1 u hu
      rw [hev.fderiv_eq, fderiv_const_apply]
    have hwK : w ∈ closedBall w₀ δ := by rw [mem_closedBall, dist_eq_norm]; exact hwδ
    -- the pole is bounded below on the support of `∇χ`
    have hP : poleWeight e₀ χP w₀ q t = (q : ℝ) * Real.log (‖w - w₀‖ ^ 2) := by
      simp only [poleWeight, ht]
      rw [chartLift_symm e₀ _ hwt, cutoffPole_eq_log hχP1 (by linarith)]
    have hPlow : (q : ℝ) * Real.log (δ ^ 2 / 4) ≤ poleWeight e₀ χP w₀ q t := by
      rw [hP]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg q)
      refine Real.log_le_log (by positivity) ?_
      have : (δ / 2) ^ 2 ≤ ‖w - w₀‖ ^ 2 := pow_le_pow_left₀ (by positivity) hwδ' 2
      linarith
    -- the Jacobian against the relative Jacobian weight
    have hJ : complexJacobian F₀ w ≠ 0 := by
      have := complexJacobian_coordinateMap_ne_zero hπ.1 hAc hBc hpre hs hleft e₀ d hte hπt htA
      rwa [e₀.val.right_inv hwt] at this
    have hJΓ := hCJ w hw.1 hJ
    have hJΓ' : Complex.normSq (complexJacobian F₀ w) * Real.exp (-(ER.weight t).toReal) ≤
        max CJ 0 := hJΓ.trans (le_max_left _ _)
    -- `ĝ ≤ |f|² M² / (π m₀)`
    have hĝle : ĝ w ≤ ‖f t‖ ^ 2 * M ^ 2 / (Real.pi * m₀) := by
      simp only [hĝ]
      have h1 : ‖fderiv ℝ χD w‖ ≤ M := (hMχ w hwK).trans (le_max_left _ _)
      have h2 : ‖fderiv ℝ χD w‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have hπm : 0 < Real.pi * m₀ := by positivity
      rw [div_le_div_iff_of_pos_right hπm]
      exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    have hTw : Tw t = realWeight π E d ρ h N a t + poleWeight e₀ χP w₀ q t +
        (ER.weight t).toReal := rfl
    rw [hTw]
    have he1 : Real.exp (-(realWeight π E d ρ h N a t + poleWeight e₀ χP w₀ q t +
        (ER.weight t).toReal)) = Real.exp (-realWeight π E d ρ h N a t) *
          Real.exp (-poleWeight e₀ χP w₀ q t) * Real.exp (-(ER.weight t).toReal) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    have he2 : Real.exp (-poleWeight e₀ χP w₀ q t) ≤
        Real.exp (-((q : ℝ) * Real.log (δ ^ 2 / 4))) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [he1, hK]
    have hA1 := Real.exp_pos (-realWeight π E d ρ h N a t)
    have hA2 := Real.exp_pos (-poleWeight e₀ χP w₀ q t)
    have hA3 := Real.exp_pos (-(ER.weight t).toReal)
    have hĝnn' := hĝnn w
    have hN2 : 0 ≤ Complex.normSq (complexJacobian F₀ w) := Complex.normSq_nonneg _
    calc Complex.normSq (complexJacobian F₀ w) * (ĝ w * (Real.exp (-realWeight π E d ρ h N a t) *
          Real.exp (-poleWeight e₀ χP w₀ q t) * Real.exp (-(ER.weight t).toReal)))
        = (Complex.normSq (complexJacobian F₀ w) * Real.exp (-(ER.weight t).toReal)) *
            Real.exp (-poleWeight e₀ χP w₀ q t) * ĝ w *
              Real.exp (-realWeight π E d ρ h N a t) := by ring
      _ ≤ max CJ 0 * Real.exp (-((q : ℝ) * Real.log (δ ^ 2 / 4))) *
            (‖f t‖ ^ 2 * M ^ 2 / (Real.pi * m₀)) * Real.exp (-realWeight π E d ρ h N a t) := by
          gcongr
      _ = max CJ 0 * Real.exp (-((q : ℝ) * Real.log (δ ^ 2 / 4))) * M ^ 2 / (Real.pi * m₀) *
            (‖f t‖ ^ 2 * Real.exp (-realWeight π E d ρ h N a t)) := by ring
  have hlint : ∫⁻ x in Ω, u x < ⊤ := by
    have h1 : ∫⁻ x in Ω, u x ≤ (∫⁻ x in T, u x) + ∫⁻ x in Ω \ T, u x := by
      refine (lintegral_mono_set ?_).trans (lintegral_union_le (μ := volume) u T (Ω \ T))
      intro x hx
      by_cases hxT : x ∈ T
      · exact Or.inl hxT
      · exact Or.inr ⟨hx, hxT⟩
    have h2 : ∫⁻ x in Ω \ T, u x = 0 := by
      rw [setLIntegral_congr_fun (hΩo.measurableSet.diff hTo.measurableSet) hu0]
      simp
    have h3 : ∫⁻ x in T, u x = ∫⁻ w in U₁,
        ENNReal.ofReal (Complex.normSq (complexJacobian F₀ w)) * u (F₀ w) := by
      rw [hTim]
      exact lintegral_image_coordinateMap_eq hπ e₀ d hU₁o hU₁d u
    have h4 : ∫⁻ w in U₁, ENNReal.ofReal (Complex.normSq (complexJacobian F₀ w)) * u (F₀ w) ≤
        ENNReal.ofReal K * ∫⁻ w in ball w₀ (2 * δ), multiplierDensity
          (chartFunction (relgenWeight π E d ρ h N a) e₀) 1 (fun w => f (e₀.val.symm w)) w := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact (setLIntegral_mono' hU₁o.measurableSet hpt₁).trans
        (lintegral_mono_set inter_subset_left)
    have h1' : ∫⁻ x in Ω, u x ≤ ∫⁻ x in T, u x := by simpa [h2] using h1
    rw [h3] at h1'
    exact h1'.trans_lt (h4.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfint))
  have hΦc : ContinuousOn Φ Ω := hΦs.continuousOn
  have hgi : Integrable (fun x => g x * Real.exp (-Φ x)) (volume.restrict Ω) := by
    refine ⟨(hgc.mul (Real.continuous_exp.comp_continuousOn hΦc.neg)).aestronglyMeasurable
      hΩo.measurableSet, ?_⟩
    refine (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => ?_)).mpr hlint
    have : 0 ≤ g x := by
      simp only [hg, chartLift]
      split_ifs
      · exact hĝnn _
      · exact le_rfl
    exact mul_nonneg this (Real.exp_pos _).le
  obtain ⟨G, hG, hGbd⟩ := exists_holomorphic_ball_inter_ne_zero hk hΦs hpsh hh₀s hg0 hfg hgi
  exact ⟨G, hG, hGbd.trans_lt ENNReal.ofReal_lt_top⟩

end SGPT.Okounkov.TranscendentalL2
