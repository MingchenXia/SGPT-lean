import SGPT.Okounkov.TranscendentalBodySingDecrease
import SGPT.Okounkov.PartialBodyKahler
import SGPT.Envelopes.SourcePositiveAffineEnvelopes

/-!
# Auxiliary results for the lower bound of `thm:DXmain1` for Kähler currents

Blueprint `claude-dx-low2`, nodes `claude-dx-low2:aux-*`.

* `ereal_convex_ineq`: if `N⁻¹ η + (1 - N⁻¹) V ≤ P` and `η ≤ P` then
  `m V + b η ≤ (m + b) P` for `b ≥ m/(N-1)` (the inequality behind the book's
  `𝓘(k'(ψ + (N-1)φ_j)) ⊆ 𝓘(k'N P_θ[φ]_𝓘)`);
* `smoothOffPoleSet_of_gentle`, `smoothOffPoleSet_const_mul`: potentials with gentle analytic
  singularities (the book's `def:analy-sing`: `e^{φ/c}` smooth) are smooth off their pole set;
* `exists_gentle_kahler_qea`: a quasi-equisingular approximation of a Kähler current
  `θ + dd^c φ ≥ κ` by gentle potentials with the uniform bound `θ + dd^c φ_j ≥ κ/4`
  (`thm:qequi`);
* `sourceAffineCoefficient_of_close`: the admissibility of the coefficient `a` of
  `lma:pathoenvelope` when the two masses are close.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.IGood.DXLow2

open Set Filter
open scoped Topology ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AdmissibleCurrentFormPositivity
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityGentle
open SGPT.PSH

/-! ### An inequality of extended reals -/

/-- If `N⁻¹ η + (1 - N⁻¹) V ≤ P` and `η ≤ P`, then `m V + b η ≤ (m + b) P` for all
`m ≥ 0` and `b ≥ m/(N-1)`. -/
theorem ereal_convex_ineq {P V η : EReal} {N : ℝ} (hN : 1 < N)
    (hbar : ((N⁻¹ : ℝ) : EReal) * η + ((1 - N⁻¹ : ℝ) : EReal) * V ≤ P) (hηP : η ≤ P)
    {m b : ℝ} (hm : 0 ≤ m) (hb : m / (N - 1) ≤ b) :
    (m : EReal) * V + (b : EReal) * η ≤ ((m + b : ℝ) : EReal) * P := by
  have hN1 : 0 < N - 1 := by linarith
  have hN0 : 0 < N := by linarith
  set l : ℝ := m * N / (N - 1) with hl
  set μ : ℝ := b - m / (N - 1) with hμ
  have hl0 : 0 ≤ l := by positivity
  have hμ0 : 0 ≤ μ := by linarith
  have h1 : l * (1 - N⁻¹) = m := by rw [hl]; field_simp
  have h2 : l * N⁻¹ + μ = b := by rw [hl, hμ]; field_simp; ring
  have h3 : m + b = l + μ := by rw [← h1, ← h2]; field_simp; ring
  have hlN : (0 : EReal) ≤ ((l * N⁻¹ : ℝ) : EReal) := by exact_mod_cast by positivity
  calc (m : EReal) * V + (b : EReal) * η
      = ((l : ℝ) : EReal) * (((1 - N⁻¹ : ℝ) : EReal) * V) +
          (((l : ℝ) : EReal) * (((N⁻¹ : ℝ) : EReal) * η) + (μ : EReal) * η) := by
        rw [← h1, ← h2, ← mul_assoc, ← mul_assoc, ← EReal.coe_mul, ← EReal.coe_mul,
          EReal.coe_add, EReal.right_distrib_of_nonneg hlN (by exact_mod_cast hμ0)]
    _ = ((l : ℝ) : EReal) * (((N⁻¹ : ℝ) : EReal) * η + ((1 - N⁻¹ : ℝ) : EReal) * V) +
          (μ : EReal) * η := by
        rw [EReal.left_distrib_of_nonneg_of_ne_top (by exact_mod_cast hl0) (EReal.coe_ne_top _)]
        abel
    _ ≤ ((l : ℝ) : EReal) * P + (μ : EReal) * P := by
        gcongr
    _ = ((m + b : ℝ) : EReal) * P := by
        rw [h3, EReal.coe_add, EReal.right_distrib_of_nonneg (by exact_mod_cast hl0)
          (by exact_mod_cast hμ0)]

/-! ### Gentle singularities are smooth off their poles -/

section Smooth

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- A potential with gentle analytic singularities (`e^{φ/c}` smooth, source `def:analy-sing`) is
smooth off its pole set. -/
theorem smoothOffPoleSet_of_gentle {v : X → EReal} {c : ℚ} {𝔞 : GermIdeal n X}
    (h : HasGentleAnalyticSingularitiesOfType (n := n) v c 𝔞) :
    SmoothOffPoleSet (n := n) v := by
  obtain ⟨hq, htype, hexp, hsmooth, -⟩ := h
  have hc : (0 : ℝ) < c := by exact_mod_cast htype.1
  set F : X → ℝ := fun x => (EReal.exp ((((c : ℝ)⁻¹ : ℝ) : EReal) * v x)).toReal with hF
  -- on the complement of the poles, `v = c log F`
  have hval : ∀ x, v x ≠ ⊥ → 0 < F x ∧ v x = (((c : ℝ) * Real.log (F x) : ℝ) : EReal) := by
    intro x hx
    have htop : v x ≠ ⊤ := hq.1.ne_top x
    obtain ⟨r, hr⟩ : ∃ r : ℝ, v x = r := ⟨(v x).toReal, (EReal.coe_toReal htop hx).symm⟩
    have hFx : F x = Real.exp ((c : ℝ)⁻¹ * r) := by
      simp only [hF, hr, ← EReal.coe_mul, EReal.exp_coe]
      exact ENNReal.toReal_ofReal (Real.exp_pos _).le
    refine ⟨hFx ▸ Real.exp_pos _, ?_⟩
    rw [hFx, Real.log_exp, hr]
    congr 1
    field_simp
  have hpos : ∀ x, 0 < F x → v x ≠ ⊥ := by
    intro x hx hbot
    simp only [hF, hbot, EReal.mul_bot_of_pos (by exact_mod_cast inv_pos.mpr hc :
      (0 : EReal) < (((c : ℝ)⁻¹ : ℝ) : EReal)), EReal.exp_bot, ENNReal.toReal_zero] at hx
    exact lt_irrefl _ hx
  intro e z hz hzp
  have hzv : v (e.val.symm z) ≠ ⊥ := hzp
  have hG := hsmooth e
  have hGz : 0 < F (e.val.symm z) := (hval _ hzv).1
  have hGc : ContinuousAt (fun y => F (e.val.symm y)) z :=
    (hG.continuousOn).continuousAt (e.val.open_target.mem_nhds hz)
  have hev : ∀ᶠ y in 𝓝 z, y ∈ e.val.target ∧ 0 < F (e.val.symm y) :=
    (e.val.open_target.eventually_mem hz).and (hGc.eventually (lt_mem_nhds hGz))
  refine ⟨fun y => (c : ℝ) * Real.log (F (e.val.symm y)), ?_, ?_⟩
  · filter_upwards [hev] with y hy
    exact contDiffAt_const.mul
      ((hG.contDiffAt (e.val.open_target.mem_nhds hy.1)).log hy.2.ne')
  · filter_upwards [hev] with y hy
    exact (hval _ (hpos _ hy.2)).2

/-- Positive multiples of potentials smooth off their poles are smooth off their poles. -/
theorem smoothOffPoleSet_const_mul {v : X → EReal} (hv : SmoothOffPoleSet (n := n) v) {a : ℝ}
    (ha : 0 < a) : SmoothOffPoleSet (n := n) (fun x => (a : EReal) * v x) := by
  intro e z hz hzp
  have hzp' : e.val.symm z ∉ poleSet v := by
    intro hbot
    apply hzp
    change (a : EReal) * v (e.val.symm z) = ⊥
    rw [show v (e.val.symm z) = ⊥ from hbot, EReal.coe_mul_bot_of_pos ha]
  obtain ⟨g, hg, heq⟩ := hv e z hz hzp'
  refine ⟨fun y => a * g y, hg.mono fun y hy => contDiffAt_const.mul hy, ?_⟩
  filter_upwards [heq] with y hy
  change (a : EReal) * v (e.val.symm y) = _
  change v (e.val.symm y) = _ at hy
  rw [hy, EReal.coe_mul]

end Smooth

/-! ### A gentle quasi-equisingular approximation of a Kähler current -/

section QEA

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]

/-- **Gentle Kähler quasi-equisingular approximation** (`thm:qequi` with the Kähler-preserving
shift): if `θ + dd^c φ ≥ κ`, there is a quasi-equisingular approximation `(φ_j)` of `φ` in
`PSH(X, θ)` by potentials with gentle analytic singularities and `θ + dd^c φ_j ≥ κ/4`. -/
theorem exists_gentle_kahler_qea {θ : ClosedRealOneOneForm n X} {κ : KahlerBackground n X}
    {φ : X → EReal} (hφ : IsThetaPshPotential (θ - κ.form).val φ) :
    ∃ U : ℕ → X → EReal, SourceQuasiEquisingularApproximation θ φ U ∧
      (∀ j, ∃ (c : ℚ) (𝔞 : GermIdeal n X), HasGentleAnalyticSingularitiesOfType (n := n) (U j) c 𝔞) ∧
      ∀ j, IsThetaPshPotential (θ - (1 / 4 : ℝ) • κ.form).val (U j) := by
  have hφ2 : IsThetaPshPotential (θ - (1 / 2 : ℝ) • κ.form).val φ := by
    refine SGPT.Okounkov.TranscendentalBody.isThetaPshPotential_of_le hφ ?_
    have heq : θ - (1 / 2 : ℝ) • κ.form - (θ - κ.form) = (1 / 2 : ℝ) • κ.form := by module
    rw [heq]
    exact KahlerDomination.isSemipositive_smul κ.isSemipositive (by norm_num)
  obtain ⟨v, hqea, hgentle⟩ := exists_sourceGentleQuasiEquisingularApproximation κ _ hφ2
  have hqθ : SourceQuasiEquisingularApproximation θ φ v := by
    refine SGPT.Okounkov.PartialBody.sourceQuasiEquisingularApproximation_of_le hqea ?_
    have heq : θ - (θ - (1 / 2 : ℝ) • κ.form) = (1 / 2 : ℝ) • κ.form := by abel
    rw [heq]
    exact KahlerDomination.isSemipositive_smul κ.isSemipositive (by norm_num)
  obtain ⟨-, -, -, ⟨ω₀, ε, hε, hterm⟩, -⟩ := hqea
  obtain ⟨C, hC, hdom⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul κ (-ω₀.form)
  have hev : ∀ᶠ j in atTop, ε j < 1 / (4 * C) :=
    hε.2.2.eventually (gt_mem_nhds (by positivity))
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp hev
  refine ⟨fun j => v (j + j₀), sourceQuasiEquisingularApproximation_tail hqθ j₀,
    fun j => ⟨_, _, (hgentle (j + j₀)).2⟩, fun j => ?_⟩
  refine SGPT.Okounkov.TranscendentalBody.isThetaPshPotential_of_le (hterm (j + j₀)) ?_
  have hεj := hj₀ (j + j₀) (Nat.le_add_left _ _)
  have hε0 := hε.1 (j + j₀)
  have heq : θ - (1 / 4 : ℝ) • κ.form - (θ - (1 / 2 : ℝ) • κ.form + ε (j + j₀) • ω₀.form) =
      ε (j + j₀) • (-ω₀.form + C • κ.form) + (1 / 4 - ε (j + j₀) * C) • κ.form := by module
  rw [heq]
  refine UniformPerturbedKahlerLowerBound.isSemipositive_add
    (KahlerDomination.isSemipositive_smul hdom hε0)
    (KahlerDomination.isSemipositive_smul κ.isSemipositive ?_)
  have : ε (j + j₀) * C < 1 / 4 := by
    rw [lt_div_iff₀ (by positivity)] at hεj
    nlinarith
  linarith

end QEA

/-! ### Admissible coefficients for `lma:pathoenvelope` -/

/-- If `p ≤ q < ∞`, `p > 0`, and `q - p < p / Nⁿ`, then `N` is an admissible coefficient for
`lma:pathoenvelope` (`SourceAffineCoefficient`). -/
theorem sourceAffineCoefficient_of_close {n : ℕ} {p q : ℝ≥0∞} {N : ℝ} (hN : 1 < N)
    (hp : 0 < p) (hpq : p ≤ q) (hq : q ≠ ⊤)
    (hclose : q.toReal - p.toReal < p.toReal / N ^ n) :
    VariableComplexAtlas.SourceAffineCoefficient n p q N := by
  refine ⟨hN, ?_⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact Or.inl hn
  rcases hpq.eq_or_lt with heq | hlt
  · exact Or.inr (Or.inl heq)
  right; right
  have hpt : 0 < p.toReal := ENNReal.toReal_pos hp.ne' (ne_top_of_le_ne_top hq hpq)
  have hlt' : p.toReal < q.toReal := (ENNReal.toReal_lt_toReal (ne_top_of_le_ne_top hq hpq) hq).mpr hlt
  have hd : 0 < q.toReal - p.toReal := by linarith
  have hN0 : 0 < N := by linarith
  have hNn : 0 < N ^ n := by positivity
  have hkey : N ^ n < q.toReal / (q.toReal - p.toReal) := by
    rw [lt_div_iff₀ hd]
    have := (lt_div_iff₀ hNn).mp hclose
    nlinarith
  have hnR : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
  calc N = (N ^ n) ^ ((n : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hN0.le hn.ne').symm
    _ < (q.toReal / (q.toReal - p.toReal)) ^ ((n : ℝ)⁻¹) :=
        Real.rpow_lt_rpow hNn.le hkey hnR

end SGPT.IGood.DXLow2
