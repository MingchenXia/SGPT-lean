import SGPT.Envelopes.RelativeMAEuler
import SGPT.Foundations.Analysis.Pending.ActualSmoothVolumeVariationalLimitMaximizer
import SGPT.Foundations.Analysis.Pending.NaturalNormalizedThetaPshCompactness
import SGPT.Foundations.Analysis.Pending.RelativePreceqStatements

/-!
# Existence of solutions of the relative exponential Monge–Ampère equation

For a model potential `φ` with positive mass in a big class, a finite measure `ν`
charging no pluripolar set with `ν(X) > 0`, `λ > 0` and `κ > 0`, the functional
`G(v) = E(v) - κ ∫ e^{λ v} dν` attains its supremum on `E¹(X, θ; φ)`
(Xia, *Foundations of pluripotential theory*,
`thm:nonpluripolar-relative-exponential-equation`).

Writing `v = w + c` with `sup_X w = 0`, we have
`G(v) = E(w) + c ∫ θ_φ^n - κ e^{λ c} ∫ e^{λ w} dν`, `E(w) ≤ 0`, and
`∫ e^{λ w} dν` is bounded below on normalized potentials (compactness and lower
semicontinuity, `RelativeMAExpLsc`). Hence `G` is bounded above, the constants
of a maximizing sequence are bounded and its energies are bounded below. A
subsequence converges in `L¹`; the energy is upper semicontinuous and the
exponential term lower semicontinuous, so the limit is a maximizer.

Combined with the Euler–Lagrange equation (`RelativeMAEuler`) this solves
`θ_u^n = e^{λ u} ν` with `u ∈ E¹(X, θ; φ)`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Envelopes.RelativeMA

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass SGPT.Foundations.Analysis.Pending.RelativePreceqClasses
open SGPT.Foundations.Analysis.Pending.RelativeDarvasDistance

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] {θ : ClosedRealOneOneForm n M} {φ : M → EReal} {hφ : IsModelPotential θ φ}

theorem energy_model_eq_zero (omega : KahlerBackground n M) : energy θ φ hφ φ = 0 := by
  rw [SingularModelEnergyCocycle.energy_eq_of_relativeEInfinity omega θ hφ
    ⟨hφ.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩,
    RelativeEnergy.relativeEnergyOfMinimalType_self, EReal.coe_zero]

theorem relativeFiniteEnergyPreceq_model (omega : KahlerBackground n M) :
    RelativeFiniteEnergyPreceq θ φ φ hφ :=
  RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
    ⟨hφ.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩

theorem toReal_energy_nonpos_of_le (omega : KahlerBackground n M) {w : M → EReal}
    (hw : ∀ x, w x ≤ φ x) : (energy θ φ hφ w).toReal ≤ 0 := by
  have h : energy θ φ hφ w ≤ 0 := (energy_mono_of_le hw).trans (energy_model_eq_zero omega).le
  exact EReal.toReal_nonpos h

theorem modelVolume_pos (omega : KahlerBackground n M) : 0 < modelVolume θ φ hφ := by
  let : IsFiniteMeasure (diagonalPotentialMeasure θ φ hφ.plurisubharmonic) :=
    DiagonalMeasureRegularity.isFiniteMeasure_diagonalPotentialMeasure omega θ hφ.plurisubharmonic
  unfold modelVolume
  rw [measureReal_def]
  exact ENNReal.toReal_pos hφ.positive_mass.ne' (measure_ne_top _ _)

/-- Decomposition `v = w + c` with `sup w = 0` and the value of `G`. -/
theorem exists_expFunctional_decomposition (omega : KahlerBackground n M) {ν : Measure M}
    (hν : DoesNotChargeManifoldPluripolar (n := n) ν) (lam κ : ℝ) {v : M → EReal}
    (hv : RelativeFiniteEnergyPreceq θ φ v hφ) :
    ∃ (w : M → EReal) (c : ℝ), RelativeFiniteEnergyPreceq θ φ w hφ ∧ (⨆ x, w x) = 0 ∧
      (∀ x, w x ≤ φ x) ∧ v = (fun x => w x + (c : EReal)) ∧
      expFunctional θ φ hφ ν lam κ v = (energy θ φ hφ w).toReal + c * modelVolume θ φ hφ -
        κ * Real.exp (lam * c) * ∫ x, expWeight lam w x ∂ν := by
  obtain ⟨a, hwF, hw0, hwφ, -, -⟩ :=
    ActualSmoothVolumeVariationalFoundation.exists_normalized_translate omega hv
  refine ⟨fun x => v x + (a : EReal), -a, hwF, hw0, hwφ,
    (translate_translate_neg v a).symm, ?_⟩
  conv_lhs => rw [← translate_translate_neg v a]
  unfold expFunctional
  rw [toReal_energy_add_const omega hwF (-a),
    integral_expWeight_add_const hν hwF.1.plurisubharmonic (-a)]
  ring

variable [ConnectedSpace M]

/-- The exponential integral is bounded below on normalized potentials. -/
theorem exists_pos_le_integral_expWeight (omega : KahlerBackground n M)
    {ν : Measure M} [IsFiniteMeasure ν] (hν : DoesNotChargeManifoldPluripolar (n := n) ν)
    (hν0 : 0 < ν univ) {lam : ℝ} (hlam : 0 < lam) :
    ∃ a : ℝ, 0 < a ∧ ∀ w : M → EReal, IsThetaPshPotential θ.val w → (⨆ x, w x) = 0 →
      a ≤ ∫ x, expWeight lam w x ∂ν := by
  by_contra hcon
  push Not at hcon
  have hseq : ∀ j : ℕ, ∃ w : M → EReal, IsThetaPshPotential θ.val w ∧ (⨆ x, w x) = 0 ∧
      ∫ x, expWeight lam w x ∂ν < 1 / ((j : ℝ) + 1) := fun j => by
    obtain ⟨w, hw, hws, hlt⟩ := hcon (1 / ((j : ℝ) + 1)) (by positivity)
    exact ⟨w, hw, hws, hlt⟩
  choose w hw hws hwlt using hseq
  obtain ⟨v, s, hv, hvs, hs, hlim, -⟩ :=
    NaturalNormalizedThetaPshCompactness.exists_strictMono_subseq_of_sup_eq_zero
      (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega) w hw hws
  have hw0 : ∀ j x, w j x ≤ 0 := fun j x => hws j ▸ le_iSup (w j) x
  have hv0 : ∀ x, v x ≤ 0 := fun x => hvs ▸ le_iSup v x
  have hI : Tendsto (fun k => ∫ x, expWeight lam (w (s k)) x ∂ν) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat
      (fun k => integral_nonneg fun x => expWeight_nonneg _ _ _) (fun k => ?_)
    refine (hwlt (s k)).le.trans ?_
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right (hs.id_le k) 1
  have hle := integral_expWeight_le_of_tendsto omega θ hν hlam (fun k => hw (s k)) hv
    (fun k => hw0 (s k)) hv0 hlim hI
  have hpos : 0 < ∫ x, expWeight lam v x ∂ν := by
    rw [integral_pos_iff_support_of_nonneg (fun x => expWeight_nonneg _ _ _)
      (integrable_expWeight hlam.le hv hv0)]
    have hsupp : Function.support (expWeight lam v) = univ := by
      ext x
      simp only [Function.mem_support, mem_univ, iff_true]
      exact (Real.exp_pos _).ne'
    rw [hsupp]
    exact hν0
  linarith

/-- **Existence of a maximizer** of `G(v) = E(v) - κ ∫ e^{λ v} dν` on `E¹(X, θ; φ)`. -/
theorem exists_expFunctional_max (omega : KahlerBackground n M) {ν : Measure M}
    [IsFiniteMeasure ν] (hν : DoesNotChargeManifoldPluripolar (n := n) ν) (hν0 : 0 < ν univ)
    {lam κ : ℝ} (hlam : 0 < lam) (hκ : 0 < κ) :
    ∃ u : M → EReal, RelativeFiniteEnergyPreceq θ φ u hφ ∧
      ∀ a : M → EReal, RelativeFiniteEnergyPreceq θ φ a hφ →
        expFunctional θ φ hφ ν lam κ a ≤ expFunctional θ φ hφ ν lam κ u := by
  set G := expFunctional θ φ hφ ν lam κ with hG
  set m := modelVolume θ φ hφ with hmdef
  have hm : 0 < m := modelVolume_pos omega
  obtain ⟨a₀, ha₀, ha₀le⟩ := exists_pos_le_integral_expWeight (θ := θ) omega hν hν0 hlam
  set β : ℝ := κ * a₀ * lam ^ 2 / 2 with hβ
  have hβpos : 0 < β := by positivity
  -- the basic upper bound
  have hupper : ∀ v, RelativeFiniteEnergyPreceq θ φ v hφ →
      ∃ (w : M → EReal) (c : ℝ), RelativeFiniteEnergyPreceq θ φ w hφ ∧ (⨆ x, w x) = 0 ∧
        (∀ x, w x ≤ φ x) ∧ v = (fun x => w x + (c : EReal)) ∧
        G v = (energy θ φ hφ w).toReal + c * m - κ * Real.exp (lam * c) * ∫ x, expWeight lam w x ∂ν ∧
        G v ≤ c * m ∧ (0 ≤ c → G v ≤ c * m - β * c ^ 2) := by
    intro v hv
    obtain ⟨w, c, hwF, hw0, hwφ, hvw, hGv⟩ := exists_expFunctional_decomposition omega hν lam κ hv
    rw [← hG, ← hmdef] at hGv
    have hE := toReal_energy_nonpos_of_le (hφ := hφ) omega hwφ
    have hIw := ha₀le w hwF.1.plurisubharmonic hw0
    have hexp := Real.exp_pos (lam * c)
    refine ⟨w, c, hwF, hw0, hwφ, hvw, hGv, ?_, ?_⟩
    · rw [hGv]
      have : 0 ≤ κ * Real.exp (lam * c) * ∫ x, expWeight lam w x ∂ν :=
        mul_nonneg (mul_nonneg hκ.le hexp.le) (integral_nonneg fun x => expWeight_nonneg _ _ _)
      linarith
    · intro hc
      have hq := Real.quadratic_le_exp_of_nonneg (mul_nonneg hlam.le hc)
      rw [hGv]
      have h1 : κ * a₀ * Real.exp (lam * c) ≤ κ * Real.exp (lam * c) * ∫ x, expWeight lam w x ∂ν := by
        have := mul_le_mul_of_nonneg_left hIw (mul_nonneg hκ.le hexp.le)
        linarith
      have h2 : κ * a₀ * ((lam * c) ^ 2 / 2) ≤ κ * a₀ * Real.exp (lam * c) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [sq_nonneg (lam * c)]
      have h3 : β * c ^ 2 = κ * a₀ * ((lam * c) ^ 2 / 2) := by rw [hβ]; ring
      linarith
  -- `G` is bounded above
  set Cmax : ℝ := m ^ 2 / (4 * β) with hCmax
  have hGbound : ∀ v, RelativeFiniteEnergyPreceq θ φ v hφ → G v ≤ Cmax := by
    intro v hv
    obtain ⟨w, c, -, -, -, -, -, h1, h2⟩ := hupper v hv
    rcases le_or_gt 0 c with hc | hc
    · have h := h2 hc
      have hsq : 0 ≤ (2 * β * c - m) ^ 2 := sq_nonneg _
      have : c * m - β * c ^ 2 ≤ m ^ 2 / (4 * β) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      linarith
    · have : c * m < 0 := mul_neg_of_neg_of_pos hc hm
      have : 0 ≤ Cmax := by positivity
      linarith
  set T : Set ℝ := {y | ∃ a, RelativeFiniteEnergyPreceq θ φ a hφ ∧ y = G a} with hT
  have hTne : T.Nonempty := ⟨G φ, φ, relativeFiniteEnergyPreceq_model omega, rfl⟩
  have hTbdd : BddAbove T := ⟨Cmax, by rintro _ ⟨a, ha, rfl⟩; exact hGbound a ha⟩
  set S := sSup T with hS
  have hGS : ∀ a, RelativeFiniteEnergyPreceq θ φ a hφ → G a ≤ S := fun a ha =>
    le_csSup hTbdd ⟨a, ha, rfl⟩
  -- a maximizing sequence
  have hseq : ∀ j : ℕ, ∃ v, RelativeFiniteEnergyPreceq θ φ v hφ ∧ S - 1 / ((j : ℝ) + 1) < G v := by
    intro j
    obtain ⟨_, ⟨v, hv, rfl⟩, hlt⟩ :=
      exists_lt_of_lt_csSup hTne (show S - 1 / ((j : ℝ) + 1) < S by
        have : 0 < 1 / ((j : ℝ) + 1) := by positivity
        linarith)
    exact ⟨v, hv, hlt⟩
  choose v hv hvS using hseq
  choose w c hwF hw0 hwφ hvw hGv hGc hGq using fun j => hupper (v j) (hv j)
  set g₀ := S - 1 with hg₀
  have hvg : ∀ j, g₀ ≤ G (v j) := fun j => by
    have h1 := hvS j
    have : 1 / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    linarith
  -- bounds on the constants and the energies
  set C₁ : ℝ := 1 + (m + |g₀|) / β with hC₁
  have hclow : ∀ j, g₀ / m ≤ c j := fun j => by
    rw [div_le_iff₀ hm]; linarith [hvg j, hGc j]
  have hcup : ∀ j, c j ≤ C₁ := by
    intro j
    by_contra hcon
    push Not at hcon
    have hc1 : 1 < c j := by
      have : 0 ≤ (m + |g₀|) / β := by positivity
      linarith
    have h := (hvg j).trans (hGq j (by linarith))
    have hdiv : (m + |g₀|) / β * β = m + |g₀| := div_mul_cancel₀ _ hβpos.ne'
    have hab := le_abs_self g₀
    have hneg := neg_abs_le g₀
    have : β * c j > m + |g₀| := by
      have : β * c j > β * C₁ := mul_lt_mul_of_pos_left hcon hβpos
      have : β * C₁ = β + (m + |g₀|) := by rw [hC₁, mul_add, mul_one, mul_comm, hdiv]
      linarith
    nlinarith
  set L₀ : ℝ := g₀ - C₁ * m with hL₀
  have hElow : ∀ j, L₀ ≤ (energy θ φ hφ (w j)).toReal := by
    intro j
    have h := hGv j
    have hpos : 0 ≤ κ * Real.exp (lam * c j) * ∫ x, expWeight lam (w j) x ∂ν :=
      mul_nonneg (mul_nonneg hκ.le (Real.exp_pos _).le)
        (integral_nonneg fun x => expWeight_nonneg _ _ _)
    have := hvg j
    have := mul_le_mul_of_nonneg_right (hcup j) hm.le
    linarith
  have hw0' : ∀ j x, w j x ≤ 0 := fun j x => hw0 j ▸ le_iSup (w j) x
  set I : ℕ → ℝ := fun j => ∫ x, expWeight lam (w j) x ∂ν with hI
  have hImem : ∀ j, I j ∈ Icc (0 : ℝ) (ν.real univ) := by
    intro j
    refine ⟨integral_nonneg fun x => expWeight_nonneg _ _ _, ?_⟩
    calc I j ≤ ∫ _x, (1 : ℝ) ∂ν :=
          integral_mono (integrable_expWeight hlam.le (hwF j).1.plurisubharmonic (hw0' j))
            (integrable_const _) (fun x => expWeight_le_one hlam.le (hw0' j) x)
      _ = ν.real univ := by simp
  -- compactness and convergent subsequences
  obtain ⟨z, s₁, hz, hzs, hs₁, hlim₁, -⟩ :=
    NaturalNormalizedThetaPshCompactness.exists_strictMono_subseq_of_sup_eq_zero
      (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega) w
      (fun j => (hwF j).1.plurisubharmonic) hw0
  obtain ⟨cL, -, s₂, hs₂, hc₂⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc (g₀ / m) C₁)
    (x := fun k => c (s₁ k)) (fun k => ⟨hclow _, hcup _⟩)
  obtain ⟨IL, -, s₃, hs₃, hI₃⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc 0 (ν.real univ))
    (x := fun k => I (s₁ (s₂ k))) (fun k => hImem _)
  set σ : ℕ → ℕ := fun k => s₁ (s₂ (s₃ k)) with hσ
  have hσmono : StrictMono σ := hs₁.comp (hs₂.comp hs₃)
  have hlim : ManifoldL1LocallyTendsto (n := n) (fun k => w (σ k)) atTop z := fun e K hK hKe =>
    (hlim₁ e K hK hKe).comp ((hs₂.comp hs₃).tendsto_atTop)
  have hcσ : Tendsto (fun k => c (σ k)) atTop (𝓝 cL) := hc₂.comp hs₃.tendsto_atTop
  have hIσ : Tendsto (fun k => I (σ k)) atTop (𝓝 IL) := hI₃
  have hGσ : Tendsto (fun k => G (v (σ k))) atTop (𝓝 S) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds
      (fun k => (hvS (σ k)).le) (fun k => hGS _ (hv (σ k)))
    have h0 : Tendsto (fun k : ℕ => 1 / ((σ k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hσmono.tendsto_atTop
    simpa only [sub_zero] using (tendsto_const_nhds (x := S)).sub h0
  set EL : ℝ := S - cL * m + κ * Real.exp (lam * cL) * IL with hEL
  have hEσ : Tendsto (fun k => (energy θ φ hφ (w (σ k))).toReal) atTop (𝓝 EL) := by
    have hexp : Tendsto (fun k => Real.exp (lam * c (σ k))) atTop (𝓝 (Real.exp (lam * cL))) :=
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).tendsto cL).comp hcσ
    have h := (hGσ.sub (hcσ.mul_const m)).add ((hexp.const_mul κ).mul hIσ)
    refine h.congr fun k => ?_
    have := hGv (σ k)
    simp only [I] at this ⊢
    linarith
  -- the limit lies in E¹ and maximizes
  have hEext : ∀ k, ((L₀ : ℝ) : EReal) ≤ energy θ φ hφ (w (σ k)) := fun k => by
    rw [← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega (hwF (σ k))]
    exact EReal.coe_le_coe_iff.mpr (hElow (σ k))
  obtain ⟨hzφ, -, hzF⟩ :=
    ActualSingularEnergyCanonicalL1Usc.relativeFiniteEnergy_of_manifoldL1LocallyTendsto_of_uniform_energy_lower
      omega (fun k => (hwF (σ k)).1.relativePSHPreceq) hz hlim (fun k => hw0' (σ k)) hEext
  have hzPre : RelativeFiniteEnergyPreceq θ φ z hφ := preceq_of_relativeFiniteEnergy hzF
  have hUSC := ActualSingularEnergyCanonicalL1Usc.limsup_energy_le_of_manifoldL1LocallyTendsto
    (hφ := hφ) omega (fun k => (hwF (σ k)).1.relativePSHPreceq) hz hlim (C := 0)
    (by simpa only [EReal.coe_zero] using fun k => hw0' (σ k))
  have hEext' : Tendsto (fun k => energy θ φ hφ (w (σ k))) atTop (𝓝 (EL : EReal)) := by
    have h := EReal.tendsto_coe.mpr hEσ
    refine h.congr fun k => ?_
    exact SingularModelFiniteEnergyPreceq.coe_toReal_energy omega (hwF (σ k))
  rw [hEext'.limsup_eq, ← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega hzPre] at hUSC
  have hEz : EL ≤ (energy θ φ hφ z).toReal := EReal.coe_le_coe_iff.mp hUSC
  have hz0 : ∀ x, z x ≤ 0 := fun x => hzs ▸ le_iSup z x
  have hIz : ∫ x, expWeight lam z x ∂ν ≤ IL :=
    integral_expWeight_le_of_tendsto omega θ hν hlam (fun k => (hwF (σ k)).1.plurisubharmonic)
      hz (fun k => hw0' (σ k)) hz0 hlim hIσ
  refine ⟨fun x => z x + (cL : EReal), RelativeFiniteEnergyPreceq.add_const omega hzPre cL, ?_⟩
  intro a ha
  refine (hGS a ha).trans ?_
  have hGu : G (fun x => z x + (cL : EReal)) =
      (energy θ φ hφ z).toReal + cL * m - κ * Real.exp (lam * cL) * ∫ x, expWeight lam z x ∂ν := by
    rw [hG]
    unfold expFunctional
    rw [toReal_energy_add_const omega hzPre cL,
      integral_expWeight_add_const hν hzPre.1.plurisubharmonic cL]
    ring
  rw [hGu]
  have := mul_le_mul_of_nonneg_left hIz (mul_nonneg hκ.le (Real.exp_pos (lam * cL)).le)
  linarith

end SGPT.Envelopes.RelativeMA
