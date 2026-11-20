import SGPT.Envelopes.RelativeCYLowerBound
import SGPT.Envelopes.RelativeMAExistence

/-!
# Existence for the relative Calabi–Yau equation `θ_u^n = ν`

Source `thm:Yau_rel` (`author/chapter_envelopes.tex`, lines 1021–1027), existence part. The
book refers to Darvas–Di Nezza–Lu; we follow Xia, *Foundations of pluripotential theory*,
`thm:nonpluripolar-relative-prescribed-measure-existence`: let `λ_j = 1/(j+1) → 0` and let
`u_j ∈ E¹(X, θ; φ)` solve `θ_{u_j}^n = e^{λ_j u_j} ν` (relative Aubin–Yau theorem,
`thm:AY_rel`, `SGPT.Envelopes.RelativeMA.exists_relativeFiniteEnergy_exp_solution`). Write
`u_j = w_j + c_j` with `sup_X w_j = 0`.

* (Dini) `H_j(w) = ∫ e^{λ_j w} dν` increases to `ν(X)` uniformly on normalized potentials:
  otherwise compactness of normalized potentials and lower semicontinuity of `H_J` produce a
  normalized limit `z` with `H_J(z) ≤ a < ν(X)` for all `J`, while `H_J(z) → ν(X)`
  (`tendsto_integral_expWeight_normalized`).
* Comparing masses, `e^{λ_j c_j} H_j(w_j) = ν(X)`, so `e^{λ_j c_j} → 1`, and
  `∫ |1 - e^{λ_j w_j}| dν = ν(X) - H_j(w_j) → 0`; along a subsequence the densities
  `e^{λ_j u_j}` tend to `1` `ν`-almost everywhere.
* The tail limit `A` of the subsequence satisfies `θ_A^n ≥ ν` (`RelativeCYLowerBound`), `A ≤ φ`
  and `sup_X A = 0`; mass monotonicity gives `θ_A^n(X) ≤ ν(X)`, hence `θ_A^n = ν` and
  `A ∈ E(X, θ; φ)`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Envelopes.RelativeCY

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass SGPT.Foundations.Analysis.Pending.RelativePreceqClasses
open SGPT.Envelopes.RelativeMA

theorem expWeight_le_of_le {X : Type*} {lam lam' : ℝ} (h : lam' ≤ lam) {w : X → EReal}
    (hw : ∀ x, w x ≤ 0) (x : X) : expWeight lam w x ≤ expWeight lam' w x := by
  unfold expWeight
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_right h (EReal.toReal_nonpos (hw x))

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal}

omit [CompactSpace M] in
/-- `∫ e^{λ_j z} dν → ν(X)` as `λ_j → 0`, for a nonpositive `θ`-psh `z`. -/
theorem tendsto_integral_expWeight_of_tendsto_zero {ν : Measure M} [IsFiniteMeasure ν]
    {lam : ℕ → ℝ} (hlam : Tendsto lam atTop (𝓝 0)) (hlam0 : ∀ j, 0 ≤ lam j) {z : M → EReal}
    (hz : IsThetaPshPotential θ.val z) (hz0 : ∀ x, z x ≤ 0) :
    Tendsto (fun j => ∫ x, expWeight (lam j) z x ∂ν) atTop (𝓝 (ν.real univ)) := by
  have h := tendsto_integral_of_dominated_convergence (μ := ν) (fun _ => (1 : ℝ))
    (F := fun j x => expWeight (lam j) z x) (f := fun _ => (1 : ℝ))
    (fun j => (integrable_expWeight (hlam0 j) hz hz0).aestronglyMeasurable) (integrable_const 1)
    (fun j => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (expWeight_nonneg _ _ _)]
      exact expWeight_le_one (hlam0 j) hz0 x)
    (Eventually.of_forall fun x => by
      have : Tendsto (fun j => Real.exp (lam j * (z x).toReal)) atTop
          (𝓝 (Real.exp (0 * (z x).toReal))) :=
        (Real.continuous_exp.tendsto _).comp (hlam.mul_const _)
      simpa only [expWeight, zero_mul, Real.exp_zero] using this)
  simpa only [integral_const, smul_eq_mul, mul_one] using h

variable [ConnectedSpace M]

/-- **Dini step.** For normalized `θ`-psh `w_j` (`sup_X w_j = 0`) and `λ_j = 1/(j+1)`,
`∫ e^{λ_j w_j} dν → ν(X)`. -/
theorem tendsto_integral_expWeight_normalized (omega : KahlerBackground n M)
    {ν : Measure M} [IsFiniteMeasure ν] (hν : DoesNotChargeManifoldPluripolar (n := n) ν)
    {w : ℕ → M → EReal} (hw : ∀ j, IsThetaPshPotential θ.val (w j)) (hws : ∀ j, (⨆ x, w j x) = 0) :
    Tendsto (fun j : ℕ => ∫ x, expWeight (1 / ((j : ℝ) + 1)) (w j) x ∂ν) atTop (𝓝 (ν.real univ)) := by
  set lam : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) with hlamdef
  have hlam : ∀ j, 0 < lam j := fun j => by positivity
  have hlam0 : Tendsto lam atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlamanti : Antitone lam := fun i j hij => by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hij 1
  have hw0 : ∀ j x, w j x ≤ 0 := fun j x => hws j ▸ le_iSup (w j) x
  set m : ℝ := ν.real univ with hm
  set H : ℕ → ℝ := fun j => ∫ x, expWeight (lam j) (w j) x ∂ν with hH
  have hint : ∀ (l : ℝ) (v : M → EReal), 0 ≤ l → IsThetaPshPotential θ.val v → (∀ x, v x ≤ 0) →
      ∫ x, expWeight l v x ∂ν ≤ m := fun l v hl hv hv0 => by
    calc ∫ x, expWeight l v x ∂ν ≤ ∫ _x, (1 : ℝ) ∂ν :=
          integral_mono (integrable_expWeight hl hv hv0) (integrable_const _)
            (fun x => expWeight_le_one hl hv0 x)
      _ = m := by simp [hm]
  have hHle : ∀ j, H j ≤ m := fun j => hint _ _ (hlam j).le (hw j) (hw0 j)
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => Eventually.of_forall fun j => (hHle j).trans_lt ha⟩
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨s, hs, hsa⟩ := extraction_of_frequently_atTop (P := fun j => H j ≤ a) (hcon.mono fun j hj => not_lt.mp hj)
  obtain ⟨z, s', hz, hzs, hs', hlim, -⟩ :=
    NaturalNormalizedThetaPshCompactness.exists_strictMono_subseq_of_sup_eq_zero
      (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega) (fun i => w (s i))
      (fun i => hw (s i)) (fun i => hws (s i))
  have hz0 : ∀ x, z x ≤ 0 := fun x => hzs ▸ le_iSup z x
  have hJ : ∀ J, ∫ x, expWeight (lam J) z x ∂ν ≤ a := by
    intro J
    set v : ℕ → M → EReal := fun k => w (s (s' k)) with hv
    set I : ℕ → ℝ := fun k => ∫ x, expWeight (lam J) (v k) x ∂ν with hI
    have hIa : ∀ k, J ≤ k → I k ≤ a := by
      intro k hk
      have hJk : J ≤ s (s' k) := hk.trans ((hs'.id_le k).trans (hs.id_le (s' k)))
      calc I k ≤ H (s (s' k)) :=
            integral_mono (integrable_expWeight (hlam J).le (hw _) (hw0 _))
              (integrable_expWeight (hlam _).le (hw _) (hw0 _))
              (fun x => expWeight_le_of_le (hlamanti hJk) (hw0 _) x)
        _ ≤ a := hsa (s' k)
    have hImem : ∀ k, I k ∈ Icc (0 : ℝ) m := fun k =>
      ⟨integral_nonneg fun x => expWeight_nonneg _ _ _, hint _ _ (hlam J).le (hw _) (hw0 _)⟩
    obtain ⟨L, -, s'', hs'', hL⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc 0 m) hImem
    have hLa : L ≤ a := by
      refine le_of_tendsto hL ?_
      filter_upwards [eventually_ge_atTop J] with k hk
      exact hIa (s'' k) (hk.trans (hs''.id_le k))
    have hlim' : ManifoldL1LocallyTendsto (n := n) (fun k => v (s'' k)) atTop z :=
      fun e K hK hKe => (hlim e K hK hKe).comp hs''.tendsto_atTop
    exact (integral_expWeight_le_of_tendsto omega θ hν (hlam J) (fun k => hw _) hz
      (fun k => hw0 _) hz0 hlim' hL).trans hLa
  have hlimz := tendsto_integral_expWeight_of_tendsto_zero (ν := ν) hlam0 (fun j => (hlam j).le)
    hz hz0
  exact absurd (le_of_tendsto' hlimz hJ) (not_le.mpr ha)

/-- **Native existence for the relative Calabi–Yau equation.** Let `φ` be a model potential
with positive mass in a big class (`dim X > 0`) and `ν` a finite measure charging no
pluripolar set with `ν(X) = ∫ θ_φ^n`. Then there is `u ∈ E(X, θ; φ)` with `θ_u^n = ν`,
`sup_X u = 0` and `u ≤ φ`. -/
theorem exists_relativeFullMass_measure_solution (omega : KahlerBackground n M) (hn : 0 < n)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) (hφ : IsModelPotential θ φ)
    {ν : Measure M} [IsFiniteMeasure ν] (hν : DoesNotChargeManifoldPluripolar (n := n) ν)
    (hνm : ν univ = diagonalPotentialMass θ φ hφ.plurisubharmonic) :
    ∃ u : M → EReal, ∃ hu : RelativeFullMassPreceq θ φ u hφ,
      diagonalPotentialMeasure θ u hu.1 = ν ∧ (⨆ x, u x) = 0 ∧ u ≤ φ := by
  have hν0 : 0 < ν univ := hνm ▸ hφ.positive_mass
  have hφP := hφ.plurisubharmonic
  set lam : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) with hlamdef
  have hlam : ∀ j, 0 < lam j := fun j => by positivity
  choose u hu hsol using fun j => exists_relativeFiniteEnergy_exp_solution (hφ := hφ) omega hn
    hbig hν hν0 (hlam j)
  choose a haF has haφ _hsv hax using fun j =>
    ActualSmoothVolumeVariationalFoundation.exists_normalized_translate omega (hu j)
  set w : ℕ → M → EReal := fun j x => u j x + (a j : EReal) with hwdef
  have hwP : ∀ j, IsThetaPshPotential θ.val (w j) := fun j => (haF j).1.plurisubharmonic
  have hw0 : ∀ j x, w j x ≤ 0 := fun j x => has j ▸ le_iSup (w j) x
  have huP : ∀ j, IsThetaPshPotential θ.val (u j) := fun j => (hu j).1.plurisubharmonic
  have hub : ∀ j, u j = fun x => w j x + ((-a j : ℝ) : EReal) := fun j =>
    (translate_translate_neg (u j) (a j)).symm
  have hμw : ∀ j, diagonalPotentialMeasure θ (w j) (hwP j) =
      diagonalPotentialMeasure θ (u j) (huP j) := by
    intro j
    rw [diagonalPotentialMeasure_congr_fun (hub j) (huP j) ((hwP j).add_const _)]
    exact (DiagonalMeasureRegularity.diagonalPotentialMeasure_add_const θ (hwP j) _ _).symm
  -- the densities `e^{λ_j u_j}`
  set r : ℕ → M → ℝ≥0∞ := fun j x => EReal.exp ((lam j : EReal) * u j x) with hrdef
  have hrm : ∀ j, Measurable (r j) := fun j =>
    measurable_ereal_exp_mul (lam j) (measurable_of_isThetaPshPotential (huP j))
  set K : ℕ → ℝ := fun j => Real.exp (lam j * (-a j)) with hKdef
  set E : ℕ → M → ℝ := fun j x => expWeight (lam j) (w j) x with hEdef
  set m : ℝ := ν.real univ with hmdef
  set H : ℕ → ℝ := fun j => ∫ x, E j x ∂ν with hHdef
  have hr_ae : ∀ j, ∀ᵐ x ∂ν, r j x = ENNReal.ofReal (K j * E j x) := by
    intro j
    filter_upwards [ae_ne_bot_of_doesNotCharge hν (hwP j)] with x hx
    have hux : u j x ≠ ⊥ := by
      rw [hub j]
      intro h
      rcases EReal.add_eq_bot_iff.mp h with h | h
      · exact hx h
      · exact EReal.coe_ne_bot _ h
    have hut : u j x ≠ ⊤ := (huP j).1.quasiPlurisubharmonic.ne_top x
    rw [hrdef]
    simp only
    rw [ereal_exp_mul_eq_expWeight (lam j) hux hut]
    congr 1
    have h := expWeight_add_const (lam := lam j) (hwP j).1.quasiPlurisubharmonic.ne_top (-a j) hx
    rw [← hub j] at h
    exact h
  have hEint : ∀ j, Integrable (E j) ν := fun j => integrable_expWeight (hlam j).le (hwP j) (hw0 j)
  have hE1 : ∀ j x, E j x ≤ 1 := fun j x => expWeight_le_one (hlam j).le (hw0 j) x
  have hE0 : ∀ j x, 0 ≤ E j x := fun j x => expWeight_nonneg _ _ _
  -- the mass identity `e^{λ_j c_j} H_j = ν(X)`
  have hνreal : ENNReal.ofReal m = ν univ := ENNReal.ofReal_toReal (measure_ne_top ν univ)
  have hmassEq : ∀ j, K j * H j = m := by
    intro j
    have h1 : ν.withDensity (r j) univ = ν univ := by
      rw [← hsol j]
      exact ((hu j).1.mass_eq (huP j)).trans hνm.symm
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_congr_ae (hr_ae j), ← ofReal_integral_eq_lintegral_ofReal
        ((hEint j).const_mul (K j)) (Eventually.of_forall fun x => mul_nonneg (Real.exp_pos _).le
          (hE0 j x)), ← hνreal, integral_const_mul] at h1
    exact (ENNReal.ofReal_eq_ofReal_iff (mul_nonneg (Real.exp_pos _).le
      (integral_nonneg (hE0 j))) measureReal_nonneg).mp h1
  have hm0 : 0 < m := by
    rw [hmdef, measureReal_def]
    exact ENNReal.toReal_pos hν0.ne' (measure_ne_top ν univ)
  -- the Dini step and its consequences
  have hHlim : Tendsto H atTop (𝓝 m) :=
    tendsto_integral_expWeight_normalized omega hν hwP has
  have hKlim : Tendsto K atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := m)).div hHlim hm0.ne'
    rw [div_self hm0.ne'] at h
    refine h.congr' ?_
    filter_upwards [hHlim.eventually (lt_mem_nhds (half_lt_self hm0))] with j hj
    have hHj : H j ≠ 0 := (lt_trans (half_pos hm0) hj).ne'
    show m / H j = K j
    rw [← hmassEq j, mul_div_cancel_right₀ _ hHj]
  -- `e^{λ_j w_j} → 1` in `L¹(ν)`, hence almost everywhere along a subsequence
  have hL1 : Tendsto (fun j => eLpNorm (E j - fun _ => (1 : ℝ)) 1 ν) atTop (𝓝 0) := by
    have heq : ∀ j, eLpNorm (E j - fun _ => (1 : ℝ)) 1 ν = ENNReal.ofReal (m - H j) := by
      intro j
      rw [eLpNorm_one_eq_lintegral_enorm]
      have hpt : ∀ x, ‖E j x - 1‖ₑ = ENNReal.ofReal (1 - E j x) := fun x => by
        rw [Real.enorm_eq_ofReal_abs, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hE1 j x))]
      simp only [Pi.sub_apply]
      simp_rw [hpt]
      rw [← ofReal_integral_eq_lintegral_ofReal (f := fun x => 1 - E j x)
        ((integrable_const 1).sub (hEint j))
        (Eventually.of_forall fun x => sub_nonneg.mpr (hE1 j x)), integral_sub (integrable_const 1)
        (hEint j)]
      simp [hmdef, hHdef]
    simp_rw [heq]
    have h := ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := m)).sub hHlim)
    rwa [sub_self, ENNReal.ofReal_zero] at h
  have hmeas : TendstoInMeasure ν E atTop (fun _ => (1 : ℝ)) :=
    tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero (fun j => (hEint j).aestronglyMeasurable)
      aestronglyMeasurable_const hL1
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  have hrlim : ∀ᵐ x ∂ν, liminf (fun i => r (ns i) x) atTop = 1 := by
    filter_upwards [hae, ae_all_iff.mpr fun i => hr_ae (ns i)] with x hx hrx
    have h1 : Tendsto (fun i => K (ns i) * E (ns i) x) atTop (𝓝 (1 * 1)) :=
      (hKlim.comp hns.tendsto_atTop).mul hx
    rw [mul_one] at h1
    have h2 := ENNReal.tendsto_ofReal h1
    rw [ENNReal.ofReal_one] at h2
    exact (h2.congr fun i => (hrx i).symm).liminf_eq
  -- the tail limit of the subsequence
  set w' : ℕ → M → EReal := fun i => w (ns i) with hw'def
  have hw'P : ∀ i, IsThetaPshPotential θ.val (w' i) := fun i => hwP (ns i)
  have hw'0 : ∀ i x, w' i x ≤ ((0 : ℝ) : EReal) := fun i x => by
    rw [EReal.coe_zero]; exact hw0 (ns i) x
  have haP := isThetaPshPotential_tailEnv hw'P hw'0
  set F : ℕ → Set M := fun j => tailEnv w' j ⁻¹' Ici 0 with hFdef
  have hFclosed : ∀ j, IsClosed (F j) := fun j =>
    upperSemicontinuous_iff_isClosed_preimage.mp (haP j).1.quasiPlurisubharmonic.upperSemicontinuous 0
  have hFmono : ∀ j, F (j + 1) ⊆ F j := fun j x hx =>
    le_trans (show (0 : EReal) ≤ tailEnv w' (j + 1) x from hx) (tailEnv_antitone w' x (Nat.le_succ j))
  have hFne : ∀ j, (F j).Nonempty := by
    intro j
    obtain ⟨x, hx⟩ := hax (ns j)
    exact ⟨x, show (0 : EReal) ≤ tailEnv w' j x from hx.symm.le.trans (le_tailEnv w' le_rfl x)⟩
  obtain ⟨x₀, hx₀⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed F hFmono
    hFne (hFclosed 0).isCompact hFclosed
  have hAx₀ : (0 : EReal) ≤ tailLimit w' x₀ := le_iInf fun j => mem_iInter.mp hx₀ j
  have hA : IsThetaPshPotential θ.val (tailLimit w') :=
    isThetaPshPotential_tailLimit hw'P hw'0 ⟨x₀, ne_bot_of_le_ne_bot EReal.zero_ne_bot hAx₀⟩
  have hA0 : ∀ x, tailLimit w' x ≤ 0 := fun x =>
    (tailLimit_le_tailEnv w' 0 x).trans
      (tailEnv_le (ψ := fun _ => (0 : EReal)) upperSemicontinuous_const (fun i x => hw0 (ns i) x) 0 x)
  have hAφ : tailLimit w' ≤ φ := (tailLimit_le_tailEnv w' 0).trans
    (tailEnv_le hφP.1.quasiPlurisubharmonic.upperSemicontinuous (fun i => haφ (ns i)) 0)
  -- the lower bound `θ_A^n ≥ ν`
  have hwf : ∀ i, ν.withDensity (r (ns i)) ≤ diagonalPotentialMeasure θ (w' i) (hw'P i) := fun i =>
    ((hsol (ns i)).symm.trans (hμw (ns i)).symm).le
  have hle := withDensity_liminf_le_tailLimit omega hφ hν hw'P (fun i => haφ (ns i))
    (fun i => hrm (ns i)) hwf hA
  have hνle : ν ≤ diagonalPotentialMeasure θ (tailLimit w') hA := by
    have h1 : ν.withDensity (fun x => liminf (fun i => r (ns i) x) atTop) = ν := by
      rw [withDensity_congr_ae hrlim]
      exact withDensity_one
    rwa [h1] at hle
  -- mass comparison
  have hmassA : diagonalPotentialMass θ (tailLimit w') hA ≤
      diagonalPotentialMass θ φ hφP :=
    diagonalPotentialMass_mono_of_kahler omega hA hφP (MoreSingularOn.of_le fun x _ => hAφ x)
  have huniv : ν univ = diagonalPotentialMeasure θ (tailLimit w') hA univ :=
    le_antisymm (hνle univ) (hmassA.trans hνm.symm.le)
  refine ⟨tailLimit w', ⟨hA, MoreSingularOn.of_le fun x _ => hAφ x, huniv.symm.trans hνm⟩,
    (Measure.eq_of_le_of_measure_univ_eq hνle huniv).symm,
    le_antisymm (iSup_le hA0) (le_iSup_of_le x₀ hAx₀), hAφ⟩

end SGPT.Envelopes.RelativeCY
