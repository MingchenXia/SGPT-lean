import SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyDiagonalGap

set_option autoImplicit false

/-!
# Actual ordered finite-energy endpoint comparison over singular models

The ordered diagonal endpoint case of Xia SGPT PDF0124--0126 weighted
truncation convergence, and Proposition 3.1.19 (3.44), is proved using actual
max locality, actual equal full masses, and vanishing integrable self-gap
tails. No moving integral convergence or endpoint inequality is assumed.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyOrderedComparison

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses RelativeEnergyIntegrability DiagonalMass
  MongeAmpereEnergyDecreasing FiniteEnergyCharacterization
  SingularModelEnergyTruncation SingularModelEnergyTruncationGap
  SingularModelFiniteEnergyDiagonalGap

noncomputable section

private theorem canonicalDiff_nonneg {a b : EReal} (hat : a ≠ ⊤) (hbt : b ≠ ⊤)
    (hba : b ≤ a) : 0 ≤ canonicalERealDiffToReal a b := by
  by_cases hab : a = ⊥
  · have hbb : b = ⊥ := bot_unique (hab ▸ hba)
    simp [hab, hbb]
  by_cases hbb : b = ⊥
  · simp [hbb, canonicalERealDiffToReal, hab]
  have hpole : a = ⊥ ↔ b = ⊥ := ⟨fun h => (hab h).elim, fun h => (hbb h).elim⟩
  rw [canonicalDiff_eq_sub_toReal hat hbt hpole]
  exact sub_nonneg.mpr (EReal.toReal_le_toReal hba hbb hat)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

variable {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal} {hφ : IsModelPotential θ φ}

private theorem integrable_referenceGap (omega : KahlerBackground n M)
    (hv : RelativeFiniteEnergy θ φ v hφ) :
    Integrable (fun x => canonicalERealDiffToReal (φ x) (v x))
      (diagonalPotentialMeasure θ v hv.1.plurisubharmonic) := by
  have hp : RelativeFiniteEnergy θ φ φ hφ := by
    refine ⟨⟨hφ.plurisubharmonic, le_rfl, rfl⟩, hφ.plurisubharmonic, ?_⟩
    have hz (x : M) : canonicalERealAbsDiff (φ x) (φ x) = 0 :=
      canonicalERealAbsDiff_self_of_ne_top (hφ.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x)
    simp only [relativeFiniteEnergyIntegral, hz, lintegral_zero]
    exact bot_lt_top
  exact (integrable_canonicalDiff_diagonal_add omega
    (preceq_of_relativeFiniteEnergy hp) (preceq_of_relativeFiniteEnergy hv)
    hv.1.le_reference).right_of_add_measure

/-- Actual weighted moving-diagonal convergence is produced by genuine max
locality, equal actual full masses, and an integrable self-gap tail. -/
theorem tendsto_integral_truncations_smaller_diagonal (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergy θ φ u hφ) (hv : RelativeFiniteEnergy θ φ v hφ)
    (hvu : v ≤ u) :
    Tendsto (fun j => ∫ x, canonicalERealDiffToReal (truncation φ u j x)
      (truncation φ v j x) ∂diagonalPotentialMeasure θ (truncation φ v j)
        (relativeEInfinity_truncation hφ.plurisubharmonic hv.1.plurisubharmonic
          (preceq_of_relativePSH hv.1.relativePSH).2 j).1)
      atTop (𝓝 (∫ x, canonicalERealDiffToReal (u x) (v x)
        ∂diagonalPotentialMeasure θ v hv.1.plurisubharmonic)) := by
  classical
  let hp := hφ.plurisubharmonic
  let hup := hu.1.plurisubharmonic
  let hvp := hv.1.plurisubharmonic
  let htu := fun j => relativeEInfinity_truncation hp hup
    (preceq_of_relativePSH hu.1.relativePSH).2 j
  let htv := fun j => relativeEInfinity_truncation hp hvp
    (preceq_of_relativePSH hv.1.relativePSH).2 j
  let μ := diagonalPotentialMeasure θ v hvp
  let ν := fun j => diagonalPotentialMeasure θ (truncation φ v j) (htv j).1
  let g := fun x => canonicalERealDiffToReal (u x) (v x)
  let f := fun x => canonicalERealDiffToReal (φ x) (v x)
  let gj := fun j x => canonicalERealDiffToReal (truncation φ u j x) (truncation φ v j x)
  let A := fun j : ℕ => {x | φ x - ((j : ℝ) : EReal) < v x}
  have : IsFiniteMeasure μ := GlobalNonPluripolar.globalMixedMeasure_isFiniteMeasure omega _
  have hνfin (j : ℕ) : IsFiniteMeasure (ν j) :=
    GlobalNonPluripolar.globalMixedMeasure_isFiniteMeasure omega _
  have hAm (j : ℕ) : MeasurableSet (A j) := measurableSet_lt_truncation hp.1 hvp.1 j
  have hAmn : Monotone A := fun i j hij x hx => lt_of_le_of_lt (EReal.sub_le_sub le_rfl
    (EReal.coe_le_coe_iff.mpr (Nat.cast_le.mpr hij))) hx
  have hAE : ∀ᵐ x ∂μ, v x ≠ ⊥ := ae_iff.mpr (by
    simpa only [not_not] using diagonalPotentialMeasure_pole_null θ hvp)
  have hAevent (x : M) (hvb : v x ≠ ⊥) : ∀ᶠ j in atTop, x ∈ A j := by
    have hpb : φ x ≠ ⊥ := ne_bot_of_le_ne_bot hvb (hv.1.le_reference x)
    obtain ⟨k, hk⟩ := exists_nat_gt ((φ x).toReal - (v x).toReal)
    have hxk : x ∈ A k := by
      change φ x - ((k : ℝ) : EReal) < v x
      rw [← EReal.coe_toReal (hp.1.quasiPlurisubharmonic.ne_top x) hpb,
        ← EReal.coe_sub, ← EReal.coe_toReal (hvp.1.quasiPlurisubharmonic.ne_top x) hvb]
      exact EReal.coe_lt_coe_iff.mpr (by linarith)
    exact (eventually_ge_atTop k).mono fun j hj => hAmn hj hxk
  have hg : Integrable g μ := (integrable_canonicalDiff_diagonal_add omega
    (preceq_of_relativeFiniteEnergy hu) (preceq_of_relativeFiniteEnergy hv) hvu).right_of_add_measure
  have hf : Integrable f μ := integrable_referenceGap omega hv
  have hgj (j : ℕ) : Integrable (gj j) (ν j) :=
    integrable_canonicalDiff_globalMixedMeasure omega (htu j).1.1 (htv j).1.1
      ((htu j).2.trans (htv j).2.symm) (fun _ : Fin n => (htv j).1.1)
  have hgnn (j : ℕ) (x : M) : 0 ≤ gj j x := canonicalDiff_nonneg
    ((htu j).1.1.quasiPlurisubharmonic.ne_top x) ((htv j).1.1.quasiPlurisubharmonic.ne_top x)
    (max_le_max (hvu x) le_rfl)
  have hgb (j : ℕ) (x : M) : gj j x ≤ (j : ℝ) := by
    by_cases hpb : φ x = ⊥
    · have hub : truncation φ u j x = ⊥ :=
        (sameSingularityTypeOn_eq_bot_iff (htu j).2 (mem_univ x)).mpr hpb
      have hvb : truncation φ v j x = ⊥ :=
        (sameSingularityTypeOn_eq_bot_iff (htv j).2 (mem_univ x)).mpr hpb
      simp only [gj, hub, hvb, canonicalERealDiffToReal_bot_bot]
      positivity
    · have hub : truncation φ u j x ≠ ⊥ := fun h => hpb
        ((sameSingularityTypeOn_eq_bot_iff (htu j).2 (mem_univ x)).mp h)
      have hvb : truncation φ v j x ≠ ⊥ := fun h => hpb
        ((sameSingularityTypeOn_eq_bot_iff (htv j).2 (mem_univ x)).mp h)
      have h1 := EReal.toReal_le_toReal (truncation_le hu.1.le_reference j x) hub
        (hp.1.quasiPlurisubharmonic.ne_top x)
      have h2 : (φ x).toReal - (j : ℝ) ≤ (truncation φ v j x).toReal := by
        have hl : φ x - ((j : ℝ) : EReal) ≤ truncation φ v j x := le_max_right _ _
        rw [← EReal.coe_toReal (hp.1.quasiPlurisubharmonic.ne_top x) hpb,
          ← EReal.coe_sub, ← EReal.coe_toReal ((htv j).1.1.quasiPlurisubharmonic.ne_top x) hvb] at hl
        exact EReal.coe_le_coe_iff.mp hl
      dsimp only [gj]
      rw [canonicalDiff_eq_sub_toReal ((htu j).1.1.quasiPlurisubharmonic.ne_top x)
        ((htv j).1.1.quasiPlurisubharmonic.ne_top x)
        (sameSingularityTypeOn_eq_bot_iff ((htu j).2.trans (htv j).2.symm) (mem_univ x))]
      linarith
  have hgood : Tendsto (fun j => ∫ x in A j, g x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
    simp_rw [← integral_indicator (hAm _)]
    refine tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
      (fun j => (hg.indicator (hAm j)).aestronglyMeasurable) hg.norm
      (fun j => Eventually.of_forall fun x => norm_indicator_le_norm_self _ _) ?_
    filter_upwards [hAE] with x hvb
    apply tendsto_const_nhds.congr'
    exact (hAevent x hvb).mono fun j hx => (indicator_of_mem hx g).symm
  have htail : Tendsto (fun j => ∫ x in (A j)ᶜ, f x ∂μ) atTop (𝓝 (0 : ℝ)) := by
    have ht : Tendsto (fun j => ∫ x, (A j)ᶜ.indicator f x ∂μ)
        atTop (𝓝 (∫ _x : M, (0 : ℝ) ∂μ)) := by
      refine tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
        (fun j => (hf.indicator (hAm j).compl).aestronglyMeasurable) hf.norm
        (fun j => Eventually.of_forall fun x => norm_indicator_le_norm_self _ _) ?_
      filter_upwards [hAE] with x hvb
      apply tendsto_const_nhds.congr'
      exact (hAevent x hvb).mono fun j hx => (indicator_of_notMem (notMem_compl_iff.mpr hx) f).symm
    simpa only [integral_indicator (hAm _).compl, integral_zero] using ht
  have hloc (j : ℕ) : (ν j).restrict (A j) = μ.restrict (A j) :=
    diagonalPotentialMeasure_truncation_restrict θ hp hvp j (htv j).1
  have hcompl (j : ℕ) : (ν j).real (A j)ᶜ = μ.real (A j)ᶜ := by
    let : IsFiniteMeasure (ν j) := hνfin j
    have htotal : ν j univ = μ univ := (diagonalPotentialMeasure_truncation_univ
      omega θ hp hvp (preceq_of_relativePSH hv.1.relativePSH).2 j).trans
        ((relativeFullMass_iff θ φ v hφ hvp).mp hv.1).2.symm
    have ha : ν j (A j) = μ (A j) := by
      rw [← Measure.restrict_apply_self, hloc, Measure.restrict_apply_self]
    have ht : (ν j).real univ = μ.real univ := congrArg ENNReal.toReal htotal
    have hAr : (ν j).real (A j) = μ.real (A j) := congrArg ENNReal.toReal ha
    linarith [measureReal_add_measureReal_compl (μ := ν j) (hAm j),
      measureReal_add_measureReal_compl (μ := μ) (hAm j)]
  have hbad (j : ℕ) : (∫ x in (A j)ᶜ, gj j x ∂ν j) ≤ ∫ x in (A j)ᶜ, f x ∂μ := by
    let : IsFiniteMeasure (ν j) := hνfin j
    calc (∫ x in (A j)ᶜ, gj j x ∂ν j) ≤ ∫ _x in (A j)ᶜ, (j : ℝ) ∂ν j :=
        integral_mono_ae (hgj j).restrict (integrable_const _)
          (Eventually.of_forall fun x => hgb j x)
      _ = ∫ _x in (A j)ᶜ, (j : ℝ) ∂μ := by
        simp only [setIntegral_const, smul_eq_mul, hcompl]
      _ ≤ ∫ x in (A j)ᶜ, f x ∂μ := by
        refine integral_mono_ae (integrable_const _) hf.restrict ?_
        filter_upwards [ae_restrict_of_ae hAE, ae_restrict_mem (hAm j).compl] with x hvb hx
        have hpb : φ x ≠ ⊥ := ne_bot_of_le_ne_bot hvb (hv.1.le_reference x)
        have hl : v x ≤ φ x - ((j : ℝ) : EReal) := not_lt.mp hx
        rw [← EReal.coe_toReal (hp.1.quasiPlurisubharmonic.ne_top x) hpb,
          ← EReal.coe_sub, ← EReal.coe_toReal (hvp.1.quasiPlurisubharmonic.ne_top x) hvb] at hl
        have hpole : φ x = ⊥ ↔ v x = ⊥ := ⟨fun h => (hpb h).elim, fun h => (hvb h).elim⟩
        dsimp only [f]
        rw [canonicalDiff_eq_sub_toReal (hp.1.quasiPlurisubharmonic.ne_top x)
          (hvp.1.quasiPlurisubharmonic.ne_top x) hpole]
        have hr := EReal.coe_le_coe_iff.mp hl
        linarith
  have hbad0 : Tendsto (fun j => ∫ x in (A j)ᶜ, gj j x ∂ν j) atTop (𝓝 (0 : ℝ)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
      (fun j => integral_nonneg fun x => hgnn j x) hbad
  have heq (j : ℕ) : (∫ x, gj j x ∂ν j) =
      (∫ x in A j, g x ∂μ) + ∫ x in (A j)ᶜ, gj j x ∂ν j := by
    rw [← integral_add_compl (hAm j) (hgj j), hloc]
    congr 1
    apply setIntegral_congr_fun (hAm j)
    intro x hx
    change canonicalERealDiffToReal (truncation φ u j x) (truncation φ v j x) = _
    rw [truncation_eq_of_lt (hx.trans_le (hvu x)), truncation_eq_of_lt hx]
  change Tendsto (fun j => ∫ x, gj j x ∂ν j) atTop (𝓝 (∫ x, g x ∂μ))
  simpa only [← heq, add_zero] using hgood.add hbad0

/-- Actual finite-type endpoint comparison passes through the produced
weighted moving integral convergence to normalized E1 energies. -/
theorem energy_sub_le_integral_smaller_diagonal (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergy θ φ u hφ) (hv : RelativeFiniteEnergy θ φ v hφ)
    (hvu : v ≤ u) :
    (energy θ φ hφ u).toReal - (energy θ φ hφ v).toReal ≤
      ∫ x, canonicalERealDiffToReal (u x) (v x)
        ∂diagonalPotentialMeasure θ v hv.1.plurisubharmonic := by
  let htu := fun j => relativeEInfinity_truncation hφ.plurisubharmonic hu.1.plurisubharmonic
    (preceq_of_relativePSH hu.1.relativePSH).2 j
  let htv := fun j => relativeEInfinity_truncation hφ.plurisubharmonic hv.1.plurisubharmonic
    (preceq_of_relativePSH hv.1.relativePSH).2 j
  have hTu := energy_tendsto_truncation omega θ hφ hu.1.plurisubharmonic
    (preceq_of_relativePSH hu.1.relativePSH).2
  have hTv := energy_tendsto_truncation omega θ hφ hv.1.plurisubharmonic
    (preceq_of_relativePSH hv.1.relativePSH).2
  rw [← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega
    (preceq_of_relativeFiniteEnergy hu)] at hTu
  rw [← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega
    (preceq_of_relativeFiniteEnergy hv)] at hTv
  exact le_of_tendsto_of_tendsto
    ((EReal.tendsto_coe.mp hTu).sub (EReal.tendsto_coe.mp hTv))
    (tendsto_integral_truncations_smaller_diagonal omega hu hv hvu)
    (Eventually.of_forall fun j =>
      (SingularModelEnergyCocycle.integral_le_relativeEnergyOfMinimalType_sub_le
        omega θ hφ.plurisubharmonic (htu j).1 (htv j).1 (htu j).2 (htv j).2).2)

private theorem canonicalDiff_add_coe (a b : EReal) (c : ℝ) :
    canonicalERealDiffToReal (a + (c : EReal)) (b + (c : EReal)) =
      canonicalERealDiffToReal a b := by
  cases a <;> cases b <;>
    simp [canonicalERealDiffToReal, poleModifiedERealDiffToReal,
      ← EReal.coe_add, ← EReal.coe_sub]

/-- Common finite translation transfers the actual ordered middle energy
inequality to the full singularity-order E1 class. -/
theorem energy_sub_le_integral_smaller_diagonal_of_preceq (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (hvu : v ≤ u) :
    (energy θ φ hφ u).toReal - (energy θ φ hφ v).toReal ≤
      ∫ x, canonicalERealDiffToReal (u x) (v x)
        ∂diagonalPotentialMeasure θ v hv.1.plurisubharmonic := by
  obtain ⟨c, hc₀, hc₁⟩ := exists_common_add_le hu.1.relativePSHPreceq hv.1.relativePSHPreceq
  have hb := energy_sub_le_integral_smaller_diagonal omega
    (hu.relativeFiniteEnergy_add omega hc₀) (hv.relativeFiniteEnergy_add omega hc₁)
    (fun x => add_le_add (hvu x) le_rfl)
  rw [DiagonalMeasureRegularity.diagonalPotentialMeasure_add_const θ hv.1.plurisubharmonic c] at hb
  simp only [canonicalDiff_add_coe] at hb
  rw [SingularModelFiniteRealEnergy.toReal_energy_add_const omega hu c,
    SingularModelFiniteRealEnergy.toReal_energy_add_const omega hv c] at hb
  have e : ((energy θ φ hφ u).toReal + c * modelVolume θ φ hφ) -
      ((energy θ φ hφ v).toReal + c * modelVolume θ φ hφ) =
      (energy θ φ hφ u).toReal - (energy θ φ hφ v).toReal := by ring
  rwa [e] at hb

/-- The three actual ordered endpoint energy inequalities hold for all
singularity-order E1 endpoints over any singular model, with constants 1
and n+1 and internally produced actual cross-measure integrability. -/
theorem integral_le_energy_sub_le_integral_le_mul (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (hvu : v ≤ u) :
    (∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂diagonalPotentialMeasure θ u hu.1.plurisubharmonic) ≤
        (energy θ φ hφ u).toReal - (energy θ φ hφ v).toReal ∧
    (energy θ φ hφ u).toReal - (energy θ φ hφ v).toReal ≤
      (∫ x, canonicalERealDiffToReal (u x) (v x)
        ∂diagonalPotentialMeasure θ v hv.1.plurisubharmonic) ∧
    (∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂diagonalPotentialMeasure θ v hv.1.plurisubharmonic) ≤
        ((n : ℝ) + 1) * ((energy θ φ hφ u).toReal - (energy θ φ hφ v).toReal) := by
  let μu := diagonalPotentialMeasure θ u hu.1.plurisubharmonic
  let μv := diagonalPotentialMeasure θ v hv.1.plurisubharmonic
  let g := fun x => canonicalERealDiffToReal (u x) (v x)
  have hg : Integrable g (μu + μv) := integrable_canonicalDiff_diagonal_add omega hu hv hvu
  have hgnn (x : M) : 0 ≤ g x := canonicalDiff_nonneg
    (hu.1.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x)
    (hv.1.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x) (hvu x)
  have hcanon (μ : Measure M) (hnull : μ {x | v x = ⊥} = 0) (hi : Integrable g μ) :
      ENNReal.ofReal (∫ x, g x ∂μ) = ∫⁻ x, canonicalERealAbsDiff (u x) (v x) ∂μ := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hgnn)]
    have hAE : ∀ᵐ x ∂μ, v x ≠ ⊥ := ae_iff.mpr (by simpa only [not_not] using hnull)
    apply lintegral_congr_ae
    filter_upwards [hAE] with x hvbot
    have hubot : u x ≠ ⊥ := ne_bot_of_le_ne_bot hvbot (hvu x)
    have hpole : u x = ⊥ ↔ v x = ⊥ := ⟨fun h => (hubot h).elim, fun h => (hvbot h).elim⟩
    rw [canonicalERealAbsDiff_eq_ofReal_abs_diff
      (hu.1.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x)
      (hv.1.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x) hpole,
      abs_of_nonneg (hgnn x)]
  have hcu := hcanon μu
    (GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate
      (fun _ : Fin n => hu.1.plurisubharmonic.1) hv.1.plurisubharmonic) hg.left_of_add_measure
  have hcv := hcanon μv (diagonalPotentialMeasure_pole_null θ hv.1.plurisubharmonic)
    hg.right_of_add_measure
  obtain ⟨ha, hb⟩ := diagonalGap_endpoint_bounds_of_preceq omega hu hv hvu
  rw [← hcu] at ha
  rw [← hcv] at hb
  have hd : 0 ≤ (energy θ φ hφ u).toReal - (energy θ φ hφ v).toReal :=
    sub_nonneg.mpr (SingularModelFiniteRealEnergy.toReal_energy_mono omega hv hu hvu)
  exact ⟨(ENNReal.ofReal_le_ofReal_iff hd).mp ha,
    energy_sub_le_integral_smaller_diagonal_of_preceq omega hu hv hvu,
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity) hd)).mp hb⟩

end

end SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyOrderedComparison
