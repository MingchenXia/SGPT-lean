import SGPT.Foundations.Analysis.Pending.SingularModelDarvasSeparation
import SGPT.Foundations.Analysis.Pending.DiagonalMeasureRegularity

set_option autoImplicit false

/-!
# Actual ordered diagonal gap bounds for singular-model finite energies

Xia SGPT PDF0119 (3.33) and PDF0161 Definition 4.3.2; an independently
proved ordered quantitative consequence via actual truncation. Genuine finite-type bounds, actual max locality on
fixed truncation levels, and monotone convergence produce cross-measure
gap integrability; there is no boundedness or assumed integral bound.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyDiagonalGap

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses RelativeEnergyIntegrability DiagonalMass
  MongeAmpereEnergyDecreasing FiniteEnergyCharacterization

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The actual canonical absolute gap against the sum of the two actual
non-pluripolar diagonal measures, as a nonnegative extended integral. -/
def diagonalGapIntegral (θ : ClosedRealOneOneForm n M) (u v : M → EReal)
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v) : ℝ≥0∞ :=
  ∫⁻ x, canonicalERealAbsDiff (u x) (v x)
    ∂(diagonalPotentialMeasure θ u hu + diagonalPotentialMeasure θ v hv)

variable {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal} {hφ : IsModelPotential θ φ}

/-- Actual ordered same-type bounds pass through fixed-level locality and
monotone convergence to the actual absolute gap of normalized E1 endpoints. -/
private theorem endpoint_gap_le (smaller : Bool) (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergy θ φ u hφ) (hv : RelativeFiniteEnergy θ φ v hφ)
    (hvu : v ≤ u) :
    (∫⁻ x, canonicalERealAbsDiff (u x) (v x)
      ∂(if smaller then diagonalPotentialMeasure θ v hv.1.plurisubharmonic
        else diagonalPotentialMeasure θ u hu.1.plurisubharmonic)) ≤
      ENNReal.ofReal ((if smaller then (n : ℝ) + 1 else 1) *
        ((energy θ φ hφ u).toReal - (energy θ φ hφ v).toReal)) := by
  classical
  have hφp := hφ.plurisubharmonic
  have hru := hu.1.relativePSH
  have hrv := hv.1.relativePSH
  let μu := diagonalPotentialMeasure θ u hu.1.plurisubharmonic
  let μv := diagonalPotentialMeasure θ v hv.1.plurisubharmonic
  let μ := if smaller then μv else μu
  have : IsFiniteMeasure μu := GlobalNonPluripolar.globalMixedMeasure_isFiniteMeasure omega _
  have : IsFiniteMeasure μv := GlobalNonPluripolar.globalMixedMeasure_isFiniteMeasure omega _
  have : IsFiniteMeasure μ := by
    dsimp only [μ]
    split <;> infer_instance
  let uk : ℕ → M → EReal := truncation φ u
  let vk : ℕ → M → EReal := truncation φ v
  have huk (k : ℕ) : RelativeEInfinity θ φ (uk k) :=
    SingularModelEnergyTruncation.relativeEInfinity_truncation hφp hru.1
      (preceq_of_relativePSH hru).2 k
  have hvk (k : ℕ) : RelativeEInfinity θ φ (vk k) :=
    SingularModelEnergyTruncation.relativeEInfinity_truncation hφp hrv.1
      (preceq_of_relativePSH hrv).2 k
  let νu := fun k => diagonalPotentialMeasure θ (uk k) (huk k).1
  let νv := fun k => diagonalPotentialMeasure θ (vk k) (hvk k).1
  let ν := fun k => if smaller then νv k else νu k
  have horder (k : ℕ) : vk k ≤ uk k := fun x => max_le_max (hvu x) le_rfl
  have htype (k : ℕ) : SameSingularityTypeOn (uk k) (vk k) univ :=
    (huk k).2.trans (hvk k).2.symm
  have heq (k : ℕ) : (fun x => canonicalERealDiffToReal (uk k x) (vk k x)) =
      fun x => (uk k x).toReal - (vk k x).toReal := funext fun x =>
    canonicalDiff_eq_sub_toReal ((huk k).1.1.quasiPlurisubharmonic.ne_top x)
      ((hvk k).1.1.quasiPlurisubharmonic.ne_top x)
      (sameSingularityTypeOn_eq_bot_iff (htype k) (mem_univ x))
  have hgiu (k : ℕ) : Integrable (fun x => (uk k x).toReal - (vk k x).toReal) (νu k) := by
    have h := integrable_canonicalDiff_globalMixedMeasure omega (huk k).1.1 (hvk k).1.1
      (htype k) (fun _ : Fin n => (huk k).1.1)
    rwa [heq k] at h
  have hgiv (k : ℕ) : Integrable (fun x => (uk k x).toReal - (vk k x).toReal) (νv k) := by
    have h := integrable_canonicalDiff_globalMixedMeasure omega (huk k).1.1 (hvk k).1.1
      (htype k) (fun _ : Fin n => (hvk k).1.1)
    rwa [heq k] at h
  have hgi (k : ℕ) : Integrable (fun x => (uk k x).toReal - (vk k x).toReal) (ν k) :=
    by
      cases smaller
      · exact hgiu k
      · exact hgiv k
  have hg0 (k : ℕ) (x : M) : 0 ≤ (uk k x).toReal - (vk k x).toReal := by
    have h := SingularModelEnergyEndpointBounds.canonicalDiff_nonpos_of_le_of_sameType
      (hvk k).1.1.quasiPlurisubharmonic.ne_top (huk k).1.1.quasiPlurisubharmonic.ne_top
      (htype k).symm (horder k) x
    rw [canonicalDiff_eq_sub_toReal ((hvk k).1.1.quasiPlurisubharmonic.ne_top x)
      ((huk k).1.1.quasiPlurisubharmonic.ne_top x)
      (sameSingularityTypeOn_eq_bot_iff (htype k).symm (mem_univ x))] at h
    linarith
  have hk (k : ℕ) : (∫ x, ((uk k x).toReal - (vk k x).toReal) ∂ν k) ≤
      (if smaller then (n : ℝ) + 1 else 1) *
        (relativeEnergyOfMinimalType θ φ (uk k) hφp (huk k).1 -
          relativeEnergyOfMinimalType θ φ (vk k) hφp (hvk k).1) := by
    cases smaller
    · have ha := (SingularModelEnergyCocycle.integral_le_relativeEnergyOfMinimalType_sub_le
        omega θ hφp (huk k).1 (hvk k).1 (huk k).2 (hvk k).2).1
      rw [heq k] at ha
      simpa only [ν, νu, diagonalPotentialMeasure, Bool.false_eq_true, if_false, one_mul] using ha
    · exact SingularModelDarvasSeparation.integral_le_mul_relativeEnergyOfMinimalType_sub
        omega θ hφp (huk k) (hvk k) (horder k)
  have hTu := SingularModelEnergyTruncation.energy_tendsto_truncation
    omega θ hφ hru.1 (preceq_of_relativePSH hru).2
  have hTv := SingularModelEnergyTruncation.energy_tendsto_truncation
    omega θ hφ hrv.1 (preceq_of_relativePSH hrv).2
  rw [← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega
    (preceq_of_relativeFiniteEnergy hu)] at hTu
  rw [← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega
    (preceq_of_relativeFiniteEnergy hv)] at hTv
  let D := (if smaller then (n : ℝ) + 1 else 1) * ((energy θ φ hφ u).toReal - (energy θ φ hφ v).toReal)
  have hD : Tendsto (fun k => (if smaller then (n : ℝ) + 1 else 1) *
      (relativeEnergyOfMinimalType θ φ (uk k) hφp (huk k).1 -
        relativeEnergyOfMinimalType θ φ (vk k) hφp (hvk k).1)) atTop (𝓝 D) :=
    ((EReal.tendsto_coe.mp hTu).sub (EReal.tendsto_coe.mp hTv)).const_mul (if smaller then (n : ℝ) + 1 else 1)
  let A := fun k : ℕ => {x | φ x - ((k : ℝ) : EReal) < v x}
  let f := fun k : ℕ => (A k).indicator fun x => (u x).toReal - (v x).toReal
  have hAm (k : ℕ) : MeasurableSet (A k) := measurableSet_lt_truncation hφp.1 hrv.1.1 k
  have hAmono : Monotone A := fun i j hij x hx => lt_of_le_of_lt (EReal.sub_le_sub le_rfl
    (EReal.coe_le_coe_iff.mpr (Nat.cast_le.mpr hij))) hx
  have hvfin : ∀ k x, x ∈ A k → v x ≠ ⊥ := fun _ _ hx => ne_bot_of_gt hx
  have hufin : ∀ k x, x ∈ A k → u x ≠ ⊥ := fun k x hx =>
    ne_bot_of_le_ne_bot (hvfin k x hx) (hvu x)
  have hφfin : ∀ k x, x ∈ A k → φ x ≠ ⊥ := fun k x hx =>
    ne_bot_of_le_ne_bot (hvfin k x hx) (hrv.2 x)
  have hutop := hru.1.1.quasiPlurisubharmonic.ne_top
  have hvtop := hrv.1.1.quasiPlurisubharmonic.ne_top
  have hφtop := hφp.1.quasiPlurisubharmonic.ne_top
  have hfnn (k : ℕ) (x : M) : 0 ≤ f k x := by
    by_cases hx : x ∈ A k
    · rw [show f k x = (u x).toReal - (v x).toReal from indicator_of_mem hx _]
      exact sub_nonneg.mpr (EReal.toReal_le_toReal (hvu x) (hvfin k x hx) (hutop x))
    · exact le_of_eq (indicator_of_notMem hx _).symm
  have hfb (k : ℕ) (x : M) : |f k x| ≤ (k : ℝ) := by
    rw [abs_of_nonneg (hfnn k x)]
    by_cases hx : x ∈ A k
    · rw [show f k x = (u x).toReal - (v x).toReal from indicator_of_mem hx _]
      have h1 := EReal.toReal_le_toReal (hru.2 x) (hufin k x hx) (hφtop x)
      have h2 : (φ x).toReal - (k : ℝ) < (v x).toReal := by
        have h := hx
        change φ x - ((k : ℝ) : EReal) < v x at h
        rw [← EReal.coe_toReal (hφtop x) (hφfin k x hx), ← EReal.coe_sub,
          ← EReal.coe_toReal (hvtop x) (hvfin k x hx)] at h
        exact EReal.coe_lt_coe_iff.mp h
      linarith
    · rw [show f k x = 0 from indicator_of_notMem hx _]
      positivity
  have hfm (k : ℕ) : Measurable (f k) :=
    (((GlobalSlotComparison.ThetaPlurisubharmonic.measurable hru.1.1).ereal_toReal).sub
      ((GlobalSlotComparison.ThetaPlurisubharmonic.measurable hrv.1.1).ereal_toReal)).indicator (hAm k)
  have hfi (k : ℕ) : Integrable (f k) μ := RelativeEnergyDiamond.integrable_of_abs_le (hfm k) (hfb k)
  have hlevel (k₀ : ℕ) : (∫ x, f k₀ x ∂μ) ≤ D := by
    refine ge_of_tendsto hD (eventually_atTop.2 ⟨k₀, ?_⟩)
    intro k hkk
    refine le_trans ?_ (hk k)
    let Ak := {x | φ x - ((k : ℝ) : EReal) < v x}
    let Au := {x | φ x - ((k : ℝ) : EReal) < u x}
    have hAAv : A k₀ ⊆ Ak := hAmono hkk
    have hAAu : A k₀ ⊆ Au := fun x hx => (hAAv hx).trans_le (hvu x)
    have hresu : (νu k).restrict Au = μu.restrict Au :=
      diagonalPotentialMeasure_truncation_restrict θ hφp hru.1 k (huk k).1
    have hresv : (νv k).restrict Ak = μv.restrict Ak :=
      diagonalPotentialMeasure_truncation_restrict θ hφp hrv.1 k (hvk k).1
    have hresAu : (νu k).restrict (A k₀) = μu.restrict (A k₀) := by
      rw [← Measure.restrict_restrict_of_subset hAAu, hresu,
        Measure.restrict_restrict_of_subset hAAu]
    have hresAv : (νv k).restrict (A k₀) = μv.restrict (A k₀) := by
      rw [← Measure.restrict_restrict_of_subset hAAv, hresv,
        Measure.restrict_restrict_of_subset hAAv]
    have hresA : (ν k).restrict (A k₀) = μ.restrict (A k₀) := by
      cases smaller
      · exact hresAu
      · exact hresAv
    calc (∫ x, f k₀ x ∂μ) = ∫ x in A k₀, ((u x).toReal - (v x).toReal) ∂μ :=
          integral_indicator (hAm k₀)
      _ = ∫ x in A k₀, ((uk k x).toReal - (vk k x).toReal) ∂μ := by
        apply setIntegral_congr_fun (hAm k₀)
        intro x hx
        change (u x).toReal - (v x).toReal = (uk k x).toReal - (vk k x).toReal
        rw [show uk k x = u x from truncation_eq_of_lt (hAAu hx),
          show vk k x = v x from truncation_eq_of_lt (hAAv hx)]
      _ = ∫ x in A k₀, ((uk k x).toReal - (vk k x).toReal) ∂ν k := by rw [hresA]
      _ ≤ ∫ x, ((uk k x).toReal - (vk k x).toReal) ∂ν k :=
        setIntegral_le_integral (hgi k) (Eventually.of_forall (hg0 k))
  have hzero : μ {x | v x = ⊥} = 0 := by
    cases smaller
    · exact GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate
        (fun _ : Fin n => hru.1.1) hrv.1
    · exact FiniteEnergyCharacterization.diagonalPotentialMeasure_pole_null θ hrv.1
  have hAE : ∀ᵐ x ∂μ, v x ≠ ⊥ := ae_iff.mpr (by simpa only [not_not] using hzero)
  have hSup : ∀ᵐ x ∂μ, canonicalERealAbsDiff (u x) (v x) =
      ⨆ k : ℕ, ENNReal.ofReal (f k x) := by
    filter_upwards [hAE] with x hvbot
    have hubot : u x ≠ ⊥ := ne_bot_of_le_ne_bot hvbot (hvu x)
    have hφbot : φ x ≠ ⊥ := ne_bot_of_le_ne_bot hvbot (hrv.2 x)
    have hreal : 0 ≤ (u x).toReal - (v x).toReal :=
      sub_nonneg.mpr (EReal.toReal_le_toReal (hvu x) hvbot (hutop x))
    have egap : canonicalERealAbsDiff (u x) (v x) =
        ENNReal.ofReal ((u x).toReal - (v x).toReal) := by
      rw [← EReal.coe_toReal (hutop x) hubot, ← EReal.coe_toReal (hvtop x) hvbot,
        canonicalERealAbsDiff_coe_coe]
      simp only [EReal.toReal_coe, abs_of_nonneg hreal]
    rw [egap]
    obtain ⟨k, hk⟩ := exists_nat_gt ((φ x).toReal - (v x).toReal)
    have hxk : x ∈ A k := by
      change φ x - ((k : ℝ) : EReal) < v x
      rw [← EReal.coe_toReal (hφtop x) hφbot, ← EReal.coe_sub, ← EReal.coe_toReal (hvtop x) hvbot]
      exact EReal.coe_lt_coe_iff.mpr (by linarith)
    refine le_antisymm (le_iSup_of_le k ?_) (iSup_le fun j => ?_)
    · rw [show f k x = (u x).toReal - (v x).toReal from indicator_of_mem hxk _]
    · by_cases hxj : x ∈ A j
      · rw [show f j x = (u x).toReal - (v x).toReal from indicator_of_mem hxj _]
      · rw [show f j x = 0 from indicator_of_notMem hxj _, ENNReal.ofReal_zero]
        positivity
  have hmono : Monotone (fun k x => ENNReal.ofReal (f k x)) := by
    intro i j hij x
    change ENNReal.ofReal (f i x) ≤ ENNReal.ofReal (f j x)
    by_cases hxi : x ∈ A i
    · rw [show f i x = (u x).toReal - (v x).toReal from indicator_of_mem hxi _,
        show f j x = (u x).toReal - (v x).toReal from indicator_of_mem (hAmono hij hxi) _]
    · rw [show f i x = 0 from indicator_of_notMem hxi _, ENNReal.ofReal_zero]
      positivity
  change (∫⁻ x, canonicalERealAbsDiff (u x) (v x) ∂μ) ≤ ENNReal.ofReal D
  calc (∫⁻ x, canonicalERealAbsDiff (u x) (v x) ∂μ) =
        ∫⁻ x, ⨆ k : ℕ, ENNReal.ofReal (f k x) ∂μ := lintegral_congr_ae hSup
    _ = ⨆ k : ℕ, ∫⁻ x, ENNReal.ofReal (f k x) ∂μ :=
      lintegral_iSup (fun k => (hfm k).ennreal_ofReal) hmono
    _ ≤ ENNReal.ofReal D := by
      refine iSup_le fun k => ?_
      rw [← ofReal_integral_eq_lintegral_ofReal (hfi k) (Eventually.of_forall (hfnn k))]
      exact ENNReal.ofReal_le_ofReal (hlevel k)

/-- Actual ordered endpoint gap bounds, including cross-measure finiteness,
retain the source's separate constants one and n+1 for arbitrary singular models. -/
theorem diagonalGap_endpoint_bounds (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergy θ φ u hφ) (hv : RelativeFiniteEnergy θ φ v hφ)
    (hvu : v ≤ u) :
    (∫⁻ x, canonicalERealAbsDiff (u x) (v x) ∂diagonalPotentialMeasure θ u hu.1.plurisubharmonic) ≤
      ENNReal.ofReal ((energy θ φ hφ u).toReal - (energy θ φ hφ v).toReal) ∧
    (∫⁻ x, canonicalERealAbsDiff (u x) (v x) ∂diagonalPotentialMeasure θ v hv.1.plurisubharmonic) ≤
      ENNReal.ofReal (((n : ℝ) + 1) * ((energy θ φ hφ u).toReal - (energy θ φ hφ v).toReal)) := by
  constructor
  · simpa only [Bool.false_eq_true, if_false, one_mul] using endpoint_gap_le false omega hu hv hvu
  · exact endpoint_gap_le true omega hu hv hvu

/-- The actual absolute gap against both actual endpoint measures is bounded
by n+2 times the actual ordered energy difference for normalized E1 endpoints. -/
theorem diagonalGapIntegral_le_mul_energy_sub (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergy θ φ u hφ) (hv : RelativeFiniteEnergy θ φ v hφ)
    (hvu : v ≤ u) :
    diagonalGapIntegral θ u v hu.1.plurisubharmonic hv.1.plurisubharmonic ≤
      ENNReal.ofReal (((n : ℝ) + 2) * ((energy θ φ hφ u).toReal - (energy θ φ hφ v).toReal)) := by
  obtain ⟨ha, hb⟩ := diagonalGap_endpoint_bounds omega hu hv hvu
  have hd : 0 ≤ (energy θ φ hφ u).toReal - (energy θ φ hφ v).toReal :=
    sub_nonneg.mpr (SingularModelFiniteRealEnergy.toReal_energy_mono omega
      (preceq_of_relativeFiniteEnergy hv) (preceq_of_relativeFiniteEnergy hu) hvu)
  have h := add_le_add ha hb
  rw [← ENNReal.ofReal_add hd (mul_nonneg (by positivity) hd)] at h
  have e : ((energy θ φ hφ u).toReal - (energy θ φ hφ v).toReal) +
      ((n : ℝ) + 1) * ((energy θ φ hφ u).toReal - (energy θ φ hφ v).toReal) =
      ((n : ℝ) + 2) * ((energy θ φ hφ u).toReal - (energy θ φ hφ v).toReal) := by ring
  rw [e] at h
  simpa only [diagonalGapIntegral, lintegral_add_measure] using h

/-- Common actual finite translations preserve the separate ordered endpoint
bounds with constants one and n+1 throughout the singularity-order E1 class. -/
theorem diagonalGap_endpoint_bounds_of_preceq (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (hvu : v ≤ u) :
    (∫⁻ x, canonicalERealAbsDiff (u x) (v x) ∂diagonalPotentialMeasure θ u hu.1.plurisubharmonic) ≤
      ENNReal.ofReal ((energy θ φ hφ u).toReal - (energy θ φ hφ v).toReal) ∧
    (∫⁻ x, canonicalERealAbsDiff (u x) (v x) ∂diagonalPotentialMeasure θ v hv.1.plurisubharmonic) ≤
      ENNReal.ofReal (((n : ℝ) + 1) * ((energy θ φ hφ u).toReal - (energy θ φ hφ v).toReal)) := by
  obtain ⟨c, hc₀, hc₁⟩ := exists_common_add_le hu.1.relativePSHPreceq hv.1.relativePSHPreceq
  have hb := diagonalGap_endpoint_bounds omega
    (hu.relativeFiniteEnergy_add omega hc₀) (hv.relativeFiniteEnergy_add omega hc₁)
    (fun x => add_le_add (hvu x) le_rfl)
  rw [DiagonalMeasureRegularity.diagonalPotentialMeasure_add_const θ hu.1.plurisubharmonic c,
    DiagonalMeasureRegularity.diagonalPotentialMeasure_add_const θ hv.1.plurisubharmonic c] at hb
  simp only [canonicalERealAbsDiff_add_coe] at hb
  rw [SingularModelFiniteRealEnergy.toReal_energy_add_const omega hu c,
    SingularModelFiniteRealEnergy.toReal_energy_add_const omega hv c] at hb
  have e : ((energy θ φ hφ u).toReal + c * modelVolume θ φ hφ) -
      ((energy θ φ hφ v).toReal + c * modelVolume θ φ hφ) =
      (energy θ φ hφ u).toReal - (energy θ φ hφ v).toReal := by ring
  rw [e] at hb
  exact hb

/-- Actual common finite translations transfer the quantitative ordered gap
bound to the full singularity-order E1 class of every singular model. -/
theorem diagonalGapIntegral_le_mul_energy_sub_of_preceq (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (hvu : v ≤ u) :
    diagonalGapIntegral θ u v hu.1.plurisubharmonic hv.1.plurisubharmonic ≤
      ENNReal.ofReal (((n : ℝ) + 2) * ((energy θ φ hφ u).toReal - (energy θ φ hφ v).toReal)) := by
  obtain ⟨c, hc₀, hc₁⟩ := exists_common_add_le hu.1.relativePSHPreceq hv.1.relativePSHPreceq
  have hb := diagonalGapIntegral_le_mul_energy_sub omega
    (hu.relativeFiniteEnergy_add omega hc₀) (hv.relativeFiniteEnergy_add omega hc₁)
    (fun x => add_le_add (hvu x) le_rfl)
  dsimp only [diagonalGapIntegral] at hb
  rw [DiagonalMeasureRegularity.diagonalPotentialMeasure_add_const θ hu.1.plurisubharmonic c,
    DiagonalMeasureRegularity.diagonalPotentialMeasure_add_const θ hv.1.plurisubharmonic c] at hb
  simp only [canonicalERealAbsDiff_add_coe] at hb
  rw [SingularModelFiniteRealEnergy.toReal_energy_add_const omega hu c,
    SingularModelFiniteRealEnergy.toReal_energy_add_const omega hv c] at hb
  have e : ((energy θ φ hφ u).toReal + c * modelVolume θ φ hφ) -
      ((energy θ φ hφ v).toReal + c * modelVolume θ φ hφ) =
      (energy θ φ hφ u).toReal - (energy θ φ hφ v).toReal := by ring
  rw [e] at hb
  exact hb

/-- For ordered actual E1 endpoints the quantitative canonical gap is bounded
by the actual Darvas distance, with no boundedness or connectedness premise. -/
theorem diagonalGapIntegral_le_mul_relativeD1 (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (hvu : v ≤ u) :
    diagonalGapIntegral θ u v hu.1.plurisubharmonic hv.1.plurisubharmonic ≤
      ENNReal.ofReal (((n : ℝ) + 2) * relativeD1 θ φ hφ u v) := by
  rw [relativeD1_comm θ φ hφ u v, relativeD1_eq_sub_of_le hv.1.plurisubharmonic hvu]
  exact diagonalGapIntegral_le_mul_energy_sub_of_preceq omega hu hv hvu

/-- The actual quantitative nonnegative gap bound produces genuine signed
cross-measure integrability for every ordered E1 pair over a singular model. -/
theorem integrable_canonicalDiff_diagonal_add (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (hvu : v ≤ u) :
    Integrable (fun x => canonicalERealDiffToReal (u x) (v x))
      (diagonalPotentialMeasure θ u hu.1.plurisubharmonic +
        diagonalPotentialMeasure θ v hv.1.plurisubharmonic) := by
  let μu := diagonalPotentialMeasure θ u hu.1.plurisubharmonic
  let μv := diagonalPotentialMeasure θ v hv.1.plurisubharmonic
  let μ := μu + μv
  have hfin : (∫⁻ x, canonicalERealAbsDiff (u x) (v x) ∂μ) < ⊤ :=
    (diagonalGapIntegral_le_mul_energy_sub_of_preceq omega hu hv hvu).trans_lt
      ENNReal.ofReal_lt_top
  have hzero : μ {x | v x = ⊥} = 0 := by
    change (μu + μv) {x | v x = ⊥} = 0
    rw [Measure.add_apply]
    have hz1 : μu {x | v x = ⊥} = 0 :=
      GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate
        (fun _ : Fin n => hu.1.plurisubharmonic.1) hv.1.plurisubharmonic
    have hz2 : μv {x | v x = ⊥} = 0 :=
      FiniteEnergyCharacterization.diagonalPotentialMeasure_pole_null θ hv.1.plurisubharmonic
    rw [hz1, hz2, add_zero]
  have hAE : ∀ᵐ x ∂μ, v x ≠ ⊥ := ae_iff.mpr (by simpa only [not_not] using hzero)
  have heq : ∀ᵐ x ∂μ, ‖canonicalERealDiffToReal (u x) (v x)‖ₑ =
      canonicalERealAbsDiff (u x) (v x) := by
    filter_upwards [hAE] with x hvbot
    have hubot : u x ≠ ⊥ := ne_bot_of_le_ne_bot hvbot (hvu x)
    have hpole : u x = ⊥ ↔ v x = ⊥ := ⟨fun h => (hubot h).elim, fun h => (hvbot h).elim⟩
    rw [Real.enorm_eq_ofReal_abs, canonicalERealAbsDiff_eq_ofReal_abs_diff
      (hu.1.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x)
      (hv.1.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x) hpole]
  have hm : Measurable (fun x => canonicalERealDiffToReal (u x) (v x)) :=
    measurable_canonicalERealDiffToReal.comp
      ((GlobalSlotComparison.ThetaPlurisubharmonic.measurable hu.1.plurisubharmonic.1).prodMk
        (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hv.1.plurisubharmonic.1))
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  change (∫⁻ x, ‖canonicalERealDiffToReal (u x) (v x)‖ₑ ∂μ) < ⊤
  rw [lintegral_congr_ae heq]
  exact hfin

end

end SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyDiagonalGap
