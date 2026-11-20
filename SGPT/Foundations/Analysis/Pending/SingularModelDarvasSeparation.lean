import SGPT.Foundations.Analysis.Pending.SingularModelDarvasContraction
import SGPT.Foundations.Analysis.Pending.SingularModelEnergyEndpointBounds

set_option autoImplicit false

/-!
# Actual Darvas separation for arbitrarily singular model references

Xia SGPT PDF0160--0161, Lemma 4.3.1, Step 1. The actual ordered finite
energy bound and fixed truncation-level max locality produce a zero
strict-order measure. Actual relative full-mass domination then gives
separation, without boundedness or moving-measure integral assumptions.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelDarvasSeparation

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses RelativeEnergyIntegrability DiagonalMass
  MongeAmpereEnergyDecreasing FiniteEnergyCharacterization

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The actual smaller diagonal integral is bounded by the finite energy
difference for genuine ordered endpoints of one singularity type. -/
theorem integral_le_mul_relativeEnergyOfMinimalType_sub (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u v : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hu : RelativeEInfinity θ φ u)
    (hv : RelativeEInfinity θ φ v) (hvu : v ≤ u) :
    (∫ x, ((u x).toReal - (v x).toReal) ∂diagonalPotentialMeasure θ v hv.1) ≤
      ((n : ℝ) + 1) * (relativeEnergyOfMinimalType θ φ u hφ hu.1 -
        relativeEnergyOfMinimalType θ φ v hφ hv.1) := by
  have ht : SameSingularityTypeOn v u univ := hv.2.trans hu.2.symm
  have hb := SingularModelEnergyEndpointBounds.energy_mul_le_integral
    omega θ hu.1 hv.1 ht hvu
  rw [← SingularModelEnergyCocycle.relativeEnergyOfMinimalType_sub
    omega θ hφ hv.1 hu.1 hv.2 hu.2] at hb
  have ei : (∫ x, canonicalERealDiffToReal (v x) (u x)
      ∂diagonalPotentialMeasure θ v hv.1) =
      -(∫ x, ((u x).toReal - (v x).toReal) ∂diagonalPotentialMeasure θ v hv.1) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change canonicalERealDiffToReal (v x) (u x) = -((u x).toReal - (v x).toReal)
      rw [canonicalDiff_eq_sub_toReal (hv.1.1.quasiPlurisubharmonic.ne_top x)
        (hu.1.1.quasiPlurisubharmonic.ne_top x) (sameSingularityTypeOn_eq_bot_iff ht (mem_univ x))]
      ring
  rw [ei] at hb
  linarith

variable {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal} {hφ : IsModelPotential θ φ}

/-- Actual max locality on each fixed truncation level and convergence of
the actual finite energies force the smaller measure of the strict-order set
to vanish, for normalized ordered finite-energy endpoints of any model. -/
theorem measure_lt_eq_zero_of_energy_eq (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergy θ φ u hφ) (hv : RelativeFiniteEnergy θ φ v hφ)
    (hvu : v ≤ u) (he : (energy θ φ hφ u).toReal = (energy θ φ hφ v).toReal) :
    diagonalPotentialMeasure θ v hv.1.plurisubharmonic {x | v x < u x} = 0 := by
  classical
  have hφp := hφ.plurisubharmonic
  have hru := hu.1.relativePSH
  have hrv := hv.1.relativePSH
  let μ := diagonalPotentialMeasure θ v hv.1.plurisubharmonic
  have : IsFiniteMeasure μ := GlobalNonPluripolar.globalMixedMeasure_isFiniteMeasure omega _
  let uk : ℕ → M → EReal := truncation φ u
  let vk : ℕ → M → EReal := truncation φ v
  have huk (k : ℕ) : RelativeEInfinity θ φ (uk k) :=
    SingularModelEnergyTruncation.relativeEInfinity_truncation hφp hru.1
      (preceq_of_relativePSH hru).2 k
  have hvk (k : ℕ) : RelativeEInfinity θ φ (vk k) :=
    SingularModelEnergyTruncation.relativeEInfinity_truncation hφp hrv.1
      (preceq_of_relativePSH hrv).2 k
  have horder (k : ℕ) : vk k ≤ uk k := fun x => max_le_max (hvu x) le_rfl
  have hTu := SingularModelEnergyTruncation.energy_tendsto_truncation
    omega θ hφ hru.1 (preceq_of_relativePSH hru).2
  have hTv := SingularModelEnergyTruncation.energy_tendsto_truncation
    omega θ hφ hrv.1 (preceq_of_relativePSH hrv).2
  rw [← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega
    (preceq_of_relativeFiniteEnergy hu)] at hTu
  rw [← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega
    (preceq_of_relativeFiniteEnergy hv)] at hTv
  have hD : Tendsto (fun k => ((n : ℝ) + 1) *
      (relativeEnergyOfMinimalType θ φ (uk k) hφp (huk k).1 -
        relativeEnergyOfMinimalType θ φ (vk k) hφp (hvk k).1)) atTop (𝓝 0) := by
    have h := ((EReal.tendsto_coe.mp hTu).sub (EReal.tendsto_coe.mp hTv)).const_mul ((n : ℝ) + 1)
    simpa only [he, sub_self, mul_zero] using h
  have hk (k : ℕ) :
      (∫ x, ((uk k x).toReal - (vk k x).toReal) ∂diagonalPotentialMeasure θ (vk k) (hvk k).1) ≤
      ((n : ℝ) + 1) * (relativeEnergyOfMinimalType θ φ (uk k) hφp (huk k).1 -
        relativeEnergyOfMinimalType θ φ (vk k) hφp (hvk k).1) :=
    integral_le_mul_relativeEnergyOfMinimalType_sub omega θ hφp (huk k) (hvk k) (horder k)
  have hlevel : ∀ k₀ : ℕ,
      μ ({x | φ x - ((k₀ : ℝ) : EReal) < v x} ∩ {x | v x < u x}) = 0 := by
    intro k₀
    let A : Set M := {x | φ x - ((k₀ : ℝ) : EReal) < v x}
    have hAm : MeasurableSet A := measurableSet_lt_truncation hφp.1 hrv.1.1 k₀
    have hvfin : ∀ x ∈ A, v x ≠ ⊥ := fun x hx => ne_bot_of_gt hx
    have hufin : ∀ x ∈ A, u x ≠ ⊥ := fun x hx => ne_bot_of_le_ne_bot (hvfin x hx) (hvu x)
    have hφfin : ∀ x ∈ A, φ x ≠ ⊥ := fun x hx =>
      ne_bot_of_le_ne_bot (hvfin x hx) (hrv.2 x)
    have hutop : ∀ x, u x ≠ ⊤ := hru.1.1.quasiPlurisubharmonic.ne_top
    have hvtop : ∀ x, v x ≠ ⊤ := hrv.1.1.quasiPlurisubharmonic.ne_top
    have hφtop : ∀ x, φ x ≠ ⊤ := hφp.1.quasiPlurisubharmonic.ne_top
    let f : M → ℝ := A.indicator fun x => (u x).toReal - (v x).toReal
    have hf0 : ∀ x, 0 ≤ f x := by
      intro x
      by_cases hx : x ∈ A
      · rw [show f x = (u x).toReal - (v x).toReal from indicator_of_mem hx _]
        exact sub_nonneg.mpr (EReal.toReal_le_toReal (hvu x) (hvfin x hx) (hutop x))
      · exact le_of_eq (indicator_of_notMem hx _).symm
    have hfb : ∀ x, |f x| ≤ (k₀ : ℝ) := by
      intro x
      rw [abs_of_nonneg (hf0 x)]
      by_cases hx : x ∈ A
      · rw [show f x = (u x).toReal - (v x).toReal from indicator_of_mem hx _]
        have h1 : (u x).toReal ≤ (φ x).toReal :=
          EReal.toReal_le_toReal (hru.2 x) (hufin x hx) (hφtop x)
        have h2 : (φ x).toReal - (k₀ : ℝ) < (v x).toReal := by
          have h := hx
          change φ x - ((k₀ : ℝ) : EReal) < v x at h
          rw [← EReal.coe_toReal (hφtop x) (hφfin x hx), ← EReal.coe_sub,
            ← EReal.coe_toReal (hvtop x) (hvfin x hx)] at h
          exact EReal.coe_lt_coe_iff.mp h
        linarith
      · rw [show f x = 0 from indicator_of_notMem hx _]
        positivity
    have hfm : Measurable f :=
      (((GlobalSlotComparison.ThetaPlurisubharmonic.measurable hru.1.1).ereal_toReal).sub
        ((GlobalSlotComparison.ThetaPlurisubharmonic.measurable hrv.1.1).ereal_toReal)).indicator hAm
    have hfi : Integrable f μ := RelativeEnergyDiamond.integrable_of_abs_le hfm hfb
    have hle : ∀ k, k₀ ≤ k → (∫ x, f x ∂μ) ≤ ((n : ℝ) + 1) *
        (relativeEnergyOfMinimalType θ φ (uk k) hφp (huk k).1 -
          relativeEnergyOfMinimalType θ φ (vk k) hφp (hvk k).1) := by
      intro k hkk
      refine le_trans ?_ (hk k)
      let ν := diagonalPotentialMeasure θ (vk k) (hvk k).1
      have : IsFiniteMeasure ν := GlobalNonPluripolar.globalMixedMeasure_isFiniteMeasure omega _
      let Ak : Set M := {x | φ x - ((k : ℝ) : EReal) < v x}
      have hAAk : A ⊆ Ak := fun x hx => lt_of_le_of_lt (EReal.sub_le_sub le_rfl
        (EReal.coe_le_coe_iff.mpr (Nat.cast_le.mpr hkk))) hx
      have hres : ν.restrict Ak = μ.restrict Ak :=
        diagonalPotentialMeasure_truncation_restrict θ hφp hrv.1 k (hvk k).1
      have hresA : ν.restrict A = μ.restrict A := by
        rw [← Measure.restrict_restrict_of_subset hAAk, hres,
          Measure.restrict_restrict_of_subset hAAk]
      have htype : SameSingularityTypeOn (uk k) (vk k) univ := (huk k).2.trans (hvk k).2.symm
      have heq : (fun x => canonicalERealDiffToReal (uk k x) (vk k x)) =
          fun x => (uk k x).toReal - (vk k x).toReal := funext fun x =>
        canonicalDiff_eq_sub_toReal ((huk k).1.1.quasiPlurisubharmonic.ne_top x)
          ((hvk k).1.1.quasiPlurisubharmonic.ne_top x)
          (sameSingularityTypeOn_eq_bot_iff htype (mem_univ x))
      have hgi : Integrable (fun x => (uk k x).toReal - (vk k x).toReal) ν := by
        have h := integrable_canonicalDiff_globalMixedMeasure omega (huk k).1.1 (hvk k).1.1
          htype (fun _ : Fin n => (hvk k).1.1)
        rwa [heq] at h
      have hg0 : ∀ x, 0 ≤ (uk k x).toReal - (vk k x).toReal := by
        intro x
        have h := SingularModelEnergyEndpointBounds.canonicalDiff_nonpos_of_le_of_sameType
          (hvk k).1.1.quasiPlurisubharmonic.ne_top (huk k).1.1.quasiPlurisubharmonic.ne_top
          htype.symm (horder k) x
        rw [canonicalDiff_eq_sub_toReal ((hvk k).1.1.quasiPlurisubharmonic.ne_top x)
          ((huk k).1.1.quasiPlurisubharmonic.ne_top x)
          (sameSingularityTypeOn_eq_bot_iff htype.symm (mem_univ x))] at h
        linarith
      calc (∫ x, f x ∂μ) = ∫ x in A, ((u x).toReal - (v x).toReal) ∂μ := integral_indicator hAm
        _ = ∫ x in A, ((uk k x).toReal - (vk k x).toReal) ∂μ := by
          apply setIntegral_congr_fun hAm
          intro x hx
          have ev : vk k x = v x := truncation_eq_of_lt (hAAk hx)
          have eu : uk k x = u x := truncation_eq_of_lt ((hAAk hx).trans_le (hvu x))
          change (u x).toReal - (v x).toReal = (uk k x).toReal - (vk k x).toReal
          rw [eu, ev]
        _ = ∫ x in A, ((uk k x).toReal - (vk k x).toReal) ∂ν := by rw [hresA]
        _ ≤ ∫ x, ((uk k x).toReal - (vk k x).toReal) ∂ν :=
          setIntegral_le_integral hgi (Eventually.of_forall hg0)
    have hint0 : (∫ x, f x ∂μ) ≤ 0 := ge_of_tendsto hD (eventually_atTop.2 ⟨k₀, hle⟩)
    have hzero : f =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg hf0 hfi).1 (le_antisymm hint0 (integral_nonneg hf0))
    refine measure_mono_null ?_ (ae_iff.mp hzero)
    rintro x ⟨hxA, hxlt⟩
    change ¬ f x = 0
    rw [show f x = (u x).toReal - (v x).toReal from indicator_of_mem hxA _]
    have hreal : (v x).toReal < (u x).toReal := by
      have h := hxlt
      change v x < u x at h
      rw [← EReal.coe_toReal (hvtop x) (hvfin x hxA),
        ← EReal.coe_toReal (hutop x) (hufin x hxA)] at h
      exact EReal.coe_lt_coe_iff.mp h
    linarith
  have hcover : {x | v x < u x} ⊆
      (⋃ k : ℕ, ({x | φ x - ((k : ℝ) : EReal) < v x} ∩ {x | v x < u x})) ∪ {x | v x = ⊥} := by
    intro x hx
    by_cases hbot : v x = ⊥
    · exact Or.inr hbot
    have hφbot : φ x ≠ ⊥ := ne_bot_of_le_ne_bot hbot (hrv.2 x)
    have hφtop := hφp.1.quasiPlurisubharmonic.ne_top x
    have hvtop := hrv.1.1.quasiPlurisubharmonic.ne_top x
    obtain ⟨k, hk⟩ := exists_nat_gt ((φ x).toReal - (v x).toReal)
    refine Or.inl (mem_iUnion.2 ⟨k, ?_, hx⟩)
    change φ x - ((k : ℝ) : EReal) < v x
    rw [← EReal.coe_toReal hφtop hφbot, ← EReal.coe_sub, ← EReal.coe_toReal hvtop hbot]
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  refine measure_mono_null hcover (measure_union_null (measure_iUnion_null hlevel) ?_)
  exact FiniteEnergyCharacterization.diagonalPotentialMeasure_pole_null θ hv.1.plurisubharmonic

variable [ConnectedSpace M]

/-- Actual relative full-mass domination separates ordered normalized
finite-energy potentials with equal energy over an arbitrary singular model. -/
theorem eq_of_le_of_energy_eq (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergy θ φ u hφ) (hv : RelativeFiniteEnergy θ φ v hφ)
    (hvu : v ≤ u) (he : (energy θ φ hφ u).toReal = (energy θ φ hφ v).toReal) : u = v :=
  le_antisymm
    (FiniteGeodesicsFullMassAnyDim.le_of_relativeFullMass_of_measure_lt_eq_zero omega hv.1 hu.1
      (measure_lt_eq_zero_of_energy_eq omega hu hv hvu he)) hvu

/-- The actual genuine finite-energy rooftop and ordered separation produce
Darvas separation on the normalized finite-energy class of every model. -/
theorem eq_of_relativeD1_eq_zero (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergy θ φ u hφ) (hv : RelativeFiniteEnergy θ φ v hφ)
    (h : relativeD1 θ φ hφ u v = 0) : u = v := by
  have hr := RelativeDarvasDistance.relativeFiniteEnergy_rooftop omega hu hv
  have hpu := hu.1.plurisubharmonic
  have hpv := hv.1.plurisubharmonic
  have h1 := SingularModelFiniteRealEnergy.toReal_energy_mono omega
    (preceq_of_relativeFiniteEnergy hr) (preceq_of_relativeFiniteEnergy hu)
    (rooftop_le_left hpu hpv)
  have h2 := SingularModelFiniteRealEnergy.toReal_energy_mono omega
    (preceq_of_relativeFiniteEnergy hr) (preceq_of_relativeFiniteEnergy hv)
    (rooftop_le_right hpu hpv)
  rw [relativeD1] at h
  have e1 : (energy θ φ hφ u).toReal = (energy θ φ hφ (rooftop θ u v)).toReal := by linarith
  have e2 : (energy θ φ hφ v).toReal = (energy θ φ hφ (rooftop θ u v)).toReal := by linarith
  exact (eq_of_le_of_energy_eq omega hu hr (rooftop_le_left hpu hpv) e1).trans
    (eq_of_le_of_energy_eq omega hv hr (rooftop_le_right hpu hpv) e2).symm

/-- Actual common finite translations transfer Darvas separation to Xia's
full singularity-order finite-energy class, with no boundedness of the model. -/
theorem eq_of_relativeD1_eq_zero_of_preceq (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (h : relativeD1 θ φ hφ u v = 0) : u = v := by
  obtain ⟨c, hc₀, hc₁⟩ := exists_common_add_le hu.1.relativePSHPreceq hv.1.relativePSHPreceq
  rw [← SingularModelDarvasBasic.relativeD1_add_const omega hu hv c] at h
  have e := eq_of_relativeD1_eq_zero omega (hu.relativeFiniteEnergy_add omega hc₀)
    (hv.relativeFiniteEnergy_add omega hc₁) h
  funext x
  exact add_coe_injective c (congrFun e x)

/-- The actual Darvas functional satisfies all metric properties on the
genuine finite-energy singularity-order class of every singular model. -/
theorem relativeD1_isMetric_of_preceq (omega : KahlerBackground n M) :
    (∀ u v, RelativeFiniteEnergyPreceq θ φ u hφ → RelativeFiniteEnergyPreceq θ φ v hφ →
      0 ≤ relativeD1 θ φ hφ u v) ∧
    (∀ u, RelativeFiniteEnergyPreceq θ φ u hφ → relativeD1 θ φ hφ u u = 0) ∧
    (∀ u v, relativeD1 θ φ hφ u v = relativeD1 θ φ hφ v u) ∧
    (∀ u v w, RelativeFiniteEnergyPreceq θ φ u hφ → RelativeFiniteEnergyPreceq θ φ v hφ →
      RelativeFiniteEnergyPreceq θ φ w hφ →
      relativeD1 θ φ hφ u v ≤ relativeD1 θ φ hφ u w + relativeD1 θ φ hφ w v) ∧
    (∀ u v, RelativeFiniteEnergyPreceq θ φ u hφ → RelativeFiniteEnergyPreceq θ φ v hφ →
      relativeD1 θ φ hφ u v = 0 → u = v) :=
  ⟨fun _ _ hu hv => SingularModelDarvasBasic.relativeD1_nonneg omega hu hv,
    fun _ hu => relativeD1_self hu.1.plurisubharmonic,
    fun u v => relativeD1_comm θ φ hφ u v,
    fun _ _ _ hu hv hw => SingularModelDarvasContraction.relativeD1_triangle omega hu hv hw,
    fun _ _ hu hv h => eq_of_relativeD1_eq_zero_of_preceq omega hu hv h⟩

end

end SGPT.Foundations.Analysis.Pending.SingularModelDarvasSeparation
