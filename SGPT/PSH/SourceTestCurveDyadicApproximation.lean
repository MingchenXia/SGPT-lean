import SGPT.PSH.SourceTestCurveEnergy
import SGPT.PSH.SourceTestCurveLegendreAlgebra
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.Order.MonotoneConvergence

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The existing entire original extension theorem gives genuine source PSH
at EVERY parameter through the cutoff, with zero cutoff mass permitted. -/
theorem SourceTestCurvePredata.at_thetaPSH_of_le (Γ : SourceTestCurvePredata θ)
    {τ : ℝ} (hτ : τ ≤ Γ.max) :
    (ofFixedModel n M).IsThetaPSH θ (sourceTestCurveAt Γ τ) :=
  (source_test_curve_extension_whole Γ).2.2.2 τ hτ


omit [CompactSpace M] [ConnectedSpace M] in
/-- The LITERAL entire nonpositive-integer dyadic prefix, retaining the
actual cutoff k=0 and every original extended-real pole. -/
def sourceTestCurveDyadicLegendre (Γ : SourceTestCurvePredata θ) (N : ℕ)
    (t : ℝ) : M → EReal := fun x ↦
  ⨆ k : Iic (0 : ℤ), sourceTestCurveAt Γ ((k.1 : ℝ) / (2 : ℝ)^N) x +
    ((t * ((k.1 : ℝ) / (2 : ℝ)^N) : ℝ) : EReal)

omit [CompactSpace M] [ConnectedSpace M] in
/-- EXACT integer-grid nesting k↦2k produces genuine increase of the SAME
whole prefixes, without maximizers or finite-value assumptions. -/
theorem SourceTestCurvePredata.dyadicLegendre_monotone (Γ : SourceTestCurvePredata θ)
    (t : ℝ) : Monotone (fun N : ℕ ↦ sourceTestCurveDyadicLegendre Γ N t) := by
  apply monotone_nat_of_le_succ
  intro N x
  apply iSup_le
  intro k
  let j : Iic (0 : ℤ) := ⟨2 * k.1, by have hk : k.1 ≤ 0 := k.2; change 2 * k.1 ≤ 0; omega⟩
  have hgrid : (j.1 : ℝ) / (2 : ℝ)^(N + 1) = (k.1 : ℝ) / (2 : ℝ)^N := by
    dsimp [j]
    push_cast
    rw [pow_succ]
    have hd : (2 : ℝ)^N ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  have hh := le_iSup (fun q : Iic (0 : ℤ) ↦
    sourceTestCurveAt Γ ((q.1 : ℝ) / (2 : ℝ)^(N + 1)) x +
      ((t * ((q.1 : ℝ) / (2 : ℝ)^(N + 1)) : ℝ) : EReal)) j
  simpa only [sourceTestCurveDyadicLegendre, hgrid] using hh


/-- The literal finite-real dyadic floor, with actual integer numerator. -/
def sourceDyadicFloor (N : ℕ) (τ : ℝ) : ℝ :=
  ((⌊(2 : ℝ)^N * τ⌋ : ℤ) : ℝ) / (2 : ℝ)^N

/-- BOTH exact floor bounds on EVERY natural level and real parameter. -/
theorem sourceDyadicFloor_le (N : ℕ) (τ : ℝ) :
    sourceDyadicFloor N τ ≤ τ ∧ τ < sourceDyadicFloor N τ + 1 / (2 : ℝ)^N := by
  have hd : 0 < (2 : ℝ)^N := pow_pos (by norm_num) N
  refine ⟨(div_le_iff₀ hd).mpr ?_, ?_⟩
  · simpa only [mul_comm] using Int.floor_le ((2 : ℝ)^N * τ)
  · have hh := Int.lt_floor_add_one ((2 : ℝ)^N * τ)
    have hdiv : τ < ((((⌊(2 : ℝ)^N * τ⌋ : ℤ) : ℝ) + 1) / (2 : ℝ)^N) :=
      (lt_div_iff₀ hd).mpr (by simpa only [mul_comm] using hh)
    simpa only [add_div, sourceDyadicFloor] using hdiv

private theorem dyadic_mesh_tendsto :
    Tendsto (fun N : ℕ ↦ 1 / (2 : ℝ)^N) atTop (𝓝 0) := by
  have hh := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹)
    (by norm_num) (by norm_num)
  simpa only [one_div, inv_pow] using hh

/-- Genuine floor convergence follows ONLY from actual floor errors and
geometric mesh squeeze; no potential continuity or readback is used. -/
theorem sourceDyadicFloor_tendsto (τ : ℝ) :
    Tendsto (fun N : ℕ ↦ sourceDyadicFloor N τ) atTop (𝓝 τ) := by
  have herr : Tendsto (fun N : ℕ ↦ τ - sourceDyadicFloor N τ) atTop (𝓝 0) := by
    apply squeeze_zero (fun N ↦ sub_nonneg.mpr (sourceDyadicFloor_le N τ).1)
      (fun N ↦ ?_) dyadic_mesh_tendsto
    linarith [(sourceDyadicFloor_le N τ).2]
  simpa only [sub_sub_cancel, sub_zero] using
    (tendsto_const_nhds (x := τ)).sub herr


omit [CompactSpace M] [ConnectedSpace M] in
/-- The SAME full dyadic prefixes have precisely the original raw
Legendre supremum, including every literal pole. Floor approach uses only
parameter antitonicity and finite-coefficient EReal continuity. -/
theorem SourceTestCurvePredata.dyadicLegendre_iSup_eq_raw (Γ : SourceTestCurvePredata θ)
    (hmax : Γ.max = 0) (t : ℝ) (_ht : 0 < t) (x : M) :
    (⨆ N : ℕ, sourceTestCurveDyadicLegendre Γ N t x) = sourceTestCurveRawLegendre Γ t x := by
  apply le_antisymm
  · apply iSup_le
    intro N
    apply iSup_le
    intro k
    rw [add_comm]
    exact le_iSup (fun τ : ℝ ↦ ((t * τ : ℝ) : EReal) + sourceTestCurveAt Γ τ x)
      ((k.1 : ℝ) / (2 : ℝ)^N)
  · rw [Γ.rawLegendre_eq_iSup_open]
    apply iSup_le
    intro τ
    have hτ0 : τ.1 < 0 := by
      have htau : τ.1 < Γ.max := τ.2
      simpa only [hmax] using htau
    have hlower (N : ℕ) : ((t * sourceDyadicFloor N τ.1 : ℝ) : EReal) + Γ.potential τ x ≤
        ⨆ j : ℕ, sourceTestCurveDyadicLegendre Γ j t x := by
      let k : Iic (0 : ℤ) := ⟨⌊(2 : ℝ)^N * τ.1⌋, by
        change ⌊(2 : ℝ)^N * τ.1⌋ ≤ 0
        exact (Int.floor_lt_zero.mpr (mul_neg_of_pos_of_neg (pow_pos (by norm_num) N) hτ0)).le⟩
      have hΓ := Γ.at_antitone x (sourceDyadicFloor_le N τ.1).1
      change sourceTestCurveAt Γ τ.1 x ≤ sourceTestCurveAt Γ (sourceDyadicFloor N τ.1) x at hΓ
      rw [sourceTestCurveAt_of_lt Γ τ.2] at hΓ
      calc
        _ ≤ ((t * sourceDyadicFloor N τ.1 : ℝ) : EReal) +
            sourceTestCurveAt Γ (sourceDyadicFloor N τ.1) x := add_le_add le_rfl hΓ
        _ ≤ sourceTestCurveDyadicLegendre Γ N t x := by
          rw [add_comm]
          exact le_iSup (fun q : Iic (0 : ℤ) ↦
            sourceTestCurveAt Γ ((q.1 : ℝ) / (2 : ℝ)^N) x +
              ((t * ((q.1 : ℝ) / (2 : ℝ)^N) : ℝ) : EReal)) k
        _ ≤ _ := le_iSup (fun j : ℕ ↦ sourceTestCurveDyadicLegendre Γ j t x) N
    have hreal : Tendsto (fun N : ℕ ↦ t * sourceDyadicFloor N τ.1) atTop (𝓝 (t * τ.1)) :=
      tendsto_const_nhds.mul (sourceDyadicFloor_tendsto τ.1)
    have hcoe := (continuous_coe_real_ereal.tendsto (t * τ.1)).comp hreal
    have hpair := hcoe.prodMk_nhds (tendsto_const_nhds (x := Γ.potential τ x))
    have hadd : ContinuousAt (fun p : EReal × EReal ↦ p.1 + p.2)
        (((t * τ.1 : ℝ) : EReal), Γ.potential τ x) :=
      EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _))
    have hlim : Tendsto (fun N : ℕ ↦ ((t * sourceDyadicFloor N τ.1 : ℝ) : EReal) + Γ.potential τ x)
        atTop (𝓝 (((t * τ.1 : ℝ) : EReal) + Γ.potential τ x)) := by
      simpa only [Function.comp_def] using hadd.tendsto.comp hpair
    exact le_of_tendsto hlim (Eventually.of_forall hlower)

omit [CompactSpace M] [ConnectedSpace M] in
/-- Existing complete-lattice monotone convergence gives the actual
original raw limit, retaining the all-bottom case without noncollapse input. -/
theorem SourceTestCurvePredata.dyadicLegendre_tendsto (Γ : SourceTestCurvePredata θ)
    (hmax : Γ.max = 0) (t : ℝ) (ht : 0 < t) (x : M) :
    Tendsto (fun N : ℕ ↦ sourceTestCurveDyadicLegendre Γ N t x) atTop
      (𝓝 (sourceTestCurveRawLegendre Γ t x)) := by
  rw [← Γ.dyadicLegendre_iSup_eq_raw hmax t ht x]
  exact tendsto_atTop_iSup (fun N P hNP ↦ Γ.dyadicLegendre_monotone t hNP x)


/-- LITERAL finite dyadic left mass sum on the fixed interval [-L,0]. -/
def dyadicMassLeftSum (f : ℝ → ℝ) (L N : ℕ) : ℝ :=
  (1 / (2 : ℝ)^N) * ∑ j ∈ Finset.range (L * 2^N),
    f (-(L : ℝ) + (1 / (2 : ℝ)^N) * (j : ℝ))

/-- LITERAL finite dyadic right mass sum INCLUDING its actual endpoint0. -/
def dyadicMassRightSum (f : ℝ → ℝ) (L N : ℕ) : ℝ :=
  (1 / (2 : ℝ)^N) * ∑ j ∈ Finset.range (L * 2^N),
    f (-(L : ℝ) + (1 / (2 : ℝ)^N) * ((j + 1 : ℕ) : ℝ))

/-- EXISTING actual Mathlib antitone sum-integral comparisons and affine
change of variables give genuine Darboux bounds; finite telescoping gives
the EXACT gap, with no energy/integrability certificate assumed. -/
theorem dyadicMassSums_bounds_gap (f : ℝ → ℝ) (hf : Antitone f)
    (V : ℝ) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ V) (L N : ℕ) :
    IntervalIntegrable f volume (-(L : ℝ)) 0 ∧
    dyadicMassRightSum f L N ≤ ∫ x in (-(L : ℝ))..0, f x ∧
    (∫ x in (-(L : ℝ))..0, f x) ≤ dyadicMassLeftSum f L N ∧
    dyadicMassLeftSum f L N - dyadicMassRightSum f L N =
      (1 / (2 : ℝ)^N) * (f (-(L : ℝ)) - f 0) ∧
    0 ≤ dyadicMassLeftSum f L N - dyadicMassRightSum f L N ∧
    dyadicMassLeftSum f L N - dyadicMassRightSum f L N ≤ (1 / (2 : ℝ)^N) * V := by
  let δ : ℝ := 1 / (2 : ℝ)^N
  let J : ℕ := L * 2^N
  let g : ℝ → ℝ := fun u ↦ f (-(L : ℝ) + δ * u)
  have hδ : 0 < δ := one_div_pos.mpr (pow_pos (by norm_num) N)
  have hJ : (J : ℝ) = (L : ℝ) * (2 : ℝ)^N := by dsimp [J]; push_cast; rfl
  have hend : -(L : ℝ) + δ * (J : ℝ) = 0 := by
    rw [hJ]
    dsimp [δ]
    have hd : (2 : ℝ)^N ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
    norm_num
  have hg : Antitone g := by
    intro a b hab
    apply hf
    nlinarith
  have hlo := AntitoneOn.sum_le_integral (f := g) (a := J) (x₀ := 0) (hg.antitoneOn _)
  have hup := AntitoneOn.integral_le_sum (f := g) (a := J) (x₀ := 0) (hg.antitoneOn _)
  have hchange : δ * (∫ u in (0 : ℝ)..(J : ℝ), g u) = ∫ x in (-(L : ℝ))..0, f x := by
    have hh := intervalIntegral.smul_integral_comp_add_mul (a := 0) (b := (J : ℝ)) f δ (-(L : ℝ))
    simpa only [smul_eq_mul, mul_zero, add_zero, hend] using hh
  have hlow : dyadicMassRightSum f L N ≤ ∫ x in (-(L : ℝ))..0, f x := by
    have hh := mul_le_mul_of_nonneg_left hlo hδ.le
    simpa only [zero_add, hchange, g, δ, J, dyadicMassRightSum] using hh
  have hupp : (∫ x in (-(L : ℝ))..0, f x) ≤ dyadicMassLeftSum f L N := by
    have hh := mul_le_mul_of_nonneg_left hup hδ.le
    simpa only [zero_add, hchange, g, δ, J, dyadicMassLeftSum] using hh
  have hgap : dyadicMassLeftSum f L N - dyadicMassRightSum f L N =
      δ * (f (-(L : ℝ)) - f 0) := by
    change δ * (∑ j ∈ Finset.range J, g (j : ℝ)) -
      δ * (∑ j ∈ Finset.range J, g ((j + 1 : ℕ) : ℝ)) = _
    rw [← mul_sub, ← Finset.sum_sub_distrib,
      Finset.sum_range_sub' (fun j : ℕ ↦ g (j : ℝ)) J]
    simp only [g, Nat.cast_zero, mul_zero, add_zero, hend]
  refine ⟨hf.intervalIntegrable, hlow, hupp, hgap, ?_, ?_⟩
  · linarith
  · rw [hgap]
    exact mul_le_mul_of_nonneg_left (by linarith [(hbound (-(L : ℝ))).2, (hbound 0).1]) hδ.le


/-- Genuine dyadic Darboux errors squeeze to zero for a fixed finite
interval, using manufactured monotone integrability and the exact finite
endpoint gap. No energy or integrability output certificate is an input. -/
theorem dyadicMassSums_tendsto (f : ℝ → ℝ) (hf : Antitone f)
    (V : ℝ) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ V) (L : ℕ) :
    Tendsto (fun N : ℕ ↦ dyadicMassLeftSum f L N) atTop
      (𝓝 (∫ x in (-(L : ℝ))..0, f x)) ∧
    Tendsto (fun N : ℕ ↦ dyadicMassRightSum f L N) atTop
      (𝓝 (∫ x in (-(L : ℝ))..0, f x)) := by
  let I : ℝ := ∫ x in (-(L : ℝ))..0, f x
  have hmesh : Tendsto (fun N : ℕ ↦ (1 / (2 : ℝ)^N) * V) atTop (𝓝 0) := by
    simpa only [zero_mul] using dyadic_mesh_tendsto.mul_const V
  have hleft : Tendsto (fun N : ℕ ↦ dyadicMassLeftSum f L N - I) atTop (𝓝 0) := by
    apply squeeze_zero (fun N ↦ sub_nonneg.mpr (dyadicMassSums_bounds_gap f hf V hbound L N).2.2.1)
      (fun N ↦ ?_) hmesh
    have hb := dyadicMassSums_bounds_gap f hf V hbound L N
    have hlo := hb.2.1
    have hgap := hb.2.2.2.2.2
    change dyadicMassRightSum f L N ≤ I at hlo
    linarith
  have hright : Tendsto (fun N : ℕ ↦ I - dyadicMassRightSum f L N) atTop (𝓝 0) := by
    apply squeeze_zero (fun N ↦ sub_nonneg.mpr (dyadicMassSums_bounds_gap f hf V hbound L N).2.1)
      (fun N ↦ ?_) hmesh
    have hb := dyadicMassSums_bounds_gap f hf V hbound L N
    have hup := hb.2.2.1
    have hgap := hb.2.2.2.2.2
    change I ≤ dyadicMassLeftSum f L N at hup
    linarith
  constructor
  · simpa only [sub_add_cancel, zero_add] using hleft.add_const I
  · simpa only [sub_sub_cancel, sub_zero] using (tendsto_const_nhds (x := I)).sub hright

variable [MeasurableSpace M] [BorelSpace M]

/-- ACTUAL closed-slice NP mass finiteness is manufactured from genuine
PSH BEFORE any real mass readback, including at the true cutoff. -/
theorem SourceTestCurve.closedMass_lt_top (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) {τ : ℝ} (hτ : τ ≤ Γ.max) :
    sourcePotentialNonPluripolarMeasure θ (sourceTestCurveAt Γ.toSourceTestCurvePredata τ)
      (Γ.toSourceTestCurvePredata.at_thetaPSH_of_le hτ) univ < ⊤ := by
  simpa only [sourceMixedNonPluripolarMass_diagonal] using
    (sourceMixedNonPluripolarMass_lt_top omega (fun _ : Fin n ↦ θ)
      (fun _ ↦ sourceTestCurveAt Γ.toSourceTestCurvePredata τ)
      (fun _ ↦ Γ.toSourceTestCurvePredata.at_thetaPSH_of_le hτ))

/-- ACTUAL closed NP mass with its finiteness proved BEFORE readback.
Above the cutoff it continues by the SAME genuine cutoff mass, never by
the old auxiliary outside-domain zero. -/
def sourceTestCurveClosedRealMassAt (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (τ : ℝ) : ℝ :=
  let finite : {m : ENNReal // m < ⊤} :=
    ⟨sourcePotentialNonPluripolarMeasure θ
      (sourceTestCurveAt Γ.toSourceTestCurvePredata (min τ Γ.max))
      (Γ.toSourceTestCurvePredata.at_thetaPSH_of_le (min_le_right _ _)) univ,
      Γ.closedMass_lt_top omega (min_le_right _ _)⟩
  finite.1.toReal

/-- The SAME original actual measure at EVERY original closed parameter. -/
theorem sourceTestCurveClosedRealMassAt_of_le (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) {τ : ℝ} (hτ : τ ≤ Γ.max) :
    sourceTestCurveClosedRealMassAt omega Γ τ =
      (sourcePotentialNonPluripolarMeasure θ (sourceTestCurveAt Γ.toSourceTestCurvePredata τ)
        (Γ.toSourceTestCurvePredata.at_thetaPSH_of_le hτ) univ).toReal := by
  simp only [sourceTestCurveClosedRealMassAt, min_eq_left hτ]

omit [ConnectedSpace M] [BorelSpace M] in
private theorem closed_realMass_congr {u v : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (heq : u = v) :
    (sourcePotentialNonPluripolarMeasure θ u hu univ).toReal =
      (sourcePotentialNonPluripolarMeasure θ v hv univ).toReal := by
  cases heq
  rfl

/-- At the cutoff this is its TRUE actual NP mass, which may be zero.
No equality with the old dummy mass reader is claimed here. -/
theorem sourceTestCurveClosedRealMassAt_cutoff (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) :
    sourceTestCurveClosedRealMassAt omega Γ Γ.max =
      (sourcePotentialNonPluripolarMeasure θ (sourceTestCurveCutoff Γ.toSourceTestCurvePredata)
        Γ.toSourceTestCurvePredata.cutoff_thetaPSH univ).toReal := by
  rw [sourceTestCurveClosedRealMassAt_of_le omega Γ le_rfl]
  exact closed_realMass_congr _ _ (sourceTestCurveAt_eq_max Γ.toSourceTestCurvePredata)

/-- Agreement with the old auxiliary reader is asserted precisely BELOW
cutoff; the genuine actual cutoff measure is retained separately. -/
theorem sourceTestCurveClosedRealMassAt_eq_realMassAt_of_lt (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) {τ : ℝ} (hτ : τ < Γ.max) :
    sourceTestCurveClosedRealMassAt omega Γ τ = sourceTestCurveRealMassAt omega Γ τ := by
  rw [sourceTestCurveClosedRealMassAt_of_le omega Γ hτ.le,
    sourceTestCurveRealMassAt_of_lt omega Γ hτ]
  exact closed_realMass_congr _ _ (sourceTestCurveAt_of_lt Γ.toSourceTestCurvePredata hτ)

/-- Actual whole-parameter source order and genuine NP mass monotonicity
produce an antitone REAL closed-mass function, including the cutoff. -/
theorem sourceTestCurveClosedRealMassAt_antitone (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) : Antitone (sourceTestCurveClosedRealMassAt omega Γ) := by
  intro a b hab
  apply ENNReal.toReal_mono (Γ.closedMass_lt_top omega (min_le_right a Γ.max)).ne
  apply sourcePotentialNonPluripolarMass_mono omega
    (Γ.toSourceTestCurvePredata.at_thetaPSH_of_le (min_le_right b Γ.max))
    (Γ.toSourceTestCurvePredata.at_thetaPSH_of_le (min_le_right a Γ.max))
  exact MoreSingularOn.of_le fun x _ ↦ Γ.toSourceTestCurvePredata.at_antitone x (min_le_min hab le_rfl)

/-- The actual based model and genuine mass order produce the complete
finite interval bounds, with zero cutoff mass explicitly retained. -/
theorem sourceTestCurveClosedRealMassAt_nonneg_le_model (omega : KahlerBackground n M)
    {φ : M → EReal} (hφ : SourceModelPotential θ φ) (Γ : SourceTestCurve θ)
    (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ) (τ : ℝ) :
    0 ≤ sourceTestCurveClosedRealMassAt omega Γ τ ∧
    sourceTestCurveClosedRealMassAt omega Γ τ ≤
      (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal := by
  have hfin : sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ < ⊤ := by
    simpa only [sourceMixedNonPluripolarMass_diagonal] using
      (sourceMixedNonPluripolarMass_lt_top omega (fun _ : Fin n ↦ θ)
        (fun _ ↦ φ) (fun _ ↦ hφ.thetaPSH))
  refine ⟨ENNReal.toReal_nonneg, ENNReal.toReal_mono hfin.ne ?_⟩
  apply sourcePotentialNonPluripolarMass_mono omega
    (Γ.toSourceTestCurvePredata.at_thetaPSH_of_le (min_le_right τ Γ.max)) hφ.thetaPSH
  apply MoreSingularOn.of_le
  intro x _
  have hx := Γ.toSourceTestCurvePredata.at_le_limit (min τ Γ.max) x
  change sourceTestCurveLimit Γ.toSourceTestCurvePredata = φ at hΓ
  rwa [hΓ] at hx

/-- Existing real antitone measurability applies to the ACTUAL mass reader. -/
theorem sourceTestCurveClosedRealMassAt_measurable (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) : Measurable (sourceTestCurveClosedRealMassAt omega Γ) :=
  (sourceTestCurveClosedRealMassAt_antitone omega Γ).measurable

/-- ACTUAL boundedness internally produces a negative integer anchor,
all original earlier function equalities, and its SAME actual model mass.
No anchor, finite energy or positive cutoff mass is supplied as a premise. -/
theorem SourceTestCurve.exists_integer_model_anchor (omega : KahlerBackground n M)
    {φ : M → EReal} (hφ : SourceModelPotential θ φ) (Γ : SourceTestCurve θ)
    (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ) (hmax : Γ.max = 0) :
    ∃ L : ℕ, 0 < L ∧
      (∀ τ : ℝ, τ ≤ -(L : ℝ) → sourceTestCurveAt Γ.toSourceTestCurvePredata τ = φ) ∧
      sourceTestCurveClosedRealMassAt omega Γ (-(L : ℝ)) =
        (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal := by
  obtain ⟨σ, hσ⟩ := eventually_atBot.mp hΓ.2
  obtain ⟨L, hL⟩ := exists_nat_gt (max (-σ.1) (0 : ℝ))
  have hLreal : (0 : ℝ) < L := (le_max_right _ _).trans_lt hL
  have hLnat : 0 < L := by exact_mod_cast hLreal
  have hminus : -(L : ℝ) ≤ σ.1 := by linarith [le_max_left (-σ.1) (0 : ℝ)]
  have hanchor (τ : ℝ) (hτ : τ ≤ -(L : ℝ)) :
      sourceTestCurveAt Γ.toSourceTestCurvePredata τ = φ := by
    have ht : τ < Γ.max := by rw [hmax]; linarith
    rw [sourceTestCurveAt_of_lt Γ.toSourceTestCurvePredata ht]
    exact hσ ⟨τ, ht⟩ (show (⟨τ, ht⟩ : Iio Γ.max) ≤ σ from hτ.trans hminus)
  refine ⟨L, hLnat, hanchor, ?_⟩
  rw [sourceTestCurveClosedRealMassAt_of_le omega Γ
    (show -(L : ℝ) ≤ Γ.max by rw [hmax]; linarith)]
  exact closed_realMass_congr _ _ (hanchor (-(L : ℝ)) le_rfl)

/-- The ORIGINAL bounded curve internally produces its genuine integer
anchor and ACTUAL closed-mass dyadic Riemann limits. The endpoint is the
true cutoff NP mass (possibly zero), never the old dummy0 branch.
No prefix energy increment or energy-continuity conclusion is assumed. -/
theorem source_test_curve_dyadic_mass_riemann (omega : KahlerBackground n M)
    {φ : M → EReal} (hφ : SourceModelPotential θ φ) (Γ : SourceTestCurve θ)
    (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ) (hmax : Γ.max = 0) :
    let f := sourceTestCurveClosedRealMassAt omega Γ
    let V := (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal
    ∃ L : ℕ, 0 < L ∧
      (∀ τ : ℝ, τ ≤ -(L : ℝ) → sourceTestCurveAt Γ.toSourceTestCurvePredata τ = φ) ∧
      f (-(L : ℝ)) = V ∧
      (∀ N j : ℕ, j ≤ L * 2^N →
        -(L : ℝ) + (1 / (2 : ℝ)^N) * (j : ℝ) ∈ Icc (-(L : ℝ)) Γ.max) ∧
      IntervalIntegrable f volume (-(L : ℝ)) 0 ∧
      (∀ N : ℕ, dyadicMassRightSum f L N ≤ ∫ x in (-(L : ℝ))..0, f x ∧
        (∫ x in (-(L : ℝ))..0, f x) ≤ dyadicMassLeftSum f L N ∧
        dyadicMassLeftSum f L N - dyadicMassRightSum f L N =
          (1 / (2 : ℝ)^N) * (V - f 0) ∧
        0 ≤ dyadicMassLeftSum f L N - dyadicMassRightSum f L N ∧
        dyadicMassLeftSum f L N - dyadicMassRightSum f L N ≤ (1 / (2 : ℝ)^N) * V) ∧
      Tendsto (fun N : ℕ ↦ dyadicMassLeftSum f L N) atTop (𝓝 (∫ x in (-(L : ℝ))..0, f x)) ∧
      Tendsto (fun N : ℕ ↦ dyadicMassRightSum f L N) atTop (𝓝 (∫ x in (-(L : ℝ))..0, f x)) := by
  let f := sourceTestCurveClosedRealMassAt omega Γ
  let V := (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal
  obtain ⟨L, hL, hanchor, hmass⟩ := Γ.exists_integer_model_anchor omega hφ hΓ hmax
  have hf : Antitone f := sourceTestCurveClosedRealMassAt_antitone omega Γ
  have hb : ∀ x, 0 ≤ f x ∧ f x ≤ V :=
    sourceTestCurveClosedRealMassAt_nonneg_le_model omega hφ Γ hΓ.1
  have hgrid (N j : ℕ) (hj : j ≤ L * 2^N) :
      -(L : ℝ) + (1 / (2 : ℝ)^N) * (j : ℝ) ∈ Icc (-(L : ℝ)) Γ.max := by
    have hd : 0 < (2 : ℝ)^N := pow_pos (by norm_num) N
    have hδ : 0 ≤ 1 / (2 : ℝ)^N := (one_div_pos.mpr hd).le
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hj' : (j : ℝ) ≤ (L : ℝ) * (2 : ℝ)^N := by exact_mod_cast hj
    have hh := mul_le_mul_of_nonneg_left hj' hδ
    have hcancel : (1 / (2 : ℝ)^N) * ((L : ℝ) * (2 : ℝ)^N) = L := by field_simp
    rw [hcancel] at hh
    rw [hmax]
    constructor <;> nlinarith
  have hlim := dyadicMassSums_tendsto f hf V hb L
  refine ⟨L, hL, hanchor, hmass, hgrid, hf.intervalIntegrable, ?_, hlim.1, hlim.2⟩
  intro N
  obtain ⟨_, hlo, hup, hgap, hnonneg, hbound⟩ := dyadicMassSums_bounds_gap f hf V hb L N
  change f (-(L : ℝ)) = V at hmass
  rw [hmass] at hgap
  exact ⟨hlo, hup, hgap, hnonneg, hbound⟩

end SGPT.PSH.VariableComplexAtlas
