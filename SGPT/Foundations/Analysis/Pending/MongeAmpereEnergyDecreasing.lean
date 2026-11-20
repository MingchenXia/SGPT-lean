import SGPT.Foundations.Analysis.Pending.BoundedMongeAmpereEnergy

set_option autoImplicit false

/-!
# Decreasing limits of the Monge–Ampère energy

Let `(M, ω)` be a compact Kähler manifold and `θ` a smooth closed real `(1,1)`-form.

* **Bounded potentials** (`relativeEnergyOfMinimalType_tendsto_of_antitone`): if bounded `θ`-PSH
  `u_k` decrease to a bounded `θ`-PSH `u`, then `E^φ(u_k) → E^φ(u)` for every bounded reference
  `φ`. Indeed `0 ≤ E^φ(u_k) - E^φ(u) ≤ ∫ (u_k - u) θ_u^n` (Xia (3.33)), and the right-hand side tends
  to `0` by dominated convergence against the fixed measure `θ_u^n`.
* **Canonical approximation** (`relativeMongeAmpereEnergy_eq_iInf_truncation`): for a bounded model
  potential `φ` and any `u ∈ PSH(X, θ; φ)`, the extended energy (Xia (3.30)) is the decreasing limit
  of the energies of the bounded truncations `max(u, φ - j)`.
* **Decreasing continuity of the extended energy** (`relativeMongeAmpereEnergy_tendsto_of_antitone`):
  for a bounded model potential, if relative potentials `u_k` decrease to a relative potential `u`,
  then `E(u_k)` decreases to `E(u)` (Xia, SGPT Lemma 3.1.6, for a bounded model potential).

The bounded case of the energy (cocycle, comparison, monotonicity) is
`Pending.BoundedMongeAmpereEnergy`.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.MongeAmpereEnergyDecreasing

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar BoundedGlobalProduct
open RelativeEnergy BoundedMongeAmpereEnergy

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-! ### Bounded potentials -/

section Bounded

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- A pointwise decreasing limit lies below every member. -/
theorem le_of_antitone_of_tendsto {uk : ℕ → M → EReal} {u : M → EReal}
    (hanti : ∀ x, Antitone fun k => uk k x)
    (hlim : ∀ x, Tendsto (fun k => uk k x) atTop (𝓝 (u x))) (k : ℕ) : u ≤ uk k := fun x =>
  (hanti x).le_of_tendsto (hlim x) k

/-- **Decreasing continuity of the energy of bounded potentials.** If bounded `θ`-PSH `u_k`
decrease pointwise to a bounded `θ`-PSH `u`, then `E^φ(u_k) → E^φ(u)` for every bounded `θ`-PSH
reference `φ`. -/
theorem relativeEnergyOfMinimalType_tendsto_of_antitone (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u : M → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hφb : IsBoundedPotential φ) (hu : IsThetaPshPotential θ.val u) (hub : IsBoundedPotential u)
    {uk : ℕ → M → EReal} (huk : ∀ k, IsThetaPshPotential θ.val (uk k))
    (hukb : ∀ k, IsBoundedPotential (uk k)) (hanti : ∀ x, Antitone fun k => uk k x)
    (hlim : ∀ x, Tendsto (fun k => uk k x) atTop (𝓝 (u x))) :
    Tendsto (fun k => relativeEnergyOfMinimalType θ φ (uk k) hφ (huk k)) atTop
      (𝓝 (relativeEnergyOfMinimalType θ φ u hφ hu)) := by
  have hle := le_of_antitone_of_tendsto hanti hlim
  set μ := globalMixedMeasure (fun _ => θ) (fun _ => u) (fun _ => hu.1) with hμ
  have hfin : IsFiniteMeasure μ := globalMixedMeasure_isFiniteMeasure_of_bounded _ fun _ => hub
  -- the upper bound tends to zero
  have hbound : Tendsto (fun k => ∫ x, ((uk k x).toReal - (u x).toReal) ∂μ) atTop (𝓝 0) := by
    obtain ⟨Q0, hQ0⟩ := GlobalSlotStokes.IsBoundedPotential.exists_abs_toReal_le (hukb 0)
    obtain ⟨Qu, hQu⟩ := GlobalSlotStokes.IsBoundedPotential.exists_abs_toReal_le hub
    have h0 : (∫ _x : M, (0 : ℝ) ∂μ) = 0 := integral_zero _ _
    rw [← h0]
    refine tendsto_integral_of_dominated_convergence (fun _ => Q0 + Qu) (fun k => ?_)
      (integrable_const _) (fun k => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · exact ((GlobalSlotStokes.ThetaPlurisubharmonic.measurable_toReal (huk k).1).sub
        (GlobalSlotStokes.ThetaPlurisubharmonic.measurable_toReal hu.1)).aestronglyMeasurable
    · have h1 : (uk k x).toReal ≤ (uk 0 x).toReal :=
        EReal.toReal_le_toReal (hanti x (Nat.zero_le k)) ((hukb k).ne_bot x) ((hukb 0).ne_top x)
      have h2 : (u x).toReal ≤ (uk k x).toReal :=
        EReal.toReal_le_toReal (hle k x) (hub.ne_bot x) ((hukb k).ne_top x)
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h2)]
      have := abs_le.mp (hQ0 x)
      have := abs_le.mp (hQu x)
      linarith
    · have ht := (EReal.tendsto_toReal (hub.ne_top x) (hub.ne_bot x)).comp (hlim x)
      simpa using ht.sub_const (u x).toReal
  -- the squeeze
  have hsq : Tendsto (fun k => relativeEnergyOfMinimalType θ φ (uk k) hφ (huk k) -
      relativeEnergyOfMinimalType θ φ u hφ hu) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound (fun k => ?_)
      (fun k => ?_)
    · exact sub_nonneg.mpr (relativeEnergyOfMinimalType_mono omega θ hφ hu (huk k) hφb hub
        (hukb k) (hle k))
    · exact (integral_le_relativeEnergyOfMinimalType_sub_le omega θ hφ (huk k) hu hφb (hukb k)
        hub).2
  simpa using hsq.add_const (relativeEnergyOfMinimalType θ φ u hφ hu)

end Bounded

/-! ### Truncations -/

section Truncation

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- The truncation `max(u, φ - j)`. -/
def truncation (φ u : M → EReal) (j : ℕ) : M → EReal :=
  fun x => max (u x) (φ x - ((j : ℝ) : EReal))

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
theorem le_truncation (φ u : M → EReal) (j : ℕ) : u ≤ truncation φ u j := fun _ =>
  le_max_left _ _

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- Truncations decrease in the level. -/
theorem truncation_antitone (φ u : M → EReal) (x : M) :
    Antitone fun j => truncation φ u j x := by
  intro i j hij
  refine max_le_max le_rfl ?_
  exact EReal.sub_le_sub le_rfl (EReal.coe_le_coe_iff.mpr (Nat.cast_le.mpr hij))

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- Truncations below a bounded `φ` are bounded. -/
theorem truncation_bounded {φ u : M → EReal} (hφb : IsBoundedPotential φ) (huφ : u ≤ φ)
    (j : ℕ) : IsBoundedPotential (truncation φ u j) := by
  obtain ⟨a, b, hab⟩ := hφb
  refine ⟨a - j, b, fun x => ⟨?_, max_le ((huφ x).trans (hab x).2) ?_⟩⟩
  · refine le_trans ?_ (le_max_right _ _)
    rw [EReal.coe_sub]
    exact EReal.sub_le_sub (hab x).1 le_rfl
  · have hj : (0 : EReal) ≤ ((j : ℝ) : EReal) :=
      EReal.coe_nonneg.mpr (Nat.cast_nonneg j)
    calc φ x - ((j : ℝ) : EReal) ≤ φ x - 0 := EReal.sub_le_sub le_rfl hj
      _ = φ x := sub_zero _
      _ ≤ b := (hab x).2

/-- Truncations of a `θ`-PSH function by a bounded `θ`-PSH function are `θ`-PSH potentials. -/
theorem isThetaPshPotential_truncation {θ : SmoothRealForm n M 2} {φ u : M → EReal}
    (hφ : ThetaPlurisubharmonic θ φ) (hu : ThetaPlurisubharmonic θ u)
    (hφb : IsBoundedPotential φ) (huφ : u ≤ φ) (j : ℕ) :
    IsThetaPshPotential θ (truncation φ u j) := by
  obtain ⟨a, b, hab⟩ := truncation_bounded hφb huφ j
  refine ⟨?_, BoundedPotentialSmoothingOfAlgebraicApproximation.locallyNondegenerate_of_coe_le
    fun x => (hab x).1⟩
  have h := BoundedGlobalProduct.ThetaPlurisubharmonic.max hu
    (GlobalPotentialTransforms.thetaPlurisubharmonic_sub_const hφ (j : ℝ))
  exact h

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- Truncations converge to the potential, also at its poles. -/
theorem tendsto_truncation {φ u : M → EReal} (hφb : IsBoundedPotential φ) (x : M) :
    Tendsto (fun j => truncation φ u j x) atTop (𝓝 (u x)) := by
  obtain ⟨a, b, hab⟩ := hφb
  -- `φ x - j → ⊥`
  have hbot : Tendsto (fun j : ℕ => φ x - ((j : ℝ) : EReal)) atTop (𝓝 ⊥) := by
    rw [EReal.tendsto_nhds_bot_iff_real]
    intro r
    obtain ⟨N, hN⟩ := exists_nat_gt (b - r)
    filter_upwards [eventually_ge_atTop N] with j hj
    have hjN : (N : ℝ) ≤ j := by exact_mod_cast hj
    calc φ x - ((j : ℝ) : EReal) ≤ (b : EReal) - ((j : ℝ) : EReal) :=
          EReal.sub_le_sub (hab x).2 le_rfl
      _ = ((b - j : ℝ) : EReal) := by rw [EReal.coe_sub]
      _ < r := EReal.coe_lt_coe_iff.mpr (by linarith)
  have h := (tendsto_const_nhds (x := u x)).max hbot
  simpa [truncation] using h

end Truncation

/-! ### The extended energy for a bounded model potential -/

section Extended

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **Canonical approximation of the extended energy.** For a bounded model potential `φ` and any
`u ∈ PSH(X, θ; φ)`, the extended energy (Xia (3.30)) is the infimum, and the decreasing limit, of
the energies of the bounded truncations `max(u, φ - j)`. -/
theorem relativeMongeAmpereEnergy_eq_iInf_truncation (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u : M → EReal} (hφ : IsModelPotential θ φ)
    (hu : RelativePSH θ φ u) (hφb : IsBoundedPotential φ) :
    relativeMongeAmpereEnergy θ φ u hφ hu =
      ⨅ j : ℕ, (relativeEnergyOfMinimalType θ φ (truncation φ u j) hφ.plurisubharmonic
        (isThetaPshPotential_truncation hφ.plurisubharmonic.1 hu.plurisubharmonic.1 hφb
          hu.le_reference j) : EReal) := by
  have htb := truncation_bounded hφb hu.le_reference
  have htp := isThetaPshPotential_truncation hφ.plurisubharmonic.1 hu.plurisubharmonic.1 hφb
    hu.le_reference
  refine le_antisymm (le_iInf fun j => ?_) (le_sInf ?_)
  · exact relativeMongeAmpereEnergy_le_of_majorant θ φ u _ hφ hu
      ⟨htp j, sameSingularityType_of_bounded (htb j) hφb⟩ (le_truncation φ u j)
  · rintro e ⟨v, hv, huv, rfl⟩
    have hvb := isBoundedPotential_of_sameSingularityType hφb hv.2
    -- a level at which the truncation lies below `v`
    obtain ⟨a, b, hab⟩ := hφb
    obtain ⟨a', b', hab'⟩ := hvb
    obtain ⟨N, hN⟩ := exists_nat_gt (b - a')
    have htv : truncation φ u N ≤ v := fun x => by
      refine max_le (huv x) ?_
      calc φ x - ((N : ℝ) : EReal) ≤ (b : EReal) - ((N : ℝ) : EReal) :=
            EReal.sub_le_sub (hab x).2 le_rfl
        _ = ((b - N : ℝ) : EReal) := by rw [EReal.coe_sub]
        _ ≤ a' := EReal.coe_le_coe_iff.mpr (by linarith)
        _ ≤ v x := (hab' x).1
    refine (iInf_le _ N).trans ?_
    exact EReal.coe_le_coe_iff.mpr (relativeEnergyOfMinimalType_mono omega θ
      hφ.plurisubharmonic (htp N) hv.1 ⟨a, b, hab⟩ (htb N) ⟨a', b', hab'⟩ htv)

/-- The energies of the truncations decrease to the extended energy. -/
theorem tendsto_relativeEnergyOfMinimalType_truncation (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u : M → EReal} (hφ : IsModelPotential θ φ)
    (hu : RelativePSH θ φ u) (hφb : IsBoundedPotential φ) :
    Tendsto (fun j : ℕ => (relativeEnergyOfMinimalType θ φ (truncation φ u j) hφ.plurisubharmonic
        (isThetaPshPotential_truncation hφ.plurisubharmonic.1 hu.plurisubharmonic.1 hφb
          hu.le_reference j) : EReal)) atTop
      (𝓝 (relativeMongeAmpereEnergy θ φ u hφ hu)) := by
  rw [relativeMongeAmpereEnergy_eq_iInf_truncation omega θ hφ hu hφb]
  refine tendsto_atTop_iInf fun i j hij => EReal.coe_le_coe_iff.mpr ?_
  exact relativeEnergyOfMinimalType_mono omega θ hφ.plurisubharmonic _ _ hφb
    (truncation_bounded hφb hu.le_reference j) (truncation_bounded hφb hu.le_reference i)
    fun x => truncation_antitone φ u x hij

/-- **Decreasing continuity of the extended energy** (Xia, SGPT Lemma 3.1.6, for a bounded model
potential). If relative potentials `u_k ∈ PSH(X, θ; φ)` decrease pointwise to `u ∈ PSH(X, θ; φ)`,
then their extended energies decrease to that of `u`. -/
theorem relativeMongeAmpereEnergy_tendsto_of_antitone (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u : M → EReal} (hφ : IsModelPotential θ φ)
    (hφb : IsBoundedPotential φ) (hu : RelativePSH θ φ u) {uk : ℕ → M → EReal}
    (huk : ∀ k, RelativePSH θ φ (uk k)) (hanti : ∀ x, Antitone fun k => uk k x)
    (hlim : ∀ x, Tendsto (fun k => uk k x) atTop (𝓝 (u x))) :
    Tendsto (fun k => relativeMongeAmpereEnergy θ φ (uk k) hφ (huk k)) atTop
      (𝓝 (relativeMongeAmpereEnergy θ φ u hφ hu)) := by
  have hle := le_of_antitone_of_tendsto hanti hlim
  have hmono : Antitone fun k => relativeMongeAmpereEnergy θ φ (uk k) hφ (huk k) :=
    fun i j hij => relativeMongeAmpereEnergy_mono θ hφ (huk j) (huk i) fun x => hanti x hij
  have hL := tendsto_atTop_iInf hmono
  suffices h : (⨅ k, relativeMongeAmpereEnergy θ φ (uk k) hφ (huk k)) =
      relativeMongeAmpereEnergy θ φ u hφ hu by rwa [h] at hL
  refine le_antisymm ?_ (le_iInf fun k => relativeMongeAmpereEnergy_mono θ hφ hu (huk k) (hle k))
  -- compare with every truncation of `u`
  rw [relativeMongeAmpereEnergy_eq_iInf_truncation omega θ hφ hu hφb]
  refine le_iInf fun j => ?_
  have hφp := hφ.plurisubharmonic
  have htp : ∀ k, IsThetaPshPotential θ.val (truncation φ (uk k) j) := fun k =>
    isThetaPshPotential_truncation hφp.1 (huk k).plurisubharmonic.1 hφb (huk k).le_reference j
  have htb : ∀ k, IsBoundedPotential (truncation φ (uk k) j) := fun k =>
    truncation_bounded hφb (huk k).le_reference j
  -- the bounded truncations decrease in `k`
  have hconv := relativeEnergyOfMinimalType_tendsto_of_antitone omega θ hφp hφb
    (isThetaPshPotential_truncation hφp.1 hu.plurisubharmonic.1 hφb hu.le_reference j)
    (truncation_bounded hφb hu.le_reference j) htp htb
    (fun x i i' hii' => max_le_max (hanti x hii') le_rfl)
    (fun x => (hlim x).max tendsto_const_nhds)
  have hconv' := (continuous_coe_real_ereal.tendsto _).comp hconv
  refine ge_of_tendsto' hconv' fun k => ?_
  refine (iInf_le _ k).trans ?_
  rw [relativeMongeAmpereEnergy_eq_iInf_truncation omega θ hφ (huk k) hφb]
  exact iInf_le _ j

end Extended

end

end SGPT.Foundations.Analysis.Pending.MongeAmpereEnergyDecreasing
