import SGPT.Foundations.Analysis.Pending.MongeAmpereEnergyDecreasing
import SGPT.Foundations.Analysis.Pending.GlobalMaxLocality

set_option autoImplicit false

/-!
# The finite-energy class for a bounded model potential

Let `(M, ω)` be a compact Kähler manifold, `θ` a smooth closed real `(1,1)`-form and `φ` a
**bounded** model potential (for instance `θ` Kähler and `φ = V_θ = 0`). For
`u ∈ PSH(X, θ; φ)` write `u_j = max(u, φ - j)` for its bounded truncations
(`MongeAmpereEnergyDecreasing.truncation`) and `E` for Xia's extended energy (3.30).

* **Finite energy forces full mass** (`relativeFullMass_of_bot_lt_energy`): if `E(u) > -∞`, then
  `∫ θ_u^n = ∫ θ_φ^n`, that is `u ∈ E(X, θ; φ)`.
* **Energy characterization of `E^1`** (`relativeFiniteEnergy_iff_bot_lt_energy`):
  `u ∈ E^1(X, θ; φ)` if and only if `E(u) > -∞` (Xia, SGPT, the characterization of the
  finite-energy class, for a bounded model potential).

## The proof

On the plurifine open set `{u > φ - j}` the truncation `u_j` agrees with `u`, and so do the
measures `θ_{u_j}^n` and `θ_u^n` (`GlobalMaxLocality`). The bounded `u_j` has the full mass
`∫ θ_φ^n` (one-slot mass invariance), and by Xia (3.33) and the shape of the energy sum

  `∫ (u_j - φ) θ_{u_j}^n ≤ E(u_j) ≤ (1/(n+1)) ∫ (u_j - φ) θ_{u_j}^n`.

* If `E(u) > -∞`: `j θ_{u_j}^n {u ≤ φ - j} ≤ ∫ (φ - u_j) θ_{u_j}^n ≤ -(n+1) E(u)`, so
  `θ_u^n {u > φ - j} = ∫ θ_φ^n - θ_{u_j}^n {u ≤ φ - j} → ∫ θ_φ^n`; and
  `∫_{u > φ - j} (φ - u) θ_u^n ≤ ∫ (φ - u_j) θ_{u_j}^n ≤ -(n + 1) E(u)`, so the energy integral is
  finite (the poles carry no mass and the sets `{u > φ - j}` exhaust their complement).
* If `u` has full mass and `∫ (φ - u) θ_u^n < ∞`: `θ_{u_j}^n {u ≤ φ - j} = θ_u^n {u ≤ φ - j}`, so
  `∫ (φ - u_j) θ_{u_j}^n ≤ ∫ (φ - u) θ_u^n` (on `{u ≤ φ - j}`, `φ - u_j = j ≤ φ - u`), hence
  `E(u) = inf_j E(u_j) ≥ -∫ (φ - u) θ_u^n`.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.FiniteEnergyCharacterization

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar BoundedGlobalProduct
open RelativeEnergy BoundedMongeAmpereEnergy MongeAmpereEnergyDecreasing DiagonalMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-! ### Energy bounds for bounded potentials below the reference -/

/-- `∫ (w - φ) θ_w^n ≤ E^φ(w)` for bounded `θ`-PSH `w` and `φ`. -/
theorem integral_le_energy (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {φ w : M → EReal} (hφ : IsThetaPshPotential θ.val φ) (hw : IsThetaPshPotential θ.val w)
    (hφb : IsBoundedPotential φ) (hwb : IsBoundedPotential w) :
    ∫ x, ((w x).toReal - (φ x).toReal) ∂(diagonalPotentialMeasure θ w hw) ≤
      relativeEnergyOfMinimalType θ φ w hφ hw := by
  have h := (integral_le_relativeEnergyOfMinimalType_sub_le omega θ hφ hw hφ hφb hwb hφb).1
  rw [relativeEnergyOfMinimalType_self, sub_zero] at h
  exact h

/-- `(n + 1) E^φ(w) ≤ ∫ (w - φ) θ_w^n` for bounded `θ`-PSH `w ≤ φ`: every term of the energy sum
is nonpositive. -/
theorem energy_mul_le_integral (θ : ClosedRealOneOneForm n M) {φ w : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hw : IsThetaPshPotential θ.val w)
    (hφb : IsBoundedPotential φ) (hwb : IsBoundedPotential w) (hwφ : w ≤ φ) :
    ((n : ℝ) + 1) * relativeEnergyOfMinimalType θ φ w hφ hw ≤
      ∫ x, ((w x).toReal - (φ x).toReal) ∂(diagonalPotentialMeasure θ w hw) := by
  rw [relativeEnergyOfMinimalType_mul θ hφ hw hφb hwb, Finset.sum_range_succ]
  have hnp : ∀ j ∈ Finset.range n, ∫ x, ((w x).toReal - (φ x).toReal) ∂(layMeasure θ n j w φ
      (fun _ => φ) hw.1 hφ.1 (fun _ => hφ.1)) ≤ 0 := fun j _ =>
    integral_nonpos fun x => sub_nonpos.mpr
      (EReal.toReal_le_toReal (hwφ x) (hwb.ne_bot x) (hφb.ne_top x))
  have hlast : layMeasure θ n n w φ (fun _ => φ) hw.1 hφ.1 (fun _ => hφ.1) =
      diagonalPotentialMeasure θ w hw :=
    BoundedIntegrationByParts.globalMixedMeasure_congr' rfl
      (by funext i; simp [lay, i.isLt]) _ _
  rw [hlast]
  linarith [Finset.sum_nonpos hnp]

/-! ### Truncations and their measures -/

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem truncation_le {φ u : M → EReal} (huφ : u ≤ φ) (j : ℕ) : truncation φ u j ≤ φ := by
  intro x
  refine max_le (huφ x) ?_
  have hj : (0 : EReal) ≤ ((j : ℝ) : EReal) := EReal.coe_nonneg.mpr (Nat.cast_nonneg j)
  calc φ x - ((j : ℝ) : EReal) ≤ φ x - 0 := EReal.sub_le_sub le_rfl hj
    _ = φ x := sub_zero _

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem truncation_eq_of_lt {φ u : M → EReal} {j : ℕ} {x : M}
    (hx : φ x - ((j : ℝ) : EReal) < u x) : truncation φ u j x = u x :=
  max_eq_left hx.le

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem truncation_eq_of_le {φ u : M → EReal} {j : ℕ} {x : M}
    (hx : u x ≤ φ x - ((j : ℝ) : EReal)) : truncation φ u j x = φ x - ((j : ℝ) : EReal) :=
  max_eq_right hx

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Off `{u > φ - j}`, `φ - u_j = j`. -/
theorem toReal_sub_truncation_of_le {φ u : M → EReal} (hφb : IsBoundedPotential φ) {j : ℕ}
    {x : M} (hx : u x ≤ φ x - ((j : ℝ) : EReal)) :
    (φ x).toReal - (truncation φ u j x).toReal = j := by
  rw [truncation_eq_of_le hx, ← EReal.coe_toReal (hφb.ne_top x) (hφb.ne_bot x), ← EReal.coe_sub,
    EReal.toReal_coe, EReal.toReal_coe]
  ring

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- In dimension zero a `θ`-PSH potential has no pole (points are open). The same statement is
`FiniteGeodesicsFullMassAnyDim.ne_bot_of_dim_zero`; it is repeated here to keep the import
closure small. -/
theorem ne_bot_of_dim_zero {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel 0) M] [IsComplexManifold 0 M] {θ : SmoothRealForm 0 M 2}
    {f : M → EReal} (hf : IsThetaPshPotential θ f) (x : M) : f x ≠ ⊥ := by
  have hopen : IsOpen ({x} : Set M) := by
    let e := chartAt (ComplexModel 0) x
    have hsrc : e.source = {x} := by
      ext y
      constructor
      · intro hy
        exact e.injOn hy (mem_chart_source _ x) (Subsingleton.elim _ _)
      · rintro rfl
        exact mem_chart_source _ y
    rw [← hsrc]
    exact e.open_source
  obtain ⟨y, hy, hfy⟩ := hf.2 x {x} hopen (mem_singleton x)
  rw [mem_singleton_iff] at hy
  rwa [hy] at hfy

/-- The pole set of a `θ`-PSH potential is null for its diagonal measure, in every dimension. -/
theorem diagonalPotentialMeasure_pole_null (θ : ClosedRealOneOneForm n M) {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) : diagonalPotentialMeasure θ u hu {x | u x = ⊥} = 0 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    have : {x | u x = ⊥} = (∅ : Set M) :=
      eq_empty_iff_forall_notMem.mpr fun x hx => ne_bot_of_dim_zero hu x hx
    rw [this, measure_empty]
  · exact GlobalSlotComparison.globalMixedMeasure_pole_null (fun _ => hu.1) ⟨0, h⟩

/-- **Plurifine locality of the truncation**: on `{u > φ - j}` the diagonal measures of `u_j`
and `u` agree. -/
theorem diagonalPotentialMeasure_truncation_restrict (θ : ClosedRealOneOneForm n M)
    {φ u : M → EReal} (hφ : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u)
    (j : ℕ) (htj : IsThetaPshPotential θ.val (truncation φ u j)) :
    (diagonalPotentialMeasure θ (truncation φ u j) htj).restrict
        {x | φ x - ((j : ℝ) : EReal) < u x} =
      (diagonalPotentialMeasure θ u hu).restrict {x | φ x - ((j : ℝ) : EReal) < u x} := by
  have hw : ∀ _i : Fin n, ThetaPlurisubharmonic θ.val fun x => φ x - ((j : ℝ) : EReal) :=
    fun _ => GlobalPotentialTransforms.thetaPlurisubharmonic_sub_const hφ.1 (j : ℝ)
  have hmax : ∀ _i : Fin n, ThetaPlurisubharmonic θ.val
      fun x => max (u x) (φ x - ((j : ℝ) : EReal)) := fun _ => htj.1
  have h := GlobalMaxLocality.globalMixedMeasure_restrict_max_eq (θ := fun _ => θ)
    (u := fun _ => u) (w := fun _ => fun x => φ x - ((j : ℝ) : EReal)) (fun _ => hu.1) hw hmax
  have hsub : {x | φ x - ((j : ℝ) : EReal) < u x} ⊆
      {x | ∀ _i : Fin n, φ x - ((j : ℝ) : EReal) < u x} := fun x hx _ => hx
  have e : diagonalPotentialMeasure θ (truncation φ u j) htj =
      globalMixedMeasure (fun _ => θ) (fun _ x => max (u x) (φ x - ((j : ℝ) : EReal))) hmax :=
    BoundedIntegrationByParts.globalMixedMeasure_congr' rfl rfl _ _
  rw [e, ← Measure.restrict_restrict_of_subset hsub, h, Measure.restrict_restrict_of_subset hsub]
  rfl

/-- A bounded truncation has the mass of the bounded reference. -/
theorem diagonalPotentialMeasure_truncation_univ (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u : M → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hφb : IsBoundedPotential φ) (huφ : u ≤ φ) (j : ℕ)
    (htj : IsThetaPshPotential θ.val (truncation φ u j)) :
    diagonalPotentialMeasure θ (truncation φ u j) htj univ = diagonalPotentialMass θ φ hφ :=
  UniformBoundedGlobalMass.globalMixedMeasure_univ_eq_of_bounded
    (GlobalNonPluripolar.oneSlotMassInvariance omega (fun _ => θ)) (fun _ => htj.1)
    (fun _ => hφ.1) (fun _ => truncation_bounded hφb huφ j) (fun _ => hφb)

omit [CompactSpace M] in
theorem measurableSet_lt_truncation {θ : SmoothRealForm n M 2} {φ u : M → EReal}
    (hφ : ThetaPlurisubharmonic θ φ) (hu : ThetaPlurisubharmonic θ u) (j : ℕ) :
    MeasurableSet {x | φ x - ((j : ℝ) : EReal) < u x} :=
  measurableSet_lt ((GlobalSlotComparison.ThetaPlurisubharmonic.measurable hφ).sub_const _)
    (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hu)

/-! ### Finite energy forces full mass -/

section Main

variable (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) {φ u : M → EReal}
  (hφ : IsModelPotential θ φ) (hφb : IsBoundedPotential φ) (hu : RelativePSH θ φ u)

omit [BorelSpace M] in
/-- The extended energy of a relative potential is at most `0` (`φ` is a majorant). -/
theorem relativeMongeAmpereEnergy_le_zero :
    relativeMongeAmpereEnergy θ φ u hφ hu ≤ 0 := by
  have h := relativeMongeAmpereEnergy_le_of_majorant θ φ u φ hφ hu
    ⟨hφ.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩ hu.le_reference
  rwa [relativeEnergyOfMinimalType_self] at h

include omega hφb in
/-- **Finite energy forces full mass** (bounded model potential): if `E(u) > -∞`, then the
mass of `θ_u^n` is that of `θ_φ^n`, and the truncations satisfy
`j θ_{u_j}^n {u ≤ φ - j} ≤ -(n + 1) E(u)`. -/
theorem relativeFullMass_of_bot_lt_energy (hE : ⊥ < relativeMongeAmpereEnergy θ φ u hφ hu) :
    RelativeFullMass θ φ u hφ := by
  classical
  have hφp := hφ.plurisubharmonic
  have hE0 := relativeMongeAmpereEnergy_le_zero θ hφ hu
  set e : ℝ := (relativeMongeAmpereEnergy θ φ u hφ hu).toReal with he_def
  have he : relativeMongeAmpereEnergy θ φ u hφ hu = (e : EReal) :=
    (EReal.coe_toReal (ne_top_of_le_ne_top EReal.zero_ne_top hE0) hE.ne').symm
  have htp : ∀ j, IsThetaPshPotential θ.val (truncation φ u j) := fun j =>
    isThetaPshPotential_truncation hφp.1 hu.1.1 hφb hu.2 j
  have htb : ∀ j, IsBoundedPotential (truncation φ u j) := fun j =>
    truncation_bounded hφb hu.2 j
  set μ := diagonalPotentialMeasure θ u hu.1 with hμ
  have hμfin : IsFiniteMeasure μ :=
    GlobalNonPluripolar.globalMixedMeasure_isFiniteMeasure omega _
  set μj : ℕ → Measure M := fun j => diagonalPotentialMeasure θ (truncation φ u j) (htp j)
    with hμj
  have hμjfin : ∀ j, IsFiniteMeasure (μj j) := fun j =>
    globalMixedMeasure_isFiniteMeasure_of_bounded _ fun _ => htb j
  set A : ℕ → Set M := fun j => {x | φ x - ((j : ℝ) : EReal) < u x} with hA
  have hAm : ∀ j, MeasurableSet (A j) := fun j => measurableSet_lt_truncation hφp.1 hu.1.1 j
  set Mφ := diagonalPotentialMass θ φ hφp with hMφ
  have hMφfin : Mφ ≠ ⊤ := (GlobalNonPluripolar.globalMixedMeasure_apply_lt_top omega _ _).ne
  -- the energy bound on the complement of `A j`
  have hK : ∀ j : ℕ, (j : ℝ) * (μj j).real (A j)ᶜ ≤ -(((n : ℝ) + 1) * e) := by
    intro j
    have h1 : e ≤ relativeEnergyOfMinimalType θ φ (truncation φ u j) hφp (htp j) := by
      have := relativeMongeAmpereEnergy_le_of_majorant θ φ u _ hφ hu
        ⟨htp j, sameSingularityType_of_bounded (htb j) hφb⟩ (le_truncation φ u j)
      rw [he] at this
      exact EReal.coe_le_coe_iff.mp this
    have h2 := energy_mul_le_integral θ hφp (htp j) hφb (htb j) (truncation_le hu.2 j)
    -- the integral is at most its part on `(A j)ᶜ`
    have hint : Integrable (fun x => (truncation φ u j x).toReal - (φ x).toReal) (μj j) := by
      obtain ⟨Q1, hQ1⟩ := GlobalSlotStokes.IsBoundedPotential.exists_abs_toReal_le (htb j)
      obtain ⟨Q2, hQ2⟩ := GlobalSlotStokes.IsBoundedPotential.exists_abs_toReal_le hφb
      exact GlobalSlotStokes.integrable_of_measurable_bounded
        ((GlobalSlotStokes.ThetaPlurisubharmonic.measurable_toReal (htp j).1).sub
          (GlobalSlotStokes.ThetaPlurisubharmonic.measurable_toReal hφp.1))
        (fun x => (abs_sub _ _).trans (add_le_add (hQ1 x) (hQ2 x))) _
    have hsplit := integral_add_compl (hAm j) hint
    have hnonpos : ∫ x in A j, ((truncation φ u j x).toReal - (φ x).toReal) ∂(μj j) ≤ 0 :=
      setIntegral_nonpos (hAm j) fun x _ => sub_nonpos.mpr (EReal.toReal_le_toReal
        (truncation_le hu.2 j x) ((htb j).ne_bot x) (hφb.ne_top x))
    have hcompl : ∫ x in (A j)ᶜ, ((truncation φ u j x).toReal - (φ x).toReal) ∂(μj j) =
        -(j : ℝ) * (μj j).real (A j)ᶜ := by
      rw [setIntegral_congr_fun (hAm j).compl (g := fun _ => -(j : ℝ)) fun x hx => by
        have hx' : u x ≤ φ x - ((j : ℝ) : EReal) := not_lt.mp hx
        have := toReal_sub_truncation_of_le (u := u) hφb hx'
        simp only
        linarith]
      rw [setIntegral_const, smul_eq_mul, mul_comm]
    have hmul : ((n : ℝ) + 1) * e ≤ ((n : ℝ) + 1) *
        relativeEnergyOfMinimalType θ φ (truncation φ u j) hφp (htp j) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    simp only [hμj] at hsplit hnonpos hcompl
    linarith
  -- the masses of `θ_u^n` on `A j`
  have hloc : ∀ j, μ (A j) = μj j (A j) := by
    intro j
    have h := diagonalPotentialMeasure_truncation_restrict θ hφp hu.1 j (htp j)
    rw [← Measure.restrict_apply_self, ← Measure.restrict_apply_self (μj j)]
    simp only [hμj, hμ, hA, h]
  have huniv : ∀ j, μj j univ = Mφ := fun j =>
    diagonalPotentialMeasure_truncation_univ omega θ hφp hφb hu.2 j (htp j)
  have hAmass : ∀ j, μ.real (A j) = Mφ.toReal - (μj j).real (A j)ᶜ := by
    intro j
    have h3 := measureReal_add_measureReal_compl (μ := μj j) (hAm j)
    have h4 : (μj j).real univ = Mφ.toReal := by simp only [Measure.real, huniv j]
    have h5 : μ.real (A j) = (μj j).real (A j) := by simp only [Measure.real, hloc j]
    linarith
  -- `μ univ` is the supremum of `μ (A j)`
  have hAmono : Monotone A := fun i j hij x (hx : φ x - ((i : ℝ) : EReal) < u x) =>
    lt_of_le_of_lt (EReal.sub_le_sub le_rfl
      (EReal.coe_le_coe_iff.mpr (Nat.cast_le.mpr hij))) hx
  have hcover : univ ⊆ (⋃ j, A j) ∪ {x | u x = ⊥} := by
    intro x _
    by_cases hx : u x = ⊥
    · exact Or.inr hx
    · left
      obtain ⟨a, b, hab⟩ := hφb
      have htop : u x ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top b) ((hu.2 x).trans (hab x).2)
      obtain ⟨r, hr⟩ : ∃ r : ℝ, u x = r := ⟨(u x).toReal, (EReal.coe_toReal htop hx).symm⟩
      obtain ⟨N, hN⟩ := exists_nat_gt (b - r)
      refine mem_iUnion.mpr ⟨N, ?_⟩
      show φ x - ((N : ℝ) : EReal) < u x
      calc φ x - ((N : ℝ) : EReal) ≤ (b : EReal) - ((N : ℝ) : EReal) :=
            EReal.sub_le_sub (hab x).2 le_rfl
        _ = ((b - N : ℝ) : EReal) := by rw [EReal.coe_sub]
        _ < u x := by rw [hr]; exact EReal.coe_lt_coe_iff.mpr (by linarith)
  have hsup : μ univ = ⨆ j, μ (A j) := by
    refine le_antisymm ?_ (iSup_le fun j => measure_mono (subset_univ _))
    calc μ univ ≤ μ ((⋃ j, A j) ∪ {x | u x = ⊥}) := measure_mono hcover
      _ ≤ μ (⋃ j, A j) + μ {x | u x = ⊥} := measure_union_le _ _
      _ = ⨆ j, μ (A j) := by
          rw [show μ {x | u x = ⊥} = 0 from diagonalPotentialMeasure_pole_null θ hu.1, add_zero,
            hAmono.measure_iUnion]
  -- the upper bound
  have hle : μ univ ≤ Mφ := by
    rw [hsup]
    exact iSup_le fun j => by
      rw [hloc j, ← huniv j]
      exact measure_mono (subset_univ _)
  -- the lower bound
  set K : ℝ := -(((n : ℝ) + 1) * e) with hK_def
  have hge : Mφ.toReal ≤ μ.real univ := by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨N, hN⟩ := exists_nat_gt (K / ε)
    have hKnn : 0 ≤ K := by
      have : e ≤ 0 := by
        have := hE0
        rw [he] at this
        exact EReal.coe_nonpos.mp this
      simp only [hK_def]
      nlinarith
    have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg hKnn hε.le) hN
    have h1 := hK N
    have hcompl : (μj N).real (A N)ᶜ < ε := by
      have hm : (μj N).real (A N)ᶜ ≤ K / N := by
        rw [le_div_iff₀ hNpos]; linarith
      have : K / N < ε := by
        rw [div_lt_iff₀ hNpos]
        rw [div_lt_iff₀ hε] at hN
        linarith
      linarith
    have h2 : μ.real (A N) ≤ μ.real univ := measureReal_mono (subset_univ _)
    have h3 := hAmass N
    linarith
  refine ⟨hu.1, hu.2, ?_⟩
  refine le_antisymm hle ?_
  exact (ENNReal.toReal_le_toReal hMφfin (measure_ne_top _ _)).mp hge


/-! ### The energy characterization of `E^1` -/

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- On `{u > φ - j}` the canonical difference `|φ - u|` is `φ - u_j`. -/
theorem canonicalERealAbsDiff_eq_of_lt {φ u : M → EReal} (hφb : IsBoundedPotential φ)
    (huφ : u ≤ φ) {j : ℕ} {x : M} (hx : φ x - ((j : ℝ) : EReal) < u x) :
    canonicalERealAbsDiff (φ x) (u x) =
      ENNReal.ofReal ((φ x).toReal - (truncation φ u j x).toReal) := by
  rw [truncation_eq_of_lt hx]
  have hbot : u x ≠ ⊥ := ne_bot_of_gt hx
  have htop : u x ≠ ⊤ := ne_top_of_le_ne_top (hφb.ne_top x) (huφ x)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, u x = r := ⟨(u x).toReal, (EReal.coe_toReal htop hbot).symm⟩
  obtain ⟨p, hp⟩ : ∃ p : ℝ, φ x = p :=
    ⟨(φ x).toReal, (EReal.coe_toReal (hφb.ne_top x) (hφb.ne_bot x)).symm⟩
  have hrp : r ≤ p := by have := huφ x; rw [hr, hp] at this; exact EReal.coe_le_coe_iff.mp this
  rw [hr, hp, canonicalERealAbsDiff_coe_coe, EReal.toReal_coe, EReal.toReal_coe,
    abs_of_nonneg (sub_nonneg.mpr hrp)]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Off `{u > φ - j}`, `|φ - u| ≥ j`, also at the poles of `u`. -/
theorem ofReal_le_canonicalERealAbsDiff_of_le {φ u : M → EReal} (hφb : IsBoundedPotential φ)
    {j : ℕ} {x : M} (hx : u x ≤ φ x - ((j : ℝ) : EReal)) :
    ENNReal.ofReal j ≤ canonicalERealAbsDiff (φ x) (u x) := by
  obtain ⟨p, hp⟩ : ∃ p : ℝ, φ x = p :=
    ⟨(φ x).toReal, (EReal.coe_toReal (hφb.ne_top x) (hφb.ne_bot x)).symm⟩
  by_cases hbot : u x = ⊥
  · have : canonicalERealAbsDiff (φ x) (u x) = ⊤ := by
      rw [hbot, hp]
      simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff]
    rw [this]
    exact le_top
  · have htop : u x ≠ ⊤ := by
      intro h
      rw [h, hp, ← EReal.coe_sub] at hx
      exact absurd hx (not_le.mpr (EReal.coe_lt_top _))
    obtain ⟨r, hr⟩ : ∃ r : ℝ, u x = r := ⟨(u x).toReal, (EReal.coe_toReal htop hbot).symm⟩
    rw [hr, hp, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hx
    rw [hr, hp, canonicalERealAbsDiff_coe_coe]
    exact ENNReal.ofReal_le_ofReal (by rw [abs_of_nonneg (by linarith)]; linarith)

include omega hφb in
/-- **The energy characterization of the finite-energy class** (bounded model potential):
`u ∈ E^1(X, θ; φ)` if and only if `E(u) > -∞`. -/
theorem relativeFiniteEnergy_iff_bot_lt_energy :
    RelativeFiniteEnergy θ φ u hφ ↔ ⊥ < relativeMongeAmpereEnergy θ φ u hφ hu := by
  classical
  have hφp := hφ.plurisubharmonic
  have htp : ∀ j, IsThetaPshPotential θ.val (truncation φ u j) := fun j =>
    isThetaPshPotential_truncation hφp.1 hu.1.1 hφb hu.2 j
  have htb : ∀ j, IsBoundedPotential (truncation φ u j) := fun j =>
    truncation_bounded hφb hu.2 j
  set μ := diagonalPotentialMeasure θ u hu.1 with hμ
  have hμfin : IsFiniteMeasure μ :=
    GlobalNonPluripolar.globalMixedMeasure_isFiniteMeasure omega _
  set μj : ℕ → Measure M := fun j => diagonalPotentialMeasure θ (truncation φ u j) (htp j)
    with hμj
  have hμjfin : ∀ j, IsFiniteMeasure (μj j) := fun j =>
    globalMixedMeasure_isFiniteMeasure_of_bounded _ fun _ => htb j
  set A : ℕ → Set M := fun j => {x | φ x - ((j : ℝ) : EReal) < u x} with hA
  have hAm : ∀ j, MeasurableSet (A j) := fun j => measurableSet_lt_truncation hφp.1 hu.1.1 j
  have hrestr : ∀ j, μ.restrict (A j) = (μj j).restrict (A j) := fun j =>
    (diagonalPotentialMeasure_truncation_restrict θ hφp hu.1 j (htp j)).symm
  set f : M → ℝ≥0∞ := fun x => canonicalERealAbsDiff (φ x) (u x) with hf
  set g : ℕ → M → ℝ := fun j x => (φ x).toReal - (truncation φ u j x).toReal with hg
  have hgnn : ∀ j x, 0 ≤ g j x := fun j x => sub_nonneg.mpr (EReal.toReal_le_toReal
    (truncation_le hu.2 j x) ((htb j).ne_bot x) (hφb.ne_top x))
  have hgint : ∀ j, Integrable (g j) (μj j) := fun j => by
    obtain ⟨Q1, hQ1⟩ := GlobalSlotStokes.IsBoundedPotential.exists_abs_toReal_le (htb j)
    obtain ⟨Q2, hQ2⟩ := GlobalSlotStokes.IsBoundedPotential.exists_abs_toReal_le hφb
    exact GlobalSlotStokes.integrable_of_measurable_bounded
      ((GlobalSlotStokes.ThetaPlurisubharmonic.measurable_toReal hφp.1).sub
        (GlobalSlotStokes.ThetaPlurisubharmonic.measurable_toReal (htp j).1))
      (fun x => (abs_sub _ _).trans (add_le_add (hQ2 x) (hQ1 x))) _
  -- `∫ (φ - u_j) θ_{u_j}^n` as a lower integral
  have hofReal : ∀ j, ENNReal.ofReal (∫ x, g j x ∂(μj j)) = ∫⁻ x, ENNReal.ofReal (g j x) ∂(μj j) :=
    fun j => ofReal_integral_eq_lintegral_ofReal (hgint j) (Eventually.of_forall (hgnn j))
  -- the energy bound `E(u_j) ≥ -∫ (φ - u_j) θ_{u_j}^n`
  have hEj : ∀ j, -(∫ x, g j x ∂(μj j)) ≤
      relativeEnergyOfMinimalType θ φ (truncation φ u j) hφp (htp j) := by
    intro j
    have h := integral_le_energy omega θ hφp (htp j) hφb (htb j)
    have e : ∫ x, ((truncation φ u j x).toReal - (φ x).toReal) ∂(μj j) =
        -∫ x, g j x ∂(μj j) := by
      rw [← integral_neg]; congr 1; funext x; simp only [hg]; ring
    simp only [hμj] at e
    linarith
  -- on `A j` the integrands agree
  have hfA : ∀ j, ∫⁻ x in A j, f x ∂μ = ∫⁻ x in A j, ENNReal.ofReal (g j x) ∂(μj j) := by
    intro j
    rw [hrestr j]
    exact setLIntegral_congr_fun (hAm j) fun x hx =>
      canonicalERealAbsDiff_eq_of_lt hφb hu.2 hx
  constructor
  · -- finite energy ⇒ `E(u) > -∞`
    rintro ⟨hfull, hη, hI⟩
    rw [relativeFiniteEnergyIntegral_proof_independent θ φ u hη hu.1] at hI
    set I := relativeFiniteEnergyIntegral θ φ u hu.1 with hIdef
    have hIf : I = ∫⁻ x, f x ∂μ := rfl
    obtain ⟨hη', -, hmass⟩ := hfull
    have hmass' : μ univ = diagonalPotentialMass θ φ hφp := by
      rw [← hmass]; exact congrArg (fun ν : Measure M => ν univ)
        (diagonalPotentialMeasure_proof_independent hu.1 hη')
    have hbound : ∀ j, ∫ x, g j x ∂(μj j) ≤ I.toReal := by
      intro j
      have hcompl : μj j (A j)ᶜ = μ (A j)ᶜ := by
        have h1 : μ (A j) = μj j (A j) := by
          rw [← Measure.restrict_apply_self, ← Measure.restrict_apply_self (μj j), hrestr j]
        rw [measure_compl (hAm j) (measure_ne_top _ _), measure_compl (hAm j) (measure_ne_top _ _),
          h1, hmass', diagonalPotentialMeasure_truncation_univ omega θ hφp hφb hu.2 j (htp j)]
      have hlin : ∫⁻ x, ENNReal.ofReal (g j x) ∂(μj j) ≤ I := by
        rw [← lintegral_add_compl (μ := μj j) _ (hAm j), hIf,
          ← lintegral_add_compl (μ := μ) f (hAm j), ← hfA j]
        refine add_le_add le_rfl ?_
        calc ∫⁻ x in (A j)ᶜ, ENNReal.ofReal (g j x) ∂(μj j)
            = ∫⁻ x in (A j)ᶜ, ENNReal.ofReal (j : ℝ) ∂(μj j) :=
              setLIntegral_congr_fun (hAm j).compl fun x hx => by
                simp only [hg]
                rw [toReal_sub_truncation_of_le hφb (not_lt.mp hx)]
          _ = ENNReal.ofReal (j : ℝ) * μj j (A j)ᶜ := by rw [setLIntegral_const]
          _ = ENNReal.ofReal (j : ℝ) * μ (A j)ᶜ := by rw [hcompl]
          _ = ∫⁻ x in (A j)ᶜ, ENNReal.ofReal (j : ℝ) ∂μ := by rw [setLIntegral_const]
          _ ≤ ∫⁻ x in (A j)ᶜ, f x ∂μ :=
              setLIntegral_mono' (hAm j).compl fun x hx =>
                ofReal_le_canonicalERealAbsDiff_of_le hφb (not_lt.mp hx)
      have := (ENNReal.ofReal_le_iff_le_toReal hI.ne).mp ((hofReal j).le.trans hlin)
      exact this
    rw [relativeMongeAmpereEnergy_eq_iInf_truncation omega θ hφ hu hφb]
    refine lt_of_lt_of_le (EReal.bot_lt_coe (-I.toReal)) (le_iInf fun j => ?_)
    exact EReal.coe_le_coe_iff.mpr (by linarith [hEj j, hbound j])
  · -- `E(u) > -∞` ⇒ finite energy
    intro hE
    refine ⟨relativeFullMass_of_bot_lt_energy omega θ hφ hφb hu hE, hu.1, ?_⟩
    have hE0 := relativeMongeAmpereEnergy_le_zero θ hφ hu
    set e : ℝ := (relativeMongeAmpereEnergy θ φ u hφ hu).toReal with he_def
    have he : relativeMongeAmpereEnergy θ φ u hφ hu = (e : EReal) :=
      (EReal.coe_toReal (ne_top_of_le_ne_top EReal.zero_ne_top hE0) hE.ne').symm
    have h1 : ∀ j, e ≤ relativeEnergyOfMinimalType θ φ (truncation φ u j) hφp (htp j) := by
      intro j
      have := relativeMongeAmpereEnergy_le_of_majorant θ φ u _ hφ hu
        ⟨htp j, sameSingularityType_of_bounded (htb j) hφb⟩ (le_truncation φ u j)
      rw [he] at this
      exact EReal.coe_le_coe_iff.mp this
    -- the pieces on `A j` are bounded by `-(n + 1) e`
    have hupper : ∀ j, ∫ x, g j x ∂(μj j) ≤ -(((n : ℝ) + 1) * e) := by
      intro j
      have h2 := energy_mul_le_integral θ hφp (htp j) hφb (htb j) (truncation_le hu.2 j)
      have e2 : ∫ x, ((truncation φ u j x).toReal - (φ x).toReal) ∂(μj j) =
          -∫ x, g j x ∂(μj j) := by
        rw [← integral_neg]; congr 1; funext x; simp only [hg]; ring
      simp only [hμj] at e2
      have hmul : ((n : ℝ) + 1) * e ≤ ((n : ℝ) + 1) *
          relativeEnergyOfMinimalType θ φ (truncation φ u j) hφp (htp j) :=
        mul_le_mul_of_nonneg_left (h1 j) (by positivity)
      linarith
    have hpiece : ∀ j, ∫⁻ x in A j, f x ∂μ ≤ ENNReal.ofReal (-(((n : ℝ) + 1) * e)) := by
      intro j
      rw [hfA j]
      calc ∫⁻ x in A j, ENNReal.ofReal (g j x) ∂(μj j)
          ≤ ∫⁻ x, ENNReal.ofReal (g j x) ∂(μj j) := setLIntegral_le_lintegral _ _
        _ = ENNReal.ofReal (∫ x, g j x ∂(μj j)) := (hofReal j).symm
        _ ≤ ENNReal.ofReal (-(((n : ℝ) + 1) * e)) := ENNReal.ofReal_le_ofReal (hupper j)
    -- the pole set is null and the `A j` exhaust its complement
    have hAmono : Monotone A := fun i j hij x (hx : φ x - ((i : ℝ) : EReal) < u x) =>
      lt_of_le_of_lt (EReal.sub_le_sub le_rfl
        (EReal.coe_le_coe_iff.mpr (Nat.cast_le.mpr hij))) hx
    have hcover : univ ⊆ (⋃ j, A j) ∪ {x | u x = ⊥} := by
      intro x _
      by_cases hx : u x = ⊥
      · exact Or.inr hx
      · left
        obtain ⟨a, b, hab⟩ := hφb
        have htop : u x ≠ ⊤ :=
          ne_top_of_le_ne_top (EReal.coe_ne_top b) ((hu.2 x).trans (hab x).2)
        obtain ⟨r, hr⟩ : ∃ r : ℝ, u x = r := ⟨(u x).toReal, (EReal.coe_toReal htop hx).symm⟩
        obtain ⟨N, hN⟩ := exists_nat_gt (b - r)
        refine mem_iUnion.mpr ⟨N, ?_⟩
        show φ x - ((N : ℝ) : EReal) < u x
        calc φ x - ((N : ℝ) : EReal) ≤ (b : EReal) - ((N : ℝ) : EReal) :=
              EReal.sub_le_sub (hab x).2 le_rfl
          _ = ((b - N : ℝ) : EReal) := by rw [EReal.coe_sub]
          _ < u x := by rw [hr]; exact EReal.coe_lt_coe_iff.mpr (by linarith)
    have hpole : μ {x | u x = ⊥} = 0 := diagonalPotentialMeasure_pole_null θ hu.1
    have hI : ∫⁻ x, f x ∂μ ≤ ENNReal.ofReal (-(((n : ℝ) + 1) * e)) := by
      calc ∫⁻ x, f x ∂μ = ∫⁻ x in univ, f x ∂μ := (setLIntegral_univ _).symm
        _ ≤ ∫⁻ x in (⋃ j, A j) ∪ {x | u x = ⊥}, f x ∂μ := lintegral_mono_set hcover
        _ ≤ (∫⁻ x in ⋃ j, A j, f x ∂μ) + ∫⁻ x in {x | u x = ⊥}, f x ∂μ :=
            lintegral_union_le _ _ _
        _ = ⨆ j, ∫⁻ x in A j, f x ∂μ := by
            rw [setLIntegral_measure_zero _ _ hpole, add_zero,
              setLIntegral_iUnion_of_directed _ hAmono.directed_le]
        _ ≤ ENNReal.ofReal (-(((n : ℝ) + 1) * e)) := iSup_le hpiece
    exact lt_of_le_of_lt hI ENNReal.ofReal_lt_top


end Main

end

end SGPT.Foundations.Analysis.Pending.FiniteEnergyCharacterization
