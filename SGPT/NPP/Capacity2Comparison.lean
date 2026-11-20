import SGPT.NPP.CapacityModulus
import SGPT.Foundations.Analysis.Pending.ManifoldPluripolar

/-!
# Comparison of capacities of big classes

Source `thm:comp_capa` (chapter `chapter_npp.tex`, section `sec:qc`): for two closed smooth
real `(1,1)`-forms `θ, θ'` representing big classes on a compact Kähler manifold `X` there are
continuous `f, g : [0, ∞) → [0, ∞)` with `f 0 = g 0 = 0` and

  `Cap_θ(E) ≤ f(Cap_θ'(E))`,   `Cap_θ'(E) ≤ g(Cap_θ(E))`   for every Borel set `E`.

`SGPT.NPP.exists_source_capacity_control` (file `KahlerCapacityBigControl`) already gives
`Cap_ω ≤ ε + C_ε Cap_θ` for the Kähler capacity `Cap_ω` and big `θ`.  This file proves the
missing direction `Cap_θ ≤ ε + C_ε Cap_ω`, in which the minimal potential `V_θ` may be
unbounded below, and assembles the theorem.

Proof of the missing direction.
* **Tail.** Bigness gives `δ > 0` and a normalized `(θ - δω)`-psh `ρ ≤ 0`.  With `A > 0` such
  that `θ + Aω ≥ 0` and `t = δ/(A+δ)`, the function `(1-t)ρ` is `θ`-psh (because
  `θ - (1-t)(θ - δω) = t(θ + Aω) ≥ 0`), hence `(1-t)ρ ≤ V_θ`.  Therefore on `{V_θ < -B}` either
  `V_θ = -∞` (a pluripolar set, of capacity zero) or `ρ < V_θ - k` with `k = tB/(1-t)`.  The
  Guedj--Zeriahi sublevel estimate (`ThetaCapacitySublevel.tendsto_thetaCapacity_sublevel`)
  makes `Cap_θ({ρ < V_θ - k}) → 0`, so `Cap_θ({V_θ < -B}) → 0` as `B → ∞`.
* **Bulk.** On `{V_θ ≥ -B}` every competitor is bounded below by `-B-1`, and
  `ActualLocallyBoundedReferenceCapacity.exists_capacity_bound` gives `Cap_θ ≤ K_B Cap_ω` on
  subsets of that locus.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open ThetaCapacity
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- A strict reference scaled by `1 - t`, `t = δ/(A+δ)`, is `θ`-psh, hence lies below `V_θ`.
This is the inequality `ρ ≤ b V_θ` with `b = 1/(1-t) > 1`. -/
theorem exists_scaled_reference_le_minimal [Nonempty M] (ω : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ ∃ ρ : M → EReal,
      IsThetaPshPotential θ.val ρ ∧ ρ ≤ 0 ∧
      IsThetaPshPotential θ.val (thetaPshSupremum θ.val) ∧
      ρ ≤ thetaPshSupremum θ.val ∧
      ∀ x, ((1 - t : ℝ) : EReal) * ρ x ≤ thetaPshSupremum θ.val x := by
  obtain ⟨δ, hδ, ρ, hρ, hρ0, hρθ, hV, hρV⟩ := exists_normalized_strict_reference ω θ hbig
  obtain ⟨A, hA, hθA⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul ω θ
  set t : ℝ := δ / (A + δ) with ht_def
  have hAδ : 0 < A + δ := by linarith
  have ht0 : 0 < t := div_pos hδ hAδ
  have ht1 : t < 1 := by rw [ht_def, div_lt_one hAδ]; linarith
  have hc : 0 < 1 - t := by linarith
  refine ⟨t, ht0, ht1, ρ, hρθ, hρ0, hV, hρV, ?_⟩
  have hq : IsThetaPshPotential ((1 - t) • (θ - δ • ω.form)).val
      (fun x => ((1 - t : ℝ) : EReal) * ρ x) :=
    PotentialMassComparison.isThetaPshPotential_smul hρ hc
  have hσ : (t • (θ + A • ω.form)).val.IsSemipositive :=
    KahlerDomination.isSemipositive_smul hθA ht0.le
  have hscal : (1 - t) * δ = t * A := by
    rw [ht_def]; field_simp; ring
  have hform : (1 - t) • (θ - δ • ω.form) + t • (θ + A • ω.form) = θ := by
    rw [smul_sub, smul_add, smul_smul, smul_smul, hscal]
    module
  have hqθ : IsThetaPshPotential θ.val (fun x => ((1 - t : ℝ) : EReal) * ρ x) := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hq hσ
    rwa [hform] at h
  have hq0 : (fun x => ((1 - t : ℝ) : EReal) * ρ x) ≤ 0 := by
    intro x
    exact EReal.mul_nonpos_iff.mpr (Or.inl ⟨EReal.coe_nonneg.mpr hc.le, hρ0 x⟩)
  exact fun x => le_thetaPshSupremum hqθ hq0 x

/-- **Tail estimate.** For big `θ`, the capacity of the deep sublevel sets `{V_θ < -B}` of the
minimal potential tends to zero: for every `ε > 0` some `B ≥ 0` gives
`Cap_θ({V_θ < -B}) < ε`. -/
theorem exists_minimalEnvelope_tail_small [Nonempty M] (ω : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧
      thetaCapacityV θ {x | thetaPshSupremum θ.val x < ((-B : ℝ) : EReal)} <
        ENNReal.ofReal ε := by
  obtain ⟨t, ht0, ht1, ρ, hρθ, _hρ0, hV, hρV, hscaled⟩ :=
    exists_scaled_reference_le_minimal ω θ hbig
  set V := thetaPshSupremum θ.val with hV_def
  have hc : 0 < 1 - t := by linarith
  have hlim := ThetaCapacitySublevel.tendsto_thetaCapacity_sublevel ω hV hρθ hρV
  obtain ⟨k, hk⟩ := (hlim.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε))).exists
  set B : ℝ := (k : ℝ) * (1 - t) / t with hB_def
  have hB : 0 ≤ B := div_nonneg (mul_nonneg (Nat.cast_nonneg k) hc.le) ht0.le
  have hBt : B * t = (k : ℝ) * (1 - t) := by rw [hB_def]; field_simp
  refine ⟨B, hB, ?_⟩
  have hpole : thetaCapacity θ V {x | V x = ⊥} = 0 :=
    thetaCapacity_eq_zero_of_manifoldLocallyPluripolar V
      (quasiPsh_poles_manifoldLocallyPluripolar hV.quasiPshPotential)
  have hsub : {x | V x < ((-B : ℝ) : EReal)} ⊆
      {x | V x = ⊥} ∪ {x | ρ x < V x + ((-(k : ℝ) : ℝ) : EReal)} := by
    intro x hx
    change V x < ((-B : ℝ) : EReal) at hx
    by_cases hVb : V x = ⊥
    · exact Or.inl hVb
    right
    change ρ x < V x + ((-(k : ℝ) : ℝ) : EReal)
    obtain ⟨z, hz⟩ : ∃ z : ℝ, V x = (z : EReal) :=
      ⟨(V x).toReal, (EReal.coe_toReal (hV.1.quasiPlurisubharmonic.ne_top x) hVb).symm⟩
    have hzB : z < -B := by rw [hz] at hx; exact EReal.coe_lt_coe_iff.mp hx
    rw [hz, ← EReal.coe_add]
    by_cases hρb : ρ x = ⊥
    · rw [hρb]; exact bot_lt_iff_ne_bot.mpr (EReal.coe_ne_bot _)
    obtain ⟨r, hr⟩ : ∃ r : ℝ, ρ x = (r : EReal) :=
      ⟨(ρ x).toReal, (EReal.coe_toReal (hρθ.1.quasiPlurisubharmonic.ne_top x) hρb).symm⟩
    have hrz : (1 - t) * r ≤ z := by
      have h := hscaled x
      rw [hr, hz, ← EReal.coe_mul] at h
      exact EReal.coe_le_coe_iff.mp h
    rw [hr, EReal.coe_lt_coe_iff]
    -- `(1-t) r ≤ z = (1-t) z + t z < (1-t) z - (1-t) k`
    have htz : t * z < -(B * t) := by nlinarith
    rw [hBt] at htz
    have h1 : (1 - t) * r < (1 - t) * (z + -(k : ℝ)) := by nlinarith
    exact lt_of_mul_lt_mul_left h1 hc.le
  calc thetaCapacityV θ {x | V x < ((-B : ℝ) : EReal)}
      ≤ thetaCapacity θ V ({x | V x = ⊥} ∪ {x | ρ x < V x + ((-(k : ℝ) : ℝ) : EReal)}) :=
        thetaCapacity_mono hsub
    _ ≤ thetaCapacity θ V {x | V x = ⊥} +
          thetaCapacity θ V {x | ρ x < V x + ((-(k : ℝ) : ℝ) : EReal)} :=
        thetaCapacity_union_le _ _ _ _
    _ < ENNReal.ofReal ε := by rw [hpole, zero_add]; exact hk

/-- **The missing half of `thm:comp_capa`, `ε`-plus-linear form.**  For big `θ` and every
`ε > 0` there is `C > 0` with `Cap_θ(E) ≤ ε + C · Cap_ω(E)` for every set `E`. -/
theorem exists_capacity_control_by_kahler (ω : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ E : Set M,
      thetaCapacityV θ E ≤ ENNReal.ofReal ε +
        ENNReal.ofReal C * thetaCapacity ω.form (fun _ => 0) E := by
  rcases isEmpty_or_nonempty M with hM | hM
  · refine ⟨1, one_pos, fun E => ?_⟩
    have he : E = ∅ := by ext x; exact isEmptyElim x
    simp only [he, thetaCapacityV, thetaCapacity_empty, zero_le]
  obtain ⟨B, _hB, htail⟩ := exists_minimalEnvelope_tail_small ω θ hbig hε
  set V := thetaPshSupremum θ.val
  have hV0 : ∀ x, V x ≤ 0 := fun x => thetaPshSupremum_le_zero _ x
  obtain ⟨K, hK, hdom⟩ := ActualLocallyBoundedReferenceCapacity.exists_capacity_bound ω θ hV0
    (Ω := {x | ((-B : ℝ) : EReal) ≤ V x}) (c := -B) (fun x hx => hx)
  refine ⟨K, hK, fun E => ?_⟩
  have hsplit : E ⊆ {x | V x < ((-B : ℝ) : EReal)} ∪
      (E ∩ {x | ((-B : ℝ) : EReal) ≤ V x}) := by
    intro x hx
    by_cases h : ((-B : ℝ) : EReal) ≤ V x
    · exact Or.inr ⟨hx, h⟩
    · exact Or.inl (lt_of_not_ge h)
  calc thetaCapacityV θ E
      ≤ thetaCapacity θ V ({x | V x < ((-B : ℝ) : EReal)} ∪
          (E ∩ {x | ((-B : ℝ) : EReal) ≤ V x})) := thetaCapacity_mono hsplit
    _ ≤ thetaCapacity θ V {x | V x < ((-B : ℝ) : EReal)} +
          thetaCapacity θ V (E ∩ {x | ((-B : ℝ) : EReal) ≤ V x}) :=
        thetaCapacity_union_le _ _ _ _
    _ ≤ ENNReal.ofReal ε + ENNReal.ofReal K * thetaCapacity ω.form (fun _ => 0) E := by
        refine add_le_add htail.le ?_
        exact (hdom _ inter_subset_right).trans
          (mul_le_mul_of_nonneg_left (thetaCapacity_mono inter_subset_left) zero_le)

/-- The same control with the source capacities of `def:cap` (the Kähler capacity is the
source capacity of `ω`, `sourceThetaCapacity_kahler`). -/
theorem exists_source_capacity_control_by_kahler (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ E : Set M,
      sourceThetaCapacity θ E ≤ ENNReal.ofReal ε +
        ENNReal.ofReal C * sourceThetaCapacity (nativeClosedFormToAtlas ω.form) E := by
  obtain ⟨C, hC, h⟩ := exists_capacity_control_by_kahler ω (atlasClosedFormToNative θ) hbig hε
  exact ⟨C, hC, fun E => by
    rw [sourceThetaCapacity_eq_native, sourceThetaCapacity_kahler]; exact h E⟩

/-- `ε`-plus-linear comparison of the source capacities of two big classes:
`Cap_θ(E) ≤ ε + C Cap_θ'(E)` on Borel sets. -/
theorem exists_source_capacity_control_of_big (ω : KahlerBackground n M)
    (θ θ' : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hbig' : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ')))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ E : Set M, MeasurableSet E →
      sourceThetaCapacity θ E ≤ ENNReal.ofReal ε + ENNReal.ofReal C * sourceThetaCapacity θ' E := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_source_capacity_control_by_kahler ω θ hbig (half_pos hε)
  have he : 0 < ε / 2 / C₁ := div_pos (half_pos hε) hC₁
  obtain ⟨C₂, hC₂, h₂⟩ := exists_source_capacity_control ω θ' hbig' he
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, fun E hE => ?_⟩
  calc sourceThetaCapacity θ E
      ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal C₁ *
          sourceThetaCapacity (nativeClosedFormToAtlas ω.form) E := h₁ E
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal C₁ *
          (ENNReal.ofReal (ε / 2 / C₁) + ENNReal.ofReal C₂ * sourceThetaCapacity θ' E) := by
        rw [sourceThetaCapacity_kahler]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (h₂ E hE) zero_le)
    _ = ENNReal.ofReal ε + ENNReal.ofReal (C₁ * C₂) * sourceThetaCapacity θ' E := by
        rw [mul_add, ← mul_assoc, ← ENNReal.ofReal_mul hC₁.le, ← ENNReal.ofReal_mul hC₁.le,
          mul_div_cancel₀ _ hC₁.ne', ← add_assoc, ← ENNReal.ofReal_add (half_pos hε).le
            (half_pos hε).le, add_halves]

/-- **Source `thm:comp_capa`.**  Let `X` be a compact Kähler manifold and `θ, θ'` closed real
smooth `(1,1)`-forms representing big classes.  There are continuous (and monotone)
`f, g : ℝ≥0 → ℝ≥0` with `f 0 = g 0 = 0` such that for every Borel set `E`,
`Cap_θ(E) ≤ f(Cap_θ'(E))` and `Cap_θ'(E) ≤ g(Cap_θ(E))`.  (Capacities are finite,
`sourceThetaCapacity_lt_top`, so they are read in `[0, ∞)` via `toNNReal`.) -/
theorem sourceCapacityComparison (ω : KahlerBackground n M)
    (θ θ' : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hbig' : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ'))) :
    ∃ f g : ℝ≥0 → ℝ≥0, Continuous f ∧ Continuous g ∧ f 0 = 0 ∧ g 0 = 0 ∧
      Monotone f ∧ Monotone g ∧ ∀ E : Set M, MeasurableSet E →
        sourceThetaCapacity θ E ≤ (f (sourceThetaCapacity θ' E).toNNReal : ℝ≥0∞) ∧
        sourceThetaCapacity θ' E ≤ (g (sourceThetaCapacity θ E).toNNReal : ℝ≥0∞) := by
  obtain ⟨f, hf, hf0, hfm, hfb⟩ := exists_continuous_modulus_of_forall_eps
    (ι := {E : Set M // MeasurableSet E})
    (fun E => sourceThetaCapacity θ E.1) (fun E => sourceThetaCapacity θ' E.1)
    (fun ε hε => by
      obtain ⟨C, hC, h⟩ := exists_source_capacity_control_of_big ω θ θ' hbig hbig' hε
      exact ⟨C, hC, fun E => h E.1 E.2⟩)
  obtain ⟨g, hg, hg0, hgm, hgb⟩ := exists_continuous_modulus_of_forall_eps
    (ι := {E : Set M // MeasurableSet E})
    (fun E => sourceThetaCapacity θ' E.1) (fun E => sourceThetaCapacity θ E.1)
    (fun ε hε => by
      obtain ⟨C, hC, h⟩ := exists_source_capacity_control_of_big ω θ' θ hbig' hbig hε
      exact ⟨C, hC, fun E => h E.1 E.2⟩)
  exact ⟨f, g, hf, hg, hf0, hg0, hfm, hgm, fun E hE =>
    ⟨hfb ⟨E, hE⟩ (sourceThetaCapacity_lt_top ω θ' E).ne,
      hgb ⟨E, hE⟩ (sourceThetaCapacity_lt_top ω θ E).ne⟩⟩

/-- Convergence to `0` in the capacity of one big class is convergence to `0` in the capacity
of any other big class, along any filter (Borel sets).  This is the independence of
`def:conv_cap` and `def:qc_fun` from the reference form asserted after `thm:comp_capa`. -/
theorem source_capacity_tendsto_zero_of_big (ω : KahlerBackground n M)
    (θ θ' : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hbig' : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ')))
    {I : Type*} {l : Filter I} (E : I → Set M) (hE : ∀ i, MeasurableSet (E i))
    (hcap : Tendsto (fun i => sourceThetaCapacity θ' (E i)) l (𝓝 0)) :
    Tendsto (fun i => sourceThetaCapacity θ (E i)) l (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  rcases eq_or_ne η ⊤ with rfl | htop
  · exact Eventually.of_forall fun _ => le_top
  · let ε : ℝ := η.toReal / 2
    have hε : 0 < ε := half_pos (ENNReal.toReal_pos hη.ne' htop)
    obtain ⟨C, hC, hb⟩ := exists_source_capacity_control_of_big ω θ θ' hbig hbig' hε
    have hsmall := (ENNReal.tendsto_nhds_zero.mp hcap)
      (ENNReal.ofReal (ε / C)) (ENNReal.ofReal_pos.mpr (div_pos hε hC))
    filter_upwards [hsmall] with i hi
    calc
      _ ≤ ENNReal.ofReal ε + ENNReal.ofReal C * sourceThetaCapacity θ' (E i) := hb (E i) (hE i)
      _ ≤ ENNReal.ofReal ε + ENNReal.ofReal C * ENNReal.ofReal (ε / C) :=
        add_le_add le_rfl (mul_le_mul' le_rfl hi)
      _ = ENNReal.ofReal ε + ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_mul hC.le, mul_div_cancel₀ ε hC.ne']
      _ = η := by
        rw [← ENNReal.ofReal_add hε.le hε.le]
        have he : ε + ε = η.toReal := by dsimp only [ε]; ring
        rw [he, ENNReal.ofReal_toReal htop]

end SGPT.NPP
