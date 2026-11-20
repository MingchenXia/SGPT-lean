import SGPT.NPP.KahlerCapacityBigControl
import SGPT.Envelopes.SourceNonPluripolarMassOrder
import SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy
import SGPT.Foundations.Analysis.Pending.ActualLocallyBoundedReferenceCapacity
import Mathlib.Analysis.Convex.Continuous

/-!
# Continuous comparison moduli for capacities

Source `thm:comp_capa` asserts, for two closed smooth real `(1,1)`-forms
`θ, θ'` in big classes, continuous `f, g : [0, ∞) → [0, ∞)` with
`f(0) = g(0) = 0`, `Cap_θ ≤ f ∘ Cap_θ'` and `Cap_θ' ≤ g ∘ Cap_θ` on Borel sets.

This file proves:
* `sourceThetaCapacity_lt_top`: source capacities are finite (so they are
  points of `[0, ∞)`);
* `exists_continuous_modulus_of_forall_eps`: an `ε`-plus-linear control
  `F ≤ ε + C_ε G` (for every `ε > 0`) yields a continuous monotone modulus
  `g` with `g 0 = 0` and `F ≤ g ∘ G`;
* `exists_modulus_kahlerCapacity_le_sourceThetaCapacity`: the inequality
  `Cap_θ' ≤ g(Cap_θ)` of `thm:comp_capa` when `θ' = ω` is a Kähler form and
  `θ` is big.

The remaining inequality `Cap_θ ≤ f(Cap_ω)` (big `θ`, whose minimal potential
`V_θ` may be unbounded) is not proved here.
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

/-- An `ε`-plus-linear control `F ≤ ε + C_ε · G` for every `ε > 0` gives a
continuous monotone modulus `g` with `g 0 = 0` and `F ≤ g(G)` wherever `G` is
finite. -/
theorem exists_continuous_modulus_of_forall_eps {ι : Type*} (F G : ι → ℝ≥0∞)
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ i, F i ≤ ENNReal.ofReal ε + ENNReal.ofReal C * G i) :
    ∃ g : ℝ≥0 → ℝ≥0, Continuous g ∧ g 0 = 0 ∧ Monotone g ∧
      ∀ i, G i ≠ ⊤ → F i ≤ (g (G i).toNNReal : ℝ≥0∞) := by
  choose C hC hFC using fun k : ℕ => h (1 / ((k : ℝ) + 1)) (by positivity)
  let term : ℕ → ℝ → ℝ := fun k s => 1 / ((k : ℝ) + 1) + C k * s
  let gR : ℝ → ℝ := fun s => ⨅ k : ℕ, term k s
  have hterm_nonneg : ∀ k {s : ℝ}, 0 ≤ s → 0 ≤ term k s := fun k {s} hs => by
    have := (hC k).le
    dsimp only [term]
    positivity
  have hbdd : ∀ {s : ℝ}, 0 ≤ s → BddBelow (range fun k => term k s) :=
    fun {s} hs => ⟨0, by rintro _ ⟨k, rfl⟩; exact hterm_nonneg k hs⟩
  have hgR_nonneg : ∀ {s : ℝ}, 0 ≤ s → 0 ≤ gR s := fun {s} hs =>
    le_ciInf fun k => hterm_nonneg k hs
  have hgR_le : ∀ k {s : ℝ}, 0 ≤ s → gR s ≤ term k s := fun k {s} hs => ciInf_le (hbdd hs) k
  have hgR_zero : gR 0 = 0 := by
    apply le_antisymm _ (hgR_nonneg le_rfl)
    apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    calc gR 0 ≤ term k 0 := hgR_le k le_rfl
      _ = 1 / ((k : ℝ) + 1) := by simp [term]
      _ < 0 + ε := by linarith
  have hgR_mono : MonotoneOn gR (Ici 0) := by
    intro s hs t ht hst
    exact ciInf_mono (hbdd hs) fun k => by
      have := (hC k).le
      dsimp only [term]
      nlinarith
  have hgR_concave : ConcaveOn ℝ (Ici 0) gR := by
    refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
    have hxy : 0 ≤ a • x + b • y := by
      simp only [smul_eq_mul]
      exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
    apply le_ciInf
    intro k
    have h1 := mul_le_mul_of_nonneg_left (hgR_le k hx) ha
    have h2 := mul_le_mul_of_nonneg_left (hgR_le k hy) hb
    simp only [smul_eq_mul, term] at h1 h2 ⊢
    have e : a * (1 / ((k : ℝ) + 1) + C k * x) + b * (1 / ((k : ℝ) + 1) + C k * y) =
        1 / ((k : ℝ) + 1) + C k * (a * x + b * y) := by
      linear_combination (1 / ((k : ℝ) + 1)) * hab
    linarith
  have hcont : ContinuousOn gR (Ici 0) := by
    intro x hx
    rcases (show (0 : ℝ) ≤ x from hx).eq_or_lt with h0 | hpos
    · subst h0
      rw [ContinuousWithinAt, hgR_zero, Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hε)
      refine ⟨ε / 2 / C k, div_pos (half_pos hε) (hC k), fun {s} hs hsd => ?_⟩
      have hs0 : (0 : ℝ) ≤ s := hs
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hs0] at hsd
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hgR_nonneg hs0)]
      have hCs : C k * s < ε / 2 := by
        rwa [lt_div_iff₀ (hC k), mul_comm] at hsd
      calc gR s ≤ term k s := hgR_le k hs0
        _ < ε / 2 + ε / 2 := by dsimp only [term]; linarith
        _ = ε := by ring
    · have hint : x ∈ interior (Ici (0 : ℝ)) := by
        rw [interior_Ici]
        exact hpos
      exact (hgR_concave.continuousOn_interior x hint).mono_of_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (isOpen_interior.mem_nhds hint))
  let g : ℝ≥0 → ℝ≥0 := fun s => ⟨gR s, hgR_nonneg s.2⟩
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · exact Continuous.subtype_mk
      (hcont.comp_continuous NNReal.continuous_coe fun s => s.2) _
  · exact Subtype.ext (show gR ((0 : ℝ≥0) : ℝ) = ((0 : ℝ≥0) : ℝ) by
      rw [NNReal.coe_zero]; exact hgR_zero)
  · intro s t hst
    exact hgR_mono s.2 t.2 (NNReal.coe_le_coe.mpr hst)
  · intro i hGi
    have hbound : ∀ k, F i ≤ ENNReal.ofReal (term k (G i).toReal) := by
      intro k
      have hk := hFC k i
      have hCnn := (hC k).le
      have he : ENNReal.ofReal (term k (G i).toReal) =
          ENNReal.ofReal (1 / ((k : ℝ) + 1)) + ENNReal.ofReal (C k) * G i := by
        dsimp only [term]
        rw [ENNReal.ofReal_add (by positivity) (mul_nonneg hCnn ENNReal.toReal_nonneg),
          ENNReal.ofReal_mul hCnn, ENNReal.ofReal_toReal hGi]
      rw [he]
      exact hk
    have hFi : F i ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound 0)
    have hreal : (F i).toReal ≤ gR (G i).toReal := by
      apply le_ciInf
      intro k
      exact (ENNReal.toReal_le_toReal hFi ENNReal.ofReal_ne_top).mpr (hbound k) |>.trans
        (le_of_eq (ENNReal.toReal_ofReal (hterm_nonneg k ENNReal.toReal_nonneg)))
    have hcoe : ((g (G i).toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (gR (G i).toReal) := by
      rw [ENNReal.ofReal, Real.toNNReal_of_nonneg (hgR_nonneg ENNReal.toReal_nonneg)]
      rfl
    rw [hcoe, ← ENNReal.ofReal_toReal hFi]
    exact ENNReal.ofReal_le_ofReal hreal

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Source capacities are finite: every competitor has the same total
non-pluripolar mass, which is finite on a compact Kähler manifold. -/
theorem sourceThetaCapacity_lt_top (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (E : Set M) :
    sourceThetaCapacity θ E < ⊤ := by
  classical
  by_cases hex : ∃ (u : M → EReal) (_ : (ofFixedModel n M).IsThetaPSH θ u),
      (fun x ↦ sourceMinimalEnvelope θ x - 1) ≤ u ∧ u ≤ sourceMinimalEnvelope θ
  · obtain ⟨u₀, hu₀, hlo₀, hhi₀⟩ := hex
    have hfin : sourcePotentialNonPluripolarMeasure θ u₀ hu₀ univ < ⊤ := by
      have h := sourceMixedNonPluripolarMass_lt_top ω (fun _ : Fin n => θ) (fun _ => u₀)
        (fun _ => hu₀)
      rwa [sourceMixedNonPluripolarMass_diagonal] at h
    refine lt_of_le_of_lt ?_ hfin
    apply iSup_le
    intro u
    apply iSup_le
    intro hu
    apply iSup_le
    intro _hlo
    apply iSup_le
    intro hhi
    refine (measure_mono (subset_univ E)).trans ?_
    apply sourcePotentialNonPluripolarMass_mono ω hu hu₀
    refine ⟨1, fun x _ => ?_⟩
    simpa only [EReal.coe_one] using (hhi x).trans ((sub_one_le_iff_le_add_one _ _).mp (hlo₀ x))
  · have h0 : sourceThetaCapacity θ E = 0 := by
      apply le_antisymm _ zero_le
      apply iSup_le
      intro u
      apply iSup_le
      intro hu
      apply iSup_le
      intro hlo
      apply iSup_le
      intro hhi
      exact absurd ⟨u, hu, hlo, hhi⟩ hex
    rw [h0]
    exact ENNReal.zero_lt_top

omit [BorelSpace M] in
/-- For a Kähler form the source capacity is the Kähler capacity (`V_ω = 0`). -/
theorem sourceThetaCapacity_kahler (ω : KahlerBackground n M) (E : Set M) :
    sourceThetaCapacity (nativeClosedFormToAtlas ω.form) E =
      thetaCapacity ω.form (fun _ => 0) E := by
  rw [sourceThetaCapacity_eq_native, sourceNativeAtlasForm_roundTrip]
  have hV : thetaPshSupremum ω.form.val = fun _ => 0 :=
    le_antisymm (thetaPshSupremum_le_zero _)
      (le_thetaPshSupremum (PluripolarCapacityDichotomy.isThetaPshPotential_zero ω) le_rfl)
  unfold thetaCapacityV
  rw [hV]

/-- Source `thm:comp_capa`, the inequality `Cap_θ' ≤ g(Cap_θ)` for `θ' = ω` a
Kähler form and `θ` in a big class: a continuous monotone `g` with `g 0 = 0`. -/
theorem exists_modulus_kahlerCapacity_le_sourceThetaCapacity (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    ∃ g : ℝ≥0 → ℝ≥0, Continuous g ∧ g 0 = 0 ∧ Monotone g ∧
      ∀ E : Set M, MeasurableSet E →
        sourceThetaCapacity (nativeClosedFormToAtlas ω.form) E ≤
          (g (sourceThetaCapacity θ E).toNNReal : ℝ≥0∞) := by
  obtain ⟨g, hg, hg0, hgm, hgb⟩ := exists_continuous_modulus_of_forall_eps
    (ι := {E : Set M // MeasurableSet E})
    (fun E => sourceThetaCapacity (nativeClosedFormToAtlas ω.form) E.1)
    (fun E => sourceThetaCapacity θ E.1)
    (fun ε hε => by
      obtain ⟨C, hC, hb⟩ := exists_source_capacity_control ω θ hbig hε
      exact ⟨C, hC, fun E => by rw [sourceThetaCapacity_kahler]; exact hb E.1 E.2⟩)
  exact ⟨g, hg, hg0, hgm, fun E hE =>
    hgb ⟨E, hE⟩ (sourceThetaCapacity_lt_top ω θ E).ne⟩

/-- Source `thm:comp_capa`, the inequality `Cap_θ' ≤ g(Cap_θ)` whenever `θ` is
big and the minimal potential `V_θ'` is bounded below (for instance `θ'`
semipositive, or Kähler): a continuous monotone `g` with `g 0 = 0`. -/
theorem exists_modulus_of_minimalEnvelope_bounded (ω : KahlerBackground n M)
    (θ θ' : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {c : ℝ} (hc : ∀ x, (c : EReal) ≤ sourceMinimalEnvelope θ' x) :
    ∃ g : ℝ≥0 → ℝ≥0, Continuous g ∧ g 0 = 0 ∧ Monotone g ∧
      ∀ E : Set M, MeasurableSet E →
        sourceThetaCapacity θ' E ≤ (g (sourceThetaCapacity θ E).toNNReal : ℝ≥0∞) := by
  have hV0 : ∀ x, thetaPshSupremum (atlasClosedFormToNative θ').val x ≤ 0 :=
    fun x => thetaPshSupremum_le_zero _ x
  have hcV : ∀ x ∈ (univ : Set M), (c : EReal) ≤ thetaPshSupremum (atlasClosedFormToNative θ').val x :=
    fun x _ => by simpa only [sourceMinimalEnvelope_eq_native] using hc x
  obtain ⟨K, hK, hdom⟩ := ActualLocallyBoundedReferenceCapacity.exists_capacity_bound ω
    (atlasClosedFormToNative θ') hV0 hcV
  obtain ⟨g, hg, hg0, hgm, hgb⟩ := exists_continuous_modulus_of_forall_eps
    (ι := {E : Set M // MeasurableSet E})
    (fun E => sourceThetaCapacity θ' E.1)
    (fun E => sourceThetaCapacity θ E.1)
    (fun ε hε => by
      obtain ⟨C, hC, hb⟩ := exists_source_capacity_control ω θ hbig (div_pos hε hK)
      refine ⟨K * C, mul_pos hK hC, fun E => ?_⟩
      calc sourceThetaCapacity θ' E.1
          = thetaCapacity (atlasClosedFormToNative θ')
              (thetaPshSupremum (atlasClosedFormToNative θ').val) E.1 := by
            rw [sourceThetaCapacity_eq_native]; rfl
        _ ≤ ENNReal.ofReal K * thetaCapacity ω.form (fun _ => 0) E.1 :=
            hdom E.1 (subset_univ _)
        _ ≤ ENNReal.ofReal K * (ENNReal.ofReal (ε / K) +
              ENNReal.ofReal C * sourceThetaCapacity θ E.1) :=
            mul_le_mul_of_nonneg_left (hb E.1 E.2) zero_le
        _ = ENNReal.ofReal ε + ENNReal.ofReal (K * C) * sourceThetaCapacity θ E.1 := by
            rw [mul_add, ← mul_assoc, ← ENNReal.ofReal_mul hK.le, ← ENNReal.ofReal_mul hK.le,
              mul_div_cancel₀ ε hK.ne'])
  exact ⟨g, hg, hg0, hgm, fun E hE =>
    hgb ⟨E, hE⟩ (sourceThetaCapacity_lt_top ω θ E).ne⟩

end SGPT.NPP
