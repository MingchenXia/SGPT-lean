import SGPT.Foundations.Analysis.Pending.ActualLocalizedLeviMarginal

set_option autoImplicit false

/-! # Actual directional Levi measure on transverse null columns

Compact smooth cutoffs are produced internally; localized transverse AC
and the actual countable compact cover give nullity of the whole column.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Laplacian

namespace SGPT.Foundations.Analysis.Pending.ActualDirectionalLeviNullColumns

open FirstPass

variable {m : ℕ} {U : Opens ℂ} {V : Opens (ComplexModel m)}

private def rectangle (U : Opens ℂ) (V : Opens (ComplexModel m)) :
    Opens (ℂ × ComplexModel m) := ⟨(U : Set ℂ) ×ˢ (V : Set (ComplexModel m)), U.isOpen.prod V.isOpen⟩

private theorem compact_null_column (ν : Measure (rectangle U V))
    (hAC : ∀ (β : 𝓓(U, ℝ)) (χ : 𝓓(V, ℝ)), (∀ s, 0 ≤ β s) → (∀ y, 0 ≤ χ y) →
      (ν.withDensity (fun x => ENNReal.ofReal (β x.val.1 * χ x.val.2))).map
        (fun x => x.val.2) ≪ volume)
    {K : Set (ℂ × ComplexModel m)} (hK : IsCompact K) (hKΩ : K ⊆ rectangle U V)
    {E : Set (ComplexModel m)} (hE : volume E = 0) :
    ν {x : rectangle U V | x.val ∈ K ∧ x.val.2 ∈ E} = 0 := by
  have hK1 : Prod.fst '' K ⊆ U := by
    rintro s ⟨x, hx, rfl⟩
    exact (hKΩ hx).1
  have hK2 : Prod.snd '' K ⊆ V := by
    rintro y ⟨x, hx, rfl⟩
    exact (hKΩ hx).2
  obtain ⟨β, hβ, hβK⟩ := exists_nonneg_testFunction_one_le_on_compact
    (hK.image continuous_fst) hK1
  obtain ⟨χ, hχ, hχK⟩ := exists_nonneg_testFunction_one_le_on_compact
    (hK.image continuous_snd) hK2
  have hw : Measurable (fun x : rectangle U V => ENNReal.ofReal
      (β x.val.1 * χ x.val.2)) :=
    ((β.continuous.comp (continuous_fst.comp continuous_subtype_val)).mul
      (χ.continuous.comp (continuous_snd.comp continuous_subtype_val))).measurable.ennreal_ofReal
  have hpr : Measurable (fun x : rectangle U V => x.val.2) :=
    (continuous_snd.comp continuous_subtype_val).measurable
  have hE' : volume (toMeasurable volume E) = 0 := by rw [measure_toMeasurable, hE]
  have hz := hAC β χ hβ hχ hE'
  rw [Measure.map_apply hpr (measurableSet_toMeasurable volume E)] at hz
  have hzero := (withDensity_apply_eq_zero hw).mp hz
  apply measure_mono_null _ hzero
  rintro x ⟨hxK, hxE⟩
  refine ⟨?_, subset_toMeasurable volume E hxE⟩
  apply ne_of_gt
  apply ENNReal.ofReal_pos.mpr
  exact mul_pos (zero_lt_one.trans_le (hβK x.val.1 ⟨x.val, hxK, rfl⟩))
    (zero_lt_one.trans_le (hχK x.val.2 ⟨x.val, hxK, rfl⟩))

private theorem whole_null_column (ν : Measure (rectangle U V))
    (hAC : ∀ (β : 𝓓(U, ℝ)) (χ : 𝓓(V, ℝ)), (∀ s, 0 ≤ β s) → (∀ y, 0 ≤ χ y) →
      (ν.withDensity (fun x => ENNReal.ofReal (β x.val.1 * χ x.val.2))).map
        (fun x => x.val.2) ≪ volume)
    {E : Set (ComplexModel m)} (hE : volume E = 0) :
    ν {x : rectangle U V | x.val.2 ∈ E} = 0 := by
  let _ : LocallyCompactSpace (rectangle U V) :=
    (rectangle U V).isOpen.locallyCompactSpace
  have hnull (k : ℕ) : ν (compactCovering (rectangle U V) k ∩
      {x : rectangle U V | x.val.2 ∈ E}) = 0 := by
    have hK := (isCompact_compactCovering (rectangle U V) k).image continuous_subtype_val
    have hKΩ : Subtype.val '' compactCovering (rectangle U V) k ⊆ rectangle U V := by
      rintro x ⟨y, hy, rfl⟩
      exact y.property
    have h := compact_null_column ν hAC hK hKΩ hE
    change ν ((Subtype.val ⁻¹' (Subtype.val '' compactCovering (rectangle U V) k)) ∩
      {x : rectangle U V | x.val.2 ∈ E}) = 0 at h
    rw [Subtype.val_injective.preimage_image] at h
    exact h
  apply measure_mono_null _ (measure_iUnion_null hnull)
  intro x hx
  obtain ⟨k, hk⟩ := exists_mem_compactCovering x
  exact mem_iUnion.mpr ⟨k, hk, hx⟩

/-- The original unbounded psh potential produces a genuine directional
measure which assigns zero outer measure to every transverse null column. -/
theorem exists_directional_measure_with_null_columns
    (U : Opens ℂ) (V : Opens (ComplexModel m)) (f : ℂ × ComplexModel m → EReal)
    (hf : PlurisubharmonicOn f ((U : Set ℂ) ×ˢ (V : Set (ComplexModel m))))
    (hΩ : IsPreconnected ((U : Set ℂ) ×ˢ (V : Set (ComplexModel m))))
    (hne : ∃ a ∈ ((U : Set ℂ) ×ˢ (V : Set (ComplexModel m))), f a ≠ ⊥) :
    let Ω : Opens (ℂ × ComplexModel m) :=
      ⟨(U : Set ℂ) ×ˢ (V : Set (ComplexModel m)), U.isOpen.prod V.isOpen⟩
    ∃ ν : Measure Ω, ν.Regular ∧ IsLocallyFiniteMeasure ν ∧
      (∀ φ : 𝓓(Ω, ℝ), (∫ x : Ω, φ x ∂ν) =
        distributionalLeviCLM (1, (0 : ComplexModel m))
          (pshRegularDistribution hf volume hΩ hne) φ) ∧
      ∀ E : Set (ComplexModel m), volume E = 0 → ν {x : Ω | x.val.2 ∈ E} = 0 := by
  obtain ⟨ν, hreg, hloc, hrep, hAC⟩ :=
    ActualLocalizedLeviMarginal.exists_directional_measure_with_localized_transverse_ac U V f hf hΩ hne
  let ν' : Measure (rectangle U V) := ν
  refine ⟨ν', hreg, hloc, hrep, ?_⟩
  intro E hE
  exact whole_null_column ν' (fun β χ hβ hχ => (hAC β χ hβ hχ).2) hE

end SGPT.Foundations.Analysis.Pending.ActualDirectionalLeviNullColumns
