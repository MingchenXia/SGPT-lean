import SGPT.PSH.SourceSubgeodesicRays
import SGPT.PSH.SourceSubgeodesicConvexity

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The actual long-time source chord forces normalized decrease at EVERY
nonnegative time, including the original assigned initial value and all poles. -/
theorem SourceIsSubgeodesicRay.normalized_antitone_of_linear_upper_bound
    {omega : KahlerBackground n M} {ℓ : SourceRayFamily M}
    (h : SourceIsSubgeodesicRay omega θ ℓ) (c : ℝ)
    (hbound : ∀ t : Ici (0 : ℝ), ∀ x, ℓ t x ≤ ((t.1 * c : ℝ) : EReal)) (x : M) :
    AntitoneOn (fun t : ℝ ↦ sourceRayExtension ℓ t x - ((t * c : ℝ) : EReal)) (Ici 0) := by
  intro s hs t ht hst
  rcases hst.eq_or_lt with heq | hst
  · subst t
    exact le_rfl
  apply EReal.le_of_forall_lt_iff_le.mp
  intro q hq
  have hsbound : sourceRayExtension ℓ s x ≤ ((s * c + q : ℝ) : EReal) := by
    have hh := (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
      (Or.inl (EReal.coe_ne_top _))).mp hq.le
    simpa only [EReal.coe_add, add_comm] using hh
  let a : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 2)
  let T : ℕ → ℝ := fun j ↦ s + ((j : ℝ) + 2) * (t - s)
  have hstep (j : ℕ) : sourceRayExtension ℓ t x ≤
      ((t * c + (1 - a j) * q : ℝ) : EReal) := by
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hden : (0 : ℝ) < (j : ℝ) + 2 := by positivity
    have ha : a j ∈ Ioo (0 : ℝ) 1 :=
      ⟨one_div_pos.mpr hden, (div_lt_one hden).mpr (by linarith)⟩
    have hT : t < T j := by
      dsimp [T]
      nlinarith
    have htime : a j * T j + (1 - a j) * s = t := by
      dsimp [a, T]
      field_simp [hden.ne']
      ring
    have hc := ((h s (T j) hs (hst.trans hT).le).2).le_closedChord
      (a := 0) (b := 1) le_rfl le_rfl zero_lt_one ⟨ha.1.le, ha.2.le⟩ x
    simp only [mul_zero, zero_add, mul_one,
      closedSubgeodesicSlice_zero, closedSubgeodesicSlice_one] at hc
    rw [closedSubgeodesicSlice_eq_curve ha, htime] at hc
    have hTbound : sourceRayExtension ℓ (T j) x ≤ ((T j * c : ℝ) : EReal) := by
      rw [sourceRayExtension_nonneg ℓ (T j) (ht.trans hT.le)]
      exact hbound ⟨T j, ht.trans hT.le⟩ x
    have hh := hc.trans (eRealChord_mono hsbound hTbound ha.1.le ha.2.le)
    rw [SubgeodesicInfimum.eRealChord_coe_coe] at hh
    have heq : (1 - a j) * (s * c + q) + a j * (T j * c) =
        t * c + (1 - a j) * q := by
      linear_combination c * htime
    simpa only [heq] using hh
  have ha_lim : Tendsto a atTop (𝓝 (0 : ℝ)) := by
    simpa [a, one_div, Function.comp_def] using
      (tendsto_mul_add_inv_atTop_nhds_zero 1 2 one_ne_zero).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hreal : Tendsto (fun j : ℕ ↦ t * c + (1 - a j) * q)
      atTop (𝓝 (t * c + q)) := by
    have htc : Tendsto (fun _ : ℕ ↦ t * c) atTop (𝓝 (t * c)) := tendsto_const_nhds
    have h1 : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa only [sub_zero, one_mul] using htc.add ((h1.sub ha_lim).mul_const q)
  have hlim := continuous_coe_real_ereal.continuousAt.tendsto.comp hreal
  have hneg : -((t * c + q : ℝ) : EReal) ≤ -sourceRayExtension ℓ t x := by
    apply le_of_tendsto hlim.neg
    exact Filter.Eventually.of_forall fun j ↦ EReal.neg_le_neg_iff.mpr (hstep j)
  have hb : sourceRayExtension ℓ t x ≤ ((t * c + q : ℝ) : EReal) :=
    EReal.neg_le_neg_iff.mp hneg
  apply (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
    (Or.inl (EReal.coe_ne_top _))).mpr
  simpa only [EReal.coe_add, add_comm] using hb

end SGPT.PSH.VariableComplexAtlas
