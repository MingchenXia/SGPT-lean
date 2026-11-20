import SGPT.PSH.SourceTestCurveLegendreAlgebra

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

variable [CompactSpace M] [ConnectedSpace M]

/-- The literal raw transform has exactly the original finite linear spatial
supremum; no positive slice mass or finite-energy premise is required. -/
theorem SourceTestCurvePredata.rawLegendre_globalSup
    (Γ : SourceTestCurvePredata θ) {t : ℝ} (ht : 0 < t) :
    (⨆ x, sourceTestCurveRawLegendre Γ t x) = ((t * Γ.max : ℝ) : EReal) := by
  apply le_antisymm
  · exact iSup_le (Γ.rawLegendre_le_cutoff ht.le)
  · have hτ (τ : Iio Γ.max) : ((t * τ.1 : ℝ) : EReal) ≤
        ⨆ x, sourceTestCurveRawLegendre Γ t x := by
      have hsup := sourceOrdinaryFixedPoint_globalSup_zero (Γ.thetaPSH τ) (Γ.fixedPoint τ)
      rw [← add_zero ((t * τ.1 : ℝ) : EReal)]
      apply EReal.add_le_of_forall_lt
      intro p hp q hq
      rw [← hsup] at hq
      obtain ⟨x, hx⟩ := lt_iSup_iff.mp hq
      have hpoint : ((t * τ.1 : ℝ) : EReal) + Γ.potential τ x ≤
          sourceTestCurveRawLegendre Γ t x := by
        rw [Γ.rawLegendre_eq_iSup_open t x]
        exact le_iSup (fun σ : Iio Γ.max ↦ ((t * σ.1 : ℝ) : EReal) + Γ.potential σ x) τ
      exact (add_le_add hp.le hx.le).trans (hpoint.trans (le_iSup _ x))
    have hlim : Tendsto (fun τ : ℝ ↦ ((t * τ : ℝ) : EReal))
        (𝓝[<] Γ.max) (𝓝 ((t * Γ.max : ℝ) : EReal)) :=
      (continuous_coe_real_ereal.comp (continuous_const.mul continuous_id)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with τ hτm
    exact hτ ⟨τ, hτm⟩

omit [CompactSpace M] [ConnectedSpace M] in
/-- The actual normalized raw transform decreases on ALL real times,
including its literal bottom values. -/
theorem SourceTestCurvePredata.rawLegendre_normalized_antitone
    (Γ : SourceTestCurvePredata θ) (x : M) :
    Antitone (fun t : ℝ ↦ sourceTestCurveRawLegendre Γ t x - ((t * Γ.max : ℝ) : EReal)) := by
  intro s t hst
  apply (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
    (Or.inl (EReal.coe_ne_top _))).mpr
  rw [Γ.rawLegendre_eq_iSup_open t x]
  apply iSup_le
  intro τ
  apply (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
    (Or.inl (EReal.coe_ne_top _))).mp
  have hreal : t * τ.1 - t * Γ.max ≤ s * τ.1 - s * Γ.max := by
    have hh := mul_le_mul_of_nonpos_right hst (sub_nonpos.mpr τ.2.le)
    nlinarith
  calc
    ((t * τ.1 : ℝ) : EReal) + Γ.potential τ x - ((t * Γ.max : ℝ) : EReal) =
        Γ.potential τ x + ((t * τ.1 - t * Γ.max : ℝ) : EReal) := by
      rw [add_comm ((t * τ.1 : ℝ) : EReal), add_sub_assoc, ← EReal.coe_sub]
    _ ≤ Γ.potential τ x + ((s * τ.1 - s * Γ.max : ℝ) : EReal) :=
      add_le_add le_rfl (EReal.coe_le_coe hreal)
    _ = ((s * τ.1 : ℝ) : EReal) + Γ.potential τ x - ((s * Γ.max : ℝ) : EReal) := by
      rw [add_comm ((s * τ.1 : ℝ) : EReal), add_sub_assoc, ← EReal.coe_sub]
    _ ≤ sourceTestCurveRawLegendre Γ s x - ((s * Γ.max : ℝ) : EReal) := by
      apply EReal.sub_le_sub _ le_rfl
      rw [Γ.rawLegendre_eq_iSup_open s x]
      exact le_iSup (fun σ : Iio Γ.max ↦ ((s * σ.1 : ℝ) : EReal) + Γ.potential σ x) τ

/-- ENTIRE original lma:suplegenlinear, on the SAME original test curve.
The original based condition is unnecessary for these two conclusions. -/
theorem sourceTestCurve_legendre_supremum_whole [MeasurableSpace M]
    (Γ : SourceTestCurve θ) :
    (∀ t : ℝ, 0 < t → (⨆ x, sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t x) =
      ((t * Γ.max : ℝ) : EReal)) ∧
    (∀ x, AntitoneOn (fun t : ℝ ↦ sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t x -
      ((t * Γ.max : ℝ) : EReal)) (Ioi 0)) :=
  ⟨fun _ ht ↦ Γ.toSourceTestCurvePredata.rawLegendre_globalSup ht,
    fun x _ _ _ _ hst ↦ Γ.toSourceTestCurvePredata.rawLegendre_normalized_antitone x hst⟩

end SGPT.PSH.VariableComplexAtlas
