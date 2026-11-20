import SGPT.Foundations.Analysis.Pending.XiaoFiniteProbeDomination

set_option autoImplicit false

/-! # Actual pure coefficient-jet topology and genuine intrinsic C0 redundancy -/

open Set Filter Topology
open scoped Topology BoundedContinuousFunction

namespace SGPT.Foundations.Analysis.Pending.XiaoPureSmoothTopology

open FirstPass FirstPass.PositiveClasses XiaoFormC0Topology XiaoSmoothFormTopology
  XiaoFiniteProbeDomination XiaoPositiveCompactChartCover

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual pure smooth topology is induced only by all actual compact scalar coefficient jets. -/
abbrev formPureSmoothTopology : TopologicalSpace (ClosedRealOneOneForm n M) :=
  TopologicalSpace.induced (allJetsLinearMap (n := n) (M := M)) inferInstance

/-- Actual addition and negation are continuous in the actual pure coefficient-jet topology. -/
theorem formPureSmoothTopology_isTopologicalAddGroup :
    @IsTopologicalAddGroup (ClosedRealOneOneForm n M) formPureSmoothTopology inferInstance :=
  topologicalAddGroup_induced allJetsLinearMap

/-- Actual real scalar multiplication is continuous in the actual pure coefficient-jet topology. -/
theorem formPureSmoothTopology_continuousSMul :
    @ContinuousSMul ℝ (ClosedRealOneOneForm n M) inferInstance inferInstance formPureSmoothTopology :=
  continuousSMul_induced allJetsLinearMap

/-- Every actual compact scalar coefficient jet is genuinely continuous for the actual pure smooth topology. -/
theorem continuous_jetLinearMap (p : JetProbe n M) :
    Continuous[formPureSmoothTopology, inferInstance] (jetLinearMap p) := by
  let : TopologicalSpace (ClosedRealOneOneForm n M) := formPureSmoothTopology
  have hjet : Continuous (allJetsLinearMap (n := n) (M := M)) := continuous_induced_dom
  exact (continuous_apply p).comp hjet

/-- The actual finite patch coefficient norm sum is continuous in the actual pure smooth topology. -/
theorem continuous_patchProbeSum {I : Type*} [Fintype I] {w : KahlerBackground n M}
    (p : PositiveChartPatch w) (b : Module.Basis I ℝ (ComplexModel n)) :
    Continuous[formPureSmoothTopology, inferInstance] (patchProbeSum p b) := by
  let : TopologicalSpace (ClosedRealOneOneForm n M) := formPureSmoothTopology
  exact continuous_finsetSum Finset.univ
    (fun s _ => (continuous_jetLinearMap (coefficientProbe p b s)).norm)

/-- Every actual fixed finite weighted patch estimate is genuinely continuous in the actual pure smooth topology. -/
theorem continuous_weighted_patchProbeSum {I : Type*} [Fintype I] {w : KahlerBackground n M}
    (b : Module.Basis I ℝ (ComplexModel n)) (t : Finset (PositiveChartPatch w)) (C : ℝ) :
    Continuous[formPureSmoothTopology, inferInstance]
      (fun θ : ClosedRealOneOneForm n M =>
        ∑ p ∈ t, (C / p.lowerConstant) * patchProbeSum p b θ) := by
  let : TopologicalSpace (ClosedRealOneOneForm n M) := formPureSmoothTopology
  exact continuous_finsetSum t (fun p _ => continuous_const.mul (continuous_patchProbeSum p b))

variable [CompactSpace M]

/-- Actual compactness and actual finite tensor probes produce genuine intrinsic C0 continuity in the pure topology. -/
theorem continuous_probeLinearMap (w : KahlerBackground n M) :
    Continuous[formPureSmoothTopology, inferInstance] (probeLinearMap w) := by
  let : TopologicalSpace (ClosedRealOneOneForm n M) := formPureSmoothTopology
  let : IsTopologicalAddGroup (ClosedRealOneOneForm n M) :=
    formPureSmoothTopology_isTopologicalAddGroup
  let b := Module.finBasis ℝ (ComplexModel n)
  obtain ⟨t, C, _hC, hbound⟩ := exists_formC0Seminorm_le_finite_probes w b
  let S : ClosedRealOneOneForm n M → ℝ :=
    fun θ => ∑ p ∈ t, (C / p.lowerConstant) * patchProbeSum p b θ
  have hS : Continuous S := continuous_weighted_patchProbeSum b t C
  have hS0 : S 0 = 0 := by simp [S, patchProbeSum, map_zero]
  apply continuous_of_continuousAt_zero (probeLinearMap w)
  change Tendsto (probeLinearMap w) (𝓝 0) (𝓝 (probeLinearMap w 0))
  rw [map_zero]
  apply squeeze_zero_norm (a := S)
  · intro θ
    rw [← formC0Seminorm_eq]
    exact hbound θ
  · have hSzero : Tendsto S (𝓝 0) (𝓝 (S 0)) := hS.continuousAt.tendsto
    simpa only [hS0] using hSzero

/-- The identity from the actual pure coefficient-jet topology to intrinsic directional C0 is genuinely continuous. -/
theorem continuous_pure_identity_to_formC0Topology (w : KahlerBackground n M) :
    Continuous[formPureSmoothTopology, formC0Topology w]
      (id : ClosedRealOneOneForm n M → ClosedRealOneOneForm n M) := by
  let : TopologicalSpace (ClosedRealOneOneForm n M) := formPureSmoothTopology
  apply continuous_induced_rng.mpr
  exact continuous_probeLinearMap w

/-- The actual intrinsic C0 component is redundant: adjoining it leaves the actual pure coefficient-jet topology unchanged. -/
theorem formSmoothTopology_eq_pure (w : KahlerBackground n M) :
    formSmoothTopology w = formPureSmoothTopology := by
  have hle : formPureSmoothTopology ≤ formC0Topology w := by
    simpa only [induced_id] using continuous_iff_le_induced.mp
      (continuous_pure_identity_to_formC0Topology w)
  rw [formSmoothTopology_eq_inf]
  exact inf_eq_right.mpr hle

end

end SGPT.Foundations.Analysis.Pending.XiaoPureSmoothTopology
