import SGPT.Foundations.Analysis.Pending.SingularPerronChartModification

set_option autoImplicit false

/-! # Actual compact support data for singular Perron chart modifications -/

open Set

namespace SGPT.Foundations.Analysis.Pending.SingularPerronCompactSupport

open FirstPass FiniteGeodesicMaximality

noncomputable section

variable {n : ℕ}

/-- The actual spatial projection of the actual patch closure. -/
def spatialProjection (D : Set (ComplexModel n × ℂ)) : Set (ComplexModel n) :=
  Prod.fst '' closure D

/-- The actual manifold support obtained by the actual inverse chart. -/
def manifoldSupport {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    (e : ComplexChart n M) (D : Set (ComplexModel n × ℂ)) : Set M :=
  e.val.symm '' spatialProjection D

/-- Continuous projection produces actual compactness, including empty patches. -/
theorem isCompact_spatialProjection {D : Set (ComplexModel n × ℂ)}
    (hDc : IsCompact (closure D)) : IsCompact (spatialProjection D) :=
  hDc.image continuous_fst

/-- The actual strip-domain inclusion puts the actual spatial support in the given chart patch. -/
theorem spatialProjection_subset {D : Set (ComplexModel n × ℂ)}
    {W : Set (ComplexModel n)} (hDW : closure D ⊆ geodesicChartDomain W) :
    spatialProjection D ⊆ W := by
  rintro _ ⟨p, hp, rfl⟩
  exact (hDW hp).1

/-- Actual inverse-chart continuity produces a compact manifold support. -/
theorem isCompact_manifoldSupport {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] (e : ComplexChart n M)
    {D : Set (ComplexModel n × ℂ)} {W : Set (ComplexModel n)}
    (hDc : IsCompact (closure D)) (hDW : closure D ⊆ geodesicChartDomain W)
    (hWt : W ⊆ e.val.target) : IsCompact (manifoldSupport e D) :=
  (isCompact_spatialProjection hDc).image_of_continuousOn
    (e.val.continuousOn_symm.mono ((spatialProjection_subset hDW).trans hWt))

/-- Actual inverse-chart target membership puts the manifold support in the chart source. -/
theorem manifoldSupport_subset_source {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] (e : ComplexChart n M)
    {D : Set (ComplexModel n × ℂ)} {W : Set (ComplexModel n)}
    (hDW : closure D ⊆ geodesicChartDomain W) (hWt : W ⊆ e.val.target) :
    manifoldSupport e D ⊆ e.val.source := by
  rintro _ ⟨z, hz, rfl⟩
  exact e.val.map_target (hWt (spatialProjection_subset hDW hz))

/-- Actual compact extrema produce strict interior time bounds for a nonempty patch. -/
theorem exists_time_bounds {D : Set (ComplexModel n × ℂ)} {W : Set (ComplexModel n)}
    (hDc : IsCompact (closure D)) (hDW : closure D ⊆ geodesicChartDomain W)
    (hne : D.Nonempty) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ b < 1 ∧
      ∀ p ∈ closure D, a ≤ p.2.re ∧ p.2.re ≤ b := by
  have hclne : (closure D).Nonempty := hne.mono subset_closure
  have hcont : Continuous fun p : ComplexModel n × ℂ => p.2.re :=
    Complex.continuous_re.comp continuous_snd
  obtain ⟨pa, hpa, hmin⟩ := hDc.exists_isMinOn hclne hcont.continuousOn
  obtain ⟨pb, hpb, hmax⟩ := hDc.exists_isMaxOn hclne hcont.continuousOn
  exact ⟨pa.2.re, pb.2.re, (hDW hpa).2.1, hmin hpb, (hDW hpb).2.2,
    fun p hp => ⟨hmin hp, hmax hp⟩⟩

/-- Only the actual continuous real correcting potential needs a finite lower bound. -/
theorem exists_potential_lower_bound {D : Set (ComplexModel n × ℂ)}
    {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hDc : IsCompact (closure D)) (hDW : closure D ⊆ geodesicChartDomain W)
    (hne : D.Nonempty) (hρ : ContinuousOn ρ W) :
    ∃ c : ℝ, ∀ z ∈ spatialProjection D, c ≤ ρ z := by
  obtain ⟨p, hp⟩ := hne
  have hne' : (spatialProjection D).Nonempty := ⟨p.1, p, subset_closure hp, rfl⟩
  obtain ⟨z, _, hmin⟩ := (isCompact_spatialProjection hDc).exists_isMinOn hne'
    (hρ.mono (spatialProjection_subset hDW))
  exact ⟨ρ z, fun y hy => hmin hy⟩

/-- The actual modification condition supplies the actual spatial, manifold, and time memberships. -/
theorem modification_mem_support {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] (e : ComplexChart n M)
    {D : Set (ComplexModel n × ℂ)} {a b : ℝ}
    (htime : ∀ p ∈ closure D, a ≤ p.2.re ∧ p.2.re ≤ b)
    {x : M} {τ : ℂ} (hx : x ∈ e.val.source) (hp : (e.val x, τ) ∈ D) :
    x ∈ manifoldSupport e D ∧ e.val x ∈ spatialProjection D ∧
      a ≤ τ.re ∧ τ.re ≤ b := by
  have hpc : (e.val x, τ) ∈ closure D := subset_closure hp
  have hpx : e.val x ∈ spatialProjection D := ⟨(e.val x, τ), hpc, rfl⟩
  exact ⟨⟨e.val x, hpx, e.val.left_inv hx⟩, hpx, (htime _ hpc).1, (htime _ hpc).2⟩

end

end SGPT.Foundations.Analysis.Pending.SingularPerronCompactSupport
