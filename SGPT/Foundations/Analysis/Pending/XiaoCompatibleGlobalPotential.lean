import SGPT.Foundations.Analysis.Pending.XiaoCompatibleLocalRepresentatives

set_option autoImplicit false

/-! # Actual global PSH gluing and Kähler currents from genuinely compatible coordinate distributions -/

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff NNReal Distributions

namespace SGPT.Foundations.Analysis.Pending.XiaoCompatibleGlobalPotential

open FirstPass FirstPass.HolomorphicMaps FirstPass.PositiveClasses ThetaPshChartLimitGluing
  XiaoPoissonChartCompatibility XiaoCompatibleLocalRepresentatives

noncomputable section

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- Actual compatible local theta-PSH distributions glue to an actual globally represented potential. -/
theorem exists_isThetaPshPotential_of_isCoordinateCompatible
    (μ : Measure (ComplexModel (m + 1))) [μ.IsAddHaarMeasure]
    {θ : SmoothRealForm (m + 1) M 2}
    (U : ∀ e : ComplexChart (m + 1) M, 𝓓'(chartTarget e, ℝ))
    (hU : IsCoordinateCompatible U)
    (hLevi : ∀ e, IsLocallyThetaPshDistribution μ θ e (U e)) :
    ∃ V : M → EReal, IsThetaPshPotential θ V ∧ ∀ e : ComplexChart (m + 1) M,
      (∀ᵐ z ∂μ.restrict (chartTarget e), chartFunction V e z ≠ ⊤ ∧ chartFunction V e z ≠ ⊥) ∧
      ∃ hV : LocallyIntegrableOn (fun z => (chartFunction V e z).toReal) (chartTarget e) μ,
        U e = regularDistribution μ (fun z => (chartFunction V e z).toReal) hV := by
  classical
  have hrep : ∀ (e : ComplexChart (m + 1) M) (z : ComplexModel (m + 1)), z ∈ e.val.target →
      ∃ R : LocalRep μ θ e (U e), z ∈ R.W := fun e _ hz => (hLevi e).exists_localRep hz
  choose R hR using hrep
  have hx : ∀ x : M, (complexChartAt (n := m + 1) x).val x ∈ (complexChartAt (n := m + 1) x).val.target :=
    fun x => (complexChartAt x).val.map_source (mem_complexChartAt_source x)
  -- the preferred local representative at `x`
  let P : ∀ x : M, LocalRep μ θ (complexChartAt (n := m + 1) x) (U (complexChartAt x)) := fun x =>
    R (complexChartAt x) ((complexChartAt x).val x) (hx x)
  let V : M → EReal := fun x =>
    (P x).u ((complexChartAt (n := m + 1) x).val x) +
      ((-(P x).ρ ((complexChartAt (n := m + 1) x).val x) : ℝ) : EReal)
  -- every local representative in every chart is `V ∘ e⁻¹ + ρ`
  have hkey : ∀ (e : ComplexChart (m + 1) M) (z : ComplexModel (m + 1)) (hz : z ∈ e.val.target),
      ∀ y ∈ (R e z hz).W, chartFunction V e y + ((R e z hz).ρ y : EReal) = (R e z hz).u y := by
    intro e z hz y hy
    have hyF : y ∈ (chartTransition e (complexChartAt (n := m + 1) (e.val.symm y))).source :=
      ⟨(R e z hz).hW hy, mem_complexChartAt_source _⟩
    have hFyW : chartTransition e (complexChartAt (n := m + 1) (e.val.symm y)) y ∈
        (P (e.val.symm y)).W := hR _ _ (hx _)
    rw [localRep_eq_transport μ hU (R e z hz) (P (e.val.symm y)) hy hyF hFyW]
    rfl
  have hpsh : ThetaPlurisubharmonic θ V := by
    intro e z hz
    refine ⟨(R e z hz).W, (R e z hz).ρ, hR e z hz, (R e z hz).pot, fun y hy => ?_⟩
    refine ((R e z hz).rep.1 y hy).congr ?_
    filter_upwards [(R e z hz).W.isOpen.mem_nhds hy] with w hw
    exact (hkey e z hz w hw).symm
  have hchart : ∀ e : ComplexChart (m + 1) M,
      (∀ᵐ z ∂μ.restrict (chartTarget e), chartFunction V e z ≠ ⊤ ∧ chartFunction V e z ≠ ⊥) ∧
      ∃ hV : LocallyIntegrableOn (fun z => (chartFunction V e z).toReal) (chartTarget e) μ,
        U e = regularDistribution μ (fun z => (chartFunction V e z).toReal) hV := by
    intro e
    have heq : ∀ z (hz : z ∈ e.val.target), ∀ y ∈ (R e z hz).W,
        chartFunction V e y = (R e z hz).u y + ((-(R e z hz).ρ y : ℝ) : EReal) :=
      fun z hz y hy => ereal_eq_add_coe_neg_of_add_coe_eq (hkey e z hz y hy)
    have hfinW : ∀ z (hz : z ∈ e.val.target), ∀ᵐ y ∂μ.restrict (R e z hz).W,
        chartFunction V e y ≠ ⊤ ∧ chartFunction V e y ≠ ⊥ := by
      intro z hz
      filter_upwards [(R e z hz).rep.2.1,
        ae_restrict_mem (R e z hz).W.isOpen.measurableSet] with y hy hyW
      rw [heq z hz y hyW]
      exact ereal_add_coe_finite hy _
    have htoReal : ∀ z (hz : z ∈ e.val.target),
        (fun y => ((R e z hz).u y).toReal - (R e z hz).ρ y) =ᵐ[μ.restrict (R e z hz).W]
          fun y => (chartFunction V e y).toReal := by
      intro z hz
      filter_upwards [(R e z hz).rep.2.1,
        ae_restrict_mem (R e z hz).W.isOpen.measurableSet] with y hy hyW
      rw [heq z hz y hyW, ereal_toReal_add_coe hy]
      ring
    have hloc : LocallyIntegrableOn (fun z => (chartFunction V e z).toReal) (chartTarget e) μ := by
      intro z hz
      have hlocW : LocallyIntegrableOn (fun y => (chartFunction V e y).toReal)
          (R e z hz).W μ :=
        ((R e z hz).rep.2.2.1.sub (R e z hz).hρi).congr (htoReal z hz)
      have h1 := hlocW z (hR e z hz)
      rw [(R e z hz).W.isOpen.nhdsWithin_eq (hR e z hz)] at h1
      rw [(chartTarget e).isOpen.nhdsWithin_eq hz]
      exact h1
    refine ⟨ae_restrict_of_open_neighborhood_ae fun z hz =>
      ⟨(R e z hz).W, (R e z hz).W.isOpen, hR e z hz, hfinW z hz⟩, hloc, ?_⟩
    apply distribution_eq_of_restrict_eq
      (fun p : (chartTarget e : Set (ComplexModel (m + 1))) => (R e p.1 p.2).W)
      (fun p => (R e p.1 p.2).hW)
    · intro z hz
      exact ⟨⟨z, hz⟩, hR e z hz⟩
    · intro p
      rw [(R e p.1 p.2).restrict_eq, restrictDistribution_regularDistribution μ hloc]
      exact regularDistribution_congr_ae_on _ _ (htoReal p.1 p.2)
  have hnd : LocallyNondegenerate V := by
    intro x U hU hxU
    set d := complexChartAt (n := m + 1) x with hddef
    have hO : IsOpen (d.val '' (d.val.source ∩ U)) := d.val.isOpen_image_source_inter hU
    have hsub : d.val '' (d.val.source ∩ U) ⊆ (chartTarget d : Set (ComplexModel (m + 1))) := by
      rintro _ ⟨y, hy, rfl⟩
      exact d.val.map_source hy.1
    have hpos : μ.restrict (chartTarget d) (d.val '' (d.val.source ∩ U)) ≠ 0 := by
      rw [Measure.restrict_apply' (chartTarget d).isOpen.measurableSet, inter_eq_left.mpr hsub]
      exact (hO.measure_pos μ ⟨d.val x, x, ⟨mem_complexChartAt_source x, hxU⟩, rfl⟩).ne'
    obtain ⟨_, ⟨y, hy, rfl⟩, hfin⟩ :=
      Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae (hchart d).1)
    refine ⟨y, hy.2, ?_⟩
    have hVy : chartFunction V d (d.val y) = V y := by
      simp only [chartFunction, d.val.left_inv hy.1]
    rw [← hVy]
    exact hfin.2
  exact ⟨V, ⟨hpsh, hnd⟩, hchart⟩


/-- The actual glued potential gives a genuine Kähler current with the prescribed class and lower bound. -/
theorem exists_kahlerCurrent_of_isCoordinateCompatible
    (μ : Measure (ComplexModel (m + 1))) [μ.IsAddHaarMeasure]
    (θ₀ : ClosedRealOneOneForm (m + 1) M) (ωδ : KahlerBackground (m + 1) M)
    (U : ∀ e : ComplexChart (m + 1) M, 𝓓'(chartTarget e, ℝ))
    (hU : IsCoordinateCompatible U)
    (hLevi : ∀ e, IsLocallyThetaPshDistribution μ (θ₀ - ωδ.form).val e (U e)) :
    ∃ K : NonKahlerLocus.KahlerCurrent (RealBottChern.ofRepresentative θ₀),
      K.representative = θ₀ ∧ K.lowerBound = ωδ ∧ ∀ e : ComplexChart (m + 1) M,
        ∃ hV : LocallyIntegrableOn (fun z => (chartFunction K.potential e z).toReal)
          (chartTarget e) μ,
          U e = regularDistribution μ (fun z => (chartFunction K.potential e z).toReal) hV := by
  obtain ⟨V, hV, hrep⟩ := exists_isThetaPshPotential_of_isCoordinateCompatible μ U hU hLevi
  exact ⟨⟨θ₀, rfl, V, ωδ, hV⟩, rfl, rfl, fun e => (hrep e).2⟩

end

end SGPT.Foundations.Analysis.Pending.XiaoCompatibleGlobalPotential
