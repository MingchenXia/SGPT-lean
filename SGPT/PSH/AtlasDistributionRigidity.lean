import SGPT.PSH.ChartNullTransport
import SGPT.PSH.PlurifineManifold
import SGPT.PSH.DistributionRigidity
import SGPT.Foundations.Analysis.Pending.ActualUnboundedScalarCurrentPullback

set_option autoImplicit false

noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter MeasureTheory Metric
open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Distributions

variable {X : Type*} [TopologicalSpace X] (A : VariableComplexAtlas X)

/-- Actual coordinate representatives agree at every original overlap point.
Compatibility is proved from the original almost-everywhere function, genuine
null-set transport and pointwise PSH uniqueness; it is not supplied as a field. -/
theorem coordinateRepresentatives_compatible (u : X → EReal)
    (v : (i : A.Index) → ComplexModel (A.dimension i) → EReal)
    (hv : ∀ i, PlurisubharmonicOn (v i) (A.chart i).target)
    (hae : ∀ i, A.coordinate u i =ᵐ[volume.restrict (A.chart i).target] v i)
    {i j : A.Index} {x : X} (hi : x ∈ (A.chart i).source)
    (hj : x ∈ (A.chart j).source) : v i (A.chart i x) = v j (A.chart j x) := by
  let F := (A.chart i).symm.trans (A.chart j)
  have hF : DifferentiableOn ℂ F F.source := A.holomorphic i j
  have hG : DifferentiableOn ℂ F.symm F.target := by
    change DifferentiableOn ℂ F.symm F.symm.source
    simpa only [F, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm] using A.holomorphic j i
  have hFi : F.source ⊆ (A.chart i).target := fun _ hz ↦ hz.1
  have hFj : F.target ⊆ (A.chart j).target := fun _ hz ↦ hz.1
  have hai := ae_restrict_of_ae_restrict_of_subset hFi (hae i)
  have haj := ae_comp_of_variable_holomorphic_model_openPartial F hF hG
    (ae_restrict_of_ae_restrict_of_subset hFj (hae j))
  have heq : v i =ᵐ[volume.restrict F.source] fun z ↦ v j (F z) := by
    filter_upwards [hai, haj, ae_restrict_mem F.open_source.measurableSet] with z hiz hjz hz
    calc
      v i z = A.coordinate u i z := hiz.symm
      _ = A.coordinate u j (F z) := by
        change u ((A.chart i).symm z) =
          u ((A.chart j).symm ((A.chart j) ((A.chart i).symm z)))
        exact congrArg u ((A.chart j).left_inv hz.2).symm
      _ = v j (F z) := hjz
  have hleft := (hv i).mono hFi
  have hright : PlurisubharmonicOn (fun z ↦ v j (F z)) F.source :=
    Pending.HolomorphicPullback.plurisubharmonicOn_comp_holomorphic
      F.open_source hF (fun z hz ↦ (F.map_source hz).1) (hv j)
  have hx : A.chart i x ∈ F.source := by
    refine ⟨(A.chart i).map_source hi, ?_⟩
    change (A.chart i).symm (A.chart i x) ∈ (A.chart j).source
    simpa only [(A.chart i).left_inv hi] using hj
  have hp := hleft.eqOn_of_ae_eq hright F.open_source volume heq hx
  simpa only [F, OpenPartialHomeomorph.trans_apply, (A.chart i).left_inv hi] using hp

/-- Genuine original coordinate positivity, formulated with the actual
normalized full degree-two current in every original chart. -/
def HasPositiveDistributionDdc (u : X → EReal) : Prop :=
  ∀ i : A.Index, ∃ hL : SourceLocallyIntegrableOn volume
    (A.coordinate u i) (A.chart i).target,
    HasPositiveSourceDdc (regularDistribution (Ω := A.chartDomain i) volume
      (fun z ↦ (A.coordinate u i z).toReal) hL.2)

/-- Actual local distributional representatives are glued by the proved
overlap uniqueness, including empty charts and varying model dimensions. -/
theorem exists_psh_of_positive_distribution_ddc {u : X → EReal}
    (hpos : A.HasPositiveDistributionDdc u) :
    ∃ g : X → EReal, A.IsPSH g ∧ A.CoordinateAEEq u g := by
  classical
  choose hL hT using hpos
  have hrep (i : A.Index) := Pending.exists_pshRepresentative volume
    ((hasPositiveSourceDdc_iff_nonnegativeLevi _).mp (hT i))
  choose v hv hf hvL hvT using hrep
  have hae (i : A.Index) :
      A.coordinate u i =ᵐ[volume.restrict (A.chart i).target] v i := by
    have hr := ae_eq_of_regularDistribution_eq volume (hL i).2 (hvL i) (hvT i)
    filter_upwards [(hL i).1, hf i, hr] with z huz hvz heq
    rw [← EReal.coe_toReal huz.1 huz.2, ← EReal.coe_toReal hvz.1 hvz.2, heq]
  choose c hc using A.cover
  let g : X → EReal := fun x ↦ v (c x) (A.chart (c x) x)
  have hg (i : A.Index) : EqOn (A.coordinate g i) (v i) (A.chart i).target := by
    intro z hz
    have hi := (A.chart i).map_target hz
    have heq := A.coordinateRepresentatives_compatible u v hv hae
      (hc ((A.chart i).symm z)) hi
    simpa only [coordinate, g, Function.comp_apply, (A.chart i).right_inv hz] using heq
  have hraw (i : A.Index) : PlurisubharmonicOn (A.coordinate g i) (A.chart i).target := by
    intro z hz
    apply (hv i z hz).congr
    filter_upwards [(A.chart i).open_target.mem_nhds hz] with y hy
    exact (hg i hy).symm
  have hfinite (i : A.Index) :
      ∀ᵐ z ∂volume.restrict (A.chart i).target,
        A.coordinate g i z ≠ ⊤ ∧ A.coordinate g i z ≠ ⊥ := by
    filter_upwards [hf i, ae_restrict_mem (A.chart i).open_target.measurableSet] with z hz hzt
    simpa only [hg i hzt] using hz
  have hpsh : A.IsPSH g := by
    intro x
    obtain ⟨i, hi⟩ := A.cover x
    have hz := (A.chart i).map_source hi
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (A.chart i).open_target
      (A.chart i x) hz
    have hbfin := ae_restrict_of_ae_restrict_of_subset hball (hfinite i)
    obtain ⟨z, hzb, hzfin⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (isOpen_ball.measure_ne_zero volume ⟨A.chart i x, mem_ball_self hr⟩) hbfin
    exact ⟨i, hi, Metric.ball (A.chart i x) r, isOpen_ball, isConnected_ball hr,
      hball, mem_ball_self hr, (hraw i).discPshOn.mono hball, z, hzb, hzfin.2⟩
  refine ⟨g, hpsh, fun i ↦ ?_⟩
  filter_upwards [hae i, ae_restrict_mem (A.chart i).open_target.measurableSet] with z hz hzt
  exact hz.trans (hg i hzt).symm

/-- A genuine global source PSH function internally supplies coordinate L1 and
full current positivity. The given original function is recovered by actual
coordinate almost-everywhere equality, without changing its values at poles. -/
theorem IsPSH.positive_distribution_ddc_of_original_coordinate_ae {u v : X → EReal}
    (hv : A.IsPSH v) (hae : A.CoordinateAEEq u v) :
    A.HasPositiveDistributionDdc u := by
  intro i
  have hraw := hv.chartPlurisubharmonic i
  have hnd : ∀ z ∈ (A.chart i).target, ∀ W : Set (ComplexModel (A.dimension i)),
      IsOpen W → z ∈ W → ∃ y ∈ (A.chart i).target ∩ W,
        A.coordinate v i y ≠ ⊥ := by
    intro z hz W hW hzW
    exact LocallyNondegenerate.exists_coordinate_ne_bot hv.locallyNondegenerate
      (A.chart i) ((A.chart i).open_target.inter hW) inter_subset_left ⟨hz, hzW⟩
  obtain ⟨hvL, hvf, _hweak⟩ :=
    Pending.ActualUnboundedScalarCurrentPullback.exists_integrable_psh_truncation_currents
      (B := A.chartDomain i) hraw hnd
  have hreal : (fun z ↦ (A.coordinate u i z).toReal) =ᵐ[volume.restrict (A.chart i).target]
      (fun z ↦ (A.coordinate v i z).toReal) :=
    (hae i).mono (fun _ hx ↦ congrArg EReal.toReal hx)
  have huf : ∀ᵐ z ∂volume.restrict (A.chart i).target,
      A.coordinate u i z ≠ ⊤ ∧ A.coordinate u i z ≠ ⊥ := by
    filter_upwards [hvf, hae i] with z hz heq
    simpa only [heq] using hz
  have huL := hvL.congr hreal.symm
  refine ⟨⟨huf, huL⟩, ?_⟩
  apply (hasPositiveSourceDdc_iff_nonnegativeLevi _).mpr
  rw [regularDistribution_congr_ae_on huL hvL hreal]
  exact hraw.hasNonnegativeDistributionalLevi_of_locallyIntegrable hvL hvf

/-- The literal original manifold distribution rigidity, with genuine charts
whose dimensions may vary, and with every original negative pole retained. -/
theorem distribution_rigidity [MeasurableSpace X] [BorelSpace X] {u : X → EReal}
    (_hu : Measurable u) (_htop : ∀ x, u x ≠ ⊤) :
    A.HasPositiveDistributionDdc u ↔
      ∃ v : X → EReal, A.IsPSH v ∧ A.CoordinateAEEq u v := by
  constructor
  · exact A.exists_psh_of_positive_distribution_ddc
  · rintro ⟨v, hv, hae⟩
    exact hv.positive_distribution_ddc_of_original_coordinate_ae A hae

/-- The original manifold representative is pointwise unique, including poles,
empty manifolds and different dimensions on different connected components. -/
theorem IsPSH.eq_of_original_coordinate_ae {u v w : X → EReal}
    (hv : A.IsPSH v) (hw : A.IsPSH w)
    (huv : A.CoordinateAEEq u v) (huw : A.CoordinateAEEq u w) : v = w :=
  hv.eq_of_coordinateAEEq hw (fun i ↦ (huv i).symm.trans (huw i))

end SGPT.PSH.VariableComplexAtlas
