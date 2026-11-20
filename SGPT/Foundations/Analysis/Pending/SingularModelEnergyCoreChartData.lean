import SGPT.Foundations.Analysis.Pending.FiniteGeodesicStripCharts
import SGPT.Foundations.Analysis.Pending.CompactAffineCurveCharts
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback
import SGPT.Foundations.Analysis.LocalPshDiscControl

set_option autoImplicit false

/-!
# Genuine product-core local potentials and Borel joint representatives

Independent localization of Xia SGPT PDF0171's actual compact extension.
The complete pulled-back two-form identity and actual zero vertical tensor
produce the joint PSH representatives. Their zero extensions are globally
Borel, including singular poles; coordinate identities follow from actual
product inverse charts and the genuine compact extension's core equality.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyCoreChartData

open scoped ProductComplexManifold
open FirstPass FirstPass.HolomorphicMaps FirstPass.LocalPotentialPullback
  ProductComplexManifold CompactAffineCurveCharts GlobalSlotStokes
  FiniteGeodesicMaximality BedfordTaylorStripCovariance BedfordTaylorFibreSlicing

noncomputable section

/-- A genuine local PSH function has a globally Borel zero extension which preserves every germ in its open domain. -/
theorem measurable_and_plurisubharmonic_indicator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [MeasurableSpace E] [BorelSpace E] {A : Set E} {u : E → EReal}
    (hA : IsOpen A) (hu : PlurisubharmonicOn u A) :
    Measurable (A.indicator u) ∧ PlurisubharmonicOn (A.indicator u) A := by
  classical
  have hsc : UpperSemicontinuousOn (fun x : A => u x) univ :=
    hu.upperSemicontinuousOn.comp continuous_subtype_val.continuousOn
      (fun x _ => x.property)
  have hm : Measurable (fun x : A => u x) :=
    (upperSemicontinuousOn_univ_iff.mp hsc).measurable
  refine ⟨measurable_of_restrict_of_restrict_compl hA.measurableSet ?_ ?_, ?_⟩
  · convert hm using 1
    funext x
    simp [Set.domRestrict, x.property]
  · have hzero : Aᶜ.domRestrict (A.indicator u) = fun _ : (Aᶜ : Set E) => (0 : EReal) := by
      funext x
      exact Set.indicator_of_notMem x.property _
    rw [hzero]
    exact measurable_const
  · intro x hx
    apply (hu x hx).congr
    filter_upwards [hA.mem_nhds hx] with y hy
    exact (Set.indicator_of_mem hy u).symm

variable {n : ℕ} {M T : Type*}
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace T] [ChartedSpace (ComplexModel 1) T] [IsComplexManifold 1 T]

/-- The actual product atlas chart, with the genuine Euclidean summed-dimension model. -/
def productComplexChart (a : ComplexChart n M) (e : ComplexChart 1 T) :
    ComplexChart (n + 1) (M × T) :=
  ⟨prodChart a.val e.val, mem_image2_of_mem a.property e.property⟩

/-- The true raw complex curve-chart domain above an open core. -/
def coreTimeDomain (e : ComplexChart 1 T) (N : Opens T) : Opens ℂ :=
  ⟨curveModelEquiv.symm ⁻¹' (e.val.target ∩ e.val.symm ⁻¹' (N : Set T)),
    (e.val.isOpen_inter_preimage_symm N.isOpen).preimage curveModelEquiv.symm.continuous⟩

private theorem stripFst_eq_prodFst (q : ComplexModel (n + 1)) :
    stripFst n q = ((prodModelEquiv n 1).symm q).1 := rfl

private theorem curve_snd_eq_prodSnd (q : ComplexModel (n + 1)) :
    curveModelEquiv.symm ((stripModelEquiv n q).2) =
      ((prodModelEquiv n 1).symm q).2 := by
  change curveModelEquiv.symm (curveModelEquiv (((prodModelEquiv n 1).symm q).2)) = _
  exact curveModelEquiv.symm_apply_apply _

omit [IsComplexManifold 1 T] in
private theorem core_product_target {θ : ClosedRealOneOneForm n M}
    (J : SlotChart (fun _ : Fin n => θ) θ) (e : ComplexChart 1 T) (N : Opens T)
    {q : ComplexModel (n + 1)}
    (hq : q ∈ stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen) :
    q ∈ (productComplexChart J.chart e).val.target := by
  change q ∈ (prodChart J.chart.val e.val).target
  rw [prodChart_target]
  exact ⟨J.domain_le_target (stripFst_eq_prodFst q ▸ hq.1),
    curve_snd_eq_prodSnd q ▸ hq.2.1⟩

omit [IsComplexManifold 1 T] in
private theorem core_fst_coordinate {θ : ClosedRealOneOneForm n M}
    (J : SlotChart (fun _ : Fin n => θ) θ) (e : ComplexChart 1 T) (N : Opens T)
    {q : ComplexModel (n + 1)}
    (hq : q ∈ stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen) :
    coordinateMap (Prod.fst : M × T → M) (productComplexChart J.chart e) J.chart q =
      stripFst n q := by
  change J.chart.val (J.chart.val.symm (((prodModelEquiv n 1).symm q).1)) = _
  rw [J.chart.val.right_inv (J.domain_le_target (stripFst_eq_prodFst q ▸ hq.1))]
  exact (stripFst_eq_prodFst q).symm

/-- The genuine zero vertical coefficient on the core and the full base pullback identity produce the actual product local potential, with no supplied joint PSH or local-potential certificate. -/
theorem isSmoothLocalPotential_core {θ : ClosedRealOneOneForm n M}
    (J : SlotChart (fun _ : Fin n => θ) θ) (e : ComplexChart 1 T) (N : Opens T)
    (κ : ClosedRealOneOneForm 1 T)
    (hκzero : ∀ z ∈ e.val.target, e.val.symm z ∈ N → κ.val.coeff e z = 0) :
    IsSmoothLocalPotential (prodForm θ κ).val (productComplexChart J.chart e)
      (stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen)
      (fun q => J.kahler (stripFst n q)) := by
  let A := stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen
  let P := productComplexChart J.chart e
  have htarget : (A : Set (ComplexModel (n + 1))) ⊆ P.val.target :=
    fun _ hq => core_product_target J e N hq
  have hfst (q : ComplexModel (n + 1)) (hq : q ∈ A) :
      q ∈ coordinateDomain (Prod.fst : M × T → M) P J.chart := by
    refine ⟨htarget hq, ?_⟩
    change J.chart.val.symm (((prodModelEquiv n 1).symm q).1) ∈ J.chart.val.source
    exact J.chart.val.map_target (J.domain_le_target (stripFst_eq_prodFst q ▸ hq.1))
  have hsub : (A : Set (ComplexModel (n + 1))) ⊆
      potentialDomain (Prod.fst : M × T → M) P J.chart J.domain := by
    intro q hq
    refine ⟨hfst q hq, ?_⟩
    change coordinateMap (Prod.fst : M × T → M) P J.chart q ∈ J.domain
    rw [core_fst_coordinate J e N hq]
    exact hq.1
  have hpull := (isSmoothLocalPotential_pullback contMDiff_fst P J.kahlerLocal).mono
    A.isOpen hsub
  have heq : EqOn (J.kahler ∘ coordinateMap (Prod.fst : M × T → M) P J.chart)
      (fun q => J.kahler (stripFst n q)) A := by
    intro q hq
    dsimp only [Function.comp_apply]
    rw [core_fst_coordinate J e N hq]
  refine ⟨A.isOpen, htarget, hpull.2.2.1.congr (fun q hq => (heq hq).symm), ?_⟩
  intro q hq
  have hsnd : q ∈ coordinateDomain (Prod.snd : M × T → T) P e := by
    refine ⟨htarget hq, ?_⟩
    change e.val.symm (((prodModelEquiv n 1).symm q).2) ∈ e.val.source
    exact e.val.map_target (curve_snd_eq_prodSnd q ▸ hq.2.1)
  have hcoord : coordinateMap (Prod.snd : M × T → T) P e q =
      ((prodModelEquiv n 1).symm q).2 := by
    change e.val (e.val.symm (((prodModelEquiv n 1).symm q).2)) = _
    exact e.val.right_inv (curve_snd_eq_prodSnd q ▸ hq.2.1)
  have hzero : (SmoothRealForm.pullback contMDiff_snd κ.val).coeff P q = 0 := by
    rw [SmoothRealForm.pullback_coeff contMDiff_snd κ.val P e hsnd, hcoord,
      hκzero _ (curve_snd_eq_prodSnd q ▸ hq.2.1) (curve_snd_eq_prodSnd q ▸ hq.2.2)]
    ext v
    rfl
  have hev : (J.kahler ∘ coordinateMap (Prod.fst : M × T → M) P J.chart) =ᶠ[𝓝 q]
      (fun q => J.kahler (stripFst n q)) := by
    filter_upwards [A.isOpen.mem_nhds hq] with w hw
    exact heq hw
  rw [← smoothDDC_congr hev, hpull.2.2.2 hq]
  change (SmoothRealForm.pullback contMDiff_fst θ.val).coeff P q =
    (prodForm θ κ).val.coeff P q
  rw [prodForm, ClosedRealOneOneForm.coeff_add]
  change _ = _ + (SmoothRealForm.pullback contMDiff_snd κ.val).coeff P q
  rw [hzero, add_zero]
  rfl

/-- The actual corrected compact-host potential on the product core, extended by zero off that true domain. -/
def coreChartPotential {θ : ClosedRealOneOneForm n M}
    (J : SlotChart (fun _ : Fin n => θ) θ) (e : ComplexChart 1 T) (N : Opens T)
    (W : M × T → EReal) : ComplexModel (n + 1) → EReal := by
  classical
  exact (stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen :
    Set (ComplexModel (n + 1))).indicator fun q =>
      chartFunction W (productComplexChart J.chart e) q + (J.kahler (stripFst n q) : EReal)

private theorem coreChartPotential_psh_measurable {θ : ClosedRealOneOneForm n M}
    (J : SlotChart (fun _ : Fin n => θ) θ) (e : ComplexChart 1 T) (N : Opens T)
    (κ : ClosedRealOneOneForm 1 T)
    (hκzero : ∀ z ∈ e.val.target, e.val.symm z ∈ N → κ.val.coeff e z = 0)
    {W : M × T → EReal} (hW : ThetaPlurisubharmonic (prodForm θ κ).val W) :
    Measurable (coreChartPotential J e N W) ∧
      PlurisubharmonicOn (coreChartPotential J e N W)
        (stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen) :=
  measurable_and_plurisubharmonic_indicator
    (stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen).isOpen
    (BoundedGlobalProduct.ThetaPlurisubharmonic.corrected_plurisubharmonicOn hW
      (productComplexChart J.chart e) (isSmoothLocalPotential_core J e N κ hκzero))

omit [IsComplexManifold 1 T] in
private theorem coreChartPotential_fibre_eq {θ : ClosedRealOneOneForm n M}
    (J : SlotChart (fun _ : Fin n => θ) θ) (e : ComplexChart 1 T) (N : Opens T)
    (W : M × T → EReal) {σ : ℂ} (hσ : σ ∈ coreTimeDomain e N)
    {y : ComplexModel n} (hy : y ∈ J.domain) :
    coreChartPotential J e N W (fibreMap n σ y) =
      W (J.chart.val.symm y, e.val.symm (curveModelEquiv.symm σ)) +
        (J.kahler y : EReal) := by
  classical
  have hf : fibreMap n σ y ∈
      stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen := by
    rw [mem_stripLift, stripFst_fibreMap, stripModelEquiv_fibreMap]
    exact ⟨hy, hσ⟩
  rw [coreChartPotential, Set.indicator_of_mem hf, stripFst_fibreMap]
  change W ((prodChart J.chart.val e.val).symm (fibreMap n σ y)) + _ = _
  rw [prodChart_symm_apply]
  have hfst : ((prodModelEquiv n 1).symm (fibreMap n σ y)).1 = y := by
    rw [← stripFst_eq_prodFst, stripFst_fibreMap]
  have hsnd : ((prodModelEquiv n 1).symm (fibreMap n σ y)).2 = curveModelEquiv.symm σ := by
    rw [← curve_snd_eq_prodSnd, stripModelEquiv_fibreMap]
  rw [hfst, hsnd]

/-- Genuine compact-host PSH and the actual core agreement internally produce both Borel joint PSH representatives and their exact fibre coordinate formulas, with common correction zero. -/
theorem core_joint_chart_data {θ : ClosedRealOneOneForm n M}
    (J : SlotChart (fun _ : Fin n => θ) θ) (e : ComplexChart 1 T) (N : Opens T)
    (κ : ClosedRealOneOneForm 1 T)
    (hκzero : ∀ z ∈ e.val.target, e.val.symm z ∈ N → κ.val.coeff e z = 0)
    {W : M × T → EReal} {φ : M → EReal}
    (hW : ThetaPlurisubharmonic (prodForm θ κ).val W)
    (hΦ : ThetaPlurisubharmonic (prodForm θ κ).val (fun p : M × T => φ p.1))
    (U : ℝ → M → EReal) (time : T → ℂ)
    (hcore : ∀ x y, y ∈ N → W (x, y) = U (time y).re x) :
    Measurable (coreChartPotential J e N W) ∧
    Measurable (coreChartPotential J e N (fun p : M × T => φ p.1)) ∧
    PlurisubharmonicOn (coreChartPotential J e N W)
      (stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen) ∧
    PlurisubharmonicOn (coreChartPotential J e N (fun p : M × T => φ p.1))
      (stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen) ∧
    ∀ σ ∈ coreTimeDomain e N, ∀ y ∈ J.domain,
      coreChartPotential J e N W (fibreMap n σ y) =
        chartFunction (U (time (e.val.symm (curveModelEquiv.symm σ))).re) J.chart y +
          (J.kahler y : EReal) + ((0 : ℝ) : EReal) ∧
      coreChartPotential J e N (fun p : M × T => φ p.1) (fibreMap n σ y) =
        chartFunction φ J.chart y + (J.kahler y : EReal) + ((0 : ℝ) : EReal) := by
  have hH := coreChartPotential_psh_measurable J e N κ hκzero hW
  have hF := coreChartPotential_psh_measurable J e N κ hκzero hΦ
  refine ⟨hH.1, hF.1, hH.2, hF.2, ?_⟩
  intro σ hσ y hy
  rw [coreChartPotential_fibre_eq J e N W hσ hy,
    coreChartPotential_fibre_eq J e N (fun p : M × T => φ p.1) hσ hy,
    hcore _ _ hσ.2]
  simp only [chartFunction, EReal.coe_zero, add_zero]
  trivial

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyCoreChartData
