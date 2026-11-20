import SGPT.Foundations.Analysis.Pending.SingularAffineTimeNonpluripolarZero
import SGPT.Foundations.Analysis.Pending.SingularModelEnergyCoreChartData
import SGPT.Foundations.Analysis.Pending.SingularReferenceChartStripZero
import SGPT.Foundations.Analysis.Pending.SingularPerronPreceqMixedZero

set_option autoImplicit false

/-! # Actual compact-product core patches have zero diagonal canonical NP measure -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.SingularProductCoreDiagonalZero

open scoped ProductComplexManifold
open FirstPass FirstPass.PositiveClasses FirstPass.GlobalPotentialPatches
  ProductComplexManifold CompactAffineCurveCharts GlobalSlotStokes
  FiniteGeodesicMaximality BedfordTaylorStripCovariance MixedNonPluripolar
  SingularAffineTimeNonpluripolarZero SingularModelEnergyCoreChartData
  SingularReferenceChartStripZero SingularPerronNonpluripolarZero
  RelativePreceqClasses

noncomputable section

variable {n : ℕ} {M T : Type*}
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace T] [ChartedSpace (ComplexModel 1) T] [IsComplexManifold 1 T]
  {θ : ClosedRealOneOneForm n M}

/-- Full zero vertical curvature and the actual base potential internally construct every diagonal compact-product patch field. -/
def coreDiagonalPatch (J : SlotChart (fun _ : Fin n => θ) θ) (e : ComplexChart 1 T)
    (N : Opens T) (κ : ClosedRealOneOneForm 1 T)
    (hκzero : ∀ z ∈ e.val.target, e.val.symm z ∈ N → κ.val.coeff e z = 0)
    {W : M × T → EReal} (hW : ThetaPlurisubharmonic (prodForm θ κ).val W) :
    Patch (fun _ : Fin (n + 1) => prodForm θ κ) (fun _ => W) where
  chart := productComplexChart J.chart e
  domain := stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen
  domain_le_target := (isSmoothLocalPotential_core J e N κ hκzero).2.1
  potential := fun _ q => J.kahler (stripFst n q)
  localPotential _ := isSmoothLocalPotential_core J e N κ hκzero
  plurisubharmonic _ := BoundedGlobalProduct.ThetaPlurisubharmonic.corrected_plurisubharmonicOn
    hW (productComplexChart J.chart e) (isSmoothLocalPotential_core J e N κ hκzero)

private theorem strip_product_model (z : ComplexModel n) (s : ComplexModel 1) :
    stripModelEquiv n (prodModelEquiv n 1 (z, s)) = (z, curveModelEquiv s) := by
  simp [stripModelEquiv, curveModelEquiv]

/-- The genuine diagonal patch source is exactly the actual base source times the true curve-chart core. -/
theorem mem_source_coreDiagonalPatch (J : SlotChart (fun _ : Fin n => θ) θ)
    (e : ComplexChart 1 T) (N : Opens T) (κ : ClosedRealOneOneForm 1 T)
    (hκzero : ∀ z ∈ e.val.target, e.val.symm z ∈ N → κ.val.coeff e z = 0)
    {W : M × T → EReal} (hW : ThetaPlurisubharmonic (prodForm θ κ).val W) (p : M × T) :
    p ∈ (coreDiagonalPatch J e N κ hκzero hW).source ↔
      p.1 ∈ J.source ∧ p.2 ∈ e.val.source ∧ p.2 ∈ N := by
  change p ∈ (prodChart J.chart.val e.val).source ∧
    (prodChart J.chart.val e.val) p ∈
      stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen ↔ _
  rw [prodChart_source, prodChart_apply]
  change (p.1 ∈ J.chart.val.source ∧ p.2 ∈ e.val.source) ∧
    stripModelEquiv n (prodModelEquiv n 1 (J.chart.val p.1, e.val p.2)) ∈
      (J.domain : Set (ComplexModel n)) ×ˢ (coreTimeDomain e N : Set ℂ) ↔ _
  rw [strip_product_model]
  change (p.1 ∈ J.chart.val.source ∧ p.2 ∈ e.val.source) ∧
    (J.chart.val p.1 ∈ J.domain ∧
      curveModelEquiv.symm (curveModelEquiv (e.val p.2)) ∈ e.val.target ∧
      e.val.symm (curveModelEquiv.symm (curveModelEquiv (e.val p.2))) ∈ N) ↔ _
  rw [curveModelEquiv.symm_apply_apply]
  constructor
  · rintro ⟨⟨hx, hy⟩, hxD, _, hyN⟩
    rw [e.val.left_inv hy] at hyN
    exact ⟨⟨hx, hxD⟩, hy, hyN⟩
  · rintro ⟨hx, hy, hyN⟩
    exact ⟨⟨hx.1, hy⟩, hx.2, e.val.map_source hy, (e.val.left_inv hy).symm ▸ hyN⟩

private theorem curve_snd_eq (q : ComplexModel (n + 1)) :
    curveModelEquiv.symm ((stripModelEquiv n q).2) = ((prodModelEquiv n 1).symm q).2 := by
  change curveModelEquiv.symm (curveModelEquiv (((prodModelEquiv n 1).symm q).2)) = _
  exact curveModelEquiv.symm_apply_apply _

omit [IsComplexManifold 1 T] in
private theorem product_inverse_eq (J : SlotChart (fun _ : Fin n => θ) θ)
    (e : ComplexChart 1 T) (q : ComplexModel (n + 1)) :
    (productComplexChart J.chart e).val.symm q =
      (J.chart.val.symm (stripFst n q),
        e.val.symm (curveModelEquiv.symm ((stripModelEquiv n q).2))) := by
  change (prodChart J.chart.val e.val).symm q = _
  rw [prodChart_symm_apply, curve_snd_eq]
  rfl

private theorem affine_curve_coordinate (z0 z : ComplexModel 1) (δ : ℝ) :
    curveModelEquiv (δ⁻¹ • (z - z0)) =
      δ⁻¹ • (curveModelEquiv z - curveModelEquiv z0) := by
  rfl

variable [CompactSpace M]

/-- Actual core agreement with the genuine Perron geodesic internally yields zero canonical NP measure of the actual compact-product diagonal patch. -/
theorem mixedTruncationLimitMeasure_core_perron_eq_zero
    (J : SlotChart (fun _ : Fin n => θ) θ) (e : ComplexChart 1 T) (N : Opens T)
    (κ : ClosedRealOneOneForm 1 T)
    (hκzero : ∀ z ∈ e.val.target, e.val.symm z ∈ N → κ.val.coeff e z = 0)
    {W : M × T → EReal} (hW : ThetaPlurisubharmonic (prodForm θ κ).val W)
    {u₀ u₁ : M → EReal}
    (hsub : IsSubgeodesicFrom θ.val (finiteGeodesic θ.val u₀ u₁) u₀ u₁)
    (z0 : ComplexModel 1) {δ : ℝ} (hδ : 0 < δ)
    (htime : ∀ y ∈ N, (curveModelEquiv (δ⁻¹ • (e.val y - z0))).re ∈ Ioo (0 : ℝ) 1)
    (hcore : ∀ x y, y ∈ N → W (x, y) =
      finiteGeodesic θ.val u₀ u₁ (curveModelEquiv (δ⁻¹ • (e.val y - z0))).re x) :
    mixedTruncationLimitMeasure (coreDiagonalPatch J e N κ hκzero hW).domain
      (coreDiagonalPatch J e N κ hκzero hW).corrected
      (coreDiagonalPatch J e N κ hκzero hW).plurisubharmonic = 0 := by
  let S := coreTimeDomain e N
  have ht (s : ℂ) (hs : s ∈ S) :
      (δ⁻¹ • (s - curveModelEquiv z0)).re ∈ Ioo (0 : ℝ) 1 := by
    have hh := htime (e.val.symm (curveModelEquiv.symm s)) hs.2
    rw [e.val.right_inv hs.1, affine_curve_coordinate, curveModelEquiv.apply_symm_apply] at hh
    exact hh
  let hp := plurisubharmonicOn_erealModel_affineTime hsub J.chart J.kahlerLocal S
    (curveModelEquiv z0) hδ ht
  have heq : ∀ i, EqOn ((coreDiagonalPatch J e N κ hκzero hW).corrected i)
      (fun q => erealModelChartFunction (finiteGeodesic θ.val u₀ u₁) J.chart J.kahler
        (affineTimeStripMap (curveModelEquiv z0) δ q))
      (coreDiagonalPatch J e N κ hκzero hW).domain := by
    intro i q hq
    change W ((productComplexChart J.chart e).val.symm q) + (J.kahler (stripFst n q) : EReal) = _
    rw [product_inverse_eq, hcore _ _ hq.2.2]
    rw [e.val.right_inv hq.2.1, affine_curve_coordinate, curveModelEquiv.apply_symm_apply]
    simp only [erealModelChartFunction, affineTimeStripMap,
      ContinuousLinearEquiv.apply_symm_apply, subgeodesicChartFunction, chartFunction]
    rfl
  have hP : ∀ i, PlurisubharmonicOn ((coreDiagonalPatch J e N κ hκzero hW).corrected i)
      (coreDiagonalPatch J e N κ hκzero hW).domain :=
    (coreDiagonalPatch J e N κ hκzero hW).plurisubharmonic
  exact (mixedTruncationLimitMeasure_congr hP (fun _ => hp) heq).trans
    (mixedTruncationLimitMeasure_erealModel_affineTime_eq_zero hsub J.chart J.kahlerLocal S
      (curveModelEquiv z0) hδ ht)

omit [CompactSpace M] in
/-- Actual base theta-PSH and genuine product-core corrections internally identify the reference diagonal patch with the real canonical base-only strip NP zero producer. -/
theorem mixedTruncationLimitMeasure_core_reference_eq_zero
    (J : SlotChart (fun _ : Fin n => θ) θ) (e : ComplexChart 1 T) (N : Opens T)
    (κ : ClosedRealOneOneForm 1 T)
    (hκzero : ∀ z ∈ e.val.target, e.val.symm z ∈ N → κ.val.coeff e z = 0)
    {φ : M → EReal} (hφ : ThetaPlurisubharmonic θ.val φ)
    (hΦ : ThetaPlurisubharmonic (prodForm θ κ).val (fun p : M × T => φ p.1)) :
    mixedTruncationLimitMeasure (coreDiagonalPatch J e N κ hκzero hΦ).domain
      (coreDiagonalPatch J e N κ hκzero hΦ).corrected
      (coreDiagonalPatch J e N κ hκzero hΦ).plurisubharmonic = 0 := by
  let hp := plurisubharmonicOn_corrected_reference_strip hφ J.chart J.kahlerLocal
    (coreTimeDomain e N).isOpen
  have heq : ∀ i, EqOn ((coreDiagonalPatch J e N κ hκzero hΦ).corrected i)
      (fun q => chartFunction φ J.chart (stripFst n q) + (J.kahler (stripFst n q) : EReal))
      (coreDiagonalPatch J e N κ hκzero hΦ).domain := by
    intro i q _
    change φ ((productComplexChart J.chart e).val.symm q).1 + _ = _
    rw [product_inverse_eq]
    rfl
  have hP : ∀ i, PlurisubharmonicOn ((coreDiagonalPatch J e N κ hκzero hΦ).corrected i)
      (coreDiagonalPatch J e N κ hκzero hΦ).domain :=
    (coreDiagonalPatch J e N κ hκzero hΦ).plurisubharmonic
  exact (mixedTruncationLimitMeasure_congr hP (fun _ => hp) heq).trans
    (mixedTruncationLimitMeasure_corrected_reference_strip_eq_zero hφ J.chart J.kahlerLocal
      (coreTimeDomain e N).isOpen)

variable [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M]

/-- Actual full singularity-order full-mass endpoints internally supply the true Perron subgeodesic needed for actual compact-core diagonal NP zero. -/
theorem mixedTruncationLimitMeasure_core_of_relativeFullMassPreceq_eq_zero
    (omega : KahlerBackground n M) {φ u₀ u₁ : M → EReal} {hφ : IsModelPotential θ φ}
    (hu₀ : RelativeFullMassPreceq θ φ u₀ hφ) (hu₁ : RelativeFullMassPreceq θ φ u₁ hφ)
    (J : SlotChart (fun _ : Fin n => θ) θ) (e : ComplexChart 1 T) (N : Opens T)
    (κ : ClosedRealOneOneForm 1 T)
    (hκzero : ∀ z ∈ e.val.target, e.val.symm z ∈ N → κ.val.coeff e z = 0)
    {W : M × T → EReal} (hW : ThetaPlurisubharmonic (prodForm θ κ).val W)
    (z0 : ComplexModel 1) {δ : ℝ} (hδ : 0 < δ)
    (htime : ∀ y ∈ N, (curveModelEquiv (δ⁻¹ • (e.val y - z0))).re ∈ Ioo (0 : ℝ) 1)
    (hcore : ∀ x y, y ∈ N → W (x, y) =
      finiteGeodesic θ.val u₀ u₁ (curveModelEquiv (δ⁻¹ • (e.val y - z0))).re x) :
    mixedTruncationLimitMeasure (coreDiagonalPatch J e N κ hκzero hW).domain
      (coreDiagonalPatch J e N κ hκzero hW).corrected
      (coreDiagonalPatch J e N κ hκzero hW).plurisubharmonic = 0 :=
  mixedTruncationLimitMeasure_core_perron_eq_zero J e N κ hκzero hW
    (finiteGeodesic_isSubgeodesicFrom_of_relativeFullMassPreceq omega hu₀ hu₁)
    z0 hδ htime hcore

end

end SGPT.Foundations.Analysis.Pending.SingularProductCoreDiagonalZero
