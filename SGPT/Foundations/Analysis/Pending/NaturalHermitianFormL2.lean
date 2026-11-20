import SGPT.Foundations.Analysis.Pending.NaturalHermitianVolumeMeasure
import SGPT.Foundations.Analysis.Pending.ProductTestForms
import SGPT.Foundations.Analysis.FirstPass.GeometricForms
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Algebra.Module.TransferInstance

set_option autoImplicit false

/-! # Actual Hermitian integral pairing and its separate original-form Hilbert completion

Complete mathematical statements and all nine proofs precede this SOURCE.
The original continuous alternating norms and smooth geometric uniformity
are preserved. Metric separation removes exactly invisible original chart
coefficient extensions; completeness belongs to the actual new completion.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianFormL2

open FirstPass NaturalHermitianSmoothFormMetric NaturalHermitianVolumeMeasure ProductTestForms

variable {n q : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual original form metric, read at the preferred original chart. -/
def pointwisePair (w : SmoothRealForm n M 2) (α β : SmoothRealForm n M q) (x : M) : ℝ :=
  let e := complexChartAt (n := n) x
  formMetricCoefficients w e (e.val x) q (α.coeff e (e.val x)) (β.coeff e (e.val x))

omit [MeasurableSpace M] [BorelSpace M] in
/-- Whole scalar readback in every original chart, proved from actual whole tensor transport. -/
theorem pointwisePair_chart (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (α β : SmoothRealForm n M q) (e : ComplexChart n M) (z : ComplexModel n)
    (hz : z ∈ e.val.target) :
    pointwisePair w α β (e.val.symm z) =
      formMetricCoefficients w e z q (α.coeff e z) (β.coeff e z) := by
  let x := e.val.symm z
  let f := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := e.val.map_target hz
  have hxf : x ∈ f.val.source := mem_complexChartAt_source x
  have hF : f.val x ∈ (chartTransition f e).source := by
    refine ⟨f.val.map_source hxf, ?_⟩
    change f.val.symm (f.val x) ∈ e.val.source
    rw [f.val.left_inv hxf]
    exact hx
  have htrans : chartTransition f e (f.val x) = z := by
    change e.val (f.val.symm (f.val x)) = z
    rw [f.val.left_inv hxf]
    exact e.val.right_inv hz
  have hα : α.coeff f (f.val x) =
      (α.coeff e z).compContinuousLinearMap (chartTransitionDerivative f e (f.val x)) := by
    ext v
    rw [α.compatible f e (f.val x) hF v, htrans]
    rfl
  have hβ : β.coeff f (f.val x) =
      (β.coeff e z).compContinuousLinearMap (chartTransitionDerivative f e (f.val x)) := by
    ext v
    rw [β.compatible f e (f.val x) hF v, htrans]
    rfl
  change formMetricCoefficients w f (f.val x) q (α.coeff f (f.val x))
    (β.coeff f (f.val x)) = _
  rw [hα, hβ, formMetricCoefficients_transport w hw f e (f.val x) hF, htrans]

omit [MeasurableSpace M] [BorelSpace M] in
/-- Actual original full operator smoothness gives genuine scalar chart smoothness. -/
theorem pointwisePair_chartSmooth (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (α β : SmoothRealForm n M q) : ChartSmooth (n := n) (pointwisePair w α β) := by
  intro e
  exact (((formMetricCoefficients_smooth w hw e q).clm_apply (α.smooth e)).clm_apply
    (β.smooth e)).congr (fun z hz => pointwisePair_chart w hw α β e z hz)

omit [MeasurableSpace M] [BorelSpace M] in
theorem pointwisePair_continuous (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (α β : SmoothRealForm n M q) : Continuous (pointwisePair w α β) :=
  ProductTestForms.ChartSmooth.continuous (pointwisePair_chartSmooth w hw α β)

omit [MeasurableSpace M] [BorelSpace M] in
theorem pointwisePair_symm (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (α β : SmoothRealForm n M q) (x : M) :
    pointwisePair w α β x = pointwisePair w β α x := by
  let e := complexChartAt (n := n) x
  exact (formMetricCoefficients_positive w hw e (e.val x)
    (e.val.map_source (mem_complexChartAt_source x)) q).1 _ _

omit [MeasurableSpace M] [BorelSpace M] in
theorem pointwisePair_add_left (w : SmoothRealForm n M 2)
    (α β γ : SmoothRealForm n M q) (x : M) :
    pointwisePair w (α + β) γ x = pointwisePair w α γ x + pointwisePair w β γ x := by
  simp only [pointwisePair, coeff_add, map_add, add_apply]

omit [MeasurableSpace M] [BorelSpace M] in
theorem pointwisePair_smul_left (w : SmoothRealForm n M 2) (c : ℝ)
    (α β : SmoothRealForm n M q) (x : M) :
    pointwisePair w (c • α) β x = c * pointwisePair w α β x := by
  simp only [pointwisePair, coeff_smul, map_smul, smul_apply, smul_eq_mul]

omit [MeasurableSpace M] [BorelSpace M] in
theorem pointwisePair_geometricallyEq (w : SmoothRealForm n M 2)
    {α α' β β' : SmoothRealForm n M q} (hα : α.GeometricallyEq α')
    (hβ : β.GeometricallyEq β') : pointwisePair w α β = pointwisePair w α' β' := by
  funext x
  let e := complexChartAt (n := n) x
  have hz : e.val x ∈ e.val.target := e.val.map_source (mem_complexChartAt_source x)
  change formMetricCoefficients w e (e.val x) q (α.coeff e (e.val x)) (β.coeff e (e.val x)) = _
  rw [hα e hz, hβ e hz]
  rfl

omit [MeasurableSpace M] [BorelSpace M] in
theorem pointwisePair_self_nonneg (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (α : SmoothRealForm n M q) (x : M) : 0 ≤ pointwisePair w α α x := by
  let e := complexChartAt (n := n) x
  let η := α.coeff e (e.val x)
  change 0 ≤ formMetricCoefficients w e (e.val x) q η η
  by_cases hη : η = 0
  · rw [hη, map_zero]
  · exact ((formMetricCoefficients_positive w hw e (e.val x)
      (e.val.map_source (mem_complexChartAt_source x)) q).2 η hη).le

omit [MeasurableSpace M] [BorelSpace M] in
theorem pointwisePair_self_eq_zero_iff (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (α : SmoothRealForm n M q) :
    (∀ x, pointwisePair w α α x = 0) ↔ α.GeometricallyEq 0 := by
  constructor
  · intro h e z hz
    change α.coeff e z = 0
    by_contra hα
    have hpos := (formMetricCoefficients_positive w hw e z hz q).2 (α.coeff e z) hα
    have hzero : formMetricCoefficients w e z q (α.coeff e z) (α.coeff e z) = 0 := by
      rw [← pointwisePair_chart w hw α α e z hz]
      exact h (e.val.symm z)
    exact hpos.ne' hzero
  · intro h x
    rw [pointwisePair_geometricallyEq w h h]
    simp only [pointwisePair, coeff_zero, map_zero]

section Compact

variable [CompactSpace M]

/-- Integrability comes from genuine continuity and internally produced finite original volume. -/
theorem pointwisePair_integrable (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (α β : SmoothRealForm n M q) : Integrable (pointwisePair w α β) (hermitianVolumeMeasure w hw) := by
  have : IsFiniteMeasure (hermitianVolumeMeasure w hw) := isFiniteMeasure_hermitianVolumeMeasure w hw
  exact (pointwisePair_continuous w hw α β).integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))

/-- The literal actual normalized Hermitian volume integral of the original form scalar. -/
def integralPair (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (α β : SmoothRealForm n M q) : ℝ :=
  ∫ x, pointwisePair w α β x ∂hermitianVolumeMeasure w hw

omit [CompactSpace M] in
theorem integralPair_symm (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (α β : SmoothRealForm n M q) : integralPair w hw α β = integralPair w hw β α :=
  integral_congr_ae (Eventually.of_forall (pointwisePair_symm w hw α β))

theorem integralPair_add_left (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (α β γ : SmoothRealForm n M q) :
    integralPair w hw (α + β) γ = integralPair w hw α γ + integralPair w hw β γ := by
  simp only [integralPair, pointwisePair_add_left]
  exact integral_add (pointwisePair_integrable w hw α γ) (pointwisePair_integrable w hw β γ)

omit [CompactSpace M] in
theorem integralPair_smul_left (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (c : ℝ)
    (α β : SmoothRealForm n M q) : integralPair w hw (c • α) β = c * integralPair w hw α β := by
  simp only [integralPair, pointwisePair_smul_left, integral_const_mul]

omit [CompactSpace M] in
theorem integralPair_self_nonneg (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (α : SmoothRealForm n M q) : 0 ≤ integralPair w hw α α :=
  integral_nonneg (pointwisePair_self_nonneg w hw α)

omit [CompactSpace M] in
theorem integralPair_geometricallyEq (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    {α α' β β' : SmoothRealForm n M q} (hα : α.GeometricallyEq α')
    (hβ : β.GeometricallyEq β') : integralPair w hw α β = integralPair w hw α' β' := by
  unfold integralPair
  rw [pointwisePair_geometricallyEq w hα hβ]

/-- True zero integral gives exactly original geometric zero, including arbitrary off-target extensions. -/
theorem integralPair_self_eq_zero_iff (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (α : SmoothRealForm n M q) : integralPair w hw α α = 0 ↔ α.GeometricallyEq 0 := by
  have : Measure.IsOpenPosMeasure (hermitianVolumeMeasure w hw) :=
    isOpenPosMeasure_hermitianVolumeMeasure w hw
  constructor
  · intro h
    have hae : pointwisePair w α α =ᵐ[hermitianVolumeMeasure w hw] 0 :=
      (integral_eq_zero_iff_of_nonneg (pointwisePair_self_nonneg w hw α)
        (pointwisePair_integrable w hw α α)).mp h
    have heq : pointwisePair w α α = 0 := Measure.eq_of_ae_eq hae
      (pointwisePair_continuous w hw α α) continuous_const
    exact (pointwisePair_self_eq_zero_iff w hw α).mp (congrFun heq)
  · intro h
    unfold integralPair
    have hp : pointwisePair w α α = 0 :=
      funext ((pointwisePair_self_eq_zero_iff w hw α).mpr h)
    simp only [hp, Pi.zero_apply, integral_zero]

/-- A separate nominal copy, leaving every original coefficient norm and smooth topology intact. -/
structure NominalL2Form (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (q : ℕ) where
  representative : SmoothRealForm n M q

/-- The literal field bijection used only to transfer the original vector-space operations. -/
def nominalRepresentativeEquiv (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (q : ℕ) :
    NominalL2Form w hw q ≃ SmoothRealForm n M q where
  toFun := NominalL2Form.representative
  invFun := NominalL2Form.mk
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

instance nominalAddCommGroup (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (q : ℕ) :
    AddCommGroup (NominalL2Form w hw q) := (nominalRepresentativeEquiv w hw q).addCommGroup

instance nominalModule (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (q : ℕ) :
    Module ℝ (NominalL2Form w hw q) := (nominalRepresentativeEquiv w hw q).module ℝ

/-- The genuine original integral internally supplies every field of a real pre-inner-product core. -/
@[instance_reducible] def nominalPreInnerProductCore
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (q : ℕ) :
    PreInnerProductSpace.Core ℝ (NominalL2Form w hw q) where
  inner x y := integralPair w hw x.representative y.representative
  conj_inner_symm x y := by
    change integralPair w hw y.representative x.representative =
      integralPair w hw x.representative y.representative
    exact integralPair_symm w hw y.representative x.representative
  re_inner_nonneg x := integralPair_self_nonneg w hw x.representative
  add_left x y z := by
    change integralPair w hw (x.representative + y.representative) z.representative = _
    exact integralPair_add_left w hw x.representative y.representative z.representative
  smul_left x y c := by
    change integralPair w hw (c • x.representative) y.representative =
      c * integralPair w hw x.representative y.representative
    exact integralPair_smul_left w hw c x.representative y.representative

instance nominalSeminormedAddCommGroup (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (q : ℕ) :
    SeminormedAddCommGroup (NominalL2Form w hw q) := by
  let _ : PreInnerProductSpace.Core ℝ (NominalL2Form w hw q) := nominalPreInnerProductCore w hw q
  exact InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ) (F := NominalL2Form w hw q)

instance nominalNormedSpace (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (q : ℕ) :
    NormedSpace ℝ (NominalL2Form w hw q) := by
  let _ : PreInnerProductSpace.Core ℝ (NominalL2Form w hw q) := nominalPreInnerProductCore w hw q
  exact InnerProductSpace.Core.toNormedSpace (𝕜 := ℝ) (F := NominalL2Form w hw q)

instance nominalInnerProductSpace (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (q : ℕ) :
    InnerProductSpace ℝ (NominalL2Form w hw q) :=
  InnerProductSpace.ofCore (nominalPreInnerProductCore w hw q)

theorem nominal_inner (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (x y : NominalL2Form w hw q) :
    inner ℝ x y = integralPair w hw x.representative y.representative := rfl

theorem nominal_norm_sq (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (x : NominalL2Form w hw q) :
    ‖x‖ ^ 2 = integralPair w hw x.representative x.representative := by
  rw [← real_inner_self_eq_norm_sq, nominal_inner]

theorem nominal_norm (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (x : NominalL2Form w hw q) :
    ‖x‖ = Real.sqrt (integralPair w hw x.representative x.representative) := rfl

theorem nominal_norm_eq_zero_iff (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (x : NominalL2Form w hw q) : ‖x‖ = 0 ↔ x.representative.GeometricallyEq 0 := by
  rw [← sq_eq_zero_iff, nominal_norm_sq, integralPair_self_eq_zero_iff]

/-- The actual separated normed space; only the new nominal metric is separated. -/
abbrev SeparatedFormL2 (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (q : ℕ) :=
  SeparationQuotient (NominalL2Form w hw q)

def toSeparatedFormL2 (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (α : SmoothRealForm n M q) : SeparatedFormL2 w hw q :=
  SeparationQuotient.mk (NominalL2Form.mk α)

/-- The actual separated inclusion is linear on the original smooth-form vector space. -/
def toSeparatedFormL2Linear (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (q : ℕ) :
    SmoothRealForm n M q →ₗ[ℝ] SeparatedFormL2 w hw q where
  toFun := toSeparatedFormL2 w hw
  map_add' α β := by
    change SeparationQuotient.mk ((NominalL2Form.mk α : NominalL2Form w hw q) +
      NominalL2Form.mk β) = _
    exact SeparationQuotient.mk_add (NominalL2Form.mk α : NominalL2Form w hw q)
      (NominalL2Form.mk β : NominalL2Form w hw q)
  map_smul' c α := by
    change SeparationQuotient.mk (c • (NominalL2Form.mk α : NominalL2Form w hw q)) = _
    exact SeparationQuotient.mk_smul c (NominalL2Form.mk α : NominalL2Form w hw q)

theorem toSeparatedFormL2Linear_apply (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (α : SmoothRealForm n M q) : toSeparatedFormL2Linear w hw q α = toSeparatedFormL2 w hw α := rfl

theorem separated_inner (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (α β : SmoothRealForm n M q) :
    inner ℝ (toSeparatedFormL2 w hw α) (toSeparatedFormL2 w hw β) = integralPair w hw α β := rfl

theorem separated_norm_sq (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (α : SmoothRealForm n M q) : ‖toSeparatedFormL2 w hw α‖ ^ 2 = integralPair w hw α α := by
  rw [← real_inner_self_eq_norm_sq, separated_inner]

/-- Metric separation identifies exactly the existing original geometric coefficient equality. -/
theorem toSeparatedFormL2_eq_iff (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (α β : SmoothRealForm n M q) :
    toSeparatedFormL2 w hw α = toSeparatedFormL2 w hw β ↔ α.GeometricallyEq β := by
  rw [toSeparatedFormL2, toSeparatedFormL2, SeparationQuotient.mk_eq_mk,
    Metric.inseparable_iff, dist_eq_norm, nominal_norm_eq_zero_iff]
  change (α - β).GeometricallyEq 0 ↔ α.GeometricallyEq β
  constructor
  · intro h e z hz
    have hz' := h e hz
    simpa only [coeff_sub, coeff_zero, sub_eq_zero] using hz'
  · intro h e z hz
    change α.coeff e z - β.coeff e z = 0
    exact sub_eq_zero.mpr (h e hz)

theorem toSeparatedFormL2_surjective (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (q : ℕ) :
    Function.Surjective (toSeparatedFormL2 (q := q) w hw) := by
  intro x
  obtain ⟨r, rfl⟩ := SeparationQuotient.surjective_mk x
  exact ⟨r.representative, rfl⟩

/-- Genuine bijection with the earlier original geometric quotient, without replacing its topology. -/
def geometricSeparatedEquiv (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (q : ℕ) :
    GeometricRealForm n M q ≃ SeparatedFormL2 w hw q := by
  let f : GeometricRealForm n M q → SeparatedFormL2 w hw q :=
    Quotient.lift (s := SmoothRealForm.geometricSetoid) (toSeparatedFormL2 w hw)
      (fun α β h => (toSeparatedFormL2_eq_iff w hw α β).mpr h)
  apply Equiv.ofBijective f
  constructor
  · intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro α β h
    exact Quotient.sound ((toSeparatedFormL2_eq_iff w hw α β).mp h)
  · intro x
    obtain ⟨α, hα⟩ := toSeparatedFormL2_surjective w hw q x
    exact ⟨GeometricRealForm.ofRepresentative α, hα⟩

theorem geometricSeparatedEquiv_ofRepresentative (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (α : SmoothRealForm n M q) :
    geometricSeparatedEquiv w hw q (GeometricRealForm.ofRepresentative α) =
      toSeparatedFormL2 w hw α := rfl

/-- The actual new real Hilbert completion of the genuine original separated form norm. -/
abbrev HilbertFormL2 (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (q : ℕ) :=
  UniformSpace.Completion (SeparatedFormL2 w hw q)

def toHilbertFormL2 (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (α : SmoothRealForm n M q) : HilbertFormL2 w hw q := ↑(toSeparatedFormL2 w hw α)

def toHilbertFormL2Linear (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (q : ℕ) :
    SmoothRealForm n M q →ₗ[ℝ] HilbertFormL2 w hw q :=
  UniformSpace.Completion.toComplL.toLinearMap.comp (toSeparatedFormL2Linear w hw q)

theorem toHilbertFormL2Linear_apply (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (α : SmoothRealForm n M q) : toHilbertFormL2Linear w hw q α = toHilbertFormL2 w hw α := rfl

theorem hilbert_complete (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (q : ℕ) :
    CompleteSpace (HilbertFormL2 w hw q) := inferInstance

theorem hilbert_inner (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (α β : SmoothRealForm n M q) :
    inner ℝ (toHilbertFormL2 w hw α) (toHilbertFormL2 w hw β) = integralPair w hw α β := by
  rw [toHilbertFormL2, toHilbertFormL2, UniformSpace.Completion.inner_coe, separated_inner]

theorem hilbert_norm_sq (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (α : SmoothRealForm n M q) : ‖toHilbertFormL2 w hw α‖ ^ 2 = integralPair w hw α α := by
  rw [← real_inner_self_eq_norm_sq, hilbert_inner]

theorem toHilbertFormL2_eq_iff (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (α β : SmoothRealForm n M q) :
    toHilbertFormL2 w hw α = toHilbertFormL2 w hw β ↔ α.GeometricallyEq β := by
  rw [toHilbertFormL2, toHilbertFormL2,
    (UniformSpace.Completion.coe_injective _).eq_iff, toSeparatedFormL2_eq_iff]

/-- The dense native completion image consists precisely of genuine original smooth-form classes. -/
theorem toHilbertFormL2_denseRange (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (q : ℕ) :
    DenseRange (toHilbertFormL2 (q := q) w hw) := by
  have hrange : range (toHilbertFormL2 (q := q) w hw) =
      range ((↑) : SeparatedFormL2 w hw q → HilbertFormL2 w hw q) := by
    ext x
    constructor
    · rintro ⟨α, rfl⟩
      exact ⟨toSeparatedFormL2 w hw α, rfl⟩
    · rintro ⟨r, rfl⟩
      obtain ⟨α, rfl⟩ := toSeparatedFormL2_surjective w hw q r
      exact ⟨α, rfl⟩
  change Dense (range (toHilbertFormL2 (q := q) w hw))
  rw [hrange]
  exact UniformSpace.Completion.denseRange_coe

end Compact

end SGPT.Foundations.Analysis.Pending.NaturalHermitianFormL2
