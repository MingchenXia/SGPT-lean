import SGPT.Foundations.Analysis.Pending.XiaoSmoothFormTopology
import SGPT.Foundations.Analysis.Pending.XiaoBottChernC0Closure

set_option autoImplicit false

/-! # Actual smooth coefficient-jet quotient and actual Kähler cone closure comparison -/

open Set Filter Topology
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.XiaoSmoothBottChernClosure

open FirstPass FirstPass.PositiveClasses XiaoSmoothFormTopology XiaoBottChernC0Closure
  ProductTestForms MixedMassClassInvariance ManifoldTubePositivity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- The actual smooth quotient is coinduced by all actual coefficient jets and the intrinsic C0 probe. -/
abbrev classSmoothTopology (w : KahlerBackground n M) : TopologicalSpace (RealBottChern n M) :=
  TopologicalSpace.coinduced RealBottChern.ofRepresentative (formSmoothTopology w)

/-- The actual smooth Bott-Chern quotient topology is independent of the actual Kähler background. -/
theorem classSmoothTopology_eq_of_background (w w' : KahlerBackground n M) :
    classSmoothTopology w = classSmoothTopology w' := by
  rw [classSmoothTopology, classSmoothTopology, formSmoothTopology_eq_of_background w w']

/-- The actual representative projection is an actual quotient map in the genuine smooth topology. -/
theorem isQuotientMap_ofRepresentative (w : KahlerBackground n M) :
    @IsQuotientMap (ClosedRealOneOneForm n M) (RealBottChern n M)
      (formSmoothTopology w) (classSmoothTopology w) RealBottChern.ofRepresentative := by
  let : TopologicalSpace (ClosedRealOneOneForm n M) := formSmoothTopology w
  let : TopologicalSpace (RealBottChern n M) := classSmoothTopology w
  refine ⟨⟨rfl⟩, fun α => ?_⟩
  exact ⟨Quotient.out α, Quotient.out_eq α⟩

/-- Actual form translations produce an actual open smooth quotient projection. -/
theorem isOpenQuotientMap_ofRepresentative (w : KahlerBackground n M) :
    @IsOpenQuotientMap (ClosedRealOneOneForm n M) (RealBottChern n M)
      (formSmoothTopology w) (classSmoothTopology w) RealBottChern.ofRepresentative := by
  let : TopologicalSpace (ClosedRealOneOneForm n M) := formSmoothTopology w
  let : IsTopologicalAddGroup (ClosedRealOneOneForm n M) :=
    formSmoothTopology_isTopologicalAddGroup w
  let : TopologicalSpace (RealBottChern n M) := classSmoothTopology w
  exact AddMonoidHom.isOpenQuotientMap_of_isQuotientMap
    (φ := RealBottChern.ofRepresentativeLinearMap.toAddMonoidHom)
    (isQuotientMap_ofRepresentative w)

/-- The actual smooth quotient controls the independently constructed actual directional C0 quotient. -/
theorem continuous_identity_to_classC0Topology (w : KahlerBackground n M) :
    Continuous[classSmoothTopology w, classC0Topology w]
      (id : RealBottChern n M → RealBottChern n M) := by
  let : TopologicalSpace (ClosedRealOneOneForm n M) := formSmoothTopology w
  let : TopologicalSpace (RealBottChern n M) := classC0Topology w
  apply continuous_coinduced_dom.mpr
  exact @Continuous.comp (ClosedRealOneOneForm n M) (ClosedRealOneOneForm n M)
    (RealBottChern n M) (formSmoothTopology w) (XiaoFormC0Topology.formC0Topology w)
    (classC0Topology w) id RealBottChern.ofRepresentative
    (continuous_coinduced_rng (f := RealBottChern.ofRepresentative)
      (t := XiaoFormC0Topology.formC0Topology w))
    (continuous_identity_to_formC0Topology w)

/-- Actual smooth Kähler cone closure gives actual directional C0 Kähler cone closure. -/
theorem mem_C0closure_of_mem_smoothClosure (w : KahlerBackground n M)
    (α : RealBottChern n M)
    (hα : α ∈ @closure (RealBottChern n M) (classSmoothTopology w) actualKahlerCone) :
    α ∈ @closure (RealBottChern n M) (classC0Topology w) actualKahlerCone :=
  @map_mem_closure (RealBottChern n M) (RealBottChern n M)
    (classSmoothTopology w) (classC0Topology w) id actualKahlerCone α actualKahlerCone
    (continuous_identity_to_classC0Topology w) hα (fun _ h => h)

/-- Genuine nef approximation produces actual Kähler classes in every actual smooth quotient neighborhood. -/
theorem mem_smoothClosure_of_nefWithRespectTo (w : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hθ : NefWithRespectTo w θ) :
    RealBottChern.ofRepresentative θ ∈
      @closure (RealBottChern n M) (classSmoothTopology w) actualKahlerCone := by
  let : TopologicalSpace (ClosedRealOneOneForm n M) := formSmoothTopology w
  let : IsTopologicalAddGroup (ClosedRealOneOneForm n M) :=
    formSmoothTopology_isTopologicalAddGroup w
  let : ContinuousSMul ℝ (ClosedRealOneOneForm n M) := formSmoothTopology_continuousSMul w
  let : TopologicalSpace (RealBottChern n M) := classSmoothTopology w
  have hline : Continuous (fun t : ℝ => θ + t • w.form) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hqline : Continuous (fun t : ℝ => RealBottChern.ofRepresentative (θ + t • w.form)) :=
    (isQuotientMap_ofRepresentative w).continuous.comp hline
  apply mem_closure_iff.mpr
  intro U hU hUθ
  have hV : IsOpen ((fun t : ℝ => RealBottChern.ofRepresentative (θ + t • w.form)) ⁻¹' U) :=
    hU.preimage hqline
  have hV0 : (0 : ℝ) ∈
      (fun t : ℝ => RealBottChern.ofRepresentative (θ + t • w.form)) ⁻¹' U := by
    simpa only [mem_preimage, zero_smul, add_zero] using hUθ
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hV 0 hV0
  have ht : 0 < r / 2 := half_pos hr
  have hη : RealBottChern.ofRepresentative (θ + (r / 2) • w.form) ∈ U := by
    apply hrV
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]
    exact half_lt_self hr
  obtain ⟨f, hf, hκ⟩ := XiaoNefPerturbation.exists_isKahler_of_nef w hθ ht
  let η : ClosedRealOneOneForm n M := θ + (r / 2) • w.form
  let κ : ClosedRealOneOneForm n M := η + ddcClosedForm f hf
  have hrel : ClosedRealOneOneForm.BottChernRel η κ := by
    refine ⟨f, hf, fun e z _ => ?_⟩
    rw [ClosedRealOneOneForm.coeff_add, ddcClosedForm_coeff]
  have hclass : RealBottChern.ofRepresentative η = RealBottChern.ofRepresentative κ :=
    (RealBottChern.ofRepresentative_eq_iff η κ).mpr hrel
  refine ⟨RealBottChern.ofRepresentative κ, ?_, κ, hκ, rfl⟩
  rwa [← hclass]

/-- The actual smooth Kähler cone closure is precisely genuine smooth nef approximation on actual classes. -/
theorem mem_smoothClosure_iff_classNef (w : KahlerBackground n M) (α : RealBottChern n M) :
    α ∈ @closure (RealBottChern n M) (classSmoothTopology w) actualKahlerCone ↔
      ClassNefWithRespectTo w α := by
  constructor
  · intro hα
    exact (mem_closure_kahlerCone_iff_classNef w α).mp
      (mem_C0closure_of_mem_smoothClosure w α hα)
  · intro hα
    let θ : ClosedRealOneOneForm n M := Quotient.out α
    have hclass : RealBottChern.ofRepresentative θ = α := Quotient.out_eq α
    have hθ : NefWithRespectTo w θ := by
      change ClassNefWithRespectTo w (RealBottChern.ofRepresentative θ)
      rwa [hclass]
    have hclosure := mem_smoothClosure_of_nefWithRespectTo w θ hθ
    rwa [hclass] at hclosure

/-- Actual smooth and actual directional C0 Kähler cone closures agree as actual sets of quotient classes. -/
theorem smoothClosure_eq_C0closure (w : KahlerBackground n M) :
    @closure (RealBottChern n M) (classSmoothTopology w) actualKahlerCone =
      @closure (RealBottChern n M) (classC0Topology w) actualKahlerCone := by
  ext α
  rw [mem_smoothClosure_iff_classNef, mem_closure_kahlerCone_iff_classNef]

/-- Xiao's actual numerical criterion consumes actual smooth Kähler cone closure of actual quotient classes. -/
theorem isBigClass_sub_of_smoothClosure_gap
    {m : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    [CompactSpace X] [PreconnectedSpace X] [MeasurableSpace X] [BorelSpace X]
    (w : KahlerBackground (m + 1) X) (α β : RealBottChern (m + 1) X)
    (hα : α ∈ @closure (RealBottChern (m + 1) X) (classSmoothTopology w) actualKahlerCone)
    (hβ : β ∈ @closure (RealBottChern (m + 1) X) (classSmoothTopology w) actualKahlerCone)
    (hgap : 0 < XiaoClassNefDifference.classTopIntersection w α -
      4 * (m + 1 : ℝ) * XiaoClassNefDifference.classOneSlotIntersection w α β) :
    NonKahlerLocus.IsBigClass (α - β) :=
  XiaoClassNefDifference.isBigClass_sub_of_classNef_gap w α β
    ((mem_smoothClosure_iff_classNef w α).mp hα)
    ((mem_smoothClosure_iff_classNef w β).mp hβ) hgap

end

end SGPT.Foundations.Analysis.Pending.XiaoSmoothBottChernClosure
