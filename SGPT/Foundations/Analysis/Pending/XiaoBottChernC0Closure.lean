import SGPT.Foundations.Analysis.Pending.XiaoFormC0Topology
import SGPT.Foundations.Analysis.Pending.XiaoClassNefDifference

set_option autoImplicit false

/-! # Actual directional C0 Bott-Chern quotient topology and Kähler cone closure -/

open Set Filter Topology
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.XiaoBottChernC0Closure

open FirstPass FirstPass.PositiveClasses XiaoFormC0Topology ProductTestForms
  MixedMassClassInvariance ManifoldTubePositivity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- The actual Bott-Chern quotient topology coinduced by the genuine directional C0 topology. -/
abbrev classC0Topology (w : KahlerBackground n M) : TopologicalSpace (RealBottChern n M) :=
  TopologicalSpace.coinduced RealBottChern.ofRepresentative (formC0Topology w)

/-- The actual Kähler cone is the actual quotient image of the genuine Kähler forms. -/
def actualKahlerCone : Set (RealBottChern n M) :=
  RealBottChern.ofRepresentative '' {θ : ClosedRealOneOneForm n M | θ.val.IsKahler}

/-- The actual quotient map is a genuine quotient map for the independently constructed C0 topology. -/
theorem isQuotientMap_ofRepresentative (w : KahlerBackground n M) :
    @IsQuotientMap (ClosedRealOneOneForm n M) (RealBottChern n M)
      (formC0Topology w) (classC0Topology w) RealBottChern.ofRepresentative := by
  let : TopologicalSpace (ClosedRealOneOneForm n M) := formC0Topology w
  let : TopologicalSpace (RealBottChern n M) := classC0Topology w
  refine ⟨⟨rfl⟩, fun α => ?_⟩
  exact ⟨Quotient.out α, Quotient.out_eq α⟩

/-- Actual linear quotient saturation and actual form translations make the actual C0 quotient map open. -/
theorem isOpenQuotientMap_ofRepresentative (w : KahlerBackground n M) :
    @IsOpenQuotientMap (ClosedRealOneOneForm n M) (RealBottChern n M)
      (formC0Topology w) (classC0Topology w) RealBottChern.ofRepresentative := by
  let : TopologicalSpace (ClosedRealOneOneForm n M) := formC0Topology w
  let : IsTopologicalAddGroup (ClosedRealOneOneForm n M) :=
    formC0Topology_isTopologicalAddGroup w
  let : TopologicalSpace (RealBottChern n M) := classC0Topology w
  exact AddMonoidHom.isOpenQuotientMap_of_isQuotientMap
    (φ := RealBottChern.ofRepresentativeLinearMap.toAddMonoidHom)
    (isQuotientMap_ofRepresentative w)

/-- Actual directional C0 Bott-Chern quotient topology is background independent. -/
theorem classC0Topology_eq_of_background (w w' : KahlerBackground n M) :
    classC0Topology w = classC0Topology w' := by
  rw [classC0Topology, classC0Topology, formC0Topology_eq_of_background w w']

/-- Actual quotient closure produces actual arbitrarily C0-close forms with a genuine Kähler representative. -/
theorem exists_kahler_near_representative_of_mem_closure (w : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M)
    (hθ : RealBottChern.ofRepresentative θ ∈
      @closure (RealBottChern n M) (classC0Topology w) actualKahlerCone)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η κ : ClosedRealOneOneForm n M,
      formC0Seminorm w (η - θ) < ε ∧ κ.val.IsKahler ∧
      ClosedRealOneOneForm.BottChernRel η κ := by
  let : TopologicalSpace (ClosedRealOneOneForm n M) := formC0Topology w
  let : TopologicalSpace (RealBottChern n M) := classC0Topology w
  let U : Set (ClosedRealOneOneForm n M) := (formC0Seminorm w).ball θ ε
  have hU : IsOpen U := isOpen_formC0Seminorm_ball w θ ε
  have hUθ : θ ∈ U := (formC0Seminorm w).mem_ball_self hε
  obtain ⟨α, ⟨η, hη, hηclass⟩, κ, hκ, hκclass⟩ :=
    mem_closure_iff.mp hθ (RealBottChern.ofRepresentative '' U)
      ((isOpenQuotientMap_ofRepresentative w).isOpenMap U hU)
      ⟨θ, hUθ, rfl⟩
  refine ⟨η, κ, hη, hκ, (RealBottChern.ofRepresentative_eq_iff η κ).mp ?_⟩
  exact hηclass.trans hκclass.symm

/-- Actual C0 Kähler cone closure yields the genuine smooth nef approximation of every actual representative. -/
theorem nefWithRespectTo_of_mem_closure_kahlerCone (w : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M)
    (hθ : RealBottChern.ofRepresentative θ ∈
      @closure (RealBottChern n M) (classC0Topology w) actualKahlerCone) :
    NefWithRespectTo w θ := by
  intro ε hε
  obtain ⟨η, κ, hnear, hκ, f, hf, heq⟩ :=
    exists_kahler_near_representative_of_mem_closure w θ hθ hε
  have herror := isSemipositive_sub_add_smul_of_formC0_lt w θ η hnear
  have hκsemi : κ.val.IsSemipositive := (KahlerBackground.isSemipositive ⟨κ, hκ⟩)
  refine ⟨f, hf, fun e z hz v => ?_⟩
  have h1 := hκsemi e z hz v
  have h2 := herror e z hz v
  rw [heq e z hz] at h1
  simp only [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add,
    ClosedRealOneOneForm.coeff_smul, ClosedRealOneOneForm.coeff_neg,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.neg_apply, smul_eq_mul] at h1 h2 ⊢
  linarith

/-- Genuine smooth nef approximation produces actual Kähler classes in every actual C0 quotient neighborhood. -/
theorem mem_closure_kahlerCone_of_nefWithRespectTo (w : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hθ : NefWithRespectTo w θ) :
    RealBottChern.ofRepresentative θ ∈
      @closure (RealBottChern n M) (classC0Topology w) actualKahlerCone := by
  let : TopologicalSpace (ClosedRealOneOneForm n M) := formC0Topology w
  let : TopologicalSpace (RealBottChern n M) := classC0Topology w
  apply mem_closure_iff.mpr
  intro U hU hUθ
  have hV : IsOpen (RealBottChern.ofRepresentative ⁻¹' U) :=
    hU.preimage (isOpenQuotientMap_ofRepresentative w).continuous
  obtain ⟨r, hr, hrU⟩ := exists_formC0Seminorm_ball_subset w hV hUθ
  have ht : 0 < r / 2 := half_pos hr
  obtain ⟨f, hf, hκ⟩ := XiaoNefPerturbation.exists_isKahler_of_nef w hθ ht
  let η : ClosedRealOneOneForm n M := θ + (r / 2) • w.form
  let κ : ClosedRealOneOneForm n M := η + ddcClosedForm f hf
  have hsmall : η ∈ (formC0Seminorm w).ball θ r := by
    change formC0Seminorm w (η - θ) < r
    have heq : η - θ = (r / 2) • w.form := by dsimp [η]; module
    rw [heq, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos ht]
    have hbg := formC0Seminorm_background_le_one w
    nlinarith [mul_le_mul_of_nonneg_left hbg ht.le]
  have hη : RealBottChern.ofRepresentative η ∈ U := hrU hsmall
  have hrel : ClosedRealOneOneForm.BottChernRel η κ := by
    refine ⟨f, hf, fun e z _ => ?_⟩
    rw [ClosedRealOneOneForm.coeff_add, ddcClosedForm_coeff]
  have hclass : RealBottChern.ofRepresentative η = RealBottChern.ofRepresentative κ :=
    (RealBottChern.ofRepresentative_eq_iff η κ).mpr hrel
  refine ⟨RealBottChern.ofRepresentative κ, ?_, κ, hκ, rfl⟩
  rwa [← hclass]

/-- Independently constructed actual C0 Kähler cone closure is exactly the genuine quotient smooth-nef predicate. -/
theorem mem_closure_kahlerCone_iff_classNef (w : KahlerBackground n M)
    (α : RealBottChern n M) :
    α ∈ @closure (RealBottChern n M) (classC0Topology w) actualKahlerCone ↔
      ClassNefWithRespectTo w α := by
  let θ : ClosedRealOneOneForm n M := Quotient.out α
  have hclass : RealBottChern.ofRepresentative θ = α := Quotient.out_eq α
  constructor
  · intro hα
    rw [← hclass]
    apply nefWithRespectTo_of_mem_closure_kahlerCone w θ
    rwa [hclass]
  · intro hα
    have hθ : NefWithRespectTo w θ := by
      change ClassNefWithRespectTo w (RealBottChern.ofRepresentative θ)
      rwa [hclass]
    have hclosure := mem_closure_kahlerCone_of_nefWithRespectTo w θ hθ
    rwa [hclass] at hclosure

/-- Xiao's numerical criterion consumes genuine directional C0 Kähler-cone closure of actual quotient classes. -/
theorem isBigClass_sub_of_C0closure_gap
    {m : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    [CompactSpace X] [PreconnectedSpace X] [MeasurableSpace X] [BorelSpace X]
    (w : KahlerBackground (m + 1) X) (α β : RealBottChern (m + 1) X)
    (hα : α ∈ @closure (RealBottChern (m + 1) X) (classC0Topology w) actualKahlerCone)
    (hβ : β ∈ @closure (RealBottChern (m + 1) X) (classC0Topology w) actualKahlerCone)
    (hgap : 0 < XiaoClassNefDifference.classTopIntersection w α -
      4 * (m + 1 : ℝ) * XiaoClassNefDifference.classOneSlotIntersection w α β) :
    NonKahlerLocus.IsBigClass (α - β) :=
  XiaoClassNefDifference.isBigClass_sub_of_classNef_gap w α β
    ((mem_closure_kahlerCone_iff_classNef w α).mp hα)
    ((mem_closure_kahlerCone_iff_classNef w β).mp hβ) hgap

end

end SGPT.Foundations.Analysis.Pending.XiaoBottChernC0Closure
