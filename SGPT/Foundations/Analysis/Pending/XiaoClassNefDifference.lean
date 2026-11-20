import SGPT.Foundations.Analysis.Pending.XiaoNefDifferenceCriterion

set_option autoImplicit false

/-! # Genuine quotient intersection numbers and Xiao's actual class nef difference criterion -/

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.XiaoClassNefDifference

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses NonKahlerLocus
  NefMixedMass MixedMassClassInvariance ManifoldTubePositivity IntegrationCurrent TopDegreeDensity
  XiaoNefDifferenceCriterion

noncomputable section

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- Genuine simultaneous actual Bott-Chern relations preserve the actual smooth slot integral. -/
theorem slotIntegral_eq_of_bottChernRel (w : KahlerBackground (m + 1) M)
    (θ η : Fin (m + 1) → ClosedRealOneOneForm (m + 1) M)
    (hrel : ∀ i, ClosedRealOneOneForm.BottChernRel (θ i) (η i)) :
    slotIntegral w η = slotIntegral w θ := by
  choose f hf heq using hrel
  have hpt : ∀ x, topRatio w.form.val (slotForm η) x =
      topRatio w.form.val (slotForm (fun i => θ i + ddcClosedForm (f i) (hf i))) x := by
    intro x
    let e := complexChartAt (n := m + 1) x
    let z := e.val x
    have hz : z ∈ e.val.target := e.val.map_source (mem_complexChartAt_source x)
    have hcoeff : (fun i => (η i).val.coeff e z) =
        fun i => (θ i + ddcClosedForm (f i) (hf i)).val.coeff e z := by
      funext i
      rw [ClosedRealOneOneForm.coeff_add, ddcClosedForm_coeff]
      exact heq i e z hz
    change chartRatio w.form.val (slotForm η) e z =
      chartRatio w.form.val (slotForm (fun i => θ i + ddcClosedForm (f i) (hf i))) e z
    simp only [chartRatio, topDensity_slotForm_coeff]
    rw [hcoeff]
  calc slotIntegral w η = slotIntegral w (fun i => θ i + ddcClosedForm (f i) (hf i)) :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = slotIntegral w θ := slotIntegral_add_ddc w θ f hf

/-- The actual real class slot number is computed from actual quotient representatives. -/
def classSlotIntegral (w : KahlerBackground (m + 1) M)
    (α : Fin (m + 1) → RealBottChern (m + 1) M) : ℝ :=
  slotIntegral w (fun i => Quotient.out (α i))

/-- Actual Bott-Chern descent gives the genuine representative formula for class slot numbers. -/
theorem classSlotIntegral_ofRepresentative (w : KahlerBackground (m + 1) M)
    (θ : Fin (m + 1) → ClosedRealOneOneForm (m + 1) M) :
    classSlotIntegral w (fun i => RealBottChern.ofRepresentative (θ i)) = slotIntegral w θ := by
  change slotIntegral w (fun i => Quotient.out (RealBottChern.ofRepresentative (θ i))) =
    slotIntegral w θ
  apply slotIntegral_eq_of_bottChernRel
  intro i
  apply (RealBottChern.ofRepresentative_eq_iff _ _).mp
  exact (Quotient.out_eq (RealBottChern.ofRepresentative (θ i))).symm

/-- The actual class slot number agrees with every actual representative tuple. -/
theorem classSlotIntegral_eq_of_representatives (w : KahlerBackground (m + 1) M)
    (α : Fin (m + 1) → RealBottChern (m + 1) M)
    (θ : Fin (m + 1) → ClosedRealOneOneForm (m + 1) M)
    (hθ : ∀ i, RealBottChern.ofRepresentative (θ i) = α i) :
    classSlotIntegral w α = slotIntegral w θ := by
  have hclass : α = fun i => RealBottChern.ofRepresentative (θ i) :=
    funext fun i => (hθ i).symm
  rw [hclass, classSlotIntegral_ofRepresentative]

/-- Actual class slot intersections are independent of the actual Kähler background. -/
theorem classSlotIntegral_eq_of_background (w w' : KahlerBackground (m + 1) M)
    (α : Fin (m + 1) → RealBottChern (m + 1) M) :
    classSlotIntegral w' α = classSlotIntegral w α :=
  UniformNefCoreSupport.slotIntegral_eq_of_background w w' (fun i => Quotient.out (α i))

/-- The actual top class intersection. -/
def classTopIntersection (w : KahlerBackground (m + 1) M)
    (α : RealBottChern (m + 1) M) : ℝ := classSlotIntegral w (fun _ => α)

/-- The actual class intersection with one beta slot and all remaining alpha slots. -/
def classOneSlotIntersection (w : KahlerBackground (m + 1) M)
    (α β : RealBottChern (m + 1) M) : ℝ :=
  classSlotIntegral w (Fin.cons β (fun _ : Fin m => α))

/-- The actual top class intersection is precisely the actual representative top slot integral. -/
theorem classTopIntersection_ofRepresentative (w : KahlerBackground (m + 1) M)
    (A : ClosedRealOneOneForm (m + 1) M) :
    classTopIntersection w (RealBottChern.ofRepresentative A) = slotIntegral w (fun _ => A) :=
  classSlotIntegral_ofRepresentative w (fun _ => A)

/-- The actual one-slot class intersection is precisely the actual representative mixed slot integral. -/
theorem classOneSlotIntersection_ofRepresentative (w : KahlerBackground (m + 1) M)
    (A B : ClosedRealOneOneForm (m + 1) M) :
    classOneSlotIntersection w (RealBottChern.ofRepresentative A) (RealBottChern.ofRepresentative B) =
      slotIntegral w (Fin.cons B (fun _ : Fin m => A)) := by
  change classSlotIntegral w (Fin.cons (RealBottChern.ofRepresentative B)
    (fun _ : Fin m => RealBottChern.ofRepresentative A)) = _
  have hfamily : Fin.cons (RealBottChern.ofRepresentative B)
      (fun _ : Fin m => RealBottChern.ofRepresentative A) =
      fun i => RealBottChern.ofRepresentative
        ((Fin.cons B (fun _ : Fin m => A) :
          Fin (m + 1) → ClosedRealOneOneForm (m + 1) M) i) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [hfamily, classSlotIntegral_ofRepresentative]

variable [PreconnectedSpace M]

/-- Xiao's strict numerical criterion for actual nef quotient classes yields a genuine Kähler current. -/
theorem isBigClass_sub_of_classNef_gap (w : KahlerBackground (m + 1) M)
    (α β : RealBottChern (m + 1) M)
    (hα : ClassNefWithRespectTo w α) (hβ : ClassNefWithRespectTo w β)
    (hgap : 0 < classTopIntersection w α - 4 * (m + 1 : ℝ) * classOneSlotIntersection w α β) :
    IsBigClass (α - β) := by
  let A : ClosedRealOneOneForm (m + 1) M := Quotient.out α
  let B : ClosedRealOneOneForm (m + 1) M := Quotient.out β
  have hA : RealBottChern.ofRepresentative A = α := Quotient.out_eq α
  have hB : RealBottChern.ofRepresentative B = β := Quotient.out_eq β
  have hAnef : NefWithRespectTo w A := by
    change ClassNefWithRespectTo w (RealBottChern.ofRepresentative A)
    rw [hA]
    exact hα
  have hBnef : NefWithRespectTo w B := by
    change ClassNefWithRespectTo w (RealBottChern.ofRepresentative B)
    rw [hB]
    exact hβ
  have hgapAB : 0 < slotIntegral w (fun _ => A) - 4 * (m + 1 : ℝ) *
      slotIntegral w (Fin.cons B (fun _ : Fin m => A)) := by
    rw [← hA, ← hB, classTopIntersection_ofRepresentative,
      classOneSlotIntersection_ofRepresentative] at hgap
    exact hgap
  have hbig := isBigClass_sub_of_nef_gap w A B hAnef hBnef hgapAB
  have hclass : RealBottChern.ofRepresentative (A - B) = α - β := by
    simp only [sub_eq_add_neg, RealBottChern.ofRepresentative_add,
      RealBottChern.ofRepresentative_neg, hA, hB]
  rw [hclass] at hbig
  exact hbig

end

end SGPT.Foundations.Analysis.Pending.XiaoClassNefDifference
