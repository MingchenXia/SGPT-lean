import SGPT.Foundations.Analysis.Pending.XiaoPureSmoothBottChernClosure
import Mathlib.Data.Nat.Find

set_option autoImplicit false

/-! Actual original moving smooth-quotient class sequence -> internally
chosen smooth representatives with vanishing genuine directional C0 error.
Full BP statement and ENTIRE proof precede this source. No supplied limiting
form, representative convergence or class calibration; no finiteD claim. -/

noncomputable section
open Set Filter Topology
open scoped Topology
namespace SGPT.Foundations.Analysis.Pending.MovingBottChernRepresentativeLift
open FirstPass FirstPass.PositiveClasses XiaoFormC0Topology
  XiaoBottChernC0Closure XiaoSmoothBottChernClosure XiaoPureSmoothBottChernClosure

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- From the original actual smooth-quotient convergence, internally choose
ONE limiting smooth form and representatives of EVERY original class with
vanishing actual C0 error. No convergent representative is supplied. -/
theorem exists_representatives_tendsto_C0 (w : KahlerBackground n M)
    (β : RealBottChern n M) (βj : ℕ → RealBottChern n M)
    (hlim : Tendsto βj atTop
      (@nhds (RealBottChern n M) classPureSmoothTopology β)) :
    ∃ (θ : ClosedRealOneOneForm n M) (η : ℕ → ClosedRealOneOneForm n M),
      RealBottChern.ofRepresentative θ = β ∧
      (∀ j, RealBottChern.ofRepresentative (η j) = βj j) ∧
      Tendsto (fun j => formC0Seminorm w (η j - θ)) atTop (𝓝 0) := by
  classical
  let : TopologicalSpace (ClosedRealOneOneForm n M) := formC0Topology w
  let : TopologicalSpace (RealBottChern n M) := classC0Topology w
  have hsm : Tendsto βj atTop (@nhds (RealBottChern n M) (classSmoothTopology w) β) := by
    rw [classSmoothTopology_eq_pure w]
    exact hlim
  have hc0 : Tendsto βj atTop (𝓝 β) :=
    (@Continuous.tendsto (RealBottChern n M) (RealBottChern n M)
      (classSmoothTopology w) (classC0Topology w) id
      (continuous_identity_to_classC0Topology w) β).comp hsm
  obtain ⟨θ,hθ⟩ : ∃ θ : ClosedRealOneOneForm n M,
      RealBottChern.ofRepresentative θ = β :=
    Quotient.inductionOn β (fun θ => ⟨θ,rfl⟩)
  let r : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hr (k : ℕ) : 0 < r k := by dsimp [r]; positivity
  have hex (k : ℕ) : ∃ N : ℕ, ∀ j ≥ N,
      ∃ a : ClosedRealOneOneForm n M,
        RealBottChern.ofRepresentative a = βj j ∧ formC0Seminorm w (a - θ) < r k := by
    let B : Set (ClosedRealOneOneForm n M) := (formC0Seminorm w).ball θ (r k)
    have hB : IsOpen B := isOpen_formC0Seminorm_ball w θ (r k)
    have hθB : θ ∈ B := (formC0Seminorm w).mem_ball_self (hr k)
    have hqB : IsOpen (RealBottChern.ofRepresentative '' B) :=
      (XiaoBottChernC0Closure.isOpenQuotientMap_ofRepresentative w).isOpenMap B hB
    have hβB : β ∈ RealBottChern.ofRepresentative '' B := ⟨θ,hθB,hθ⟩
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hc0.eventually (hqB.mem_nhds hβB))
    refine ⟨N,fun j hj => ?_⟩
    obtain ⟨a,ha,haj⟩ := hN j hj
    exact ⟨a,haj,ha⟩
  choose N hN using hex
  let level : ℕ → ℕ := fun j => Nat.findGreatest (fun k => N k ≤ j) j
  have hlevel (j : ℕ) (hj : N 0 ≤ j) : N (level j) ≤ j :=
    Nat.findGreatest_spec (P := fun k => N k ≤ j) (Nat.zero_le j) hj
  let lift (j : ℕ) (hj : N 0 ≤ j) : ClosedRealOneOneForm n M :=
    (hN (level j) j (hlevel j hj)).choose
  let η (j : ℕ) : ClosedRealOneOneForm n M :=
    if hj : N 0 ≤ j then lift j hj else Quotient.out (βj j)
  have hηclass (j : ℕ) : RealBottChern.ofRepresentative (η j) = βj j := by
    dsimp only [η]
    split_ifs with hj
    · exact (hN (level j) j (hlevel j hj)).choose_spec.1
    · exact Quotient.out_eq _
  have htlevel : Tendsto level atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop (max k (N k))] with j hj
    exact Nat.le_findGreatest ((le_max_left _ _).trans hj) ((le_max_right _ _).trans hj)
  have hbound : ∀ᶠ j in atTop, formC0Seminorm w (η j - θ) ≤ r (level j) := by
    filter_upwards [eventually_ge_atTop (N 0)] with j hj
    dsimp only [η]
    rw [dif_pos hj]
    exact (hN (level j) j (hlevel j hj)).choose_spec.2.le
  refine ⟨θ,η,hθ,hηclass,?_⟩
  exact squeeze_zero' (Eventually.of_forall fun j => norm_nonneg (probeLinearMap w (η j - θ)))
    hbound (tendsto_one_div_add_atTop_nhds_zero_nat.comp htlevel)

end SGPT.Foundations.Analysis.Pending.MovingBottChernRepresentativeLift
