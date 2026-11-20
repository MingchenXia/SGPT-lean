import SGPT.Foundations.Analysis.Pending.XiaoFormC0Topology
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp

set_option autoImplicit false

/-! # Actual compact coefficient jets and their genuine smooth initial topology -/

open Set Filter Topology
open scoped Topology BoundedContinuousFunction ENat ContDiff

namespace SGPT.Foundations.Analysis.Pending.XiaoSmoothFormTopology

open FirstPass FirstPass.PositiveClasses XiaoFormC0Topology

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual compact chart targets, finite derivative orders and actual tensor and derivative directions. -/
structure JetProbe (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] where
  chart : ComplexChart n M
  compactSet : Set (ComplexModel n)
  isCompact : IsCompact compactSet
  subset_target : compactSet ⊆ chart.val.target
  order : ℕ
  vectors : Fin 2 → ComplexModel n
  directions : Fin order → ComplexModel n

/-- A genuine scalar tensor component evaluated on an actual pair of tangent vectors. -/
def scalarCoefficient (p : JetProbe n M) (θ : ClosedRealOneOneForm n M) :
    ComplexModel n → ℝ := fun z => θ.val.coeff p.chart z p.vectors

/-- The actual scalar coefficient is smooth on its actual open chart target. -/
theorem scalarCoefficient_contDiffOn (p : JetProbe n M) (θ : ClosedRealOneOneForm n M) :
    ContDiffOn ℝ ∞ (scalarCoefficient p θ) p.chart.val.target := by
  exact (ContinuousAlternatingMap.apply ℝ (ComplexModel n) ℝ p.vectors).contDiff.comp_contDiffOn
    (θ.val.smooth p.chart)

private def boundedJet (p : JetProbe n M) (θ : ClosedRealOneOneForm n M) :
    p.compactSet →ᵇ ℝ := by
  letI : CompactSpace p.compactSet := isCompact_iff_compactSpace.mp p.isCompact
  have hk : (p.order : WithTop ℕ∞) ≤ ∞ :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl p.order
  have hcont := ContinuousOn.continuousOn_iteratedFDeriv (scalarCoefficient_contDiffOn p θ)
    p.chart.val.open_target hk
  have heval : Continuous (fun T : ContinuousMultilinearMap ℝ
      (fun _ : Fin p.order => ComplexModel n) ℝ => T p.directions) :=
    continuous_eval_const p.directions
  exact BoundedContinuousFunction.mkOfCompact
    ⟨fun z => iteratedFDeriv ℝ p.order (scalarCoefficient p θ) z p.directions,
      (heval.comp_continuousOn hcont).comp_continuous continuous_subtype_val
        (fun z => p.subset_target z.property)⟩

/-- Genuine iterated Fréchet derivatives on actual compact targets give actual bounded-function linear probes. -/
def jetLinearMap (p : JetProbe n M) :
    ClosedRealOneOneForm n M →ₗ[ℝ] (p.compactSet →ᵇ ℝ) where
  toFun := boundedJet p
  map_add' := by
    intro θ η
    apply BoundedContinuousFunction.ext
    intro z
    change iteratedFDeriv ℝ p.order (scalarCoefficient p (θ + η)) z p.directions =
      iteratedFDeriv ℝ p.order (scalarCoefficient p θ) z p.directions +
        iteratedFDeriv ℝ p.order (scalarCoefficient p η) z p.directions
    have hcoeff : scalarCoefficient p (θ + η) =
        scalarCoefficient p θ + scalarCoefficient p η := by
      funext y
      exact congrArg (fun T => T p.vectors) (ClosedRealOneOneForm.coeff_add θ η p.chart y)
    rw [hcoeff]
    have hk : (p.order : WithTop ℕ∞) ≤ ∞ :=
      ENat.natCast_le_of_coe_top_le_withTop le_rfl p.order
    exact congrArg (fun T => T p.directions) (iteratedFDeriv_add_apply
      (((scalarCoefficient_contDiffOn p θ) z (p.subset_target z.property)).contDiffAt
        (p.chart.val.open_target.mem_nhds (p.subset_target z.property)) |>.of_le hk)
      (((scalarCoefficient_contDiffOn p η) z (p.subset_target z.property)).contDiffAt
        (p.chart.val.open_target.mem_nhds (p.subset_target z.property)) |>.of_le hk))
  map_smul' := by
    intro c θ
    apply BoundedContinuousFunction.ext
    intro z
    change iteratedFDeriv ℝ p.order (scalarCoefficient p (c • θ)) z p.directions =
      c • iteratedFDeriv ℝ p.order (scalarCoefficient p θ) z p.directions
    have hcoeff : scalarCoefficient p (c • θ) = c • scalarCoefficient p θ := by
      funext y
      exact congrArg (fun T => T p.vectors) (ClosedRealOneOneForm.coeff_smul c θ p.chart y)
    rw [hcoeff]
    have hk : (p.order : WithTop ℕ∞) ≤ ∞ :=
      ENat.natCast_le_of_coe_top_le_withTop le_rfl p.order
    exact congrArg (fun T => T p.directions) (iteratedFDeriv_const_smul_apply (a := c)
      (((scalarCoefficient_contDiffOn p θ) z (p.subset_target z.property)).contDiffAt
        (p.chart.val.open_target.mem_nhds (p.subset_target z.property)) |>.of_le hk))

/-- Every actual compact coefficient jet is the genuine iterated derivative of the actual tensor coefficient. -/
theorem jetLinearMap_apply (p : JetProbe n M) (θ : ClosedRealOneOneForm n M)
    (z : p.compactSet) :
    jetLinearMap p θ z = iteratedFDeriv ℝ p.order (scalarCoefficient p θ) z p.directions := rfl

/-- All actual charts, compact targets, finite orders, tensor vectors and derivative directions are included. -/
def allJetsLinearMap :
    ClosedRealOneOneForm n M →ₗ[ℝ] ((p : JetProbe n M) → (p.compactSet →ᵇ ℝ)) :=
  LinearMap.pi jetLinearMap

variable [CompactSpace M]

/-- The genuine smooth probe records the actual intrinsic C0 component and every actual compact coefficient jet. -/
def smoothProbeLinearMap (w : KahlerBackground n M) :
    ClosedRealOneOneForm n M →ₗ[ℝ]
      ((LineProbe n M →ᵇ ℝ) × ((p : JetProbe n M) → (p.compactSet →ᵇ ℝ))) :=
  (probeLinearMap w).prod allJetsLinearMap

/-- The actual smooth form topology is the genuine initial topology of all actual C0 and compact-jet probes. -/
abbrev formSmoothTopology (w : KahlerBackground n M) :
    TopologicalSpace (ClosedRealOneOneForm n M) :=
  TopologicalSpace.induced (smoothProbeLinearMap w) inferInstance

/-- Actual addition and negation are continuous for the actual smooth coefficient-jet topology. -/
theorem formSmoothTopology_isTopologicalAddGroup (w : KahlerBackground n M) :
    @IsTopologicalAddGroup (ClosedRealOneOneForm n M) (formSmoothTopology w) inferInstance :=
  topologicalAddGroup_induced (smoothProbeLinearMap w)

/-- Actual real scalar multiplication is continuous for the actual smooth coefficient-jet topology. -/
theorem formSmoothTopology_continuousSMul (w : KahlerBackground n M) :
    @ContinuousSMul ℝ (ClosedRealOneOneForm n M) inferInstance inferInstance (formSmoothTopology w) :=
  continuousSMul_induced (smoothProbeLinearMap w)

/-- The genuine smooth topology controls the actual intrinsic directional C0 topology. -/
theorem continuous_identity_to_formC0Topology (w : KahlerBackground n M) :
    Continuous[formSmoothTopology w, formC0Topology w]
      (id : ClosedRealOneOneForm n M → ClosedRealOneOneForm n M) := by
  let : TopologicalSpace (ClosedRealOneOneForm n M) := formSmoothTopology w
  apply continuous_induced_rng.mpr
  have hprobe : Continuous[formSmoothTopology w, inferInstance] (smoothProbeLinearMap w) :=
    continuous_induced_dom
  exact continuous_fst.comp hprobe

/-- The actual smooth topology separates into actual intrinsic C0 control and all actual compact jets. -/
theorem formSmoothTopology_eq_inf (w : KahlerBackground n M) :
    formSmoothTopology w =
      formC0Topology w ⊓ TopologicalSpace.induced allJetsLinearMap inferInstance := by
  change TopologicalSpace.induced (smoothProbeLinearMap w)
    (@instTopologicalSpaceProd (LineProbe n M →ᵇ ℝ)
      ((p : JetProbe n M) → (p.compactSet →ᵇ ℝ)) _ _) = _
  rw [instTopologicalSpaceProd, induced_inf, induced_compose, induced_compose]
  rfl

/-- All actual coefficient jets are background independent, as is the genuine intrinsic C0 component. -/
theorem formSmoothTopology_eq_of_background (w w' : KahlerBackground n M) :
    formSmoothTopology w = formSmoothTopology w' := by
  rw [formSmoothTopology_eq_inf w, formSmoothTopology_eq_inf w',
    formC0Topology_eq_of_background w w']

end

end SGPT.Foundations.Analysis.Pending.XiaoSmoothFormTopology
