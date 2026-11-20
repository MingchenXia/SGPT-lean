import SGPT.Foundations.Analysis.Pending.ManifoldBorelFoundation
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

set_option autoImplicit false

/-!
# Countable assembly of compact regular branches

A local regular parametrization of an analytic subvariety gives a finite Borel
measure on each compact parameter ball.  This module isolates the
measure-theoretic skeleton needed before constructing the integration current:
a countable family of compact regular branches covering the regular locus and a
summable series of their parameter masses.

The construction below deliberately produces only an *auxiliary parameter
measure*.  A pushforward of parameter Lebesgue measure is not automatically the
metric volume measure of the branch: the Jacobian density remains to be supplied
by the local finite-projection and Wirtinger argument.  Likewise, this module
makes no claim that the assembled measure defines a closed current.  Thus the
remaining Lelong and singular-Stokes inputs stay explicit rather than being
hidden in this countable-measure construction.
-/

open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.CountableRegularBranchMeasure

open FirstPass FirstPass.NumericalRestrictedVolume FirstPass.RegularPatchNeighborhood
open MeasureTheory
open ManifoldBorelFoundation

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A countable compact regular-branch cover of the regular locus.  Its final
field is separate data because finite mass on individual compact branches does
not imply that their countable sum has finite total mass. -/
structure CountableCompactRegularBranchCover
    (V : ClosedIrreducibleAnalyticSubvariety n M) where
  patch : ℕ → RegularPatch V
  radius : ℕ → ℝ
  closedBall_subset_parameterDomain : ∀ i,
    Metric.closedBall (0 : ComplexModel V.dim) (radius i) ⊆
      (patch i).parameterDomain
  regularLocus_subset_iUnion_image :
    regularLocus (n := n) V.carrier V.dim ⊆
      ⋃ i, (patch i).toManifold '' Metric.closedBall (0 : ComplexModel V.dim) (radius i)
  summable_parameter_mass :
    ∑' i, regularPatchClosedBallPushforwardBorel (patch i) (radius i) Set.univ < ⊤

namespace CountableCompactRegularBranchCover

variable {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- The image of the `i`-th compact parameter ball. -/
def branchImage (A : CountableCompactRegularBranchCover V) (i : ℕ) : Set M :=
  (A.patch i).toManifold '' Metric.closedBall (0 : ComplexModel V.dim) (A.radius i)

/-- The Borel pushforward of parameter Lebesgue measure on the `i`-th compact
regular branch.  It is auxiliary until a Jacobian comparison identifies it with
intrinsic volume. -/
def branchParameterMeasure (A : CountableCompactRegularBranchCover V) (i : ℕ) :
    @Measure M (manifoldBorel M) :=
  regularPatchClosedBallPushforwardBorel (A.patch i) (A.radius i)

/-- The finite auxiliary Borel measure obtained by summing parameter measures of
all declared compact branches. -/
def assembledParameterMeasure (A : CountableCompactRegularBranchCover V) :
    @Measure M (manifoldBorel M) :=
  Measure.sum A.branchParameterMeasure

/-- Every declared branch image lies in the regular locus. -/
theorem branchImage_subset_regularLocus (A : CountableCompactRegularBranchCover V) (i : ℕ) :
    A.branchImage i ⊆ regularLocus (n := n) V.carrier V.dim := by
  rintro x ⟨w, hw, rfl⟩
  exact RegularPatch.toManifold_mem_regularLocus (A.patch i)
    (A.closedBall_subset_parameterDomain i hw)

/-- The declared branch images cover exactly the regular locus. -/
theorem iUnion_branchImage_eq_regularLocus (A : CountableCompactRegularBranchCover V) :
    ⋃ i, A.branchImage i = regularLocus (n := n) V.carrier V.dim := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset (fun i => A.branchImage_subset_regularLocus i)
  · exact A.regularLocus_subset_iUnion_image

/-- Every branch image is compact, independently of any global cover theorem. -/
theorem isCompact_branchImage (A : CountableCompactRegularBranchCover V) (i : ℕ) :
    IsCompact (A.branchImage i) :=
  (isCompact_closedBall (0 : ComplexModel V.dim) (A.radius i)).image_of_continuousOn
    ((RegularPatch.continuousOn_toManifold (A.patch i)).mono
      (A.closedBall_subset_parameterDomain i))

/-- With the usual Hausdorff separation of the ambient manifold, each compact
branch image is Borel for the explicitly chosen manifold Borel structure. -/
theorem branchImage_measurableSet (A : CountableCompactRegularBranchCover V) (i : ℕ) :
    @MeasurableSet M (manifoldBorel M) (A.branchImage i) := by
  let _ : MeasurableSpace M := manifoldBorel M
  let _ : BorelSpace M := ⟨rfl⟩
  exact (A.isCompact_branchImage i).measurableSet

/-- The parameter measure of one branch is carried by that branch image. -/
theorem branchParameterMeasure_compl_branchImage
    (A : CountableCompactRegularBranchCover V) (i : ℕ) :
    A.branchParameterMeasure i (A.branchImage i)ᶜ = 0 := by
  rw [branchParameterMeasure,
    regularPatchClosedBallPushforwardBorel_apply (A.patch i)
      (A.closedBall_subset_parameterDomain i) (A.branchImage i)ᶜ
      (A.branchImage_measurableSet i).compl]
  rw [Measure.restrict_apply' Metric.isClosed_closedBall.measurableSet]
  have hempty :
      (A.patch i).toManifold ⁻¹' (A.branchImage i)ᶜ ∩
        Metric.closedBall (0 : ComplexModel V.dim) (A.radius i) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro w hw
    exact hw.1 ⟨w, hw.2, rfl⟩
  rw [hempty, measure_empty]

/-- Each branch parameter measure gives zero mass to the complement of the
regular locus, because its compact image lies entirely in that locus. -/
theorem branchParameterMeasure_compl_regularLocus
    (A : CountableCompactRegularBranchCover V) (i : ℕ) :
    A.branchParameterMeasure i (regularLocus (n := n) V.carrier V.dim)ᶜ = 0 := by
  apply nonpos_iff_eq_zero.mp
  calc
    A.branchParameterMeasure i (regularLocus (n := n) V.carrier V.dim)ᶜ ≤
        A.branchParameterMeasure i (A.branchImage i)ᶜ :=
      measure_mono (Set.compl_subset_compl.mpr (A.branchImage_subset_regularLocus i))
    _ = 0 := A.branchParameterMeasure_compl_branchImage i

/-- A branch parameter measure has finite total mass. -/
theorem branchParameterMeasure_univ_lt_top (A : CountableCompactRegularBranchCover V) (i : ℕ) :
    A.branchParameterMeasure i Set.univ < ⊤ :=
  regularPatchClosedBallPushforwardBorel_univ_lt_top (A.patch i)
    (A.closedBall_subset_parameterDomain i)

/-- Evaluation of the assembled auxiliary measure is the series of branch
measure evaluations.  This holds for every set because the index is `ℕ`. -/
theorem assembledParameterMeasure_apply (A : CountableCompactRegularBranchCover V) (s : Set M) :
    A.assembledParameterMeasure s = ∑' i, A.branchParameterMeasure i s := by
  exact Measure.sum_apply_of_countable A.branchParameterMeasure s

/-- The assembled auxiliary measure is carried by the regular locus.  This
does not identify it with the integration current, but makes it usable as a
measure-theoretic object on `V_reg`. -/
theorem assembledParameterMeasure_compl_regularLocus
    (A : CountableCompactRegularBranchCover V) :
    A.assembledParameterMeasure (regularLocus (n := n) V.carrier V.dim)ᶜ = 0 := by
  change Measure.sum A.branchParameterMeasure
    (regularLocus (n := n) V.carrier V.dim)ᶜ = 0
  exact Measure.sum_apply_eq_zero.mpr fun i =>
    A.branchParameterMeasure_compl_regularLocus i

/-- Almost every point for the assembled auxiliary measure belongs to the
regular locus. -/
theorem ae_mem_regularLocus (A : CountableCompactRegularBranchCover V) :
    ∀ᵐ x ∂A.assembledParameterMeasure,
      x ∈ regularLocus (n := n) V.carrier V.dim := by
  rw [ae_iff]
  exact A.assembledParameterMeasure_compl_regularLocus

/-- The assembled parameter measure has the supplied finite total mass. -/
theorem assembledParameterMeasure_univ_lt_top (A : CountableCompactRegularBranchCover V) :
    A.assembledParameterMeasure Set.univ < ⊤ := by
  rw [A.assembledParameterMeasure_apply]
  exact A.summable_parameter_mass

/-- The countable branch construction therefore yields a finite Borel measure. -/
theorem assembledParameterMeasure_isFiniteMeasure (A : CountableCompactRegularBranchCover V) :
    @IsFiniteMeasure M (manifoldBorel M) A.assembledParameterMeasure :=
  ⟨A.assembledParameterMeasure_univ_lt_top⟩

/-- The assembled auxiliary measure, packaged for APIs requiring a finite Borel
measure. -/
def finiteAssembledParameterMeasure (A : CountableCompactRegularBranchCover V) :
    @FiniteMeasure M (manifoldBorel M) :=
  ⟨A.assembledParameterMeasure, A.assembledParameterMeasure_isFiniteMeasure⟩

@[simp]
theorem finiteAssembledParameterMeasure_coe (A : CountableCompactRegularBranchCover V) :
    (A.finiteAssembledParameterMeasure : @Measure M (manifoldBorel M)) =
      A.assembledParameterMeasure :=
  rfl

/-- Integration against the assembled parameter measure is the sum of
integrations against its compact regular branches. -/
theorem lintegral_assembledParameterMeasure (A : CountableCompactRegularBranchCover V)
    (f : M → ENNReal) :
    ∫⁻ x, f x ∂A.assembledParameterMeasure =
      ∑' i, ∫⁻ x, f x ∂A.branchParameterMeasure i := by
  exact lintegral_sum_measure f A.branchParameterMeasure

/-- A Bochner-integrable test function can be integrated branch by branch.
This is the usable testing interface for a later construction of an
integration current; the theorem requires only integrability for the already
assembled finite parameter measure. -/
theorem integral_assembledParameterMeasure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : CountableCompactRegularBranchCover V) (f : M → E)
    (hf : Integrable f A.assembledParameterMeasure) :
    ∫ x, f x ∂A.assembledParameterMeasure =
      ∑' i, ∫ x, f x ∂A.branchParameterMeasure i := by
  change ∫ x, f x ∂Measure.sum A.branchParameterMeasure =
    ∑' i, ∫ x, f x ∂A.branchParameterMeasure i
  exact integral_sum_measure hf

/-- Integration against the assembled measure is insensitive to changes away
from the regular locus.  This is the support statement in a form directly
usable by test-function constructions. -/
theorem integral_assembledParameterMeasure_congr_on_regularLocus
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : CountableCompactRegularBranchCover V) (f g : M → E)
    (hfg : Set.EqOn f g (regularLocus (n := n) V.carrier V.dim)) :
    ∫ x, f x ∂A.assembledParameterMeasure =
      ∫ x, g x ∂A.assembledParameterMeasure := by
  apply integral_congr_ae
  filter_upwards [A.ae_mem_regularLocus] with x hx
  exact hfg hx

/-- A bounded continuous real test function is integrable against the finite
assembled parameter measure. -/
theorem integrable_boundedContinuousTest
    (A : CountableCompactRegularBranchCover V) (f : BoundedContinuousFunction M ℝ) :
    Integrable (fun x => f x) A.assembledParameterMeasure := by
  let _ : MeasurableSpace M := manifoldBorel M
  let _ : BorelSpace M := ⟨rfl⟩
  let _ : IsFiniteMeasure A.assembledParameterMeasure :=
    A.assembledParameterMeasure_isFiniteMeasure
  apply Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖
  exact Filter.Eventually.of_forall fun x => f.norm_coe_le_norm x

/-- The degree-zero test functional associated to the assembled parameter
measure.  It is linear on bounded continuous real functions.  It is not yet
the integration current `[V]`: a Jacobian-density comparison and the
distributional closedness argument remain separate analytic obligations. -/
def parameterTestFunctional (A : CountableCompactRegularBranchCover V) :
    BoundedContinuousFunction M ℝ →ₗ[ℝ] ℝ where
  toFun := fun f => ∫ x, f x ∂A.assembledParameterMeasure
  map_add' := by
    intro f g
    simpa using integral_add (A.integrable_boundedContinuousTest f)
      (A.integrable_boundedContinuousTest g)
  map_smul' := by
    intro c f
    simpa using (A.integrable_boundedContinuousTest f).integral_smul c

/-- The parameter test functional is supported on the regular locus. -/
theorem parameterTestFunctional_congr_on_regularLocus
    (A : CountableCompactRegularBranchCover V) (f g : BoundedContinuousFunction M ℝ)
    (hfg : Set.EqOn (fun x => f x) (fun x => g x)
      (regularLocus (n := n) V.carrier V.dim)) :
    A.parameterTestFunctional f = A.parameterTestFunctional g :=
  A.integral_assembledParameterMeasure_congr_on_regularLocus (fun x => f x)
    (fun x => g x) hfg

/-- Evaluation of the bounded-continuous test functional is the convergent
series of its compact regular-branch evaluations. -/
theorem parameterTestFunctional_eq_tsum
    (A : CountableCompactRegularBranchCover V) (f : BoundedContinuousFunction M ℝ) :
    A.parameterTestFunctional f =
      ∑' i, ∫ x, f x ∂A.branchParameterMeasure i :=
  A.integral_assembledParameterMeasure (fun x => f x)
    (A.integrable_boundedContinuousTest f)

end CountableCompactRegularBranchCover

end

end SGPT.Foundations.Analysis.Pending.CountableRegularBranchMeasure
