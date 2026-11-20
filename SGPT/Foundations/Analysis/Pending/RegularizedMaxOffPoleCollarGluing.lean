import SGPT.Foundations.Analysis.Pending.RegularizedMaxCollarGluing
import SGPT.Foundations.Analysis.Pending.FiniteRegularizedMaxOffPoleCoreCover

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The collar glue in the bounded-remainder convention

`Pending.RegularizedMaxCollarGluing.hasManifoldSmoothAnalyticSingularities_eregularizedMaxGlued`
carries the collar glue into the STRONG convention
(`HasManifoldSmoothAnalyticSingularities`), at the price of an alignment
hypothesis at points where both branches are poles.
`AdmissibleRestrictedCurrentPresentation` asks instead for the convention the
human fixed in `I-0489` (`HasManifoldAnalyticSingularitiesSmoothOffPole`), and in
that convention **no alignment is needed at all**: the append theorem
`Pending.RegularizedMaxOffPoleAppend.hasAnalyticSingularitiesSmoothOffPoleAt_eregularizedMax`
concatenates the two generator families, provided they carry ONE common
coefficient `c`.

In the collar situation of CT22 Lemma 4.3, Step 3 the common coefficient is free:
the LOCAL branch there is `ψ + sρ` with `ψ` finite and chart-smooth on the collar
neighbourhood, so it is a smooth real germ, and a smooth real germ is presented
with the one-element constant generator family `(1)` and an ARBITRARY positive
coefficient.  So the local branch simply adopts whatever coefficient the global
branch happens to have at the point.

That is the whole content of this module: the off-pole analogue of the strong
collar-gluing theorem, with the alignment hypothesis replaced by *smoothness of
the local branch* — which the construction supplies by definition of the open set
on which it glues.
-/

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.RegularizedMaxOffPoleCollarGluing

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.Pending.RegularizedMaxEReal
open SGPT.Foundations.Analysis.Pending.RegularizedMaxOffPoleAppend
open SGPT.Foundations.Analysis.Pending.RegularizedMaxCollarGluing
open SGPT.Foundations.Analysis.Pending.FiniteRegularizedMaxOffPoleCoreCover

noncomputable section

/-- **A smooth real germ is presented in the bounded-remainder convention with EVERY
positive coefficient.**  The generator family is the one-element constant family
`(1)`, whose logarithm vanishes identically, so the coefficient never appears.
This is the off-pole analogue of
`Pending.RegularizedMaxSmoothAnalyticType.hasSmoothAnalyticSingularitiesAt_of_eventuallyEq_coe`,
with the coefficient left free — which is what lets a smooth branch share the
coefficient of an arbitrary singular one. -/
theorem boundedSmoothOffPoleLogarithmicTypeAt_of_eventuallyEq_coe {n : ℕ} {c : ℝ}
    (hc : 0 < c) {u : ComplexModel n → EReal} {z : ComplexModel n}
    {φ : ComplexModel n → ℝ} (hφ : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ ∞ φ y)
    (hu : u =ᶠ[𝓝 z] fun y => (φ y : EReal)) :
    BoundedSmoothOffPoleLogarithmicTypeAt u c
      (fun (_ : Fin 1) (_ : ComplexModel n) => (1 : ℂ)) z := by
  refine ⟨hc, ⟨univ, isOpen_univ, mem_univ z, fun _ => differentiableOn_const 1⟩, φ,
    boundedRealGermAt_of_continuousAt hφ.self_of_nhds.continuousAt,
    hφ.mono fun _ hy _ => hy, ?_⟩
  filter_upwards [hu] with y hy
  have h0 : generatorLog (fun (_ : Fin 1) (_ : ComplexModel n) => (1 : ℂ)) y = 0 := by
    rw [generatorLog_of_nonzero ⟨0, one_ne_zero⟩]
    norm_num [generatorNormSq]
  rw [hy, h0]
  simp

/-- The same statement in existential form. -/
theorem hasAnalyticSingularitiesSmoothOffPoleAt_of_eventuallyEq_coe {n : ℕ}
    {u : ComplexModel n → EReal} {z : ComplexModel n} {φ : ComplexModel n → ℝ}
    (hφ : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ ∞ φ y)
    (hu : u =ᶠ[𝓝 z] fun y => (φ y : EReal)) :
    HasAnalyticSingularitiesSmoothOffPoleAt u z :=
  ⟨1, 1, _, boundedSmoothOffPoleLogarithmicTypeAt_of_eventuallyEq_coe one_pos hφ hu⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The bounded-remainder convention survives the collar glue, with no alignment
hypothesis.**  The local branch is only asked to be a smooth real germ at every
chart point of `U`; the global branch carries the convention everywhere.  This is
the form `AdmissibleRestrictedCurrentPresentation.smoothAnalyticSingularities`
consumes. -/
theorem hasManifoldAnalyticSingularitiesSmoothOffPole_eregularizedMaxGlued
    {U U' : Set M} {δ : ℝ} {f g : M → EReal}
    (hδ : 0 < δ) (hU : IsOpen U) (hclosure : closure U' ⊆ U)
    (hgap : ∀ x ∈ U \ U', f x + (δ : EReal) ≤ g x) (hgtop : ∀ x, g x ≠ ⊤)
    (hg : HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) g)
    (hf : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      e.val.symm z ∈ U → ∃ φ : ComplexModel n → ℝ,
        (∀ᶠ w in 𝓝 z, ContDiffAt ℝ ∞ φ w) ∧
          chartFunction f e =ᶠ[𝓝 z] fun w => (φ w : EReal)) :
    HasManifoldAnalyticSingularitiesSmoothOffPole (n := n)
      (eregularizedMaxGlued U δ f g) := by
  intro e z hz
  by_cases hxU : e.val.symm z ∈ U
  · -- inside `U` the glue is the regularized maximum of the two branches
    have hO : IsOpen (e.val.target ∩ e.val.symm ⁻¹' U) :=
      e.val.continuousOn_symm.isOpen_inter_preimage e.val.open_target hU
    have heq : chartFunction (eregularizedMaxGlued U δ f g) e =ᶠ[𝓝 z]
        fun y => eregularizedMax δ (chartFunction g e y) (chartFunction f e y) := by
      filter_upwards [hO.mem_nhds ⟨hz, hxU⟩] with w hw
      exact eregularizedMaxGlued_of_mem hw.2
    obtain ⟨c, N, F, hgpres⟩ := hg e z hz
    obtain ⟨φ, hφ, hfeq⟩ := hf e z hz hxU
    have hfpres := boundedSmoothOffPoleLogarithmicTypeAt_of_eventuallyEq_coe
      hgpres.1 hφ hfeq
    obtain ⟨c', N', F', hpres⟩ :=
      hasAnalyticSingularitiesSmoothOffPoleAt_eregularizedMax hδ hgpres hfpres
    exact ⟨c', N', F', BoundedSmoothOffPoleLogarithmicTypeAt.congr_eventuallyEq hpres heq⟩
  · -- off `U` the glue IS the global branch, as a germ
    have hchart : chartFunction (eregularizedMaxGlued U δ f g) e =ᶠ[𝓝 z]
        chartFunction g e :=
      (eregularizedMaxGlued_eventuallyEq_global hδ hclosure hgap hgtop hxU).comp_tendsto
        (e.val.continuousAt_symm hz)
    obtain ⟨c, N, F, hgpres⟩ := hg e z hz
    exact ⟨c, N, F, BoundedSmoothOffPoleLogarithmicTypeAt.congr_eventuallyEq hgpres hchart⟩

end

end SGPT.Foundations.Analysis.Pending.RegularizedMaxOffPoleCollarGluing
